// -*- mode: Bluespec; -*-

/**
 * Consensus State Machine Interface (CSMI)
 *
 * A library to handle common patterns in consensus specifications
 *
 * Gabriela Moreira, Josef Widder and Yassine Boukhari,
 * Informal Systems, 2025
 */
module CSMIBase {
  import basicSpells.* from "basicSpells"

  type LocalState[process_id, message, other_fields] = {
    process_id: process_id,
    messages: Set[message]
    | other_fields
  }

  type ConsensusResult[state, output] = {
    output: Set[output],
    state: state,
  }
  type UponResult[s, o] = Option[ConsensusResult[s, o]]

  type TimeoutEvent[fields] = fields

  type Environment[p, s, m, te, b] = {
    system: p -> LocalState[p, m, s],
    activeTimeouts: p -> Option[TimeoutEvent[te]],
    bookkeeping: b
  }

  type ReceiveMessage[p, s, m, o] = (LocalState[p, m, s], m) => Set[UponResult[LocalState[p, m, s], o]]

  type ApplyEffect[p, s, m, te, o, b] =
    (Environment[p, s, m, te, b], p, Set[o]) => Environment[p, s, m, te, b]
  type FireTimeoutEvent[p, s, m, te, o] = (LocalState[p, m, s], TimeoutEvent[te]) => ConsensusResult[LocalState[p, m, s], o]

  pure def bookkeep(env: Environment[p, s, m, te, b], f: b => b): Environment[p, s, m, te, b] = {
    { ...env, bookkeeping: f(env.bookkeeping) }
  }

  pure def broadcast(env: Environment[p, s, m, te, b], msg: m): Environment[p, s, m, te, b] = {
    { ...env, system: env.system.transformValues(s => { ...s, messages: s.messages.setAdd(msg) }) }
  }

  pure def timeout(
    env: Environment[p, s, m, te, b],
    v: p,
    timeout: TimeoutEvent[te],
    should_replace: (TimeoutEvent[te], TimeoutEvent[te]) => bool
  ): Environment[p, s, m, te, b] = {
    { ...env,
      activeTimeouts: env.activeTimeouts.setBy(v, old_timeout => Some({
        match old_timeout {
          | None => timeout
          | Some(ts) => if (should_replace(ts, timeout)) timeout else ts
        }
      }))
    }
  }

  pure def update_state(
    env: Environment[p, s, m, te, b],
    v: p,
    res: ConsensusResult[LocalState[p, m, s], o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): Environment[p, s, m, te, b] = {
    val new = { ... env, system: env.system.set(v, res.state) }
    apply_effect(new, v, res.output)
  }

  pure def and_then(
    res: ConsensusResult[LocalState[p, m, s], o],
    f: (LocalState[p, m, s]) => ConsensusResult[LocalState[p, m, s], o]
  ): ConsensusResult[LocalState[p, m, s], o] = {
    pure val new_res = f(res.state)
    join_results(res, new_res)
  }

  pure def and_then_state(
    state: LocalState[p, m, s],
    f: (LocalState[p, m, s]) => r
  ): r = {
    f(state)
  }

  pure def join_results(
    res1: ConsensusResult[LocalState[p, m, s], o],
    res2: ConsensusResult[LocalState[p, m, s], o]
  ): ConsensusResult[LocalState[p, m, s], o] = {
    { state: res2.state, output: res1.output.union(res2.output) }
  }

  pure def no_output(s: LocalState[p, m, s]): ConsensusResult[LocalState[p, m, s], o] = {
    { state: s, output: Set() }
  }

  pure def upon(condition: bool, transition: (bool) => ConsensusResult): UponResult = {
    if (condition)
      Some(transition(true))
    else
      None
  }
}

module CSMIState {
  import basicSpells.* from "basicSpells"
  import CSMIBase.*

  // FIXME: I think this will not work with Apalache. However, I can't test this as this is resulting in a
  // huge spec once we resolve type aliases as the types are too complex. This exceeds the gRPC limit which
  // is already quite high.
  // My alternative approach (sending processes as a param in init and step) is not working due to some
  // weird effect error on step.
  const processes: Set[p]
  var s: Environment

  // This specification is event triggered, so a process step can only be triggered by a message or a timeout
  // as a result we need either messages or timeouts in the initial state
  action init(
    initialize_process: (p) => LocalState[p, m, s],
    initial_bookkeeping: b
  ): bool = all {
    s' = {
      system: processes.mapBy(v => initialize_process(v)),
      activeTimeouts: processes.mapBy(v => None),
      bookkeeping: initial_bookkeeping,
    }
  }

  //
  // Standard interleaving semantics (one process receives one message/timeout in one action)
  //

  action receive_one_message(
    env: Environment[p, s, m, te, b],
    v: p,
    msg: m,
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b],
  ): bool = {
    nondet res = env.system.get(v).receive_message(msg).oneOf()
    all {
      // Pre-condition: only make a transition if the condition held true
      // (that is, the "upon" condition - as `upon` will return None if the
      // condition does not hold).
      res != None,
      s' = update_state(env, v, res.unwrap(), apply_effect)
    }
  }

  pure def fire_one_timeout_event(
    env: Environment[p, s, m, te, b],
    v: p,
    timeout: TimeoutEvent[te],
    fire_timeout_event: FireTimeoutEvent[p, s, m, te, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): Environment[p, s, m, te, b] = {
    val consumed_timeout_env = {
      ...env,
      activeTimeouts: env.activeTimeouts.set(v, None)
    }
    val res = consumed_timeout_env.system.get(v).fire_timeout_event(timeout)
    update_state(consumed_timeout_env, v, res, apply_effect)
  }

  action receive_msg(
    v: p,
    msg: m,
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
    s.system.get(v).messages.contains(msg),
    receive_one_message(s, v, msg, receive_message, apply_effect)
  }

  action receive_some_msg(
    v: p,
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
    // s.msgBuffer.get(v) != Set(),
    nondet msg = oneOf(s.system.get(v).messages)
    receive_msg(v, msg, receive_message, apply_effect)
  }

  action fire_timeout(
    v: p,
    fire_timeout_event: FireTimeoutEvent[p, s, m, te, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = {
     val timeout = s.activeTimeouts.get(v)
     all {
       timeout != None,
       s' = fire_one_timeout_event(s, v, timeout.unwrap(), fire_timeout_event, apply_effect),
     }
  }

  action step(
    receive_message: ReceiveMessage[p, s, m, o],
    fire_timeout_event: FireTimeoutEvent[p, s, m, te, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b],
    byzantine_messages: Set[m],
    timeout_chance: int // between 0 and 100
  ): bool = any {
    all {
      nondet timeout_frequency_control = 1.to(100).oneOf()
      or {
        // s.msgBuffer.values().flatten() == Set(),
        timeout_frequency_control <= timeout_chance,
      },
      s.activeTimeouts.values().exists(t => t != None),
      // pick a process that has an active timeout
      nondet v = oneOf(processes.filter(v => s.activeTimeouts.get(v) != None))
      fire_timeout(v, fire_timeout_event, apply_effect)
    },
    all {
      // s.msgBuffer.values().flatten() != Set(),
      // pick a process that has a message available in its buffer
      nondet v = oneOf(processes.filter(v => s.system.get(v).messages != Set()))
      receive_some_msg(v, receive_message, apply_effect)
    },
    all {
      // byzantine_messages != Set(),
      nondet msg = oneOf(byzantine_messages)
      // Workaround weird effect bug if we don't use `s` here
      nondet v = oneOf(processes.filter(v => s.system.keys() != Set()))
      receive_one_message(s, v, msg, receive_message, apply_effect)
    },
  }

  action step_no_timeout(
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
    // s.msgBuffer.values().flatten() != Set(),
    // pick a process that has a message available in its buffer
    nondet v = oneOf(processes.filter(v => s.system.get(v).messages != Set()))
    receive_some_msg(v, receive_message, apply_effect)
  }

  //
  // Accelerated semantics (multiple process may receive multiple messages/timeouts in one action)
  //

  // action receive_msg_accelerated(
  //   receive_message: ReceiveMessage[p, s, m, o],
  //   apply_effect: ApplyEffect[p, s, m, te, o, b]
  // ): bool = all {
  //   nondet msgs = processes.map(v =>
  //     s.msgBuffer.get(v).powerset().exclude(Set(Set())).map(m => (v, m))
  //   ).flatten().powerset().oneOf()
  //   val deliver = msgs.setToMap()
  //   s' = deliver.keys().fold(s, (s, v) =>
  //     deliver.get(v).fold(
  //       s,
  //       (s2, msg) => receive_one_message(s, v, msg, receive_message, apply_effect))
  //   )
  // }

  // action receive_timeout_accelerated(
  //   fire_timeout_event: FireTimeoutEvent[p, s, te, o],
  //   apply_effect: ApplyEffect[p, s, m, te, o, b]
  // ): bool = all {
  //    nondet processes_to_timeout = processes.filter(v => s.activeTimeouts.get(v) != None)
  //      .powerset().exclude(Set()).oneOf()
  //    s' = processes_to_timeout.fold(s, (s, v) => {
  //      val timeout = s.activeTimeouts.get(v)
  //      fire_one_timeout_event(s, v, timeout.unwrap(), fire_timeout_event, apply_effect)
  //    })
  // }

  // action step_accelerated(
  //   receive_message: ReceiveMessage[p, s, m, o],
  //   fire_timeout_event: FireTimeoutEvent[p, s, te, o],
  //   apply_effect: ApplyEffect[p, s, m, te, o, b],
  //   timeout_chance: int // between 0 and 100
  // ): bool = any {
  //   all {
  //     nondet timeout_frequency_control = 1.to(100).oneOf()
  //     timeout_frequency_control <= timeout_chance,
  //     s.activeTimeouts.values().exists(t => t != None),
  //     // pick a process that has an active timeout
  //     nondet v = oneOf(processes.filter(v => s.activeTimeouts.get(v) != None))
  //     fire_timeout(v, fire_timeout_event, apply_effect)
  //   },
  //   all {
  //     s.msgBuffer.values().flatten() != Set(),
  //     // pick a process that has a message available in its buffer
  //     nondet v = oneOf(processes.filter(v => s.msgBuffer.get(v) != Set()))
  //     receive_some_msg(v, receive_message, apply_effect)
  //   }
  // }
}
