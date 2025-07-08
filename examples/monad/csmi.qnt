// -*- mode: Bluespec; -*-

/**
 * Consensus State Machine Interface (CSMI)
 *
 * A library to handle common patterns in consensus specifications
 *
 * Gabriela Moreira, Josef Widder and Yassine Boukhari,
 * Informal Systems, 2025
 */
module CSMITypes {
  /// Given a type for identifying process and a record type to represent a state,
  /// Create a record type with the `process_id` and remaining fields.
  ///
  /// Use it like:
  /// ```
  /// type ProcessID = int
  /// type State = { field1: int, field2: str }
  /// type LocalState = CSMI::LocalState[ProcessID, State]
  /// ```
  type LocalState[process_id, other_fields] = { process_id: process_id |other_fields }

  /// Given a type that represents the state and a type that represents all kinds of outputs
  /// an operator can produce, create a type to represent the result of a consensus operation.
  ///
  /// Use it like:
  /// ```
  /// type State = { field1: int, field2: str }
  /// type Output =
  ///   | Broadcast(Message)
  ///   | StartTimeout(TimeoutEvent)
  ///   | BuyBananas(int)
  /// type ConsensusResult = CSMI::ConsensusResult[State, Output]
  type ConsensusResult[state, output] = {
    state: state,
    output: Set[output],
  }

  /// Given several type definitions, create a type to represent the environment of a consensus
  /// state machine.
  ///
  /// 1. `p` is the type of the process identifier
  /// 2. `s` is the type of the state
  /// 3. `m` is the type of the messages
  /// 4. `te` is the type of the timeout events
  /// 5. `b` is the type of the bookkeeping
  ///
  /// Use it like:
  /// ```
  /// type ProcessID = int
  /// type State = { field1: int, field2: str }
  /// type Message =
  ///   | Hello(int)
  ///   | Bye(str)
  /// type TimeoutEvent = int
  /// type Bookkeeping = { foo: int, bar: str }
  /// type Environment = CSMI::Environment[ProcessID, State, Message, TimeoutEvent, Bookkeeping]
  /// ```
  type Environment[p, s, m, te, b] = {
    system: p -> LocalState[p, s],
    msgBuffer: p -> Set[m],
    activeTimeouts: p -> Set[te],
    bookkeeping: b
  }

  /// The type expected for the `receive_message` function.
  /// It takes the local state of the process and a message and returns a
  /// `ConsensusResult` with the new state and the output
  type ReceiveMessage[p, s, m, o] = (LocalState[p, s], m) => ConsensusResult[LocalState[p, s], o]

  /// The type expected for the `apply_effect` function.
  /// It takes the environment, the process id and a set of outputs and returns
  /// a new environment
  type ApplyEffect[p, s, m, te, o, b] =
    (Environment[p, s, m, te, b], p, Set[o]) => Environment[p, s, m, te, b]

  /// The type expected for the `fire_timeout_event` function.
  /// It takes the local state of the process and a timeout event and returns a
  /// `ConsensusResult` with the new state and the output
  type FireTimeoutEvent[p, s, te, o] = (LocalState[p, s], te) => ConsensusResult[LocalState[p, s], o]
}

module CSMIInternal {
  import basicSpells.* from "basicSpells"
  import CSMITypes.*

  /// Apply a consensus result to the environment. Given an environment, a
  /// process id, a consensus result, and a function to apply the effect, return
  /// a new environment with the state of the process updated with the state
  /// from result plus the effects from the result's output applied.
  pure def update_state(
    env: Environment[p, s, m, te, b],
    v: p,
    res: ConsensusResult[LocalState[p, s], o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): Environment[p, s, m, te, b] = {
    val new = { ...env, system: env.system.set(v, res.state) }
    apply_effect(new, v, res.output)
  }
}

module CSMIHelpers {
  import basicSpells.* from "basicSpells"
  import CSMITypes.*
  import CSMIInternal.*

  /// Given an environment and a function to update the bookkeeping,
  /// return a new environment with the bookkeeping updated.
  ///
  /// Use it like:
  /// ```
  /// CSMI::bookkeep(env, b => { ...b, my_counter: b.my_counter + 1 })
  /// ```
  pure def bookkeep(env: Environment[p, s, m, te, b], f: b => b): Environment[p, s, m, te, b] = {
    { ...env, bookkeeping: f(env.bookkeeping) }
  }

  /// Given an environment and a message, return a new environment with the message
  /// added to the message buffer of all processes.
  pure def broadcast(env: Environment[p, s, m, te, b], msg: m): Environment[p, s, m, te, b] = {
    { ...env, msgBuffer: env.msgBuffer.transformValues(v => v.setAdd(msg)) }
  }

  /// Given an environment, a process id and a timeout event, return a new environment
  /// with the timeout event added to the active timeouts of the process.
  pure def timeout(
    env: Environment[p, s, m, te, b],
    v: p,
    timeout: te,
  ): Environment[p, s, m, te, b] = {
    { ...env, activeTimeouts: env.activeTimeouts.setBy(v, ts => ts.setAdd(timeout)) }
  }

  /// Given an environment and a process id, return the set of active timeouts
  /// for the process.
  pure def get_timeouts(
    env: Environment[p, s, m, te, b],
    v: p,
  ): Set[te] = {
    env.activeTimeouts.get(v)
  }

  /// Given an environment and a process id, return a new environment
  /// where the process has no active timeouts.
  pure def reset_timeouts(
    env: Environment[p, s, m, te, b],
    v: p,
  ): Environment[p, s, m, te, b] = {
    { ...env, activeTimeouts: env.activeTimeouts.set(v, Set()) }
  }

  /// Join two consensus results. Given two consensus results, return a new
  /// consensus result with the state of the second result and the output
  /// of the first result plus the output of the second result.
  pure def join_results(
    res1: ConsensusResult[LocalState[p, s], o],
    res2: ConsensusResult[LocalState[p, s], o]
  ): ConsensusResult[LocalState[p, s], o] = {
    { state: res2.state, output: res1.output.union(res2.output) }
  }

  /// Chain two consensus operations together. Given the result of a consensus
  /// operation and another consensus operation, call the second operation with
  /// the state of the first operation and return a new result with the outputs
  /// combined.
  ///
  /// Use it like:
  /// ```
  /// import CSMI.and_then from "csmi"
  /// pure def foo(state: LocalState): ConsensusResult = { ... }
  /// pure def bar(state: LocalState): ConsensusResult = { ... }
  //
  /// pure def my_op(state: LocalState): ConsensusResult = {
  ///   foo.and_then(bar)
  /// }
  /// ```
  pure def and_then(
    res: ConsensusResult[LocalState[p, s], o],
    f: (LocalState[p, s]) => ConsensusResult[LocalState[p, s], o]
  ): ConsensusResult[LocalState[p, s], o] = {
    pure val new_res = f(res.state)
    join_results(res, new_res)
  }

  /// A estetic operator to allow symmetry with `and_then`. This is similar to
  /// `and_then` but it takes a simple state instead of a full consensus result
  /// as the first param.
  ///
  /// Use it like:
  /// ```
  /// import CSMI.and_then_state from "csmi"
  /// pure def foo(state: LocalState): ConsensusResult = { ... }
  ///
  /// pure def my_op(state: LocalState): ConsensusResult = {
  ///   { ...state, my_field: 42 }.and_then_state(foo)
  /// }
  /// ```
  ///
  /// This is also helpful so you don't have to create variables like `state2`
  /// or `stateAfterUpdate`.
  /// Before:
  /// ```
  /// pure val state2 = { ...state, my_field: 42 }
  /// pure val my_value = compute_something(state2)
  /// foo({ ...state2, other_field: my_value })
  /// ```
  /// After:
  /// ```
  /// { ...state, my_field: 42 }.and_then_state(s => {
  ///  val my_value = compute_something(s)
  ///  foo({ ...s, other_field: my_value })
  /// })
  pure def and_then_state(
    state: LocalState[p, s],
    f: (LocalState[p, s]) => r
  ): r = {
    f(state)
  }

  /// Return a state with no output. Instead of writing:
  /// ```
  /// if (something)
  ///   foo(s)
  /// else
  ///  // do nothing
  ///  { state: s, output: Set() }
  /// ```
  /// You can write:
  /// ```
  /// if (something)
  ///   foo(s)
  /// else
  ///   CSMI::no_output(s)
  /// ```
  /// To make things more explicit.
  pure def no_output(s: LocalState[p, s]): ConsensusResult[LocalState[p, s], o] = {
    { state: s, output: Set() }
  }
}

module CSMIState {
  import basicSpells.* from "basicSpells"
  import CSMITypes.*
  import CSMIInternal.*

  // FIXME: I think this will not work with Apalache. However, I can't test this as this is resulting in a
  // huge spec once we resolve type aliases as the types are too complex. This exceeds the gRPC limit which
  // is already quite high.
  // My alternative approach (sending processes as a param in init and step) is not working due to some
  // weird effect error on step.
  const processes: Set[p]

  /// A single variable to store the whole state
  var s: Environment

  /// Initialize a system with a given operator to initialize each processes state, a set of initial
  /// messages and a bookkeeping state.
  ///
  /// This specification is event triggered, so a process step can only be
  /// triggered by a message or a timeout as a result we need either messages or
  /// timeouts in the initial state.
  ///
  /// Use it like:
  /// ```
  /// pure def initialize_process(p: ProcessID): LocalState = {
  ///   { process_id: p, field1: 0, field2: "" }
  /// }
  ///
  /// action init = CSMI::init(initialize_process, Set(Hello(1)), { foo: 0, bar: "" })
  /// ```
  action init(
    initialize_process: (p) => LocalState[p, s],
    initial_messages: Set[m],
    initial_bookkeeping: b
  ): bool = all {
    s' = {
      system: processes.mapBy(v => initialize_process(v)),
      msgBuffer: processes.mapBy(v => initial_messages),
      // TODO parameterize this, some protocols might want to start with timeouts.
      activeTimeouts: processes.mapBy(_ => Set()),
      bookkeeping: initial_bookkeeping,
    }
  }

  //
  // Standard interleaving semantics (one process receives one message/timeout in one action)
  //

  /// Given an environment, a process id, a message, and the receive_message and apply_effect
  /// operators, return a new environment with the message consumed and result applied.
  pure def consume_message(
    env: Environment[p, s, m, te, b],
    v: p,
    msg: m,
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b],
  ): Environment[p, s, m, te, b] = {
    val consumed_msg_env = {
      ...env,
      msgBuffer: env.msgBuffer.setBy(v, b => b.exclude(Set(msg)))
    }
    val res = env.system.get(v).receive_message(msg)
    update_state(consumed_msg_env, v, res, apply_effect)
  }

  /// Given an environment, a process id, a timeout event, and the fire_timeout_event and apply_effect
  /// operators, return a new environment with the timeout event consumed and the result applied.
  pure def consume_timeout_event(
    env: Environment[p, s, m, te, b],
    v: p,
    timeout: te,
    fire_timeout_event: FireTimeoutEvent[p, s, te, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): Environment[p, s, m, te, b] = {
    val consumed_timeout_env = {
      ...env,
      activeTimeouts: env.activeTimeouts.setBy(v, ts => ts.exclude(Set(timeout)))
    }
    val res = consumed_timeout_env.system.get(v).fire_timeout_event(timeout)
    update_state(consumed_timeout_env, v, res, apply_effect)
  }

  /* Actions */

  /// Given a process id, a message, and the receive_message and apply_effect
  /// operators, update the state variable with the message consumed and the result applied.
  action receive_msg(
    v: p,
    msg: m,
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
    s.msgBuffer.get(v).contains(msg),
    s' = consume_message(s, v, msg, receive_message, apply_effect)
  }

  /// Given a process id and the receive_message and apply_effect operators, non-deterministically
  /// pick a message from the process' message buffer and receive it using the operators.
  action receive_some_msg(
    v: p,
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
    s.msgBuffer.get(v) != Set(),
    nondet msg = oneOf(s.msgBuffer.get(v))
    receive_msg(v, msg, receive_message, apply_effect)
  }


  /// Given a process id, a timeout event, and the fire_timeout_event and apply_effect
  /// operators, update the state variable with the timeout event consumed and the result applied.
  action fire_timeout(
    v: p,
    timeout: te,
    fire_timeout_event: FireTimeoutEvent[p, s, te, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
    s.activeTimeouts.get(v).contains(timeout),
    s' = consume_timeout_event(s, v, timeout, fire_timeout_event, apply_effect)
  }

  /// Given a process id and the fire_timeout_event and apply_effect operators, non-deterministically
  /// pick a timeout event from the process' active timeouts and fire it using the operators.
  action fire_some_timeout(
    v: p,
    fire_timeout_event: FireTimeoutEvent[p, s, te, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
    s.activeTimeouts.get(v) != Set(),
    nondet t = oneOf(s.activeTimeouts.get(v))
    fire_timeout(v, t, fire_timeout_event, apply_effect)
  }

  /// Given the receive_message, fire_timeout_event and apply_effect operators,
  /// and a number between 0 and 100 to determine the chance of a timeout,
  /// either receive a message or fire a timeout event. The action is non-deterministic.
  ///
  /// Notes on the timeout chance:
  /// - 0 means timeouts are impossible, not unlikely
  /// - This is only relevant for random simulation. Model checking
  /// considers all paths, so probablity doesn't matter.
  ///
  /// Use it like:
  /// ```
  /// action step = CSMI::step(receive_message, fire_timeout_event, apply_effect, 50)
  /// ```
  action step(
    receive_message: ReceiveMessage[p, s, m, o],
    fire_timeout_event: FireTimeoutEvent[p, s, te, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b],
    timeout_chance: int // between 0 and 100
  ): bool = {
    nondet timeout_frequency_control = 1.to(100).oneOf()
    val messages_exist = s.msgBuffer.values().flatten() != Set()
    if ((timeout_frequency_control <= timeout_chance or not(messages_exist)) and s.activeTimeouts.values().flatten() != Set())
      all {
        // pick a process that has an active timeout
        nondet v = oneOf(processes.filter(v => s.activeTimeouts.get(v) != Set()))
        fire_some_timeout(v, fire_timeout_event, apply_effect)
      }
    else
      all {
        messages_exist,
        // pick a process that has a message available in its buffer
        nondet v = oneOf(processes.filter(v => s.msgBuffer.get(v) != Set()))
        receive_some_msg(v, receive_message, apply_effect)
      }
  }

  /// A version of `step` with no timeouts. It's equivalent to calling `step` with
  /// a timeout chance of 0, but more performant.
  action step_no_timeout(
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
    s.msgBuffer.values().flatten() != Set(),
    // pick a process that has a message available in its buffer
    nondet v = oneOf(processes.filter(v => s.msgBuffer.get(v) != Set()))
    receive_some_msg(v, receive_message, apply_effect)
  }

  //
  // Accelerated semantics (multiple process may receive multiple messages/timeouts in one action)
  //

  /// Given the receive_message and apply_effect operators, receive a subset of
  /// messages from the message buffer of all processes and apply the effects
  /// incrementally to the environment, all in a single action.
  action receive_msg_accelerated(
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
    nondet msgs = processes.map(v =>
      s.msgBuffer.get(v).powerset().exclude(Set(Set())).map(m => (v, m))
    ).flatten().powerset().oneOf()
    val deliver = msgs.setToMap()
    s' = deliver.keys().fold(s, (s, v) =>
      deliver.get(v).fold(
        s,
        (s2, msg) => consume_message(s, v, msg, receive_message, apply_effect))
    )
  }

  /// Given the fire_timeout_event and apply_effect operators, receive a subset of
  /// timeout events from the active timeouts of all processes and apply the effects
  /// incrementally to the environment, all in a single action.
  action receive_timeout_accelerated(
    fire_timeout_event: FireTimeoutEvent[p, s, te, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b]
  ): bool = all {
     nondet timeouts = processes.map(v =>
       s.activeTimeouts.get(v).powerset().exclude(Set(Set())).map(t => (v, t))
     ).flatten().powerset().oneOf()
     val deliver = timeouts.setToMap()
     s' = deliver.keys().fold(s, (s, v) =>
       deliver.get(v).fold(s, (s2, timeout) =>
         consume_timeout_event(s2, v, timeout, fire_timeout_event, apply_effect)
       )
     )
  }

  /// Given the receive_message, fire_timeout_event and apply_effect operators,
  /// and a number between 0 and 100 to determine the chance of a timeout,
  /// either receive a subset of messages from the message buffer of all processes or
  /// fire a subset of timeout events from the active timeouts of all processes
  /// and apply the effects incrementally to the environment, all in a single action.
  /// The action is non-deterministic.
  ///
  /// Notes on the timeout chance:
  /// - 0 means timeouts are impossible, not unlikely
  /// - This is only relevant for random simulation. Model checking
  /// considers all paths, so probablity doesn't matter.
  ///
  /// Use it like:
  /// ```
  /// action step = CSMI::step_accelerated(receive_message, fire_timeout_event, apply_effect, 50)
  /// ```
  action step_accelerated(
    receive_message: ReceiveMessage[p, s, m, o],
    fire_timeout_event: FireTimeoutEvent[p, s, te, o],
    apply_effect: ApplyEffect[p, s, m, te, o, b],
    timeout_chance: int // between 0 and 100
  ): bool = {
    nondet timeout_frequency_control = 1.to(100).oneOf()
    val messages_exist = s.msgBuffer.values().flatten() != Set()
    if ((timeout_frequency_control <= timeout_chance or not(messages_exist)) and s.activeTimeouts.values().flatten() != Set())
      receive_timeout_accelerated(fire_timeout_event, apply_effect)
    else
      receive_msg_accelerated(receive_message, apply_effect)
  }
}

module CSMI {
  // import from this module to get all the user-faced functionality.
  import CSMITypes.*
  import CSMIHelpers.*
  import CSMIState.*

  export CSMITypes.*
  export CSMIHelpers.*
  export CSMIState.*
}
