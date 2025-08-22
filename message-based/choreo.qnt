// -*- mode: Bluespec; -*-

/**
 * Quint Choreos, a library for delightful specifications
 * of distributed systems.
 *
 * Gabriela Moreira, Josef Widder and Yassine Boukhari,
 * Informal Systems, 2025
 */

module choreosBase {
  import basicSpells.* from "../spells/basicSpells"

  type LocalState[process_id, message, other_fields] = {
    process_id: process_id,
    message_buffer: Set[message] // can be moved to GlobalState
    //internal_events_buffer: Set[e] 
    | other_fields
  }

  type HandlerOutput[state, effect] = {
    effects: Set[effect],
    state: state,
  }

  type GlobalState[p, s, m, b] = {
    system: p -> LocalState[p, m, s],
    logging: b
  }

  // This is the message routing to the # handler
  type ReceiveMessage[p, s, m, o] = (LocalState[p, m, s], m) => HandlerOutput[LocalState[p, m, s], o]

  type ApplyEffect[p, s, m, o, b] =
    (GlobalState[p, s, m, b], p, Set[o]) => GlobalState[p, s, m, b]
  
  pure def logging(env: GlobalState[p, s, m,  b], f: b => b): GlobalState[p, s, m, b] = {
    { ...env, logging: f(env.logging)}
  }

}

module choreoNetwork {
  import basicSpells.* from "../spells/basicSpells"
  import choreosBase.*

  pure def broadcast(
    env: GlobalState[p, s, m, b],
    msg: m
  ): GlobalState[p, s, m, b] = {
    { ...env,
      system: env.system.transformValues(s => { ...s, message_buffer: s.message_buffer.setAdd(msg) })
    }
  }

  pure def send(
    env: GlobalState[p, s, m, b],
    v: p,
    msg: m
  ): GlobalState[p, s, m, b] = {
    { ...env,
      system: env.system.set(v, { ...env.system.get(v), message_buffer: env.system.get(v).message_buffer.setAdd(msg) })
    }
  }

}

module choreoDriver {
  import basicSpells.* from "../spells/basicSpells"
  import choreosBase.*

  const processes: Set[p]
  var s: GlobalState[p, s, m, b]

  type InitializeProcess[p, m, s] = (p) => LocalState[p, m, s]

  action init(
    initialize_process: InitializeProcess[p, m, s],
    initial_logging: b
  ): bool = all {
    s' = {
      system: processes.mapBy(v => initialize_process(v)),
      logging: initial_logging,
    }
  }

  /// The step action applies a macro step to the system by non deterministically
  /// selecting a process and processing all messages in its buffer until an external
  /// effects is produced.
  /// The action is parameterized by a receive_message function that defines how to handle
  /// one received message and an apply_effect function that defines how to apply the effects
  /// of the message processing to the global state.
  action step(
    receive_message: ReceiveMessage[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, o, b]
  ): bool = {
    nondet process = processes.oneOf()
    val msgs = s.system.get(process).message_buffer
    val initial = { state: s.system.get(process), effects: Set() }
    
    val result = msgs.fold(initial, (accumulated_result, message) => {
      // Stop after finding the first effect
      if (accumulated_result.effects != Set()) accumulated_result 
      else {
        // accumulate the effects of the message
        val message_result = receive_message(accumulated_result.state, message)
        {
          state: message_result.state,
          effects: accumulated_result.effects.union(message_result.effects)
        }
      }
    })
    
    all {
      result.effects != Set(),
      // apply the effects to the environment
      val new_system = s.system.set(process, result.state)
      s' = apply_effect(
        { ...s, system: new_system },
        process,
        result.effects
      )
    }
  }
}
