// -*- mode: Bluespec; -*-

/**
 * Quint Glyphs, a library for delightful specifications
 * of distributed systems.
 *
 * Gabriela Moreira, Josef Widder and Yassine Boukhari,
 * Informal Systems, 2025
 */

module glyphsBase {
  import basicSpells.* from "basicSpells"

  type LocalState[process_id, message, other_fields] = {
    process_id: process_id,
    message_buffer: Set[message] // can be moved to GlobalState
    //internal_events_buffer: Set[e] 
    | other_fields
  }

  type ListenerOutput[state, effect] = {
    effects: Set[effect],
    state: state,
  }

  type GlobalState[p, s, m, b] = {
    system: p -> LocalState[p, m, s],
    logging: b
  }

  // This is the message routing to the # handler
  type Listener[p, s, m, o] = (LocalState[p, m, s], Set[m]) => Set[ListenerOutput[LocalState[p, m, s], o]]

  type ApplyEffect[p, s, m, o, b] =
    (GlobalState[p, s, m, b], p, Set[o]) => GlobalState[p, s, m, b]
  
  pure def logging(env: GlobalState[p, s, m,  b], f: b => b): GlobalState[p, s, m, b] = {
    { ...env, logging: f(env.logging)}
  }

}

module glyphNetwork {

  import basicSpells.* from "basicSpells"
  import glyphsBase.*

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

module glyphDriver {
  import basicSpells.* from "basicSpells"
  import glyphsBase.*

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


  action step(
    ev_listener: Listener[p, s, m, o],
    apply_effect: ApplyEffect[p, s, m, o, b]
  ): bool = {
    nondet process = oneOf(processes.filter(v => s.system.get(v).message_buffer != Set()))
    val msgs = s.system.get(process).message_buffer
    val initial = s.system.get(process)
    val valid_transitions = ev_listener(initial, msgs)
    all {
      valid_transitions != Set(),
      // choose one of the valid transitions
      nondet transition = oneOf(valid_transitions)
      // apply the effects of the transition
      val gs = apply_effect(s, process, transition.effects)
      val gs1 = {...gs, system: gs.system.put(process, q::debug("test",transition.state))}
      s' = gs1
    }
  }
}
