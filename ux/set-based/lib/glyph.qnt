// -*- mode: Bluespec; -*-

/**
 * Quint Glyphs, a library for delightful specifications
 * of distributed systems.
 *
 * Gabriela Moreira, Josef Widder and Yassine Boukhari,
 * Informal Systems, 2025
 */

module glyph {
  import basicSpells.* from "basicSpells"

  type LocalState[process_id, ext] = {
    process_id: process_id
    | ext
  }

  type Transition[state, effect] = {
    post_state: state,
    effects: Set[effect],
  }

  type GlobalContext[p, s, m, e, ext] = {
    system: p -> LocalState[p, s],
    messages: p -> Set[m],
    events: p -> Set[e],
    extensions: ext
  }

  type LocalContext[m, e, ext] = {
    messages: Set[m],
    events: Set[e],
    extensions: ext
  }

  // This is the message routing to the # handler
  type Listener[p, s, m, e, ef, ext] =
    (LocalState[p, s], LocalContext[m, e, ext]) => Set[Transition[LocalState[p, s], ef]]

  type EffectProcessor[p, s, m, e, ef, ext] =
    (GlobalContext[p, s, m, e, ext], p, Transition[LocalState[p, s], ef]) => GlobalContext[p, s, m, e, ext]

  type ExtensionsConverter[p, l, g] =
    (g, p) => l

  pure def broadcast(
    env: GlobalContext[p, s, m, e, ext],
    msg: m
  ): GlobalContext[p, s, m, e, ext] = {
    { ...env,
      messages: env.messages.transformValues(s => s.setAdd(msg))
    }
  }

  pure def send(
    env: GlobalContext[p, s, m, e, ext],
    v: p,
    msg: m
  ): GlobalContext[p, s, m, e, ext] = {
    { ...env,
      messages: env.messages.setBy(v, s => s.setAdd(msg))
    }
  }

  const processes: Set[p]
  var s: GlobalContext[p, s, m, e, ext]

  pure def initialize(x: a, f: Option[(a) => Set[b]]): Set[b] = {
    match f {
      | Some(fun) => fun(x)
      | None => Set()
    }
  }

  pure def convert_context(
    env: GlobalContext[p, s, m, e, ext],
    v: p,
    local_to_global_extensions: ExtensionsConverter[p, ext, local_ext]
  ): LocalContext[m, e, local_ext] = {
    {
      messages: env.messages.get(v),
      events: env.events.get(v),
      extensions: local_to_global_extensions(env.extensions, v)
    }
  }

  // TODO: displayer

  action init(e: GlobalContext[p, s, m , e, ext]): bool = {
    s' = e
  }

  action step (
    listener: Listener[p, s, m, e, l, extensions],
    apply_effect: EffectProcessor[p, s, m, e, l, extensions],
    local_to_global_extensions: ExtensionsConverter[p, extensions, local_extensions],
    // displayer: Displayer[p, s, m, te, l, extensions, d],
    more_byzantines: Set[m]
  ): bool = all {
    nondet v = oneOf(processes)
    val input = convert_context(s, v, local_to_global_extensions)
    val ls = s.system.get(v)
    val transitions = listener(ls, input)
    all {
      transitions.size() > 0,
      nondet transition = oneOf(transitions)
      val post_env = apply_effect(s, v, transition)
      all {
        s' = post_env,
        // display' = displayer(post_env)
      }
    },
  }
}
