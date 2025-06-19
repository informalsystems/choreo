module draft {
  type LocalState = { received_hellos: Set[str] }
  type Result = { state: LocalState, effects: Set[Effect] }

  type Message = Hello(str) | Goodbye
  type CustomEffect = Finish | Dummy
  // should be imported/instantiated from lib later
  type Effect = Broadcast(Message) | Custom(CustomEffect)
  type MessageWithDestinatary = { destinatary: str, content: Message }
  type GlobalState = { messages: Set[MessageWithDestinatary], finished: bool }

  pure def receive_message(s: LocalState, m: Message): Result = {
    match m {
      | Hello(greeter) =>
        pure val s1 = { ...s, received_hellos: s.received_hellos.union(Set(greeter)) }
        if (s1.received_hellos.size() >= 3)
          { state: s1, effects: Set(Broadcast(Goodbye)) }
        else
          { state: s1, effects: Set() }

      | Goodbye =>
        { state: s, effects: Set(Custom(Finish)) }
    }
  }

  pure def apply_custom_effect(global_state: GlobalState, effect: CustomEffect): GlobalState = {
    match effect {
      | Finish => { ...global_state, finished: true }
      | Dummy => global_state
    }
  }
}

module interleavings {
  import draft.*

  var states: str -> LocalState
  var global_state: GlobalState

  pure val processes = Set("p1", "p2", "p3", "p4")

  pure def apply_effect(global_state: GlobalState, effect: Effect): GlobalState = {
    match effect {
      | Broadcast(m) => { ...global_state, messages: global_state.messages.union(processes.map(p => {
          destinatary: p, content: m
        }))}
      | Custom(e) => global_state.apply_custom_effect(e)
    }
  }


  // initial state and messages need to be provided by user
  action init = all {
    states' = processes.mapBy(p => { received_hellos: Set() }),
    global_state' = {
      messages: processes.map(p => { destinatary: "p1", content: Hello(p) }),
      finished: false,
    }
  }

  // Only external interlavings: only make a transition when an effect is found
  action step = {
    nondet process = processes.oneOf()
    // depends on network config.
    // i.e. for at-least-once delivery, we can use allListsUpTo(messages.size())
    //      for exactly-once, we need a non-deterministic order and then we iterate
    //      for at-most-once, we can use powerset. In this case, we need to remove the message from the soup when making a transition

    // TODO: non-deterministic order
    val msgs = global_state.messages.filter(m => m.destinatary == process).map(m => m.content)
    val initial = { state: states.get(process), effects: Set() }
    val result = msgs.fold(initial, (accumulated_result, message) => {
      // Stop after finding the first effect
      if (accumulated_result.effects != Set()) accumulated_result else

      accumulated_result.state.receive_message(message)
    })
    all {
      not(global_state.finished), // only for this draft, as I want a finite state space
      result.effects != Set(),
      states' = states.set(process, result.state),
      global_state' = result.effects.fold(global_state, (s, e) => s.apply_effect(e))
    }
  }

  // Message-by-message interlavings
  action step_message_by_message = {
    nondet process = processes.oneOf()
    val msgs = global_state.messages.filter(m => m.destinatary == process)
    nondet message = msgs.oneOf()
    val result = states.get(process).receive_message(message.content)
    all {
      states' = states.set(process, result.state),
      global_state' = result.effects.fold(
        // Without message removal:
        // global_state
        // With message removal:
        { ...global_state, messages: global_state.messages.exclude(Set(message)) },
        (s, e) => s.apply_effect(e))
    }
  }
}
