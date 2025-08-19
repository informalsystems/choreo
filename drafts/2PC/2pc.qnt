// -*- mode: Bluespec; -*-

module two_phase_commit {
  import basicSpells.* from "../../ux/set-based/lib/basicSpells"
  import glyph(processes = NODES) as glyph from "../../ux/set-based/lib/glyph"

  // Auxiliary types
  type Role = Coordinator | Participant
  type Stage = Working | Prepared | Committed | Aborted

  // Mandatory types for the Glyph
  type Node = str
  type Message =
    | CoordinatorAbort
    | CoordinatorCommit
    | ParticipantPrepared(Node)

  type StateFields = {
    role: Role,
    stage: Stage,
  }

  type CustomEffects = ()
  type Event = ()
  type Extensions = ()

  /* Boilerplate */
  type LocalState = glyph::LocalState[Node, StateFields]
  type LocalContext = glyph::LocalContext[Message, Event, Extensions]
  type Transition = glyph::Transition[Node, StateFields, Message, CustomEffects]
  type GlobalContext = glyph::GlobalContext[
    Node,
    StateFields,
    Message,
    Event,
    Extensions
  ]
  /* End of boilerplate */

  pure def get_prepared_msgs(msgs: Set[Message]): Set[Node] = {
    msgs.filterMap(m => match m {
      | ParticipantPrepared(n) => Some(n)
      | _ => None
    })
  }

  // --- Participant transitions ----------------------------------------------
  pure def spontaneously_prepares(s: LocalState, msgs: Set[Message]): Set[Transition] = {
    if (not(s.role == Participant and s.stage == Working)) {
      Set()
    } else {
      Set({
        effects: Set(glyph::Broadcast(ParticipantPrepared(s.process_id))),
        post_state: { ...s, stage: Prepared }
      })
    }
  }

  pure def spontaneously_aborts(s: LocalState, msgs: Set[Message]): Set[Transition] = {
    if (not(s.role == Participant and s.stage == Working)) {
      Set()
    } else {
      Set({
        effects: Set(),
        post_state: { ...s, stage: Aborted }
      })
    }
  }

  pure def aborts_as_instructed(s: LocalState, msgs: Set[Message]): Set[Transition] = {
    if (not(s.role == Participant and msgs.contains(CoordinatorAbort))) {
      Set()
    } else {
      Set({
        effects: Set(),
        post_state: { ...s, stage: Aborted }
      })
    }
  }

  pure def commits_as_instructed(s: LocalState, msgs: Set[Message]): Set[Transition] = {
    if (not(s.role == Participant and msgs.contains(CoordinatorCommit))) {
      Set()
    } else {
      Set({
        effects: Set(),
        post_state: { ...s, stage: Committed }
      })
    }
  }

  // --- Coordinator transitions ------------------------------
  pure def decides_on_commit(
    s: LocalState,
    msgs: Set[Message]
  ): Set[Transition] = {
    if (not(
      s.role == Coordinator
        and s.stage == Working
        and msgs.get_prepared_msgs().size() == PARTICIPANTS.size()
    )) {
      Set()
    } else {
      Set({
        effects: Set(glyph::Broadcast(CoordinatorCommit)),
        post_state: { ...s, stage: Committed }
      })
    }
  }

  pure def decides_on_abort(
    s: LocalState,
    msgs: Set[Message]
  ): Set[Transition] = {
    if (not(s.role == Coordinator and s.stage == Working)) {
      Set()
    } else {
      Set({
        effects: Set(glyph::Broadcast(CoordinatorAbort)),
        post_state: { ...s, stage: Aborted }
      })
    }
  }

  pure def main_listener(s: LocalState, c: LocalContext): Set[Transition] = {
    Set(
      spontaneously_prepares(s, c.messages),
      spontaneously_aborts(s, c.messages),
      aborts_as_instructed(s, c.messages),
      commits_as_instructed(s, c.messages),
      decides_on_commit(s, c.messages),
      decides_on_abort(s, c.messages)
    ).flatten()
  }

  pure val COORDINATOR: Node = "c"
  pure val PARTICIPANTS: Set[Node] = Set("p1", "p2", "p3")
  pure val NODES = PARTICIPANTS.union(Set(COORDINATOR))

  pure def initialize(n: Node): LocalState = {
    {
      process_id: n,
      role: if (n == COORDINATOR) Coordinator else Participant,
      stage: Working,
    }
  }

  // Setting up the state machine

  action init = glyph::init({
    system: NODES.mapBy(n => initialize(n)),
    messages: NODES.mapBy(n => Set()),
    events: NODES.mapBy(n => Set()),
    extensions: ()
  })

  action step = glyph::step(
    main_listener,
    (c, _) => c,
    (e, p) => e, // env to local context,
    Set() // more byzantines
  )

  // Invariants and witnesses

  val consistency = PARTICIPANTS.forall(p1 => {
    PARTICIPANTS.forall(p2 => {
      not(glyph::s.system.get(p1).stage == Committed
        and glyph::s.system.get(p2).stage == Aborted)
    })
  })

  val wit_commit = PARTICIPANTS.exists(p => glyph::s.system.get(p).stage != Committed)
}
