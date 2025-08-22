// -*- mode: Bluespec; -*-

module two_phase_commit {
  import basicSpells.* from "../../spells/basicSpells"
  import glyph(processes = NODES) as glyph from "../../set-based/glyph"

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
  type LocalContext = glyph::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition = glyph::Transition[Node, StateFields, Message, Event, CustomEffects]
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
  pure def spontaneously_prepares(ctx: LocalContext): Set[Transition] = {
    if (not(ctx.state.role == Participant and ctx.state.stage == Working)) {
      Set()
    } else {
      Set({
        effects: Set(glyph::Broadcast(ParticipantPrepared(ctx.state.process_id))),
        post_state: { ...ctx.state, stage: Prepared }
      })
    }
  }

  pure def spontaneously_aborts(ctx: LocalContext): Set[Transition] = {
    if (not(ctx.state.role == Participant and ctx.state.stage == Working)) {
      Set()
    } else {
      Set({
        effects: Set(),
        post_state: { ...ctx.state, stage: Aborted }
      })
    }
  }

  pure def aborts_as_instructed(ctx: LocalContext): Set[Transition] = {
    if (not(ctx.state.role == Participant and ctx.messages.contains(CoordinatorAbort))) {
      Set()
    } else {
      Set({
        effects: Set(),
        post_state: { ...ctx.state, stage: Aborted }
      })
    }
  }

  pure def commits_as_instructed(ctx: LocalContext): Set[Transition] = {
    if (not(ctx.state.role == Participant and ctx.messages.contains(CoordinatorCommit))) {
      Set()
    } else {
      Set({
        effects: Set(),
        post_state: { ...ctx.state, stage: Committed }
      })
    }
  }

  // --- Coordinator transitions ------------------------------
  pure def decides_on_commit(ctx: LocalContext): Set[Transition] = {
    if (not(
      ctx.state.role == Coordinator
        and ctx.state.stage == Working
        and ctx.messages.get_prepared_msgs().size() == PARTICIPANTS.size()
    )) {
      Set()
    } else {
      Set({
        effects: Set(glyph::Broadcast(CoordinatorCommit)),
        post_state: { ...ctx.state, stage: Committed }
      })
    }
  }

  pure def decides_on_abort(ctx: LocalContext): Set[Transition] = {
    if (not(ctx.state.role == Coordinator and ctx.state.stage == Working)) {
      Set()
    } else {
      Set({
        effects: Set(glyph::Broadcast(CoordinatorAbort)),
        post_state: { ...ctx.state, stage: Aborted }
      })
    }
  }

  pure def main_listener(input: LocalContext): Set[Transition] = {
    Set(
      spontaneously_prepares(input),
      spontaneously_aborts(input),
      aborts_as_instructed(input),
      commits_as_instructed(input),
      decides_on_commit(input),
      decides_on_abort(input)
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
  )

  // Invariants and witnesses

  val consistency = PARTICIPANTS.forall(p1 => {
    PARTICIPANTS.forall(p2 => {
      not(glyph::s.system.get(p1).stage == Committed
        and glyph::s.system.get(p2).stage == Aborted)
    })
  })

  val wit_commit = PARTICIPANTS.exists(p => glyph::s.system.get(p).stage != Committed)

  action step_with(v: Node, listener: LocalContext => Set[Transition]): bool =
    glyph::step_with(v, listener, (c, _) => c, (e, p) => e)

  run commitTest = init
    .then(step_with("p1", spontaneously_prepares))
    .then(step_with("p2", spontaneously_prepares))
    .then(step_with("p3", spontaneously_prepares))
    .then(step_with(COORDINATOR, decides_on_commit))
    .then(step_with("p1", commits_as_instructed))
    .then(step_with("p2", commits_as_instructed))
    .then(step_with("p3", commits_as_instructed))
    .expect({
      // Check that all participants have committed
      PARTICIPANTS.forall(p => {
        glyph::s.system.get(p).stage == Committed
      })
    })
}
