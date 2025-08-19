// -*- mode: Bluespec; -*-

module two_phase_commit {
  import basicSpells.* from "../../ux/set-based/lib/basicSpells"
  import glyph(processes = NODES) as glyph from "../../ux/set-based/lib/glyph"

  // --- Types ----------------------------------------------------------------
  type Node = str
  type Role = Coordinator | Participant

  type Stage = Working | Prepared | Committed | Aborted

  // Messages exchanged in 2PC
  type PrepareMsg = Node

  type Message =
    | CoordinatorAbort
    | CoordinatorCommit
    | ParticipantPrepared(Node)

  type Effect =
    | Broadcast(Message)

  type StateFields = {
    role: Role,
    stage: Stage,
  }

  type Event = ()
  type Extensions = ()


  /* Boilerplate */
  type LocalState = glyph::LocalState[Node, StateFields]
  type LocalContext = glyph::LocalContext[Message, Event, Extensions]
  type Transition = glyph::Transition[LocalState, Effect]
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
        effects: Set(Broadcast(ParticipantPrepared(s.process_id))),
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
    if (not(s.role == Coordinator and s.stage == Working and msgs.get_prepared_msgs().size() == PARTICIPANTS.size())) {
      Set()
    } else {
      Set({
        effects: Set(Broadcast(CoordinatorCommit)),
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
        effects: Set(Broadcast(CoordinatorAbort)),
        post_state: { ...s, stage: Aborted }
      })
    }
  }

  pure def main_listener(
    s: LocalState,
    c: LocalContext
  ): Set[Transition] = {
    Set(
      spontaneously_prepares(s, c.messages),
      spontaneously_aborts(s, c.messages),
      aborts_as_instructed(s, c.messages),
      commits_as_instructed(s, c.messages),
      decides_on_commit(s, c.messages),
      decides_on_abort(s, c.messages)
    ).flatten()
  }

  pure def apply_effect(env: GlobalContext, v: Node, tr: Transition): GlobalContext = {
    val env1 = { ...env, system: env.system.setBy(v, s => tr.post_state) }
    tr.effects.fold(env1, (e, x) => {
      match x {
        | Broadcast(m) => {
          { ...e, messages: e.messages.transformValues(b => b.setAdd(m)) }
        }
      }
    })
  }

  val COORDINATOR: Node = "c"
  val PARTICIPANTS: Set[Node] = Set("p1", "p2", "p3")
  pure val NODES = PARTICIPANTS.union(Set(COORDINATOR))

  def initialize(n: Node): LocalState = {
    val role = if (n == COORDINATOR) Coordinator else Participant
    {
      process_id: n,
      role: role,
      stage: Working,
    }
  }

  action init = glyph::init({
    system: NODES.mapBy(n => initialize(n)),
    messages: NODES.mapBy(n => Set()),
    events: NODES.mapBy(n => Set()),
    extensions: ()
  })

  action step = glyph::step(
    main_listener,
    apply_effect,
    (e, p) => e, // env to local context,
    Set() // more byzantines
  )

  val consistency = PARTICIPANTS.forall(p1 => {
    PARTICIPANTS.forall(p2 => {
      not(glyph::s.system.get(p1).stage == Committed
        and glyph::s.system.get(p2).stage == Aborted)
    })
  })

  val wit_commit = PARTICIPANTS.exists(p => glyph::s.system.get(p).stage != Committed)
}
