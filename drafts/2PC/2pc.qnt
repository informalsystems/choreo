// -*- mode: Bluespec; -*-

module two_phase_commit {
  import basicSpells.* from "lib/basicSpells"
  import csmi(processes = NODES) as csmi from "lib/csmi"

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

  type LocalState = csmi::LocalState[Node, {
    role: Role,
    stage: Stage,
  }]

  type LocalContext = csmi::LocalContext[Message, (), ()]
  type Transition = csmi::Transition[LocalState, Effect]

  type Environment = csmi::Environment[
    Node,
    LocalState,
    Message,
    (),
    (),
    ()
  ]

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
        postState: { ...s, stage: Prepared }
      })
    }
  }

  pure def spontaneously_aborts(s: LocalState, msgs: Set[Message]): Set[Transition] = {
    if (not(s.role == Participant and s.stage == Working)) {
      Set()
    } else {
      Set({
        effects: Set(),
        postState: { ...s, stage: Aborted }
      })
    }
  }

  pure def aborts_as_instructed(s: LocalState, msgs: Set[Message]): Set[Transition] = {
    if (not(s.role == Participant and msgs.contains(CoordinatorAbort))) {
      Set()
    } else {
      Set({
        effects: Set(),
        postState: { ...s, stage: Aborted }
      })
    }
  }

  pure def commits_as_instructed(s: LocalState, msgs: Set[Message]): Set[Transition] = {
    if (not(s.role == Participant and msgs.contains(CoordinatorCommit))) {
      Set()
    } else {
      Set({
        effects: Set(),
        postState: { ...s, stage: Committed }
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
        postState: { ...s, stage: Committed }
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
        postState: { ...s, stage: Aborted }
      })
    }
  }

   // --- Main Listener --------------------------------------------------------
  pure def main_listener(
    s: LocalState,
    c: LocalContext
  ): Set[Transition] = {
    Set(
     spontaneously_prepares(s, c.msgBuffer),
     spontaneously_aborts(s, c.msgBuffer),
     aborts_as_instructed(s, c.msgBuffer),
     commits_as_instructed(s, c.msgBuffer),
     decides_on_commit(s, c.msgBuffer),
     decides_on_abort(s, c.msgBuffer)
    ).flatten().filter(o => o.effects.size() > 0 or o.postState != s)
  }

  pure def apply_effect(env: Environment, v: Node, tr: Transition): Environment = {
    val env1 = { ...env, system: env.system.setBy(v, s => tr.postState) }
    tr.effects.fold(env1, (e, x) => {
      match x {
        | Broadcast(m) => {
          { ...e, msgBuffer: e.msgBuffer.transformValues(b => b.setAdd(m)) }
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

  action init = csmi::init(
    initialize,
    (_) => Set(), // no initial/byzantine messages
    (_) => Set(), // no timeouts
    {
      system: Map(),
      msgBuffer: Map(),
      internalBuffer: Map(),
      logging: (),
    },
    (d) => d,
  )

  pure def env_to_local_context(env: Environment, process_id: Node): LocalContext =
    {
      msgBuffer: env.msgBuffer.getOrElse(process_id, Set()),
      internalBuffer: env.internalBuffer.getOrElse(process_id, Set()),
    }

  action step = csmi::step(
    main_listener,
    apply_effect,
    env_to_local_context, // env to local context,
    (d) => d, // displayer
    Set() // more byzantines
  )

  val consistency = PARTICIPANTS.forall(p1 => {
    PARTICIPANTS.forall(p2 => {
      not(csmi::s.system.get(p1).stage == Committed
        and csmi::s.system.get(p2).stage == Aborted)
    })
  })

  val wit_commit = PARTICIPANTS.exists(p => csmi::s.system.get(p).stage != Committed)
}
