module two_phase_commit {
  import basicSpells.* from "lib/basicSpells"

  // --- Types ----------------------------------------------------------------
  type TransactionId = int
  type Value = str
  type Node = str
  type Role = Coordinator | Participant

  type Stage =
    | InitStage           // before any messages
    | PrepareStage        // coordinator has sent Prepare
    | WaitPrepareStage    // participant waiting for Prepare
    | VoteStage           // participant has sent Vote
    | WaitVoteStage       // coordinator waiting for Votes
    | CommitStage         // coordinator sent Commit or Abort
    | DecidedStage        // participant has received decision

  // Messages exchanged in 2PC
  type PrepareMsg = { src: Node, tx: TransactionId }
  type VoteMsg    = { src: Node, tx: TransactionId, vote: bool }
  type DecisionMsg= { src: Node, tx: TransactionId, commit: bool }

  type Message =
    | Prepare(PrepareMsg)
    | Vote(VoteMsg)
    | Decision(DecisionMsg)

  // Effects: broadcast, start timeouts, logging
  type ExternalEffect = Broadcast(Message)
  type InternalEffect = StartTimeout({ tx: TransactionId, stage: Stage })
  type LoggingEffect  = CollectEvidence(Message)

  type Effect =
    | Ext(ExternalEffect)
    | Inter(InternalEffect)
    | Log(LoggingEffect)

  type LocalState = {
    process_id: Node,
    role: Role,
    tx: TransactionId,
    value: Option[Value],    // only coordinator holds proposed value
    stage: Stage,
    message_buffer: Set[Message],
    votes: Node -> bool,  // collected votes
    decision: Option[bool],  // true=commit, false=abort
  }

  type ListenerOutput = { effects: Set[Effect], state: LocalState }

  pure def get_proposals
  pure def get_votes(msgs: Set[Message]): Set[VoteMsg] =
    msgs.filterMap(m => match m { | Vote(v) => Some(v) | _ => None })

  // --- Participant: on Prepare ----------------------------------------------
  pure def on_wait_prepare(
    s: LocalState,
    msgs: Set[Message]
  ): Set[ListenerOutput] = {
    val state_guard = s.stage == WaitPrepareStage
    // filter Prepare for our tx
    val preps = msgs.filterMap(m => match m {
      | Prepare(p) if p.tx == s.tx => Some(p)
      | _ => None
    })
    if state_guard and preps.size() == 1 {
      val p = preps.head
      // decide locally whether to commit; user-defined canCommit
      val can_commit = TRUE  // replace with application check
      val vote_msg = Vote({ src: s.process_id, tx: s.tx, vote: can_commit })
      val new_stage = VoteStage
      val effs = Set(
        Log(CollectEvidence(Prepare(p))),
        Ext(Broadcast(vote_msg))
      )
      Set({ effects: effs, state: { ...s, stage: new_stage } })
    } else {
      Set()
    }
  }

  // --- Coordinator: on Init -> send Prepare ------------------------------
  pure def on_init_coordinator(
    s: LocalState,
    _: Set[Message]
  ): Set[ListenerOutput] = {
    if s.role == "Coordinator" and s.stage == InitStage {
      val prep = Prepare({ src: s.process_id, tx: s.tx })
      val effs = Set(
        Log(CollectEvidence(prep)),
        Ext(Broadcast(prep)),
        Inter(StartTimeout({ tx: s.tx, stage: WaitVoteStage }))
      )
      Set({ effects: effs, state: { ...s, stage: WaitVoteStage } })
    } else {
      Set()
    }
  }

  // --- Coordinator: on Votes quorum -----------------------------------------
  pure def on_wait_votes(
    s: LocalState,
    msgs: Set[Message]
  ): Set[ListenerOutput] = {
    val state_guard = s.stage == WaitVoteStage
    if not(state_guard) then Set() else {
      val votes = get_votes(msgs)
      val by_nodes = votes.map(v => v.src).set()
      // assume participants = ALL minus coordinator
      val expected = NODES.remove(s.process_id)
      if by_nodes.size() >= expected.size() {
        // quorum received from all participants
        // abort if any vote==false
        val commit_decision = votes.forall(v => v.vote)
        val decision_msg = Decision({ src: s.process_id, tx: s.tx, commit: commit_decision })
        val effs = Set(
          Log(CollectEvidence(decision_msg)),
          Ext(Broadcast(decision_msg))
        )
        val new_stage = CommitStage
        Set({ effects: effs, state: { ...s, stage: new_stage, decision: Some(commit_decision) } })
      } else {
        Set()
      }
    }
  }

  // --- Participant: on Decision ---------------------------------------------
  pure def on_receive_decision(
    s: LocalState,
    msgs: Set[Message]
  ): Set[ListenerOutput] = {
    val state_guard = s.stage == VoteStage
    if not(state_guard) then Set() else {
      val decs = msgs.filterMap(m => match m {
        | Decision(d) if d.tx == s.tx => Some(d)
        | _ => None
      })
      if decs.size() == 1 {
        val d = decs.head
        // apply or rollback based on d.commit (true=commit)
        // user can hook application logic here
        val new_stage = DecidedStage
        val effs = Set(Log(CollectEvidence(Decision(d))))
        Set({ effects: effs, state: { ...s, stage: new_stage, decision: Some(d.commit) } })
      } else {
        Set()
      }
    }
  }

  // --- Main Listener --------------------------------------------------------
  pure def main_listener(
    s: LocalState,
    msgs: Set[Message]
  ): Set[ListenerOutput] = {
    Set(
      on_init_coordinator(s, msgs),
      on_wait_prepare(s, msgs),
      on_wait_votes(s, msgs),
      on_receive_decision(s, msgs)
    ).flatten().filter(o => o.effects.size() > 0 or o.state != s)
  }

  // --- Initialization ------------------------------------------------------
  val COORDINATOR: Node = "c"
  val PARTICIPANTS: Set[Node] = Set("p1", "p2")
  pure val NODES = PARTICIPANTS.union(Set(COORDINATOR))

  def initialize(n: Node, tx: TransactionId, value: Option[Value]): LocalState = {
    let role = if n == COORDINATOR then "Coordinator" else "Participant"
    {
      process_id: n,
      role: role,
      tx: tx,
      value: value,
      stage: InitStage,
      message_buffer: Set(),
      votes: Map(),
      decision: None,
    }
  }
}
