module tender_one{

  import basicSpells.* from "lib/basicSpells"

  type Round = int
  type Stage = ProposeStage | PreVoteStage | PreCommitStage | DecidedStage
  type Value = str
  /// The ID of a value. In the implementation, this would be a hash of the value.
  /// Here, we wrap it in a record and don't convert it back into a value.
  /// This keeps the property that v1.id() == v2.id() iff v1 == v2.
  type ValueId = { hashed: Value }
  type Node = str

  type LocalState = {
    round: Round,
    stage: Stage,
    decision: Option[Value],
    locked_value: Option[Value],
    locked_round: Round,
    valid_value: Option[Value],
    valid_round: Round,
    after_prevote_for_first_time: bool,
    precommit_quorum: bool,
    messages: Set[Message],
    process_id : Node,
  }

  type ProposeMsg = {
    src: Node,
    round: Round,
    proposal: Value,
    valid_round: Round,
  }

  type PreVoteMsg = {
    src: Node,
    round: Round,
    id: Option[ValueId],
  }

  type Message =
    | Propose(ProposeMsg)
    | PreVote(PreVoteMsg)
    | PreCommit(PreVoteMsg)

  type ExternalEffect =
    | Broadcast(Message)

  type InternalEffect=
    | StartTimeout(TimeoutEvent)


   type LoggingEffect =
    | CollectEvidence(Message)
    | Breakpoint

    type Effect =
      | External(ExternalEffect)
      | Internal(InternalEffect)
      | Logging(LoggingEffect)
    
    
    /*
    type HandlerOutput = {
      state: LocalState,
      output: Set[Effect],
    }
    */

    type HandlerOutput = {
        state: LocalState,
        external: Set[ExternalEffect],
        internal: Set[InternalEffect],
        logging: Set[LoggingEffect],
    }

  type TimeoutKind = ProposeTimeout | PreVoteTimeout | PreCommitTimeout
  type TimeoutEvent = { kind: TimeoutKind, round: Round}


  pure def get_proposals(s: LocalState): Set[ProposeMsg] =
    s.messages.filterMap(m => {
      match m {
        | Propose(p) => Some(p)
        | _ => None
      }
    })

  /// All received PreVotes with a given round and value id
  pure def get_prevotes(s: LocalState, round: Round, id: Option[ValueId]): Set[PreVoteMsg] =
    s.messages.filterMap(m => {
      match m {
        | PreVote(p) => if (p.round == round and p.id == id) Some(p) else None
        | _ => None
      }
    })

  /// All received PreCommits
  pure def get_all_precommits(s: LocalState): Set[PreVoteMsg] =
    s.messages.filterMap(m => {
      match m {
        | PreCommit(p) => Some(p)
        | _ => None
      }
    })

  /// All received PreCommits with a given round and value id
  pure def get_precommits(s: LocalState, round: Round, id: ValueId): Set[PreVoteMsg] =
    s.messages.filterMap(m => {
      match m {
        | PreCommit(p) => if (p.round == round and p.id == Some(id)) Some(p) else None
        | _ => None
      }
    })
  
  /* CONSTANTS */

  /// An upper bound on the number of Byzantine processes
  const F: int
  /// The set of correct processes
  const CORRECT: Set[Node]
  /// The set of faulty processes
  const FAULTY: Set[Node]
  /// Which node is the proposer in each round
  const PROPOSER: Round -> Node
  /// Which value is proposed in each round.
  /// Values from rounds with correct nodes (in PROPOSER) are considered valid values.
  const VALUES: Round -> Value

  /// The set of all nodes
  pure val NODES = CORRECT.union(FAULTY)
  /// The set of all rounds (prepared by the constants)
  pure val ROUNDS = VALUES.keys()
  /// The set of all correct values (prepared by the constants)
  pure val VALID_VALUES = ROUNDS.filter(k => PROPOSER.get(k).in(CORRECT)).map(k => VALUES.get(k))


  pure def valid(v: Value): bool = {
    VALID_VALUES.contains(v)
  }

  /// A value hash in an abstract way.
  pure def id(v: Value): ValueId = { hashed: v }

  pure def process_proposal_at_propose_stage(s: LocalState, msg: Message): HandlerOutput = {
  pure val propose_msg = match msg {
    | Propose(p) => Some(p)
    | _ => None
  }
  // If msg is not a proposal, return no output.
  if (propose_msg == None)  
    {state: s, external: Set(), internal: Set(), logging: Set()}
  else {
    pure val msg_val = propose_msg.unwrap()
    pure val cond = and {
      propose_msg != None,
      msg_val.valid_round == -1,
      msg_val.src == PROPOSER.get(s.round),
      s.stage == ProposeStage,
    }
    if (cond){
      pure val broadcast =
        if (msg_val.proposal.valid() and (s.locked_round == -1 or s.locked_value == Some(msg_val.proposal)))
          Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some(msg_val.proposal.id()) }))
        else Broadcast(PreVote({ src: s.process_id, round: s.round, id: None }))
      { 
        state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true},
        external: Set(broadcast),
        internal: Set(),
        logging: Set()
      }
    } else 
      {state: s, external: Set(), internal: Set(), logging: Set()}
  }
}

// Rewritten process_proposal_and_quorum_at_propose_stage
pure def process_proposal_and_quorum_at_propose_stage(s: LocalState, msg: Message): HandlerOutput = {
  pure val propose_msg = match msg {
    | Propose(p) => Some(p)
    | PreVote(pv) => s.get_proposals().find(p =>
                          p.src == PROPOSER.get(s.round) and Some(p.proposal.id()) == pv.id and p.round == pv.round
                        )
    | PreCommit(p) => None
  }
  if (propose_msg == None)  
    {state: s, external: Set(), internal: Set(), logging: Set()}
  else {
    pure val msg_val = propose_msg.unwrap()
    pure val prevotes = s.get_prevotes(s.round, Some(msg_val.proposal.id()))
    pure val cond = and {
      propose_msg != None,
      msg_val.src == PROPOSER.get(s.round),
      prevotes.map(m => m.src).size() >= 2 * F + 1,
      s.stage == ProposeStage,
      msg_val.valid_round >= 0 and msg_val.valid_round < s.round,
    }
    if (cond) {
      pure val broadcast =
        if (msg_val.proposal.valid() and (s.locked_round <= msg_val.valid_round or s.locked_value.unwrap() == msg_val.proposal))
          Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some(msg_val.proposal.id()) }))
          else Broadcast(PreVote({ src: s.process_id, round: s.round, id: None }))
      { 
        state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true },
        external: Set(broadcast), 
        logging: Set(CollectEvidence(Propose(msg_val)), Breakpoint).union(prevotes.map(m => CollectEvidence(PreVote(m)))),
        internal: Set()
      }
    } else 
      {state: s, external: Set(), internal: Set(), logging: Set()}
  }
}

// Rewritten process_prevote_quorum_on_prevote_stage
pure def process_prevote_quorum_on_prevote_stage(s: LocalState, msg: Message): HandlerOutput = {
  pure val prevotes = match msg {
    | Propose(p) => Set()
    | PreVote(pv)   => s.get_prevotes(s.round, pv.id)
    | PreCommit(p)  => Set()
  }
  pure val cond = and {
    prevotes.map(m => m.src).size() >= 2 * F + 1,
    s.stage == PreVoteStage and s.after_prevote_for_first_time,
  }
  if (cond){
    {
      state: { ...s, after_prevote_for_first_time: false },
      internal: Set(StartTimeout({ kind: ProposeTimeout, round: s.round })),
      external: Set(),
      logging: Set()
    }
  } else 
    {state: s, external: Set(), internal: Set(), logging: Set()}
}

// Rewritten process_proposal_and_quorum_after_prevote_stage_for_the_first_time

pure def process_proposal_and_quorum_after_prevote_stage_for_the_first_time(s: LocalState, msg: Message): HandlerOutput = {
  pure val propose_msg = match msg {
    | Propose(p) => Some(p)
    | PreVote(pv) => s.get_proposals().find(p =>
                          p.src == PROPOSER.get(s.round) and Some(p.proposal.id()) == pv.id and p.round == pv.round
                        )
    | PreCommit(p) => None
  }
  if (propose_msg == None) 
    {state: s, external: Set(), internal: Set(), logging: Set()}
  else {
    pure val msg_val = propose_msg.unwrap()
    pure val prevotes = s.get_prevotes(s.round, Some(msg_val.proposal.id()))
    pure val cond = and {
      propose_msg != None,
      msg_val.src == PROPOSER.get(s.round),
      prevotes.map(m => m.src).size() >= 2 * F + 1,
      s.stage.in(Set(PreVoteStage, PreCommitStage)) and s.after_prevote_for_first_time,
    }
    if (cond){
      pure val base_result = {
        state: { ...s, valid_value: Some(msg_val.proposal), valid_round: s.round },
        external: Set(),
        internal: Set(),
        logging: Set(CollectEvidence(Propose(msg_val)))
                .union(prevotes.map(m => CollectEvidence(PreVote(m))))
      }

  
      val s2 = base_result.state
      if (s2.stage == PreVoteStage) 
        {
          state: { ...s2, locked_value: Some(msg_val.proposal), locked_round: msg_val.round, stage: PreCommitStage },
          external: Set(Broadcast(PreCommit({ src: s2.process_id, round: msg_val.round, id: Some(msg_val.proposal.id()) }))),
          internal: Set(),
          logging: base_result.logging
        }
      else 
        {state: s2, external: Set(), internal: Set(), logging: base_result.logging}
      
    } else 
      {state: s, external: Set(), internal: Set(), logging: Set()}
  }
}


// Rewritten process_prevote_quorum_at_prevote_stage
pure def process_prevote_quorum_at_prevote_stage(s: LocalState, msg: Message): HandlerOutput = {
  pure val prevotes = match msg {
    | Propose(p)   => Set()
    | PreVote(pv)  => if (pv.id == None) s.get_prevotes(s.round, None) else Set()
    | PreCommit(p) => Set()
  }
  pure val cond = and {
    prevotes.map(m => m.src).size() >= 2 * F + 1,
    s.stage == PreVoteStage,
  }
  if (cond){
    {
      state: { ...s, stage: PreCommitStage },
      external: Set(Broadcast(PreCommit({ src: s.process_id, round: s.round, id: None }))),
      internal: Set(),
      logging:  prevotes.map(m => CollectEvidence(PreVote(m)))
    }
  } else 
    {state: s, external: Set(), internal: Set(), logging: Set()}
}

// Rewritten process_precommit_quorum_for_the_first_time
pure def process_precommit_quorum_for_the_first_time(s: LocalState, msg: Message): HandlerOutput = {
  pure val precommits = match msg {
    | Propose(p)   => Set()
    | PreVote(pv)  => Set()
    | PreCommit(p) => s.get_all_precommits().filter(r => r.round == s.round)
  }
  pure val cond = and {
    precommits.map(m => m.src).size() >= 2 * F + 1,
    not(s.precommit_quorum),
  }
  if (cond){
    {
      state: { ...s, precommit_quorum: true },
      internal: Set(StartTimeout({ kind: PreCommitTimeout, round: s.round })),
      external: Set(),
      logging: precommits.map(m => CollectEvidence(PreCommit(m)))
    }
  } else 
    {state: s, external: Set(), internal: Set(), logging: Set()}
}

// Rewritten process_proposal_and_precommit_quorum_but_no_decision
pure def process_proposal_and_precommit_quorum_but_no_decision(s: LocalState, msg: Message): HandlerOutput = {
  pure val propose_msg = match msg {
    | Propose(p)   => Some(p)
    | PreVote(pv)  => None
    | PreCommit(pc) => s.get_proposals().find(p => p.src == PROPOSER.get(s.round) and p.round == pc.round)
  }
  if (propose_msg == None)
    {state: s, external: Set(), internal: Set(), logging: Set()}
  else {
    pure val msg_val = propose_msg.unwrap()
    pure val precommits = s.get_precommits(msg_val.round, msg_val.proposal.id())
    pure val cond = and {
      propose_msg != None,
      msg_val.src == PROPOSER.get(msg_val.round),
      precommits.map(m => m.src).size() >= 2 * F + 1,
      s.decision == None,
    }
    if (cond){
      if (not(msg_val.proposal.valid())) 
        {state: s, external: Set(), internal: Set(), logging: Set()}
      else 
        { 
          state: { ...s, decision: Some(msg_val.proposal), stage: DecidedStage },
          external: Set(),
          internal: Set(),
          logging: Set(CollectEvidence(Propose(msg_val)))
                  .union(precommits.map(m => CollectEvidence(PreCommit(m))))
        }
    } else 
      {state: s, external: Set(), internal: Set(), logging: Set()}
  }
}
}