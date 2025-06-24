module tendermint{

  import basicSpells.* from "lib/basicSpells"
  import rareSpells.* from "lib/rareSpells"

  type Round = int
  type Height = int
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
    decisions: Round -> Option[Value],
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
    | Finalize

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

  type Bookkeeping = {
    evidence_propose: Set[ProposeMsg],
    evidence_prevote: Set[PreVoteMsg],
    evidence_precommit: Set[PreVoteMsg],
    // For debugging. See README.md#using-breakpoints
    breakpoint: bool,
  }

  type Environment = {
    system : Node -> LocalState,
    active_timeouts : Node -> Option[TimeoutEvent],
    bookkeeping : Bookkeeping,
  }

  type TimeoutKind = ProposeTimeout | PreVoteTimeout | PreCommitTimeout
  type TimeoutEvent = { kind: TimeoutKind, round: Round}

  pure def no_effects(s: LocalState): HandlerOutput = {
    {state: s, external: Set(), internal: Set(), logging: Set()}
  }
  
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

  pure def get_all_prevotes(s: LocalState): Set[PreVoteMsg] =
    s.messages.filterMap(m => {
      match m {
        | PreVote(p) => Some(p)
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


  pure def valid(v: Value): bool = {
    VALID_VALUES.contains(v)
  }

  /// A value hash in an abstract way.
  pure def id(v: Value): ValueId = { hashed: v }


  // -------------------------------------------------------- New Logic ------------------------------------------------------------

  pure def start_round(s: LocalState, round: Round): HandlerOutput = {
    //if (round > MAX_ROUND) no_effects(s) else
    pure val s1 = { 
      ...s,
      round: round,
      stage: ProposeStage,
      precommit_quorum: false
    }

    if (s1.process_id == PROPOSER.get(round)){
      pure val proposal = if (s1.valid_value != None) s1.valid_value.unwrap() else VALUES.get(round)
      { 
        state: s1,
        external: Set(
          Broadcast(
            Propose({ src: s1.process_id, round: s1.round, proposal: proposal, valid_round: s1.valid_round })
          )
        ),
        internal: Set(),
        logging: Set()
      }
    } else {
      { 
        state: s1,
        external: Set(),
        internal: Set(
          StartTimeout({ kind: ProposeTimeout, round: s1.round })
        ),
        logging: Set()
      }
    }
  }
  
  
  pure def process_proposal_at_propose_stage(s: LocalState, msg: ProposeMsg): HandlerOutput = {
    pure val upon_condition = and {
      // upon <PROPOSAL, hp , roundp , v, −1>
      msg.valid_round == -1,
      // from proposer(hp, roundp)
      msg.src == PROPOSER.get(s.round),
      // while stepp = propose
      s.stage == ProposeStage,
    }
    if (not(upon_condition)) no_effects(s) else

    pure val broadcast =
      if (msg.proposal.valid() and (s.locked_round == -1 or s.locked_value == Some(msg.proposal)))
        Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some(msg.proposal.id()) }))
      else
        Broadcast(PreVote({ src: s.process_id, round: s.round, id: None }))

    {
      state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true },
      external: Set(broadcast),
      logging: Set(CollectEvidence(Propose(msg))),
      internal: Set()
    }
  }  
  
  
  pure def process_proposal_and_quorum_at_propose_stage(
    s: LocalState,
    msg: ProposeMsg,
  ): HandlerOutput = {
    pure val prevotes = s.get_prevotes(msg.valid_round, Some(msg.proposal.id()))

    pure val upon_condition = and {
      // upon <PROPOSAL, hp , roundp , v, vr>
      // from proposer(hp, roundp)
      msg.src == PROPOSER.get(s.round),
      // AND 2f + 1 <PREVOTE, hp , vr, id(v)>
      prevotes.map(m => m.src).size() >= 2 * F + 1,
      // while stepp = propose
      s.stage == ProposeStage,
      // ∧ (vr ≥ 0 ∧ vr < roundp)
      msg.valid_round >= 0 and msg.valid_round < s.round,
    }
    if (not(upon_condition)) no_effects(s) else

    pure val broadcast =
      if (msg.proposal.valid() and (s.locked_round <= msg.valid_round or s.locked_value == Some(msg.proposal)))
        Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some(msg.proposal.id()) }))
      else
        Broadcast(PreVote({ src: s.process_id, round: s.round, id: None }))

    {
      state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true },
      external: Set(broadcast), 
      logging: Set(CollectEvidence(Propose(msg)), Breakpoint)
        .union(prevotes.map(m => CollectEvidence(PreVote(m)))),
      internal: Set()
    }
  }

  pure def process_prevote_quorum_on_prevote_stage(s: LocalState, msg: PreVoteMsg): HandlerOutput = {
    pure val prevotes = s.get_all_prevotes().filter(r => r.round == s.round) 

    pure val upon_condition = and {
      // upon 2f + 1 <PREVOTE, hp , roundp , ∗>
      prevotes.map(m => m.src).size() >= 2 * F + 1,
      // while stepp = prevote for the first time
      s.stage == PreVoteStage and s.after_prevote_for_first_time,
    }
    if (not(upon_condition)) no_effects(s) else

    {
      state: { ...s, after_prevote_for_first_time: false },
      internal: Set(StartTimeout({ kind: PreVoteTimeout, round: msg.round })),
      logging: prevotes.map(m => CollectEvidence(PreVote(m))),
      external: Set()
    }
  }
  
  pure def process_proposal_and_quorum_after_prevote_stage_for_the_first_time(s: LocalState, msg: ProposeMsg): HandlerOutput = {
    pure val prevotes = s.get_prevotes(s.round, Some(msg.proposal.id()))

    pure val upon_condition = and {
      // upon <PROPOSAL, hp , roundp , v, ∗>
      // from proposer(hp , roundp)
      msg.src == PROPOSER.get(s.round),
      // AND 2f + 1 <PREVOTE, hp , roundp , id(v)>
      prevotes.map(m => m.src).size() >= 2 * F + 1,
      // while valid(v) ∧ stepp ≥ prevote for the first time
      s.stage.in(Set(PreVoteStage, PreCommitStage)) and s.after_prevote_for_first_time,
    }
    if (not(upon_condition)) no_effects(s) else

      pure val base_result = {
        state: {
          ...s,
          valid_value: Some(msg.proposal),
          valid_round: s.round,
        },
        logging: Set(CollectEvidence(Propose(msg)))
          .union(prevotes.map(m => CollectEvidence(PreVote(m)))),
        external: Set(),
        internal: Set()
      }

      val s2 = base_result.state
      if (s2.stage == PreVoteStage) 
        {
          state: { ...s2, locked_value: Some(msg.proposal), locked_round: msg.round, stage: PreCommitStage },
          external: Set(Broadcast(PreCommit({ src: s2.process_id, round: msg.round, id: Some(msg.proposal.id()) }))),
          internal: Set(),
          logging: base_result.logging
        }
      else 
        {state: s2, external: Set(), internal: Set(), logging: base_result.logging}
        
  
  }


  pure def process_prevote_quorum_at_prevote_stage(s: LocalState, msg: PreVoteMsg): HandlerOutput= {
    pure val prevotes = s.get_prevotes(s.round, None)
    pure val upon_condition = and {
      // upon 2f + 1 <PREVOTE, hp , roundp , nil>
      prevotes.map(m => m.src).size() >= 2 * F + 1,
      // while stepp = prevote
      s.stage == PreVoteStage,
    }
    if (not(upon_condition)) no_effects(s) else

    {
      state: { ...s, stage: PreCommitStage },
      external: Set(Broadcast(PreCommit({ src: s.process_id, round: msg.round, id: None }))),
      logging: prevotes.map(m => CollectEvidence(PreVote(m))),
      internal: Set()
    }
  }

  // line 47
  pure def process_precommit_quorum_for_the_first_time(s: LocalState, msg: PreVoteMsg): HandlerOutput = {
    pure val precommits = s.get_all_precommits().filter(r => r.round == s.round)

    pure val upon_condition = and {
      // upon 2f + 1 <PRECOMMIT, hp , roundp , ∗> for the first time
      precommits.map(m => m.src).size() >= 2 * F + 1,
      not(s.precommit_quorum),
    }
    if (not(upon_condition)) no_effects(s) else
      {
        state: { ...s, precommit_quorum: true },
        internal: Set(StartTimeout({ kind: PreCommitTimeout, round: msg.round })),
        logging:  precommits.map(m => CollectEvidence(PreCommit(m))),
        external: Set()
      }
  }

  pure def process_proposal_and_precommit_quorum_but_no_decision(s: LocalState, msg: ProposeMsg): HandlerOutput = {
    pure val precommits = s.get_precommits(msg.round, msg.proposal.id())

    pure val upon_condition = and {
      // upon <PROPOSAL, hp , r, v, ∗>
      // from proposer(hp , r)
      msg.src == PROPOSER.get(msg.round),
      // AND 2f + 1 <PRECOMMIT, hp , r, id(v)>
      precommits.map(m => m.src).size() >= 2 * F + 1,
      // while decisionp[hp] = nil
      s.decision == None,
    }
    if (not(upon_condition)) no_effects(s) else
    if (not(msg.proposal.valid())) no_effects(s) else

      //pure val s1 = {...s, decisions: s.decisions.put(msg.round, Some(msg.proposal))}
      //pure val s2 = reset_state(s1)
      //pure val ho = start_round(s2, s1.round + 1)
      {
        state: {
          ...s,
          decision: Some(msg.proposal),
          stage: DecidedStage,
          // TODO: Maybe we model a single consensus round, maybe we want more. If more, we need to add:
          // height: s.height + 1
          // reset
        },
        logging: Set(CollectEvidence(Propose(msg)))
          .union(precommits.map(m => CollectEvidence(PreCommit(m)))),
        external: Set(Finalize),//Set(Decided),
        internal: Set()
        // TODO Send start round msg to reset
      }
      /*
      {
        state: ho.state,
        external: ho.external,
        internal: ho.internal,
        logging: ho.logging.union(Set(CollectEvidence(Propose(msg)))
          .union(precommits.map(m => CollectEvidence(PreCommit(m)))))
      }
      */
  }

  pure def on_prevote_quorum(s: LocalState): HandlerOutput ={
    pure val proposals = s.get_proposals()
    proposals.fold(no_effects(s), (acc, msg) => {
      pure val res1 = process_proposal_and_quorum_at_propose_stage(acc.state, msg)
      pure val res2 = process_proposal_and_quorum_after_prevote_stage_for_the_first_time(res1.state, msg)
      {
        state: res2.state,
        external: acc.external.union(res1.external).union(res2.external),
        internal: acc.internal.union(res1.internal).union(res2.internal),
        logging: acc.logging.union(res1.logging).union(res2.logging)}
      }  
    )
  }

  pure def on_precommit_quorum(s: LocalState): HandlerOutput = {
    pure val proposals = s.get_proposals()
    proposals.fold(no_effects(s), (acc, msg) => {
      pure val res = process_proposal_and_precommit_quorum_but_no_decision(acc.state, msg)
      {
        state: res.state,
        external: acc.external.union(res.external),
        internal: acc.internal.union(res.internal),
        logging: acc.logging.union(res.logging)
      }
    })
  }

  pure def reset_state(s: LocalState): LocalState = {
    {
      ...s,
      stage: ProposeStage,
      decision: None,
      locked_value: None,
      locked_round: -1,
      valid_value: None,
      valid_round: -1,
      after_prevote_for_first_time: false,
      precommit_quorum: false,
    }
  }

  // -------------------------------------------------------- Message Handlers ------------------------------------------------------------
  pure def process_propose(s: LocalState, msg: ProposeMsg): HandlerOutput = {
    val s0 = {... s, messages: s.messages.setAdd(Propose(msg))}
    val res1 = process_proposal_at_propose_stage(s0, msg)
    val res2 = process_proposal_and_quorum_at_propose_stage(res1.state, msg)
    val res3 = process_proposal_and_quorum_after_prevote_stage_for_the_first_time(res2.state, msg)
    {
      state: res3.state,
      external: res1.external.union(res2.external).union(res3.external),
      internal: res1.internal.union(res2.internal).union(res3.internal),
      logging: res1.logging.union(res2.logging).union(res3.logging)
    } 
  }

  def process_prevote(s: LocalState, msg: PreVoteMsg): HandlerOutput = {
    val s0 = {... s, messages: s.messages.setAdd(PreVote(msg))}
    val res1 = on_prevote_quorum(s0)
    val res2 = process_prevote_quorum_on_prevote_stage(res1.state, msg)
    {
      state: res2.state,
      external: res1.external.union(res2.external),
      internal: res1.internal.union(res2.internal),
      logging: res1.logging.union(res2.logging)
    }
  }

  def process_precommit(s: LocalState, msg: PreVoteMsg): HandlerOutput = {
    val s0 = {... s, messages: s.messages.setAdd(PreCommit(msg))}
    val res1 = on_precommit_quorum(s0)
    val res2 = process_precommit_quorum_for_the_first_time(res1.state, msg)
    {
      state: res2.state,
      external: res1.external.union(res2.external),
      internal: res1.internal.union(res2.internal),
      logging: res1.logging.union(res2.logging)
    }
  }

  pure def receive_message(s: LocalState, m: Message): HandlerOutput = {
    match m {
      | Propose(p) => s.process_propose(p)
      | PreVote(p) => s.process_prevote(p)
      | PreCommit(p) => s.process_precommit(p)
    }
  }



//--------------------------------------------------------------------------------
//-------------------------------- glyphs -----------------------------------------
//--------------------------------------------------------------------------------

  
  var s: Environment // Global state of the system

  pure def broadcast(env: Environment, msg: Message): Environment = 
  { ...env, system: env.system.transformValues(s => { ...s, messages: s.messages.setAdd(msg) }) }

  pure val TIMEOUT_ORDER = Map(ProposeTimeout -> 0, PreVoteTimeout -> 1, PreCommitTimeout -> 2)
  pure def should_replace(t1: TimeoutEvent, t2: TimeoutEvent): bool = {
      TIMEOUT_ORDER.get(t2.kind) < TIMEOUT_ORDER.get(t1.kind) or t2.round > t1.round
  }
  pure def timeout(env: Environment, v: Node, event: TimeoutEvent): Environment = 
  { ...env,
      active_timeouts: env.active_timeouts.setBy(v, old_timeout => Some({
          match old_timeout {
          | None => event
          | Some(ts) => if (should_replace(ts, event)) event else ts
          }
      }))
  }

  pure def bookkeep(env: Environment, f: Bookkeeping => Bookkeeping): Environment = {
  { ...env, 
      bookkeeping: f(env.bookkeeping)
  }
  }

  // -------------------------------- effect processors --------------------------------
  pure def apply_effect(
    env: Environment,
    n: Node,
    ext: Set[ExternalEffect],
    inte: Set[InternalEffect],
    log: Set[LoggingEffect]
    ): Environment = {
    // Process external effects
    val env1 = ext.fold(env, (env, effect) => {
        match effect {
        | Broadcast(msg) => broadcast(env, msg)
        | Finalize => env // Finalize is a no-op in this model
        }
    });
    
    // Process internal effects
    val env2 = inte.fold(env1, (env, effect) => {
        match effect {
        | StartTimeout(event) => timeout(env, n, event)
        }
    });
    
    // Process logging effects
    val env3 = log.fold(env2, (env, effect) => {
        match effect {
        | CollectEvidence(msg) =>
            bookkeep(env, b => {
                match msg {
                | Propose(p)   => { ...b, evidence_propose: b.evidence_propose.setAdd(p) }
                | PreVote(p)   => { ...b, evidence_prevote: b.evidence_prevote.setAdd(p) }
                | PreCommit(p) => { ...b, evidence_precommit: b.evidence_precommit.setAdd(p) }
                }
            })
        | Breakpoint =>
            bookkeep(env, b => { ...b, breakpoint: true })
        }
    });
    env3
  }

  // -------------------------------- initialization --------------------------------
  pure val initial_message =
    Propose({src: PROPOSER.get(0), round: 0, proposal: VALUES.get(0), valid_round: -1 })

  pure val initial_bookkeeping = {
    evidence_propose: Set(),
    evidence_prevote: Set(),
    evidence_precommit: Set(),
    breakpoint: false,
  }

  pure def initialize_process(n: Node): LocalState = {
    {
    process_id: n,
    messages: Set(initial_message),//.union(byzantine_messages),
    round: 0,
    stage: ProposeStage,
    decision: None,
    locked_value: None,
    locked_round: -1,
    valid_value: None,
    valid_round: -1,
    after_prevote_for_first_time: false,
    precommit_quorum: false,
    decisions: Map(0 -> None, 1 -> None, 2 -> None, 3 -> None, 4 -> None, 5 -> None, 6 -> None),
    }
  }

  val byzantine_messages = {
    val rounds = Set (0) //s.system.values().map(s => s.round)
    val byzantine_proposals = rounds.map(r => {
      tuples(FAULTY, VALUES.values(), ROUNDS.setAdd(-1)).map(((f, v, vr)) => {
        Propose({ src: f, round: r, proposal: v, valid_round: vr })
      })
    }).flatten()

    val byzantine_prevotes = rounds.map(r => {
      tuples(FAULTY, VALUES.values()).map(((f, v)) => {
        PreVote({ src: f, round: r, id: Some(v.id()) })
      })
    }).flatten()

    val byzantine_precommits = rounds.map(r => {
      tuples(FAULTY, VALUES.values()).map(((f, v)) => {
        PreCommit({ src: f, round: r, id: Some(v.id()) })
      })
    }).flatten()

    // Reintegrate byzantine proposals
    Set(byzantine_prevotes, byzantine_precommits, byzantine_proposals).flatten()
  }

  // -------------------------------- actions --------------------------------
  action init = all {
    s' = {
      system: NODES.mapBy(n => initialize_process(n)),
      active_timeouts: NODES.mapBy(n => None),
      bookkeeping: initial_bookkeeping,
    }
  }


  action step_permutations = {
    nondet process = NODES.oneOf()
    val all_msgs = s.system.get(process).messages.union(byzantine_messages)
    val idxs = 1.to(all_msgs.size())
    val msgs_maps = setOfMaps(idxs, all_msgs).filter(m => tuples(idxs, idxs).forall(((i, j)) => i != j implies m.get(i) != m.get(j)))
    val msgs_lists = msgs_maps.map(m => {
      range(1, all_msgs.size() + 1).foldl([], (acc, i) => {
        if (acc != []) acc.append(m.get(i)) else
        val state = s.system.get(process)
        val result = receive_message(state, m.get(i))
        if (result.state != state) acc.append(m.get(i)) else acc
      })
    })
    nondet ordered_messages = msgs_lists.oneOf()
    val initial = { state: s.system.get(process), external: Set(), internal: Set(), logging: Set() }
    val result = ordered_messages.foldl(initial, (accumulated_result, message) => {
      // Stop after finding the first effect
      if (accumulated_result.external != Set()) accumulated_result 
      else{
        val internal = accumulated_result.internal
        val external = accumulated_result.external
        val logging = accumulated_result.logging
        // accumulate the effects of the message
        val message_result = receive_message(accumulated_result.state, message)
        {
          state: message_result.state,
          external: external.union(message_result.external),
          internal: internal.union(message_result.internal),
          logging: logging.union(message_result.logging)
        }
        //accumulated_result.state.receive_message(message)
      }
    })
    all{
        result.external != Set(),
        // apply the effects to the environment
        val new_system = s.system.set(process, result.state)
        val new_env = {...s, system: new_system}
        s' = apply_effect(
            new_env,
            process,
            result.external,
            result.internal,
            result.logging
        )
    }
  }


  action step_accelerated = {
    nondet process = CORRECT.oneOf()
    val msgs = s.system.get(process).messages.union(byzantine_messages)
    val initial = { state: s.system.get(process), external: Set(), internal: Set(), logging: Set() }
    val all_pos = msgs.powerset().filter(m => m.size() > 0)
    nondet msgs2 =  all_pos.oneOf()
    val result = msgs2.fold(initial, (accumulated_result, message) => {
      // Stop after finding the first effect
      if (accumulated_result.external != Set()) accumulated_result 
      else{
        val internal = accumulated_result.internal
        val external = accumulated_result.external
        val logging = accumulated_result.logging
        // accumulate the effects of the message
        val message_result = receive_message(accumulated_result.state, message)
        {
          state: message_result.state,
          external: external.union(message_result.external),
          internal: internal.union(message_result.internal),
          logging: logging.union(message_result.logging)
        }
        //accumulated_result.state.receive_message(message)
      }
    })
    all{
        result.external != Set(),
        // apply the effects to the environment
        val new_system = s.system.set(process, result.state)
        val new_env = {...s, system: new_system}
        s' = apply_effect(
            new_env,
            process,
            result.external,
            result.internal,
            result.logging
        )
    }
  }
  action step_one_message = {
    nondet process = NODES.oneOf()
    val msgs = s.system.get(process).messages.union(byzantine_messages)
    nondet message = msgs.oneOf()
    val message_result = receive_message(s.system.get(process), message)
    all {
      // only for this draft, as I want a finite state space
      s' = apply_effect(
        { ...s, system: s.system.set(process, message_result.state) },
        process,
        message_result.external,
        message_result.internal,
        message_result.logging
      )
    }
  }


  val correct_nodes = s.system.values().filter(s => s.process_id.in(CORRECT))
  /// Agreement: no two correct full nodes decide differently.




  val agreement = tuples(correct_nodes, correct_nodes).forall(((p1, p2)) => {
    p1.decision == None or p2.decision == None or p1.decision == p2.decision
  })
  // Witness
  val no_decision = correct_nodes.forall(n => n.decision == None)
  val validity = correct_nodes.forall(s => s.decision.in(VALID_VALUES.map(v => Some(v)).setAdd(None)))




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
  const MAX_ROUND: Round // The maximum round we want to simulate

  /// The set of all nodes
  pure val NODES = CORRECT.union(FAULTY)
  /// The set of all rounds (prepared by the constants)
  pure val ROUNDS = VALUES.keys()
  /// The set of all correct values (prepared by the constants)
  pure val VALID_VALUES = ROUNDS.filter(k => PROPOSER.get(k).in(CORRECT)).map(k => VALUES.get(k))
}

module test{
  //import glyph.* from "glyph"
  import tendermint(
    F = 1,
    CORRECT = Set("p0"),
    FAULTY = Set("p3", "p1",  "P2"),
    PROPOSER = Map(0 -> "p3", 1 -> "p2", 2 -> "p3", 3 -> "p4"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v2", 3 -> "v3"),
    MAX_ROUND = 4
  ).*
}


