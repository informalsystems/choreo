// -*- mode: Bluespec; -*-

module tendermint {
  import CSMIBase as CSMI from "lib/csmi"
  import CSMIBase.and_then from "lib/csmi"
  import CSMIBase.and_then_state from "lib/csmi"
  import CSMIState(processes = NODES) as CSMI from "lib/csmi"

  import basicSpells.* from "lib/basicSpells"

  type Round = int
  type Stage = ProposeStage | PreVoteStage | PreCommitStage | DecidedStage
  type Value = str
  /// The ID of a value. In the implementation, this would be a hash of the value.
  /// Here, we wrap it in a record and don't convert it back into a value.
  /// This keeps the property that v1.id() == v2.id() iff v1 == v2.
  type ValueId = { hashed: Value }
  type Node = str

  type State = {
    round: Round,
    stage: Stage,
    decision: Option[Value],
    locked_value: Option[Value],
    locked_round: Round,
    valid_value: Option[Value],
    valid_round: Round,
    after_prevote_for_first_time: bool,
    precommit_quorum: bool,
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

  type ConsensusOutput =
    | Broadcast(Message)
    | StartTimeout(TimeoutEvent)
    | CollectEvidence(Message)
    | Breakpoint

  type TimeoutKind = ProposeTimeout | PreVoteTimeout | PreCommitTimeout
  type TimeoutEvent = { kind: TimeoutKind, round: Round }

  type Bookkeeping = {
    evidence_propose: Set[ProposeMsg],
    evidence_prevote: Set[PreVoteMsg],
    evidence_precommit: Set[PreVoteMsg],
    // For debugging. See README.md#using-breakpoints
    breakpoint: bool,
  }

  // Instantiate the CSMI types
  type LocalState = CSMI::LocalState[Node, Message, State]
  type ConsensusResult = CSMI::ConsensusResult[LocalState, ConsensusOutput]
  type UponResult = CSMI::UponResult[LocalState, ConsensusOutput]
  type Environment = CSMI::Environment[Node, State, Message, TimeoutEvent, Bookkeeping]

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

  /// Whether a value is valid. From the paper: "In Tendermint, transaction
  /// verification is the responsibility of the service that is being
  /// replicated; upon receiving a transaction from the client, the Tendermint
  /// process will ask the service if the request is valid, and only valid
  /// requests will be processed."
  pure def valid(v: Value): bool = {
    VALID_VALUES.contains(v)
  }

  /// A value hash in an abstract way.
  pure def id(v: Value): ValueId = { hashed: v }

  /* MESSAGE HANDLING */

  // line 11
  pure def start_round(s: LocalState, round: Round): ConsensusResult = {
    ({
      ...s,
      round: round,
      stage: ProposeStage,
      precommit_quorum: false,
    }).and_then_state(s => {
      pure val output =
        if (s.process_id == PROPOSER.get(round)) {
          pure val proposal =
            if (s.valid_value != None)
              s.valid_value.unwrap()
            else
              VALUES.get(round)

          Set(
            Broadcast(
              Propose({ src: s.process_id, round: s.round, proposal: proposal, valid_round: s.valid_round })
            )
          )
        } else {
          Set(StartTimeout({ kind: ProposeTimeout, round: s.round }))
        }

      { state: s, output: output }
    })
  }

  // line 22
  pure def process_proposal_at_propose_stage(s: LocalState, msg: Message): UponResult = {
    pure val propose_msg = match msg {
      | Propose(p) => Some(p)
      | _ => None
    }
    pure val msg = propose_msg.unwrap()

    pure val upon_condition = and {
      // upon <PROPOSAL, hp , roundp , v, −1>
      propose_msg != None,
      msg.valid_round == -1,
      // from proposer(hp, roundp)
      msg.src == PROPOSER.get(s.round),
      // while stepp = propose
      s.stage == ProposeStage,
    }

   CSMI::upon(upon_condition, (a) => {
     pure val broadcast =
       if (msg.proposal.valid() and (s.locked_round == -1 or s.locked_value == msg.proposal))
         Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some(msg.proposal.id()) }))
       else
         Broadcast(PreVote({ src: s.process_id, round: s.round, id: None }))

     {
       state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true },
       output: Set(broadcast, CollectEvidence(Propose(msg)))
     }
   })
  }

  // line 28
  pure def process_proposal_and_quorum_at_propose_stage(
    s: LocalState,
    msg: Message
  ): UponResult = {
    pure val propose_msg = match msg {
      | Propose(p) => Some(p)
      | PreVote(pv) => s.get_proposals().find(p =>
          p.src == PROPOSER.get(s.round) and Some(p.proposal.id()) == pv.id and p.round == pv.round
        )
      | PreCommit(p) => None
    }

    pure val msg = propose_msg.unwrap()

    pure val prevotes = s.get_prevotes(s.round, Some(msg.proposal.id()))

    pure val upon_condition =
      and {
        // upon <PROPOSAL, hp , roundp , v, vr>
        propose_msg != None,
        // from proposer(hp, roundp)
        msg.src == PROPOSER.get(s.round),
        // AND 2f + 1 <PREVOTE, hp , vr, id(v)>
        prevotes.map(m => m.src).size() >= 2 * F + 1,
        // while stepp = propose
        s.stage == ProposeStage,
        // ∧ (vr ≥ 0 ∧ vr < roundp)
        msg.valid_round >= 0 and msg.valid_round < s.round,
      }

   CSMI::upon(upon_condition, (a) => {
     pure val broadcast =
       if (msg.proposal.valid() and (s.locked_round <= msg.valid_round or s.locked_value == msg.proposal))
         Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some(msg.proposal.id()) }))
       else
         Broadcast(PreVote({ src: s.process_id, round: s.round, id: None }))

     {
       state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true },
       output: Set(broadcast, CollectEvidence(Propose(msg)), Breakpoint)
         .union(prevotes.map(m => CollectEvidence(PreVote(m))))
     }
   })
  }

  // line 34
  pure def process_prevote_quorum_on_prevote_stage(s: LocalState, msg: Message): UponResult = {
    pure val prevotes = match msg {
      | Propose(p) => Set()
      | PreVote(pv) => s.get_prevotes(s.round, pv.id) // can we filter by id here?
      | PreCommit(p) => Set()
    }

    pure val upon_condition = and {
      // upon 2f + 1 <PREVOTE, hp , roundp , ∗>
      prevotes.map(m => m.src).size() >= 2 * F + 1,
      // while stepp = prevote for the first time
      s.stage == PreVoteStage and s.after_prevote_for_first_time,
    }

    CSMI::upon(upon_condition, (a) => {
      {
        state: { ...s, after_prevote_for_first_time: false },
        output: Set(StartTimeout({ kind: PreVoteTimeout, round: s.round })) // msg.get_round()?
          .union(prevotes.map(m => CollectEvidence(PreVote(m))))
      }
    })
  }

  // line 36
  pure def process_proposal_and_quorum_after_prevote_stage_for_the_first_time(
    s: LocalState,
    msg: Message
  ): UponResult = {
    pure val propose_msg = match msg {
      | Propose(p) => Some(p)
      | PreVote(pv) => s.get_proposals().find(p =>
          p.src == PROPOSER.get(s.round) and Some(p.proposal.id()) == pv.id and p.round == pv.round
        )
      | PreCommit(p) => None
    }

    pure val msg = propose_msg.unwrap()

    pure val prevotes = s.get_prevotes(s.round, Some(msg.proposal.id()))

    pure val upon_condition = and {
      // upon <PROPOSAL, hp , roundp , v, ∗>
      propose_msg != None,
      // from proposer(hp , roundp)
      msg.src == PROPOSER.get(s.round),
      // AND 2f + 1 <PREVOTE, hp , roundp , id(v)>
      prevotes.map(m => m.src).size() >= 2 * F + 1,
      // while valid(v) ∧ stepp ≥ prevote for the first time
      s.stage.in(Set(PreVoteStage, PreCommitStage)) and s.after_prevote_for_first_time,
    }

    CSMI::upon(upon_condition, (a) => {
      pure val base_result = {
        state: {
          ...s,
          valid_value: Some(msg.proposal),
          valid_round: s.round,
        },
        output: Set(CollectEvidence(Propose(msg)))
          .union(prevotes.map(m => CollectEvidence(PreVote(m))))
      }

      base_result.and_then(s => {
        if (s.stage == PreVoteStage) {
          {
            state: {
              ...s,
              locked_value: Some(msg.proposal),
              locked_round: msg.round,
              stage: PreCommitStage,
            },
            output: Set(
              Broadcast(PreCommit({ src: s.process_id, round: msg.round, id: Some(msg.proposal.id()) }))
            )
          }
        } else {
          CSMI::no_output(s)
        }
      })
    })
  }

  // line 44
  pure def process_prevote_quorum_at_prevote_stage(s: LocalState, msg: Message): UponResult = {
    pure val prevotes = match msg {
      | Propose(p) => Set()
      | PreVote(pv) => if (pv.id == None) s.get_prevotes(s.round, None) else Set()
      | PreCommit(p) => Set()
    }

    pure val upon_condition = and {
      // upon 2f + 1 <PREVOTE, hp , roundp , nil>
      prevotes.map(m => m.src).size() >= 2 * F + 1,
      // while stepp = prevote
      s.stage == PreVoteStage,
    }

    CSMI::upon(upon_condition, (a) => {
      state: { ...s, stage: PreCommitStage },
      output: Set(Broadcast(PreCommit({ src: s.process_id, round: s.round, id: None })))
        .union(prevotes.map(m => CollectEvidence(PreVote(m))))
    })
  }

  // line 47
  pure def process_precommit_quorum_for_the_first_time(s: LocalState, msg: Message): UponResult = {
    pure val precommits = match msg {
      | Propose(p) => Set()
      | PreVote(pv) => Set()
      | PreCommit(p) => s.get_all_precommits().filter(r => r.round == s.round)
    }

    pure val upon_condition = and {
      // upon 2f + 1 <PRECOMMIT, hp , roundp , ∗> for the first time
      precommits.map(m => m.src).size() >= 2 * F + 1,
      not(s.precommit_quorum),
    }

    CSMI::upon(upon_condition, (a) => {
      state: { ...s, precommit_quorum: true },
      output: Set(StartTimeout({ kind: PreCommitTimeout, round: s.round }))
        .union(precommits.map(m => CollectEvidence(PreCommit(m))))
    })
  }

  // line 49
  pure def process_proposal_and_precommit_quorum_but_no_decision(s: LocalState, msg: Message): UponResult = {
    pure val propose_msg = match msg {
      | Propose(p) => Some(p)
      | PreVote(pv) => None
      | PreCommit(pc) => s.get_proposals().find(p => p.src == PROPOSER.get(s.round) and p.round == pc.round)
    }

    pure val msg = propose_msg.unwrap()
    pure val precommits = s.get_precommits(msg.round, msg.proposal.id())

    pure val upon_condition = and {
      // upon <PROPOSAL, hp , r, v, ∗>
      propose_msg != None,
      // from proposer(hp , r)
      msg.src == PROPOSER.get(msg.round),
      // AND 2f + 1 <PRECOMMIT, hp , r, id(v)>
      precommits.map(m => m.src).size() >= 2 * F + 1,
      // while decisionp[hp] = nil
      s.decision == None,
    }

    CSMI::upon(upon_condition, (a) => {
      if (not(msg.proposal.valid())) CSMI::no_output(s) else

      {
        state: {
          ...s,
          decision: Some(msg.proposal),
          stage: DecidedStage,
          // Maybe we model a single consensus round, maybe we want more. If more, we need to add:
          // height: s.height + 1
          // reset
        },
        output: Set(CollectEvidence(Propose(msg)))
          .union(precommits.map(m => CollectEvidence(PreCommit(m))))
        // Send start round msg to reset
      }
    })
  }

  /* CSMI DEFINITIONS */

  pure def initialize_process(n: Node): LocalState = {
    {
      process_id: n,
      messages: Set(initial_message),
      round: 0,
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

  pure def receive_message(s: LocalState, m: Message): Set[UponResult] = {
    // Set of potential transitions to do, with the conditions on when they can be done.
    // CSMI will take care of selecting one that can be done.
    Set(
      process_proposal_at_propose_stage(s, m),
      process_proposal_and_quorum_at_propose_stage(s, m),
      process_prevote_quorum_on_prevote_stage(s, m),
      process_proposal_and_quorum_after_prevote_stage_for_the_first_time(s, m),
      process_prevote_quorum_at_prevote_stage(s, m),
      process_precommit_quorum_for_the_first_time(s, m),
      process_proposal_and_precommit_quorum_but_no_decision(s, m),
    )
  }

  pure def fire_timeout_event(s: LocalState, t: TimeoutEvent): ConsensusResult = {
    match t.kind {
      | ProposeTimeout => {
        // line 55
        if (s.round != t.round or s.stage != ProposeStage) CSMI::no_output(s) else

        {
          state: { ...s, stage: PreVoteStage },
          output: Set(Broadcast(PreVote({ src: s.process_id, round: s.round, id: None })))
        }
      }
      | PreVoteTimeout => {
        // line 61
        if (s.round != t.round or s.stage != PreVoteStage) CSMI::no_output(s) else

        {
          state: { ...s, stage: PreCommitStage },
          output: Set(Broadcast(PreCommit({ src: s.process_id, round: s.round, id: None })))
        }
      }
      | PreCommitTimeout => {
        // line 65
        if (s.round != t.round) CSMI::no_output(s) else

        s.start_round(s.round + 1)
      }
    }
  }

  pure val TIMEOUT_ORDER = Map(ProposeTimeout -> 0, PreVoteTimeout -> 1, PreCommitTimeout -> 2)
  pure def should_replace(t1: TimeoutEvent, t2: TimeoutEvent): bool = {
    // TODO: this won't be needed once I update the CSMI lib with the sets of timeouts
    TIMEOUT_ORDER.get(t2.kind) < TIMEOUT_ORDER.get(t1.kind) or t2.round > t1.round
  }

  pure def apply_effect(env: Environment, n: Node, outputs: Set[ConsensusOutput]): Environment = {
    outputs.fold(env, (env, output) => {
      match output {
        | Broadcast(msg) => CSMI::broadcast(env, msg)
        | StartTimeout(r) => CSMI::timeout(env, n, r, should_replace)
        | CollectEvidence(msg) => {
          CSMI::bookkeep(env, b => {
            match msg {
              | Propose(p) => { ...b, evidence_propose: b.evidence_propose.setAdd(p) }
              | PreVote(p) => { ...b, evidence_prevote: b.evidence_prevote.setAdd(p) }
              | PreCommit(p) => { ...b, evidence_precommit: b.evidence_precommit.setAdd(p) }
            }
          })
        }
        | Breakpoint => {
          CSMI::bookkeep(env, b => { ...b, breakpoint: true })
        }
      }
    })
  }

  pure val initial_message =
    Propose({ src: PROPOSER.get(0), round: 0, proposal: VALUES.get(0), valid_round: -1 })

  pure val initial_bookkeeping = {
    evidence_propose: Set(),
    evidence_prevote: Set(),
    evidence_precommit: Set(),
    breakpoint: false,
  }

  val byzantine_messages = {
    val rounds = CSMI::s.system.values().map(s => s.round)
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

    Set(byzantine_proposals, byzantine_prevotes, byzantine_precommits).flatten()
  }

  action init = CSMI::init(initialize_process, initial_bookkeeping)
  action step = CSMI::step(receive_message, fire_timeout_event, apply_effect, byzantine_messages, 20)

  /* FORK SCENARIOS */

  pure def equivocation_in(n: Node, evidence: Set[{ src: Node, round: Round | other }]): bool = {
    tuples(evidence, evidence).exists(((e1, e2)) => {
      e1 != e2 and e1.src == n and e2.src == n and e1.round == e2.round
    })
  }

  /// Equivocation by a node n
  def equivocation_by(n: Node): bool = {
    or {
      n.equivocation_in(CSMI::s.bookkeeping.evidence_propose),
      n.equivocation_in(CSMI::s.bookkeeping.evidence_prevote),
      n.equivocation_in(CSMI::s.bookkeeping.evidence_precommit),
    }
  }

  /// Amnesic behavior by a node n
  def amnesia_by(n: Node): bool = {
    tuples(ROUNDS, ROUNDS).exists(((r1, r2)) => {
      r1 < r2 and tuples(VALID_VALUES, VALID_VALUES).exists(((v1, v2)) => {
        and {
          v1 != v2,
          CSMI::s.bookkeeping.evidence_propose.contains({
            { src: n, round: r1, proposal: v1.id(), valid_round: r1 }
          }),
          CSMI::s.bookkeeping.evidence_propose.contains({
            { src: n, round: r2, proposal: v2.id(), valid_round: r2 }
          }),
          ROUNDS.filter(r => r1 <= r and r < r2).forall(r => {
            CSMI::s.bookkeeping.evidence_prevote.filter(m => {
              m.round == r and m.id == v2.id()
            }).size() >= 2 * F + 1
          }),
        }
      })
    })
  }

  /* PROPERTIES */

  /// Sanity check for decisions
  val no_decision = CSMI::s.system.values().forall(v => v.decision == None)

  /// Invariant for debugging. See README.md#using-breakpoints
  val breakpoint = not(CSMI::s.bookkeeping.breakpoint)

  val correct_nodes = CSMI::s.system.values().filter(s => s.process_id.in(CORRECT))

  /// Agreement: no two correct full nodes decide differently.
  val agreement = tuples(correct_nodes, correct_nodes).forall(((p1, p2)) => {
    p1.decision == None or p2.decision == None or p1.decision == p2.decision
  })

  /// Validity: the decided block satisfies the predefined predicate valid().
  val validity = correct_nodes.forall(s => s.decision.in(VALID_VALUES.map(v => Some(v)).setAdd(None)))

  /// The protocol safety. Two cases are possible:
  ///   1. There is no fork, that is, Agreement holds true.
  ///   2. A subset of faulty processes demonstrates equivocation or amnesia.
  val accountability = or {
    agreement,
    FAULTY.powerset().exists(f => and {
      f.size() >= F + 1,
      f.forall(n => equivocation_by(n) or amnesia_by(n)),
    })
  }
}

module tendermint_valid {
  import tendermint(
    F = 1,
    CORRECT = Set("p1", "p2", "p3"),
    FAULTY = Set("p4"),
    PROPOSER = Map(0 -> "p1", 1 -> "p2", 2 -> "p3", 3 -> "p4", 4 -> "p1"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v0", 3 -> "v2", 4 -> "v0"),
  ).*
}

module tendermint_faulty {
  import tendermint(
    F = 1,
    CORRECT = Set("p1", "p2"),
    FAULTY = Set("p3", "p4"),
    PROPOSER = Map(0 -> "p3", 1 -> "p2", 2 -> "p3", 3 -> "p4", 4 -> "p1"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v0", 3 -> "v2", 4 -> "v0"),
  ).*
}
