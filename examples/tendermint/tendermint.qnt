// -*- mode: Bluespec; -*-
module tendermint {
    import basicSpells.* from "../../ux/set-based/lib/basicSpells"
    import glyph(processes = NODES) as glyph from "../../ux/set-based/lib/glyph"


    type Round = int    
    type Stage = ProposeStage | PreVoteStage | PreCommitStage | DecidedStage
    type Value = str
    /// The ID of a value. In the implementation, this would be a hash of the value.
    /// Here, we wrap it in a record and don't convert it back into a value.
    /// This keeps the property that v1.id() == v2.id() iff v1 == v2.
    type ValueId = { hashed: Value }
    type Node = str

    type StateFields = {
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

    type CustomEffects = ()
    type Event = ()
    type Extensions = ()

    /* Boilerplate */
    type LocalState = glyph::LocalState[Node, StateFields]
    type LocalContext = glyph::LocalContext[Node, StateFields, Message, Event, Extensions]
    type Transition = glyph::Transition[Node, StateFields, Message, CustomEffects]
    type GlobalContext = glyph::GlobalContext[
        Node,
        StateFields,
        Message,
        Event,
        Extensions
    ]
    /* End of boilerplate */

    type Bookkeeping = {
        evidence_propose: Set[ProposeMsg],
        evidence_prevote: Set[PreVoteMsg],
        evidence_precommit: Set[PreVoteMsg],
    }

    type ListenerOutput = Set[Transition]

    type TimeoutKind = ProposeTimeout | PreVoteTimeout | PreCommitTimeout
    type TimeoutEvent = { kind: TimeoutKind, round: Round}

    type ExternalEffect = 
        |Broadcast(Message)
        | Finalize


    type InternalEffect = 
        |StartTimeout(TimeoutEvent)

    type LoggingEffect =
        |CollectEvidence(Message)

    type Effect = 
      | Ext(ExternalEffect)
      | Inter(InternalEffect)
      | Log(LoggingEffect)

    pure def get_proposals(messages: Set[Message]): Set[ProposeMsg] =
        messages.filterMap(m => {
            match m {
                | Propose(p) => Some(p)
                | _ => None
            }
        })

    pure def get_pre_votes(messages: Set[Message]): Set[PreVoteMsg] =
        messages.filterMap(m => {
            match m {
                | PreVote(p) => Some(p)
                | _ => None
            }
        })

    pure def get_pre_commits(messages: Set[Message]): Set[PreVoteMsg] =
        messages.filterMap(m => {
            match m {
                | PreCommit(p) => Some(p)
                | _ => None
            }
        })

    
    pure def valid(v: Value): bool = {
        VALID_VALUES.contains(v)
        //true
    }

    pure def id(v: Value): ValueId = { hashed: v }
// ------------------------------------------------------

    pure def start_round(
        s: LocalState,
        round: Round
    ): ListenerOutput =
        val s1 = {
            ...s,
            stage: ProposeStage,
            precommit_quorum: false,
        } 

        pure val output =
            if (s.process_id == PROPOSER.get(round)) {
            pure val proposal =
                if (s.valid_value != None)
                    s.valid_value.unwrap()
                else
                    VALUES.get(round)

            Set(
                Ext(
                    Broadcast(
                        Propose({ src: s.process_id, round: s.round, proposal: proposal, valid_round: s.valid_round })
                    )
                )
            )
            } else {

                Set(Inter(StartTimeout({ kind: ProposeTimeout, round: s.round })))
            }
        { 
            effects: output,
            state: s1
        }

    pure def upon_proposal_in_propose(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {

        val state_guard = and {
            s.stage == ProposeStage
        }

        // Message guards: predicates on the messages that can use the state as context
        def message_guard = (p) => and {
            p.valid_round == -1,
            p.src == PROPOSER.get(s.round),
        } 


        // Apply Guards
        val proposals = messages.get_proposals()
        val enabled_proposals = proposals.filter(p => and {
            message_guard(p),
            state_guard
        })

        def effect_builder = (p) => {
            // Broadcast the PreVote message for the proposal
            if (valid(p.proposal) and (s.locked_round == -1 or s.locked_value == Some(p.proposal))) {
                Set(Ext(Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some(id(p.proposal)) }))))
            } else {
                Set(Ext(Broadcast(PreVote({ src: s.process_id, round: s.round, id: None }))))
            }
        } 
        
        
        // Map the enabled proposals to effects and teh corresponding state updates
        val outputs = enabled_proposals.map(p => {
            state: { ...s, stage: PreVoteStage},
            effects: effect_builder(p).union(
                Set(Inter(StartTimeout({ kind: PreVoteTimeout, round: s.round })))
            )
            // TODO -> add logging effect to collect evidence
            }   
        )
        outputs

    }

    pure def upon_proposal_in_propose_prevote(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        val state_guard = and {
            s.stage == PreVoteStage,
        }
        def message_guard = (p) => and {
            p.src == PROPOSER.get(s.round),
            p.valid_round >= 0,
            p.valid_round < s.round
        }

        val proposals = messages.get_proposals().filter(p => and {
            message_guard(p),
            state_guard,
        })

        val pre_votes = messages.get_pre_votes()
        val enabled_proposals = proposals.filter(p => and {
            pre_votes.filter(q => q.id == Some(p.proposal.id()) and q.round == p.valid_round).size() >= 2 * F + 1 // quorum size is F + 1
        })

        def effect_builder = (p) => {
            // Broadcast the PreVote message for the proposal
            if (valid(p.proposal) and (s.locked_round <= p.valid_round or s.locked_value == Some(p.proposal))) {
                Set(Ext(Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some(id(p.proposal))}))))
            } else {
                Set(Ext(Broadcast(PreVote({ src: s.process_id, round: s.round, id: None }))))
            }
        }

        val outputs = enabled_proposals.map(p => {
            state: { ...s, stage: PreVoteStage},
            effects: effect_builder(p).union(
                Set(Inter(StartTimeout({ kind: PreCommitTimeout, round: s.round })))
            )
        }
        )
        outputs 
    }
        
    
    //this can be skipped for now
    pure def upon_quorum_prevotes_any(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        // Do we have a quorum of PreVotes in the current round
        def message_guard = (pv) => (pv.round == s.round)
        val quorum = messages.get_pre_votes().filter(pv => and {
            message_guard(pv),
        }).size() >= 2 * F + 1 // quorum size is F + 1

        if (quorum) {
            // If we have a quorum, we can move to precommit stage
            val outputs = Set({
                state: s,
                effects: Set(Inter(StartTimeout({ kind: PreVoteTimeout, round: s.round })))
            })
            outputs
        } else {
            Set()
        } 
    }

    pure def upon_quorum_nil_prevotes(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        val state_guard = and {
            s.stage == PreVoteStage,
        }

        // Do we have a quorum of PreVotes in the current round
        def message_guard = (pv) => (pv.round == s.round and pv.id == None)
        val prevotes = messages.get_pre_votes().filter(pv => message_guard(pv))
        val quorum = prevotes.size() >= 2 * F + 1

        if (quorum and state_guard) {
            // If we have a quorum, we can move to precommit stage
            val outputs = Set({
                state: { ...s, stage: PreCommitStage},
                effects: Set(Ext(Broadcast(PreCommit({ src: s.process_id, round: s.round, id: None })))
                            , Inter(StartTimeout({ kind: PreCommitTimeout, round: s.round })))
            })
            outputs
        } else {
            Set()
        }
    }
            
    pure def upon_quorum_precommits_any(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        

        // Do we have a quorum of PreCommits in the current round
        def message_guard = (pc) => (pc.round == s.round)
        val quorum = messages.get_pre_commits().filter(pc => and {
            message_guard(pc),
        }).size() >= 2 * F + 1 // quorum size is F + 1

        if (quorum) {
            // If we have a quorum, we can move to decided stage
            val outputs = Set({
                state: s,
                effects: Set(Inter(StartTimeout({ kind: PreCommitTimeout, round: s.round })))
            }
            )
            outputs
        } else {
            Set()
        } 
    }

    pure def upon_proposal_in_prevote_commit(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        val state_guard = and {
            s.stage.in(Set(PreVoteStage, PreCommitStage))
        }

        def message_guard = (p) => and {
            p.src == PROPOSER.get(s.round),
            p.round == s.round
        }

        val proposals = messages.get_proposals()
        val pre_votes = messages.get_pre_votes()
        
        val enabled_proposals = proposals.filter(p => and {
            message_guard(p),
            state_guard,
            // Check for quorum of prevotes for this proposal in current round
            pre_votes.filter(pv => and {
                pv.round == s.round,
                pv.id == Some(id(p.proposal))
            }).map(pv => pv.src).size() >= 2 * F + 1
        })

        def effect_builder = (p) => {
            if (s.stage == PreVoteStage) {
                // If in prevote stage, broadcast precommit and move to precommit stage
                Set(Ext(Broadcast(PreCommit({ src: s.process_id, round: s.round, id: Some(id(p.proposal)) }))),
                    Inter(StartTimeout({ kind: PreCommitTimeout, round: s.round })))
            } else {
                // If already in precommit stage, just update valid value
                Set()
            }
        }

        def state_builder = (p) => {
            if (s.stage == PreVoteStage) {
                // Move to precommit stage and update values
                { ...s, 
                stage: PreCommitStage,
                valid_value: Some(p.proposal),
                valid_round: s.round,
                locked_value: Some(p.proposal),
                locked_round: s.round
                }
            } else {
                // Just update valid value if already in precommit
                { ...s,
                valid_value: Some(p.proposal),
                valid_round: s.round
                }
            }
        }

        val outputs = enabled_proposals.map(p => {
            state: state_builder(p),
            effects: effect_builder(p)
        })
        
        outputs
    }

    pure def upon_proposal_in_precommit_no_decision(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        val state_guard = and {
            s.decision == None
        }

        def message_guard = (p) => and {
            p.src == PROPOSER.get(p.round),
            p.round <= s.round  // Can decide on current or past rounds
        }

        val proposals = messages.get_proposals()
        val pre_commits = messages.get_pre_commits()
        
        val enabled_proposals = proposals.filter(p => and {
            message_guard(p),
            state_guard,
            // Check for quorum of precommits for this proposal
            pre_commits.filter(pc => and {
                pc.round == p.round,
                pc.id == Some(id(p.proposal))
            }).map(pc => pc.src).size() >= 2 * F + 1
        })

        def effect_builder = (p) => {
            // Decision is made, broadcast finalize
            Set(Ext(Finalize))
        }

        def state_builder = (p) => {
            // Make decision and move to decided stage
            { ...s,
            decision: Some(p.proposal),
            stage: DecidedStage
            }
        }

        val outputs = enabled_proposals.map(p => {
            state: state_builder(p),
            effects: effect_builder(p)
        })
        
        outputs
    }

    pure def on_propose_timeout(
        s: LocalState,
        t: Set[TimeoutEvent]
    ): Set[ListenerOutput] = {

        val candidates = t.filter(t => t.round >= s.round and t.kind == ProposeTimeout)
        val guard = and {
            candidates.size() > 0,
            s.stage == ProposeStage,
        }

        if (guard)

            Set({
                effects: Set(Ext(Broadcast(PreVote({ src: s.process_id, round: s.round, id: None })))
                            , Inter(StartTimeout({ kind: PreVoteTimeout, round: s.round }))),
                state: { ...s, stage: PreVoteStage}
            }
            )
        else 
            Set()
    }

    pure def on_prevote_timeout(
        s: LocalState,
        t: Set[TimeoutEvent]
    ): Set[ListenerOutput] = {
        val candidates = t.filter(t => t.round >= s.round and t.kind == PreVoteTimeout)
        val guard = and {
            candidates.size() > 0,
            s.stage == PreVoteStage,
        }
        if (guard)

            Set({
                effects: Set(Ext(Broadcast(PreCommit({ src: s.process_id, round: s.round, id: None })))
                            , Inter(StartTimeout({ kind: PreCommitTimeout, round: s.round }))),
                state: { ...s, stage: PreCommitStage}
            }
            )
        else 
            Set()
    }

    pure def on_precommit_timeout(
        s: LocalState,
        t: Set[TimeoutEvent]
    ): Set[ListenerOutput] = {
        val candidates = t.filter(t => t.round >= s.round and t.kind == PreCommitTimeout)
        val guard = and {
            candidates.size() > 0,
            s.stage == PreCommitStage,
        }
        if (guard)
            Set(
                start_round(s, s.round + 1)
            )
        else 
            Set()
    }
    
    pure def main_listener(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] =
        val outputs = Set (
            upon_proposal_in_propose(s,messages),
            upon_proposal_in_propose_prevote(s,messages),
            upon_proposal_in_precommit_no_decision(s,messages),
            upon_proposal_in_prevote_commit(s,messages),
            //upon_quorum_prevotes_any(s,messages), 
            upon_quorum_nil_prevotes(s,messages),
            //upon_quorum_precommits_any(s,messages), 
            //on_propose_timeout(s, timeouts),
            //on_prevote_timeout(s, timeouts),
            //on_precommit_timeout(s, timeouts)
        ).flatten().filter(o => o.effects.size() > 0 or o.state != s)
        outputs



    pure val initial_message =
        Propose({src: PROPOSER.get(0), round: 0, proposal: VALUES.get(0), valid_round: -1 })

    pure val initial_bookkeeping = {
        evidence_propose: Set(),
        evidence_prevote: Set(),
        evidence_precommit: Set(),
    }

    def initialize_process(n: Node): LocalState = {
        {
        process_id: n,
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

    // Card(powset) = 4096
    val byzantine_messages_1 = {
        val rounds = Set(0) 
        val byzantine_proposals = rounds.map(r => {
        tuples(FAULTY, Set("v0","v1","v2"), rounds.setAdd(-1)).map(((f, v, vr)) => {
            Propose({ src: f, round: r, proposal: v, valid_round: vr })
        })
        }).flatten()

        val byzantine_prevotes = rounds.map(r => {
        tuples(FAULTY, Set("v0","v1","v2")).map(((f, v)) => {
            PreVote({ src: f, round: r, id: Some(v.id()) })
        })
        }).flatten()

        val byzantine_precommits = rounds.map(r => {
        tuples(FAULTY, Set("v0","v1","v2")).map(((f, v)) => {
            PreCommit({ src: f, round: r, id: Some(v.id()) })
        })
        }).flatten()

        // Reintegrate byzantine proposals
        Set(byzantine_prevotes, byzantine_precommits, byzantine_proposals).flatten()
    }

    val byzantine_messages = {
        // We can have at most 2^F faulty nodes, so we take the powerset of the byzantine messages
        // to simulate all possible combinations of byzantine messages.
        
        // 10 dummy prevotes for future rounds
        val dummy_prevotes = 1000.to(1025).map(r => {
            PreVote({ src: "p4", round: r, id: None })
        })
        dummy_prevotes
        //Set()
    }

    
    type GlobalState = GlobalContext

    pure def apply_effects(
        env: GlobalState,
        n: Node,
        effects: Set[Effect]
    ): GlobalState =
        effects.fold(env, (currentEnv, effect) =>
            match effect {
            | Ext(ext) =>
                match ext {
                    | Broadcast(msg) => GNet::broadcast(currentEnv, msg)
                    | Finalize => currentEnv
                }
            | Inter(inte) =>
                match inte {
                    | StartTimeout(event) => currentEnv
                }
            | Log(log) =>
                match log {
                    | CollectEvidence(msg) =>
                        currentEnv
                }
        }
    )



    action init = GD::init(initialize_process, initial_bookkeeping)
    action step = GD::step(main_listener, apply_effects)


  // -------------------------------- semantic symmetry utilities --------------------------------
  type StateFingerprint = {
    round: Round,
    stage: Stage,
    decision: Option[Value],
    locked_value: Option[Value],
    locked_round: Round,
    valid_value: Option[Value],
    valid_round: Round,
    after_prevote_for_first_time: bool,
    precommit_quorum: bool,
    is_proposer: bool,
  }

  pure def select_representatives(s: GlobalState): Set[Node] = {
    val states = s.system.values()
    val unique = group_by_fingerprint(states)
    unique.setByAll((k, group) => group.filter(n =>(n.in(CORRECT))).takeOne()).
      values().filter(n => n != None).map(n => n.unwrap())
  }

  def group_by_fingerprint(s: Set[LocalState]): StateFingerprint -> Set[Node] = {
    val init = Map()
    s.fold(init, (acc, state) => {
      val key = {
        round: state.round,
        stage: state.stage,
        decision: state.decision,
        locked_value: state.locked_value,
        locked_round: state.locked_round,
        valid_value: state.valid_value,
        valid_round: state.valid_round,
        after_prevote_for_first_time: state.after_prevote_for_first_time,
        precommit_quorum: state.precommit_quorum,
        is_proposer: state.process_id == PROPOSER.get(state.round)
      }
      acc.setByWithDefault(key, (e) => e.setAdd(state.process_id),Set())
    })
  }
  // -------------------------------- semantic symmetry utilities --------------------------------

    val correct_nodes = GD::s.system.values().filter(s => s.process_id.in(CORRECT))
    val agreement = tuples(correct_nodes, correct_nodes).forall(((p1, p2)) => {
        p1.decision == None or p2.decision == None or p1.decision == p2.decision})
    
    val one_decided =
        not( 
            GD::s.system.values().forall(v => v.decision == None)
        )
    
    val all_decided =
        not(
            correct_nodes.exists(v => v.decision == None)
        )
    
    // Witness for a to find a case where a node is in the decided stage while another is prevote
    // state
    val stages = 
        and{
            GD::s.system.values().map(v => v.stage).contains(ProposeStage), 
            GD::s.system.values().map(v => v.stage).contains(PreVoteStage), 
            GD::s.system.values().map(v => v.stage).contains(PreCommitStage),
            GD::s.system.values().map(v => v.stage).contains(DecidedStage)
        }
        

            
    
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
    const MAX_ROUND: Round
    
    /// The set of all nodes
    pure val NODES = CORRECT.union(FAULTY)
    /// The set of all rounds (prepared by the constants)
    pure val ROUNDS = VALUES.keys()
   
    /// The set of all correct values (prepared by the constants)
    //pure val VALID_VALUES = ROUNDS.filter(k => PROPOSER.get(k).in(CORRECT)).map(k => VALUES.get(k))
    pure val VALID_VALUES = Set("v0","v1", "v2")
}


module valid{
  import tendermint(
    F = 1,
    CORRECT = Set("p1","p2", "p3"),
    FAULTY = Set("p4"),
    PROPOSER = Map(0 -> "p1", 1 -> "p2", 2 -> "p3", 3 -> "p4"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v2", 3 -> "v3"),
    MAX_ROUND = 4
  ).*
}

module no_agreement{
  import tendermint(
    F = 1,
    CORRECT = Set("p2", "p3"),
    FAULTY = Set("p1","p4"),
    PROPOSER = Map(0 -> "p1", 1 -> "p2", 2 -> "p3", 3 -> "p4"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v2", 3 -> "v3"),
    MAX_ROUND = 4
  ).*
}