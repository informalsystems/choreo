module tendermint {
    import basicSpells.* from "lib/basicSpells"

    import glyphNetwork as GNet from "lib/glyph"
    import glyphDriver as GD from "lib/glyph"
    import glyphsBase as GB from "lib/glyph"

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

    type LocalState = GB::LocalState[Node, Message, StateFields]

    type Bookkeeping = {
        evidence_propose: Set[ProposeMsg],
        evidence_prevote: Set[PreVoteMsg],
        evidence_precommit: Set[PreVoteMsg],
    }

    type TimeoutKind = ProposeTimeout | PreVoteTimeout | PreCommitTimeout
    type TimeoutEvent = { kind: TimeoutKind, round: Round}

    type ExternalEffect = 
        |Broadcast(Message)

    type InternalEffect = 
        |StartTimeout(TimeoutEvent)

    type LoggingEffect =
        |CollectEvidence(Message)

    type Effect = 
      | Ext(ExternalEffect)
      | Inter(InternalEffect)
      | Log(LoggingEffect)

    type ListenerOutput = GB::ListenerOutput[LocalState, Effect]

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
    }

    pure def id(v: Value): ValueId = { hashed: v }

    pure def no_transition(state: LocalState): ListenerOutput = {
        // No transition, return the current state with no effects
        { effects: Set(), state: state }
    }


    

    // Broadcast Pre-Vote Block and start timeout (based on the state and messages can this 
    // transition be enabled?)
    // the core idea is that each event Listener is structured as follows:
    // State guards: predicates on the current state only
    // Message guards: predicates on message soup that can use the state as context
    // Effect builder: function to produce the effects 
    // State update: how to produce the next state when this rule fires -> should we have some kind of priority/consolidation rules ? 




    pure def broadcast_prevote_upon_proposal(
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
            state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true },
            effects: effect_builder(p),
            // TODO -> add logging effect to collect evidence
            }   
        )
        outputs
    }


    pure def broadcast_prevote_upon_prevote_quorum(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        val state_guard = and {
            s.stage == PreVoteStage
        }

        def message_guard = (p) => and {
            p.src == PROPOSER.get(s.round),
            p.valid_round >= 0,
            p.valid_round < s.round,
        }

        
        val proposals = messages.get_proposals()
        val pre_votes = messages.get_pre_votes()

        val enabled_proposals = proposals.filter(p => and {
            message_guard(p),
            state_guard,
            pre_votes.filter(q => q.id == Some(p.proposal.id()) and q.round == p.round).size() >= 2 * F + 1 // quorum size is F + 1
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
            state: { ...s, stage: PreCommitStage, after_prevote_for_first_time: true },
            effects: effect_builder(p),
            // TODO -> add logging effect to collect evidence
        })
        outputs

    }

    pure def start_timeout_upon_prevote_quorum(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        val state_guard = and {
            s.stage == PreVoteStage,
            s.after_prevote_for_first_time
        }

        def message_guard = (pv) => and {
            pv.round == s.round,
        }

        val pre_votes = messages.get_pre_votes()
        val enabled_pre_votes = pre_votes.filter(pv => and {
            message_guard(pv),
            state_guard
        })

        val quorum = (enabled_pre_votes.map(pv => pv.src).size() >= 2 * F + 1)

        val output = 
            if (quorum) {
                // Start the timeout for PreVote
                Set({ effects: Set(Inter(StartTimeout({ kind: PreVoteTimeout, round: s.round }))), state: { ...s, stage: PreCommitStage, after_prevote_for_first_time: false }})
            } else {
                Set()
            }
        
        output
    }

    pure def update_state_upon_prevote_quorum(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        val state_guard = and {
            s.stage == PreCommitStage,
            s.after_prevote_for_first_time
        }

        def message_guard = (p) => and {
            p.src == PROPOSER.get(s.round),   
        }

        val pre_votes = messages.get_pre_votes()
        val proposals = messages.get_proposals()
        val enabled_proposals = proposals.filter(p => and {
            message_guard(p),
            state_guard,
            pre_votes.filter(q => q.id == Some(p.proposal.id()) and q.round == p.round).size() >= 2 * F + 1 // quorum size is F + 1
        })

        val outputs = enabled_proposals.map(p => {
            state: { ...s,  valid_value: Some(p.proposal), valid_round: s.round},
            effects: Set(),
            // TODO -> add logging effect to collect evidence
        })
        outputs
    }

    pure def broadcast_precommit_upon_prevote_quorum(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
               
         val state_guard = and {
            s.stage == PreVoteStage,
            s.after_prevote_for_first_time
        }

        def message_guard = (p) => and {
            p.src == PROPOSER.get(s.round),   
        }

        val pre_votes = messages.get_pre_votes()
        val proposals = messages.get_proposals()
        val enabled_proposals = proposals.filter(p => and {
            message_guard(p),
            state_guard,
            pre_votes.filter(q => q.id == Some(p.proposal.id()) and q.round == p.round).size() >= 2 * F + 1 // quorum size is F + 1
        })

        val outputs = enabled_proposals.map(p => {
            state: { ...s, stage: PreCommitStage, valid_value: Some(p.proposal),
                    locked_value: Some(p.proposal), locked_round: p.round, 
                    valid_round: s.round},
            effects: Set(Ext(Broadcast(PreCommit({ src: s.process_id, round: p.round, id: Some(id(p.proposal)) })))),
            // TODO -> add logging effect to collect evidence
        })
        outputs
    }

    // This is relative to nil block broadcast 
    pure def broadcast_precommit_at_prevote_stage(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        val state_guard = and {
            s.stage == PreVoteStage
        }
        def message_guard = (p) => and {
            p.round == s.round,
            p.id == None
        }
        
        val pre_votes = messages.get_pre_votes()
        val enabled_pre_votes = pre_votes.filter(p => and {
            message_guard(p),
            state_guard
        })
        
        // TODO: review this
        val quorums = enabled_pre_votes.map(p => p.src).size() >= 2 * F + 1 
        val outputs = 
            if (quorums) {
                Set({
                    effects: Set(Ext(Broadcast(PreCommit({ src: s.process_id, round: s.round, id: None })))),
                    state: { ...s, stage: PreCommitStage}
                })
            } else {
                Set()
            }
        outputs
    }

    pure def start_timeout_upon_precommit_quorum(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        val state_guard = and {
            not(s.precommit_quorum)
        }

        def message_guard = (p) => and {
            p.round == s.round
            }

        val pre_commits = messages.get_pre_commits()
        val enabled_pre_commits = pre_commits.filter(p => and {
            message_guard(p),
            state_guard
        })

        val quorum = (enabled_pre_commits.map(p => p.src).size() >= 2 * F + 1)

        val output = 
            if (quorum) {
                // Start the timeout for PreCommit
                //TODO: s.round and p.round are the same 
                Set({ effects: Set(Inter(StartTimeout({ kind: PreCommitTimeout, round: s.round }))), state: { ...s, stage: DecidedStage }})
            } else {
                Set()
            }
        
        output
    }

    pure def decide_upon_precommit_quorum(
        s: LocalState,
        messages: Set[Message]
    ): Set[ListenerOutput] = {
        
        val state_guard = and {
            s.decision == None,
        }

        def message_guard = (p) => and {
            p.src == PROPOSER.get(s.round),
            p.proposal.valid()   
        }

        val pre_commits = messages.get_pre_commits()
        val proposals = messages.get_proposals()
        val enabled_proposals = proposals.filter(p => and {
            message_guard(p),
            state_guard,
            pre_commits.filter(q => q.id == Some(p.proposal.id()) and q.round == p.round).map(p => p.src).size() >= 2 * F + 1 // quorum size is F +
        })
        val outputs = enabled_proposals.map(p => {
            state: { ...s, decision: Some(p.proposal), stage: DecidedStage },
            effects: Set(),
            // TODO -> do we need an effect for decision? to stop execution
            // TODO -> add logging effect to collect evidence
        })
        outputs
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

    /// The set of all nodes
    pure val NODES = CORRECT.union(FAULTY)
    /// The set of all rounds (prepared by the constants)
    pure val ROUNDS = VALUES.keys()
    /// The set of all correct values (prepared by the constants)
    pure val VALID_VALUES = ROUNDS.filter(k => PROPOSER.get(k).in(CORRECT)).map(k => VALUES.get(k))


}