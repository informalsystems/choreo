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

    type ExternalEffect = 
        |Broadcast(Message)

    type InternalEffect = 
        |StartTimeout

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
    pure def pre_vote_block_listener(
        s: LocalState,
        messages: Set[Message]
    ): ListenerOutput = {
        
        // State guards: predicates on the local state
        val state_guard = and {
            s.stage == ProposeStage
        }

        // Message guards: predicates on the messages that can use the state as context
        def message_guard = (p) => and {
            p.valid_round == -1,
            p.src == PROPOSER.get(s.round),
            //p.proposal.valid
            (p.proposal == s.locked_value or s.locked_round == -1),
            } 


        // Apply Guards
        val proposals = messages.get_proposals()
        val enabled_proposals = proposals.filter(p => and {
            message_guard(p),
            state_guard
        })
        
        // Effects builder: produce the effects
        val eff = enabled_proposals.map(p => 
        //Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some(p.proposal.id()) })))
            Ext(Broadcast(PreVote({ src: s.process_id, round: s.round, id: Some({ hashed: p.proposal }) })))
        )
        
        // State Update: how to produce the next state when this rule fires
        // Issue here -> what if multiple transitions are enabled. 
        {
            state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true },
            effects: eff
        }
    }

    pure def pre_vote_nil_listener(
        s: LocalState,
        messages: Set[Message]
    ): ListenerOutput = {
        
        // State guards: predicates on the local state
        val state_guard = and {
            s.stage == ProposeStage,
        }

        // Message guards: predicates on the messages that can use the state as context
        def message_guard = (p) => and {
            p.valid_round == -1,
            p.src == PROPOSER.get(s.round),
            (p.proposal != s.locked_value and s.locked_round != -1), //or ! p.proposal.valid
            } 

        // Apply Guards
        val proposals = messages.get_proposals()
        val enabled_proposals = proposals.filter(p => and {
            message_guard(p),
            state_guard
        })
        
        // Effects builder: produce the effects
        val eff = enabled_proposals.map(p => 
            Ext(Broadcast(PreVote({ src: s.process_id, round: s.round, id: None })))
        )
        
        // State Update: how to produce the next state when this rule fires
        // Issue here -> what if multiple transitions are enabled.
        // should we have some kind of priority/consolidation rules ? 
        {
            state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true },
            effects: eff
        }
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