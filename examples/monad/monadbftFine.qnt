// -*- mode: Bluespec; -*-

module monadbft{
    import basicSpells.* from "../../spells/basicSpells"
    import rareSpells.* from "../../spells/rareSpells"
    import choreo(processes = validators) as choreo from "../../choreo"
     
    
    /// Set of validators participating in the consensus.
    const validators: Set[Address]
    /// Number of byzantine nodes
    const F: int
    
    //
    // Wiring into the reusable consensus state machine interface
    //
    type TimeoutData = int
    type InternalEvent = TimeoutEvent(TimeoutData)
    
    type Message =
        | Prop(Proposal)
        | Vote(VoteMsg)
        | Timeout(TimeoutMsg)
        | NoEndorsement(NoEndorsementMsg)

    type CustomEffects =
        | LogMessage(Message)
        | LogProposal(Proposal)
        | Commit(Proposal)
        | EarlyConfirmation(Proposal)
        | Confirmation(Proposal)
    // Algorithm 5 (block recovery) has more responses

    type Logging = {
        committed_proposals: Address -> Set[Proposal],
        msgHistory: Set[Message],
        timeoutHistory: Set[TimeoutData],
    }

    // Define types for the parameterized choreo types with the proper type arguments
    // for MonadBFT
    
    type EnvExtensions = {
        proposals_mock: Set[Proposal],
        ancestors_mock: ProposalID -> Set[ProposalID],
        logging: Logging,
    }

    /* Boilerplate */
    type LocalState = choreo::LocalState[Address, State]
    type LocalContext = choreo::LocalContext[Address, State, Message, InternalEvent, EnvExtensions]
    type Transition = choreo::Transition[Address, State, Message, InternalEvent, CustomEffects]
    type GlobalContext = choreo::GlobalContext[
        Address,
        State,
        Message,
        InternalEvent,
        EnvExtensions
    ]
    /* End of boilerplate */
    
    //
    // Some utilities to handle state accumulation
    //
    pure def nop(s: LocalState): Transition = {
        { post_state: s, effects: Set() }
    }

    pure def join_results(
        t1: Transition,
        t2: Transition
    ): Transition = {
        { post_state: t2.post_state, effects: t1.effects.union(t2.effects) }
    }

    pure def and_then(
        t: Transition,
        f: LocalState => Transition
    ): Transition = 
        join_results(t, f(t.post_state))

    pure def and_then_state(
        state: LocalState,
        f: LocalState => r
    ): r = f(state)
    
    pure def groupBy(s: Set[a], keyFunc: a => k): k -> Set[a] = {
        s.fold(Map(), (acc, elem) => {
            val key = keyFunc(elem)
            val existing = acc.getOrElse(key, Set())
            acc.put(key, existing.setAdd(elem))
        })
    }
    
    /// Number of votes needed to reach consensus
    pure val Q = 2 * F + 1
    /// Number of nodes
    pure val N = validators.size()
    pure val leaders = validators.fold(List(), (acc, v) => acc.append(v))

    
    pure val BLOCK_PAYLOAD = "VALID_TRANSACTION"
    type Address = str

    type State = {
        // Variables from Algorithm 2
        high_tip: Option[Tip],
        tip: Option[Tip],
        last_tc: Option[TC],
        curView: int,
        ledger: Ledger,
        highest_voted_view: int,

        // Variables from Algorithm 4

        // Not listed on top but used in Alg 4 line 30
        votes: ProposalID -> Set[VoteMsg],
        // Mapping from view number to set of timeout messages (Alg 4 line 17)
        timeouts: int -> Set[TimeoutMsg],
        // Set of view numbers for which a timeout was broadcast (Alg 4 line 21/22)
        timeouts_already_broadcast: Set[int],
    }



    //
    // Data structures (page 8)
    //

    type Ledger = List[Proposal]
    type ProposalID = { seq: int, view: int, byzantine: int }
    // The signature is symbolic, we represent it with the sender address
    type Signature = Address
    // We don't model hashes explicitly, but under the assumption of collision-free hash functions,
    // we can use this model to test for equality.
    type StateHash = List[ProposalID]


    /// ⟨view, proposal id, block header, σ, nec⟩ (page 8)
    type Tip = {
        view: int,
        proposal_id: ProposalID,
        block_header: BlockHeader,
        sigma: Signature,
        nec: Option[NEC],
    }

    /// ⟨view, seq, proposal id, state hash, σ⟩ (page 8)
    type VoteMsg = {
        view: int,
        seq: int,
        proposal_id: ProposalID,
        state_hash: StateHash,
        sigma: Signature,
    }

    /// ⟨view, highqc_view, σ⟩ (page 9)
    type NoEndorsementMsg = {
        view: int,
        highqc_view: int,
        sigma: Signature,
    }

    /// ⟨view, tip, tc, σ⟩ (page 9)
    type TimeoutMsg = {
        view: int,
        tip: Tip,
        // Timeout certificate use tc.view. Needed to avoid cyclic data type.
        // TODO: Maybe this should be an option
        tc: TCAux,
        sigma: Signature,
    }

    /// ⟨view, seq, proposal id, state hash, Σ⟩ (page 8)
    type QC = {
        c: Set[VoteMsg],
        view: int,
        seq: int,
        proposal_id: ProposalID,
        state_hash: StateHash,
        sigma: Signature,
    }

    /// TC = ⟨view, tips, high_tip, Σ⟩ (page 9)
    type TC = {
        view: int,
        high_tip: Option[Tip],
        tips: Set[Tip],
        sigma: Signature,
        c: Set[TimeoutMsg],
    }

    /// Auxiliary type for timeout certificate to avoid circular data types
    type TCAux = {
        view: int,
        high_tip: Option[Tip],
        tips: Set[Tip],
        sigma: Signature,
    }

    /// ⟨view, highqc view, Σ⟩ (page 9)
    type NEC = {
        view: int,
        highqc_view: int,
        sigma: Signature,
        c: Set[NoEndorsementMsg]
    }

    /// We don't model hashes explicitly, but under the assumption of collision-free hash functions,
    /// we can use this model to test for equality.
    type BlockHash = {
        seq: int,
        payload_hash: str,
        qc: QC
    }

    /// ⟨seq, payload, payload hash, qc, block hash⟩ (page 8)
    type Block = {
        seq: int,
        payload: str,
        payload_hash: str,
        qc: QC,
        block_hash: BlockHash
    }

    /// ⟨seq, payload hash, qc, block hash⟩ (page 8)
    type BlockHeader = {
        seq: int,
        payload_hash: str,
        qc: QC,
        block_hash: BlockHash
    }

    /// ⟨view, proposal id, block, σ, tc, nec⟩ (page 8)
    type Proposal = {
        view: int,
        proposal_id: ProposalID,
        block: Block,
        sigma: Signature,
        tc: Option[TC],
        nec: Option[NEC],
    }

    //
    // State manipulation utilities
    //


    pure def mark_already_broadcast_timeout(s: LocalState, view: int): LocalState = {
        { ...s, timeouts_already_broadcast: s.timeouts_already_broadcast.setAdd(view) }
    }

    pure def was_timeout_already_broadcast(s: LocalState, view: int): bool = {
        s.timeouts_already_broadcast.contains(view)
    }
    
    pure def add_timeouts(s: LocalState, view: int, timeouts: Set[TimeoutMsg]): LocalState = {
        { ...s, timeouts: s.timeouts.put(view, timeouts) }
    }

    
    pure def add_votes(s: LocalState, proposal_id: ProposalID, votes: Set[VoteMsg]): LocalState =
    { ...s, votes: s.votes.put(proposal_id, votes) }


    //
    // Utility functions
    //

    /// Hash is modeled as identity for payloads
    pure def hash(s: str): str = {
        s
    }

    /// Block hash is modeled as a tuple of the block seq, the payload hash and the qc 
    pure def hash_block(seq: int, payload_hash: str, qc: QC): BlockHash = {
        {
        seq: seq,
        payload_hash: payload_hash,
        qc: qc,
        }
    }

    /// Cryptographic hash to the post‐execution state
    /// Modeled here as the ordered list of executed proposal ids
    pure def state_hash(s: LocalState): StateHash = {
        s.ledger.foldl(List(), (acc, p) => acc.append(p.proposal_id))
    }

    /// Check if a node(other) is the leader of some view
    pure def is_leader(s: LocalState, signature: Address): bool =
        leader_from_view(s.curView) == signature
    
    /// Check if the node(self) is the leader of the current view
    pure def i_am_leader(s: LocalState): bool =
        leader_from_view(s.curView) == s.process_id

    pure def leader_from_view(view: int): Address = {
        leaders[view % leaders.length()]
    }

    /// Check if qc1 extends qc2
    pure def extend(qc1: QC, qc2: QC, ancestors: ProposalID -> Set[ProposalID]): bool =
        ancestors.getOrElse(qc1.proposal_id, Set()).contains(qc2.proposal_id)

    /// Check if two proposals are conflicting
    pure def conflicting_props(p1: Proposal, p2: Proposal, ancestors: ProposalID -> Set[ProposalID]): bool =
        and {
        not(extend(p1.block.qc, p2.block.qc, ancestors)),
        not(extend(p2.block.qc, p1.block.qc, ancestors)),
        }

    /// Extract the tips from a set of timeout messages
    /// This function retruns a set of Tips. 
    pure def get_tips_from_timeouts(msgs: Set[TimeoutMsg]): Set[Tip]= {
        msgs.fold(Set(), (acc, msg) => acc.setAdd(msg.tip))
    }

    /// Extract the block header out of a block
    pure def header_from_block(b: Block): BlockHeader = {
        {
        seq: b.seq,
        payload_hash: b.payload_hash,
        qc: b.qc,
        block_hash: b.block_hash,
        }
    }

    /// Build a TC out of a set of timeout messages
    pure def build_tc(timeouts: Set[TimeoutMsg], addr: Address): TC = {
        // getOnlyElement will throw an error if we have different views
        val view = timeouts.map(t => t.view).getOnlyElement()
        val high_tip = find_high_tip_from_messages(timeouts) 
        {
        c: timeouts,
        view: view,
        high_tip: high_tip,
        tips: get_tips_from_timeouts(timeouts),
        sigma: addr,
        }
    }

    /// Build a QC out of a set of votes
    pure def build_qc(votes: Set[VoteMsg], addr: Address, state_hash: StateHash): QC = {
        // getOnlyElement will throw an error if we have different seqs/views
        val seq = votes.map(v => v.seq).getOnlyElement()
        val view = votes.map(v => v.view).getOnlyElement()
        val id = { seq: seq, view: view, byzantine: 0 }
        {
        c: votes,
        view: view,
        seq: seq,
        proposal_id: id,
        state_hash: state_hash,
        sigma: addr,
        }
    }

    
    /// Execute the proposal
    /// TODO: This is fine as it is, but we should think if we can do better here.
    pure def execute_block(ledger: Ledger, p: Proposal): Ledger = {
        ledger.append(p)
    }

    /// Check if a proposal conflicts with the ledger
    pure def proposal_conflicts(ledger: Ledger, p: Proposal, ancestors: ProposalID -> Set[ProposalID]): bool = {
        ledger.toSet().exists(l => conflicting_props(l, p, ancestors))
    }

    /// Revert the ledger back to the latest ancestor of p that is in the ledger.
    /// `ancestors` maps each proposalID to the full set of its ancestor‐IDs.
    pure def revert_ledger(ledger: Ledger, p: Proposal, ancestors: ProposalID -> Set[ProposalID]): Ledger = {
        // 1) Look up the set of all ancestor IDs for p
        pure val ancIds = ancestors.getOrElse(p.proposal_id, Set())

        // 2) Walk the ledger and remember the last index where we saw one of those IDs
        //    foldl((nextIndex, lastMatch), ((idx, foundIdx), elem )) =>
        //      if elem.proposal_id ∈ ancIds then (idx+1, idx) else (idx+1, foundIdx)
        pure val result = ledger.foldl((0, -1), (acc, elem) => {
        pure val idx = acc._1
        pure val foundIdx = acc._2
        if (elem.proposal_id.in(ancIds))
            (idx + 1, idx)
        else
            (idx + 1, foundIdx)
        })

        val lastIdx = result._2

        // 3) If we never found a match (lastIdx == -1), just return an empty ledger
        //    otherwise slice up through that index (inclusive)
        if (lastIdx < 0) {
        List()
        } else {
        ledger.slice(0, lastIdx + 1)
        }
    }

    /// Check if a block was alread received
    pure def block_present(mock: Set[Proposal], bh: BlockHeader): bool = {
        mock.exists(p => p.block.header_from_block() == bh)
    }

    /// Fetch the block from the local state
    pure def get_present_block(mock: Set[Proposal], bh: BlockHeader): Block = {
        mock.find(p => p.block.header_from_block() == bh).unwrap().block
    }

    //
    // Algorithm 1 (page 13)
    // Utilities for a validator
    //

    /// Alg 1, line 1
    /// Form a block out of a QC and a payload
    pure def build_block(qc: QC, payload: str): Block =
        {
        seq: qc.seq + 1,
        payload: payload,
        payload_hash: hash(payload),
        qc: qc,
        block_hash: hash_block(qc.seq + 1, hash(payload), qc),
        }

    /// Algorithm 1, page 13 (line 6)
    /// Form a proposal out of a block and a set of certificates
    pure def build_proposal(
        view: int,
        block: Block,
        tc: Option[TC],
        nec: Option[NEC],
        addr: Address
    ): Proposal = {
        val id = { seq: block.seq, view: view, byzantine: 0 }
        {
        view: view,
        proposal_id: id,
        block: block,
        sigma: addr,
        tc: tc,
        nec: nec,
        }
    }

    /// Alg 1, line 10
    /// Confirm the proposal continues from the last certified block.
    /// It then accepts proposals made under normal operation, when the leader advances without any timeouts.
    /// In recovery after a timeout, it only accepts either the reproposal of the highest‐tip block or, 
    /// if that block couldn’t be recovered, a new block justified by a No‑Endorsement Certificate.
    pure def safety_check(p: Proposal): bool = {
        if (p.block.seq != p.block.qc.seq + 1) // Warning: typo in the paper (line 11)
            false
        else if (p.view == p.block.qc.view + 1)
            true
        else if (p.tc != None and p.view == p.tc.unwrap().view + 1)
            pure val p_tc = p.tc.unwrap()
            if (p.block.qc != p_tc.high_tip.unwrap().block_header.qc
                    or p_tc.high_tip != find_high_tip_from_tc(p_tc))
                false
            else if (p.nec != None)
                p.nec.unwrap().view == p.view and p.nec.unwrap().highqc_view == p.block.qc.view
            else
                p.block.block_hash == p_tc.high_tip.unwrap().block_header.block_hash
            else
                false
    }

    /// Alg 1 line 22
    pure def update_tip(p: Proposal): Option[Tip] = {
        if (p.view == p.block.qc.view + 1 or p.nec != None)
        Some({
            view: p.view,
            proposal_id: p.proposal_id,
            block_header: p.block.header_from_block(),
            sigma: p.sigma,
            nec: p.nec,
        })
        else
        find_high_tip_from_tc(p.tc.unwrap()) // Warning: why is there no check for none TC?
    }     
        
    /// Alg 1 line 26
    pure def parent_id(p: Proposal): ProposalID =
        p.block.qc.proposal_id

    //
    // Algorithm 3 (page 16)
    // Finding high tip from a tc or set of timeout messages
    //

    /// Alg 3 line 11
    /// Returns true only if a tip represents a “fresh” proposal:
    ///   - A happy‑path proposal where tip.view == tip.block.qc.view+1, or
    ///   - A NEC‑driven proposal where tip.nec.view == tip.view && tip.nec.highqc_view == tip.block.qc.view
    pure def verify_fresh_proposal(tip: Tip): bool ={
        if (tip.view == tip.block_header.qc.view + 1)
            true
        else
        match tip.nec {
            | None => false
            | Some(nec) =>
                tip.view == nec.view and tip.block_header.qc.view == nec.highqc_view
        }
    }

    /// Alg 3 line 1
    /// Gathers all validator tips from a timeout certificate or timeout messages.
    ///   - It aborts and returns nil if any tip fails the fresh‑proposal checks.
    ///   - Otherwise, it picks and returns the tip with the highest view number.
    /// Warning: the side effects of this function in the pseudocode seem wrong, why are we updating the stored TC to None at the start?
    pure def find_high_tip(tips: Set[Tip]): Option[Tip] = {
        // The first if else block (L3 -> L7) is skipped because we implemented a separate function for sets of timeout messages (find_high_tip_from_messages).
        if (tips.exists(t => not(t.verify_fresh_proposal())))
            None
        else
        // argmax (t ∈ tips) t.view
        // Returns None if tips is empty
        tips.fold(None, (acc, t) => {
            match acc {
            | None => Some(t)
            | Some(h) => if (t.view > h.view) Some(t) else acc
            }
        })
    }

    /// Alg 3 line 1
    /// find_high_tip() for a timeout certificate
    pure def find_high_tip_from_tc(tc: TC): Option[Tip] = {
        find_high_tip(tc.tips)
    }

    /// Alg 3 line 1
    /// find_high_tip() for a set of timeout messages.
    pure def find_high_tip_from_messages(msgs: Set[TimeoutMsg]): Option[Tip] = {
        find_high_tip(get_tips_from_timeouts(msgs))
    }

    //
    // Algorithm 4 (page 22)
    // Pacemaker for View Synchronization
    //

    /// Alg 4 line 2 / Alg 4 line 6
    /// Update the local state with a new view.
    /// We pass view instead of cert to simplify the code.
    pure def increment_view(view: int, s: LocalState): Transition = {
        if (view >= s.curView)
        // Increment view to next and reset the timer, old timers are discarded at apply_effect
        { post_state: { ...s, curView: view + 1 }, effects: Set(choreo::TriggerEvent(TimeoutEvent(view + 1))) }
        else
        // If we are already in a higher view, we do not change the state.
        { post_state: s, effects: Set() }
    }


    /// Alg 2 line 49
    /// As opposed to the paper, we write the timeout event as a function that is called by the timeout handler.
    /// Instead of of a "upon" statement that gets triggered.
    /// Warning: The upon trigger event block is not clear on its synchrony assumptions. 
    pure def trigger_timeout_event(s: LocalState): Transition = {
        pure val timeout_msg = {
            view: s.curView,
            // TODO: check if this is safe, it is not specified in the paper, made me think it is an option (Line 50)
            tip: s.tip.unwrap(),
            tc: { view: s.curView, high_tip: None, tips: Set(), sigma: s.process_id },
            sigma: s.process_id
        }

        {
            post_state: { ...s, highest_voted_view: max(s.highest_voted_view, s.curView) },
            effects: Set(
                choreo::Broadcast(Timeout(timeout_msg)),
                choreo::CustomEffect(LogMessage(Timeout(timeout_msg)))
            )
        }
    }


    pure def get_timeout_events(
        events: Set[InternalEvent]
    ): Set[TimeoutData] = 
        events.filterMap(e => {
                match e {
                    | TimeoutEvent(data) => Some(data)
                    | _ => None
                }
        })


    pure def handle_proposal(
        ls: LocalState, 
        p: Proposal, 
        props_mock: Set[Proposal], // This is a mock environment extension to simulate proposal fetching 
        ancestors_mock: ProposalID -> Set[ProposalID] // This is a mock environment extension to simulate ancestor fetching
    ): Transition = {
        match p.tc {
            | None => nop(ls)
            | Some(tc) => increment_view(tc.view, ls)
        }.and_then(s => {
            increment_view(p.block.qc.view, s)
        }).and_then(s => {
            // Warning: is the view being updated before the Leader check? Lines 35-36.
            if (p.view != s.curView or not (is_leader(s, p.sigma))) nop(s) else

            // Warning: The view being updated before the safety check.
            if (not(safety_check(p) and p.view > max(s.highest_voted_view, p.block.qc.view))) nop(s) else

                // Line 38
                pure val parent_proposal = props_mock.find(pp => pp.proposal_id == p.parent_id()).unwrap()
                pure val grandparent_proposal = props_mock.find(pp => pp.proposal_id == parent_proposal.parent_id()).unwrap()

                // Line 41
                pure val commit = if (p.block.qc.view == parent_proposal.block.qc.view + 1)
                    Set(choreo::CustomEffect(Commit(grandparent_proposal)), choreo::CustomEffect(Confirmation(p)))
                else
                    Set()

                // Line 43
                pure val early_confirmation = if (p.view == p.block.qc.view + 1) // Warning: typo in the paper
                    Set(choreo::CustomEffect(EarlyConfirmation(parent_proposal)))
                else
                    Set()

                // Line 44 - If ledger conflicts with parent proposal, revert to the common ancestor.
                pure val reverted_ledger = if (proposal_conflicts(s.ledger, parent_proposal, ancestors_mock))
                    revert_ledger(s.ledger, parent_proposal, ancestors_mock)
                else
                    s.ledger

                //Line 45 - Speculate
                pure val ledger = if (p.view == p.block.qc.view + 1)
                    execute_block(reverted_ledger, parent_proposal)
                else
                    reverted_ledger

                pure val vote_msg = {
                    view: p.view,
                    seq: p.block.seq,
                    proposal_id: p.proposal_id,
                    state_hash: state_hash(s),
                    sigma: s.process_id,
                }

                // TODO: send to next leader
                pure val next_leader = leader_from_view(p.view + 1)
                pure val send_vote = Set(
                    choreo::Send({to: next_leader, message: Vote(vote_msg)}),
                    choreo::CustomEffect(LogMessage(Vote(vote_msg)))
                )

                {
                    post_state: { ...s, highest_voted_view: p.view, ledger: ledger, tip: update_tip(p) },
                    effects: commit.union(early_confirmation).union(send_vote)
                }
            })
    }
    
        
    /// Alg 4 line 10
    /// Output = (TC, Side effects, bool: whether to trigger timeout event)
    pure def handle_timeout(t: TimeoutMsg, s: LocalState): (Option[TC], Transition)  = {
        val v = t.view

        if (v < s.curView) (None, nop(s)) else

        pure val res = increment_view(t.tip.block_header.qc.view, s)
        .and_then(s => increment_view(t.tip.view, s))

        // Timeout is new, let's accumulate it
        val acc_timeouts = res.post_state.timeouts.getOrElse(v, Set()).setAdd(t)
        val updated_state = res.post_state.add_timeouts(v, acc_timeouts)
        
        // Check if we have a quorum
        val res2 = if (acc_timeouts.size() >= Q) {
            val tc = build_tc(acc_timeouts, updated_state.process_id)
            (Some(tc), increment_view(tc.view, updated_state))
        } else if (acc_timeouts.size() >= F + 1 and not(res.post_state.timeouts_already_broadcast.contains(v))) {
            // TRIGGER TIMEOUT EVENT
            (None, updated_state.mark_already_broadcast_timeout(v).trigger_timeout_event())
        } else {
            (None, nop(updated_state))
        }

        (res2._1, join_results(res, res2._2))
    }

    /// Alg 4 line 25
    pure def handle_vote(vote: VoteMsg, s: LocalState): (Option[QC], Transition) = {
        val v = vote.view
        val id = vote.proposal_id
        
        if (v < s.curView) (None, nop(s)) else

        // Vote is new, let's accumulate it
        val acc_votes = s.votes.getOrElse(id, Set()).setAdd(vote)
        val updated_state = s.add_votes(id, acc_votes)
        
        // Check if we have a quorum
        if (acc_votes.size() >= Q) {
            val qc = build_qc(acc_votes, updated_state.process_id, state_hash(updated_state))
            (Some(qc), increment_view(qc.view, updated_state))
        } else {
            (None, nop(updated_state))
        }
    }

    //
    // Algorithm 2 (page 15)
    // Consensus for Validator i
    // 

    /// Alg 2 line 3 (Only for the leader)
    pure def upon_vote_msg(s: LocalState, v: VoteMsg): Transition = {
        //if (not(s.i_am_leader())) nop(s) else
        // Line 3
        pure val r = handle_vote(v, s)
        pure val qc = r._1
        pure val res = r._2
        if (not(res.post_state.i_am_leader())) nop(s) else
            res.and_then(s => {
            if (qc == None) nop(s) else
            val new_block = build_block(qc.unwrap(), BLOCK_PAYLOAD)
            val p = build_proposal(s.curView, new_block, None, None, s.process_id)
            { post_state: s, effects: Set(
                choreo::Broadcast(Prop(p)),
                choreo::CustomEffect(LogProposal(p))
            ) }
            })
    }


    /// Alg 2 line 10 / line 52 (leader/ non-leader)
    pure def upon_timeout_msg(ls: LocalState, t: TimeoutMsg, prop_mock: Set[Proposal]): Transition = {
        pure val res = handle_timeout(t, ls)
        pure val tc = res._1
        res._2.and_then(s => {
        // line 52 (non-leader)
        if (not(s.i_am_leader())) nop(s) else

        // line 11 (leader)

        // Not enough timeout messages to form tc
        if (tc == None) nop(s) else {
            val updated_state = { ...s, last_tc: tc, high_tip: tc.unwrap().high_tip }
            // TODO: it should be safe to unwrap here, but we should check.
            val high_tip = tc.unwrap().high_tip.unwrap()

            // if block and its payload (block.payload) for high tip is present
            if ( block_present(prop_mock ,high_tip.block_header)) {
                // Line 17
                val block = get_present_block(prop_mock, high_tip.block_header)
                val p = build_proposal(updated_state.curView, block, tc, None, updated_state.process_id)
                { post_state: updated_state, effects: Set(
                    choreo::Broadcast(Prop(p)),
                    choreo::CustomEffect(LogProposal(p))
                ) }
            } else {
                // Line 18-19-20 recoveringcurView ← true; SendRecoveryRequest(curView, high tip, tc);
                // TODO: For the moment this is replaced by fetching the block from the DA variable for debugging purposes
                val block = get_present_block(prop_mock, high_tip.block_header)
                val p = build_proposal(updated_state.curView, block, tc, None, updated_state.process_id)
                { post_state: updated_state, effects: Set(
                    choreo::Broadcast(Prop(p)),
                    choreo::CustomEffect(LogProposal(p))
                ) }
            }
        }
        })
    }

    
    pure def upon_proposal_msg(
        ls: LocalState,
        proposal: Proposal,
        context: LocalContext
    ): Transition = {
        val props_mock = context.extensions.proposals_mock
        val ancestors_mock = context.extensions.ancestors_mock
        handle_proposal(ls, proposal, props_mock, ancestors_mock)
    }




    pure def main_listener(ctx: LocalContext): Set[Transition] = {
        val messages = ctx.messages.map(msg => 
            match msg {
                | Prop(p) => upon_proposal_msg(ctx.state, p, ctx)
                | Vote(v) => upon_vote_msg(ctx.state, v)
                | Timeout(t) => upon_timeout_msg(ctx.state, t, ctx.extensions.proposals_mock)
                | _ => nop(ctx.state) // Ignore other external messages
            }
        )
        val events = ctx.events.map(e => 
            match e {
                | TimeoutEvent(data) => trigger_timeout_event(ctx.state)
                | _ => nop(ctx.state) // Ignore other internal events
            }
        )
        messages.union(events).filter(tr => tr.effects.size() > 0 or tr.post_state != ctx.state)
    }
        
        
 

    // ------------------------------------------- Effect Application -------------------------------------------
    
    pure def update_ancestors(
        ext: EnvExtensions,
        p: Proposal
    ): EnvExtensions = {
        val ancestors_mock = ext.ancestors_mock
        val parent_ancestors = ancestors_mock.getOrElse(p.parent_id(), Set())
        val ancestors_mock1 = ancestors_mock.put(p.proposal_id, 
            parent_ancestors.setAdd(p.parent_id()))
        {...ext, 
            ancestors_mock: ancestors_mock1
        }
    }

    pure def apply_custom_effect(env: GlobalContext, effect: CustomEffects): GlobalContext = {
        match effect {
            | LogMessage(msg) => {
                val ext = env.extensions
                val log = ext.logging
                val ext1 = {...ext,
                    logging: {...log, msgHistory: log.msgHistory.setAdd(msg)}
                }
                {...env, extensions: ext1}
            }
            | LogProposal(p) => {
                val ext = env.extensions
                val log = ext.logging
                val ext1 = {...ext, 
                    proposals_mock: ext.proposals_mock.setAdd(p),
                    logging: {...log, msgHistory: log.msgHistory.setAdd(Prop(p))},
                }
                {...env, extensions: update_ancestors(ext1, p)}
            }
            | Commit(p) => {
                val ext = env.extensions
                val log = ext.logging
                val ext1 = {...ext,
                    logging: {...log, 
                        committed_proposals: log.committed_proposals.transformValues(s => s.setAdd(p))
                    }
                }
                {...env, extensions: ext1}
            }
            | EarlyConfirmation(p) => env
            | Confirmation(p) => env
        }
    }
    // ------------------------------------------- Initialization & Execution -------------------------------------------
    pure val sigs = range(0, 5).foldl(List(), (acc,v) => acc.append(leader_from_view(v)))
    pure val genesis_qc = {
        c: Set(),
        view: 0,
        seq: 0,
        proposal_id: { seq: 0, view: 0, byzantine: 0 },
        state_hash: List(),
        sigma: sigs[0],
    }
    
    pure val b1 = build_block(genesis_qc, "VALID_TRANSACTION_INIT_1")
    pure val p1 = build_proposal(1, b1, None, None, sigs[1])
    pure val votes1 = validators.map(v => {
        { view: 1, seq: 1, proposal_id: p1.proposal_id, state_hash: List(), sigma: v }
    })
    pure val qc1 = build_qc(votes1, sigs[2], List())
    pure val b2 = build_block(qc1, "VALID_TRANSACTION_INIT_2")
    pure val p2 = build_proposal(2, b2, None, None, sigs[2])
    pure val votes2 = validators.map(v => {
        { view: 2, seq: 2, proposal_id: p2.proposal_id, state_hash: List(p1.proposal_id), sigma: v }
    })
    pure val qc2 = build_qc(votes2, sigs[3], List(p1.proposal_id))
    pure val b3 = build_block(qc2, "VALID_TRANSACTION_INIT_3")
    pure val p3 = build_proposal(3, b3, None, None, sigs[3])
    pure val votes3 = validators.map(v => {
        { view: 3, seq: 3, proposal_id: p3.proposal_id, state_hash: List(p1.proposal_id, p2.proposal_id), sigma: v }
    })
    pure val qc3 = build_qc(votes3, sigs[4], List(p1.proposal_id, p2.proposal_id))
    pure val b4 = build_block(qc3, "VALID_TRANSACTION_INIT_4")
    pure val p4 = build_proposal(4, b4, None, None, sigs[4])

    pure val ancestors_4 = Map(
        p1.proposal_id -> Set(p1.proposal_id),
        p2.proposal_id -> Set(p1.proposal_id),
        p3.proposal_id -> Set(p1.proposal_id, p2.proposal_id),
        p4.proposal_id -> Set(p1.proposal_id, p2.proposal_id, p3.proposal_id)
    )
    pure val proposals_4 = Set(p1, p2, p3, p4)
    
    pure val initial_messages = Set(Prop(p4))

    pure def initialize_process_empty(process_id: Address): LocalState = {
        high_tip: None,
        last_tc: None,
        tip: None,
        timeouts_already_broadcast: Set(),
        curView: 0,
        ledger: [],
        highest_voted_view: -1,
        process_id: process_id,
        votes: Map(),
        timeouts: Map(),
    }

    pure def initialize_process(process_id: Address): LocalState = {
        val base = initialize_process_empty(process_id)
        { ... base,
            curView: 2,
            ledger: List(p1, p2),
            highest_voted_view: 3,
            tip: Some({
                view: 3,
                proposal_id: p3.proposal_id,
                block_header: header_from_block(b3),
                sigma: p3.sigma,
                nec: None,
            }),
        }
    }

    pure def initialize_msg_buffer(
        process_id: Address
    ): Set[Message] =  initial_messages.union(byz_messages)

    pure def initialize_internal_buffer(
        process_id: Address
    ): Set[InternalEvent] = Set()

    pure val initial_logging: Logging = {
        committed_proposals: validators.mapBy(_ => Set(p1, p2)),
        msgHistory: votes1.union(votes2).map(x => Vote(x)),
        timeoutHistory: Set(),
    }

    pure val initial_env = {
        system: Map(),
        msgBuffer: Map(),
        internalBuffer: Map(),
        logging: initial_logging,
        extensions: {
            proposals_mock: proposals_4,
            ancestors_mock: ancestors_4,
        },
    }

    action init = choreo::init({
        system: validators.mapBy(v => initialize_process(v)),
        messages: validators.mapBy(v => initialize_msg_buffer(v)),
        events: validators.mapBy(v => initialize_internal_buffer(v)),
        extensions: {
            proposals_mock: proposals_4,
            ancestors_mock: ancestors_4,
            logging: initial_logging,
        }
    })

    action step = choreo::step(
        main_listener,
        apply_custom_effect,
        (e, p) => e
    )

    pure val byz_messages = {
        val faulty = Set("v4")
        val target_views = 1000.to(1025)
        
        // Use fold to build a set directly
        target_views.fold(Set(), (acc1, v) => 
            faulty.fold(acc1, (acc2, f) => {
                val voteMsg = { 
                    view: v, 
                    seq: v, 
                    proposal_id: { seq: v, view: v, byzantine: 1 }, 
                    state_hash: List(), 
                    sigma: f 
                }
                acc2.setAdd(Vote(voteMsg))
            })
        )
    }

    // ------------------------------------------- Invariants and Witnesses -------------------------------------------
    /// Witness: Search for a scenario where a proposal gets reproposed.
    def reproposal =
            val proposals = choreo::s.extensions.logging.msgHistory.fold(Set(), (s, x) => match x {
                | Prop(p) => s.setAdd(p)
                | _ => s
            })
            proposals.exists(p =>
                proposals.exists(p2 =>
                p.proposal_id != p2.proposal_id and p.block.seq == p2.block.seq))
        

    /// No Tail-Forking (NTF) page 10:
    def ntf =
        val votes = choreo::s.extensions.logging.msgHistory.fold(Set(), (s, x) => match x {
            | Vote(v) => s.setAdd(v)
            | _ => s
        })
        val committed_proposals = choreo::s.extensions.logging.committed_proposals.values().flatten()
        votes.forall(v =>
            // If an honest leader’s proposal for sequence number s is voted upon by a majority of honest validators,
            // TODO: filter faulty proposer's proposals
            votes.filter(v2 => v2.seq == v.seq and v2.proposal_id == v.proposal_id).size() > N / 2
            implies
            // then no other proposal can commit at sequence s.
            committed_proposals.forall(p =>
                p.block.seq == v.seq implies
                (p.proposal_id.seq == v.proposal_id.seq and p.proposal_id.byzantine == v.proposal_id.byzantine))
            )

    /// Safety property page 10: No two correct validators commit different blocks
    /// for the same sequence number
    def safety =
        val ps = choreo::s.extensions.logging.committed_proposals.values().flatten()
        ps.forall(p1 => ps.forall(p2 => p1.block.seq == p2.block.seq implies p1 == p2))

    
    /// Witness: Search for a scenario where a proposal is committed with a TC.
    def commit_with_tc =
        val ps = choreo::s.extensions.logging.committed_proposals.values().flatten()
        ps.exists(p => p.tc != None)
        


    /// Witness: Search for a view where no one timed out.
    def no_timeouts =
            val timeouts = choreo::s.extensions.logging.msgHistory.fold(Set(), (s, x) => match x {
                | Timeout(t) => s.setAdd(t)
                | _ => s
            })
            val proposals = choreo::s.extensions.logging.msgHistory.fold(Set(), (s, x) => match x {
                | Prop(p) => s.setAdd(p)
                | _ => s
            })
            //check if there are views with proposals but no timeouts
            proposals.exists(p =>
                timeouts.forall(t => t.view != p.view)
            )

    /// Witness: search for a QC that was not followed by a proposal referencing it.
    def missing_qc =
        val votes = choreo::s.extensions.logging.msgHistory.filterMap(x => match x {
            | Vote(v) => Some(v)
            | _ => None
        })
        val props = choreo::s.extensions.logging.msgHistory.filterMap(x => match x {
            | Prop(p) => Some(p)
            | _ => None
        })
        // Group views by view and proposal_id
        val grouped_votes = votes.groupBy(v => (v.view, v.proposal_id))
        grouped_votes.values().exists(entry => {
            val view = entry.map(v => v.view).getOnlyElement()
            val quorum = entry.size() >= Q

            val skipped = props.exists(
                p => p.block.qc.view > view
            )

            val not_used = props.forall(
                p => p.block.qc.view != view
            )
            quorum and skipped and not_used and view > 4
        })

    def missing_qc_w = not(missing_qc)
    
    /// Witness: search for a disappearing TIP.
    def missing_tip =
        val props = choreo::s.extensions.logging.msgHistory.filterMap(x => match x {
            | Prop(p) => Some(p)
            | _ => None
        })
        val tcs = props.filter(p => p.tc != None).map(p => (p.view,p.tc.unwrap()))
        // find a pair of (view, tc)
        tcs.exists(pair => {
            val view1 = pair._1
            val tc1 = pair._2
            tc1.high_tip != None and
            tcs.exists(pair2 => {
                val view2 = pair2._1
                val tc2 = pair2._2
                view1 < view2 and
                tc2.high_tip != None and
                tc1.high_tip.unwrap().view > tc2.high_tip.unwrap().view
            })
        })
                
    def missing_tip_w = not(missing_tip)


}

module test {
  import monadbft(validators = Set("v1", "v2", "v3", "v4"), F = 1).*

}