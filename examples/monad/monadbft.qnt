// -*- mode: Bluespec; -*-

/**
 * Specification of MonadBFT Consensus [1]
 *
 * [1]: https://arxiv.org/pdf/2502.20692
 *
 * Yassine Boukhari, Josef Widder and Gabriela Moreira,
 * Informal Systems, 2025
 */
module monadbft {
  import basicSpells.* from "./basicSpells"

  // TODO: this is just a placeholder
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

    // Extra variables to provide data availability and abstract some of the logic.

    // All the proposals that circulated in the network to avoid network requests if block is missing.
    // This field should be removed/replaced when the block recovery is implemented.
    proposals: Set[Proposal],
    // Mapping from proposal id to its ancestors, serves as an accumulator to avoid recursion for QC tree checks.
    ancestors: ProposalID -> Set[ProposalID],
  }

  type TimeoutEvent = int

  type Message =
    | Prop(Proposal)
    | Vote(VoteMsg)
    | Timeout(TimeoutMsg)
    | NoEndorsement(NoEndorsementMsg)

  type ConsensusOutput =
    | BroadcastProp(Proposal)
    | BroadCastTimeout(TimeoutMsg)
    | Commit(Proposal)
    | EarlyConfirmation(Proposal)
    | Confirmation(Proposal)
    | SendVoteToNextLeader((Address, VoteMsg))
    | StartTimeout(TimeoutEvent)
  // Algorithm 5 (block recovery) has more responses

  type Bookkeeping = {
    committed_proposals: Address -> Set[Proposal],
    msgHistory: Set[Message],
    timeoutHistory: Set[TimeoutEvent],
  }

  // Define types for the parameterized CSMI types with the proper type arguments
  // for MonadBFT
  type LocalState = {
    process_id: Address,
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

    // Extra variables to provide data availability and abstract some of the logic.

    // All the proposals that circulated in the network to avoid network requests if block is missing.
    // This field should be removed/replaced when the block recovery is implemented.
    proposals: Set[Proposal],
    // Mapping from proposal id to its ancestors, serves as an accumulator to avoid recursion for QC tree checks.
    ancestors: ProposalID -> Set[ProposalID]
  }
  type ConsensusResult = {
    state: LocalState,
    output: Set[ConsensusOutput]
  }
  type Environment = {
    system: Address -> LocalState,
    msgBuffer: Address -> Set[Message],
    activeTimeouts: Address -> Set[TimeoutEvent],
    bookkeeping: Bookkeeping,
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

  pure def add_timeouts(s: LocalState, view: int, timeouts: Set[TimeoutMsg]): LocalState = {
    { ...s, timeouts: s.timeouts.put(view, timeouts) }
  }

  pure def mark_already_broadcast_timeout(s: LocalState, view: int): LocalState = {
    { ...s, timeouts_already_broadcast: s.timeouts_already_broadcast.setAdd(view) }
  }

  pure def was_timeout_already_broadcast(s: LocalState, view: int): bool = {
    s.timeouts_already_broadcast.contains(view)
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

  /// Get a proposal based on the proposal id
  pure def get_proposal(s: LocalState, id: ProposalID): Proposal =
    s.proposals.find(p => p.proposal_id == id).unwrap()

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
  pure def block_present(s: LocalState, bh: BlockHeader): bool = {
    s.proposals.exists(p => p.block.header_from_block() == bh)
  }

  /// Fetch the block from the local state
  pure def get_present_block(s: LocalState, bh: BlockHeader): Block = {
    s.proposals.find(p => p.block.header_from_block() == bh).unwrap().block
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
  pure def increment_view(view: int, s: LocalState): ConsensusResult = {
    if (view >= s.curView)
      // Increment view to next and reset the timer, old timers are discarded at apply_effect
      { state: { ...s, curView: view + 1 }, output: Set(StartTimeout(view + 1)) }
    else
      no_output(s)
  }


  /// Alg 4 line 10
  /// Output = (TC, Side effects, bool: whether to trigger timeout event)
  pure def handle_timeout(t: TimeoutMsg, s: LocalState): (Option[TC], ConsensusResult)  = {
    val v = t.view

    if (v < s.curView) (None, no_output(s)) else

    pure val res = increment_view(t.tip.block_header.qc.view, s)
      .and_then(s => increment_view(t.tip.view, s))

    pure val res2 = res.state.and_then_state(s => {
      // Timeout is new, let's accumulate it
      val acc_timeouts = s.timeouts.getOrElse(v, Set()).setAdd(t)
      s.add_timeouts(v, acc_timeouts).and_then_state(s => {
        // Check if we have a quorum
        if (acc_timeouts.size() >= Q) {
          val tc = build_tc(acc_timeouts, s.process_id)
          (Some(tc), increment_view(tc.view, s))
        } else if (acc_timeouts.size() >= F + 1 and not(s.timeouts_already_broadcast.contains(v))) {
          // TRIGGER TIMEOUT EVENT
          (None, s.mark_already_broadcast_timeout(v).trigger_timeout_event())
        } else {
          (None, no_output(s))
        }
      })
    })

    (res2._1, join_results(res, res2._2))
  }

  /// Alg 4 line 25
  pure def handle_vote(vote: VoteMsg, s: LocalState): (Option[QC], ConsensusResult) = {
    val v = vote.view
    val id = vote.proposal_id
    
    if (v < s.curView) (None, no_output(s)) else

    // Vote is new, let's accumulate it
    val acc_votes = s.votes.getOrElse(id, Set()).setAdd(vote)

    s.add_votes(id, acc_votes).and_then_state(s => {
      // Check if we have a quorum
      if (acc_votes.size() >= Q) {
        val qc = build_qc(acc_votes, s.process_id, state_hash(s))
        (Some(qc), increment_view(qc.view, s))
      } else {
        (None, no_output(s))
      }
    })
  }

  //
  // Algorithm 2 (page 15)
  // Consensus for Validator i
  // 

  /// Alg 2 line 3 (Only for the leader)
  pure def receive_vote_msg(s: LocalState, v: VoteMsg): ConsensusResult = {
    if (not(s.i_am_leader())) no_output(s) else
    // Line 3
    pure val r = handle_vote(v, s)
    pure val qc = r._1
    pure val res = r._2

    res.and_then(s => {
      if (qc == None) no_output(s) else

      val new_block = build_block(qc.unwrap(), BLOCK_PAYLOAD)
      val p = build_proposal(s.curView, new_block, None, None, s.process_id)
      { state: s, output: Set(BroadcastProp(p)) }
    })
  }

  /// Alg 2 line 49
  /// As opposed to the paper, we write the timeout event as a function that is called by the timeout handler.
  /// Instead of of a "upon" statement that gets triggered.
  /// Warning: The upon trigger event block is not clear on its synchrony assumptions. 
  pure def trigger_timeout_event(s: LocalState): ConsensusResult = {
    pure val timeout_msg = {
      view: s.curView,
      // TODO: check if this is safe, it is not specified in the paper, made me think it is an option (Line 50)
      tip: s.tip.unwrap(),
      tc: { view: s.curView, high_tip: None, tips: Set(), sigma: s.process_id },
      sigma: s.process_id
    }

    {
      state: { ...s, highest_voted_view: max(s.highest_voted_view, s.curView) },
      output: Set(BroadCastTimeout(timeout_msg))
    }
  }

  /// Alg 2 line 10 / line 52 (leader/ non-leader)
  pure def receive_timeout_msg(s: LocalState, t: TimeoutMsg): ConsensusResult = {
    pure val res = handle_timeout(t, s)
    pure val tc = res._1
    res._2.and_then(s => {
      // line 52 (non-leader)
      if (not(s.i_am_leader())) no_output(s) else

      // line 11 (leader)

      // Not enough timeout messages to form tc
      if (tc == None) no_output(s) else

      { ...s, last_tc: tc, high_tip: tc.unwrap().high_tip }.and_then_state(s => {
        // TODO: it should be safe to unwrap here, but we should check.
        val high_tip = tc.unwrap().high_tip.unwrap()

        // if block and its payload (block.payload) for high tip is present
        if (s.block_present(high_tip.block_header)) {
          // Line 17
          val block = s.get_present_block(high_tip.block_header)
          val p = build_proposal(s.curView, block, tc, None, s.process_id)
          { state: s, output: Set(BroadcastProp(p)) }
        } else
          // Line 18-19-20 recoveringcurView ← true; SendRecoveryRequest(curView, high tip, tc);
          // TODO: For the moment this is replaced by fetching the block from the DA variable for debugging purposes
          val block = s.get_present_block(high_tip.block_header)
          val p = build_proposal(s.curView, block, tc, None, s.process_id)
          { state: s, output: Set(BroadcastProp(p)) }
      })
    })
  }

  // Alg 2 line 34
  pure def receive_proposal_msg(s: LocalState, p: Proposal): ConsensusResult = {
    match p.tc {
      | None => no_output(s)
      | Some(tc) => increment_view(tc.view, s)
    }.and_then(s => {
      increment_view(p.block.qc.view, s)
    }).and_then(s => {
      // TODO: add leader check here -> Is this message coming form the leader of the view?
      // Warning: is the view being updated before the Leader check? Lines 35-36.
      if (p.view != s.curView or not (is_leader(s, p.sigma))) no_output(s) else

      // Warning: The view being updated before the safety check.
      if (not(safety_check(p) and p.view > max(s.highest_voted_view, p.block.qc.view))) no_output(s) else

      // Line 38
      pure val parent_proposal = s.get_proposal(p.parent_id())
      pure val grandparent_proposal = s.get_proposal(parent_proposal.parent_id())

      // Line 41
      pure val commit = if (p.block.qc.view == parent_proposal.block.qc.view + 1)
        Set(Commit(grandparent_proposal), Confirmation(p))
      else
        Set()

      // Line 43
      pure val early_confirmation = if (p.view == p.block.qc.view + 1) // Warning: typo in the paper
        Set(EarlyConfirmation(parent_proposal))
      else
        Set()

      // Line 44 - If ledger conflicts with parent proposal, revert to the common ancestor.
      pure val reverted_ledger = if (proposal_conflicts(s.ledger, parent_proposal, s.ancestors))
        revert_ledger(s.ledger, parent_proposal, s.ancestors)
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
      pure val send_vote = Set(SendVoteToNextLeader((next_leader, vote_msg)))

      {
        state: { ...s, highest_voted_view: p.view, ledger: ledger, tip: update_tip(p) },
        output: commit.union(early_confirmation).union(send_vote)
      }
    })
  }

  //
  // Alg 5 (page 26)
  // Block Recovery
  //

  // Block recovery is not implemented yet and is simulated using the proposals variable.


  //
  //
  // State machine
  //
  //

  /// Set of validators participating in consensus
  const validators: Set[Address]
  /// Number of byzantine nodes
  const F: int

  /// Number of votes needed to reach consensus
  pure val Q = 2 * F + 1
  /// Number of nodes
  pure val N = validators.size()
  // TODO: change between runs
  pure val leaders = validators.fold(List(), (acc, v) => acc.append(v))

  /// Safety property page 10: No two correct validators commit different blocks
  /// for the same sequence number
  def safety =
    val ps = s.bookkeeping.committed_proposals.values().flatten()
    ps.forall(p1 => ps.forall(p2 => p1.block.seq == p2.block.seq implies p1 == p2))

  /// No Tail-Forking (NTF) page 10:
  def ntf =
    val votes = s.bookkeeping.msgHistory.fold(Set(), (s, x) => match x {
      | Vote(v) => s.setAdd(v)
      | _ => s
    })
    val committed_proposals = s.bookkeeping.committed_proposals.values().flatten()
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
  
  /// Witness: Search for a scenario where a proposal gets reproposed.
  def reproposal =
    not(
    val proposals = s.bookkeeping.msgHistory.fold(Set(), (s, x) => match x {
      | Prop(p) => s.setAdd(p)
      | _ => s
    })
    proposals.exists(p =>
      proposals.exists(p2 =>
        p.proposal_id != p2.proposal_id and p.block.seq == p2.block.seq))
    )
  //
  // Initialization constants
  //
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
    proposals: Set(),
    ancestors: Map(),
    timeouts: Map(),
    timeouts_already_broadcast: Set(),
    curView: 0,
    ledger: [],
    highest_voted_view: -1,
    votes: Map(),
    process_id: process_id,
  }

  pure def initialize_process(process_id: Address): LocalState = {
    val base = initialize_process_empty(process_id)
    { ... base,
        curView: 2,
        ledger: List(p1, p2),
        proposals: proposals_4,
        ancestors: ancestors_4,
        highest_voted_view: 3,
        tip: Some({
          view: 3,
          proposal_id: p3.proposal_id,
          block_header: header_from_block(b3),
          sigma: p3.sigma,
          nec: None,
        })
    }
  }

  pure val initial_bookkeeping: Bookkeeping = {
    committed_proposals: validators.mapBy(_ => Set(p1, p2)),
    msgHistory: votes1.union(votes2).map(x => Vote(x)),
    timeoutHistory: Set(),
  }

  var s: Environment
  action init : bool = all{
    s' = {
      system: validators.mapBy(v => initialize_process(v)),
      msgBuffer: validators.mapBy(_ => initial_messages),
      activeTimeouts: validators.mapBy(_ => Set()),
      bookkeeping: initial_bookkeeping,
    },
  } 

  /// This is the function that contains all the message handlers of the algorithm
  pure def receive_message(state: LocalState, msg: Message): ConsensusResult =
    match msg {
      | Prop(p) =>
          state.receive_proposal_msg(p)
      | Vote(v) =>
          state.receive_vote_msg(v)
      | Timeout(t) =>
          state.receive_timeout_msg(t)
      | NoEndorsement(n) =>
          // TODO: to be added with block recovery
          { state: state, output: Set() }
    }

  /// This is the function that contains all the timeout handlers of the algorithm
  pure def fire_timeout_event(state: LocalState, timeout: TimeoutEvent): ConsensusResult =
    if (state.curView == timeout)
      state.trigger_timeout_event()
    else
      { state: state, output: Set() }

  pure def apply_effect(env: Environment, v: Address, outputs: Set[ConsensusOutput]): Environment =
    outputs.fold(env, (e, x) => {
      match x {
        | BroadcastProp(p) =>
          // Abstraction: This was added to provide a data availability layer for the proposals to avoid having missing proposals.
          // and remove the need for a block recovery mechanism.
          // TODO: refractor this when we have a block recovery mechanism.
          // TODO: refractor this to be more readable.
          // TODO: do we need a mechanism to filter out the "bad" proposals.
          val s_da = env.system.keys().fold(env.system, (p_map, node) => // s_da = system with "data availability"
            p_map.set(node,
              { ... p_map.get(node),
                proposals : p_map.get(node).proposals.setAdd(p),
                ancestors : p_map.get(node).ancestors.put(p.proposal_id, p_map.get(node).ancestors.getOrElse(p.parent_id(), Set()).setAdd(p.parent_id()))
              }
            )
          )
          val env_with_da = { ...env, system: s_da }
          val env_with_bk = bookkeep(env_with_da, b => {
            ...b,
            msgHistory: b.msgHistory.setAdd(Prop(p)),
          })
          broadcast(env_with_bk, Prop(p))

        | BroadCastTimeout(t) => broadcast(e, Timeout(t))

        | Commit(p) => bookkeep(e, b => {
            ...b,
            committed_proposals: b.committed_proposals.setBy(v, ps => ps.setAdd(p))
          })

        | EarlyConfirmation(p) => e

        | Confirmation(p) => e

        | SendVoteToNextLeader(am) =>
          pure val updated_env = bookkeep(e, b => {
            ...b, msgHistory: b.msgHistory.setAdd(Vote(am._2)),
          })

          broadcast(updated_env, Vote(am._2))

        | StartTimeout(t) =>
          pure val existing_timeouts = get_timeouts(e, v)
          // We want to have a single active timeout per process
          if (existing_timeouts == Set() or existing_timeouts.getOnlyElement() < t)
            timeout(reset_timeouts(e, v), v, t)
          else
            e
      }
    })


  pure val TIMEOUT_PROBABILITY = 20 // 20%


  action step: bool = all{
    s.msgBuffer.values().flatten() != Set(),
    nondet v = oneOf(validators.filter(v => s.msgBuffer.get(v) != Set()))
    true
  }

  // -------------------------------------------------------------------------- Helpers ------------------------------------------------------------------------
  pure def bookkeep(env: Environment, f: Bookkeeping => Bookkeeping): Environment = {
    { ...env, bookkeeping: f(env.bookkeeping) }
  }

  pure def broadcast(env: Environment, msg: Message): Environment = {
    { ...env, msgBuffer: env.msgBuffer.transformValues(v => v.setAdd(msg)) }
  }

  pure def timeout(env: Environment, v: Address, t: TimeoutEvent): Environment ={
    { ...env, activeTimeouts: env.activeTimeouts.setBy(v, ts => ts.setAdd(t)) }
  }

  pure def get_timeouts(env: Environment, v: Address): Set[TimeoutEvent] = {
    env.activeTimeouts.getOrElse(v, Set())
  }

  pure def reset_timeouts(env: Environment, v: Address): Environment = {
    { ...env, activeTimeouts: env.activeTimeouts.set(v, Set()) }
  }

  pure def join_results(
    res1: ConsensusResult,
    res2: ConsensusResult
  ): ConsensusResult = {
    { state: res2.state, output: res1.output.union(res2.output) }
  }  

  pure def and_then(res: ConsensusResult, f: LocalState => ConsensusResult): ConsensusResult = {
    pure val new_res = f(res.state)
    join_results(res, new_res)
  }

  pure def and_then_state(
    state: LocalState,
    f: (LocalState) => r
  ): r = {
    f(state)
  }

  pure def no_output(s: LocalState): ConsensusResult = {
    { state: s, output: Set() }
  }
  
 } // end of module monadbft


module valid {
  import monadbft(validators = Set("v1", "v2", "v3", "v4"), F = 1).*
} // end of module test
