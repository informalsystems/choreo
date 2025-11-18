// -*- mode: Bluespec; -*-

/**
 * TetraBFT Consensus in Choreo Framework
 *
 * Based on "TetraBFT: Reducing Latency of Unauthenticated, Responsive BFT Consensus"
 * by Qianyu Yu, Giuliano Losa, Xuechao Wang (PODC 2024)
 * Paper: https://arxiv.org/abs/2405.02615
 *
 * TetraBFT achieves consensus in 5 message delays without cryptographic signatures.
 *
 * PROTOCOL STRUCTURE (Section 3.2):
 * Seven sequential phases: suggest/proof → proposal → vote-1 → vote-2 → vote-3 → vote-4 → view-change
 * Good-case consensus achieves decision in 5 phases (suggest/proof through vote-4).
 *
 * SAFETY RULES (Section 3.2):
 * - Rule 1: Leader determines safe value from quorum of suggests
 * - Rule 2: Node claims value safe in suggest using vote-2 history
 * - Rule 3: Follower verifies proposal safety from quorum of proofs
 * - Rule 4: Node claims value safe in proof using vote-1 history
 *
 * VIEW CHANGE: Timeout-based view transitions to ensure liveness
 *
 * Yassine & Claude Code, 2025
 */
module tetrabft {
  import basicSpells.* from "./spells/basicSpells"
  import option.* from "./spells/option"
  import types.* from "./types"
  import safety_rules.* from "./safety_rules"
  // Import choreo with qualified names to avoid conflicts
  import choreo(processes = NODES) as choreo from "./choreo"

  // ==========================================================================
  // Constants (Module Parameters)
  // ==========================================================================

  const N: int                      // Total number of nodes
  const F: int                      // Maximum Byzantine faults (n > 3f)
  const CORRECT: Set[NodeId]        // Set of correct node IDs
  const FAULTY: Set[NodeId]         // Set of Byzantine node IDs
  const INITIAL_GST_VIEW: int       // View at which GST occurs
  const MAX_VIEWS: int              // Maximum views to explore

  // ==========================================================================
  // Derived Values
  // ==========================================================================

  pure val QUORUM_SIZE = N - F      // 2f + 1 for n = 3f + 1
  pure val BLOCKING_SIZE = F + 1    // f + 1 nodes
  pure val NODES: Set[NodeId] = CORRECT.union(FAULTY)



  // ==========================================================================
  // Choreo Type Aliases
  // ==========================================================================

  type LocalState = choreo::LocalState[NodeId, StateFields]
  type LocalContext = choreo::LocalContext[NodeId, StateFields, Message, Event, Extensions]
  type Transition = choreo::Transition[NodeId, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[NodeId, StateFields, Message, Event, Extensions]

  // ==========================================================================
  // Helper Functions
  // ==========================================================================

  pure def get_leader(ext: Extensions, view: View): NodeId = {
    if (view < ext.leaders.length()) {
      ext.leaders[view]
    } else {
      val all_nodes = CORRECT.union(FAULTY).fold(List(), (acc, id) => acc.append(id))
      all_nodes[view % all_nodes.length()]
    }
  }

  pure def is_leader(ctx: LocalContext): bool = {
    get_leader(ctx.extensions, ctx.state.current_view) == ctx.state.process_id
  }

  // Update vote record (highest and second-highest)
  pure def update_vote_record(
    self: LocalState,
    phase: VotePhase,
    vote_record: VoteRecord
  ): LocalState = {
    val current_highest = self.highest_votes.get(phase)
    match (current_highest) {
      | None => {
        { ...self,
          highest_votes: self.highest_votes.set(phase, Some(vote_record))
        }
      }
      | Some(h) => {
        if (vote_record.view > h.view) {
          { ...self,
            highest_votes: self.highest_votes.set(phase, Some(vote_record)),
            second_highest_votes: self.second_highest_votes.set(phase, Some(h))
          }
        } else if (vote_record.view < h.view) {
          val current_second = self.second_highest_votes.get(phase)
          match (current_second) {
            | None => {
              { ...self,
                second_highest_votes: self.second_highest_votes.set(phase, Some(vote_record))
              }
            }
            | Some(sh) => {
              if (vote_record.view > sh.view) {
                { ...self,
                  second_highest_votes: self.second_highest_votes.set(phase, Some(vote_record))
                }
              } else {
                self
              }
            }
          }
        } else {
          self
        }
      }
    }
  }

  // ==========================================================================
  // Quorum Detection on Messages (Choreo-style)
  // ==========================================================================

  // Get all votes for a specific phase and view from messages
  pure def get_votes_from_messages(
    messages: Set[Message],
    phase: VotePhase,
    view: View
  ): Set[{ value: Value, from: NodeId }] = {
    messages.fold(Set(), (acc, msg) => match (msg) {
      | MsgVote(v) => {
        if (v.phase == phase and v.view == view) {
          acc.union(Set({ value: v.value, from: v.from }))
        } else {
          acc
        }
      }
      | _ => acc
    })
  }

  // Group votes by value and count unique voters
  pure def count_votes_by_value(
    votes: Set[{ value: Value, from: NodeId }]
  ): Value -> Set[NodeId] = {
    votes.fold(Map(), (acc, vote) => {
      val current = if (acc.keys().contains(vote.value)) {
        acc.get(vote.value)
      } else {
        Set()
      }
      acc.put(vote.value, current.union(Set(vote.from)))
    })
  }

  // Find values that have quorum support
  pure def values_with_quorum(
    messages: Set[Message],
    phase: VotePhase,
    view: View
  ): Set[Value] = {
    val votes = get_votes_from_messages(messages, phase, view)
    val vote_counts = count_votes_by_value(votes)
    vote_counts.keys().filter(v => vote_counts.get(v).size() >= QUORUM_SIZE)
  }

  // Check if any value has quorum
  pure def has_any_quorum(
    messages: Set[Message],
    phase: VotePhase,
    view: View
  ): bool = {
    values_with_quorum(messages, phase, view).size() > 0
  }

  // Get the first value with quorum (deterministic choice)
  pure def get_quorum_value(
    messages: Set[Message],
    phase: VotePhase,
    view: View
  ): Value = {
    val vs = values_with_quorum(messages, phase, view)
    vs.fold("", (acc, v) => if (acc == "") v else acc)
  }

  // ==========================================================================
  // Safety Predicates (from TLA+ spec)
  // These operate on global state for invariant checking
  // ==========================================================================

  // Convert VotePhase enum to int for comparisons
  pure def phase_to_int(p: VotePhase): int = match (p) {
    | Phase1 => 1
    | Phase2 => 2
    | Phase3 => 3
    | Phase4 => 4
  }

  pure def int_to_phase(i: int): VotePhase = {
    if (i == 1) Phase1
    else if (i == 2) Phase2
    else if (i == 3) Phase3
    else Phase4
  }

  // Get all votes from a node's state (highest and second-highest for all phases)
  pure def get_all_votes(state: LocalState): Set[VoteRecord] = {
    val phases = Set(Phase1, Phase2, Phase3, Phase4)
    phases.fold(Set(), (acc, ph) => {
      val with_highest = match (state.highest_votes.get(ph)) {
        | Some(vr) => acc.union(Set(vr))
        | None => acc
      }
      match (state.second_highest_votes.get(ph)) {
        | Some(vr) => with_highest.union(Set(vr))
        | None => with_highest
      }
    })
  }

  // Get votes for a specific phase from a node's state
  pure def get_votes_for_phase(state: LocalState, phase: VotePhase): Set[VoteRecord] = {
    val with_highest = match (state.highest_votes.get(phase)) {
      | Some(vr) => Set(vr)
      | None => Set()
    }
    match (state.second_highest_votes.get(phase)) {
      | Some(vr) => with_highest.union(Set(vr))
      | None => with_highest
    }
  }

  // ClaimsSafeAt: v is safe in view r2 according to p's votes in phase before view r
  // This checks if a blocking set can certify safety
  // A node claims v is safe at r2 if:
  // - r2 == 0 (trivially safe), OR
  // - The node has a vote in `phase` at some view vt1.view where r2 <= vt1.view < r, and either:
  //   - vt1.value == v (voted for v), OR
  //   - There exists another vote vt2 in `phase` where r2 <= vt2.view < vt1.view and vt2.value != vt1.value
  //     (evidence of conflicting votes means no single value was locked)
  pure def claims_safe_at(
    state: LocalState,
    v: Value,
    r: View,
    r2: View,
    phase: VotePhase
  ): bool = {
    val votes = get_votes_for_phase(state, phase)
    or {
      r2 == 0,
      votes.exists(vt1 => and {
        vt1.view < r,
        r2 <= vt1.view,
        or {
          vt1.value == v,
          votes.exists(vt2 => and {
            r2 <= vt2.view,
            vt2.view < vt1.view,
            vt2.value != vt1.value
          })
        }
      })
    }
  }

  // ShowsSafeAt: Whether value v is safe to vote for/propose in view r
  // phaseA=4, phaseB=1 for voting; phaseA=3, phaseB=2 for proposing
  // A quorum Q shows v is safe at r if:
  // - r == 0 (trivially safe), OR
  // - Every member of Q is in view at least r, AND either:
  //   - No member of Q ever voted in phaseA before view r, OR
  //   - There exists a view r2 < r where:
  //     - All members of Q that voted in phaseA did so at or before r2
  //     - All who voted at r2 voted for v
  //     - A blocking set claims v is safe at r2
  pure def shows_safe_at_global(
    sys: NodeId -> LocalState,
    Q: Set[NodeId],
    v: Value,
    r: View,
    phaseA: VotePhase,
    phaseB: VotePhase
  ): bool = {
    or {
      r == 0,
      and {
        // Every member of Q is in view at least r
        Q.forall(q => sys.get(q).current_view >= r),
        or {
          // Members of Q never voted in phaseA before view r
          // Check that highest vote for phaseA is None or happened at view >= r
          Q.forall(q => {
            val highest = sys.get(q).highest_votes.get(phaseA)
            match (highest) {
              | None => true
              | Some(vr) => vr.view >= r  // No votes before r
            }
          }),
          // Or there exists a view r2 < r where...
          0.to(r - 1).exists(r2 => and {
            // All members of Q that voted in phaseA did so at or before r2
            // and all who voted at r2 voted for v
            Q.forall(q => {
              val highest = sys.get(q).highest_votes.get(phaseA)
              match (highest) {
                | None => true
                | Some(vr) => and {
                  vr.view <= r2,
                  (vr.view == r2) implies (vr.value == v)
                }
              }
            }),
            // v must be safe at r2 (blocking set claims it)
            // At least f+1 nodes must claim safety (any f+1 nodes form a blocking set)
            val claiming_nodes = Q.filter(q => claims_safe_at(sys.get(q), v, r, r2, phaseB))
            claiming_nodes.size() >= BLOCKING_SIZE
          })
        }
      }
    }
  }

  // Check if a quorum exists that shows safety
  pure def exists_safe_quorum(
    sys: NodeId -> LocalState,
    v: Value,
    r: View,
    phaseA: VotePhase,
    phaseB: VotePhase
  ): bool = {
    // Check if correct nodes form a quorum and show safety
    val correct_subset = CORRECT.filter(n => sys.get(n).current_view >= r)
    correct_subset.size() >= QUORUM_SIZE and shows_safe_at_global(sys, correct_subset, v, r, phaseA, phaseB)
  }

  // ==========================================================================
  // Initialization
  // ==========================================================================

  pure def initialize(id: NodeId): LocalState = {
    {
      process_id: id,
      current_view: 0,
      phase: PhaseSendSuggestProof,  // Start at the beginning of view 0
      highest_votes: Map(Phase1 -> None, Phase2 -> None, Phase3 -> None, Phase4 -> None),
      second_highest_votes: Map(Phase1 -> None, Phase2 -> None, Phase3 -> None, Phase4 -> None),
      decided: None
    }
  }

  action init = choreo::init({
    system: NODES.mapBy(id => initialize(id)),
    messages: NODES.mapBy(id => Set()),
    events: NODES.mapBy(id => Set()),
    extensions: {
      leaders: List("n0", "n1", "n2", "n3"),
      GST_view: INITIAL_GST_VIEW,
      ghost_step: StepPropose
    }
  })

  // ==========================================================================
  // Listeners
  // ==========================================================================

  // ==========================================================================
  // Phase 0: View Start - Send Suggest+Proof Messages
  // Paper Section 3.2: "suggest/proof" phase
  // ==========================================================================
  // Both suggest and proof messages are sent at the START of each view (view > 0).
  // - Suggest: Contains vote-2 and vote-3 history (sent to leader, used for Rule 1)
  // - Proof: Contains vote-1 and vote-4 history (broadcast, used for Rule 3)
  // View 0 is special: nodes skip this phase since there's no prior voting history.

  // Non-leader: Send suggest to leader + broadcast proof
  pure def listen_start_view_nonleader(ctx: LocalContext): Set[()] = {
    val self = ctx.state
    if (and {
      not(is_leader(ctx)),
      self.phase == PhaseSendSuggestProof,
      self.current_view < MAX_VIEWS,
      CORRECT.contains(self.process_id),
      self.decided == None,
      self.current_view > 0  // View 0 is special - skip suggest/proof
    }) {
      Set(())
    } else {
      Set()
    }
  }

  def upon_start_view_nonleader(ctx: LocalContext, _trigger: ()): Transition = {
    val self = ctx.state

    // Build suggest message (vote-2 and vote-3 history)
    val suggest_content: SuggestMessage = {
      highest_vote2: self.highest_votes.get(Phase2),
      second_highest_vote2: self.second_highest_votes.get(Phase2),
      latest_vote3: self.highest_votes.get(Phase3)
    }
    val suggest_msg = MsgSuggest({
      from: self.process_id,
      content: suggest_content
    })

    // Build proof message (vote-1 and vote-4 history)
    val proof_content: ProofMessage = {
      highest_vote1: self.highest_votes.get(Phase1),
      second_highest_vote1: self.second_highest_votes.get(Phase1),
      latest_vote4: self.highest_votes.get(Phase4)
    }
    val proof_msg = MsgProof({
      from: self.process_id,
      content: proof_content
    })

    // Send suggest to leader + broadcast proof + transition to waiting
    val leader = get_leader(ctx.extensions, self.current_view)
    val new_self = { ...self, phase: PhaseWaitingProposal }

    // Schedule timeout event for this view
    {
      effects: Set(
        choreo::Send({ to: leader, message: suggest_msg }),
        choreo::Broadcast(proof_msg),
        choreo::TriggerEvent(EventViewTimeout({ view: self.current_view }))
      ),
      post_state: new_self
    }
  }

  // Leader: Broadcast proof only (doesn't send suggest to itself)
  pure def listen_start_view_leader(ctx: LocalContext): Set[()] = {
    val self = ctx.state
    if (and {
      is_leader(ctx),
      self.phase == PhaseSendSuggestProof,
      self.current_view < MAX_VIEWS,
      CORRECT.contains(self.process_id),
      self.decided == None,
      self.current_view > 0  // View 0 is special
    }) {
      Set(())
    } else {
      Set()
    }
  }

  def upon_start_view_leader(ctx: LocalContext, _trigger: ()): Transition = {
    val self = ctx.state

    // Build proof message (vote-1 and vote-4 history)
    val proof_content: ProofMessage = {
      highest_vote1: self.highest_votes.get(Phase1),
      second_highest_vote1: self.second_highest_votes.get(Phase1),
      latest_vote4: self.highest_votes.get(Phase4)
    }
    val proof_msg = MsgProof({
      from: self.process_id,
      content: proof_content
    })

    // Broadcast proof + transition to collecting suggests
    val new_self = { ...self, phase: PhaseCollectingSuggests }

    // Schedule timeout event for this view
    {
      effects: Set(
        choreo::Broadcast(proof_msg),
        choreo::TriggerEvent(EventViewTimeout({ view: self.current_view }))
      ),
      post_state: new_self
    }
  }

  // View 0 special case: Skip suggest/proof, go straight to proposal/waiting
  pure def listen_view0_skip(ctx: LocalContext): Set[()] = {
    val self = ctx.state
    if (and {
      self.phase == PhaseSendSuggestProof,
      self.current_view == 0,  // Only view 0
      CORRECT.contains(self.process_id),
      self.decided == None
    }) {
      Set(())
    } else {
      Set()
    }
  }

  def upon_view0_skip(ctx: LocalContext, _trigger: ()): Transition = {
    val self = ctx.state
    // View 0: skip suggest/proof phase
    val new_phase = if (is_leader(ctx)) {
      PhaseCollectingSuggests  // Leader goes to proposing (will propose immediately)
    } else {
      PhaseWaitingProposal  // Non-leader waits for proposal
    }
    val new_self = { ...self, phase: new_phase }
    // Schedule timeout for view 0 (non-deterministic event)
    {
      effects: Set(choreo::TriggerEvent(EventViewTimeout({ view: 0 }))),
      post_state: new_self
    }
  }

  // Helper: Extract SuggestMessage contents from messages
  pure def extract_suggests(messages: Set[Message]): Set[SuggestMessage] = {
    messages.fold(Set(), (acc, msg) => match (msg) {
      | MsgSuggest(s) => acc.union(Set(s.content))
      | _ => acc
    })
  }

  // ==========================================================================
  // Helper: Determine safe value using Rule 1 (Algorithm 4)
  // Paper Section 3.2, Algorithm 4 (Appendix A)
  // ==========================================================================
  /**
   * Leader determines which value is safe to propose based on suggests.
   * Implements Rule 1 by checking all candidate values from the suggest history.
   *
   * Note: Leader includes its OWN vote history in the quorum count (Section 3.2).
   */
  pure def determine_safe_value(ctx: LocalContext, messages: Set[Message]): Value = {
    val suggests = extract_suggests(messages)
    val current_view = ctx.state.current_view

    // Leader includes its OWN knowledge in the suggest set
    // The leader knows its own vote history, which counts toward the quorum
    val leader_suggest: SuggestMessage = {
      highest_vote2: ctx.state.highest_votes.get(Phase2),
      second_highest_vote2: ctx.state.second_highest_votes.get(Phase2),
      latest_vote3: ctx.state.highest_votes.get(Phase3)
    }
    val all_suggests = suggests.union(Set(leader_suggest))

    // Get possible values to check for safety
    // Include ALL values mentioned in suggests (highest vote-2, vote-3)
    val suggested_values = all_suggests.fold(Set(), (acc, sug) => {
      val with_v2 = match sug.highest_vote2 {
        | Some(v2) => acc.union(Set(v2.value))
        | None => acc
      }
      val with_v3 = match sug.latest_vote3 {
        | Some(v3) => with_v2.union(Set(v3.value))
        | None => with_v2
      }
      with_v3
    })

    // Add own process ID as another candidate
    val candidate_values = suggested_values.union(Set(ctx.state.process_id))

    // Find a value that satisfies Rule 1 (leader_determines_safe)
    val safe_values = candidate_values.filter(v =>
      leader_determines_safe(all_suggests, v, current_view, BLOCKING_SIZE)
    )

    if (safe_values.size() > 0) {
      // Prefer values from highest vote-3 (locked values)
      val highest_v3_value = all_suggests.fold(None, (acc, sug) => {
        match sug.latest_vote3 {
          | None => acc
          | Some(v3) => match acc {
            | None => Some(v3)
            | Some(current) => if (v3.view > current.view) Some(v3) else acc
          }
        }
      })
      match highest_v3_value {
        | Some(vr) => if (safe_values.contains(vr.value)) vr.value else {
          // Pick first safe value deterministically
          safe_values.fold("", (acc, v) => if (acc == "") v else acc)
        }
        | None => safe_values.fold("", (acc, v) => if (acc == "") v else acc)
      }
    } else {
      // Fallback: propose own value (should not reach here in correct execution)
      ctx.state.process_id
    }
  }

  // Helper: Extract ProofMessage contents from messages
  pure def extract_proofs(messages: Set[Message]): Set[ProofMessage] = {
    messages.fold(Set(), (acc, msg) => match (msg) {
      | MsgProof(p) => acc.union(Set(p.content))
      | _ => acc
    })
  }

  // ==========================================================================
  // Phase 1: Proposal Phase
  // Paper Section 3.2: "proposal" phase
  // ==========================================================================
  // Leader broadcasts a proposal after collecting a quorum of suggests.
  // The proposed value must satisfy Rule 1 (leader_determines_safe).

  pure def listen_propose(ctx: LocalContext): Set[Value] = {
    val self = ctx.state
    if (and {
      is_leader(ctx),
      self.phase == PhaseCollectingSuggests,  // Leader is ready to propose
      self.current_view < MAX_VIEWS,
      CORRECT.contains(ctx.state.process_id),
      self.decided == None
    }) {
      // Collect suggests to determine safe value
      val suggests = ctx.messages.filter(msg => match (msg) {
        | MsgSuggest(s) => true
        | _ => false
      })

      // In view 0: no suggests needed (all values safe)
      // In view > 0: wait for quorum of suggests, then use Rule 1
      // NOTE: Leader counts its OWN knowledge as part of the quorum
      // So we need QUORUM_SIZE - 1 suggests from others
      if (self.current_view == 0) {
        // View 0: propose own value immediately
        Set(self.process_id)
      } else if (suggests.size() >= QUORUM_SIZE - 1) {
        // View > 0: use Rule 1 to find safe value
        // Leader's knowledge is included in determine_safe_value
        Set(determine_safe_value(ctx, suggests))
      } else {
        // Not enough suggests yet, wait
        Set()
      }
    } else {
      Set()
    }
  }

  def upon_propose(ctx: LocalContext, value: Value): Transition = {
    val self = ctx.state
    val proposal = MsgProposal({
      view: self.current_view,
      value: value,
      from: self.process_id
    })

    val new_self = { ...self, phase: PhaseVote1 }

    {
      effects: Set(choreo::Broadcast(proposal)),
      post_state: new_self
    }
  }

  // ==========================================================================
  // Phase 2: Vote-1
  // Paper Section 3.2: "vote-1" phase
  // ==========================================================================
  // Vote-1: "I accept this proposal"
  //   // Follower checks Rule 3 using PROOF messages (vote-1, vote-4 history)
  //   val is_safe = follower_determines_safe(proofs, proposal.value, view, BLOCKING_SIZE)
  //   if (is_safe) {
  //     broadcast VOTE-1  // ← "Proposal passes my safety check"
  //   }
  //   Why needed?: First vote after proposal, verified against proof history
  //
  // Followers vote for proposal if it passes Rule 3 (follower_determines_safe).
  // Verification uses quorum of proof messages (Algorithm 5 in Appendix A).

  pure def listen_vote1(ctx: LocalContext): Set[Message] = {
    ctx.messages.filter(msg => match (msg) {
      | MsgProposal(p) => and {
          p.view == ctx.state.current_view,
          // Non-leaders wait in PhaseWaitingProposal, leader waits in PhaseVote1
          or {
            ctx.state.phase == PhaseWaitingProposal,
            ctx.state.phase == PhaseVote1
          },
          ctx.state.decided == None
        }
      | _ => false
    })
  }

  def upon_vote1(ctx: LocalContext, msg: Message): Transition = {
    match (msg) {
      | MsgProposal(p) => {
        val self = ctx.state

        // Apply Rule 3: Follower determines safe before voting
        val proofs = extract_proofs(ctx.messages)

        // Check if value is safe to vote for (Rule 3)
        // In view 0 or with enough proofs showing safety, we can vote
        val is_safe = if (p.view == 0) {
          true  // View 0: all values safe
        } else if (proofs.size() >= QUORUM_SIZE - 1) {
          // We have enough proofs (quorum minus self since we count our own proof)
          follower_determines_safe(proofs, p.value, p.view, BLOCKING_SIZE)
        } else {
          // NOT SAFE: Insufficient proofs to verify proposal safety
          // Do not vote - this is critical for safety
          false
        }

        if (is_safe) {
          val vote = MsgVote({
            phase: Phase1,
            view: p.view,
            value: p.value,
            from: self.process_id
          })

          // Update vote record for vote-1
          val vote_record = { view: p.view, value: p.value, voter: self.process_id }
          val updated_self = update_vote_record(self, Phase1, vote_record)

          val new_self = { ...updated_self, phase: PhaseVote2 }

          {
            effects: Set(choreo::Broadcast(vote)),
            post_state: new_self
          }
        } else {
          // Value not safe - don't vote (would trigger view change in full impl)
          { effects: Set(), post_state: self }
        }
      }
      | _ => { effects: Set(), post_state: ctx.state }
    }
  }

  // ==========================================================================
  // Phase 3: Vote-2
  // Paper Section 3.2: "vote-2" phase
  // ==========================================================================
  // Vote-2: "Quorum accepted the proposal"
  //   // Upon seeing quorum of vote-1 for value v
  //   if (has_quorum(messages, Phase1, view, v)) {
  //     broadcast VOTE-2  // ← Goes into SUGGEST messages (used by Rule 1, Rule 2)
  //   }
  //   Why needed?: Aggregates individual votes (vote-1) into quorum-based progress
  //   Goes into: SUGGEST messages for leader safety checking (Rule 1, Rule 2)
  //
  // Nodes vote-2 upon seeing quorum of vote-1 for a value.
  // Vote-2 history is included in suggest messages (used by Rule 1 and Rule 2).

  pure def listen_vote2(ctx: LocalContext): Set[Value] = {
    if (and {
      ctx.state.phase == PhaseVote2,
      ctx.state.decided == None,
      has_any_quorum(ctx.messages, Phase1, ctx.state.current_view)
    }) {
      // Return values that have quorum
      values_with_quorum(ctx.messages, Phase1, ctx.state.current_view)
    } else {
      Set()
    }
  }

  def upon_vote2(ctx: LocalContext, value: Value): Transition = {
    val self = ctx.state
    val vote2 = MsgVote({
      phase: Phase2,
      view: self.current_view,
      value: value,
      from: self.process_id
    })

    // Update vote record for vote-2
    val vote_record = { view: self.current_view, value: value, voter: self.process_id }
    val updated_self = update_vote_record(self, Phase2, vote_record)

    val new_self = { ...updated_self, phase: PhaseVote3 }

    {
      effects: Set(choreo::Broadcast(vote2)),
      post_state: new_self
    }
  }

  // ==========================================================================
  // Phase 4: Vote-3
  // Paper Section 3.2: "vote-3" phase
  // ==========================================================================
  // Vote-3: "Value is LOCKED"
  //   // Upon seeing quorum of vote-2 for value v
  //   if (has_quorum(messages, Phase2, view, v)) {
  //     broadcast VOTE-3  // ← Creates "lock" - prevents conflicting proposals in future views
  //   }
  //   Why needed?: Creates commitment (lock) that constrains future leader proposals
  //   Goes into: SUGGEST messages as latest_vote3 (Rule 1 uses this)
  //
  // Nodes vote-3 upon seeing quorum of vote-2 for a value.
  // Vote-3 creates a "lock" - suggest messages track latest vote-3 (Rule 1 condition b).

  pure def listen_vote3(ctx: LocalContext): Set[Value] = {
    if (and {
      ctx.state.phase == PhaseVote3,
      ctx.state.decided == None,
      has_any_quorum(ctx.messages, Phase2, ctx.state.current_view)
    }) {
      values_with_quorum(ctx.messages, Phase2, ctx.state.current_view)
    } else {
      Set()
    }
  }

  def upon_vote3(ctx: LocalContext, value: Value): Transition = {
    val self = ctx.state
    val vote3 = MsgVote({
      phase: Phase3,
      view: self.current_view,
      value: value,
      from: self.process_id
    })

    // Update vote record for vote-3
    val vote_record = { view: self.current_view, value: value, voter: self.process_id }
    val updated_self = update_vote_record(self, Phase3, vote_record)

    val new_self = { ...updated_self, phase: PhaseVote4 }

    {
      effects: Set(choreo::Broadcast(vote3)),
      post_state: new_self
    }
  }

  // ==========================================================================
  // Phase 5: Vote-4
  // Paper Section 3.2: "vote-4" phase
  // ==========================================================================
  // Vote-4: "Ready to commit"
  //   // Upon seeing quorum of vote-3 for value v
  //   if (has_quorum(messages, Phase3, view, v)) {
  //     broadcast VOTE-4  // ← Goes into PROOF messages (used by Rule 3, Rule 4)
  //   }
  //   Why needed?: Final vote before decision, verified against vote-3 quorum
  //   Goes into: PROOF messages for follower safety checking (Rule 3, Rule 4)
  //
  // Nodes vote-4 upon seeing quorum of vote-3 for a value.
  // Vote-4 history is included in proof messages (used by Rule 3 and Rule 4).

  pure def listen_vote4(ctx: LocalContext): Set[Value] = {
    if (and {
      ctx.state.phase == PhaseVote4,
      ctx.state.decided == None,
      has_any_quorum(ctx.messages, Phase3, ctx.state.current_view)
    }) {
      values_with_quorum(ctx.messages, Phase3, ctx.state.current_view)
    } else {
      Set()
    }
  }

  def upon_vote4(ctx: LocalContext, value: Value): Transition = {
    val self = ctx.state
    val vote4 = MsgVote({
      phase: Phase4,
      view: self.current_view,
      value: value,
      from: self.process_id
    })

    // Update vote record for vote-4
    val vote_record = { view: self.current_view, value: value, voter: self.process_id }
    val updated_self = update_vote_record(self, Phase4, vote_record)

    // After sending vote-4, we stay in PhaseVote4 waiting for decision
    // Decision happens when we see quorum of Phase4 votes
    val new_self = { ...updated_self, phase: PhaseDecision }

    {
      effects: Set(choreo::Broadcast(vote4)),
      post_state: new_self
    }
  }

  // ==========================================================================
  // Phase 6: Decision
  // Paper Section 3.2
  // ==========================================================================
  // Nodes decide when they observe a quorum of vote-4 for a value.
  // Good-case consensus: 5 phases total (suggest/proof → proposal → vote-1 → vote-2 → vote-3 → vote-4).
  // This achieves decision in 5 message delays without cryptographic signatures.

  pure def listen_decide(ctx: LocalContext): Set[Value] = {
    if (and {
      ctx.state.phase == PhaseDecision,
      ctx.state.decided == None,
      has_any_quorum(ctx.messages, Phase4, ctx.state.current_view)
    }) {
      values_with_quorum(ctx.messages, Phase4, ctx.state.current_view)
    } else {
      Set()
    }
  }

  def upon_decide(ctx: LocalContext, value: Value): Transition = {
    val self = ctx.state
    val new_self = { ...self, decided: Some(value) }

    {
      effects: Set(choreo::TriggerEvent(EventDecide({ id: self.process_id, value: value }))),
      post_state: new_self
    }
  }

  // ==========================================================================
  // Phase 7: View Change Protocol
  // Paper Section 3.2, Section 5 (Liveness)
  // ==========================================================================
  // Ensures liveness when views don't complete within timeout.
  //
  // Triggering conditions:
  // 1. View timeout event (non-deterministic, Tendermint pattern)
  // 2. f+1 view-change messages received (early transition)
  // 3. n-f view-change messages received (quorum, actual view change)
  //


  // Helper: Count view-change messages for a specific view
  pure def count_view_change_msgs(messages: Set[Message], target_view: View): int = {
    messages.fold(0, (count, msg) => match (msg) {
      | MsgViewChange(vc) => if (vc.to_view == target_view) count + 1 else count
      | _ => count
    })
  }

  // Helper: Get maximum view from view-change messages
  pure def max_view_change_view(messages: Set[Message]): View = {
    messages.fold(-1, (max_v, msg) => match (msg) {
      | MsgViewChange(vc) => if (vc.to_view > max_v) vc.to_view else max_v
      | _ => max_v
    })
  }

  // Listener: View timeout event triggers view change
  // Non-deterministically triggered timeout event (Tendermint pattern)
  pure def listen_view_timeout(ctx: LocalContext): Set[TimeoutEvent] = {
    val self = ctx.state
    if (and {
      CORRECT.contains(self.process_id),
      self.current_view < MAX_VIEWS - 1,
      self.decided == None
    }) {
      // Check for timeout events for current view or later
      ctx.events.fold(Set(), (acc, evt) => match (evt) {
        | EventViewTimeout(te) => if (te.view >= self.current_view) acc.union(Set(te)) else acc
        | _ => acc
      })
    } else {
      Set()
    }
  }

  def upon_view_timeout(ctx: LocalContext, timeout: TimeoutEvent): Transition = {
    val self = ctx.state
    val next_view = self.current_view + 1
    val vc_msg = MsgViewChange({ to_view: next_view, from: self.process_id })

    // Broadcast view-change but don't transition yet
    // Transition happens when we receive n-f view-change messages
    {
      effects: Set(choreo::Broadcast(vc_msg)),
      post_state: self
    }
  }

  // Listener: Receive f+1 view-change messages for higher view
  // This triggers us to also send view-change (if we haven't)
  pure def listen_early_view_change(ctx: LocalContext): Set[View] = {
    val self = ctx.state
    if (and {
      CORRECT.contains(self.process_id),
      self.current_view < MAX_VIEWS - 1,
      self.decided == None
    }) {
      // Check for any view > current_view that has at least f+1 messages
      (self.current_view + 1).to(MAX_VIEWS - 1).filter(v =>
        count_view_change_msgs(ctx.messages, v) >= BLOCKING_SIZE
      )
    } else {
      Set()
    }
  }

  def upon_early_view_change(ctx: LocalContext, target_view: View): Transition = {
    val self = ctx.state
    // Broadcast view-change for this view if we're behind
    val vc_msg = MsgViewChange({ to_view: target_view, from: self.process_id })
    {
      effects: Set(choreo::Broadcast(vc_msg)),
      post_state: self
    }
  }

  // Listener: Receive n-f view-change messages - actually transition
  pure def listen_view_change_quorum(ctx: LocalContext): Set[View] = {
    val self = ctx.state
    if (and {
      CORRECT.contains(self.process_id),
      self.current_view < MAX_VIEWS - 1,
      self.decided == None
    }) {
      // Check for any view > current_view that has at least n-f messages
      (self.current_view + 1).to(MAX_VIEWS - 1).filter(v =>
        count_view_change_msgs(ctx.messages, v) >= QUORUM_SIZE
      )
    } else {
      Set()
    }
  }

  def upon_view_change_quorum(ctx: LocalContext, new_view: View): Transition = {
    val self = ctx.state
    // Transition to the new view
    val new_self = {
      ...self,
      current_view: new_view,
      phase: PhaseSendSuggestProof  // Start at beginning of new view
    }
    {
      effects: Set(),
      post_state: new_self
    }
  }

  // ==========================================================================
  // Main Listener
  // ==========================================================================

  pure def main_listener(ctx: LocalContext): Set[Transition] = {
    Set(
      // Phase 0: View Start - Send suggest+proof at view start
      choreo::cue(ctx, listen_view0_skip, upon_view0_skip),  // View 0 special case
      choreo::cue(ctx, listen_start_view_nonleader, upon_start_view_nonleader),  // Non-leader sends suggest+proof
      choreo::cue(ctx, listen_start_view_leader, upon_start_view_leader),  // Leader sends proof only
      // Phase 1: Proposal
      choreo::cue(ctx, listen_propose, upon_propose),
      // Phase 2-5: Voting rounds
      choreo::cue(ctx, listen_vote1, upon_vote1),
      choreo::cue(ctx, listen_vote2, upon_vote2),
      choreo::cue(ctx, listen_vote3, upon_vote3),
      choreo::cue(ctx, listen_vote4, upon_vote4),
      // Decision
      choreo::cue(ctx, listen_decide, upon_decide),
      // View Change Protocol
      choreo::cue(ctx, listen_view_timeout, upon_view_timeout),  // Event-based timeout (Tendermint pattern)
      choreo::cue(ctx, listen_early_view_change, upon_early_view_change),  // f+1 view-change
      choreo::cue(ctx, listen_view_change_quorum, upon_view_change_quorum)  // n-f view-change (transition)
    ).flatten()
  }

  // ==========================================================================
  // Custom Effect Handler
  // ==========================================================================

  pure def apply_custom_effect(env: GlobalContext, effect: CustomEffects): GlobalContext = {
    match (effect) {
      | ByzantineProposal(params) => {
        { ...env, extensions: { ...env.extensions, ghost_step: StepPropose } }
      }
      | ByzantineVote(params) => {
        { ...env, extensions: { ...env.extensions, ghost_step: StepVote } }
      }
      | ByzantineSilence => {
        { ...env, extensions: { ...env.extensions, ghost_step: StepIdle } }
      }
    }
  }

  // ==========================================================================
  // Main Step
  // ==========================================================================

  action step = choreo::step(
    main_listener,
    apply_custom_effect
  )

  // ==========================================================================
  // Invariants
  // ==========================================================================

  pure def agreement_inv(s: GlobalContext): bool = {
    val decided_values = s.system.keys().fold(Set(), (acc, id) => {
      if (CORRECT.contains(id)) {
        match s.system.get(id).decided {
          | Some(v) => acc.union(Set(v))
          | None => acc
        }
      } else {
        acc
      }
    })
    decided_values.size() <= 1
  }

  pure def validity_inv(s: GlobalContext): bool = {
    val all_nodes = CORRECT.union(FAULTY)
    s.system.keys().fold(true, (acc, id) => {
      if (CORRECT.contains(id)) {
        match s.system.get(id).decided {
          | Some(v) => and { acc, all_nodes.contains(v) }
          | None => acc
        }
      } else {
        acc
      }
    })
  }

  pure def has_decision(s: GlobalContext): bool = {
    s.system.keys().exists(id => {
      CORRECT.contains(id) and s.system.get(id).decided != None
    })
  }

  // ==========================================================================
  // Additional Safety Invariants (from TLA+ spec)
  // ==========================================================================

  // No future votes: process cannot have votes in views higher than their current view
  pure def no_future_vote_inv(s: GlobalContext): bool = {
    CORRECT.forall(p => {
      val state = s.system.get(p)
      val all_votes = get_all_votes(state)
      all_votes.forall(vt => vt.view <= state.current_view)
    })
  }

  // One value per phase per view: each process votes for at most one value per phase per view
  pure def one_value_per_phase_per_view_inv(s: GlobalContext): bool = {
    CORRECT.forall(p => {
      val state = s.system.get(p)
      val phases = Set(Phase1, Phase2, Phase3, Phase4)
      phases.forall(ph => {
        val votes = get_votes_for_phase(state, ph)
        // If we have both highest and second highest, they must be from different views
        votes.forall(vt1 =>
          votes.forall(vt2 =>
            (vt1.view == vt2.view) implies (vt1.value == vt2.value)
          )
        )
      })
    })
  }

  // Vote has quorum in previous phase: votes in phase > 1 require quorum support
  // For this invariant, we check that if a correct node voted in phase k,
  // then a quorum must have voted for the same value in phase k-1
  pure def vote_has_quorum_in_previous_phase_inv(s: GlobalContext): bool = {
    CORRECT.forall(p => {
      val state = s.system.get(p)
      val phases_after_1 = Set(Phase2, Phase3, Phase4)
      phases_after_1.forall(ph => {
        val current_vote = state.highest_votes.get(ph)
        match (current_vote) {
          | None => true
          | Some(vr) => {
            // Get previous phase
            val prev_ph = match (ph) {
              | Phase2 => Phase1
              | Phase3 => Phase2
              | Phase4 => Phase3
              | _ => Phase1  // Should not happen
            }
            // Check if quorum voted for this value in previous phase
            val supporting_nodes = NODES.filter(q => {
              val q_state = s.system.get(q)
              val q_vote = q_state.highest_votes.get(prev_ph)
              match (q_vote) {
                | None => false
                | Some(qvr) => qvr.view == vr.view and qvr.value == vr.value
              }
            })
            supporting_nodes.size() >= QUORUM_SIZE
          }
        }
      })
    })
  }

  // Votes are safe: vote-1 must be safe according to ShowsSafeAt(Q, v, r, 4, 1)
  // This checks that if a correct node voted-1 for v in view r, then v was safe
  pure def votes_safe_inv(s: GlobalContext): bool = {
    CORRECT.forall(p => {
      val state = s.system.get(p)
      val vote1_opt = state.highest_votes.get(Phase1)
      match (vote1_opt) {
        | None => true
        | Some(vr) => {
          // Check that there exists a quorum that shows v is safe at view vr.view
          // using phase 4 for phaseA and phase 1 for phaseB
          exists_safe_quorum(s.system, vr.value, vr.view, Phase4, Phase1)
        }
      }
    })
  }

  // Type invariant: ensure all state fields are within valid ranges
  pure def type_ok_inv(s: GlobalContext): bool = {
    NODES.forall(p => {
      val state = s.system.get(p)
      and {
        state.current_view >= 0,
        state.current_view <= MAX_VIEWS,
        // All votes have valid views
        get_all_votes(state).forall(vt =>
          vt.view >= 0 and vt.view <= MAX_VIEWS
        )
      }
    })
  }

  // Combined consistency invariant (like TLA+ spec)
  pure def consistency_invariant_inv(s: GlobalContext): bool = and {
    type_ok_inv(s),
    no_future_vote_inv(s),
    one_value_per_phase_per_view_inv(s),
    vote_has_quorum_in_previous_phase_inv(s)
  }

  // Invariant vals for easy use

  val s = choreo::s
  val agreement = agreement_inv(s)
  val validity = validity_inv(s)
  val no_future_vote = no_future_vote_inv(s)
  val one_value_per_phase_per_view = one_value_per_phase_per_view_inv(s)
  val vote_has_quorum_in_previous_phase = vote_has_quorum_in_previous_phase_inv(s)
  val votes_safe = votes_safe_inv(s)
  val type_ok = type_ok_inv(s)
  val consistency_invariant = consistency_invariant_inv(s)
}
