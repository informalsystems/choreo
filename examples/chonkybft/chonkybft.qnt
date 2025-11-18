// -*- mode: Bluespec; -*-

/**
 * ZKSync Chonky BFT Protocol - Choreo Implementation
 *
 * This is a Choreo-based rewrite of the ZKSync Chonky BFT consensus protocol.
 * Original spec: advanced/zk-sync-chonky-bft/replica.qnt
 *
 * Key differences from original:
 * - Uses Choreo framework for message-passing and state management
 * - Separates local state (per-process) from global extensions
 * - Uses listener pattern for protocol transitions
 * - Byzantine behavior handled through custom effects
 */

module chonkybft {
  import types.* from "./types"
  import option.* from "./spells/option"
  import basicSpells.* from "./spells/basicSpells"
  import choreo(processes = REPLICAS) as choreo from "./choreo"

  // Helper from defs
  pure def max(x: int, y: int): int = {
    if (x > y) x else y
  }

  // =============================================================================
  // PROTOCOL CONFIGURATION
  // =============================================================================

  // Weights of all replicas
  const WEIGHTS: ReplicaId -> Weight
  // The keys of the replicas
  const REPLICA_KEYS: ReplicaId -> ReplicaKey
  // The number of all replicas
  const N: int
  // Byzantine replica number threshold
  const F: int
  // Identities of the correct replicas
  const CORRECT: Set[ReplicaId]
  // Identities of the faulty replicas
  const FAULTY: Set[ReplicaId]
  // All replicas
  pure val REPLICAS = CORRECT.union(FAULTY)

  // Check that threshold assumptions hold
  assume FIVE_F = (N >= 5 * F + 1 and F >= 0)
  assume REPLICA_SIZE = (N == REPLICAS.size() and F == FAULTY.size())

  // The sum of all validator weights
  pure val TOTAL_WEIGHT: Weight = WEIGHTS.keys().fold(0, (s, id) => s + WEIGHTS.get(id))
  // The maximum weight of faulty replicas
  pure val FAULTY_WEIGHT: Weight = (TOTAL_WEIGHT - 1) / 5
  // The weight threshold needed to form a quorum certificate
  pure val QUORUM_WEIGHT: Weight = TOTAL_WEIGHT - FAULTY_WEIGHT
  // The weight threshold needed to trigger a reproposal
  pure val SUBQUORUM_WEIGHT: Weight = TOTAL_WEIGHT - 3 * FAULTY_WEIGHT

  // Produce replica's signature
  pure def sig_of_id(id: ReplicaId): ReplicaKey = REPLICA_KEYS.get(id)

  // The set of all views
  const VIEWS: Set[ViewNumber]

  // The set of all blocks
  const VALID_BLOCKS: Set[Block]
  const INVALID_BLOCKS: Set[Block]
  pure val ALL_BLOCKS = VALID_BLOCKS.union(INVALID_BLOCKS)
  assume DISJOINT_BLOCKS = (VALID_BLOCKS.intersect(INVALID_BLOCKS) == Set())

  // =============================================================================
  // CHOREO TYPE DEFINITIONS
  // =============================================================================

  // Node identifier type for Choreo
  type Node = ReplicaId

  // Message types for the protocol
  type Message =
    | MsgSignedTimeoutVote(SignedTimeoutVote)
    | MsgSignedCommitVote(SignedCommitVote)
    | MsgNewView(NewView)
    | MsgProposal(Proposal)

  // Local state fields for each replica
  type StateFields = {
    // The current view number
    view: ViewNumber,
    // The phase of the replica
    phase: Phase,
    // The commit vote with the highest view that this replica has signed
    high_vote: Option[CommitVote],
    // The commit QC with the highest view that this replica has observed
    high_commit_qc: Option[CommitQC],
    // The timeout QC with the highest view that this replica has observed
    high_timeout_qc: Option[TimeoutQC],
    // A cache of not-yet-committed proposals
    cached_proposals: Set[(BlockNumber, BlockHash)],
    // A history of committed blocks
    committed_blocks: List[CommittedBlock],
  }

  // Custom effects for protocol-specific actions
  type CustomEffects =
    // Update the leader function
    | UpdateLeader(ViewNumber -> ReplicaKey)
    // Record a justification
    | RecordJustification({ id: ReplicaId, view: ViewNumber, just: Justification })
    // Update replica view (for timeout tracking)
    | UpdateReplicaView({ id: ReplicaId, view: ViewNumber })
    // Update proposer view
    | UpdateProposerView({ id: ReplicaId, view: ViewNumber })
    // Byzantine effects - inject arbitrary messages
    | ByzantineCommitVote(Set[SignedCommitVote])
    | ByzantineTimeoutVote(Set[SignedTimeoutVote])
    | ByzantineNewView(Set[NewView])
    | ByzantineProposal(Set[Proposal])

  // Timeout events for modeling asynchronous timeouts
  type TimeoutEvent = { view: ViewNumber }
  type Event = TimeoutEvent

  // Global extensions - state not local to any process
  // NOTE: Removed store_signed_timeout and store_signed_commit
  // Quorums are now computed directly from messages (pure functional)
  type Extensions = {
    // The leader function from view to replica keys
    leader: ViewNumber -> ReplicaKey,
    // Ghost variables for tracking justifications
    ghost_justifications: (ReplicaId, ViewNumber) -> Justification,
    // Replica view tracking for timeouts
    replica_view: ReplicaId -> ViewNumber,
    // Proposer view tracking
    proposer_view: ReplicaId -> ViewNumber,
    // Last executed step (for debugging)
    ghost_step: StepKind,
  }

  // Choreo type aliases for readability
  type LocalState = choreo::LocalState[Node, StateFields]
  type LocalContext = choreo::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition = choreo::Transition[Node, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[Node, StateFields, Message, Event, Extensions]

  // =============================================================================
  // HELPER FUNCTIONS (from original spec)
  // =============================================================================

  // =============================================================================
  // QUORUM DETECTION ON MESSAGE SETS (Pure Functional)
  // =============================================================================

  // Extract all commit votes from message set
  pure def extract_commit_votes(messages: Set[Message]): Set[SignedCommitVote] = {
    messages.filterMap(m => match m {
      | MsgSignedCommitVote(v) => Some(v)
      | _ => None
    })
  }

  // Extract all timeout votes from message set
  pure def extract_timeout_votes(messages: Set[Message]): Set[SignedTimeoutVote] = {
    messages.filterMap(m => match m {
      | MsgSignedTimeoutVote(v) => Some(v)
      | _ => None
    })
  }

  // Get all CommitQCs that have quorum from message set
  // Groups votes by (view, block_hash, block_number), returns QCs for groups with >= QUORUM_WEIGHT
  pure def extract_commit_qcs(messages: Set[Message]): Set[CommitQC] = {
    val votes = extract_commit_votes(messages)
    // Group votes by their key (view, block_hash, block_number)
    val vote_keys = votes.map(sv => (sv.vote.view, sv.vote.block_hash, sv.vote.block_number))
    vote_keys.filterMap(key => {
      val similar_votes = votes.filter(sv =>
        sv.vote.view == key._1 and
        sv.vote.block_hash == key._2 and
        sv.vote.block_number == key._3
      )
      if (similar_votes.size() >= QUORUM_WEIGHT) {
        Some({
          vote: {
            view: key._1,
            block_number: key._3,
            block_hash: key._2,
          },
          agg_sig: similar_votes.map(sv => sv.sig),
        })
      } else {
        None
      }
    })
  }

  // Get all TimeoutQCs that have quorum from message set
  // Groups votes by view, returns QCs for views with >= QUORUM_WEIGHT votes
  pure def extract_timeout_qcs(messages: Set[Message]): Set[TimeoutQC] = {
    val votes = extract_timeout_votes(messages)
    // Group votes by view
    val views = votes.map(sv => sv.vote.view)
    views.filterMap(view => {
      val view_votes = votes.filter(sv => sv.vote.view == view)
      if (view_votes.size() >= QUORUM_WEIGHT) {
        // Build the QC
        val high_commit_qc: Option[CommitQC] = view_votes.fold(HIGH_COMMIT_QC_NONE,
          (prev_max_qc, sv) => max_commit_qc(prev_max_qc, sv.high_commit_qc))
        val qc_votes: ReplicaKey -> TimeoutVote =
          view_votes.map(v => (v.sig, v.vote)).setToMap()
        Some({
          votes: qc_votes,
          agg_sig: view_votes.map(v => v.sig),
          high_commit_qc: high_commit_qc,
          ghost_view: view,
        })
      } else {
        None
      }
    })
  }

  // Block verification
  def block_verify(block: Option[Block], implied_block_number: BlockNumber): bool = {
    match (block) {
      | Some(blk) => and {
          VALID_BLOCKS.contains(blk),
          implied_block_number >= 0,
        }
      | None => false
    }
  }

  // Process a commit QC
  def process_commit_qc(self: LocalState, qc_opt: Option[CommitQC]): LocalState = {
    match (qc_opt) {
      | None => self
      | Some(qc) =>
        if (self.cached_proposals.contains((qc.vote.block_number, qc.vote.block_hash))
            and self.committed_blocks.length() == qc.vote.block_number) {
          val block = qc.vote.block_hash
          {
            ...self,
            committed_blocks: self.committed_blocks.append({ block: block, commit_qc: qc }),
            high_commit_qc: max_commit_qc(Some(qc), self.high_commit_qc)
          }
        } else {
          {
            ...self,
            high_commit_qc: max_commit_qc(Some(qc), self.high_commit_qc)
          }
        }
    }
  }

  // Given two timeout QCs, return the one with the largest view
  def max_timeout_qc(qc1_opt: Option[TimeoutQC], qc2_opt: Option[TimeoutQC]): Option[TimeoutQC] = {
    match (qc2_opt) {
      | None => qc1_opt
      | Some(qc2) =>
        match (qc1_opt) {
          | None => qc2_opt
          | Some(qc1) =>
            if (qc1.ghost_view >= qc2.ghost_view) qc1_opt else qc2_opt
        }
    }
  }

  // Given two commit QCs, return the one with the largest view
  def max_commit_qc(qc1_opt: Option[CommitQC], qc2_opt: Option[CommitQC]): Option[CommitQC] = {
    match (qc2_opt) {
      | None => qc1_opt
      | Some(qc2) =>
        match(qc1_opt) {
          | None => qc2_opt
          | Some(qc1) =>
            if (qc1.vote.view >= qc2.vote.view) qc1_opt else qc2_opt
        }
    }
  }

  // Get timeout QC from votes if there's a quorum
  def get_timeout_qc(votes: Set[SignedTimeoutVote], view: ViewNumber): Option[TimeoutQC] = {
    val view_signed_votes = votes.filter(v => v.vote.view == view)
    if (view_signed_votes.size() < QUORUM_WEIGHT) {
      None
    } else {
      val high_commit_qc: Option[CommitQC] = view_signed_votes.fold(HIGH_COMMIT_QC_NONE,
        (prev_max_qc, sv) => max_commit_qc(prev_max_qc, sv.high_commit_qc))
      val qc_votes: ReplicaKey -> TimeoutVote =
        view_signed_votes.map(v => (v.sig, v.vote)).setToMap()
      Some({
        votes: qc_votes,
        agg_sig: view_signed_votes.map(v => v.sig),
        high_commit_qc: high_commit_qc,
        ghost_view: view,
      })
    }
  }

  // Get commit QC from votes if there's a quorum
  def get_commit_qc(votes: Set[SignedCommitVote], last_signed_vote: SignedCommitVote): Option[CommitQC] = {
    pure val similar_votes: Set[SignedCommitVote] =
      votes.filter(v => and {
        v.vote.view == last_signed_vote.vote.view,
        v.vote.block_hash == last_signed_vote.vote.block_hash,
        v.vote.block_number == last_signed_vote.vote.block_number,
      })
    pure val votes_count = similar_votes.size()
    if (votes_count < QUORUM_WEIGHT) {
      None
    } else {
      Some({
        vote: last_signed_vote.vote,
        agg_sig: similar_votes.map(v => v.sig),
      })
    }
  }

  // Get the view of a justification
  pure def view(justification: Justification): ViewNumber = {
    match (justification) {
      | Commit(qc) => qc.vote.view + 1
      | Timeout(qc) => qc.ghost_view + 1
    }
  }

  // Get the implied block from a justification
  pure def get_implied_block(justification: Justification): (BlockNumber, Option[BlockHash]) = {
    match (justification) {
      | Commit(qc) => {
        (qc.vote.block_number + 1, None)
      }
      | Timeout(qc) => {
        pure val qc_high_vote: Option[CommitVote] = qc.high_vote()
        match (qc_high_vote) {
          | Some(hv) =>
            match (qc.high_commit_qc) {
              | Some(hqc) =>
                if (hv.block_number > hqc.vote.block_number) {
                  (hv.block_number, Some(hv.block_hash))
                } else {
                  (hqc.vote.block_number + 1, None)
                }
              | None =>
                (hv.block_number, Some(hv.block_hash))
            }
          | None =>
            match (qc.high_commit_qc) {
              | Some(hqc) => (hqc.vote.block_number + 1, None)
              | None => (0, None)
            }
        }
      }
    }
  }

  // Get the high vote of a timeout QC
  pure def high_vote(qc: TimeoutQC): Option[CommitVote] = {
    pure val high_votes = qc.votes.keys().map(pk => qc.votes.get(pk).high_vote)
    pure val high_votes_sizes =
      high_votes.map(hv => (hv, qc.votes.keys().filter(pk => qc.votes.get(pk).high_vote == hv).size()))
    val subquorums = high_votes_sizes.fold([], (hv_list, hvs) => {
      if (hvs._2 >= SUBQUORUM_WEIGHT) {
        hv_list.append(hvs._1)
      } else {
        hv_list
      }
    })
    if (subquorums.length() == 1) {
      subquorums[0]
    } else {
      None
    }
  }

  // Create a justification from local state
  def create_justification(self: LocalState, ext: Extensions): Justification = {
    pure val init_timeout_qc: TimeoutQC = {
      votes: REPLICAS.map(id => sig_of_id(id)).mapBy(_ => {
        view: 0,
        high_vote: COMMIT_VOTE_NONE,
        high_commit_qc_view: VIEW_NUMBER_NONE
      }),
      agg_sig: REPLICAS.map(id => sig_of_id(id)),
      high_commit_qc: HIGH_COMMIT_QC_NONE,
      ghost_view: 0,
    }
    val timeout_qc =
      match (self.high_timeout_qc) {
        | None => init_timeout_qc
        | Some(qc) => qc
      }
    match (self.high_commit_qc) {
      | None =>
        Timeout(timeout_qc)
      | Some(commit_qc) =>
        if (commit_qc.vote.view >= timeout_qc.ghost_view) {
          Commit(commit_qc)
        } else {
          Timeout(timeout_qc)
        }
    }
  }

  // Verification functions
  pure def aggregate_verify(agg_sig: AggregateSignature): bool = and {
    agg_sig.size() >= QUORUM_WEIGHT,
    agg_sig.subseteq(REPLICAS.map(id => sig_of_id(id))),
  }

  pure def commit_vote_verify(vote: CommitVote): bool = all {
    vote.view >= 0,
    vote.block_number >= 0,
  }

  pure def timeout_vote_verify(vote: TimeoutVote): bool = all {
    vote.view >= 0,
    match vote.high_vote {
      | None => true
      | Some(high_vote) => and {
          commit_vote_verify(high_vote),
          vote.view >= high_vote.view,
          match vote.high_commit_qc_view {
            | None => true
            | Some(v) => high_vote.view >= v
          }
        }
    }
  }

  pure def commit_qc_verify(qc: CommitQC): bool = and {
    commit_vote_verify(qc.vote),
    qc.agg_sig.aggregate_verify()
  }

  pure def timeout_qc_verify(qc: TimeoutQC): bool = {
    val votes = qc.votes.keys().map(pk => qc.votes.get(pk))
    and {
      votes.forall(v => timeout_vote_verify(v)),
      votes.forall(v => v.view == qc.ghost_view),
      qc.agg_sig.aggregate_verify(),
      qc.votes.keys() == qc.agg_sig,
      val high_qc_view: Option[ViewNumber] =
        votes.fold(VIEW_NUMBER_NONE, (prev_max_opt, v) => match (prev_max_opt) {
          | None =>
            v.high_commit_qc_view
          | Some(prev_max) =>
            if (v.high_commit_qc_view.option_has(qcv => qcv > prev_max)) {
              v.high_commit_qc_view
            } else {
              prev_max_opt
            }
        })
      match (qc.high_commit_qc) {
        | None =>
          high_qc_view.is_none()
        | Some (high_qc) => and {
          high_qc_view == Some(high_qc.vote.view),
          commit_qc_verify(high_qc),
        }
      }
    }
  }

  def justification_verify(justification: Justification): bool = {
    match (justification) {
      | Timeout(qc) =>
        qc.timeout_qc_verify()
      | Commit(qc) =>
        qc.commit_qc_verify()
    }
  }

  pure def signed_commit_vote_verify(signed_vote: SignedCommitVote): bool = all {
    commit_vote_verify(signed_vote.vote),
    REPLICAS.exists(id => sig_of_id(id) == signed_vote.sig),
  }

  pure def signed_timeout_vote_verify(signed_vote: SignedTimeoutVote): bool = all {
    signed_vote.vote.view >= 0,
    match (signed_vote.high_commit_qc) {
      | None =>
        signed_vote.vote.high_commit_qc_view.is_none()
      | Some(qc) => and {
          Some(qc.vote.view) == signed_vote.vote.high_commit_qc_view,
          commit_qc_verify(qc),
        }
    },
    timeout_vote_verify(signed_vote.vote)
  }

  def proposal_verify(p: Proposal): bool = all {
    p.justification.justification_verify(),
  }

  pure def new_view_verify(new_view: NewView): bool = all {
    new_view.justification.justification_verify()
  }

  // NOTE: Removed is_new_signed_commit_vote_for_replica and is_new_signed_timeout_vote_for_replica
  // These functions are no longer needed - quorum detection is now pure functional on message set
  // No per-replica vote storage, no duplicate checking required

  // =============================================================================
  // LISTENER FUNCTIONS (Protocol transitions)
  // =============================================================================

  // Listen for proposals
  pure def listen_proposal(ctx: LocalContext): Set[Proposal] = {
    ctx.messages.filterMap(m => match m {
      | MsgProposal(p) => Some(p)
      | _ => None
    })
  }

  // Upon receiving a proposal
  def upon_proposal(ctx: LocalContext, proposal: Proposal): Transition = {
    val self = ctx.state
    val ext = ctx.extensions
    val proposal_view = proposal.justification.view()

    // Guard conditions
    val can_process = and {
      or {
        proposal_view == self.view and self.phase == PhasePrepare,
        proposal_view > self.view
      },
      VIEWS.contains(proposal_view),
      proposal.sig == ext.leader.get(proposal_view),
      proposal.proposal_verify(),
    }

    if (not(can_process)) {
      // Return no-op transition
      {
        effects: Set(),
        post_state: self
      }
    } else {
      val block_number_and_opt_block_hash = proposal.justification.get_implied_block()
      val block_number = block_number_and_opt_block_hash._1
      val opt_block_hash = block_number_and_opt_block_hash._2

      val block_hash: BlockHash = match(opt_block_hash) {
        | Some(hash) => hash
        | None => unwrap_or(proposal.block, "").hash()
      }

      val vote: CommitVote = {
        view: proposal_view,
        block_number: block_number,
        block_hash: block_hash,
      }

      val can_vote = and {
        block_number == length(self.committed_blocks),
        if (is_some(opt_block_hash)) {
          is_none(proposal.block)
        } else {
          all {
            is_some(proposal.block),
            proposal.block.block_verify(block_number),
            proposal.ghost_block_number == block_number,
          }
        },
      }

      if (not(can_vote)) {
        {
          effects: Set(),
          post_state: self
        }
      } else {
        val self1 = {
          ...self,
          view: proposal_view,
          phase: PhaseCommit,
          high_vote: Some(vote),
          cached_proposals:
            if (is_none(proposal.block)) {
              self.cached_proposals
            } else {
              self.cached_proposals.union(Set((block_number, block_hash)))
            }
        }
        val self2 =
          match (proposal.justification) {
            | Commit(qc) => self1.process_commit_qc(Some(qc))
            | Timeout(qc) => {
                ...self1.process_commit_qc(qc.high_commit_qc),
                high_timeout_qc: max_timeout_qc(Some(qc), self1.high_timeout_qc)
              }
          }

        {
          effects: Set(
            choreo::Broadcast(MsgSignedCommitVote({ vote: vote, sig: sig_of_id(self.process_id) })),
            choreo::CustomEffect(RecordJustification({
              id: self.process_id,
              view: proposal.justification.view(),
              just: proposal.justification
            })),
            choreo::TriggerEvent({ view: proposal_view })
          ),
          post_state: self2
        }
      }
    }
  }

  // Listen for commit QCs (quorum-based: triggers when quorum exists)
  // Returns CommitQCs formed from message set where QC view >= current view
  pure def listen_commit_qc(ctx: LocalContext): Set[CommitQC] = {
    val self = ctx.state
    val qcs = extract_commit_qcs(ctx.messages)
    // Only return QCs for views >= current view
    qcs.filter(qc => qc.vote.view >= self.view)
  }

  // Upon observing a commit QC (quorum already formed)
  def upon_commit_qc(ctx: LocalContext, qc: CommitQC): Transition = {
    val self = ctx.state
    val ext = ctx.extensions
    val id = self.process_id

    // Guard: QC must be valid and for current or future view
    val can_process = and {
      qc.vote.view >= self.view,
      qc.commit_qc_verify(),
    }

    if (not(can_process)) {
      {
        effects: Set(),
        post_state: self
      }
    } else {
      // Process the QC - no need to accumulate votes or check quorum!
      val self1 = self.process_commit_qc(Some(qc))
      val new_view = qc.vote.view + 1

      if (not(VIEWS.contains(new_view))) {
        {
          effects: Set(),
          post_state: self1
        }
      } else {
        val self2 = { ...self1, view: new_view, phase: PhasePrepare }
        val justification = self2.create_justification(ext)

        {
          effects: Set(
            choreo::Broadcast(MsgNewView({
              justification: justification,
              sig: sig_of_id(id)
            })),
            choreo::CustomEffect(RecordJustification({
              id: id,
              view: new_view,
              just: justification
            })),
            choreo::TriggerEvent({ view: new_view })
          ),
          post_state: self2
        }
      }
    }
  }

  // Listen for timeout events
  pure def listen_timer_finished(ctx: LocalContext): Set[TimeoutEvent] = {
    val self = ctx.state
    ctx.events.filter(e => and {
      e.view == self.view,
      self.phase != PhaseTimeout
    })
  }

  // Upon timer finishing
  def upon_timer_finished(ctx: LocalContext, event: TimeoutEvent): Transition = {
    val self = ctx.state
    val ext = ctx.extensions
    val id = self.process_id

    val vote: SignedTimeoutVote = {
      vote: {
        view: self.view,
        high_vote: self.high_vote,
        high_commit_qc_view:
          match (self.high_commit_qc) {
            | None => VIEW_NUMBER_NONE
            | Some(qc) => Some(qc.vote.view)
          }
      },
      sig: sig_of_id(id),
      high_commit_qc: self.high_commit_qc,
    }

    {
      effects: Set(
        choreo::Broadcast(MsgSignedTimeoutVote(vote))
      ),
      post_state: { ...self, phase: PhaseTimeout }
    }
  }

  // Listen for timeout QCs (quorum-based: triggers when quorum exists)
  // Returns TimeoutQCs formed from message set where QC view >= current view
  pure def listen_timeout_qc(ctx: LocalContext): Set[TimeoutQC] = {
    val self = ctx.state
    val qcs = extract_timeout_qcs(ctx.messages)
    // Only return QCs for views >= current view
    qcs.filter(qc => qc.ghost_view >= self.view)
  }

  // Upon observing a timeout QC (quorum already formed)
  def upon_timeout_qc(ctx: LocalContext, qc: TimeoutQC): Transition = {
    val self = ctx.state
    val ext = ctx.extensions
    val id = self.process_id

    // Guard: QC must be valid and for current or future view
    val can_process = and {
      qc.ghost_view >= self.view,
      qc.timeout_qc_verify(),
    }

    if (not(can_process)) {
      {
        effects: Set(),
        post_state: self
      }
    } else {
      // Process the QC - no need to accumulate votes or check quorum!
      val self1 = {
        ...self.process_commit_qc(qc.high_commit_qc),
        high_timeout_qc: max_timeout_qc(Some(qc), self.high_timeout_qc)
      }
      val new_view = qc.ghost_view + 1

      if (not(VIEWS.contains(new_view))) {
        {
          effects: Set(),
          post_state: self1
        }
      } else {
        val self2 = { ...self1, view: new_view, phase: PhasePrepare }
        val justification = self2.create_justification(ext)

        {
          effects: Set(
            choreo::Broadcast(MsgNewView({
              justification: justification,
              sig: sig_of_id(id)
            })),
            choreo::CustomEffect(RecordJustification({
              id: id,
              view: new_view,
              just: justification
            })),
            choreo::TriggerEvent({ view: new_view })
          ),
          post_state: self2
        }
      }
    }
  }

  // Listen for new view messages
  pure def listen_new_view(ctx: LocalContext): Set[NewView] = {
    ctx.messages.filterMap(m => match m {
      | MsgNewView(nv) => Some(nv)
      | _ => None
    })
  }

  // Upon receiving a new view message
  def upon_new_view(ctx: LocalContext, new_view: NewView): Transition = {
    val self = ctx.state
    val ext = ctx.extensions
    val id = self.process_id
    val new_view_view = new_view.justification.view()

    val can_process = and {
      new_view_view >= self.view,
      new_view.new_view_verify(),
    }

    if (not(can_process)) {
      {
        effects: Set(),
        post_state: self
      }
    } else {
      val self1 =
        match (new_view.justification) {
          | Commit(qc) => self.process_commit_qc(Some(qc))
          | Timeout(qc) => {
              ...self.process_commit_qc(qc.high_commit_qc),
              high_timeout_qc: max_timeout_qc(Some(qc), self.high_timeout_qc)
            }
        }

      if (new_view_view > self.view) {
        if (not(VIEWS.contains(new_view_view))) {
          {
            effects: Set(),
            post_state: self1
          }
        } else {
          val self2 = { ...self1, view: new_view_view, phase: PhasePrepare }
          val justification = self2.create_justification(ext)

          {
            effects: Set(
              choreo::Broadcast(MsgNewView({
                justification: justification,
                sig: sig_of_id(id)
              })),
              choreo::CustomEffect(RecordJustification({
                id: id,
                view: new_view_view,
                just: justification
              })),
              choreo::TriggerEvent({ view: new_view_view })
            ),
            post_state: self2
          }
        }
      } else {
        {
          effects: Set(),
          post_state: self
        }
      }
    }
  }

  // Listen for proposer opportunity
  pure def listen_proposer(ctx: LocalContext): Set[Block] = {
    val self = ctx.state
    val ext = ctx.extensions
    val id = self.process_id
    val replica_state_view = self.view
    val proposer_state_view = ext.proposer_view.get(id)

    if (and {
      CORRECT.contains(id),
      proposer_state_view < replica_state_view,
      sig_of_id(id) == ext.leader.get(replica_state_view),
    }) {
      VALID_BLOCKS
    } else {
      Set()
    }
  }

  // Upon proposing
  def upon_proposer(ctx: LocalContext, new_block: Block): Transition = {
    val self = ctx.state
    val ext = ctx.extensions
    val id = self.process_id
    val replica_state_view = self.view

    val justification = self.create_justification(ext)
    val block_and_hash = justification.get_implied_block()
    val block_number = block_and_hash._1
    val opt_block_hash = block_and_hash._2

    val block =
      match (opt_block_hash) {
        | Some(h) => None
        | None => Some(new_block)
      }

    val proposal: Proposal = {
      block: block,
      justification: justification,
      sig: sig_of_id(id),
      ghost_block_number: block_number,
    }

    val can_propose = and {
      justification.view() == replica_state_view,
      block_number == length(self.committed_blocks),
      or {
        is_none(block),
        block_number == 0,
        self.cached_proposals.exists(((bn, bh)) => {
          block_number == bn + 1
        }),
      },
    }

    if (can_propose) {
      {
        effects: Set(
          choreo::Broadcast(MsgProposal(proposal)),
          choreo::CustomEffect(UpdateProposerView({ id: id, view: replica_state_view }))
        ),
        post_state: self
      }
    } else {
      {
        effects: Set(),
        post_state: self
      }
    }
  }

  // Main listener - combines all protocol transitions
  // NOTE: Uses quorum-based listeners (listen_commit_qc, listen_timeout_qc)
  pure def main_listener(ctx: LocalContext): Set[Transition] = {
    Set(
      choreo::cue(ctx, listen_proposal, upon_proposal),
      choreo::cue(ctx, listen_commit_qc, upon_commit_qc),       // Quorum-based
      choreo::cue(ctx, listen_timer_finished, upon_timer_finished),
      choreo::cue(ctx, listen_timeout_qc, upon_timeout_qc),     // Quorum-based
      choreo::cue(ctx, listen_new_view, upon_new_view),
      choreo::cue(ctx, listen_proposer, upon_proposer),
    ).flatten()
  }

  // =============================================================================
  // CUSTOM EFFECT PROCESSOR
  // =============================================================================

  pure def apply_custom_effect(env: GlobalContext, effect: CustomEffects): GlobalContext = {
    match effect {
      | UpdateLeader(ldr) => {
          ...env,
          extensions: { ...env.extensions, leader: ldr }
        }
      | RecordJustification(r) => {
          ...env,
          extensions: {
            ...env.extensions,
            ghost_justifications: env.extensions.ghost_justifications.put((r.id, r.view), r.just)
          }
        }
      | UpdateReplicaView(r) => {
          ...env,
          extensions: {
            ...env.extensions,
            replica_view: env.extensions.replica_view.set(r.id, r.view)
          }
        }
      | UpdateProposerView(r) => {
          ...env,
          extensions: {
            ...env.extensions,
            proposer_view: env.extensions.proposer_view.set(r.id, r.view)
          }
        }
      | ByzantineCommitVote(votes) => {
          ...env,
          messages: env.messages.transformValues(msgs =>
            msgs.union(votes.map(v => MsgSignedCommitVote(v)))
          )
        }
      | ByzantineTimeoutVote(votes) => {
          ...env,
          messages: env.messages.transformValues(msgs =>
            msgs.union(votes.map(v => MsgSignedTimeoutVote(v)))
          )
        }
      | ByzantineNewView(nvs) => {
          ...env,
          messages: env.messages.transformValues(msgs =>
            msgs.union(nvs.map(nv => MsgNewView(nv)))
          )
        }
      | ByzantineProposal(props) => {
          ...env,
          messages: env.messages.transformValues(msgs =>
            msgs.union(props.map(p => MsgProposal(p)))
          )
        }
    }
  }

  // =============================================================================
  // INITIALIZATION
  // =============================================================================

  pure def initialize(id: ReplicaId): LocalState = {
    {
      process_id: id,
      view: 1,
      phase: PhasePrepare,
      high_vote: COMMIT_VOTE_NONE,
      high_commit_qc: HIGH_COMMIT_QC_NONE,
      high_timeout_qc: HIGH_TIMEOUT_QC_NONE,
      cached_proposals: Set(),
      committed_blocks: [],
    }
  }

  action init = {
    nondet ldr = VIEWS.setOfMaps(REPLICAS.map(id => sig_of_id(id))).oneOf()

    // Initialize with view 1 (bootstrapped state)
    pure val init_timeout_qc: TimeoutQC = {
      votes: REPLICAS.map(id => sig_of_id(id)).mapBy(_ => {
        view: 0,
        high_vote: COMMIT_VOTE_NONE,
        high_commit_qc_view: VIEW_NUMBER_NONE
      }),
      agg_sig: REPLICAS.map(id => sig_of_id(id)),
      high_commit_qc: HIGH_COMMIT_QC_NONE,
      ghost_view: 0,
    }

    // NOTE: Removed timeout_votes0 initialization - no longer needed
    // Quorum detection is now pure functional on message set

    choreo::init({
      system: REPLICAS.mapBy(id => initialize(id)),
      messages: REPLICAS.mapBy(id =>
        Set(MsgNewView({
          sig: sig_of_id(id),
          justification: Timeout(init_timeout_qc)
        }))
      ),
      events: REPLICAS.mapBy(id => Set({ view: 1 })),
      extensions: {
        leader: ldr,
        // NOTE: Removed store_signed_timeout and store_signed_commit
        // Quorum detection is now pure functional on message set
        ghost_justifications:
          tuples(CORRECT, Set(1)).mapBy(((id, view)) => Timeout(init_timeout_qc)),
        replica_view: REPLICAS.mapBy(id => 0),
        proposer_view: REPLICAS.mapBy(id => 0),
        ghost_step: InitStep,
      }
    })
  }

  // =============================================================================
  // STEP FUNCTION
  // =============================================================================

  action step = choreo::step(
    main_listener,
    apply_custom_effect
  )

  action step_with(id: ReplicaId, listener: (LocalContext) => Set[Transition]): bool = {
    choreo::step_with(id, listener, apply_custom_effect)
  }

  // =============================================================================
  // INVARIANTS
  // =============================================================================

  // No two correct replicas disagree on the committed blocks
  pure def agreement_inv: bool = tuples(CORRECT, CORRECT).forall(((id1, id2)) => {
    val blocks1 = choreo::s.system.get(id1).committed_blocks
    val blocks2 = choreo::s.system.get(id2).committed_blocks
    or {
      blocks1.length() > blocks2.length(),
      blocks1.indices().forall(i => blocks1[i].block == blocks2[i].block)
    }
  })

  // Check that all replicas have consistent state
  pure def consistency_inv: bool = CORRECT.forall(id => {
    val state = choreo::s.system.get(id)
    and {
      state.view >= 0,
      match state.high_vote {
        | None => true
        | Some(v) => v.view <= state.view
      },
      match state.high_commit_qc {
        | None => true
        | Some(qc) => qc.vote.view < state.view
      }
    }
  })

  // =============================================================================
  // TESTING
  // =============================================================================

  run simpleTest = init.then(step).then(step).then(step)

  // Test that agreement holds
  run agreementTest = init
    .then(10.reps(_ => step))
    .expect(agreement_inv)
}
