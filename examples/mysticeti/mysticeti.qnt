// -*- mode: Bluespec; -*-

/**
 * Mysticeti DAG BFT Consensus - Choreo Framework Implementation
 *
 * Adapted from advanced/mysticeti-dag-bft for Choreo message-passing framework
 *
 * Original spec: dag_evolution.qnt + mysticeti_c.qnt
 * This version: Unified Choreo-based implementation
 *
 * Yassine & Claude Code, 2025
 */
module mysticeti {
  import basicSpells.* from "./spells/basicSpells"
  import option.* from "./spells/option"
  import types.* from "./types"
  import list_utils.* from "./list_utils"

  // ==========================================================================
  // Constants (Module Parameters)
  // ==========================================================================

  const N: int                              // Total number of nodes
  const F: int                              // Number of Byzantine nodes
  const CORRECT: Set[NodeId]                 // Correct node IDs
  const FAULTY: Set[NodeId]                  // Faulty node IDs
  const INITIAL_GST_ROUND: int              // Round at which GST is reached
  const MAX_ROUNDS: int                       // Maximum rounds for bounded model checking

  // ==========================================================================
  // Derived Values
  // ==========================================================================

  pure val NODES: Set[NodeId] = CORRECT.union(FAULTY)
  pure val QUORUM_SIZE: int = 2 * F + 1

  assume n_correct = NODES.size() == N
  assume f_bound = F >= 0 and F < N
  assume disjoint = CORRECT.intersect(FAULTY) == Set()
  assume gst_positive = INITIAL_GST_ROUND > 0

  // Import choreo with qualified names to avoid conflicts
  import choreo(processes = NODES) as choreo from "./choreo"

  // ==========================================================================
  // Choreo Message Types
  // ==========================================================================

  type Message = MsgBlock(StatementBlock)

  type Event = ()  // No events needed for Mysticeti

  // ==========================================================================
  // Choreo State Types
  // ==========================================================================

  type StateFields = {
    authority: Authority,                // This node's authority index
    dag: DAG,                             // Local DAG
    backlog: Set[StatementBlock],         // Blocks waiting for parents
    current_round: Round,                 // Current round number
    committed_sequence: List[BlockReference], // Committed block sequence
  }

  // ==========================================================================
  // Extensions (Global State)
  // ==========================================================================

  type LeaderRanking = Authority -> LeaderRank

  type Extensions = {
    leader_ranks: List[LeaderRanking],    // Leader ranking for each round
    GST_round: Round,                      // Global Stabilization Time round
    ghost_step: StepKind,                  // For verification
  }

  type StepKind =
    | StepReceiveBlock
    | StepConsumeBacklog
    | StepProposeBlock
    | StepByzantine

  // ==========================================================================
  // Custom Effects
  // ==========================================================================

  type CustomEffects =
    | ElectLeaders({ round: Round, ranking: LeaderRanking })
    | RecordCommit({ id: NodeId, sequence: List[BlockReference] })
    | ByzantineBlock(Set[StatementBlock])

  // ==========================================================================
  // Choreo Type Aliases
  // ==========================================================================

  type LocalState = choreo::LocalState[NodeId, StateFields]
  type LocalContext = choreo::LocalContext[NodeId, StateFields, Message, Event, Extensions]
  type Transition = choreo::Transition[NodeId, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[NodeId, StateFields, Message, Event, Extensions]

  // ==========================================================================
  // Consensus Algorithm (Pure Functions from mysticeti_c.qnt)
  // ==========================================================================

  /**
   * Direct decision rule: Check for skip or commit patterns
   * Skip: 2F+1 blocks in next round don't support proposal
   */
  pure def should_skip(dag: DAG, proposal: StatementBlock): bool = {
    val next_round_blocks = dag.blocks_at_round(proposal.reference.round + 1)
    val non_supporters = next_round_blocks.filter(block => {
      not(block.parents.exists(parent => parent == proposal.reference))
    })
    non_supporters.size() >= QUORUM_SIZE
  }

  /**
   * Check if a certificate block has 2F+1 parents supporting the proposer block
   */
  pure def is_certificate(
    dag: DAG,
    certificate_block: StatementBlock,
    proposer_block: StatementBlock
  ): bool = {
    val parents_supporting_proposer = certificate_block.parents.filter(ref => {
      dag.exists(parent_block => and {
        parent_block.reference == ref,
        parent_block.parents.contains(proposer_block.reference)
      })
    })
    parents_supporting_proposer.size() >= QUORUM_SIZE
  }

  /**
   * Check if anchor has certified link with proposer block
   */
  pure def has_certified_link(
    dag: DAG,
    anchor_block: StatementBlock,
    proposer_block: StatementBlock
  ): bool = {
    val potential_certified_links = dag.children_of(proposer_block)
      .map(b => dag.children_of(b))
      .flatten()

    potential_certified_links.exists(block => and {
      is_certificate(dag, block, proposer_block),
      dag.is_link(block, anchor_block)
    })
  }

  /**
   * Find all certificates for a proposer block
   */
  pure def find_certificates(dag: DAG, proposer_block: StatementBlock): Set[StatementBlock] = {
    val potential_certificates = dag.children_of(proposer_block)
      .map(b => dag.children_of(b))
      .flatten()

    potential_certificates.filter(c => is_certificate(dag, c, proposer_block))
  }

  /**
   * Try direct decision for a proposer block
   */
  pure def try_direct_decide(dag: DAG, proposer_block: StatementBlock): Decision = {
    val certificates = find_certificates(dag, proposer_block)

    val status = if (should_skip(dag, proposer_block)) {
      Skip
    } else if (certificates.size() >= QUORUM_SIZE) {
      Commit
    } else {
      Undecided
    }

    { status: status, block: proposer_block.reference }
  }

  /**
   * Try indirect decision using anchor-based rule
   */
  def try_indirect_decide(
    dag: DAG,
    sequence: List[Decision],
    proposer_block: StatementBlock
  ): Decision = {
    val anchor_round = proposer_block.reference.round + 3
    val filtered = sequence.select(s => s.block.round >= anchor_round)
    val sorted = sort_decisions(filtered, (a, b) => {
      if (a.block.round != b.block.round) {
        a.block.round < b.block.round
      } else {
        a.block.leader_rank < b.block.leader_rank
      }
    })
    val potential_anchors = sorted.select(decision => {
      decision.status == Undecided or decision.status == Commit
    })

    if (potential_anchors.length() == 0) {
      { status: Undecided, block: proposer_block.reference }
    } else {
      val anchor = potential_anchors.head()
      if (anchor.status == Undecided) {
        { status: Undecided, block: proposer_block.reference }
      } else {
        // Find the anchor block in the DAG
        val anchor_blocks = dag.filter(b => b.reference == anchor.block)
        if (anchor_blocks.size() == 0) {
          { status: Undecided, block: proposer_block.reference }
        } else {
          // Pick one anchor block (should have exactly one with matching reference)
          val anchor_block_list = anchor_blocks.fold(List(), (acc, b) => acc.append(b))
          val anchor_block = anchor_block_list[0]
          val status = if (has_certified_link(dag, anchor_block, proposer_block)) {
            Commit
          } else {
            Skip
          }
          { status: status, block: proposer_block.reference }
        }
      }
    }
  }

  /**
   * Try to decide one block
   */
  def try_decide_one(
    dag: DAG,
    sequence: List[Decision],
    proposer_block: StatementBlock
  ): List[Decision] = {
    if (proposer_block.reference.round > dag.highest_round() - 2) {
      // Incomplete wave, cannot decide
      List({ status: Undecided, block: proposer_block.reference }).concat(sequence)
    } else {
      val direct_decision = try_direct_decide(dag, proposer_block)
      val decision = if (direct_decision.status != Undecided) {
        direct_decision
      } else {
        try_indirect_decide(dag, sequence, proposer_block)
      }
      List(decision).concat(sequence)
    }
  }

  /**
   * Compute committed sequence from decisions
   */
  pure def commit_order(decisions: List[Decision]): List[BlockReference] = {
    val until_undecided = take_while(decisions, decision => decision.status != Undecided)
    val commits = until_undecided.select(decision => decision.status == Commit)
    range(0, commits.length()).foldl(List(), (acc, i) => acc.append(commits[i].block))
  }

  /**
   * Iterate through all blocks in DAG and compute decisions
   * Processes from highest round to lowest, by leader rank
   */
  def try_decide_all(dag: DAG): List[Decision] = {
    val highest = dag.highest_round()

    // Process rounds from highest down to 0
    range(0, highest + 1).foldl(List(), (sequence, r_idx) => {
      val round = highest - r_idx  // Count backwards

      // Process leader ranks from N-1 down to 0
      range(0, N).foldl(sequence, (seq, lr_idx) => {
        val leader_rank = N - 1 - lr_idx  // Count backwards

        // Find block with this round and leader_rank
        val matching_blocks = dag.filter(b => and {
          b.reference.round == round,
          b.reference.leader_rank == leader_rank
        })

        // Convert to list and take first element
        val block_list = matching_blocks.fold(List(), (acc, b) => acc.append(b))
        if (block_list.length() > 0) {
          try_decide_one(dag, seq, block_list[0])
        } else {
          seq
        }
      })
    })
  }

  // ==========================================================================
  // Helper Functions
  // ==========================================================================


  /**
   * Check if GST has been reached
   */
  pure def gst_reached(ext: Extensions, round: Round): bool = {
    round >= ext.GST_round
  }

  /**
   * Check if node can progress to new round
   */
  pure def can_go_to_new_round(self: LocalState, ext: Extensions): bool = {
    // Compute correct authorities (0, 1, 2, ..., CORRECT.size()-1)
    val correct_authorities = range(0, CORRECT.size()).foldl(Set(), (acc, i) => acc.union(Set(i)))

    self.current_round == 0 or if (gst_reached(ext, self.current_round)) {
      self.dag.is_stabilized(self.current_round, correct_authorities)
    } else {
      // Before GST, wait for F+1 blocks (allows progress with partial quorum)
      self.dag.has_quorum_at_round(self.current_round, F)
    }
  }

  /**
   * Get leader rank for a round (or default to authority)
   */
  pure def get_leader_rank(ext: Extensions, round: Round, authority: Authority): LeaderRank = {
    if (round < ext.leader_ranks.length()) {
      ext.leader_ranks[round].get(authority)
    } else {
      authority  // Default: rank = authority
    }
  }

  /**
   * Try to add block to DAG or backlog
   */
  pure def receive_block_helper(self: LocalState, block: StatementBlock): LocalState = {
    if (self.dag.all_parents_present(block)) {
      { ...self, dag: self.dag.union(Set(block)) }
    } else {
      { ...self, backlog: self.backlog.union(Set(block)) }
    }
  }

  /**
   * Process backlog to add blocks whose parents are now present
   */
  pure def consume_backlog_helper(self: LocalState): LocalState = {
    val highest = self.dag.highest_round()

    val new_dag = range(0, highest + 1).foldl(self.dag, (updated_dag, r) => {
      val to_add = self.backlog.filter(b => and {
        b.reference.round == r,
        updated_dag.all_parents_present(b)
      })
      updated_dag.union(to_add)
    })

    { ...self, dag: new_dag, backlog: self.backlog.exclude(new_dag) }
  }

  // ==========================================================================
  // Listener 1: Receive Block Messages
  // ==========================================================================

  pure def listen_block(ctx: LocalContext): Set[StatementBlock] = {
    ctx.messages.fold(Set(), (blocks, msg) => {
      match msg {
        | MsgBlock(block) => blocks.union(Set(block))
      }
    })
  }

  def upon_block(ctx: LocalContext, block: StatementBlock): Transition = {
    val self = ctx.state
    val after_receive = receive_block_helper(self, block)

    // Recompute decisions after receiving block
    val decisions = try_decide_all(after_receive.dag)
    val new_committed = commit_order(decisions)

    val new_self = { ...after_receive, committed_sequence: new_committed }

    {
      effects: Set(),
      post_state: new_self
    }
  }

  // ==========================================================================
  // Listener 2: Consume Backlog
  // ==========================================================================

  pure def listen_consume_backlog(ctx: LocalContext): Set[bool] = {
    val self = ctx.state
    if (self.backlog.size() > 0) Set(true) else Set()
  }

  def upon_consume_backlog(ctx: LocalContext, _trigger: bool): Transition = {
    val self = ctx.state
    val after_backlog = consume_backlog_helper(self)

    // Recompute decisions after consuming backlog
    val decisions = try_decide_all(after_backlog.dag)
    val new_committed = commit_order(decisions)

    val new_self = { ...after_backlog, committed_sequence: new_committed }

    {
      effects: Set(),
      post_state: new_self
    }
  }

  // ==========================================================================
  // Listener 3: Propose New Block
  // ==========================================================================

  pure def listen_propose(ctx: LocalContext): Set[bool] = {
    val self = ctx.state
    val ext = ctx.extensions

    if (can_go_to_new_round(self, ext)) Set(true) else Set()
  }

  def upon_propose(ctx: LocalContext, _trigger: bool): Transition = {
    val self = ctx.state
    val ext = ctx.extensions
    val new_round = self.current_round + 1

    // Create new block
    val parents = self.dag.blocks_at_round(self.current_round).map(b => b.reference)
    val leader_rank = get_leader_rank(ext, new_round, self.authority)
    val label = ctx.state.process_id  // Simple label = node ID
    val new_block = {
      reference: {
        authority: self.authority,
        round: new_round,
        label: label,
        leader_rank: leader_rank
      },
      parents: parents
    }

    // Update DAG with new block
    val updated_dag = self.dag.union(Set(new_block))

    // Compute decisions and committed sequence
    val decisions = try_decide_all(updated_dag)
    val new_committed = commit_order(decisions)

    // Update local state with new round, DAG, and committed sequence
    val new_self = {
      ...self,
      current_round: new_round,
      dag: updated_dag,
      committed_sequence: new_committed
    }

    // Broadcast block and record commit
    val effects = if (CORRECT.contains(ctx.state.process_id)) {
      Set(
        choreo::Broadcast(MsgBlock(new_block)),
        choreo::CustomEffect(RecordCommit({ id: ctx.state.process_id, sequence: new_committed }))
      )
    } else {
      Set()
    }

    {
      effects: effects,
      post_state: new_self
    }
  }

  // ==========================================================================
  // Main Listener (combines all listeners)
  // ==========================================================================

  pure def main_listener(ctx: LocalContext): Set[Transition] = {
    Set(
      choreo::cue(ctx, listen_block, upon_block),
      choreo::cue(ctx, listen_consume_backlog, upon_consume_backlog),
      choreo::cue(ctx, listen_propose, upon_propose),
    ).flatten()
  }

  // ==========================================================================
  // Custom Effect Handler
  // ==========================================================================

  pure def apply_custom_effect(env: GlobalContext, effect: CustomEffects): GlobalContext = {
    match effect {
      | ElectLeaders(params) => {
        { ...env, extensions: { ...env.extensions, leader_ranks: env.extensions.leader_ranks.append(params.ranking) } }
      }
      | RecordCommit(params) => {
        // Just update ghost step (could track commits here)
        { ...env, extensions: { ...env.extensions, ghost_step: StepProposeBlock } }
      }
      | ByzantineBlock(blocks) => {
        // Byzantine behavior handled through custom injection
        { ...env, extensions: { ...env.extensions, ghost_step: StepByzantine } }
      }
    }
  }

  // ==========================================================================
  // Initialization
  // ==========================================================================

  /**
   * Initialize state for a single node
   */
  pure def initialize(id: NodeId): LocalState = {
    val authority_map = CORRECT.fold((Map(), 0), (acc, nid) => {
      (acc._1.put(nid, acc._2), acc._2 + 1)
    })._1
    {
      process_id: id,
      authority: if (CORRECT.contains(id)) authority_map.get(id) else N - 1,
      dag: Set(),
      backlog: Set(),
      current_round: 0,
      committed_sequence: List(),
    }
  }

  action init = choreo::init({
    system: NODES.mapBy(id => initialize(id)),
    messages: NODES.mapBy(id => Set()),
    events: NODES.mapBy(id => Set()),
    extensions: {
      leader_ranks: List(),
      GST_round: INITIAL_GST_ROUND,
      ghost_step: StepProposeBlock,
    }
  })

  // ==========================================================================
  // Step (Main Transition)
  // ==========================================================================

  action step = choreo::step(
    main_listener,
    apply_custom_effect
  )

  // ==========================================================================
  // Invariants
  // ==========================================================================

  /**
   * Total Order: All correct nodes commit consistent sequences
   * (one is prefix of another)
   */
  pure def total_order_inv: bool = {
    // Check all pairs of correct nodes for prefix property
    CORRECT.forall(id1 => {
      CORRECT.forall(id2 => {
        val seq1 = choreo::s.system.get(id1).committed_sequence
        val seq2 = choreo::s.system.get(id2).committed_sequence
        if (seq1.length() <= seq2.length()) {
          range(0, seq1.length()).foldl(true, (acc, i) => acc and seq1[i] == seq2[i])
        } else {
          range(0, seq2.length()).foldl(true, (acc, i) => acc and seq1[i] == seq2[i])
        }
      })
    })
  }

  /**
   * Safety: No two correct nodes commit conflicting blocks at same slot
   */
  pure def safety_inv: bool = {
    // Same as total_order_inv - sequences must be consistent (prefix property)
    CORRECT.forall(id1 => {
      CORRECT.forall(id2 => {
        val seq1 = choreo::s.system.get(id1).committed_sequence
        val seq2 = choreo::s.system.get(id2).committed_sequence
        val min_len = if (seq1.length() <= seq2.length()) seq1.length() else seq2.length()
        range(0, min_len).foldl(true, (acc, i) => acc and seq1[i] == seq2[i])
      })
    })
  }

  /**
   * Helper: Check if any correct node has committed blocks
   */
  pure def has_commits: bool = {
    CORRECT.exists(id => choreo::s.system.get(id).committed_sequence.length() > 0)
  }

  val has_commits_witness = not(has_commits)


}
