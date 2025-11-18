// -*- mode: Bluespec; -*-

/**
 * Types and basic functionality for the Mysticeti Choreo implementation
 * Adapted from mysticeti_types.qnt for Choreo framework
 *
 * Yassine & Claude Code, 2025
 */
module types {
  import basicSpells.* from "./spells/basicSpells"
  import option.* from "./spells/option"

  // ============================================================================
  // Core Types
  // ============================================================================

  type NodeId = str
  type Authority = int
  type Round = int
  type LeaderRank = int

  type BlockReference = {
    authority: Authority,
    round: Round,
    label: str,
    leader_rank: LeaderRank
  }

  type StatementBlock = {
    reference: BlockReference,
    parents: Set[BlockReference]
  }

  type DAG = Set[StatementBlock]

  // ============================================================================
  // Decision Types (from mysticeti_c.qnt)
  // ============================================================================

  type ProposerSlotStatus = Commit | Skip | Undecided

  type Decision = {
    status: ProposerSlotStatus,
    block: BlockReference,
  }

  // ============================================================================
  // DAG Helper Functions
  // ============================================================================

  /**
   * Get all blocks from a specific round in the DAG
   */
  pure def blocks_at_round(dag: DAG, round: Round): Set[StatementBlock] = {
    dag.filter(b => b.reference.round == round)
  }

  /**
   * Get children of a block (blocks in next round that reference it)
   */
  pure def children_of(dag: DAG, block: StatementBlock): Set[StatementBlock] = {
    val potential_children = dag.blocks_at_round(block.reference.round + 1)
    potential_children.filter(child => child.parents.contains(block.reference))
  }

  /**
   * Check if later_block has a causal link to earlier_block
   */
  pure def is_link(dag: DAG, earlier_block: StatementBlock, later_block: StatementBlock): bool = {
    val linked_to_earlier = range(earlier_block.reference.round + 1, later_block.reference.round + 1)
      .foldl(Set(earlier_block), (linked_blocks, r) => {
        val r_blocks = dag.blocks_at_round(r)
        linked_blocks.union(r_blocks.filter(block =>
          linked_blocks.exists(b => block.parents.contains(b.reference))
        ))
      })

    linked_to_earlier.contains(later_block)
  }

  /**
   * Check if block with given reference exists in DAG
   */
  pure def has_block(dag: DAG, reference: BlockReference): bool = {
    dag.exists(b => and {
      b.reference.authority == reference.authority,
      b.reference.round == reference.round,
      b.reference.leader_rank == reference.leader_rank
    })
  }

  /**
   * Get highest round in DAG
   */
  pure def highest_round(dag: DAG): Round = {
    dag.fold(0, (max_round, block) => {
      if (block.reference.round > max_round) block.reference.round else max_round
    })
  }

  /**
   * Check if all parents of a block are in the DAG
   */
  pure def all_parents_present(dag: DAG, block: StatementBlock): bool = {
    if (block.reference.round == 0) {
      true
    } else {
      val prev_round_blocks = dag.blocks_at_round(block.reference.round - 1)
      val prev_round_refs = prev_round_blocks.map(b => b.reference)
      block.parents.subseteq(prev_round_refs)
    }
  }

  /**
   * Check if DAG has enough blocks for a round (2F+1)
   */
  pure def has_quorum_at_round(dag: DAG, round: Round, faulty: int): bool = {
    dag.blocks_at_round(round).size() >= 2 * faulty + 1
  }

  /**
   * Check if all correct nodes have blocks at a round (stabilization)
   */
  pure def is_stabilized(dag: DAG, round: Round, correct_nodes: Set[Authority]): bool = {
    val authorities_with_blocks = dag.blocks_at_round(round).map(b => b.reference.authority)
    correct_nodes.subseteq(authorities_with_blocks)
  }
}
