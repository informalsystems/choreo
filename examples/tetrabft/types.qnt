// -*- mode: Bluespec; -*-

/**
 * TetraBFT Types for Choreo Implementation
 *
 * Based on "TetraBFT: Reducing Latency of Unauthenticated, Responsive BFT Consensus"
 * by Qianyu Yu, Giuliano Losa, Xuechao Wang (PODC 2024)
 *
 * TetraBFT achieves consensus in 5 message delays without cryptographic signatures.
 *
 * Yassine & Claude Code, 2025
 */
module types {
  import basicSpells.* from "./spells/basicSpells"
  import option.* from "./spells/option"

  // ==========================================================================
  // Core Types
  // ==========================================================================

  type NodeId = str
  type View = int
  type Value = str  // The value being proposed for consensus

  /**
   * Vote record - tracks a node's vote at a specific phase
   */
  type VoteRecord = {
    view: View,
    value: Value,
    voter: NodeId
  }

  /**
   * Vote phase enumeration
   * TetraBFT has 4 voting phases: vote-1, vote-2, vote-3, vote-4
   */
  type VotePhase =
    | Phase1
    | Phase2
    | Phase3
    | Phase4

  /**
   * Suggest message - contains voting history for safety checking
   * Leader uses these to determine safe values (Rule 1)
   * NOTE: All fields optional - node might not have voted in early views
   */
  type SuggestMessage = {
    highest_vote2: Option[VoteRecord],        // Highest vote-2 this node sent
    second_highest_vote2: Option[VoteRecord],  // Second-highest vote-2
    latest_vote3: Option[VoteRecord]  // Latest vote-3 this node sent (used in Rule 1)
  }

  /**
   * Proof message - parallel to suggest, uses vote-1 and vote-4
   * Followers use these to verify leader's proposal (Rule 3)
   * NOTE: All fields optional - node might not have voted in early views
   */
  type ProofMessage = {
    highest_vote1: Option[VoteRecord],        // Highest vote-1 this node sent
    second_highest_vote1: Option[VoteRecord],  // Second-highest vote-1
    latest_vote4: Option[VoteRecord]  // Latest vote-4 this node sent (used in Rule 3)
  }

  // ==========================================================================
  // Message Types
  // ==========================================================================

  /**
   * All message types in TetraBFT
   */
  type Message =
    | MsgSuggest({ from: NodeId, content: SuggestMessage })
    | MsgProof({ from: NodeId, content: ProofMessage })
    | MsgProposal({ view: View, value: Value, from: NodeId })
    | MsgVote({ phase: VotePhase, view: View, value: Value, from: NodeId })
    | MsgViewChange({ to_view: View, from: NodeId })

  // ==========================================================================
  // Local State
  // ==========================================================================

  /**
   * Node phase within a view
   * Updated to match exact protocol flow from TetraBFT paper
   */
  type NodePhase =
    | PhaseSendSuggestProof   // Initial: Need to send suggest+proof at view start
    | PhaseWaitingProposal    // Non-leader: After sending suggest+proof, waiting for proposal
    | PhaseCollectingSuggests // Leader: After sending proof, collecting suggests
    | PhaseVote1              // Vote-1 phase
    | PhaseVote2              // Vote-2 phase
    | PhaseVote3              // Vote-3 phase
    | PhaseVote4              // Vote-4 phase
    | PhaseDecision           // Decided

  /**
   * State fields specific to TetraBFT
   * Each node maintains constant-size state (highest and second-highest votes)
   */
  type StateFields = {
    // Process ID (for identification)
    process_id: NodeId,

    // Current view number
    current_view: View,

    // Current phase within view
    phase: NodePhase,

    // Highest and second-highest votes for each voting phase (1-4)
    // Maps from VotePhase to vote record
    highest_votes: VotePhase -> Option[VoteRecord],
    second_highest_votes: VotePhase -> Option[VoteRecord],

    // Decided value (None if not yet decided)
    decided: Option[Value]
  }

  // ==========================================================================
  // Extensions (Global Parameters)
  // ==========================================================================

  type Extensions = {
    leaders: List[NodeId],
    GST_view: View,
    ghost_step: GhostStep
  }

  type GhostStep =
    | StepPropose
    | StepVote
    | StepViewChange
    | StepIdle

  // ==========================================================================
  // Events
  // ==========================================================================

  // Timeout event (non-deterministic, models "eventually timeout occurs")
  type TimeoutEvent = { view: View }

  type Event =
    | EventDecide({ id: NodeId, value: Value })
    | EventViewTimeout(TimeoutEvent)

  // ==========================================================================
  // Custom Effects (Byzantine Behavior)
  // ==========================================================================

  type CustomEffects =
    | ByzantineProposal({ view: View, values: Set[Value] })
    | ByzantineVote({ phase: VotePhase, view: View, values: Set[Value] })
    | ByzantineSilence
}
