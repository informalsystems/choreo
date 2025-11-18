# ChonkyBFT: The Big Picture

ChonkyBFT is ZKSync's Byzantine fault tolerant consensus protocol designed for high-throughput blockchain applications. It achieves consensus with a 5F+1 resilience threshold in partial synchrony, optimized for environments with weighted voting where validators have different stake amounts.

## Key Features

- **Weighted Voting**: Supports validators with different voting weights based on stake
- **5F+1 Resilience**: Tolerates up to F Byzantine faults among 5F+1 replicas
- **View-Based Protocol**: Uses rotating leader election with view changes
- **Quorum Certificates**: Relies on signed quorum certificates for safety

## Execution Flow

        View v (Normal Operation):
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 1: NEW VIEW                                            │
        │ ─────────────────────                                        │
        │ Leader for view v broadcasts NEW_VIEW message containing:    │
        │ • View number v                                              │
        │ • Highest QC (quorum certificate) from previous views        │
        │                                                              │
        │ Purpose: Synchronize replicas on new view and safe block     │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 2: PROPOSE                                             │
        │ ────────────────────                                         │
        │ Leader proposes new block extending from highest QC:         │
        │ • Creates block with pending transactions                    │
        │ • Block extends from block in highest QC                     │
        │ • Broadcasts PROPOSAL to all replicas                        │
        │                                                              │
        │ Safety: Must extend from highest certified block             │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 3: VOTE                                                │
        │ ─────────────────                                            │
        │ Replicas validate proposal and vote:                         │
        │ • Check block extends from highest known QC                  │
        │ • Verify block is valid (well-formed, correct parent)        │
        │ • Send signed VOTE to leader                                 │
        │                                                              │
        │ Vote includes: view number, block hash, signature            │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 4: COMMIT                                              │
        │ ───────────────────                                          │
        │ Leader collects votes and forms QC:                          │
        │ • Waits for votes with quorum weight (2F+1)                  │
        │ • Creates QC (quorum certificate) with signatures            │
        │ • Broadcasts COMMIT message with QC                          │
        │                                                              │
        │ QC proves: quorum of replicas voted for this block           │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 5: DECIDE                                              │
        │ ───────────────────                                          │
        │ Block becomes committed when:                                │
        │ • Block b has QC                                             │
        │ • Block b' extends b and has QC (2-chain rule)               │
        │ • Execute block b and all ancestors ✓                        │
        │                                                              │
        │ Commit rule: 2-chain of certified blocks                     │
        └──────────────────────────────────────────────────────────────┘

## Safety and Liveness

    Safety Mechanism:
    ┌─────────────────────────────────────────────────────────────┐
    │ Quorum Intersection:                                        │
    │ • Any two quorums (2F+1 weight each) must intersect         │
    │ • Intersection contains at least one honest replica         │
    │ • Honest replica will not vote for conflicting blocks       │
    │                                                             │
    │ Lock Mechanism:                                             │
    │ • Replicas lock on highest QC they've seen                  │
    │ • Only vote for blocks extending from locked block          │
    │ • Prevents voting for conflicting forks                     │
    └─────────────────────────────────────────────────────────────┘

    View Changes (Liveness):
    ┌─────────────────────────────────────────────────────────────┐
    │ Timeout Mechanism:                                          │
    │ • Replicas timeout if no progress in current view           │
    │ • Send VIEW_CHANGE message to next leader                   │
    │ • Include highest QC as proof of progress                   │
    │                                                             │
    │ New View Formation:                                         │
    │ • New leader waits for quorum of VIEW_CHANGE messages       │
    │ • Selects highest QC among received messages                │
    │ • Starts new view by broadcasting NEW_VIEW                  │
    └─────────────────────────────────────────────────────────────┘
