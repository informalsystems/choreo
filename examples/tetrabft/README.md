# TetraBFT: The Big Picture

TetraBFT is a novel unauthenticated Byzantine fault tolerant protocol for solving consensus in partial synchrony, eliminating the need for public key cryptography and ensuring resilience against
computationally unbounded adversaries ("TetraBFT: Reducing Latency of Unauthenticated, Responsive BFT Consensus" by Qianyu Yu, Giuliano Losa, Xuechao Wang (PODC 2024); Paper: [arXiv:2405.02615](https://arxiv.org/abs/2405.02615)). TetraBFT achieves consensus in 5 message delays without cryptographic signatures.

## Execution Flow

        View 0 (or new view):
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 0: SUGGEST/PROOF                                       │
        │ ─────────────────────────                                    │
        │ Nodes exchange voting history:                               │
        │ • Non-leaders → Send SUGGEST to leader (vote-2, vote-3)      │
        │ • All nodes   → Broadcast PROOF (vote-1, vote-4)             │
        │                                                              │
        │ Why? Leader needs vote history to determine safe value       │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 1: PROPOSAL                                            │
        │ ─────────────────────                                        │
        │ Leader waits for quorum of suggests, then:                   │
        │ • Uses Rule 1 to pick safe value from voting history         │
        │ • Broadcasts PROPOSAL                                        │
        │                                                              │
        │ Rule 1: "No conflicting locks? Any value safe.               │
        │          Conflicting locks? Pick locked value."              │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 2: VOTE-1                                              │
        │ ───────────────────                                          │
        │ Followers receive proposal:                                  │
        │ • Use Rule 3 to verify proposal safety from proofs           │
        │ • If safe → Broadcast VOTE-1                                 │
        │                                                              │
        │ Rule 3: "Check if proposal matches locked value              │
        │          or no value was locked."                            │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 3: VOTE-2                                              │
        │ ───────────────────                                          │
        │ Upon seeing QUORUM of vote-1 for value v:                    │
        │ • Broadcast VOTE-2 for v                                     │
        │                                                              │
        │ Note: Vote-2 goes into SUGGEST messages (Rule 1, Rule 2)     │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 4: VOTE-3                                              │
        │ ───────────────────                                          │
        │ Upon seeing QUORUM of vote-2 for value v:                    │
        │ • Broadcast VOTE-3 for v  ← THIS CREATES A "LOCK"            │
        │                                                              │
        │ Note: Vote-3 goes into SUGGEST messages (Rule 1)             │
        │       Locked value = value with quorum of vote-3             │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 5: VOTE-4                                              │
        │ ───────────────────                                          │
        │ Upon seeing QUORUM of vote-3 for value v:                    │
        │ • Broadcast VOTE-4 for v                                     │
        │                                                              │
        │ Note: Vote-4 goes into PROOF messages (Rule 3, Rule 4)       │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 6: DECISION                                            │
        │ ─────────────────────                                        │
        │ Upon seeing QUORUM of vote-4 for value v:                    │
        │ • DECIDE on v                                                │
        │ • Done! ✓                                                    │
        └──────────────────────────────────────────────────────────────┘

## Safety Rules

    TetraBFT uses two parallel tracks to verify safety:

    Track 1: Suggest Messages (for proposals)

    Leader's Safety Check (Rule 1):
        ┌─> Collect QUORUM of suggests (vote-2, vote-3 history)
        ├─> Check: Is anyone locked on a value? (vote-3 quorum)
        │   └─> YES: Must propose that locked value
        │   └─> NO:  Can propose any value
        └─> Verify with blocking set via Rule 2 (vote-2 history)

    Track 2: Proof Messages (for voting)

    Follower's Safety Check (Rule 3):
        ┌─> Collect QUORUM of proofs (vote-1, vote-4 history)
        ├─> Check: Is anyone locked on a value? (vote-4 quorum)
        │   └─> YES: Proposal must match that locked value
        │   └─> NO:  Can vote for any safe proposal
        └─> Verify with blocking set via Rule 4 (vote-1 history)

    ╔══════════════════════════════════════════════════════════╗
    ║  Track 1: SUGGEST Track (vote-2, vote-3)                 ║
    ║  ────────────────────────────────────────                ║
    ║  Used by: LEADERS (Rule 1)                               ║
    ║  Purpose: Determine which value is safe to PROPOSE       ║
    ║                                                          ║
    ║  vote-2 → vote-3 → LOCK created                          ║
    ║                                                          ║
    ║  Stored in: SUGGEST messages (sent to leader)            ║
    ╚══════════════════════════════════════════════════════════╝

    ╔══════════════════════════════════════════════════════════╗
    ║  Track 2: PROOF Track (vote-1, vote-4)                   ║
    ║  ────────────────────────────────────────                ║
    ║  Used by: FOLLOWERS (Rule 3)                             ║
    ║  Purpose: Verify that proposal is safe to VOTE FOR       ║
    ║                                                          ║
    ║  vote-1 → vote-4 → COMMITMENT created                    ║
    ║                                                          ║
    ║  Stored in: PROOF messages (broadcast to all)            ║
    ╚══════════════════════════════════════════════════════════╝
