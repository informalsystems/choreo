# Mysticeti: The Big Picture

Mysticeti is a DAG-based Byzantine fault tolerant consensus protocol designed for high-throughput distributed systems. Unlike traditional chain-based protocols, Mysticeti uses a Directed Acyclic Graph (DAG) structure to achieve consensus, enabling higher throughput through parallel block proposals and implicit voting through block references.

## Key Features

- **DAG Structure**: Uses a DAG instead of a chain for higher throughput
- **Implicit Voting**: Blocks vote for ancestors through causal history (parent references)
- **Parallel Proposals**: Multiple authorities can propose blocks simultaneously
- **Leaderless Operation**: No single leader needed for normal operation
- **2F+1 Resilience**: Tolerates up to F Byzantine faults among 3F+1 replicas

## Execution Flow

        Round r:
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 1: BLOCK CREATION                                      │
        │ ─────────────────────────                                    │
        │ Each authority creates a block in round r:                   │
        │ • Include references to ALL blocks from round r-1            │
        │   (These references = implicit votes for ancestors)          │
        │ • Add new transactions from local pool                       │
        │ • Sign and broadcast block                                   │
        │                                                              │
        │ Key insight: Referencing = voting for entire causal history  │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 2: BLOCK RECEPTION & VALIDATION                        │
        │ ──────────────────────────────────────────                   │
        │ Upon receiving a block b:                                    │
        │ • Verify signature and well-formedness                       │
        │ • Check all parent blocks are present in DAG                 │
        │   └─> If missing parents: add to backlog                     │
        │   └─> If all parents present: add to DAG                     │
        │                                                              │
        │ DAG structure ensures causal ordering                        │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 3: QUORUM DETECTION                                    │
        │ ──────────────────────────                                   │
        │ For each block b in the DAG:                                 │
        │ • Count blocks in round r that reference b (directly or      │
        │   transitively through their causal history)                 │
        │ • If quorum (2F+1) blocks in round r reference b:            │
        │   └─> Block b is "certified" at round r                      │
        │                                                              │
        │ Certification proves quorum voted for block (via references) │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 4: COMMIT DECISION                                     │
        │ ────────────────────────                                     │
        │ A block b is committed when:                                 │
        │ • Block b is certified at round r                            │
        │ • At round r+1, a quorum of blocks (2F+1) built on top of b  │
        │   (This creates a "2-chain" of certified rounds)             │
        │                                                              │
        │ Commit rule: Certified block + certified child round         │
        └──────────────────────────────────────────────────────────────┘
                                    ↓
        ┌──────────────────────────────────────────────────────────────┐
        │ Phase 5: ORDERING & EXECUTION                                │
        │ ─────────────────────────────                                │
        │ Once blocks are committed:                                   │
        │ • Use DAG causal ordering to determine execution order       │
        │ • Deterministic function maps DAG to total order             │
        │ • Execute transactions in committed blocks ✓                 │
        │                                                              │
        │ All honest nodes compute same execution order                │
        └──────────────────────────────────────────────────────────────┘

## Safety and Liveness

    Safety Mechanism:
    ┌─────────────────────────────────────────────────────────────┐
    │ Causal History Preservation:                                │
    │ • If block b is certified, all ancestors of b are certified │
    │ • Certification requires quorum (2F+1) support              │
    │ • Quorum intersection ensures consistency                   │
    │                                                             │
    │ 2-Chain Rule:                                               │
    │ • Need two consecutive certified rounds for commit          │
    │ • Prevents premature commits on unstable history            │
    │ • Ensures all honest nodes see same committed blocks        │
    └─────────────────────────────────────────────────────────────┘

    Liveness Guarantee:
    ┌─────────────────────────────────────────────────────────────┐
    │ After GST (Global Stabilization Time):                      │
    │ • All honest authorities propose in each round              │
    │ • Quorum of blocks reference previous round                 │
    │ • Progress is guaranteed (commit at least one block/round)  │
    │                                                             │
    │ No View Changes Needed:                                     │
    │ • DAG structure naturally handles message delays            │
    │ • Blocks can be added out of order (via backlog)            │
    │ • No need for explicit view-change protocol                 │
    └─────────────────────────────────────────────────────────────┘
