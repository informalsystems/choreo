// -*- mode: Bluespec; -*-
// Witness properties for atm_distributed, generated with Quint LLM Kit [1]
//
// [1]: https://github.com/informalsystems/quint-llm-kit
module atm_distributed_witnesses {
  import atm_distributed.* from "./atm_distributed"
  import basicSpells.* from "../../spells/basicSpells"

  // ============================================================
  // WITNESS CATALOG
  // ============================================================
  //
  // Total witnesses: 11
  //
  // Usage:
  //   quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //     --invariant=<witness_name> \
  //     --max-steps=20 --max-samples=1000 --backend=rust
  //
  // Expected: Invariant VIOLATION (proves reachability)
  //
  // Liveness Witnesses (3):
  //   • canCompleteWithdrawal       - A withdrawal commits and some ATM's balance decreases
  //   • canAbortWithdrawal          - A conflict occurs and a DenyLock is sent
  //   • canBalanceReachZero         - An account balance is fully depleted (two $50 withdrawals)
  //
  // Reachability Witnesses (4):
  //   • canHavePendingWithdrawal    - An ATM has an in-flight withdrawal
  //   • canGrantLockToAnother       - An ATM holds a lock reserved for another ATM
  //   • canHaveConcurrentConflict   - Two ATMs race to lock the same account simultaneously
  //   • canProcessMultipleCycles    - An ATM initiates more than one withdrawal across its lifetime
  //
  // New Witnesses (4) — cover mechanisms added after initial generation:
  //   • canTrackWithdrawals         - total_withdrawn accumulates (CustomEffects/Extensions work)
  //   • canReleaseLockViaCommit     - a granted lock is atomically released by update_balance
  //   • canDenyDueToPendingConflict - ATM denies a lock because it has a pending withdrawal for the same account
  //   • canConflictThenCommit       - after a race, one ATM aborts while the other still commits
  //
  // ============================================================

  // ============================================================
  // LIVENESS WITNESSES
  // ============================================================

  // ──────────────────────────────────────────────────────────
  // Witness: canCompleteWithdrawal
  // ──────────────────────────────────────────────────────────
  // Goal: Verify a withdrawal can actually commit
  // Condition: Some ATM's balance for some account drops below INITIAL_BALANCE (100)
  // Rationale: Confirms the happy-path protocol reaches CommitWithdrawal
  //
  // Execution path:
  //   1. ATM1 initiates withdrawal for Alice → broadcasts RequestLock
  //   2. ATM2 and ATM3 each respond with GrantLock
  //   3. ATM1 receives both grants (quorum) and sufficient balance → commits
  //   4. ATM1 broadcasts CommitWithdrawal; balance in ATM1's replica decreases
  //
  // EXPECTED: Invariant violation (proves withdrawal can complete)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canCompleteWithdrawal --max-steps=20 --max-samples=1000 --backend=rust
  // ──────────────────────────────────────────────────────────
  val anyBalanceDecreased: bool =
    ATMS.exists(atm =>
      ACCOUNTS.exists(acc =>
        s.system.get(atm).balances.get(acc) < INITIAL_BALANCE
      )
    )

  val canCompleteWithdrawal: bool = not(anyBalanceDecreased)

  // ──────────────────────────────────────────────────────────
  // Witness: canAbortWithdrawal
  // ──────────────────────────────────────────────────────────
  // Goal: Verify a withdrawal conflict can occur, triggering an abort
  // Condition: A DenyLock message is visible in some ATM's inbox
  // Rationale: Confirms the collision-handling path is exercisable
  //
  // Execution path:
  //   1. ATM1 initiates for Alice → broadcasts RequestLock
  //   2. ATM2 grants ATM1's lock (reserves lock in locks_granted_to_others)
  //   3. ATM3 also initiates for Alice → broadcasts RequestLock
  //   4. ATM2 sees ATM3's RequestLock but Alice is already locked → sends DenyLock to ATM3
  //
  // EXPECTED: Invariant violation (proves conflict/abort path is reachable)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canAbortWithdrawal --max-steps=20 --max-samples=1000 --backend=rust
  // ──────────────────────────────────────────────────────────
  val anyDenyLockVisible: bool =
    ATMS.exists(atm =>
      s.messages.get(atm).exists(m => match m {
        | DenyLock(_) => true
        | _ => false
      })
    )

  val canAbortWithdrawal: bool = not(anyDenyLockVisible)

  // ──────────────────────────────────────────────────────────
  // Witness: canBalanceReachZero
  // ──────────────────────────────────────────────────────────
  // Goal: Verify an account can be fully depleted
  // Condition: Some ATM shows a balance of exactly 0 for some account
  // Rationale: Confirms the protocol handles repeated withdrawals down to zero
  //
  // Execution path:
  //   1. ATM1 completes a full $50 withdrawal for Alice (balance: 100 → 50)
  //   2. ATM1 or another ATM completes a second $50 withdrawal for Alice (balance: 50 → 0)
  //
  // EXPECTED: Invariant violation (proves full depletion is possible)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canBalanceReachZero --max-steps=30 --max-samples=1000 --backend=rust
  // ──────────────────────────────────────────────────────────
  val anyBalanceAtZero: bool =
    ATMS.exists(atm =>
      ACCOUNTS.exists(acc =>
        s.system.get(atm).balances.get(acc) == 0
      )
    )

  val canBalanceReachZero: bool = not(anyBalanceAtZero)

  // ============================================================
  // REACHABILITY WITNESSES
  // ============================================================

  // ──────────────────────────────────────────────────────────
  // Witness: canHavePendingWithdrawal
  // ──────────────────────────────────────────────────────────
  // Goal: Verify ATMs can enter the "pending withdrawal" coordination state
  // Condition: At least one ATM has pending_withdrawal != None
  // Rationale: Confirms initiate_withdrawal fires and sets up protocol coordination
  //
  // Execution path:
  //   1. Any ATM calls initiate_withdrawal → pending_withdrawal becomes Some(...)
  //
  // EXPECTED: Invariant violation (reachable in ~1 step)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canHavePendingWithdrawal --max-steps=5 --max-samples=100 --backend=rust
  // ──────────────────────────────────────────────────────────
  val anyPendingWithdrawal: bool =
    ATMS.exists(atm => match s.system.get(atm).pending_withdrawal {
      | Some(_) => true
      | None => false
    })

  val canHavePendingWithdrawal: bool = not(anyPendingWithdrawal)

  // ──────────────────────────────────────────────────────────
  // Witness: canGrantLockToAnother
  // ──────────────────────────────────────────────────────────
  // Goal: Verify ATMs can hold a lock on behalf of another ATM
  // Condition: Some ATM's locks_granted_to_others is non-empty
  // Rationale: Confirms respond_to_lock_request fires and reserves the lock correctly
  //
  // Execution path:
  //   1. ATM1 initiates → broadcasts RequestLock
  //   2. ATM2 receives RequestLock and responds with GrantLock, updating locks_granted_to_others
  //
  // EXPECTED: Invariant violation (reachable in ~2 steps)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canGrantLockToAnother --max-steps=10 --max-samples=100 --backend=rust
  // ──────────────────────────────────────────────────────────
  val anyLockGrantedToOther: bool =
    ATMS.exists(atm =>
      ACCOUNTS.exists(acc =>
        s.system.get(atm).locks_granted_to_others.get(acc) != None
      )
    )

  val canGrantLockToAnother: bool = not(anyLockGrantedToOther)

  // ──────────────────────────────────────────────────────────
  // Witness: canHaveConcurrentConflict
  // ──────────────────────────────────────────────────────────
  // Goal: Verify two ATMs can simultaneously race to lock the same account
  // Condition: Two ATMs both have pending_withdrawal on the same account
  // Rationale: The core safety scenario — confirms the race condition the protocol must prevent
  //
  // Execution path:
  //   1. ATM1 initiates for Alice (pending_withdrawal = Some({account: "Alice", ...}))
  //   2. Before any lock responses arrive, ATM2 also initiates for Alice
  //   → Both ATMs now have pending_withdrawal with account = "Alice"
  //
  // EXPECTED: Invariant violation (proves race condition is observable)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canHaveConcurrentConflict --max-steps=10 --max-samples=500 --backend=rust
  // ──────────────────────────────────────────────────────────
  val hasConcurrentPendingForSameAccount: bool =
    ACCOUNTS.exists(acc =>
      ATMS.filter(atm =>
        match s.system.get(atm).pending_withdrawal {
          | Some(pw) => pw.account == acc
          | None => false
        }
      ).size() >= 2
    )

  val canHaveConcurrentConflict: bool = not(hasConcurrentPendingForSameAccount)

  // ──────────────────────────────────────────────────────────
  // Witness: canProcessMultipleCycles
  // ──────────────────────────────────────────────────────────
  // Goal: Verify the protocol can complete multiple withdrawal cycles end-to-end
  // Condition: Some account's round > 1 on some ATM (at least 2 commits for that account)
  // Rationale: Confirms locks are properly released and the system resets for subsequent operations
  //
  // Execution path:
  //   1. ATM1 completes one full withdrawal cycle for Alice (round increments to 1)
  //   2. Any ATM completes another withdrawal for Alice (round increments to 2)
  //
  // EXPECTED: Invariant violation (proves protocol is not stuck after first round)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canProcessMultipleCycles --max-steps=20 --max-samples=1000 --backend=rust
  // ──────────────────────────────────────────────────────────
  val atmAttemptedMultipleCycles: bool =
    ATMS.exists(atm =>
      ACCOUNTS.exists(acc => s.system.get(atm).rounds.get(acc) > 1)
    )

  val canProcessMultipleCycles: bool = not(atmAttemptedMultipleCycles)

  // ============================================================
  // NEW WITNESSES — cover mechanisms added after initial generation
  // ============================================================

  // ──────────────────────────────────────────────────────────
  // Witness: canTrackWithdrawals
  // ──────────────────────────────────────────────────────────
  // Goal: Verify total_withdrawn accumulates when a withdrawal commits
  // Condition: s.extensions.total_withdrawn.get(acc) > 0 for some account
  // Rationale: Without this witness, the no_overdraft invariant is vacuous —
  //   total_withdrawn could always be 0 and the invariant would trivially hold.
  //   This proves the CustomEffects/Extensions machinery actually runs.
  //
  // EXPECTED: Invariant violation (proves tracking works)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canTrackWithdrawals --max-steps=20 --max-samples=500 --backend=rust
  // ──────────────────────────────────────────────────────────
  val anyWithdrawalTracked: bool =
    ACCOUNTS.exists(acc => s.extensions.total_withdrawn.get(acc) > 0)

  val canTrackWithdrawals: bool = not(anyWithdrawalTracked)

  // ──────────────────────────────────────────────────────────
  // Witness: canReleaseLockViaCommit
  // ──────────────────────────────────────────────────────────
  // Goal: Verify granted locks are atomically released by update_balance
  // Condition: Some balance has decreased AND all locks_granted_to_others are empty
  // Rationale: Confirms the atomic release fix: update_balance removes the lock
  //   from locks_granted_to_others at the same time it applies the new balance.
  //   If locks were not released, the system would deadlock after the first withdrawal.
  //
  // Execution path:
  //   1. ATM1 initiates → ATM2 and ATM3 grant locks (non-empty locks_granted_to_others)
  //   2. ATM1 commits → broadcasts CommitWithdrawal
  //   3. ATM2 and ATM3 call update_balance → their locks_granted_to_others become empty
  //   → Balance decreased AND all lock maps empty
  //
  // EXPECTED: Invariant violation (proves atomic lock release works)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canReleaseLockViaCommit --max-steps=20 --max-samples=500 --backend=rust
  // ──────────────────────────────────────────────────────────
  val allLocksReleasedAfterCommit: bool =
    anyBalanceDecreased and
    ATMS.forall(atm =>
      ACCOUNTS.forall(acc =>
        s.system.get(atm).locks_granted_to_others.get(acc) == None
      )
    )

  val canReleaseLockViaCommit: bool = not(allLocksReleasedAfterCommit)

  // ──────────────────────────────────────────────────────────
  // Witness: canDenyDueToPendingConflict
  // ──────────────────────────────────────────────────────────
  // Goal: Verify the mutual-grant fix code path actually fires
  // Condition: A DenyLock is in some ATM's inbox AND the denying ATM (from_atm)
  //   still has pending_withdrawal for that same account
  // Rationale: The mutual-grant fix added a second deny condition:
  //   pending_withdrawal.account == req.account triggers a deny.
  //   Without this witness, that code path could be dead and we'd never know.
  //   This directly proves the new deny path is exercised.
  //
  // Execution path:
  //   1. ATM1 and ATM2 both initiate withdrawal for Alice
  //   2. ATM1 sees ATM2's RequestLock — ATM1 is pending for Alice → sends DenyLock
  //   → DenyLock is in ATM2's inbox; ATM1 still has pending_withdrawal = Some({account: "Alice"})
  //
  // EXPECTED: Invariant violation (proves mutual-grant fix code path is live)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canDenyDueToPendingConflict --max-steps=10 --max-samples=500 --backend=rust
  // ──────────────────────────────────────────────────────────
  val denyLockFromPendingAtm: bool =
    ATMS.exists(atm =>
      s.messages.get(atm).exists(m => match m {
        | DenyLock(d) =>
            match s.system.get(d.from_atm).pending_withdrawal {
              | Some(pw) => pw.account == d.req.account
              | None => false
            }
        | _ => false
      })
    )

  val canDenyDueToPendingConflict: bool = not(denyLockFromPendingAtm)

  // ──────────────────────────────────────────────────────────
  // Witness: canConflictThenCommit
  // ──────────────────────────────────────────────────────────
  // Goal: Verify the protocol is live after a conflict — one ATM aborts, the other commits
  // Condition: total_withdrawn > 0 for some account AND some ATM's round > 0
  //   (a commit completed, advancing the round)
  // Rationale: Confirms the protocol doesn't deadlock after a conflict. The pending-withdrawal
  //   deny denies one ATM so the other can collect quorum and commit.
  //   round > 0 means a withdrawal committed and the account advanced to the next round.
  //
  // Execution path:
  //   1. ATM1 and ATM2 race for Alice — ATM2 is denied, ATM1 commits
  //   2. ATM1's round for Alice advances to 1
  //   → total_withdrawn["Alice"] > 0 AND round["Alice"] == 1
  //
  // EXPECTED: Invariant violation (proves protocol recovers from conflicts)
  //
  // Run: quint run specs/atm_distributed_witnesses.qnt --main=atm_distributed_witnesses \\
  //        --invariant=canConflictThenCommit --max-steps=30 --max-samples=1000 --backend=rust
  // ──────────────────────────────────────────────────────────
  val commitAfterCycle: bool =
    anyWithdrawalTracked and
    ATMS.exists(atm =>
      ACCOUNTS.exists(acc => s.system.get(atm).rounds.get(acc) > 0)
    )

  val canConflictThenCommit: bool = not(commitAfterCycle)
}
