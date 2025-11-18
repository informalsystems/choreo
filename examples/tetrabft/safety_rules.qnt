// -*- mode: Bluespec; -*-

/**
 * TetraBFT Safety Rules (Rules 1-4)
 *
 * Based on the TetraBFT paper (PODC 2024), Section 3.2
 * Paper: https://arxiv.org/abs/2405.02615
 *
 * These rules determine when a value is safe to propose/vote for:
 * - Rule 1 (Section 3.2): Leader determines safe value using suggest messages
 * - Rule 2 (Section 3.2): Node claims value safe in suggest using vote-2 history
 * - Rule 3 (Section 3.2): Follower verifies proposal safety using proof messages
 * - Rule 4 (Section 3.2): Node claims value safe in proof using vote-1 history
 *
 * Implementation follows Algorithm 1 (node_claim_safe) from Section 3.3
 */
module safety_rules {
  import option.* from "./spells/option"
  import types.* from "./types"

  // ==========================================================================
  // Rule 2: Claims Safe in Suggest (vote-2 based)
  // Paper Section 3.2, Algorithm 1
  // ==========================================================================
  /**
   * Rule 2 (Section 3.2): Node claims v safe at r' based on its vote-2 history
   *
   * Paper quote: "A node claims val safe at v' by reporting:
   * (1) v'=0, (2) highest vote-2 at view ≥v' for val, or
   * (3) second-highest vote-2 view ≥v'"
   *
   * Implementation note: We use exact equality for condition (2) to match
   * the algorithm's "at view r' for value v" requirement.
   *
   * @param suggest - The suggest message containing vote-2 history
   * @param v - The value being checked for safety
   * @param r_prime - The view at which we're checking safety
   * @return true if node claims v is safe at r'
   */
  pure def claims_safe_in_suggest(
    suggest: SuggestMessage,
    v: Value,
    r_prime: View
  ): bool = {
    or {
      // Condition 1: r' = 0
      r_prime == 0,
      // Condition 2: highest vote-2 at r' for v
      match suggest.highest_vote2 {
        | Some(hv2) => hv2.view == r_prime and hv2.value == v
        | None => false
      },
      // Condition 3: second-highest vote-2 >= r' (means conflicting votes)
      match suggest.second_highest_vote2 {
        | Some(shv2) => shv2.view >= r_prime
        | None => false
      }
    }
  }

  // ==========================================================================
  // Rule 4: Claims Safe in Proof (vote-1 based)
  // Paper Section 3.2, Algorithm 1
  // ==========================================================================
  /**
   * Rule 4 (Section 3.2): Node claims v safe at r' based on its vote-1 history
   *
   * Paper: "Parallel to Rule 2, using vote-1 history instead of vote-2"
   *
   * Same structure as Rule 2:
   * (1) r' = 0, OR
   * (2) highest vote-1 is at view r' for value v, OR
   * (3) second-highest vote-1 is at view >= r' (conflicting votes)
   *
   * @param proof - The proof message containing vote-1 history
   * @param v - The value being checked for safety
   * @param r_prime - The view at which we're checking safety
   * @return true if node claims v is safe at r'
   */
  pure def claims_safe_in_proof(
    proof: ProofMessage,
    v: Value,
    r_prime: View
  ): bool = {
    or {
      // Condition 1: r' = 0
      r_prime == 0,
      // Condition 2: highest vote-1 at r' for v
      match proof.highest_vote1 {
        | Some(hv1) => hv1.view == r_prime and hv1.value == v
        | None => false
      },
      // Condition 3: second-highest vote-1 >= r' (means conflicting votes)
      match proof.second_highest_vote1 {
        | Some(shv1) => shv1.view >= r_prime
        | None => false
      }
    }
  }

  // ==========================================================================
  // Helper: Extract max vote-3 view from suggests
  // ==========================================================================
  pure def max_vote3_view(suggests: Set[SuggestMessage]): Option[View] = {
    suggests.fold(None, (acc, sug) => {
      match sug.latest_vote3 {
        | None => acc
        | Some(v3) => match acc {
          | None => Some(v3.view)
          | Some(max_v) => if (v3.view > max_v) Some(v3.view) else acc
        }
      }
    })
  }

  // ==========================================================================
  // Helper: Check if quorum has no vote-3 before view r
  // ==========================================================================
  pure def no_vote3_before_r(suggests: Set[SuggestMessage], r: View): bool = {
    suggests.forall(sug => {
      match sug.latest_vote3 {
        | None => true
        | Some(v3) => v3.view >= r  // If they voted, it must be at or after r
      }
    })
  }

  // ==========================================================================
  // Helper: Get the highest view where quorum voted-3
  // ==========================================================================
  pure def get_highest_vote3_view(suggests: Set[SuggestMessage]): Option[View] = {
    val all_vote3_views = suggests.fold(Set(), (acc, sug) => {
      match sug.latest_vote3 {
        | None => acc
        | Some(v3) => acc.union(Set(v3.view))
      }
    })
    if (all_vote3_views.size() == 0) {
      None
    } else {
      Some(all_vote3_views.fold(0, (max_v, v) => if (v > max_v) v else max_v))
    }
  }

  // ==========================================================================
  // Rule 1: Leader Determines Safe (from suggests)
  // Paper Section 3.2, Algorithm 4 (Appendix A)
  // ==========================================================================
  /**
   * Rule 1 (Section 3.2): Leader determines v is safe to propose at view r
   *
   * Paper quote: "All values are safe in view 0. If v≠0, a leader determines
   * value val safe when: (1) quorum q sent suggests in view v, and (2) either
   * no member of q sent vote-3 before v, or there exists v'<v where all members
   * of q sending vote-3 in v' used val, with a blocking set claiming val safe at v'"
   *
   * Implementation (Algorithm 4):
   * IF r = 0: all values safe (no history)
   * ELSE: quorum Q sent suggests AND either:
   *   (a) No Q member sent vote-3 before r (no lock established), OR
   *   (b) ∃ r' < r where:
   *       (i)   No Q member sent vote-3 after r' (all agree on highest lock)
   *       (ii)  All Q members that voted-3 at r' voted for v (they locked on v)
   *       (iii) Blocking set (f+1) claims v safe at r' via Rule 2
   *
   * @param suggests - Quorum of suggest messages from nodes
   * @param v - The value being checked for safety
   * @param r - The current view number
   * @param blocking_size - Size of blocking set (f+1)
   * @return true if v is safe to propose at view r
   */
  pure def leader_determines_safe(
    suggests: Set[SuggestMessage],
    v: Value,
    r: View,
    blocking_size: int  // f+1
  ): bool = {
    or {
      // View 0: all values safe
      r == 0,

      // View > 0: check conditions (a) or (b)
      and {
        suggests.size() > 0,  // We have suggests
        or {
          // (a) No Q member sent vote-3 before r
          suggests.forall(sug => {
            match sug.latest_vote3 {
              | None => true
              | Some(v3) => v3.view >= r  // Should not have voted before r
            }
          }),

          // (b) Find r' < r satisfying (i), (ii), (iii)
          // Check all possible r' values from 0 to r-1
          (0).to(r - 1).exists(r_prime => {
            and {
              // (i) No Q member sent vote-3 after r'
              suggests.forall(sug => {
                match sug.latest_vote3 {
                  | None => true
                  | Some(v3) => v3.view <= r_prime
                }
              }),

              // (ii) All Q members that voted-3 at r' voted for v
              suggests.forall(sug => {
                match sug.latest_vote3 {
                  | None => true  // Didn't vote, ok
                  | Some(v3) => (v3.view != r_prime) or (v3.value == v)
                }
              }),

              // (iii) Blocking set (f+1) claims v safe at r' via Rule 2
              val claiming_nodes = suggests.filter(sug =>
                claims_safe_in_suggest(sug, v, r_prime)
              )
              claiming_nodes.size() >= blocking_size
            }
          })
        }
      }
    }
  }

  // ==========================================================================
  // Helper: Extract max vote-4 view from proofs
  // ==========================================================================
  pure def max_vote4_view(proofs: Set[ProofMessage]): Option[View] = {
    proofs.fold(None, (acc, prf) => {
      match prf.latest_vote4 {
        | None => acc
        | Some(v4) => match acc {
          | None => Some(v4.view)
          | Some(max_v) => if (v4.view > max_v) Some(v4.view) else acc
        }
      }
    })
  }

  // ==========================================================================
  // Rule 3: Follower Determines Safe (from proofs)
  // Paper Section 3.2, Algorithm 5 (Appendix A)
  // ==========================================================================
  /**
   * Rule 3 (Section 3.2): Follower determines v is safe to vote-1 for at view r
   *
   * Paper: "Node determines proposal safe mirroring Rule 1, using proof messages
   * with vote-1/vote-4 instead of vote-2/vote-3, plus special case detecting
   * two blocking sets claiming different values safe at sequential views"
   *
   * Implementation (Algorithm 5):
   * IF r = 0: all values safe (no history)
   * ELSE: quorum Q sent proofs AND either:
   *   (a) No Q member sent vote-4 before r, OR
   *   (b) ∃ r' < r where:
   *       (i)   No Q member sent vote-4 after r'
   *       (ii)  All Q members that voted-4 at r' voted for v
   *       (iii) Either:
   *             (A) Blocking set claims v safe at r' via Rule 4, OR
   *             (B) Two blocking sets claim different values safe at different r'
   *                 (escape hatch: means no value was actually locked)
   *
   * @param proofs - Quorum of proof messages from nodes
   * @param v - The value being checked for safety
   * @param r - The current view number
   * @param blocking_size - Size of blocking set (f+1)
   * @return true if v is safe to vote for at view r
   */
  pure def follower_determines_safe(
    proofs: Set[ProofMessage],
    v: Value,
    r: View,
    blocking_size: int  // f+1
  ): bool = {
    or {
      // View 0: all values safe
      r == 0,

      // View > 0: check conditions
      and {
        proofs.size() > 0,
        or {
          // (a) No Q member sent vote-4 before r
          proofs.forall(prf => {
            match prf.latest_vote4 {
              | None => true
              | Some(v4) => v4.view >= r
            }
          }),

          // (b) Find r' < r satisfying conditions
          (0).to(r - 1).exists(r_prime => {
            and {
              // (i) No Q member sent vote-4 after r'
              proofs.forall(prf => {
                match prf.latest_vote4 {
                  | None => true
                  | Some(v4) => v4.view <= r_prime
                }
              }),

              // (ii) All Q members that voted-4 at r' voted for v
              proofs.forall(prf => {
                match prf.latest_vote4 {
                  | None => true
                  | Some(v4) => (v4.view != r_prime) or (v4.value == v)
                }
              }),

              // (iii) Either (A) or (B)
              or {
                // (A) Blocking set claims v safe at r' via Rule 4
                val claiming_nodes = proofs.filter(prf =>
                  claims_safe_in_proof(prf, v, r_prime)
                )
                claiming_nodes.size() >= blocking_size,

                // (B) Two blocking sets claim different values safe
                // This is the "escape hatch" - if no value was really locked,
                // any value is safe to propose
                has_conflicting_locks(proofs, r, blocking_size)
              }
            }
          })
        }
      }
    }
  }

  // ==========================================================================
  // Helper: Check for conflicting locks (Rule 3, Item 2iiiB)
  // ==========================================================================
  /**
   * Check if there are two blocking sets claiming different values safe.
   * This means no value was actually locked, so any value is safe.
   */
  pure def has_conflicting_locks(
    proofs: Set[ProofMessage],
    r: View,
    blocking_size: int
  ): bool = {
    // For each pair of different r' values < r, check if we have
    // blocking sets claiming safety at different views
    (0).to(r - 1).exists(r1 => {
      (0).to(r - 1).exists(r2 => {
        and {
          r1 != r2,
          // Blocking set 1 claiming some value safe at r1
          proofs.exists(prf1 => {
            match prf1.highest_vote1 {
              | Some(hv1) => {
                val claiming_r1 = proofs.filter(prf =>
                  claims_safe_in_proof(prf, hv1.value, r1)
                )
                claiming_r1.size() >= blocking_size
              }
              | None => false
            }
          }),
          // Blocking set 2 claiming some value safe at r2
          proofs.exists(prf2 => {
            match prf2.highest_vote1 {
              | Some(hv2) => {
                val claiming_r2 = proofs.filter(prf =>
                  claims_safe_in_proof(prf, hv2.value, r2)
                )
                claiming_r2.size() >= blocking_size
              }
              | None => false
            }
          })
        }
      })
    })
  }
}
