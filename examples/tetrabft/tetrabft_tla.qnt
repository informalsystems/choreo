// -*- mode: Bluespec; -*-

/**
 * TetraBFT Consensus - Abstract Specification
 *
 * Based on the TLA+ specification from:
 * https://github.com/nano-o/tetrabft-tla
 *
 * This is a high-level specification of TetraBFT without network/messages.
 * Processes vote directly based on quorum predicates.
 */
module tetrabft_abstract {

  // ==========================================================================
  // Type Definitions
  // ==========================================================================

  type Process = str
  type Value = str
  type Round = int
  type Phase = int  // 1..4

  type Vote = {
    round: Round,
    phase: Phase,
    value: Value
  }

  // ==========================================================================
  // Constants (Module Parameters)
  // ==========================================================================

  const V: Set[Value]           // Set of values to decide on
  const P: Set[Process]         // Set of processes (3f+1)
  const Quorum: Set[Set[Process]]  // Quorums (sets of 2f+1 nodes)
  const Blocking: Set[Set[Process]] // Blocking sets (sets of f+1 nodes)
  const MaxRound: int           // Maximum round to explore

  // ==========================================================================
  // State Variables
  // ==========================================================================

  var Byz: Set[Process]           // Byzantine processes
  var votes: Process -> Set[Vote]  // Votes cast by each process
  var round: Process -> Round      // Current round of each process
  var proposed: bool               // Whether proposal made in good round
  var proposal: Value              // The good-round proposal
  var goodRound: Round             // Round that lasts long enough

  // ==========================================================================
  // Helper Functions
  // ==========================================================================

  pure def allRounds: Set[Round] = 0.to(MaxRound)

  // A value is decided if a quorum of non-Byzantine processes voted for it in phase 4
  pure def decided: Set[Value] = {
    V.filter(v =>
      Quorum.exists(Q =>
        allRounds.exists(r =>
          Q.exclude(Byz).forall(p =>
            votes.get(p).contains({ round: r, phase: 4, value: v })
          )
        )
      )
    )
  }

  // `v` is safe in round `r2` according to the votes of process `p` in phase `phase` before round r
  def claimsSafeAt(v: Value, r: Round, r2: Round, p: Process, phase: Phase): bool = {
    or {
      r2 == 0,
      votes.get(p).exists(vt1 =>
        and {
          vt1.round < r,
          r2 <= vt1.round,
          vt1.phase == phase,
          or {
            vt1.value == v,
            votes.get(p).exists(vt2 =>
              and {
                r2 <= vt2.round,
                vt2.round < vt1.round,
                vt2.phase == phase,
                vt2.value != vt1.value
              }
            )
          }
        }
      )
    }
  }

  // Whether value v is safe to vote for/propose in round r
  // phaseA=4, phaseB=1 for voting; phaseA=3, phaseB=2 for proposing
  def showsSafeAt(Q: Set[Process], v: Value, r: Round, phaseA: Phase, phaseB: Phase): bool = {
    or {
      r == 0,
      and {
        // Every member of Q is in round at least r
        Q.forall(q => round.get(q) >= r),
        or {
          // Members of Q never voted in phaseA before round r
          Q.forall(q =>
            votes.get(q).forall(vt => vt.round < r implies vt.phase != phaseA)
          ),
          // Or there exists a round r2 < r where...
          allRounds.filter(r2 => r2 >= 0 and r2 < r).exists(r2 =>
            and {
              // No member of Q voted in phaseA after r2 and before r
              // All members of Q that voted in r2 voted for v
              Q.forall(q =>
                votes.get(q).forall(vt =>
                  (vt.round < r and vt.phase == phaseA) implies and {
                    vt.round <= r2,
                    (vt.round == r2) implies (vt.value == v)
                  }
                )
              ),
              // v must be safe at r2 (blocking set claims it)
              Blocking.exists(S =>
                S.forall(q => claimsSafeAt(v, r, r2, q, phaseB))
              )
            }
          )
        }
      }
    }
  }

  // Helper to check if value accepted by quorum
  def accepted(p: Process, v: Value, r: Round, phase: Phase): bool = {
    Quorum.exists(Q =>
      Q.forall(q => votes.get(q).contains({ round: r, phase: phase, value: v }))
    )
  }

  // ==========================================================================
  // Actions
  // ==========================================================================

  action init = all {
    nondet byz = P.powerset().oneOf()
    Byz' = byz,
    votes' = P.mapBy(p => Set()),
    round' = P.mapBy(p => -1),
    proposed' = false,
    nondet v = V.oneOf()
    proposal' = v,
    nondet gr = Set(-1).union(allRounds).oneOf()
    goodRound' = gr
  }

  action startRoundAction(p: Process, r: Round): bool = all {
    not(Byz.contains(p)),
    (goodRound > -1) implies (r <= goodRound),
    round.get(p) < r,
    round' = round.set(p, r),
    votes' = votes,
    proposed' = proposed,
    proposal' = proposal,
    goodRound' = goodRound,
    Byz' = Byz
  }

  action proposeAction(v: Value): bool = all {
    goodRound > -1,
    not(proposed),
    Quorum.exists(Q => showsSafeAt(Q, v, goodRound, 3, 2)),
    proposed' = true,
    proposal' = v,
    votes' = votes,
    round' = round,
    goodRound' = goodRound,
    Byz' = Byz
  }

  // Helper: cast vote if not already voted in this round/phase
  action doVote(p: Process, v: Value, r: Round, phase: Phase): bool = all {
    // Never voted before in this round and phase
    votes.get(p).forall(vt => vt.round != r or vt.phase != phase),
    // Cast the vote
    votes' = votes.set(p, votes.get(p).union(Set({ round: r, phase: phase, value: v })))
  }

  action vote1Action(p: Process, v: Value, r: Round): bool = all {
    not(Byz.contains(p)),
    r == round.get(p),
    (r == goodRound) implies (proposed and v == proposal),
    Quorum.exists(Q => showsSafeAt(Q, v, r, 4, 1)),
    doVote(p, v, r, 1),
    round' = round,
    proposed' = proposed,
    proposal' = proposal,
    goodRound' = goodRound,
    Byz' = Byz
  }

  action vote2Action(p: Process, v: Value, r: Round): bool = all {
    not(Byz.contains(p)),
    round.get(p) <= r,
    accepted(p, v, r, 1),
    doVote(p, v, r, 2),
    round' = round.set(p, r),
    proposed' = proposed,
    proposal' = proposal,
    goodRound' = goodRound,
    Byz' = Byz
  }

  action vote3Action(p: Process, v: Value, r: Round): bool = all {
    not(Byz.contains(p)),
    round.get(p) <= r,
    accepted(p, v, r, 2),
    doVote(p, v, r, 3),
    round' = round.set(p, r),
    proposed' = proposed,
    proposal' = proposal,
    goodRound' = goodRound,
    Byz' = Byz
  }

  action vote4Action(p: Process, v: Value, r: Round): bool = all {
    not(Byz.contains(p)),
    round.get(p) <= r,
    accepted(p, v, r, 3),
    doVote(p, v, r, 4),
    round' = round.set(p, r),
    proposed' = proposed,
    proposal' = proposal,
    goodRound' = goodRound,
    Byz' = Byz
  }

  // Byzantine behavior: arbitrary vote/round changes for Byzantine processes
  action byzantineHavoc = {
    nondet p = Byz.oneOf()
    nondet newVotes = votes.get(p).powerset().oneOf()
    nondet newRound = allRounds.oneOf()
    all {
      votes' = votes.set(p, newVotes),
      round' = round.set(p, newRound),
      proposed' = proposed,
      proposal' = proposal,
      goodRound' = goodRound,
      Byz' = Byz
    }
  }

  action step = any {
    nondet p = P.oneOf()
    nondet v = V.oneOf()
    nondet r = allRounds.oneOf()
    any {
      byzantineHavoc,
      vote1Action(p, v, r),
      vote2Action(p, v, r),
      vote3Action(p, v, r),
      vote4Action(p, v, r),
      startRoundAction(p, r),
      proposeAction(v)
    }
  }

  // ==========================================================================
  // Safety Properties
  // ==========================================================================

  // Consistency: at most one value is decided
  val consistency = decided.size() <= 1

  // Type invariant
  val typeOK = and {
    P.forall(p =>
      votes.get(p).forall(vt =>
        and {
          vt.phase >= 1 and vt.phase <= 4,
          vt.round >= 0 and vt.round <= MaxRound,
          V.contains(vt.value)
        }
      )
    ),
    P.forall(p => round.get(p) >= -1 and round.get(p) <= MaxRound),
    goodRound >= -1 and goodRound <= MaxRound
  }

  // No future votes: process cannot have votes in rounds higher than their current round
  val noFutureVote = P.exclude(Byz).forall(p =>
    votes.get(p).forall(vt => vt.round <= round.get(p))
  )

  // One value per phase per round
  val oneValuePerPhasePerRound = P.exclude(Byz).forall(p =>
    votes.get(p).forall(vt =>
      votes.get(p).forall(vt2 =>
        (vt2.round == vt.round and vt2.phase == vt.phase) implies (vt2.value == vt.value)
      )
    )
  )

  // Votes in phase > 1 require quorum support in previous phase
  val voteHasQuorumInPreviousPhase = P.exclude(Byz).forall(p =>
    votes.get(p).forall(vt =>
      (vt.phase > 1) implies Quorum.exists(Q =>
        Q.exclude(Byz).forall(q =>
          votes.get(q).contains({ round: vt.round, phase: vt.phase - 1, value: vt.value })
        )
      )
    )
  )

  // Combined consistency invariant
  val consistencyInvariant = and {
    typeOK,
    noFutureVote,
    oneValuePerPhasePerRound,
    voteHasQuorumInPreviousPhase
  }
}
