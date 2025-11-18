// -*- mode: Bluespec; -*-

/**
 * Test instance of TetraBFT Choreo
 * Configuration: N=4, F=1 (one Byzantine fault)
 */
module instance {
  import option.* from "./spells/option"
  import types.* from "./types"
  import tetrabft(
    N = 4,
    F = 1,
    CORRECT = Set("n0", "n1", "n2"),
    FAULTY = Set("n3"),
    INITIAL_GST_VIEW = 2,
    MAX_VIEWS = 5
  ).* from "./tetrabft"

  // Re-export for easy access (already exported via .*)
  // action init = tetrabft::init
  // action step = tetrabft::step

  // Invariants exported from tetrabft (already exported via .*)
  // val agreement = tetrabft::agreement
  // val validity = tetrabft::validity

  // ==========================================================================
  // Tests
  // ==========================================================================

  // Simple test: Initialize and run a few steps
  run simpleTest = init.then(step).then(step).then(step)

  // Test that protocol progresses through phases
  // NOTE: Full consensus may not always be reachable in fixed steps due to
  // non-deterministic scheduling. This test verifies protocol mechanics work.
  run decisionTest = init.then(15.reps(_ => step))

  // ==========================================================================
  // Witnesses (Reachability Tests)
  // These check that the system actually evolves and reaches interesting states
  // ==========================================================================

  // Witness: At least one correct node decides
  val witness_some_decision = {
    CORRECT.exists(id => s.system.get(id).decided != None)
  }

  // Witness: All correct nodes decide
  val witness_all_decide = {
    CORRECT.forall(id => s.system.get(id).decided != None)
  }

  // Witness: All correct nodes decide on the same value (stronger than just agreement)
  val witness_consensus_reached = {
    val decided_values = CORRECT.fold(Set(), (acc, id) => {
      match s.system.get(id).decided {
        | Some(v) => acc.union(Set(v))
        | None => acc
      }
    })
    and {
      CORRECT.forall(id => s.system.get(id).decided != None),
      decided_values.size() == 1
    }
  }

  // Witness: Some node has cast a Phase1 vote
  val witness_phase1_vote = {
    CORRECT.exists(id => s.system.get(id).highest_votes.get(Phase1) != None)
  }

  // Witness: Some node has cast a Phase2 vote (means quorum of Phase1 seen)
  val witness_phase2_vote = {
    CORRECT.exists(id => s.system.get(id).highest_votes.get(Phase2) != None)
  }

  // Witness: Some node has cast a Phase3 vote
  val witness_phase3_vote = {
    CORRECT.exists(id => s.system.get(id).highest_votes.get(Phase3) != None)
  }

  // Witness: Some node has cast a Phase4 vote
  val witness_phase4_vote = {
    CORRECT.exists(id => s.system.get(id).highest_votes.get(Phase4) != None)
  }

  // Witness: All correct nodes have voted in Phase1
  val witness_all_voted_phase1 = {
    CORRECT.forall(id => s.system.get(id).highest_votes.get(Phase1) != None)
  }

  // Witness: All correct nodes have voted in Phase4
  val witness_all_voted_phase4 = {
    CORRECT.forall(id => s.system.get(id).highest_votes.get(Phase4) != None)
  }

  // Witness: Leader has broadcast a proposal (messages exist)
  val witness_proposal_sent = {
    NODES.exists(id =>
      s.messages.get(id).exists(msg => match (msg) {
        | MsgProposal(_) => true
        | _ => false
      })
    )
  }

  // Witness: Phase1 votes are in the network
  val witness_phase1_votes_in_network = {
    NODES.exists(id =>
      s.messages.get(id).exists(msg => match (msg) {
        | MsgVote(v) => v.phase == Phase1
        | _ => false
      })
    )
  }

  // Witness: A quorum of Phase4 votes exists (decision possible)
  val witness_phase4_quorum = {
    has_any_quorum(
      NODES.fold(Set(), (acc, id) => acc.union(s.messages.get(id))),
      Phase4,
      0  // view 0
    )
  }
}

