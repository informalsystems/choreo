// -*- mode: Bluespec; -*-

/**
 * Test instance of Mysticeti Choreo
 * Configuration: N=4, F=1 (one Byzantine fault)
 */
module instance {
  import mysticeti(N = 4, F = 1, CORRECT = Set("n0", "n1", "n2"), FAULTY = Set("n3"), INITIAL_GST_ROUND = 3, MAX_ROUNDS = 6).* from "./mysticeti"

  // Re-export for easy access (already exported via .*)
  // action init = mysticeti::init
  // action step = mysticeti::step
  // pure def total_order_inv = mysticeti::total_order_inv
  // pure def safety_inv = mysticeti::safety_inv

  // Simple test: Initialize and run a few steps
  run simpleTest = init.then(step).then(step).then(step)

  // Test total order invariant
  run totalOrderTest = init
    .then(5.reps(_ => step))
    .expect(total_order_inv)

  // Test safety invariant
  run safetyTest = init
    .then(5.reps(_ => step))
    .expect(safety_inv)

  // Test that eventually some commits are made
  val eventually_commits_witness = not(has_commits)

}
