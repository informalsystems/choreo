// -*- mode: Bluespec; -*-

/**
 * Concrete instance of Chonky BFT for testing
 * Configuration: N=4, F=0 (no Byzantine faults for simplicity)
 */
module instance {
  import chonkybft(
    N = 4,
    F = 0,
    CORRECT = Set("n1", "n2", "n3", "n4"),
    FAULTY = Set(),
    WEIGHTS = Map("n1" -> 1, "n2" -> 1, "n3" -> 1, "n4" -> 1),
    REPLICA_KEYS = Map("n1" -> "k1", "n2" -> "k2", "n3" -> "k3", "n4" -> "k4"),
    VIEWS = Set(0, 1, 2, 3, 4, 5),
    VALID_BLOCKS = Set("b0", "b1", "b2"),
    INVALID_BLOCKS = Set("invalid")
  ) as chonky from "./chonkybft"

  // Re-export for easy access
  action init = chonky::init
  action step = chonky::step
  pure def agreement_inv = chonky::agreement_inv
  pure def consistency_inv = chonky::consistency_inv

  // Simple test
  run simpleTest = init.then(step).then(step).then(step)

  // Test that agreement holds
  run agreementTest = init
    .then(5.reps(_ => step))
    .expect(agreement_inv)

  // Test that consistency holds
  run consistencyTest = init
    .then(5.reps(_ => step))
    .expect(consistency_inv)
}
