// -*- mode: Bluespec; -*-

module test_base {
  import basicSpells.* from "lib/basicSpells"
  import tendermint.* from "tendermint"
  import CSMIBase as CSMI from "lib/csmi"
  import CSMIState(processes = Set("p1", "p2", "p3", "p4")) as CSMI from "lib/csmi"

  /// All received PreVotes
  pure def get_all_prevotes(s: LocalState): Set[PreVoteMsg] =
    s.messages.filterMap(m => {
      match m {
        | PreVote(p) => Some(p)
        | _ => None
      }
    })

  action receive_proposal_from(n: Node, src: Node): bool = {
    val msg = CSMI::s.system.get(n).get_proposals().filter(msg => msg.src == src).getOnlyElement()
    CSMI::receive_one_message(CSMI::s, n, Propose(msg), receive_message, apply_effect)
  }

  action receive_prevote_from(n: Node, src: Node): bool = {
    val msg = CSMI::s.system.get(n).get_all_prevotes().filter(msg => msg.src == src).getOnlyElement()
    CSMI::receive_one_message(CSMI::s, n, PreVote(msg), receive_message, apply_effect)
  }

  action receive_precommit_from(n: Node, src: Node): bool = {
    val msg = CSMI::s.system.get(n).get_all_precommits().filter(msg => msg.src == src).getOnlyElement()
    CSMI::receive_one_message(CSMI::s, n, PreCommit(msg), receive_message, apply_effect)
  }

  action receive_byzantine(n: Node, msg: Message): bool = {
    CSMI::receive_one_message(CSMI::s, n, msg, receive_message, apply_effect)
  }

  action expire_timeout(n: Node): bool = {
    val timeout = CSMI::s.activeTimeouts.get(n)
    CSMI::s' = CSMI::fire_one_timeout_event(CSMI::s, n, timeout.unwrap(), fire_timeout_event, apply_effect)
  }

  /* TESTS */

  // p2 is the next proposer
  run line28 = CSMI::init(initialize_process, initial_bookkeeping)
    // Both p1 and p2 receive the initial proposal
    .then("p1".receive_proposal_from("p1"))
    .then("p2".receive_proposal_from("p1"))

    // p1 receives prevotes from p1 and p2, and a byzantine prevote from p4
    // .then("p1".receive_prevote_from("p1"))
    // .then("p1".receive_prevote_from("p2"))
    .then("p1".receive_byzantine(PreVote({ src: "p4", round: 0, id: Some("v0".id()) })))

    // p1 has prevote quorum
    .expect(CSMI::s.system.get("p1").received_prevotes == Set(
      { src: "p1", round: 0, id: Some("v0".id()) },
      { src: "p2", round: 0, id: Some("v0".id()) },
      { src: "p4", round: 0, id: Some("v0".id()) },
    ))

    // And therefore sends a precommit
    .expect(CSMI::s.system.values().forall(s => s.messages.contains(
      PreCommit({ src: "p1", round: 0, id: Some("v0".id()) })
    )))

    // The same happens for p2
    // p2 receives prevotes from p1 and p2, and a byzantine prevote from p4
    .then("p2".receive_prevote_from("p1"))
    .then("p2".receive_prevote_from("p2"))
    .then("p2".receive_byzantine(PreVote({ src: "p4", round: 0, id: Some("v0".id()) })))

    // p2 has prevote quorum
    .expect(CSMI::s.system.get("p2").received_prevotes == Set(
      { src: "p1", round: 0, id: Some("v0".id()) },
      { src: "p2", round: 0, id: Some("v0".id()) },
      { src: "p4", round: 0, id: Some("v0".id()) },
    ))

    // And therefore sends a precommit
    .expect(CSMI::s.system.values().forall(s => s.messages.contains(
      PreCommit({ src: "p2", round: 0, id: Some("v0".id()) })
    )))

    // We already check we have two precommits in flight, let's receive them

    // p2 receives precommits from p1 and p2, and a byzantine precommit from p4
    .then("p2".receive_precommit_from("p1"))
    .then("p2".receive_precommit_from("p2"))
    .then("p2".receive_byzantine(PreCommit({ src: "p4", round: 0, id: Some("v2".id()) })))

    // p2 has precommit quorum
    .expect(CSMI::s.system.get("p2").received_precommits == Set(
      { src: "p1", round: 0, id: Some("v0".id()) },
      { src: "p2", round: 0, id: Some("v0".id()) },
      { src: "p4", round: 0, id: Some("v2".id()) },
    ))

    // so p2 starts a timeout
    .expect(CSMI::s.activeTimeouts.get("p2") == Some({ kind: PreCommitTimeout, round: 0 }))

    // and stores the valid value
    .expect(CSMI::s.system.get("p2").valid_value == Some("v0"))

    // At this point, if the timeout expires
    .then("p2".expire_timeout())
    // p2 should start a new round by sending a new proposal with the stored valid_value
    .expect(all {
      CSMI::s.system.get("p2").round == 1,
      CSMI::s.system.get("p2").stage == ProposeStage,
      CSMI::s.system.values().forall(s => s.messages.contains(
        Propose({ src: "p2", round: 1, proposal: "v0", valid_round: 0 })
      )),
    })

    // Which enables line 28 to be called by p2, as it is in propose stage and can receive
    // the new proposal with valid_round 0.
    // TODO: we might need more steps so this can also be called by different processes
    .expect(
      val current_state = CSMI::s.system.get("p2")
      val msg = CSMI::s.system.get("p2").get_proposals().filter(p => p.valid_round == 0).getOnlyElement()
      // line 28
      val result = current_state.process_proposal_and_quorum_at_propose_stage(Propose(msg))
      all {
        current_state.stage == ProposeStage,
        result != None,
        result.unwrap().state.stage == PreVoteStage,
        result.unwrap().output.contains(
          Broadcast(PreVote({ round: 1, src: "p2", id: Some("v0".id()) }))
        ),
      }
    )

  // p3 (faulty) is the first proposer
  run disagreement = CSMI::init(initialize_process, initial_bookkeeping)
    // p1 and p2 are the correct processes. Each of them receives a proposal with a different value
    .then("p1".receive_byzantine(Propose({ src: "p3", round: 0, proposal: "v0", valid_round: -1 })))
    .then("p2".receive_byzantine(Propose({ src: "p3", round: 0, proposal: "v1", valid_round: -1 })))

    // p1 and p2 will send their prevotes, but not receive messages from each other
    .then("p1".receive_prevote_from("p1"))
    .then("p2".receive_prevote_from("p2"))

    // Interesting note: adding the following breaks this test. We don't get to disagreement
    // if p1 and p2 exchange prevotes, but exchanging precommits is fine.
    // .then("p1".receive_prevote_from("p2"))
    // .then("p2".receive_prevote_from("p1"))

    // but there are also byzantine prevotes
    .then("p1".receive_byzantine(PreVote({ src: "p3", round: 0, id: Some("v0".id()) })))
    .then("p1".receive_byzantine(PreVote({ src: "p4", round: 0, id: Some("v0".id()) })))
    .then("p2".receive_byzantine(PreVote({ src: "p3", round: 0, id: Some("v1".id()) })))
    .then("p2".receive_byzantine(PreVote({ src: "p4", round: 0, id: Some("v1".id()) })))

    // p1 has prevote quorum for value v0
    .expect(Set(
      { src: "p1", round: 0, id: Some("v0".id()) },
      { src: "p3", round: 0, id: Some("v0".id()) },
      { src: "p4", round: 0, id: Some("v0".id()) },
    ).subseteq(
      CSMI::s.system.get("p1").received_prevotes
    ))

    // p2 has prevote quorum for value v1
    .expect(Set(
      { src: "p2", round: 0, id: Some("v1".id()) },
      { src: "p3", round: 0, id: Some("v1".id()) },
      { src: "p4", round: 0, id: Some("v1".id()) },
    ).subseteq(
      CSMI::s.system.get("p2").received_prevotes
    ))

    // p1 and p2 will send their precommits
    .then("p1".receive_precommit_from("p1"))
    .then("p1".receive_precommit_from("p2"))
    .then("p2".receive_precommit_from("p1"))
    .then("p2".receive_precommit_from("p2"))
    // but there are also byzantine precommits
    .then("p1".receive_byzantine(PreCommit({ src: "p3", round: 0, id: Some("v0".id()) })))
    .then("p1".receive_byzantine(PreCommit({ src: "p4", round: 0, id: Some("v0".id()) })))
    .then("p2".receive_byzantine(PreCommit({ src: "p3", round: 0, id: Some("v1".id()) })))
    .then("p2".receive_byzantine(PreCommit({ src: "p4", round: 0, id: Some("v1".id()) })))

    // p1 has precommit quorum for value v0
    .expect(Set(
      { src: "p1", round: 0, id: Some("v0".id()) },
      { src: "p3", round: 0, id: Some("v0".id()) },
      { src: "p4", round: 0, id: Some("v0".id()) },
    ).subseteq(
      CSMI::s.system.get("p1").received_precommits
    ))

    // p2 has precommit quorum for value v1
    .expect(Set(
      { src: "p2", round: 0, id: Some("v1".id()) },
      { src: "p3", round: 0, id: Some("v1".id()) },
      { src: "p4", round: 0, id: Some("v1".id()) },
    ).subseteq(
      CSMI::s.system.get("p2").received_precommits
    ))

    // So they decide and disagree
    .expect(and {
      CSMI::s.system.get("p1").decision == Some("v0"),
      CSMI::s.system.get("p2").decision == Some("v1"),
    })

    // And we can detect equivocation from p3 and p4 in the evidence
    .expect(and {
      equivocation_in("p3", CSMI::s.bookkeeping.evidence_prevote),
      equivocation_in("p3", CSMI::s.bookkeeping.evidence_precommit),
      equivocation_in("p4", CSMI::s.bookkeeping.evidence_prevote),
      equivocation_in("p4", CSMI::s.bookkeeping.evidence_precommit),
    })
}

module tendermint_tests {
  import test_base(
    F = 1,
    CORRECT = Set("p1", "p2", "p3"),
    FAULTY = Set("p4"),
    PROPOSER = Map(0 -> "p1", 1 -> "p2", 2 -> "p3", 3 -> "p4", 4 -> "p1"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v0", 3 -> "v2", 4 -> "v0"),
  ) as valid

  run line28Test = valid::line28

  import test_base(
    F = 1,
    CORRECT = Set("p1", "p2"),
    FAULTY = Set("p3", "p4"),
    PROPOSER = Map(0 -> "p3", 1 -> "p2", 2 -> "p3", 3 -> "p4", 4 -> "p1"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v0", 3 -> "v2", 4 -> "v0"),
  ) as faulty

  run disagreementTest = faulty::disagreement
}
