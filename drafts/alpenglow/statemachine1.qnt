// -*- mode: Bluespec; -*-

module consensus {
  import basicSpells.* from "./basicSpells"
  import alpenglow.* from "./alpenglow"

  
  /// This is all the information of the global state
  type Environment = {
    // The local state of each process
    system: ProcessID -> LocalState,
    // Global time, we can push to different views of slots later
    now: Slot,
    // Messages sent so far, a.k.a. the message soup
    msgBuffer: ProcessID -> Set[NetworkMsg],
    // Started timeouts per process
    internalBuffer: ProcessID -> Set[TimeoutEventData],
  }

  /// Interface consensus algorithm / state machine: how consensus algorithm effects the environment
  pure def applyEffect(env: Environment, v: ProcessID, res: Result): Environment =
    val new = { ... env, system: env.system.set(v, res.post) } // update the state of the process
    res.output.fold(new, (s, o) =>
      match o {
        | Broadcast(msg) =>
          val nm = { sender: v, msg: msg }
          { ...s, msgBuffer: s.msgBuffer.transformValues(m => m.union(Set(nm)))}
        | ScheduleEventTimeout(slot) =>
          { ...s, internalBuffer: s.internalBuffer.set(v, s.internalBuffer.get(v).union(Set(slot))) }
        | ExcludeTimeout(slot) =>
          { ...s, internalBuffer: s.internalBuffer.set(v, s.internalBuffer.get(v).exclude(Set(slot))) }
  })

  action listenerA(ls: LocalState, input: ListenerInput):bool = all {
    any {
      {
        val transitions = blockReceived(ls, input).filter(out => out.output.size()>0 or out.post != ls)
        all {
          transitions.size() > 0,
          nondet transition = oneOf(transitions)
          s' = applyEffect(s, ls.pid, transition),
        }
      },
      {
        val transitions = timeout(ls, input).filter(out => out.output.size()>0 or out.post != ls)
        all {
          transitions.size() > 0,
          nondet transition = oneOf(transitions)
          s' = applyEffect(s, ls.pid, transition),
        }
      },
      {
        val transitions = blockNotarized(ls, input).filter(out => out.output.size()>0 or out.post != ls)
        all {
          transitions.size() > 0,
          nondet transition = oneOf(transitions)
          s' = applyEffect(s, ls.pid, transition),
        }
      },
      {
        val transitions = parentReady(ls, input).filter(out => out.output.size()>0 or out.post != ls)
        all {
          transitions.size() > 0,
          nondet transition = oneOf(transitions)
          s' = applyEffect(s, ls.pid, transition),
        }
      },
      {
        val transitions = safeToNotar(ls, input).filter(out => out.output.size()>0 or out.post != ls)
        all {
          transitions.size() > 0,
          nondet transition = oneOf(transitions)
          s' = applyEffect(s, ls.pid, transition),
        }
      },
      {
        val transitions = safeToSkip(ls, input).filter(out => out.output.size()>0 or out.post != ls)
        all {
          transitions.size() > 0,
          nondet transition = oneOf(transitions)
          s' = applyEffect(s, ls.pid, transition),
        }
      },           
    }
  }


  //
  //
  // State Machine
  //
  //
  var s: Environment
  var counter: int
  val allMessages = s.msgBuffer.values().flatten().
                    union(byzNetworkMsgs) // all messages sent so far 



  action init = all {
    counter' = 0,
    s' = {
      system: benevolent.mapBy(p => {
        state: [
          Set(ParentReady(-1)),
          Set(),
          Set(),
          Set(),
          Set(),
        ],
        pendingBlocks: [None, None, None, None, None],
        pid: p,
      }),
      now: 0,
      msgBuffer: benevolent.mapBy(v => Set()),
      internalBuffer: benevolent.mapBy(v => Set()),
    }
  }



  /// increment the global time (slot number)
  action tick = all {
    s.now < maxSlot, // make sure we don't enter a slot for which we don't have a block in the model
    s' = { ... s, now: s.now + 1 }
  }

  /// Main step action. Includes all behavior
  action step = all {
    counter < 10,
    counter' = counter + 1,
    any {
      nondet v = oneOf(benevolent)
      val input = {
        msgBuffer: s.msgBuffer.get(v).union(byzNetworkMsgs),
        internalBuffer: s.internalBuffer.get(v),
        now: s.now,
      }
      val ls = s.system.get(v)
      val transitions = listener(ls, input)
      all {
      transitions.size() > 0, // we have a transition to apply
      nondet transition = oneOf(transitions)
      s' = applyEffect(s, v, transition),
      },
      tick,
    }
  }
  /// Main step action. Includes all behavior
  action stepA = all {
    counter < 10,
    counter' = counter + 1,
    any {
      nondet v = oneOf(benevolent)
      val input = {
        msgBuffer: s.msgBuffer.get(v).union(byzNetworkMsgs),
        internalBuffer: s.internalBuffer.get(v),
        now: s.now,
      }
      val ls = s.system.get(v)
      listenerA(ls, input),
      tick,
    }
  }

/// Witness to find a run where a block is fast finalized
  val fastFinalizedWitness =
    allBlocks.forall(b => not(isCertified(FastFinalizationCertificate(b.reference()), allMessages)))
  val timeoutWitness = 
     s.internalBuffer.values().forall(v => v == Set())
}

module some_byz {
  // For a trace where a value is fast finalized call
  // quint run statemachine.qnt --main some_byz --invariant fastFinalizedWitness

  import consensus(
    correct = Set("v1", "v2", "v3", "v4", "v5"),
    good = Set(),
    byzantine = Set("b1"),
    correctBlocks = Set(
      { slot: 0, hash: 42, parent: -1 },
      { slot: 1, hash: 43, parent: 42 },
      { slot: 2, hash: 44, parent: 43 },
    ),
    byzantineBlocks = Set(
      { slot: 1, hash: 46, parent: 42 },
      { slot: 1, hash: 47, parent: 45 },
      { slot: 2, hash: 48, parent: 43 },
      { slot: 2, hash: 49, parent: 45 },
    ),
    aliveSlots = 0.to(2),
    aliveHashes = 42.to(49),
  ).*
}

module too_many_byz_1 {
  // to violate agreement, run
  // quint run statemachine.qnt --main too_many_byz_1 --step oneSlotNoTimeout  --invariant agreement

  import consensus(
    correct = Set("v1", "v2", "v3", "v4"),
    good = Set(),
    byzantine = Set("b1"),
    correctBlocks = Set(
      { slot: 0, hash: 42, parent: -1 },
      { slot: 1, hash: 43, parent: 42 },
      { slot: 2, hash: 44, parent: 43 },
    ),
    byzantineBlocks = Set(
      { slot: 0, hash: 45, parent: -1 },
      { slot: 1, hash: 46, parent: 42 },
      { slot: 1, hash: 47, parent: 45 },
      { slot: 2, hash: 48, parent: 43 },
      { slot: 2, hash: 49, parent: 45 },
    ),
    aliveSlots = 0.to(2),
    aliveHashes = 42.to(49),
  ).*
}

module too_many_byz {
  // to violate agreement, run
  // quint run statemachine.qnt --main too_many_byz --step oneSlotNoTimeout --invariant agreement

  import consensus(
    correct = Set("v1", "v2", "v3", "v4"),
    good = Set(),
    byzantine = Set("b1", "b2"),
    correctBlocks = Set({ slot: 0, hash: 42, parent: -1 }),
    byzantineBlocks = Set({ slot: 0, hash: 41, parent: -1 }),
    aliveSlots = Set(0),
    aliveHashes = 41.to(42),
  ).*
}
