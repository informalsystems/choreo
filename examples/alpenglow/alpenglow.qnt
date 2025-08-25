// -*- mode: Bluespec; -*-
/**
 * Specification of Alpenglow Consensus [1]
 *
 * [1]: https://drive.google.com/file/d/1y_7ddr8oNOknTQYHzXeeMD2ProQ0WjMs/view
 *
 * Josef Widder, Gabriela Moreira
 * Informal Systems, 2025
 */

module alpenglow {
  import basicSpells.* from "../../spells/basicSpells"
  import choreo(processes = correct.union(good)) as choreo from "../../choreo"

  // -------------------------------------  Constants -------------------------------------------------
  /// Set of correct processes (non Byzantine)
  const correct: Set[ProcessID]
  /// Set of processes that follow the algorithm but might fail in a benign way
  const good: Set[ProcessID]
  /// Set of Byzantine processes
  const byzantine: Set[ProcessID]
  /// Voting power of the processes
  const power: ProcessID -> int
  /// Set of blocks
  const correctBlocks: Set[Block]
  /// Set of Byzantine blocks
  const byzantineBlocks: Set[Block]
  /// Slots for which this model considers votes
  const aliveSlots: Set[Slot]
  /// Hashes for which this model considers votes
  const aliveHashes: Set[Blockhash]
  
  //---------------------------------------------------------------------------------------------------

  type ProcessID = str
  //
  // Wiring into the reusable consensus state machine interface
  //
  
  type TimeoutEvent = Slot
  
  type CustomEffects = 
    | ScheduleEventTimeout(TimeoutEvent)
    | ExcludeTimeout(TimeoutEvent)

  type Slot = int

  type Block = {
    slot: Slot,
    hash: Blockhash,
    parent: Blockhash,
  }

  type BlockReference = { slot: Slot, hash: Blockhash }

  type Blockhash = int

  /// Fields are lists indexed by slot
  type State = {
    pendingBlocks: List[Option[Block]],
    state: List[Set[SlotObject]],
  }

  /// Definition 18 (Votor State)
  type SlotObject =
    | ParentReady(Blockhash)
    | Voted
    | VotedNotar(Blockhash)
    | BlockNotarized(Blockhash)
    | ItsOver
    | BadWindow

  type ConsensusInput =
    | BlockInput(Block)
    | TimeOutInput(Slot)
    | BlockNotarizedInput(BlockReference)
    | ParentReadyInput(BlockReference)
    | SafeToNotarInput(BlockReference)
    | SafeToSkipInput(Slot)

  /// Table 4 (Alpenglow’s voting messages)
  type Message =
    | NotarVoteMsg(BlockReference)
    | NotarFallBackVoteMsg(BlockReference)
    | SkipVoteMsg(Slot)
    | SkipFallbackVoteMsg(Slot)
    | FinalVoteMsg(Slot)

  /// Messages on the network carry the sender (the broadcast call in the pseudo code
  /// doesn't carry the sender, so does our encoding of the consensus main loop)
  type NetworkMsg = {
    sender: ProcessID,
    msg: Message,
  }
  type Extensions = {}

  /* Boilerplate */
  type LocalState = choreo::LocalState[ProcessID, State]
  type LocalContext = choreo::LocalContext[ProcessID, State, Message, TimeoutEvent, Extensions]
  type Transition = choreo::Transition[ProcessID, State, Message, TimeoutEvent, CustomEffects]
  type GlobalContext = choreo::GlobalContext[
    ProcessID,
    State,
    Message,
    TimeoutEvent,
    Extensions
  ]
  /* End of boilerplate */

  type Certificate =
    | FastFinalizationCertificate(BlockReference)
    | NotarizationCertificate(BlockReference)
    | NotarFallbackCertificate(BlockReference)
    | SkipCertificate(Slot)
    | FinalizationCertificate(Slot)

  type Bookkeeping

  type Result = {
    output: Set[choreo::Effect[ProcessID, Message, TimeoutEvent, CustomEffects]],
    post: State,
  }

  /// Set of all blocks
  pure val allBlocks = correctBlocks.union(byzantineBlocks)

  /// Set of correct processes and processes that follow the algorithm but might fail in a benign way
  pure val benevolent = correct.union(good)

  pure val maxSlot = allBlocks.fold(-1, (s, x) => max(x.slot, s))

  //
  // Constraints on the number of processes
  //

  assume uniqueRole = and {
    correct.intersect(byzantine) == Set(),
    correct.intersect(good) == Set(),
    good.intersect(byzantine) == Set(),
  }

  pure def voting_power(s: Set[ProcessID]): int =
    s.fold(0, (s, x) => s + power.get(x))

  pure val totalVotingPower = correct.union(good).union(byzantine).voting_power()

  // Assumption 1 and Assumption 2
  assume resilienceCondition = all {
    totalVotingPower > byzantine.voting_power() * 5, // N > 5F
    totalVotingPower > good.voting_power() * 5, // Less than a fifth is not Byzantine but may be silent
  }

  /// Checks for thresholds, using the known total voting power
  pure def surpassesThreshold(votes, threshold) =
    votes.voting_power() * 100 >= totalVotingPower * threshold

  /// All votes that can be sent by the Byzantine processes (without senders)
  pure val byzMessages = tuples(aliveSlots, aliveHashes).map(((slot, hash)) =>
    Set(
      NotarVoteMsg({ slot: slot, hash: hash }),
      NotarFallBackVoteMsg({ slot: slot, hash: hash }),
      SkipVoteMsg(slot),
      SkipFallbackVoteMsg(slot),
      FinalVoteMsg(slot)
    )
  ).flatten()

  /// All votes that can be sent by the Byzantine processes
  pure val byzNetworkMsgs = tuples(byzantine, byzMessages).map(((sender, msg)) =>
    { sender: sender, msg: msg }
  )

  // Auxiliary functions

  pure def slotOf(msg: Message): Slot =
    match msg {
      | NotarVoteMsg(m) => m.slot
      | NotarFallBackVoteMsg(m) => m.slot
      | SkipVoteMsg(slot) => slot
      | SkipFallbackVoteMsg(slot) => slot
      | FinalVoteMsg(slot) => slot
    }

  pure def reference(b: Block): BlockReference = { slot: b.slot, hash: b.hash }

  pure def addObjects(ls: State, slot: Slot, obj: Set[SlotObject]): State =
    { ...ls, state: ls.state.replaceAt(slot, ls.state[slot].union(obj)) }

  pure def setPendingBlock(ls: State, slot: Slot, b: Option[Block]): State =
    { ...ls, pendingBlocks: ls.pendingBlocks.replaceAt(slot, b) }

  /// line 10 of TryNotar. TODO: Is there more to it?
  pure def firstSlotInLeaderWindow(slot: Slot): bool =
    slot % 4 == 0 // TODO implement

  pure def notarizedBlocks(msgs: Set[NetworkMsg]): Set[BlockReference] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | NotarVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(b => isCertified(NotarizationCertificate(b), msgs))

  pure def notarFallbackBlocks(msgs: Set[NetworkMsg]): Set[BlockReference] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | NotarVoteMsg(m) => s.union(Set(m))
        | NotarFallBackVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(b => isCertified(NotarFallbackCertificate(b), msgs))

  pure def slotsSkipCertified(msgs: Set[NetworkMsg]): Set[Slot] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | SkipVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(s => isCertified(SkipCertificate(s), msgs))

  // Definition 5 (ancestor and descendant). An ancestor of a block b is any
  // block that can be reached from b by the parent links, i.e., b, b’s parent,
  // b’s parent’s parent, and so on. If b′ is an ancestor of b, b is a
  // descendant of b′ . Note that b is its own ancestor and descendant.
  pure def isDescendant(a: Block, b: Block): bool = {
    // TODO: this can have better performance if we can make assumptions about slots
    // Filter by minimal slot
    // The slot of the parent will always be smaller then that of the child
    // but its not in increments of 1 like in mysticeti
    pure val bAncestors = (b.slot.to(a.slot)).fold(Set(b.hash), (path, s) =>
      pure val potentialAncestors = allBlocks.filter(block => block.slot == s)
      pure val ancestors = potentialAncestors.filter(ancestor =>
        path.exists(h => ancestor.parent == h)
      )
      path.union(ancestors.map(block => block.hash))
    )

    bAncestors.contains(a.hash)
  }

  // Definition 13 (certificates)
  // They are defined over a set of messages. Currently we evaluate this over the
  // message soup. But they can be also used over locally received messages if such
  // a semantics is needed.

  /// Table 5: Apenglow's certificate messages.
  pure def isCertified(cert: Certificate, msgs: Set[NetworkMsg]): bool = {
    pure val aggregatedVotes = msgs.filter(m => {
      match cert {
        | FastFinalizationCertificate(b) =>
          m.msg == NotarVoteMsg(b)
        | NotarizationCertificate(b) =>
          m.msg == NotarVoteMsg(b)
        | NotarFallbackCertificate(b) =>
          m.msg == NotarVoteMsg(b) or m.msg == NotarFallBackVoteMsg(b)
        | SkipCertificate(s) =>
          m.msg == SkipVoteMsg(s) or m.msg == SkipFallbackVoteMsg(s)
        | FinalizationCertificate(s) =>
          m.msg == FinalVoteMsg(s)
      }
    })

    pure val threshold = match cert {
      | FastFinalizationCertificate => 80
      | NotarizationCertificate => 60
      | NotarFallbackCertificate => 60
      | SkipCertificate => 60
      | FinalizationCertificate => 60
    }

    aggregatedVotes.map(x => x.sender).surpassesThreshold(threshold)
  }

  // Definition 14 (finalization). We have two ways to finalize a block:
  // Warning: definitions uses "unique" perhaps unclear in case of more faults

  /// If a finalization certificate on slot s is in Pool, the unique notarized block
  /// in slot s is finalized (we call this slow-finalized).
  pure def finalized(slot: Slot, msgs: Set[NetworkMsg]): Set[Blockhash] =
    allBlocks.map(b => b.reference())
      .filter(b => b.slot == slot)
      .filter(b => {
        isCertified(FinalizationCertificate(b.slot), msgs)
          and isCertified(NotarizationCertificate(b), msgs)
      })
      .map(b => b.hash)

  /// If a fast-finalization certificate on block b is in Pool, the block b is
  /// finalized (fast-finalized).
  pure def fastFinalized(slot: Slot, msgs: Set[NetworkMsg]): Set[Blockhash] =
    allBlocks.map(b => b.reference())
      .filter(b => b.slot == slot)
      .filter(b => isCertified(FastFinalizationCertificate(b), msgs))
      .map(b => b.hash)

  // Algorithm 2

  pure def windowSlots(slot: Slot): Set[Slot] =
    // TODO: Not sure this makes any sense
    if (slot % 4 == 0)
      Set(slot, slot + 1, slot + 2, slot + 3)
    else if (slot % 4 == 1)
      Set(slot - 1, slot, slot + 1, slot + 2)
    else if (slot % 4 == 2)
      Set(slot - 2, slot - 1, slot, slot + 1)
    else
      Set(slot - 3, slot - 2, slot - 1, slot)

  pure def setTimeouts(ls: State, slot: Slot): Result =
    { post: ls,
      output: windowSlots(slot).map(i => (choreo::CustomEffect(ScheduleEventTimeout(i)))) }

  /// Check if a notarization vote can be cast
  pure def tryNotar(ls: State, b: Block): { result: Result, success: bool } =
    if (ls.state[b.slot].contains(Voted))
      { result: { post: ls, output: Set() }, success: false }
    else
      val firstSlot = firstSlotInLeaderWindow(b.slot)
      if ((firstSlot and ParentReady(b.parent).in(ls.state[b.slot]))
        or (not(firstSlot) and VotedNotar(b.parent).in(ls.state[b.slot - 1])))

        // Notarization vote
        val out = Set(choreo::Broadcast(NotarVoteMsg({ slot:b.slot, hash: b.hash })))
        val s2 = ls
          .addObjects(b.slot, Set(Voted, VotedNotar(b.hash)))
          // Won't vote notar a second time
          .setPendingBlock(b.slot, None)

        // Maybe vote finalize as well
        val tf = tryFinal(s2, b.slot, b.hash)

        { result: { post: tf.post, output: out.union(tf.output) }, success: true }
      else
        { result: { post: ls, output: Set() }, success: false }

  pure def tryFinal(ls: State, slot: Slot, hash: Blockhash): Result =
    if (BlockNotarized(hash).in(ls.state[slot]) and VotedNotar(hash).in(ls.state[slot])
        and not(BadWindow.in(ls.state[slot])))
      // Finalization vote
      { output: Set(choreo::Broadcast(FinalVoteMsg(slot))), post: ls.addObjects(slot, Set(ItsOver)) }
    else
      { output: Set(), post: ls }

  pure def trySkipWindow(ls: State, slot: Slot): Result =
    // Skip unvoted slots
    windowSlots(slot).fold({ output: Set(), post: ls }, (s, k) => {
      if (not(Voted.in(s.post.state[k])))
        // Skip vote
        val update = Set(choreo::Broadcast(SkipVoteMsg(k)))
        val s2 = s.post
          .addObjects(k, Set(Voted, BadWindow))
          // Won't vote notar after skip
          .setPendingBlock(k, None)

        { output: s.output.union(update), post: s2 }
      else
        s
    })

  pure def checkPendingBlocks(ls: State): Result =
    // Iterate with increasing slot
    // (left to right)
    ls.pendingBlocks.foldl({ output: Set(), post: ls }, (res, pendingBlock) =>
      match pendingBlock {
        | Some(b) =>
          val tn = tryNotar(res.post, b)
          { output: res.output.union(tn.result.output), post: tn.result.post } // TODO implement
        | None =>
          res
      }
    )


  /// Algorithm 1: each upon corresponds to one consensus input
  pure def consensus(ls: State, input: ConsensusInput): Result =
    match input {
      | BlockInput(b) =>
        val tn = tryNotar(ls, b) // looks like a function but has two side effects: changes state and broadcasts
        if (tn.success)
          val cpb = checkPendingBlocks(tn.result.post)
          // as tryNotar changed the local state, we pass it to checkPendingBlocks
          { post: cpb.post, output: cpb.output.union(tn.result.output) }
          // both, tryNotar and checkPendingBlocks have side effects of sending messages. Thus we build the union here.
        else if (not(Voted.in(tn.result.post.state[b.slot])))
          { output: tn.result.output, post: tn.result.post.setPendingBlock(b.slot, Some(b)) }
        else
          // Even if all if conditions evaluate to false, tryNotar may have side effects and may change the local state
          { output: tn.result.output, post: tn.result.post } // The state might have changed although all if conditions evaluate to false

      | TimeOutInput(slot) =>
        if (not(Voted.in(ls.state[slot])))
          trySkipWindow(ls, slot)
        else
          // No change state, no messages sent
          { output: Set(), post: ls }

      | BlockNotarizedInput(sh) =>
        val s1 = ls.addObjects(sh.slot, Set(BlockNotarized(sh.hash)))
        tryFinal(s1, sh.slot, sh.hash)

      | ParentReadyInput(sh) =>
        val s1 = ls.addObjects(sh.slot, Set(ParentReady(sh.hash)))
        val s2 = checkPendingBlocks(s1)
        // Start time for all slots in this window
        val s3 = setTimeouts(s2.post, sh.slot)
        { output: s2.output.union(s3.output), post: s3.post } // TODO

      | SafeToNotarInput(sh) =>
        val s1 = trySkipWindow(ls, sh.slot)
        if (not(ItsOver.in(s1.post.state[sh.slot])))
          // Notar-fallback vote
          val output = s1.output.union(Set(choreo::Broadcast(NotarFallBackVoteMsg(sh))))
          { output: output, post: s1.post.addObjects(sh.slot, Set(BadWindow)) }
        else
          s1

      | SafeToSkipInput(slot) =>
        val s1 = trySkipWindow(ls, slot)
        if (not(ItsOver.in(s1.post.state[slot])))
          // Skip-fallback vote
          val output = s1.output.union(Set(choreo::Broadcast(SkipFallbackVoteMsg(slot))))
          { output: output, post: addObjects(s1.post, slot, Set(BadWindow)) }
        else
          s1
    }
}
