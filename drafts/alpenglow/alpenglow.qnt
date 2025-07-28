// -*- mode: Bluespec; -*-
/**
 * Specification of Alpenglow Consensus [1]
 *
 * [1]: https://drive.google.com/file/d/1y_7ddr8oNOknTQYHzXeeMD2ProQ0WjMs/view
 *
 * Josef Widder, Gabriela Moreira and Yassine Boukhari 
 * Informal Systems, 2025
 */

module alpenglow {
  import basicSpells.* from "lib/basicSpells"
  import statemachine(processes = Set()) as csmi from "statemachine"

  // -------------------------------------  Constants -------------------------------------------------
  /// Set of correct processes (non Byzantine)
  const correct: Set[ProcessID]
  /// Set of processes that follow the algorithm but might fail in a benign way
  const good: Set[ProcessID]
  /// Set of Byzantine processes
  const byzantine: Set[ProcessID]
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

  type TimeoutEventData = Slot // TODO not sure what timeouts they start

  type Effect =
    | ScheduleEventTimeout(TimeoutEventData) // might be multiple from one function call
    | ExcludeTimeout(TimeoutEventData)
    | Broadcast(Message)

    /// Table 4 (Alpenglow’s voting messages)
  type Message =
    | NotarVoteMsg(BlockReference)
    | NotarFallBackVoteMsg(BlockReference)
    | SkipVoteMsg(Slot)
    | SkipFallbackVoteMsg(Slot)
    | FinalVoteMsg(Slot)

  /// Messages on the network carry the sender 
  type NetworkMsg = {
    sender: ProcessID,
    msg: Message,
  }
  type LocalState = csmi::LocalState[ProcessID, State]
  type Logging = {}
  type Transition = csmi::Transition[LocalState, Effect]
  type Transitions = csmi::Transitions[Transition]
  type Environment = csmi::Environment[ProcessID, State, Message, TimeoutEventData, Logging, {}]
  type LocalContext = csmi::LocalContext[Message, TimeoutEventData, {}]

  // ------------------------------------- Data Types ------------------------------------------------
  type Slot = int

  type Block = {
    slot: Slot,
    hash: Blockhash,
    parent: Blockhash,
  }

  type BlockReference = { slot: Slot, hash: Blockhash }

  type Blockhash = int


  /// Definition 18 (Votor State)
  type SlotObject =
    | ParentReady(Blockhash)
    | Voted
    | VotedNotar(Blockhash)
    | BlockNotarized(Blockhash)
    | ItsOver
    | BadWindow
 

  type Certificate =
    | FastFinalizationCertificate(BlockReference)
    | NotarizationCertificate(BlockReference)
    | NotarFallbackCertificate(BlockReference)
    | SkipCertificate(Slot)
    | FinalizationCertificate(Slot)

  
  /// Local state of a process
  /// Fields are lists indexed by slot
  type State = {
    pendingBlocks: List[Option[Block]],
    state: List[Set[SlotObject]],
  }

  // -------------------------------------  State Machine Related Types -------------------------------------


  type Bookkeeping

  type Result = {
    output: Set[Effect],
    post: LocalState,
  }
  
  type ListenerInput = {
    msgBuffer: Set[NetworkMsg], // Messages received by the process
    internalBuffer: Set[Slot], // Timeouts for the process
    now: Slot, // Current slot
  }
  
  type ListenerOutput = Set[Result]



  
  // ----------------------------------------------  Constants and utility variables ----------------------------------------------


  /// Set of all blocks
  pure val allBlocks = correctBlocks.union(byzantineBlocks)

  /// Set of correct processes and processes that follow the algorithm but might fail in a benign way
  pure val benevolent = correct.union(good)

  pure val maxSlot = allBlocks.fold(-1, (s, x) => max(x.slot, s))

  
  // Definition of byzantine messages
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
  //
  // Constraints on the number of processes
  //

  assume uniqueRole = and {
    correct.intersect(byzantine) == Set(),
    correct.intersect(good) == Set(),
    good.intersect(byzantine) == Set(),
  }

  pure val numProcesses = correct.size() + good.size() + byzantine.size()

  // Assumption 1 and Assumption 2
  assume resilienceCondition = all {
    numProcesses > byzantine.size() * 5, // N > 5F
    numProcesses > good.size() * 5,
  }


  // ----------------------------------------------  Auxiliary Functions ----------------------------------------------

  /// Checks for thresholds, using the known number of processes
  pure def surpassesThreshold(votes, threshold) =
    votes.size() * 100 >= numProcesses * threshold

  pure def slotOf(msg: Message): Slot =
    match msg {
      | NotarVoteMsg(m) => m.slot
      | NotarFallBackVoteMsg(m) => m.slot
      | SkipVoteMsg(slot) => slot
      | SkipFallbackVoteMsg(slot) => slot
      | FinalVoteMsg(slot) => slot
    }

  pure def reference(b: Block): BlockReference = { slot: b.slot, hash: b.hash }

  pure def addObjects(ls: LocalState, slot: Slot, obj: Set[SlotObject]): LocalState =
    { ...ls, state: ls.state.replaceAt(slot, ls.state[slot].union(obj)) }

  pure def setPendingBlock(ls: LocalState, slot: Slot, b: Option[Block]): LocalState =
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

    aggregatedVotes.surpassesThreshold(threshold)
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

  pure def setTimeouts(ls: LocalState, slot: Slot): Result =
    { post: ls,
      output: windowSlots(slot).map(i => (ScheduleEventTimeout(i))) }

  /// Check if a notarization vote can be cast
  pure def tryNotar(ls: LocalState, b: Block): { result: Result, success: bool } =
    if (ls.state[b.slot].contains(Voted))
      { result: { post: ls, output: Set() }, success: false }
    else
      val firstSlot = firstSlotInLeaderWindow(b.slot)
      if ((firstSlot and ParentReady(b.parent).in(ls.state[b.slot]))
        or (not(firstSlot) and VotedNotar(b.parent).in(ls.state[b.slot - 1])))
        // Warning: parentheses not matching in paper

        // Notarization vote
        val out = Set(Broadcast(NotarVoteMsg({ slot:b.slot, hash: b.hash })))
        val s2 = ls
          .addObjects(b.slot, Set(Voted, VotedNotar(b.hash)))
          // Won't vote notar a second time
          .setPendingBlock(b.slot, None)

        // Maybe vote finalize as well
        val tf = tryFinal(s2, b.slot, b.hash)

        { result: { post: tf.post, output: out.union(tf.output) }, success: true }
      else
        { result: { post: ls, output: Set() }, success: false }

  pure def tryFinal(ls: LocalState, slot: Slot, hash: Blockhash): Result =
    if (BlockNotarized(hash).in(ls.state[slot]) and VotedNotar(hash).in(ls.state[slot])
        and not(BadWindow.in(ls.state[slot])))
      // Finalization vote
      { output: Set(Broadcast(FinalVoteMsg(slot))), post: ls.addObjects(slot, Set(ItsOver)) }
    else
      { output: Set(), post: ls }

  pure def trySkipWindow(ls: LocalState, slot: Slot): Result =
    // Skip unvoted slots
    windowSlots(slot).fold({ output: Set(), post: ls }, (s, k) => {
      if (not(Voted.in(s.post.state[k])))
        // Skip vote
        val update = Set(Broadcast(SkipVoteMsg(k)))
        val s2 = s.post
          .addObjects(k, Set(Voted, BadWindow))
          // Won't vote notar after skip
          .setPendingBlock(k, None)

        { output: s.output.union(update), post: s2 }
      else
        s
    })

  pure def checkPendingBlocks(ls: LocalState): Result =
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

  pure def parentReadyCondition(slot: Slot, hash: Blockhash, msgs: Set[NetworkMsg]): bool = all {
    firstSlotInLeaderWindow(slot),
    0.to(slot - 1).exists(s =>
      val b = { slot: s, hash: hash }
      and {
        or {
          isCertified(NotarizationCertificate(b), msgs),
          isCertified(NotarFallbackCertificate(b), msgs)
        },
        b.slot.to(slot).subseteq(slotsSkipCertified(msgs))
      }
    )
  }
  
  pure def votedToSkip(s: Slot, msgs: Set[NetworkMsg]): Set[ProcessID] =
    msgs.filter(m =>  m.msg == SkipVoteMsg(s)).map(m => m.sender)

  // Warning: vote doesn't contain parent. Assumption about parent hashed in hash?
  pure def votedToNotar(b: BlockReference, msgs: Set[NetworkMsg]): Set[ProcessID] =
    msgs.filter(m => m.msg == NotarVoteMsg(b)).map(m => m.sender)

  
  def safeToNotarCondition(v: ProcessID, msgs: Set[NetworkMsg], now: Slot, b: Block): bool = all {
    // Consider block b in slot s = slot(b).
    b.slot == now,

    val voted = msgs.filter(m => m.sender == v and now == slotOf(m.msg))
    val notarVoted =
      voted.filter(m => match m.msg {
        | NotarVoteMsg(m) => true
        | _ => false
      })

    and {
      voted.size() > 0,
      notarVoted.size() == 0,
    },
    val notar = votedToNotar(b.reference(), msgs)
    val skip = votedToSkip(now, msgs)
    // notar(b) ≥ 40% or (skip(s) + notar(b) ≥ 60% and notar(b) ≥ 20%).
    // Question: is (+) here the sum of the sizes or the size of the union?
    or {
      surpassesThreshold(notar, 40),
      and {
        surpassesThreshold(skip.union(notar), 60),
        surpassesThreshold(notar, 20)
      }
    }
  }

  def safeToSkipCondition(v: ProcessID,  allMessages: Set[NetworkMsg], now: Slot): bool = all {
    // node voted in slot s already, but not to skip s.
    allMessages.exists(m =>
      m.sender == v
      and slotOf(m.msg) == now
      and m.msg != SkipVoteMsg(now)
    ),

    // Moreover:
    // skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.
    val blocksWithNotarVotes =
      allMessages
        .filter(m => slotOf(m.msg) == now)
        .fold(Set(), (s, m) => match m.msg {
          | NotarVoteMsg(n) => s.setAdd(n)
          | _ => s
        })

    // Σ_b notar(b)
    val allNotarVotes = blocksWithNotarVotes.map(b =>
      votedToNotar(b, allMessages)
    ).flatten()

    // max_b
    val blockWithMostVotes = blocksWithNotarVotes.fold({ slot: -1, hash: -1 }, (res, x) => {
      if (votedToNotar(x, allMessages).size() > votedToNotar(res, allMessages).size())
        x
      else
        res
    })

    // skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.
    // Question: is (+) here the sum of the sizes or the size of the union?
    // same for (-)

    // skip(s)
    votedToSkip(now, allMessages)
      // + Σ_b notar(b)
      .union(allNotarVotes)
      // - max_b notar(b)
      .exclude(votedToNotar(blockWithMostVotes, allMessages))
      // ≥ 40%.
      .surpassesThreshold(40)
  }

//----------------------------------------------------- Event Listeners -----------------------------------------------------

  /// Emit Block and process it
  /// Warning: The pseudo code uses s. Does this mean s is checked against the local
  /// view of the slot, and thus only "current" blocks can be received, or could BlockInput(block)
  /// could also be executed for blocks from future slots?
  /// This question applies to all "upon"s
  pure def blockReceived(
    ls: LocalState,
    input: ListenerInput
  ): ListenerOutput =
    
    val now = input.now
    val candidates = allBlocks.filter(b => b.slot == now)
    
    val results = candidates.map(b => {
        // If the block is not in the pending blocks, we add it
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
          { output: tn.result.output, post: tn.result.post } // Warning: The state might have changed
    })
    results 
      
  pure def timeout(
    ls: LocalState,
    input: ListenerInput
  ): ListenerOutput =
    val slot = input.now
    val timeouts = input.internalBuffer

    val condition = timeouts.contains(slot)
    if (not(condition))
      // No change state, no messages sent
      Set({ output: Set(), post: ls })
    else
      // If the timeout is set, we try to skip the window
      // We assume that the timeout is set for the current slot
      val candidate =  if (Voted.in(ls.state[slot]))
          trySkipWindow(ls, slot)
        else
          // No change state, no messages sent
          {output: Set(), post: ls }
      Set(candidate)


  /// Emit BlockNotarized and process it. The structure of this actions is that we first
  /// build a set of data (blocks or slot numbers) for which a certain event is enabled,
  /// and then we pick one non-deterministically, process it, and updated the global state.
  pure def blockNotarized(
    ls: LocalState,
    input: ListenerInput
  ): ListenerOutput =
    val msgs = input.msgBuffer
    val candidates = allBlocks.map(b => {slot: input.now, hash: b.hash})
              .filter(nc => isCertified(NotarizationCertificate(nc),msgs))
    candidates.map(sh => {
          val s1 = ls.addObjects(sh.slot, Set(BlockNotarized(sh.hash)))
          tryFinal(s1, sh.slot, sh.hash)
      }
    )


  // • ParentReady(s, hash(b)): Slot s is the first of its leader window, and Pool
  // holds a notarization or notar-fallback certificate for a previous block b,
  // and skip certificates for every slot s′ since b, i.e., for slot(b) < s′ < s.
  // Warning "notarization or notar-fallback": notar-fallback seems to imply notar
  // Warning: Previous block? Block for previous slot
  /// Emit ParentReady and process it
  pure def parentReady(
    ls: LocalState,
    input: ListenerInput
  ): ListenerOutput =
    val msgs = input.msgBuffer
    val now = input.now
    val candidates = allBlocks.filter(b => parentReadyCondition(now, b.hash, msgs))

    candidates.map(sh => {
        val s1 = ls.addObjects(sh.slot, Set(ParentReady(sh.hash)))
        val s2 = checkPendingBlocks(s1)
        // Start time for all slots in this window
        val s3 = setTimeouts(s2.post, sh.slot)
        { output: s2.output.union(s3.output), post: s2.post }
      }
    )


  /// Definition 16 (fallback events)
  // Emit SafeToNotar and process it
  pure def safeToNotar(
    ls: LocalState,
    input: ListenerInput
  ): ListenerOutput =
    val msgs = input.msgBuffer
    val now = input.now
    val candidates = allBlocks.filter(b => safeToNotarCondition(ls.pid, msgs, now, b))
                        .map(b => {slot: b.slot, hash: b.hash})
    candidates.map(sh => {
        val s1 = trySkipWindow(ls, sh.slot)
        if (not(ItsOver.in(s1.post.state[sh.slot])))
          // Notar-fallback vote
          val output = s1.output.union(Set(Broadcast(NotarFallBackVoteMsg(sh))))
          { output: output, post: s1.post.addObjects(sh.slot, Set(BadWindow)) }
        else
          s1
      }
    )
  
  // Emit SafeToSkip and process it
  pure def safeToSkip(
    ls: LocalState,
    input: ListenerInput
  ): ListenerOutput =
    val slot = input.now
    val msgs = input.msgBuffer
    val condition = safeToSkipCondition(ls.pid, msgs, slot)
    if (not(condition))
      Set()
    else
      val candidate = {
          val s1 = trySkipWindow(ls, slot)
          if (not(ItsOver.in(s1.post.state[slot])))
            // Skip-fallback vote
            val output = s1.output.union(Set(Broadcast(SkipFallbackVoteMsg(slot))))
            { output: output, post: addObjects(s1.post, slot, Set(BadWindow)) }
          else
            s1
        }
      Set(candidate)


  pure def listener(ls: LocalState, input: ListenerInput): ListenerOutput = 
    val res = Set(
      blockReceived(ls, input),
      timeout(ls, input),
      blockNotarized(ls, input),
      parentReady(ls, input),
      safeToNotar(ls, input),
      safeToSkip(ls, input)
    ).flatten().filter(out => out.output.size() > 0 or out.post != ls) // Flatten the set of sets into a single set of results
    res

}
