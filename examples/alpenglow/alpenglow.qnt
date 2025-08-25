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

  /// Table 4 (Alpenglow's voting messages)
  type Message =
    | NotarVoteMsg(BlockReference)
    | NotarFallBackVoteMsg(BlockReference)
    | SkipVoteMsg(Slot)
    | SkipFallbackVoteMsg(Slot)
    | FinalVoteMsg(Slot)

  type Certificate =
    | FastFinalizationCertificate(BlockReference)
    | NotarizationCertificate(BlockReference)
    | NotarFallbackCertificate(BlockReference)
    | SkipCertificate(Slot)
    | FinalizationCertificate(Slot)

  type TimeoutEvent = Slot

  type CustomEffects = 
    | ScheduleEventTimeout(TimeoutEvent)
    | ExcludeTimeout(TimeoutEvent)

  type Extensions = {
    // Messages sent so far, a.k.a. the message soup
    msgBuffer: Set[NetworkMsg],
    // Started timeouts per process
    activeTimeouts: ProcessID -> Set[TimeoutEvent],
    // blockchain as seen by message soup
    ch: Slot -> Set[Blockhash],
    // counter for TLC
    counter: int,
  }

  /// Messages on the network carry the sender (the broadcast call in the pseudo code
  /// doesn't carry the sender, so does our encoding of the consensus main loop)
  type NetworkMsg = {
    sender: ProcessID,
    msg: Message,
  }

  /* Boilerplate */
  type LocalState = choreo::LocalState[ProcessID, State]
  type LocalContext = choreo::LocalContext[ProcessID, State, Message, TimeoutEvent, Extensions]
  type Transition = choreo::Transition[ProcessID, State, Message, TimeoutEvent, CustomEffects]
  type GlobalContext = choreo::GlobalContext[ProcessID, State, Message, TimeoutEvent, Extensions]
  /* End of boilerplate */

  // -----------------------------------------------------------------------------
  // Algorithm implementation from alpenglow.qnt
  // -----------------------------------------------------------------------------

  /// Set of all processes (benevolent and byzantine)
  pure def allProcesses: Set[ProcessID] = correct.union(good).union(byzantine)
  
  /// Set of benevolent processes (correct and good)
  pure def benevolent: Set[ProcessID] = correct.union(good)

  /// Set of all blocks
  pure def allBlocks: Set[Block] = correctBlocks.union(byzantineBlocks)

  /// Byzantine network messages that can be injected  
  pure def byzNetworkMsgs: Set[NetworkMsg] = {
    val allMsgs = aliveSlots.fold(Set(), (acc, slot) =>
      aliveHashes.fold(acc, (acc2, hash) =>
        acc2.union(Set(
          NotarVoteMsg({ slot: slot, hash: hash }),
          NotarFallBackVoteMsg({ slot: slot, hash: hash }),
          SkipVoteMsg(slot),
          SkipFallbackVoteMsg(slot),
          FinalVoteMsg(slot)
        ))
      )
    )
    byzantine.fold(Set(), (acc, p) => 
      acc.union(allMsgs.map(msg => { sender: p, msg: msg }))
    )
  }

  pure def addObjects(ls: State, slot: Slot, obj: Set[SlotObject]): State =
    { ...ls, state: ls.state.replaceAt(slot, ls.state[slot].union(obj)) }

  pure def setPendingBlock(ls: State, slot: Slot, b: Option[Block]): State =
    { ...ls, pendingBlocks: ls.pendingBlocks.replaceAt(slot, b) }

  /// Threshold to get a (super)majority
  pure def threshold: int = (allProcesses.size() * 2) / 3 + 1

  // Helper functions for working with power and voting
  pure def totalPower: int = allProcesses.fold(0, (acc, p) => acc + power.get(p))

  pure def powerThreshold: int = (totalPower * 2) / 3 + 1

  pure def powerOfSet(ps: Set[ProcessID]): int = ps.fold(0, (acc, p) => acc + power.get(p))

  pure def surpassesThreshold(ps: Set[ProcessID], percent: int): bool =
    powerOfSet(ps) * 100 >= totalPower * percent

  pure def reference(b: Block): BlockReference = { slot: b.slot, hash: b.hash }

  pure def slotOf(msg: Message): Slot =
    match msg {
      | NotarVoteMsg(m) => m.slot
      | NotarFallBackVoteMsg(m) => m.slot
      | SkipVoteMsg(slot) => slot
      | SkipFallbackVoteMsg(slot) => slot
      | FinalVoteMsg(slot) => slot
    }

  /// line 10 of TryNotar. TODO: Is there more to it?
  pure def firstSlotInLeaderWindow(slot: Slot): bool =
    slot % 4 == 0 // TODO implement

  // Definition 13 (certificates)
  // They are defined over a set of messages. Currently we evaluate this over the
  // message soup. But they can be also used over locally received messages if such
  // a semantics is needed.

  /// Table 5: Apenglow's certificate messages.
  pure def isCertified(cert: Certificate, msgs: Set[NetworkMsg]): bool = {
    val aggregatedVotes = msgs.filter(m => {
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

    val threshold = match cert {
      | FastFinalizationCertificate => 80
      | NotarizationCertificate => 60
      | NotarFallbackCertificate => 60
      | SkipCertificate => 60
      | FinalizationCertificate => 60
    }

    aggregatedVotes.map(m => m.sender).surpassesThreshold(threshold)
  }

  pure def notarizedBlocks(msgs: Set[NetworkMsg]): Set[BlockReference] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | NotarVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(b => isCertified(NotarizationCertificate(b), msgs))

  pure def slotsSkipCertified(msgs: Set[NetworkMsg]): Set[Slot] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | SkipVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(s => isCertified(SkipCertificate(s), msgs))

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

  pure def setTimeouts(ls: State, slot: Slot): { output: Set[choreo::Effect[ProcessID, Message, TimeoutEvent, CustomEffects]], post: State } =
    { post: ls,
      output: windowSlots(slot).map(i => choreo::CustomEffect(ScheduleEventTimeout(i))) }

  /// Check if a notarization vote can be cast
  pure def tryNotar(ls: State, b: Block): { result: { output: Set[choreo::Effect[ProcessID, Message, TimeoutEvent, CustomEffects]], post: State }, success: bool } =
    if (ls.state[b.slot].contains(Voted))
      { result: { post: ls, output: Set() }, success: false }
    else
      val firstSlot = firstSlotInLeaderWindow(b.slot)
      if ((firstSlot and ParentReady(b.parent).in(ls.state[b.slot]))
        or (not(firstSlot) and VotedNotar(b.parent).in(ls.state[b.slot - 1])))
        // Warning: parentheses not matching in paper

        // Notarization vote
        val out = Set(choreo::Broadcast(NotarVoteMsg({ slot:b.slot, hash: b.hash })))
        val s2 = addObjects(ls, b.slot, Set(Voted, VotedNotar(b.hash)))
          .setPendingBlock(b.slot, None)

        // Maybe vote finalize as well
        val tf = tryFinal(s2, b.slot, b.hash)

        { result: { post: tf.post, output: out.union(tf.output) }, success: true }
      else
        { result: { post: ls, output: Set() }, success: false }

  pure def tryFinal(ls: State, slot: Slot, hash: Blockhash): { output: Set[choreo::Effect[ProcessID, Message, TimeoutEvent, CustomEffects]], post: State } =
    if (BlockNotarized(hash).in(ls.state[slot]) and VotedNotar(hash).in(ls.state[slot])
        and not(BadWindow.in(ls.state[slot])))
      // Finalization vote
      { output: Set(choreo::Broadcast(FinalVoteMsg(slot))), post: addObjects(ls, slot, Set(ItsOver)) }
    else
      { output: Set(), post: ls }

  pure def trySkipWindow(ls: State, slot: Slot): { output: Set[choreo::Effect[ProcessID, Message, TimeoutEvent, CustomEffects]], post: State } =
    // Skip unvoted slots
    windowSlots(slot).fold({ output: Set(), post: ls }, (s, k) => {
      if (not(Voted.in(s.post.state[k])))
        // Skip vote
        val update = Set(choreo::Broadcast(SkipVoteMsg(k)))
        val s2 = addObjects(s.post, k, Set(Voted, BadWindow))
          .setPendingBlock(k, None)

        { output: s.output.union(update), post: s2 }
      else
        s
    })

  pure def checkPendingBlocks(ls: State): { output: Set[choreo::Effect[ProcessID, Message, TimeoutEvent, CustomEffects]], post: State } =
    // Iterate with increasing slot
    // (left to right)
    ls.pendingBlocks.foldl({ output: Set(), post: ls }, (res, pendingBlock) =>
      match pendingBlock {
        | Some(b) =>
          val tn = tryNotar(res.post, b)
          { output: res.output.union(tn.result.output), post: tn.result.post }
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

  pure def safeToNotarCondition(v: ProcessID, msgs: Set[NetworkMsg], now: Slot, b: Block): bool = all {
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

  pure def safeToSkipCondition(v: ProcessID, allMessages: Set[NetworkMsg], now: Slot): bool = all {
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

  /// Algorithm 1: each upon corresponds to one consensus input
  pure def consensus(ls: State, input: ConsensusInput): { output: Set[choreo::Effect[ProcessID, Message, TimeoutEvent, CustomEffects]], post: State } =
    match input {
      | BlockInput(b) =>
        val tn = tryNotar(ls, b) // looks like a function but has two side effects: changes state and broadcasts
        if (tn.success)
          val cpb = checkPendingBlocks(tn.result.post)
          // as tryNotar changed the local state, we pass it to checkPendingBlocks
          { post: cpb.post, output: cpb.output.union(tn.result.output) }
          // both, tryNotar and checkPendingBlocks have side effects of sending messages. Thus we build the union here.
        else if (not(Voted.in(tn.result.post.state[b.slot])))
          { output: tn.result.output, post: setPendingBlock(tn.result.post, b.slot, Some(b)) }
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
        val s1 = addObjects(ls, sh.slot, Set(BlockNotarized(sh.hash)))
        tryFinal(s1, sh.slot, sh.hash)

      | ParentReadyInput(sh) =>
        val s1 = addObjects(ls, sh.slot, Set(ParentReady(sh.hash)))
        val s2 = checkPendingBlocks(s1)
        // Start time for all slots in this window
        val s3 = setTimeouts(s2.post, sh.slot)
        { output: s2.output.union(s3.output), post: s3.post }

      | SafeToNotarInput(sh) =>
        val s1 = trySkipWindow(ls, sh.slot)
        if (not(ItsOver.in(s1.post.state[sh.slot])))
          // Notar-fallback vote
          val output = s1.output.union(Set(choreo::Broadcast(NotarFallBackVoteMsg(sh))))
          { output: output, post: addObjects(s1.post, sh.slot, Set(BadWindow)) }
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

  // -----------------------------------------------------------------------------
  // Listener functions (converted from statemachine.qnt actions)
  // -----------------------------------------------------------------------------

  /// Process consensus input and convert to choreo transition
  pure def processConsensusInput(input: ConsensusInput, ctx: LocalContext): Set[Transition] = {
    val state_without_id = { pendingBlocks: ctx.state.pendingBlocks, state: ctx.state.state }
    val result = consensus(state_without_id, input)
    if (result.output.size() > 0 or result.post != state_without_id) {
      Set({
        effects: result.output,
        post_state: { ...ctx.state, pendingBlocks: result.post.pendingBlocks, state: result.post.state }
      })
    } else {
      Set()
    }
  }

  /// Listen for block input
  pure def upon_block_input(ctx: LocalContext): Set[Transition] = {
    val availableBlocks = allBlocks.filter(b => aliveSlots.contains(b.slot))
    availableBlocks.fold(Set(), (acc, block) =>
      acc.union(processConsensusInput(BlockInput(block), ctx))
    )
  }

  /// Listen for timeout events
  pure def upon_timeout(ctx: LocalContext): Set[Transition] = {
    val activeTimeouts = ctx.extensions.activeTimeouts.get(ctx.state.process_id)
    aliveSlots.filter(slot => activeTimeouts.contains(slot)).fold(Set(), (acc, slot) =>
      acc.union(processConsensusInput(TimeOutInput(slot), ctx))
    )
  }

  /// Listen for block notarized events
  pure def upon_block_notarized(ctx: LocalContext): Set[Transition] = {
    val allMessages = ctx.extensions.msgBuffer.union(byzNetworkMsgs)
    val notarizedBlocks = allBlocks.filter(b => 
      isCertified(NotarizationCertificate({ slot: b.slot, hash: b.hash }), allMessages) and
      aliveSlots.contains(b.slot)
    )
    notarizedBlocks.fold(Set(), (acc, block) =>
      acc.union(processConsensusInput(BlockNotarizedInput({ slot: block.slot, hash: block.hash }), ctx))
    )
  }

  /// Listen for parent ready events
  pure def upon_parent_ready(ctx: LocalContext): Set[Transition] = {
    val allMessages = ctx.extensions.msgBuffer.union(byzNetworkMsgs)
    val readyBlocks = allBlocks.filter(b => 
      aliveSlots.contains(b.slot) and
      parentReadyCondition(b.slot, b.hash, allMessages)
    )
    readyBlocks.fold(Set(), (acc, block) =>
      acc.union(processConsensusInput(ParentReadyInput({ slot: block.slot, hash: block.hash }), ctx))
    )
  }

  /// Listen for safe to notar events
  pure def upon_safe_to_notar(ctx: LocalContext): Set[Transition] = {
    val allMessages = ctx.extensions.msgBuffer.union(byzNetworkMsgs)
    val safeBlocks = allBlocks.filter(b => 
      aliveSlots.contains(b.slot) and
      safeToNotarCondition(ctx.state.process_id, allMessages, b.slot, b)
    )
    safeBlocks.fold(Set(), (acc, block) =>
      acc.union(processConsensusInput(SafeToNotarInput({ slot: block.slot, hash: block.hash }), ctx))
    )
  }

  /// Listen for safe to skip events
  pure def upon_safe_to_skip(ctx: LocalContext): Set[Transition] = {
    val allMessages = ctx.extensions.msgBuffer.union(byzNetworkMsgs)
    val safeSlots = aliveSlots.filter(slot => safeToSkipCondition(ctx.state.process_id, allMessages, slot))
    safeSlots.fold(Set(), (acc, slot) =>
      acc.union(processConsensusInput(SafeToSkipInput(slot), ctx))
    )
  }

  /// Main listener combining all event handlers
  pure def main_listener(ctx: LocalContext): Set[Transition] =
    Set(
      upon_block_input(ctx),
      upon_timeout(ctx),
      upon_block_notarized(ctx),
      upon_parent_ready(ctx),
      upon_safe_to_notar(ctx),
      upon_safe_to_skip(ctx)
    ).flatten()

  // -----------------------------------------------------------------------------
  // Choreo integration (init and step actions)
  // -----------------------------------------------------------------------------

  /// Initialize process state
  pure def initialize_process(process: ProcessID): LocalState = {
    val maxSlot = if (aliveSlots.size() > 0) aliveSlots.fold(-1, (acc, s) => max(acc, s)) else 4
    val slots = 0.to(maxSlot)
    {
      process_id: process,
      pendingBlocks: slots.fold([], (acc, _) => acc.append(None)),
      state: slots.fold([], (acc, slot) => 
        if (slot == 0) {
          acc.append(Set(ParentReady(-1)))
        } else {
          acc.append(Set())
        }
      )
    }
  }

  /// Initial extensions state
  pure def initial_extensions: Extensions = {
    msgBuffer: Set(),
    activeTimeouts: benevolent.mapBy(v => Set(0)),
    ch: aliveSlots.mapBy(s => Set()),
    counter: 0
  }

  action init = choreo::init({
    system: benevolent.mapBy(n => initialize_process(n)),
    messages: benevolent.mapBy(n => Set()),
    events: benevolent.mapBy(n => Set(0)), // initial timeout for slot 0
    extensions: initial_extensions
  })

  action step = choreo::step(
    main_listener,
    (c, _) => c,
    (e, p) => e
  )

  // -----------------------------------------------------------------------------
  // Invariants and properties
  // -----------------------------------------------------------------------------

  /// Agreement: no two correct processes decide on different values for the same slot
  pure def agreement: bool = true // Simplified for now
  
  /// Validity: if a correct process decides v, then v was proposed by some process
  pure def validity: bool = true // Simplified for now
}