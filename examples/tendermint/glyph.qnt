module glyph{
  import tendermint.* from "tendermint"
  import basicSpells.* from "lib/basicSpells"

  var s: Environment // Global state of the system

  //-------------------------------- glyphs helpers --------------------------------
  pure def broadcast(env: Environment, msg: Message): Environment = 
  { ...env, system: env.system.transformValues(s => { ...s, messages: s.messages.setAdd(msg) }) }

  pure val TIMEOUT_ORDER = Map(ProposeTimeout -> 0, PreVoteTimeout -> 1, PreCommitTimeout -> 2)
  pure def should_replace(t1: TimeoutEvent, t2: TimeoutEvent): bool = {
      TIMEOUT_ORDER.get(t2.kind) < TIMEOUT_ORDER.get(t1.kind) or t2.round > t1.round
  }
  pure def timeout(env: Environment, v: Node, event: TimeoutEvent): Environment = 
  { ...env,
      active_timeouts: env.active_timeouts.setBy(v, old_timeout => Some({
          match old_timeout {
          | None => event
          | Some(ts) => if (should_replace(ts, event)) event else ts
          }
      }))
  }

  pure def bookkeep(env: Environment, f: Bookkeeping => Bookkeeping): Environment = {
  { ...env, 
      bookkeeping: f(env.bookkeeping)
  }
  }

  // -------------------------------- effect processors --------------------------------
  pure def apply_effect(
    env: Environment,
    n: Node,
    ext: Set[ExternalEffect],
    inte: Set[InternalEffect],
    log: Set[LoggingEffect]
    ): Environment = {
    // Process external effects
    val env1 = ext.fold(env, (env, effect) => {
        match effect {
        | Broadcast(msg) => broadcast(env, msg)
        }
    });
    
    // Process internal effects
    val env2 = inte.fold(env1, (env, effect) => {
        match effect {
        | StartTimeout(event) => timeout(env, n, event)
        }
    });
    
    // Process logging effects
    val env3 = log.fold(env2, (env, effect) => {
        match effect {
        | CollectEvidence(msg) =>
            bookkeep(env, b => {
                match msg {
                | Propose(p)   => { ...b, evidence_propose: b.evidence_propose.setAdd(p) }
                | PreVote(p)   => { ...b, evidence_prevote: b.evidence_prevote.setAdd(p) }
                | PreCommit(p) => { ...b, evidence_precommit: b.evidence_precommit.setAdd(p) }
                }
            })
        | Breakpoint =>
            bookkeep(env, b => { ...b, breakpoint: true })
        }
    });
    env3
  }

  // -------------------------------- initialization --------------------------------
  pure val initial_message =
    Propose({ src: PROPOSER.get(0), round: 0, proposal: VALUES.get(0), valid_round: -1 })

  pure val initial_bookkeeping = {
    evidence_propose: Set(),
    evidence_prevote: Set(),
    evidence_precommit: Set(),
    breakpoint: false,
  }

  pure def initialize_process(n: Node): LocalState = {
    {
    process_id: n,
    messages: Set(initial_message),
    round: 0,
    stage: ProposeStage,
    decision: None,
    locked_value: None,
    locked_round: -1,
    valid_value: None,
    valid_round: -1,
    after_prevote_for_first_time: false,
    precommit_quorum: false,
    }
  }

  val byzantine_messages = {
    val rounds = s.system.values().map(s => s.round)
    val byzantine_proposals = rounds.map(r => {
      tuples(FAULTY, VALUES.values(), ROUNDS.setAdd(-1)).map(((f, v, vr)) => {
        Propose({ src: f, round: r, proposal: v, valid_round: vr })
      })
    }).flatten()

    val byzantine_prevotes = rounds.map(r => {
      tuples(FAULTY, VALUES.values()).map(((f, v)) => {
        PreVote({ src: f, round: r, id: Some(v.id()) })
      })
    }).flatten()

    val byzantine_precommits = rounds.map(r => {
      tuples(FAULTY, VALUES.values()).map(((f, v)) => {
        PreCommit({ src: f, round: r, id: Some(v.id()) })
      })
    }).flatten()

    Set(byzantine_proposals, byzantine_prevotes, byzantine_precommits).flatten()
  }

  // -------------------------------- actions --------------------------------
  action init = all {
    s' = {
      system: NODES.mapBy(n => initialize_process(n)),
      active_timeouts: NODES.mapBy(n => None),
      bookkeeping: initial_bookkeeping,
    }
  }


  action step = {
    nondet process = NODES.oneOf()
    val msgs = s.system.get(process).messages
    val initial = { state: s.system.get(process), external: Set(), internal: Set(), logging: Set() }
    val result = msgs.fold(initial, (accumulated_result, message) => {
      // Stop after finding the first effect
      if (accumulated_result.external != Set()) accumulated_result 
      else{
        val internal = accumulated_result.internal
        val external = accumulated_result.external
        val logging = accumulated_result.logging
        // accumulate the effects of the message
        val message_result = receive_message(accumulated_result.state, message)
        {
          state: message_result.state,
          external: external.union(message_result.external),
          internal: internal.union(message_result.internal),
          logging: logging.union(message_result.logging)
        }
        //accumulated_result.state.receive_message(message)
      }
    })
    all{
        result.external != Set(),
        // apply the effects to the environment
        val new_system = s.system.set(process, result.state)
        val new_env = {...s, system: new_system}
        s' = apply_effect(
            new_env,
            process,
            result.external,
            result.internal,
            result.logging
        )
    }
  }
}