// -*- mode: Bluespec; -*-
/**
 * Distributed ATM System with Coordinated Withdrawals
 *
 * This specification models a set of ATM machines that share account data
 * through distributed databases. The key challenge is preventing double
 * withdrawals: without coordination, two ATMs could approve simultaneous
 * withdrawals, allowing a user to withdraw more than their balance.
 *
 * Problem we want to avoid:
 * User has $100 in account. Two ATMs process $80 withdrawal requests
 * simultaneously. Without coordination, both might see balance=$100,
 * both approve, and user withdraws $160 total.
 *
 * ATMs use a distributed locking protocol:
 * 1. ATM requests lock from all other ATMs before withdrawal
 * 2. Only proceeds if all ATMs grant the lock
 * 3. Broadcasts withdrawal completion to update all databases
 * 4. Releases lock for next operation
 *
 * This ensures at most one ATM processes a withdrawal for an account at a time.
 */

module atm_distributed {
  import basicSpells.* from "../../spells/basicSpells"
  import choreo(processes = ATMS) as choreo from "../../choreo"

  // Account identifiers
  type Account = str

  // Money amounts (simplified as integers)
  type Amount = int

  // Each ATM is a process in the system
  type Node = str

  // A withdrawal request: uniquely identifies a specific withdrawal attempt
  type Request = {
    account: Account,
    amount: Amount,
    request_id: int,
    requester: Node
  }

  // Messages exchanged between ATMs for coordination
  type Message =
    // Request exclusive lock on account to process withdrawal
    | RequestLock(Request)
    // Grant lock to requesting ATM
    | GrantLock({ req: Request, from_atm: Node })
    // Deny lock (already locked by someone else)
    | DenyLock({ req: Request, from_atm: Node })
    // Broadcast completed withdrawal to update all databases
    | CommitWithdrawal({ req: Request, new_balance: Amount })
    // Release lock after withdrawal completes or aborts
    | ReleaseLock(Request)

  // Local state maintained by each ATM
  type StateFields = {
    // Local database replica - each ATM has a copy of all balances
    balances: Account -> Amount,

    // Accounts we've granted locks for to other ATMs
    // Maps account -> request_id we granted it for (to prevent stale lock reuse)
    locks_granted_to_others: Account -> Option[int],

    // Our own withdrawal coordination.
    // When we initiate a withdrawal, we track it here until commit/abort
    pending_withdrawal: Option[Request],

    // Request ID counter. Increments with each new withdrawal request
    next_request_id: int
  }

  // Emitted by commit_withdrawal to record a successful withdrawal globally
  type CustomEffects = { account: Account, amount: Amount }
  type Event = ()
  // Global environment tracking total amount withdrawn per account across all ATMs
  type Extensions = { total_withdrawn: Account -> Amount }

  type LocalState = choreo::LocalState[Node, StateFields]
  type LocalContext = choreo::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition = choreo::Transition[Node, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[Node, StateFields, Message, Event, Extensions]

  // =============================================================================
  // HELPER FUNCTIONS
  // =============================================================================

  /// Number of ATMs needed for quorum (all ATMs must agree for lock)
  pure val quorum_size = ATMS.size() - 1  // All other ATMs must respond

  /// Check if account has sufficient balance
  pure def has_sufficient_balance(balances: Account -> Amount, account: Account, amount: Amount): bool = {
    balances.get(account) >= amount
  }

  /// Count how many ATMs have granted us the lock for a specific request
  pure def count_approvals(messages: Set[Message], req: Request): int = {
    messages.filter(m => match m {
      | GrantLock(grant) =>
          grant.req.account == req.account and
          grant.req.request_id == req.request_id
      | _ => false
    }).size()
  }

  /// Check if any ATM has denied us the lock for a specific request
  pure def has_any_denials(messages: Set[Message], req: Request): bool = {
    messages.exists(m => match m {
      | DenyLock(deny) =>
          deny.req.account == req.account and
          deny.req.request_id == req.request_id
      | _ => false
    })
  }

  /// Extract CommitWithdrawal messages
  pure def get_commit_withdrawals(messages: Set[Message]): Set[{ req: Request, new_balance: Amount }] = {
    messages.filterMap(m => match m {
      | CommitWithdrawal(commit) => Some(commit)
      | _ => None
    })
  }

  /// Extract ReleaseLock messages
  pure def get_release_locks(messages: Set[Message]): Set[Request] = {
    messages.filterMap(m => match m {
      | ReleaseLock(rel) => Some(rel)
      | _ => None
    })
  }

  // =============================================================================
  // TRANSITION FUNCTIONS
  // =============================================================================

  /// User initiates withdrawal at an ATM
  pure def listen_initiate_withdrawal(ctx: LocalContext): Set[Request] = {
    val s = ctx.state

    // Can only initiate if not already processing a withdrawal
    val can_initiate = s.pending_withdrawal == None

    if (can_initiate) {
      // All possible requests we can make from this ATM
      tuples(ACCOUNTS, WITHDRAWAL_AMOUNTS).map(((account, amount)) => {
        { account: account, amount: amount, request_id: s.next_request_id, requester: s.process_id }
      })
    } else {
      Set()
    }
  }

  pure def initiate_withdrawal(ctx: LocalContext, req: Request): Transition = {
    val s = ctx.state
    {
      effects: Set(
        choreo::Broadcast(RequestLock(req))
      ),
      post_state: {
        ...s,
        pending_withdrawal: Some(req),
        next_request_id: req.request_id + 1
      }
    }
  }

  /// ATM responds to lock request from another ATM
  pure def listen_lock_request(ctx: LocalContext): Set[Request] = {
    val s = ctx.state
    val messages = ctx.messages

    messages.filterMap(m => match m {
      | RequestLock(req) =>
          // Don't respond to our own requests
          if (req.requester != s.process_id) Some(req)
          else None
      | _ => None
    })
  }

  pure def respond_to_lock_request(ctx: LocalContext, req: Request): Transition = {
    val s = ctx.state

    // Grant lock if we don't have it locked and are not already withdrawing from
    // this account ourselves, otherwise two ATMs could mutually grant each other
    // and both collect quorum simultaneously
    val is_locked = s.locks_granted_to_others.get(req.account) != None or
      match s.pending_withdrawal {
        | Some(pw) => pw.account == req.account
        | None => false
      }

    val response_message = if (is_locked) {
      DenyLock({ req: req, from_atm: s.process_id })
    } else {
      GrantLock({ req: req, from_atm: s.process_id })
    }

    val new_locks = if (is_locked) {
      s.locks_granted_to_others
    } else {
      // Reserve the lock for the requester with this request_id
      s.locks_granted_to_others.set(req.account, Some(req.request_id))
    }

    {
      effects: Set(
        choreo::Send({ to: req.requester, message: response_message })
      ),
      post_state: {
        ...s,
        locks_granted_to_others: new_locks
      }
    }
  }

  /// ATM processes lock responses and commits withdrawal if all granted
  pure def listen_approval_quorum(ctx: LocalContext): Set[Request] = {
    val s = ctx.state

    match s.pending_withdrawal {
      | Some(req) => {
          // Query the message soup for responses (filtered by request_id!)
          val approvals = count_approvals(ctx.messages, req)
          val has_denials = has_any_denials(ctx.messages, req)

          // All other ATMs must approve (no denials)
          val all_approved = approvals >= quorum_size and not(has_denials)

          // Check sufficient balance
          val sufficient_balance = has_sufficient_balance(s.balances, req.account, req.amount)

          if (all_approved and sufficient_balance) Set(req) else Set()
        }
      | None => Set()
    }
  }

  pure def commit_withdrawal(ctx: LocalContext, req: Request): Transition = {
    val s = ctx.state

    val new_balance = s.balances.get(req.account) - req.amount

    {
      effects: Set(
        // Broadcast the completed withdrawal; receivers release their lock atomically
        // in update_balance (no separate ReleaseLock needed on the commit path)
        choreo::Broadcast(CommitWithdrawal({ req: req, new_balance: new_balance })),
        // Record the withdrawal in the global environment
        choreo::CustomEffect({ account: req.account, amount: req.amount })
      ),
      post_state: {
        ...s,
        balances: s.balances.set(req.account, new_balance),
        locks_granted_to_others: s.locks_granted_to_others.set(req.account, None),
        pending_withdrawal: None
      }
    }
  }

  /// ATM aborts withdrawal if any lock denied
  pure def listen_abort_withdrawal(ctx: LocalContext): Set[Request] = {
    val s = ctx.state

    match s.pending_withdrawal {
      | Some(req) => {
          // Query the message soup (filtered by request_id!)
          val has_denial = has_any_denials(ctx.messages, req)

          // Also abort if insufficient balance
          val insufficient_balance = not(has_sufficient_balance(s.balances, req.account, req.amount))

          if (has_denial or insufficient_balance) Set(req) else Set()
        }
      | None => Set()
    }
  }

  pure def abort_withdrawal(ctx: LocalContext, req: Request): Transition = {
    val s = ctx.state

    {
      effects: Set(
        // Notify others that we're releasing the lock request
        choreo::Broadcast(ReleaseLock(req))
      ),
      post_state: {
        ...s,
        pending_withdrawal: None
      }
    }
  }

  /// ATM updates local database when seeing committed withdrawals
  pure def listen_commit_withdrawal(ctx: LocalContext): Set[{ req: Request, new_balance: Amount }] = {
    val s = ctx.state
    val messages = ctx.messages

    get_commit_withdrawals(messages)
  }

  pure def update_balance(ctx: LocalContext, commit: { req: Request, new_balance: Amount }): Transition = {
    val s = ctx.state

    // Release the lock atomically with the balance update: an ATM can only free a
    // lock for an account once it has applied the committed balance, closing the
    // window where a stale (too-high) balance could enable a second withdrawal.
    val should_release =
      s.locks_granted_to_others.get(commit.req.account) == Some(commit.req.request_id)

    {
      effects: Set(),
      post_state: {
        ...s,
        balances: s.balances.set(commit.req.account, commit.new_balance),
        locks_granted_to_others: if (should_release)
          s.locks_granted_to_others.set(commit.req.account, None)
        else
          s.locks_granted_to_others
      }
    }
  }

  /// ATM releases lock when seeing ReleaseLock message
  pure def listen_release_lock(ctx: LocalContext): Set[Request] = {
    val s = ctx.state
    val messages = ctx.messages

    get_release_locks(messages).filter(rel => {
      // Only process releases from other ATMs for accounts we have locked
      // AND the request_id must match what we granted
      rel.requester != s.process_id and
      s.locks_granted_to_others.get(rel.account) == Some(rel.request_id)
    })
  }

  pure def release_lock(ctx: LocalContext, rel: Request): Transition = {
    val s = ctx.state

    {
      effects: Set(),
      post_state: {
        ...s,
        locks_granted_to_others: s.locks_granted_to_others.set(rel.account, None)
      }
    }
  }

  // =============================================================================
  // MAIN LISTENER
  // =============================================================================

  pure def main_listener(ctx: LocalContext): Set[Transition] = {
    Set(
      // User initiates withdrawal
      choreo::cue(ctx, listen_initiate_withdrawal, initiate_withdrawal),

      // ATM responds to lock requests from others
      choreo::cue(ctx, listen_lock_request, respond_to_lock_request),

      // ATM commits withdrawal after receiving enough approvals
      choreo::cue(ctx, listen_approval_quorum, commit_withdrawal),

      // ATM aborts withdrawal if denied
      choreo::cue(ctx, listen_abort_withdrawal, abort_withdrawal),

      // ATM updates balance from broadcast commits
      choreo::cue(ctx, listen_commit_withdrawal, update_balance),

      // ATM releases lock when others release
      choreo::cue(ctx, listen_release_lock, release_lock)
    ).flatten()
  }

  // =============================================================================
  // CUSTOM EFFECT PROCESSOR
  // =============================================================================

  pure def apply_custom_effect(ctx: GlobalContext, effect: CustomEffects): GlobalContext = {
    val prev = ctx.extensions.total_withdrawn.get(effect.account)
    { ...ctx, extensions: { total_withdrawn: ctx.extensions.total_withdrawn.set(effect.account, prev + effect.amount) } }
  }

  // =============================================================================
  // PROTOCOL CONFIGURATION
  // =============================================================================

  // Three ATM machines in the system
  pure val ATMS = Set("ATM1", "ATM2", "ATM3")

  // Available accounts
  pure val ACCOUNTS = Set("Alice", "Bob")

  // Possible withdrawal amounts
  pure val WITHDRAWAL_AMOUNTS = 0.to(100)

  // Initial balance for all accounts
  pure val INITIAL_BALANCE = 100

  // =============================================================================
  // INITIALIZATION
  // =============================================================================

  pure def initialize(atm: Node): LocalState = {
    {
      process_id: atm,
      balances: ACCOUNTS.mapBy(acc => INITIAL_BALANCE),
      locks_granted_to_others: ACCOUNTS.mapBy(acc => None),
      pending_withdrawal: None,
      next_request_id: 0
    }
  }

  action init = choreo::init({
    system: ATMS.mapBy(atm => initialize(atm)),
    messages: ATMS.mapBy(atm => Set()),
    events: ATMS.mapBy(atm => Set()),
    extensions: { total_withdrawn: ACCOUNTS.mapBy(acc => 0) }
  })

  // =============================================================================
  // STEP FUNCTION
  // =============================================================================

  action step = choreo::step(main_listener, apply_custom_effect)

  // =============================================================================
  // INVARIANTS - KEY SAFETY PROPERTIES
  // =============================================================================

  val s = choreo::s

  /// No account balance goes negative
  val no_negative_balance = ATMS.forall(atm => {
    ACCOUNTS.forall(account => {
      s.system.get(atm).balances.get(account) >= 0
    })
  })

  /// At most one ATM holds lock on any account
  val mutual_exclusion = ACCOUNTS.forall(account => {
    val atms_holding_lock = ATMS.filter(atm => {
      s.system.get(atm).locks_granted_to_others.get(account) != None
    })
    atms_holding_lock.size() <= 1
  })

  /// All ATMs converge to same balance (after messages processed)
  val consistency = ACCOUNTS.forall(account => {
    // If no pending operations, all ATMs should agree on balance
    val no_pending = ATMS.forall(atm => {
      s.system.get(atm).pending_withdrawal == None and
      s.messages.get(atm) == Set()
    })

    val balances = ATMS.map(atm => s.system.get(atm).balances.get(account))

    no_pending implies balances.size() == 1
  })

  /// Total money in system never increases
  /// Sum of all balances across all accounts should never exceed initial total
  val conservation_of_money = {
    val total_balance = ATMS.fold(0, (sum, atm) => {
      ACCOUNTS.fold(sum, (acc_sum, account) => {
        acc_sum + s.system.get(atm).balances.get(account)
      })
    })

    val initial_total = ATMS.size() * ACCOUNTS.size() * INITIAL_BALANCE

    total_balance <= initial_total
  }

  /// Total withdrawn per account never exceeds the initial balance
  val no_overdraft = ACCOUNTS.forall(account =>
    s.extensions.total_withdrawn.get(account) <= INITIAL_BALANCE
  )

  // =============================================================================
  // WIRING (for testing with cue pattern)
  // =============================================================================

  action step_with(v: Node, listener: LocalContext => Set[Transition]): bool =
    choreo::step_with(v, listener, apply_custom_effect)

  action step_deterministic(v: Node, listener: LocalContext => Transition): bool =
    choreo::step_deterministic(v, listener, apply_custom_effect)

  def with_cue(process, listen_fn, params) =
    choreo::with_cue(process, listen_fn, params)

  action perform(cue_ctx, upon_fn) =
    choreo::perform(cue_ctx, upon_fn, apply_custom_effect)

  // =============================================================================
  // EXAMPLE RUNS
  // =============================================================================

  /// Happy path - a single ATM successfully withdraws from an account.
  /// Full protocol: initiate → grant locks → commit → propagate balance → release locks.
  run happyPathWithdrawalTest = {
    val req  = { account: "Alice", amount: 50, request_id: 0, requester: "ATM1" }
    val balance_to_write = { req: req, new_balance: 50 }

    init
    // A user at ATM1 requests a $50 withdrawal from Alice's account
    .then("ATM1".with_cue(listen_initiate_withdrawal, req).perform(initiate_withdrawal))

    // ATM2 and ATM3 receive the lock request; account is free so both grant it
    .then("ATM2".with_cue(listen_lock_request, req).perform(respond_to_lock_request))
    .expect(s.messages.get("ATM1").contains(GrantLock({ req: req, from_atm: "ATM2" })))
    .then("ATM3".with_cue(listen_lock_request, req).perform(respond_to_lock_request))
    .expect(s.messages.get("ATM1").contains(GrantLock({ req: req, from_atm: "ATM3" })))

    // ATM1 has quorum (grants from ATM2 + ATM3) and sufficient balance → commits
    .then("ATM1".with_cue(listen_approval_quorum, req).perform(commit_withdrawal))

    // Both ATM2 and ATM3 apply the committed balance and release their lock
    .then("ATM2".with_cue(listen_commit_withdrawal, balance_to_write).perform(update_balance))
    .then("ATM3".with_cue(listen_commit_withdrawal, balance_to_write).perform(update_balance))

    // All ATMs converged: Alice has $50, no locks held, no pending withdrawals
    .expect(no_negative_balance)
    .expect(mutual_exclusion)
    .expect(s.system.get("ATM1").balances.get("Alice") == 50)
    .expect(s.system.get("ATM2").balances.get("Alice") == 50)
    .expect(s.system.get("ATM3").balances.get("Alice") == 50)
    .expect(s.system.get("ATM2").locks_granted_to_others == ACCOUNTS.mapBy(acc => None))
    .expect(s.system.get("ATM3").locks_granted_to_others == ACCOUNTS.mapBy(acc => None))
  }

  /// Concurrent conflict - two ATMs race to withdraw from the same account.
  /// ATM3 grants ATM1's lock first. ATM2 is now pending for Alice, so both
  /// ATM3 (already locked) and ATM1 (pending for Alice) deny ATM2's request.
  /// ATM2 aborts. With its pending cleared, ATM2 can then grant ATM1's lock,
  /// giving ATM1 quorum. Only one $80 withdrawal commits.
  run concurrentConflictTest = {
    val req1 = { account: "Alice", amount: 80, request_id: 0, requester: "ATM1" }
    val req2 = { account: "Alice", amount: 80, request_id: 0, requester: "ATM2" }
    val balance_to_write = { req: req1, new_balance: 20 }

    init
    // Both ATM1 and ATM2 initiate $80 withdrawals from Alice "simultaneously"
    .then("ATM1".with_cue(listen_initiate_withdrawal, req1).perform(initiate_withdrawal))
    .then("ATM2".with_cue(listen_initiate_withdrawal, req2).perform(initiate_withdrawal))

    // ATM3 grants ATM1's lock first (Alice is free, ATM3 has no pending)
    .then("ATM3".with_cue(listen_lock_request, req1).perform(respond_to_lock_request))
    .expect(s.messages.get("ATM1").contains(GrantLock({ req: req1, from_atm: "ATM3" })))
    // ATM3 denies ATM2's lock (Alice already locked for ATM1)
    .then("ATM3".with_cue(listen_lock_request, req2).perform(respond_to_lock_request))
    .expect(s.messages.get("ATM2").contains(DenyLock({ req: req2, from_atm: "ATM3" })))
    // ATM1 also denies ATM2's lock: ATM1 is pending for Alice 
    .then("ATM1".with_cue(listen_lock_request, req2).perform(respond_to_lock_request))
    .expect(s.messages.get("ATM2").contains(DenyLock({ req: req2, from_atm: "ATM1" })))

    // ATM2 receives denials from both ATM3 and ATM1 → aborts
    .then("ATM2".with_cue(listen_abort_withdrawal, req2).perform(abort_withdrawal))

    // ATM2's pending is now None → it can grant ATM1's lock request
    .then("ATM2".with_cue(listen_lock_request, req1).perform(respond_to_lock_request))
    .expect(s.messages.get("ATM1").contains(GrantLock({ req: req1, from_atm: "ATM2" })))

    // ATM1 has quorum (grants from ATM3 + ATM2) → commits
    .then("ATM1".with_cue(listen_approval_quorum, req1).perform(commit_withdrawal))

    // ATM2 and ATM3 apply the committed balance and release their lock for ATM1
    .then("ATM2".with_cue(listen_commit_withdrawal, balance_to_write).perform(update_balance))
    .then("ATM3".with_cue(listen_commit_withdrawal, balance_to_write).perform(update_balance))
    // Only one $80 withdrawal occurred: Alice has $20, not -$60
    .expect(no_negative_balance)
    .expect(no_overdraft)
    .expect(mutual_exclusion)
    .expect(s.system.get("ATM1").balances.get("Alice") == 20)
    .expect(s.system.get("ATM2").balances.get("Alice") == 20)
    .expect(s.system.get("ATM2").pending_withdrawal == None)
    .expect(s.system.get("ATM3").locks_granted_to_others == ACCOUNTS.mapBy(acc => None))
  }

  /// Insufficient balance causes immediate abort.
  /// After ATM1 withdraws $80 (Alice's balance drops to $20), ATM2 updates its
  /// local replica and then tries to withdraw $80. Since ATM2's local balance
  /// shows $20 < $80, `listen_abort_withdrawal` fires without waiting for lock
  /// responses - ATM2 aborts before even collecting grants.
  run balanceDepletedAbortTest = {
    val req1 = { account: "Alice", amount: 80, request_id: 0, requester: "ATM1" }
    val req2 = { account: "Alice", amount: 80, request_id: 0, requester: "ATM2" }
    val balance_to_write = { req: req1, new_balance: 20 }

    init
    // ATM1 performs a full $80 withdrawal from Alice
    .then("ATM1".with_cue(listen_initiate_withdrawal, req1).perform(initiate_withdrawal))
    .then("ATM2".with_cue(listen_lock_request, req1).perform(respond_to_lock_request))
    .then("ATM3".with_cue(listen_lock_request, req1).perform(respond_to_lock_request))
    .expect(s.messages.get("ATM1").contains(GrantLock({ req: req1, from_atm: "ATM2" })))
    .expect(s.messages.get("ATM1").contains(GrantLock({ req: req1, from_atm: "ATM3" })))
    .then("ATM1".with_cue(listen_approval_quorum, req1).perform(commit_withdrawal))

    // ATM2 applies the committed balance. Also atomically releases its lock for ATM1
    .then("ATM2".with_cue(listen_commit_withdrawal, balance_to_write).perform(update_balance))

    // ATM2 tries to withdraw $80 from Alice (aware that balance is only $20)
    .then("ATM2".with_cue(listen_initiate_withdrawal, req2).perform(initiate_withdrawal))

    // ATM2 aborts immediately: local balance ($20) is insufficient for $80 withdrawal
    // No lock grants are needed - the balance check alone triggers the abort
    .then("ATM2".with_cue(listen_abort_withdrawal, req2).perform(abort_withdrawal))

    .expect(no_negative_balance)
    .expect(s.system.get("ATM2").balances.get("Alice") == 20)
    .expect(s.system.get("ATM2").pending_withdrawal == None)
  }
}
