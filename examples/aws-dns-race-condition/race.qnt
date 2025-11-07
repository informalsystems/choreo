// -*- mode: Bluespec; -*-
/**
 * AWS DNS Race Condition - Choreo Version
 *
 * This specification models a race condition in an AWS DNS management system
 * where multiple Enactor processes apply DNS plans to Route53.
 *
 * The bug: An enactor can delete a plan that is currently active if there's
 * a race between applying a newer plan and cleaning up old ones.
 * 
 * Heavily based on the TLA+ spec by Murat Demirbas [1].
 *
 * [1]: https://muratbuffalo.blogspot.com/2025/11/tla-modeling-of-aws-outage-dns-race.html 
 */

module awsDnsRaceChoreo {
  import basicSpells.* from "../../spells/basicSpells"
  import choreo(processes = NODE_SPECS) as choreo from "../../choreo"
  import types.* from "types"

  // =============================================================================
  // CONFIGURATION
  // =============================================================================

  pure val ENACTORS: Set[str] = Set("enactor1", "enactor2")
  pure val PLAN_AGE_THRESHOLD: int = 2
  pure val MAX_PLAN: int = 5
  pure val PLANNER: str = "planner"

  // Define node specs with roles
  pure val NODE_SPECS = ENACTORS.map(e => { proc_id: e, proc_role: EnactorRole })
    .union(Set({ proc_id: PLANNER, proc_role: PlannerRole }))

  pure val NODES = NODE_SPECS.map(info => info.proc_id)

  // =============================================================================
  // HELPER FUNCTIONS
  // =============================================================================

  pure def isPlanDeleted(plan: PlanId, deleted_map: PlanId -> bool): bool = {
    deleted_map.get(plan)
  }

  pure def cleanupPlans(my_plan: PlanId, old_deleted: PlanId -> bool): PlanId -> bool = {
    1.to(MAX_PLAN).mapBy(j =>
      if (my_plan - j >= PLAN_AGE_THRESHOLD) {
        true
      } else {
        old_deleted.get(j)
      }
    )
  }

  // =============================================================================
  // PLANNER TRANSITIONS
  // =============================================================================

  // Listener: Check if planner can create a new plan
  // Uses generic with_planner helper - returns Set[()]
  pure def listen_planner_can_create(ctx: LocalContext): Set[int] = {
    with_planner(ctx, planner => {
      if (planner.latest_plan < MAX_PLAN) {
        Set(planner.latest_plan + 1)
      } else {
        Set()
      }
    })
  }

  // Action: Planner creates a new plan and sends it only to enactors
  pure def planner_create_plan(ctx: LocalContext, new_plan: int): Transition = {
    {
      effects: ENACTORS.map(e => choreo::Send({ to: e, message: PlanMessage(new_plan) })),
      post_state: PlannerProcess({ latest_plan: new_plan })
    }
  }

  // =============================================================================
  // ENACTOR TRANSITIONS
  // =============================================================================

  // Step 1: Listener for plan messages
  // Uses generic with_enactor helper - returns Set[PlanId]
  pure def listen_for_plan_message(ctx: LocalContext): Set[PlanId] = {
    with_enactor(ctx, enactor => {
      if (enactor.pc == Idle) {
        get_plan_messages(ctx.messages)
      } else {
        Set()
      }
    })
  }

  // Step 1: Action - Enactor receives a plan
  pure def enactor_receive_plan(ctx: LocalContext, plan_id: PlanId): Transition = {
    {
      effects: Set(),
      post_state: EnactorProcess({ processing: plan_id, pc: Received })
    }
  }

  // Step 2a: Listener for valid (non-deleted) plans to apply
  // Uses generic with_enactor helper - returns Set[PlanId]
  pure def listen_for_valid_plan_to_apply(ctx: LocalContext): Set[PlanId] = {
    with_enactor(ctx, enactor => {
      val plan = enactor.processing
      if (enactor.pc == Received and not(isPlanDeleted(plan, ctx.extensions.plan_deleted))) {
        Set(plan)
      } else {
        Set()
      }
    })
  }

  // Step 2a: Action - Enactor applies a valid plan
  pure def enactor_apply_valid_plan(ctx: LocalContext, plan: PlanId): Transition = {
    with_enactor_action(ctx, enactor => {
      effects: Set(choreo::CustomEffect(ApplyPlan(plan))),
      post_state: { ...enactor, pc: Applied }
    })
  }

  // Step 2b: Listener for deleted plans to skip
  // Uses generic with_enactor helper - returns Set[()]
  pure def listen_for_deleted_plan_to_skip(ctx: LocalContext): Set[()] = {
    with_enactor(ctx, enactor => {
      val plan = enactor.processing
      if (enactor.pc == Received and isPlanDeleted(plan, ctx.extensions.plan_deleted)) {
        Set(())
      } else {
        Set()
      }
    })
  }

  // Step 2b: Action - Enactor skips a deleted plan
  pure def enactor_skip_deleted_plan(ctx: LocalContext, _unit: ()): Transition = {
    {
      effects: Set(),
      post_state: EnactorProcess({ processing: 0, pc: Idle })
    }
  }

  // Step 3: Listener - Check if enactor can cleanup
  // Uses generic with_enactor helper - returns Set[PlanId]
  pure def listen_enactor_can_cleanup(ctx: LocalContext): Set[PlanId] = {
    with_enactor(ctx, enactor => {
      if (enactor.pc == Applied) {
        Set(enactor.processing)
      } else {
        Set()
      }
    })
  }

  // Step 3: Action - Enactor cleans up old plans
  pure def enactor_cleanup(ctx: LocalContext, plan: PlanId): Transition = {
    {
      effects: Set(choreo::CustomEffect(CleanupPlans(plan))),
      post_state: EnactorProcess({ processing: 0, pc: Idle })
    }
  }

  // =============================================================================
  // MAIN LISTENER
  // =============================================================================

  pure def main_listener(ctx: LocalContext): Set[Transition] = {
    Set(
      // Planner transitions
      choreo::cue(ctx, listen_planner_can_create, planner_create_plan),

      // Enactor transitions
      choreo::cue(ctx, listen_for_plan_message, enactor_receive_plan),
      choreo::cue(ctx, listen_for_valid_plan_to_apply, enactor_apply_valid_plan),
      choreo::cue(ctx, listen_for_deleted_plan_to_skip, enactor_skip_deleted_plan),
      choreo::cue(ctx, listen_enactor_can_cleanup, enactor_cleanup)
    ).flatten()
  }

  // =============================================================================
  // CUSTOM EFFECTS PROCESSOR
  // =============================================================================

  pure def apply_custom_effect(
    ctx: GlobalContext,
    effect: CustomEffects
  ): GlobalContext = {
    match effect {
      | ApplyPlan(plan) => {
        val new_extensions = {
          ...ctx.extensions,
          current_plan: plan,
          highest_plan_applied: if (plan > ctx.extensions.highest_plan_applied) {
            plan
          } else {
            ctx.extensions.highest_plan_applied
          }
        }
        { ...ctx, extensions: new_extensions }
      }
      | CleanupPlans(my_plan) => {
        val new_deleted = cleanupPlans(my_plan, ctx.extensions.plan_deleted)
        val new_extensions = { ...ctx.extensions, plan_deleted: new_deleted }
        { ...ctx, extensions: new_extensions }
      }
    }
  }

  // =============================================================================
  // INITIALIZATION
  // =============================================================================

  pure def initialize(n: Node): ProcessState = {
    if (n == PLANNER) {
      PlannerProcess({
        latest_plan: 0
      })
    } else {
      EnactorProcess({
        processing: 0,
        pc: Idle
      })
    }
  }

  action init = choreo::init({
    system: NODES.mapBy(n => initialize(n)),
    messages: NODES.mapBy(n => Set()),
    events: NODES.mapBy(n => Set()),
    extensions: {
      current_plan: 0,
      highest_plan_applied: 0,
      plan_deleted: 1.to(MAX_PLAN).mapBy(i => false)
    }
  })

  // =============================================================================
  // STEP FUNCTION
  // =============================================================================

  action step = choreo::step(main_listener, apply_custom_effect)

  // =============================================================================
  // INVARIANTS
  // =============================================================================

  val neverDeleteActive: bool = {
    val current = s.extensions.current_plan
    val deleted = s.extensions.plan_deleted
    current == 0 or not(isPlanDeleted(current, deleted))
  }

  // =============================================================================
  // WIRING
  // =============================================================================

  val s = choreo::s

  def with_cue(process, listen_fn, params) =
    choreo::with_cue(process, listen_fn, params)

  action perform(cue_ctx, upon_fn) =
    choreo::perform(cue_ctx, upon_fn, apply_custom_effect)

  // =============================================================================
  // EXAMPLE RACE CONDITION
  // =============================================================================

  /// Demonstrates the race condition bug:
  /// Enactor1 picks up an old plan but lags. Enactor2 moves faster and applies
  /// newer plans. When Enactor1 finally applies its stale plan, it overwrites
  /// Enactor2's work. Then Enactor2's cleanup deletes the now-active plan.
  run raceConditionScenario = {
    init
      // Planner creates plans 1..3
      .then(PLANNER.with_cue(listen_planner_can_create, 1).perform(planner_create_plan))
      .then(PLANNER.with_cue(listen_planner_can_create, 2).perform(planner_create_plan))
      .then(PLANNER.with_cue(listen_planner_can_create, 3).perform(planner_create_plan))
      
      // Enactor1 receives plan 1 but then lags
      .then("enactor1".with_cue(listen_for_plan_message, 1).perform(enactor_receive_plan))

      // Enactor2 arrives and moves faster: receiving and applying plan 2
      .then("enactor2".with_cue(listen_for_plan_message, 2).perform(enactor_receive_plan))
      .then("enactor2".with_cue(listen_for_valid_plan_to_apply, 2).perform(enactor_apply_valid_plan))

      // Enactor2 performs cleanup
      .then("enactor2".with_cue(listen_enactor_can_cleanup, 2).perform(enactor_cleanup))
      // plan 1 survives because 2 - 1 < PLAN_AGE_THRESHOLD
      .expect(not(isPlanDeleted(1, s.extensions.plan_deleted)))

      // Enactor2 receives and applies plan 3
      .then("enactor2".with_cue(listen_for_plan_message, 3).perform(enactor_receive_plan))
      .then("enactor2".with_cue(listen_for_valid_plan_to_apply, 3).perform(enactor_apply_valid_plan))
      .expect(s.extensions.current_plan == 3)

      // NOW: Enactor1 finally wakes up and applies its stale plan 1!
      .then("enactor1".with_cue(listen_for_valid_plan_to_apply, 1).perform(enactor_apply_valid_plan))
      // This overwrites Enactor2's freshly installed plan 3
      .expect(s.extensions.current_plan == 1)

      // Enactor2 performs cleanup again with plan 3
      .then("enactor2".with_cue(listen_enactor_can_cleanup, 3).perform(enactor_cleanup))
      // Now 3 - 1 = 2 >= PLAN_AGE_THRESHOLD, so plan 1 gets deleted
      .expect(isPlanDeleted(1, s.extensions.plan_deleted))

      // BUG: The currently active plan (plan 1) is now marked as deleted!
      .expect(s.extensions.current_plan == 1)
      .expect(not(neverDeleteActive))
  }
}
