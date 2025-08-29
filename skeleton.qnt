// -*- mode: Bluespec; -*-
/**
 * Choreo Protocol Skeleton
 *
 * This is a template file to help you get started with implementing
 * distributed protocols using the Choreo framework.
 *
 * Replace the TODO comments with your protocol-specific implementation.
 */

module my_protocol {
  import basicSpells.* from "spells/basicSpells"
  import choreo(processes = NODES) as choreo from "choreo"

  // TODO: Define your protocol-specific types here
  // For example:
  // type Phase = Init | Working | Committed | Aborted
  // type Value = str
  // type Role = Leader | Follower

  // =============================================================================
  // MANDATORY TYPE DEFINITIONS
  // =============================================================================

  // TODO: Define the node identifier type (usually str)
  type Node = str

  // TODO: Define all message types your protocol uses
  // This should be a union type of all possible messages
  type Message =
    | ExampleMessage(Node)
    // | AnotherMessage(Value)
    // | YetAnotherMessage

  // TODO: Define the local state fields for each process
  // Include all state variables each process needs to track
  type StateFields = {
    // TODO: Add your state fields here
    // For example:
    // phase: Phase,
    // value: Option[Value],
    // round: int,
  }

  // TODO: Define custom effects if your protocol needs them
  // Use () if you don't need custom effects
  type CustomEffects = ()
  // Alternative example:
  // type CustomEffects =
  //   | LogEvidence(Message)
  //   | UpdateMetrics(Node, int)

  // TODO: Define external events if your protocol uses them
  // Use () if you don't need external events
  type Event = ()
  // Alternative example:
  // type Event =
  //   | TimeoutEvent(int)
  //   | Restart

  // TODO: Define global extensions if needed
  // Use () if you don't need global extensions
  type Extensions = ()
  // Alternative example:
  // type Extensions = {
  //   global_round: int
  //   database_mock: str -> int
  // }

  // =============================================================================
  // BOILERPLATE (no need to modify - unless you rename something)
  // =============================================================================
  type LocalState = choreo::LocalState[Node, StateFields]
  type LocalContext = choreo::LocalContext[Node, StateFields, Message, Event, Extensions]
  type Transition = choreo::Transition[Node, StateFields, Message, Event, CustomEffects]
  type GlobalContext = choreo::GlobalContext[
    Node,
    StateFields,
    Message,
    Event,
    Extensions
  ]

  // =============================================================================
  // HELPER FUNCTIONS
  // =============================================================================

  // TODO: Add helper functions for message filtering, state predicates, etc.
  // Examples:

  // Extract specific message types from message set
  // pure def get_example_messages(messages: Set[Message]): Set[Node] = {
  //   messages.filterMap(m => match m {
  //     | ExampleMessage(node) => Some(node)
  //     | _ => None
  //   })
  // }

  // Calculate quorum size
  // pure def quorum_size(): int = {
  //   (NODES.size() * 2) / 3 + 1
  // }

  // =============================================================================
  // TRANSITION FUNCTIONS
  // =============================================================================

  // TODO: Implement your transition functions
  // Each transition function should:
  // 1. Check if the transition is applicable (guard condition)
  // 2. Return Set() if not applicable
  // 3. Return Set({ effects: ..., post_state: ... }) if applicable

  pure def example_transition(ctx: LocalContext): Set[Transition] = {
    // TODO: Add guard condition - when should this transition fire?
    if (true) {  // Replace with actual condition
      Set({
        // TODO: Define what effects this transition produces
        effects: Set(
          // Examples of effects:
          // choreo::Broadcast(ExampleMessage(ctx.state.process_id)),
          // choreo::Send({ to: "specific_node", message: ExampleMessage(ctx.state.process_id) }),
          // choreo::TriggerEvent(TimeoutEvent(ctx.state.round)),
          // choreo::CustomEffect(LogEvidence(msg))
        ),
        // TODO: Define the new state after this transition
        post_state: {
          ...ctx.state
          // Update specific fields:
          // phase: NewPhase,
          // round: ctx.state.round + 1
        }
      })
    } else {
      Set()  // No transition
    }
  }

  // TODO: Add more transition functions for your protocol
  // Examples:

  // pure def handle_vote_message(ctx: LocalContext): Set[Transition] = {
  //   // TODO: Implement vote handling
  //   Set()
  // }

  // pure def handle_timeout(ctx: LocalContext): Set[Transition] = {
  //   // TODO: Implement timeout handling
  //   Set()
  // }

  // pure def spontaneous_action(ctx: LocalContext): Set[Transition] = {
  //   // TODO: Implement actions that can happen without external triggers
  //   Set()
  // }

  // =============================================================================
  // MAIN LISTENER
  // =============================================================================

  // TODO: Combine all your transition functions in the main listener
  pure def main_listener(ctx: LocalContext): Set[Transition] = {
    Set(
      example_transition(ctx)
      // TODO: Add all your transition functions here:
      // handle_vote_message(ctx),
      // handle_timeout(ctx),
      // spontaneous_action(ctx)
    ).flatten()
  }

  // =============================================================================
  // CUSTOM EFFECT PROCESSOR (if needed)
  // =============================================================================

  // TODO: Implement custom effect processing if you defined CustomEffects
  // If CustomEffects = (), you can skip this
  pure def apply_custom_effect(
    ctx: GlobalContext,
    effect: CustomEffects
  ): GlobalContext = {
    // TODO: Handle your custom effects
    // match effect {
    //   | LogEvidence(msg) => {
    //     // Update global state based on effect
    //     ctx
    //   }
    //   | UpdateMetrics(node, value) => {
    //     // Update metrics
    //     ctx
    //   }
    // }
    ctx  // No-op if no custom effects
  }

  // =============================================================================
  // PROTOCOL CONFIGURATION
  // =============================================================================

  // TODO: Define your process set
  pure val NODES = Set("n1", "n2", "n3")  // Replace with your node set

  // TODO: Add any protocol-specific constants
  // Examples:
  // pure val COORDINATOR = "coordinator"
  // pure val PARTICIPANTS = Set("p1", "p2", "p3")
  // pure val INITIAL_VALUE = "default"
  // pure val TIMEOUT_DURATION = 10

  // =============================================================================
  // INITIALIZATION
  // =============================================================================

  // TODO: Define how to initialize each process's local state
  pure def initialize(n: Node): LocalState = {
    {
      process_id: n,
      // TODO: Initialize your state fields
      // phase: Init,
      // value: None,
      // round: 0,
    }
  }

  // TODO: Define initial global state
  action init = choreo::init({
    system: NODES.mapBy(n => initialize(n)),
    messages: NODES.mapBy(n => Set()),  // Or add initial messages if needed
    events: NODES.mapBy(n => Set()),    // Or add initial events if needed
    extensions: ()  // Or initialize your extensions
  })

  // =============================================================================
  // STEP FUNCTION
  // =============================================================================

  // TODO: Define how the system makes progress
  action step = choreo::step(
    main_listener,
    apply_custom_effect,  // Use (c, _) => c if no custom effects
    (e, p) => e          // Use your extensions converter if needed
  )

  // =============================================================================
  // PROPERTIES AND INVARIANTS
  // =============================================================================

  // TODO: Define invariants and properties for verification
  // Examples:

  // Safety property: agreement on decisions
  // val agreement = NODES.forall(n1 => {
  //   NODES.forall(n2 => {
  //     val state1 = s.system.get(n1)
  //     val state2 = s.system.get(n2)
  //     // TODO: Define your agreement condition
  //     true
  //   })
  // })


  // Validity property: only valid values are chosen
  // val validity = NODES.forall(n => {
  //   val state = s.system.get(n)
  //   // TODO: Define validity condition
  //   true
  // })

  // =============================================================================
  // TESTING AND DEBUGGING
  // =============================================================================

  // TODO: Add test scenarios and witnesses
  // Examples:

  // run myTest = init
  //   .then(step_with("n1", example_transition))
  //   .expect(s.system.get(n1).process_id == "n1")

  // =============================================================================
  // WIRING
  // =============================================================================

  // TODO: Add any additional utility functions specific to your protocol

  // Access global state
  val s = choreo::s

  // "Instantiate" the `step_with` operator with the extra types
  action step_with(v: Node, listener: LocalContext => Set[Transition]): bool =
    choreo::step_with(v, listener, apply_custom_effect, (e, p) => e)

  // TODO do the same for other step_ operators you want to use.
  // You can also create aliases for your convenience, like:
  // val ms = choreo::s.messages
 }

// =============================================================================
// INSTANCE MODULE (Optional)
// =============================================================================

// TODO: Create specific instances of your protocol for testing
// module test_instance {
//   // i.e. if you have `const NODES: Set[Node]` instead of `pure val NODES = ...`
//   import my_protocol(
//     NODES = Set("alice", "bob", "charlie")
//   ).* from "my_protocol"
// }
