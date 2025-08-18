// -*- mode: Bluespec; -*-

module csmi {
    import basicSpells.* from "basicSpells"


    /// Given a type for identifying process and a record type to represent a state,
    /// Create a record type with the `process_id` and remaining fields.
    ///
    /// Use it like:
    /// ```
    /// type ProcessID = int
    /// type State = { field1: int, field2: str }
    /// type LocalState = CSMI::LocalState[ProcessID, State]
    /// ```
    type LocalState[process_id, other_fields] = { process_id: process_id | other_fields}

    /// Given several type definitions, create a type to represent the environment of a consensus
    /// state machine.
    ///
    /// 1. `p` is the type of the process identifier
    /// 2. `s` is the type of the state
    /// 3. `m` is the type of the messages
    /// 4. `te` is the type of the internal events
    /// 5. `l` is the type of the logging information
    /// 6. `extensions` is a type that can be used to extend the environment
    ///
    /// Use it like:
    /// ```
    /// type ProcessID = int
    /// type State = { field1: int, field2: str }
    /// type Message =
    ///   | Hello(int)
    ///   | Bye(str)
    /// type TimeoutEvent = int
    /// type Logging = { foo: int, bar: str }
    /// type EnvExtensions = { baz: bool }
    /// type Environment = CSMI::Environment[ProcessID, State, Message, TimeoutEvent, Logging, EnvExtensions]
    /// ```
    type Environment[p, s, m, te, l, extensions] = {
        system: p -> LocalState[p, s],
        msgBuffer: p -> Set[m],
        internalBuffer: p -> Set[te],
        logging: l
        | extensions
    }

    /// Given a type for the Local State and a type for Effects (Effects are the
    /// used by a process to change the state of the system, e.g sending a message, updating a mock variable, etc.),
    /// create a type to represent a state machine transition.
    /// The transition is a record type that contains:
    /// 1. `effects` is a set of effects that the transition produces
    /// 2. `postState` is the state that the transition leads to.
    /// Use it like:
    /// ```
    /// type LocalState = CSMI::LocalState[ProcessID, State]
    /// type Effect = SendMessage(Message) | UpdateVariable(str, int)
    /// type Transition = CSMI::Transition[LocalState, Effect]
    /// ```
    ///

    type Transition[state, effect] = {
        effects: Set[effect],
        postState: state,
    }

    /// Given a type for a single transition, create a type to represent a set of transitions.
    type Transitions[tr] = Set[tr]

    /// Given several type definitions, create a type to represent the local context of a process.
    /// The local context represents a process's view of the system. It may include: the set of received messages, the set of internal events, and any other extensions that are needed.
    /// the set of internal events, and any other extensions that are needed.
    /// Local Contexts are used as input to the event listeners and message handlers.
    /// Use it like:
    /// ```
    /// type LocalContext = CSMI::LocalContext[Message, InternalEvent, SomeExtension]
    type LocalContext[m, te, extensions] = {
        msgBuffer: Set[m],
        internalBuffer: Set[te]
        | extensions
        }

    /// A context builder is a function that takes  an environment and a process identifier,
    /// and returns a local context for that process.
    /// After type instantiation, it should have the following signature:
    /// ```
    /// (Environment, ProcessID) => LocalContext
    /// ```
    type ContextBuilder[p, s, m, te, l, other] = (Environment[p, s, m, te, l, other],p) => LocalContext[m, te, other]

    /// A listener is a function that takes a local state and a local context, and returns a set of transitions.
    /// After type instantiation, it should have the following signature:
    /// ```
    /// (LocalState, LocalContext) => Transitions
    /// ```
    type Listener[p, s, m, te, l, other] = (LocalState[p, s], LocalContext[m, te, other]) => Transitions

    /// An effect processor is a function that takes an environment, a process identifier, and a transition,
    /// and returns a new environment after applying the effects of the transition.
    /// After type instantiation, it should have the following signature:
    /// ```
    /// (Environment, ProcessID, Transition) => Environment
    /// ```
    type EffectProcessor[p, s, m, te, l, other] = (Environment[p, s, m, te, l, other], p, Transition) => Environment[p, s, m, te, l, other]

    /// A displayer is a function that takes an environment and returns a displayable representation of the environment.
    /// This is used to visualize the state of the system for debugging or monitoring purposes.
    /// After type instantiation, it should have the following signature:
    /// ```
    /// (Environment) => Display
    /// ```
    /// The display type can be anything.
    type Displayer[p,s,m, te, l, extensions, d] = (Environment[p, s, m, te, l, extensions]) => d



    const processes: Set[p]
    /// A single variable to store the whole state
    var s: Environment[p, s, m, te, l, extensions]
    var display: d
    var byzNetworkMsgs: Set[m]


    // Symmetry Reduction Interface
    // TODO: expose the symmetry reduction interface



    //
    //
    // State Machine Actions
    //
    //

    /// Initialize the state machine with a set of processes, an initial environment, and a set of byzantine messages.
    /// The `initialize_processes` function is used to initialize the local state of each process
    /// The `initial_msgBuffer` function is used to initialize the message buffer of each process
    /// The `initial_internalBuffer` function is used to initialize the internal buffer of each process
    /// The `env` parameter is the initial environment of the system and will be used as a starting point
    /// for initializing the whole system.
    /// The `byzNetworkMsgs` parameter is a set of byzantine messages that will be injected into the message buffer of the system.
    /// Use it like:
    /// ```
    /// pure def initialize_processes(p: ProcessID): LocalState[ProcessID, State] = { process_id: p, field1: 0, field2: "" }
    /// pure def initial_msgBuffer(p: ProcessID): Set[Message] = Set()
    /// pure def initial_internalBuffer(p: ProcessID): Set[TimeoutEvent] = Set(Timeout(1))
    /// pure val init_env = { system: Map(), msgBuffer: Map(), internalBuffer: Map(), logging: { foo: 0, bar: "" } | { baz: true } }
    /// pure val byz_msgs = Set(Hello(1), Bye("test"))
    /// action init = csmi::init(
    ///     initialize_processes,
    ///     initial_msgBuffer,
    ///     initial_internalBuffer,
    ///     init_env,
    ///     byz_msgs
    /// )
    /// ```
    action init(
        initialize_processes: (p) => LocalState[p, s],
        initial_msgBuffer: (p) => Set[m],
        initial_internalBuffer: (p) => Set[te],
        env : Environment[p, s, m, te, l, extensions],
        displayer : Displayer[p, s, m, te, l, extensions, d],
    ):bool = {
        val e = { ... env,
            system: processes.mapBy(initialize_processes),
            msgBuffer: processes.mapBy(initial_msgBuffer),
            internalBuffer: processes.mapBy(initial_internalBuffer),
        }
        all {
          s' = e,
          // display' = displayer(e),
        }
    }

    /// Initialize the state machine with an environment and a set of byzantine messages.
    /// the `env` parameter is the initial environment of the system.
    /// The `byzNetworkMsgs` parameter is a set of byzantine messages that will be injected into the message buffer of the system.
    /// Use it like:
    /// ```
    /// pure val init_env = { system: Map(), msgBuffer: Map(), internalBuffer: Map(), logging: { foo: 0, bar: "" } | { baz: true } }
    /// pure val byz_msgs = Set(Hello(1), Bye("test"))
    /// action init = csmi::init_basic(init_env, byz_msgs)
    /// ```
    action init_basic(
        env: Environment[p, s, m, te, l, extensions],
        byzNetworkMsgs: Set[m],
    )
    : bool = all {
        s' = env,
        byzNetworkMsgs' = byzNetworkMsgs,
        processes.size() > 0, // we have at least one process
    }


    /// Given a set of pure functions, apply a single step of the state machine.
    /// The `listener` function listens to the local state and the local context of a process, and returns a set of transitions.
    /// The `apply_effect` function applies the effects of a transition to the environment and returns the new environment.
    /// The `context` function builds a local context for a process given the environment and the process identifier.
    /// The `displayer` function displays the current state of the system.
    /// The `more_byzantines` parameter is a set of byzantine messages that will be injected into the message buffer of the system.
    /// Use it like:
    /// ```
    /// action step = csmi::step(
    ///     listener,
    ///     apply_effect,
    ///     context,
    ///     displayer,
    ///     more_byzantines
    /// )
    /// ```
    action step (
        listener: Listener[p, s, m, te, l, extensions],
        apply_effect: EffectProcessor[p, s, m, te, l, extensions],
        context: ContextBuilder[p, s, m, te, l, extensions],
        displayer : Displayer[p, s, m, te, l, extensions, d],
        more_byzantines: Set[m]
    ):bool = all {
        any {
            nondet v = oneOf(processes)
            val input = context(s, v)
            val ls = s.system.get(v)
            val transitions = listener(ls, input)
            all {
                transitions.size() > 0, // we have a transition to apply
                nondet transition = oneOf(transitions)
                val post_env = apply_effect(s, v, transition)
                all{
                    s' = post_env,
                    // display' = displayer(post_env)
                    }
            },
        }
    }

}
