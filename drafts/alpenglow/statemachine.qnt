    // -*- mode: Bluespec; -*-

module statemachine {
    import basicSpells.* from "lib/basicSpells"


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
    /// 4. `te` is the type of the timeout events
    /// 5. `b` is the type of the bookkeeping
    ///
    /// Use it like:
    /// ```
    /// type ProcessID = int
    /// type State = { field1: int, field2: str }
    /// type Message =
    ///   | Hello(int)
    ///   | Bye(str)
    /// type TimeoutEvent = int
    /// type Bookkeeping = { foo: int, bar: str }
    /// type Environment = CSMI::Environment[ProcessID, State, Message, TimeoutEvent, Bookkeeping]
    /// ```
    type Environment[p, s, m, te, l, extensions] = {
        system: p -> LocalState[p, s],
        msgBuffer: p -> Set[m],
        internalBuffer: p -> Set[te],
        logging: l
        | extensions
    }


    type Transition[state, effect] = {
        effects: Set[effect],
        postState: state,
    }
    type Transitions[tr] = Set[tr]
    type LocalContext[m, te, extensions] = {
        msgBuffer: Set[m], 
        internalBuffer: Set[te] 
        | extensions
        } 

    type ContextBuilder[p, s, m, te, l, other] = (Environment[p, s, m, te, l, other],p) => LocalContext[m, te, other]
    type Listener[p, s, m, te, l, other] = (LocalState[p, s], LocalContext[m, te, other]) => Transitions
    type EffectProcessor[p, s, m, te, l, other] = (Environment[p, s, m, te, l, other], p, Transition) => Environment[p, s, m, te, l, other]
    type Displayer[p,s,m, te, l, extensions, d] = (Environment[p, s, m, te, l, extensions]) => d 
    

    type Event[m,te] = Ext(m) | Inter(te)
    type LocalContextF[m, te, extensions] = {
        event: Event[m, te]| extensions
    }
    type ContextBuilderF[p, s, m, te, l, extensions] = (Environment[p, s, m, te, l, extensions], p, Event[m,te]) => LocalContextF[m, te, extensions]
    type Handler[p, s, m, te, l, extensions] = (LocalState[p, s], LocalContextF[m, te, extensions]) => Transition[s, m]

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

    action init(
        initialize_processes: (p) => LocalState[p, s],
        initial_msgBuffer: (p) => Set[m],
        initial_internalBuffer: (p) => Set[te],
        env : Environment[p, s, m, te, l, extensions],
        byzNetworkMsgs: Set[m],
    ):bool = all{
        s' =  { ... env,
            system: processes.mapBy(initialize_processes),
            msgBuffer: processes.mapBy(initial_msgBuffer),
            internalBuffer: processes.mapBy(initial_internalBuffer),
        },
        byzNetworkMsgs' = byzNetworkMsgs,

    }

    action init_basic(
        env: Environment[p, s, m, te, l, extensions],
        byzNetworkMsgs: Set[m],
    )
    : bool = all {
        s' = env,
        byzNetworkMsgs' = byzNetworkMsgs,
        processes.size() > 0, // we have at least one process
    }

   
    /// Main step action. Includes all behavior
    action step (
        listener: Listener[p, s, m, te, l, extensions],
        apply_effect: EffectProcessor[p, s, m, te, l, extensions],
        context: ContextBuilder[p, s, m, te, l, extensions],
        displayer : Displayer[p, s, m, te, l, extensions, d],
        more_byzantines: Set[m]
    ):bool = all {
        {
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
                    display' = displayer(post_env)
                    }
            }
        }
    }

    action stepF(
        handler: Handler[p, s, m, te, l, extensions],
        apply_effect: EffectProcessor[p, s, m, te, l, extensions],
        context: ContextBuilderF[p, s, m, te, l, extensions],
        displayer : Displayer[p, s, m, te, l, extensions, d],
        more_byzantines: Set[m]
    ):bool = all {
        {
            nondet v = oneOf(processes)
            val events = s.msgBuffer.get(v).map(e => Ext(e)).union(s.internalBuffer.get(v).map(e => Inter(e)))
            nondet event = oneOf(events)
            val input = context(s, v, event)
            val ls = s.system.get(v)
            val transition = handler(ls, input)
            val post_env = apply_effect(s, v, transition)
            all {
                s' = post_env,
                display' = displayer(post_env),
            }
        }
    }  

}


