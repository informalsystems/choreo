module protocol {
    import basicSpells.* from "lib/basicSpells"

    import glyphNetwork as GNet from "lib/glyph"
    import glyphDriver as GD from "lib/glyph"
    import glyphsBase as GB from "lib/glyph"

    type Process = str

    /// Here we define the custom local state for each process
    type StateFields = {
        round: int,
        decision: Option[int],
        stage: Stage
    }

    /// Here we define the structure of the messages
    type Request = {
        some_value: int,
        other_value: str
    }

    type Response = {
        some_value: int,
        other_value: str
    }

    type Message = 
      | RequestMsg(Request)
      | ResponseMsg(Response)

    
    // Wire the custom state to the glyph
    type LocalState = GB::LocalState[Process, Message, StateFields]

    // Define the structure of your logging, logs are used for
    // debugging and for properties verification
    type Logging = {
        accepted_requests: Set[Request],
        sent_responses: Set[Response],
        decisions: Set[int]
    }

    // Now we define the global state of the system
    type GlobalState = GB::GlobalState[Process, LocalState, Message, Logging]



    // Define the rest of the types and data structures
    type Stage = 
      | Listen
      | Reply
    
    type SomeOtherType = {
        some_list: List[int],
    }


    // Now we define the effects: effects are the events that a node 
    // can create as a result of processing a message or an internal event.
    type ExternalEffect = 
      | SendResponse((Process, Response))
      | SendRequest((Process, Request))
      | BroadcastRequest(Request)

    type InternalEffect =
      | StartTimer(int)

    type LoggingEffect = 
      | LogAcceptedRequest(Request)
      | LogSentResponse(Response)
      | LogDecision(int)

    type Effect = 
      | Ext(ExternalEffect)
      | Inter(InternalEffect)
      | Log(LoggingEffect)

    // Now we wire the effects into the glyph to define the event handlers.
    // We start by defining the return type of the handlers called handler output.
    // The handler output is the result of processing a an event. 
    // It contains the new state and the effects that were produced.
    type HandlerOutput = GB::HandlerOutput[LocalState, Effect]

    // Now we will define the handlers, which constitute the core protocol logic.


    pure def handle_request(
        state: LocalState,
        request: Request
    ): HandlerOutput = {
        if (state.stage == Listen) {
            // Accept the request and move to the Reply stage
            val s1 = { ...state, stage: Reply, round: state.round + 1 }
            val resp = { some_value: request.some_value, other_value: request.other_value }
            val effects = Set(
                Ext(SendResponse((state.process_id, resp))),
                Log(LogAcceptedRequest(request))
            )
            { effects: effects, state: s1 }
        } else {
            // Ignore the request if not in Listen stage
            { effects: Set(), state: state }
        }
    }

    pure def handle_response(
        state: LocalState,
        response: Response
    ): HandlerOutput = {
        if (state.stage == Reply) {
            // Process the response and log it
            val s1 = { ...state, decision: Some(response.some_value) }
            val effects = Set(
                Log(LogDecision(response.some_value))
            )
            { effects: effects, state: s1 }
        } else {
            // Ignore the response if not in Reply stage
            { effects: Set(), state: state }
        }
    }

    // Define the receive message handler that routes messages to the appropriate handler
    pure def receive_message(
        state: LocalState,
        message: Message
    ): HandlerOutput = {
        match message {
            | RequestMsg(req) => handle_request(state, req)
            | ResponseMsg(resp) => handle_response(state, resp)
        }
    }

    // Define how each effect is applied to the global state
    // This can be skipped if you want to compress everything into the same apply_effect function
    pure def apply_broadcast_request(
        env: GlobalState,
        request: Request
    ): GlobalState = {
        GNet::broadcast(env, RequestMsg(request))
    }
    pure def apply_send_response(
        env: GlobalState,
        process: Process,
        response: Response
    ): GlobalState = {
        GNet::send(env, process, ResponseMsg(response))
    }
    pure def apply_send_request(
        env: GlobalState,
        process: Process,
        request: Request
    ): GlobalState = {
        GNet::send(env, process, RequestMsg(request))   
    }

    pure def apply_start_timer(
        env: GlobalState,
        duration: int
    ): GlobalState = {
        env
    }

    // Define the effect router that applies the effects to the global state
    pure def apply_effect(
        env: GlobalState,
        effect: Effect
    ): GlobalState = 
        match effect {
            | Ext(ee) => 
                match ee {
                    | SendResponse(r) => apply_send_response(env, r._1, r._2)
                    | SendRequest(r) => apply_send_request(env, r._1, r._2)
                    | BroadcastRequest(request) => apply_broadcast_request(env, request)
                }
    
            | Inter(ie)
                => match ie {
                    | StartTimer(duration) => apply_start_timer(env, duration)
                }
            | Log(le)
                => match le {
                    | LogAcceptedRequest(request) => { ...env, logging: { ...env.logging, accepted_requests: env.logging.accepted_requests.setAdd(request) } }
                    | LogSentResponse(response) => { ...env, logging: { ...env.logging, sent_responses: env.logging.sent_responses.setAdd(response) } }
                    | LogDecision(decision) => { ...env, logging: { ...env.logging, decisions: env.logging.decisions.setAdd(decision) } }
                }
        }
    
    pure def apply_effects(
        env: GlobalState,
        process_id: Process,
        effects: Set[Effect]
    ): GlobalState = {
        effects.fold(env, (acc, effect) => apply_effect(acc, effect))
    }



    // Define an initialize function to set up the initial state of the system
    pure def initialize_process(
        process_id: Process,
    ): LocalState = 
        { process_id: process_id, round: 0, decision: None, stage: Listen , message_buffer: Set() }
    
    // define the initial logging state
    pure val initial_logging: Logging = {
        accepted_requests: Set(),
        sent_responses: Set(),
        decisions: Set()
    }

    // wire the glyph driver into the protocol
    action init = GD::init(
        initialize_process,
        initial_logging
    )
    action step = GD::step(
        receive_message,
        apply_effects
    )

}