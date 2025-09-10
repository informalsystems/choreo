<div align="center">

<!-- Title -->
<picture>
  <source media="(prefers-color-scheme: dark)" srcset="./logos/choreo-logo-light.png">
  <img alt="Choreo" src="./logos/choreo-logo-dark.png" width=700>
</picture>

</div>

<br>

<div align="center">

# Choreograph Distributed Protocols

</div>

Choreo provides a structured foundation for writing distributed protocol specifications in [Quint](https://github.com/informalsystems/quint). Instead of starting with a blank file, you get a paved path with pre-built abstractions for message passing, state management, and common distributed systems patterns, all implementing the best techniques for modeling this type of system.

## Why use Choreo

When specifying distributed protocols in Quint, the same problems appear:
- How to represent message passing more efficiently?
- How to distinguish local state from global environment?
- How to represent timeouts?

Experience and research have led us to some answers:
- The [message soup technique](https://quint-lang.org/posts/soup) is the most efficient way of modeling exchange of messages
- Functions with proper interface help isolate local state manipulation and effects on the global environment without mixing them up and accidentally reading from global state.
- Timeouts are simply internal events that can be consumed at any point in the future

We learned this and this helps us write good specs. Choreo hands these techniques to you with a structured way to write specs.

Compare a [traditional Tendermint specification](https://github.com/informalsystems/quint/blob/main/examples/cosmos/tendermint/Tendermint.qnt) with its [Choreo version](examples/tendermint/tendermint.qnt) - the Choreo version focuses on protocol logic only, letting the framework handles the distributed systems mechanics in the best way we know.

## How Choreo looks like

Choreo provides ready-made abstractions that protocol designers can import and use immediately:

```bluespec
import choreo(processes = NODES) as choreo from "./choreo"
```

### Built-in Message Handling
Instead of manually managing message routing and filtering, define listeners that automatically trigger on relevant messages:
```bluespec
pure def listen_proposal_in_propose(ctx: LocalContext): Set[ProposeMsg] = {
  // Filter for relevant proposals
}

pure def broadcast_prevote_for_proposal(ctx: LocalContext, p: ProposeMsg): Transition = {
  // React to proposal
}

pure def main_listener(ctx: LocalContext): Set[Transition] = {
  Set(
    choreo::cue(ctx, listen_proposal_in_propose, broadcast_prevote_for_proposal),
    // other listeners
  )
}
```

### Structured State Transitions

This is what a `Transition` looks like:
```bluespec
{
  post_state: { ...s, stage: PreVoteStage },
  effects: Set(choreo::Broadcast(PreVote(message)))
}
```

Choreo ships some built-in effects like `choreo::Broadcast` which are handled automatically. You can define custom effects and provide a function on how to handle them as well.

### Environment Abstraction
The framework separates protocol logic from environmental concerns like network delays, message loss, and Byzantine behavior - letting you focus on the protocol correctness.

## Examples

- [Two-Phase Commit](examples/two_phase_commit/)
- [Tendermint](examples/tendermint/)
- [MonadBFT](examples/monadbft/)
- [Alpenglow](examples/alpenglow/)
