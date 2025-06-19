def find_representative_traces(msgs, initial_state, receive_message):
    """
    Finds one representative trace per distinct final state
    by memoizing seen (used_messages, state) pairs.
    """
    seen = set()
    reps = {}

    def dfs(state, used, trace):
        key = (frozenset(used), state)
        if key in seen:
            return
        seen.add(key)

        # If all messages used, record this trace for the final state
        if len(used) == len(msgs):
            reps.setdefault(state, list(trace))
            return

        for m in msgs:
            if m not in used:
                new_state = receive_message(m, state)
                dfs(new_state, used | {m}, trace + [m])

    dfs(initial_state, set(), [])
    return reps

# Updated 'receive_message' function for BFT simulation
def receive_message(msg, state):
    # Simulate a simple BFT mechanism
    # Assume state is a tuple (current_value, votes)
    current_value, votes = state

    if msg == 'propose':
        # Propose a new value
        return (current_value + 1, votes)  # Increment value for simplicity
    elif msg == 'vote':
        # Vote for the current value
        votes += 1
        # Check if we have enough votes (e.g., 2/3 of total)
        if votes >= 2:  # Assuming 3 nodes for simplicity
            return (current_value, votes)  # Consensus reached
        return (current_value, votes)
    elif msg == 'commit':
        # Commit the current value
        return (current_value, 0)  # Reset votes after commit
    else:
        raise ValueError(f"Unknown message: {msg}")

# Define messages and initial state
messages = ['propose', 'vote', 'commit']
initial_state = (0, 0)  # Starting with value 0 and 0 votes

# Run the PoC
representatives = find_representative_traces(messages, initial_state, receive_message)
# All possible permutations of messages
from itertools import permutations
all_permutations = list(permutations(messages))

# Display the results
print("Representative trace for each final state:")
for final_state, trace in representatives.items():
    print(f"  Final state {final_state}: trace {trace}")
print("\nAll permutations of messages and their traces:")
for perm in all_permutations:
    trace = []
    state = initial_state
    for msg in perm:
        state = receive_message(msg, state)
        trace.append(msg)
    print(f"  {perm}: final {state}")
    