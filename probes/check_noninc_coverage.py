#!/usr/bin/env python3
"""
Check: do the 4 mechanisms cover non-incrementing cycles too?

The mechanisms are about intervals where a proc doesn't fire.
They don't care about the specific transition values.

But our VERIFICATION only checked incrementing cycles.
Let's check non-incrementing ones.

At n=5, ms=[2,3,2,3,2]: generate cycles with ALL possible
transition behaviors (not just incrementing).

For non-incrementing: a ternary proc could do 0→2→0 or 1→0→1 etc.
"""
from itertools import product as iproduct
from collections import Counter

n = 5
ms = [2, 3, 2, 3, 2]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

# Generate cycles with ALL possible transition values
# At each step: mover p fires, changing c[p] to some value != c[p]
results = []
def dfs(word, vals, config):
    """word: mover sequence, vals: new values after fire, config: current"""
    if len(word) > 16: return
    if len(word) >= 2*n and config == start:
        # Check all procs fired at least once
        fired = set(word)
        if len(fired) == n:
            results.append((tuple(word), tuple(vals)))
        return
    remaining = 16 - len(word)
    if remaining < 1: return
    last = word[-1] if word else 0
    movers = ring_adj[last] if word else list(range(n))
    for nxt in movers:
        old_val = config[nxt]
        for new_val in range(ms[nxt]):
            if new_val == old_val: continue  # must change
            nc = list(config)
            nc[nxt] = new_val
            word.append(nxt)
            vals.append(new_val)
            dfs(word, vals, tuple(nc))
            word.pop()
            vals.pop()

# This is too slow for full enumeration. Let's just check: at n=5 with
# non-incrementing ternary transitions, do EC-free cycles exist?

# Simpler approach: enumerate mover words (nearest-neighbor walks),
# then for each word, try ALL possible value assignments
# Actually that's also huge.

# Simplest: just check a few specific non-incrementing cycles
# For example: ternary proc does 0→2→1→0 instead of 0→1→2→0

print("Checking specific non-incrementing cycles...")

def check_ec(word, configs):
    ell = len(word)
    for p in range(n):
        m_ctx, n_ctx = set(), set()
        for s in range(ell):
            ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: return True, p
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: return True, p
                n_ctx.add(ctx)
    return False, None

# Build a cycle manually with non-incrementing ternary
# Proc 1 (ternary): instead of 0→1→2→0, do 0→2→1→0
# This means fc=3 but the VALUES are 0,2,1 not 0,1,2

# Actually, the WORD (mover sequence) is the same — it's only the
# config values that differ. The word determines WHICH proc fires,
# not what value it transitions to.

# In the incrementing model: fire always does +1 mod m.
# In non-incrementing: fire can do any change.
# But in a GOOD CYCLE with entry conflict constraints:
# the transition function f_p is FIXED. So if p fires with context
# (L,S,R), the new value is always f_p(L,S,R).
# Different contexts can give different transitions.

# The key: for a FIXED transition function, each firing of p with
# context (L,S,R) produces the same output. So the cycle's config
# sequence is determined by the word + the transition functions.

# For the EC check: we DON'T need to know the transition function.
# We just need: does any (L,S,R) appear at p as both mover and nonmover?
# This is determined by the config sequence, which depends on the
# transition function.

# With non-incrementing transitions, the config sequence is different
# even for the same word. So the EC check gives different results.

# Let me generate ALL possible config sequences for a given word,
# trying all possible non-incrementing transition values.

# Take a specific word and check all possible value assignments
word = (0, 4, 3, 2, 3, 4, 3, 2, 1, 0, 1, 2, 1, 2)  # from our earlier data
ell = len(word)

print(f"Word: {word} (len={ell})")
print(f"Checking all possible transition value assignments...")

# For each step, the mover can transition to any value != current
# We need the cycle to close (return to start) and visit distinct configs

count_valid = 0
count_ec = 0
count_no_ec = 0

# This is exponential but let's try for small cases
# At each step, mover has (m_p - 1) choices. Total: prod of choices.
# For this word: binary procs have 1 choice, ternary have 2 choices.
# Number of ternary fires: count ternary movers in word
ternary_fires = sum(1 for s in range(ell) if ms[word[s]] == 3)
binary_fires = ell - ternary_fires
total_assignments = 2 ** ternary_fires  # each ternary fire has 2 choices
print(f"Ternary fires: {ternary_fires}, binary: {binary_fires}")
print(f"Total value assignments: {total_assignments}")

if total_assignments > 100000:
    print("Too many — sampling instead")
    import random
    sample_size = 10000
else:
    sample_size = total_assignments

# Enumerate
from itertools import product as iprod

# Build choice list: for each step, what values are possible?
choices = []
for s in range(ell):
    p = word[s]
    # We'll determine the current value dynamically
    choices.append(ms[p])  # m_p possible values, will filter != current

# Dynamic enumeration: build config sequence trying all ternary choices
ternary_step_indices = [s for s in range(ell) if ms[word[s]] == 3]
binary_step_indices = [s for s in range(ell) if ms[word[s]] == 2]

for combo in iprod(*[range(2) for _ in ternary_step_indices]):
    # combo[i] = which of the 2 non-current values to use for ternary fire i
    configs = [list(start)]
    valid = True
    for s in range(ell):
        p = word[s]
        cur = configs[-1][p]
        if ms[p] == 2:
            new_val = 1 - cur  # only option for binary
        else:
            # ternary: 2 choices (both != cur)
            options = [v for v in range(3) if v != cur]
            idx = ternary_step_indices.index(s)
            new_val = options[combo[idx]]
        nc = list(configs[-1])
        nc[p] = new_val
        configs.append(nc)

    # Check closure
    if tuple(configs[-1]) != start:
        continue
    # Check distinct configs
    config_set = set(tuple(c) for c in configs[:ell])
    if len(config_set) != ell:
        continue

    count_valid += 1
    has, p = check_ec(word, configs)
    if has:
        count_ec += 1
    else:
        count_no_ec += 1
        if count_no_ec <= 3:
            print(f"  NO EC: combo={combo}")

print(f"\nValid cycles: {count_valid}")
print(f"  With EC: {count_ec}")
print(f"  Without EC: {count_no_ec}")
if count_no_ec == 0 and count_valid > 0:
    print("*** ALL valid non-incrementing cycles have EC ***")
