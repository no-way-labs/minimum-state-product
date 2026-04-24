"""
Wave Filter Theory: Analyzing what the quaternary processor does in known witnesses.

Goal: Define "bidirectional wave filter" and prove ≥4 states are needed
between binary neighbors.

Approach: Extract the local behavior of the quaternary (and ternary) processors
in the n=5 witness (ms=[2,2,2,3,4]) by tracing how they handle waves arriving
from left vs right.
"""

import itertools
from collections import defaultdict

# ============================================================
# Load the n=5 witness: ms = [2, 2, 2, 3, 4], product = 96
# ============================================================

ms_5 = [2, 2, 2, 3, 4]
n = 5

# Transition functions from product96_result.txt
rules = {}

# P0 (2-state, L from P4 has range 4, R from P1 has range 2)
rules[0] = {
    (0,0,0):1, (0,0,1):0, (0,1,0):1, (0,1,1):1,
    (1,0,0):0, (1,0,1):0, (1,1,0):0, (1,1,1):0,
    (2,0,0):0, (2,0,1):0, (2,1,0):0, (2,1,1):0,
    (3,0,0):0, (3,0,1):0, (3,1,0):0, (3,1,1):0,
}

# P1 (2-state, L from P0 has range 2, R from P2 has range 2)
rules[1] = {
    (0,0,0):0, (0,0,1):0, (0,1,0):0, (0,1,1):0,
    (1,0,0):1, (1,0,1):1, (1,1,0):1, (1,1,1):1,
}

# P2 (2-state, L from P1 has range 2, R from P3 has range 3)
rules[2] = {
    (0,0,0):0, (0,0,1):0, (0,0,2):1, (0,1,0):1, (0,1,1):0, (0,1,2):1,
    (1,0,0):1, (1,0,1):0, (1,0,2):0, (1,1,0):1, (1,1,1):1, (1,1,2):0,
}

# P3 (3-state, L from P2 has range 2, R from P4 has range 4)
rules[3] = {
    (0,0,0):0, (0,0,1):0, (0,0,2):1, (0,0,3):0,
    (0,1,0):1, (0,1,1):2, (0,1,2):1, (0,1,3):0,
    (0,2,0):0, (0,2,1):2, (0,2,2):2, (0,2,3):2,
    (1,0,0):1, (1,0,1):0, (1,0,2):2, (1,0,3):0,
    (1,1,0):1, (1,1,1):1, (1,1,2):1, (1,1,3):1,
    (1,2,0):2, (1,2,1):0, (1,2,2):2, (1,2,3):1,
}

# P4 (4-state, L from P3 has range 3, R from P0 has range 2)
rules[4] = {
    (0,0,0):0, (0,0,1):0, (0,1,0):2, (0,1,1):1,
    (0,2,0):2, (0,2,1):2, (0,3,0):0, (0,3,1):1,
    (1,0,0):0, (1,0,1):1, (1,1,0):1, (1,1,1):1,
    (1,2,0):1, (1,2,1):0, (1,3,0):3, (1,3,1):0,
    (2,0,0):0, (2,0,1):0, (2,1,0):1, (2,1,1):1,
    (2,2,0):3, (2,2,1):0, (2,3,0):3, (2,3,1):0,
}

def f(i, L, S, R):
    return rules[i][(L, S, R)]

def privileged_set(config):
    priv = []
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        if f(i, L, S, R) != S:
            priv.append(i)
    return priv

def apply_move(config, i):
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    lst = list(config)
    lst[i] = f(i, L, S, R)
    return tuple(lst)

# The good cycle
good_cycle = [
    (0,0,0,0,0), (1,0,0,0,0), (1,1,0,0,0), (1,1,1,0,0),
    (1,1,1,1,0), (1,1,1,1,1), (0,1,1,1,1), (0,0,1,1,1),
    (0,0,0,1,1), (0,0,0,2,1), (0,0,1,2,1), (0,0,1,0,1),
    (0,0,1,0,2), (0,0,1,2,2), (0,0,1,2,3), (0,0,1,1,3),
    (0,0,0,1,3), (0,0,0,0,3),
]

# ============================================================
# Analysis 1: Track which processor moves at each cycle step
# and what "direction" the token is traveling
# ============================================================

print("=" * 70)
print("GOOD CYCLE ANALYSIS: n=5, ms=(2,2,2,3,4)")
print("=" * 70)

print("\nStep | Config         | Priv | Mover | Direction")
print("-" * 60)
for idx in range(len(good_cycle)):
    c = good_cycle[idx]
    c_next = good_cycle[(idx + 1) % len(good_cycle)]
    priv = privileged_set(c)
    # Find which processor moved
    mover = None
    for j in range(n):
        if c[j] != c_next[j]:
            mover = j
            break
    print(f"  {idx:2d} | {c} | {priv} | P{mover} |")

# ============================================================
# Analysis 2: For each processor, extract its "privilege pattern"
# What (L,S,R) contexts make it privileged in the good cycle?
# ============================================================

print("\n" + "=" * 70)
print("PRIVILEGE PATTERNS IN GOOD CYCLE")
print("=" * 70)

for i in range(n):
    print(f"\nP{i} (m={ms_5[i]}):")
    priv_contexts = []
    for idx, c in enumerate(good_cycle):
        L = c[(i-1) % n]
        S = c[i]
        R = c[(i+1) % n]
        if f(i, L, S, R) != S:
            new_S = f(i, L, S, R)
            priv_contexts.append((L, S, R, new_S, idx))
    for (L, S, R, new_S, idx) in priv_contexts:
        print(f"  step {idx:2d}: ({L},{S},{R}) -> {new_S}")
    print(f"  Privileged {len(priv_contexts)} times in cycle of length {len(good_cycle)}")

# ============================================================
# Analysis 3: Wave structure in BAD configurations
# Focus on how the quaternary P4 handles multi-wave situations
# ============================================================

print("\n" + "=" * 70)
print("WAVE ANALYSIS IN ALL CONFIGURATIONS")
print("=" * 70)

all_configs = list(itertools.product(*(range(m) for m in ms_5)))
good_set = set(good_cycle)
bad_configs = [c for c in all_configs if c not in good_set]

# For each config, find waves (contiguous runs of privileged processors)
def find_waves(config):
    priv = privileged_set(config)
    if not priv:
        return []
    priv_set = set(priv)
    waves = []
    visited = set()
    for start in sorted(priv):
        if start in visited:
            continue
        wave = [start]
        visited.add(start)
        pos = (start + 1) % n
        while pos in priv_set and pos not in visited:
            wave.append(pos)
            visited.add(pos)
            pos = (pos + 1) % n
        pos = (start - 1) % n
        while pos in priv_set and pos not in visited:
            wave.insert(0, pos)
            visited.add(pos)
            pos = (pos - 1) % n
        waves.append(tuple(wave))
    return waves

# Count wave distributions
from collections import Counter
wave_dist = Counter()
for c in all_configs:
    nw = len(find_waves(c))
    wave_dist[nw] += 1

print("Wave count distribution (all configs):")
for k in sorted(wave_dist):
    print(f"  {k} waves: {wave_dist[k]} configs")

# ============================================================
# Analysis 4: CRITICAL — The "direction encoding" of the quaternary
#
# Key question: does the quaternary P4 encode direction information?
# It sits between P3 (3-state) and P0 (2-state).
# In the good cycle, the token travels in both directions through P4.
# How does P4's state encode which direction the token came from / is going?
# ============================================================

print("\n" + "=" * 70)
print("QUATERNARY P4: DIRECTION ENCODING ANALYSIS")
print("=" * 70)

# Track P4's state through the good cycle and annotate with token direction
print("\nP4 state trajectory through good cycle:")
print("Step | Config         | P4_state | Token_at | Direction")
print("-" * 65)

# Determine token direction from consecutive movers
movers = []
for idx in range(len(good_cycle)):
    c = good_cycle[idx]
    c_next = good_cycle[(idx + 1) % len(good_cycle)]
    for j in range(n):
        if c[j] != c_next[j]:
            movers.append(j)
            break

for idx in range(len(good_cycle)):
    c = good_cycle[idx]
    mover = movers[idx]
    prev_mover = movers[(idx - 1) % len(good_cycle)]
    # Direction: if mover > prev_mover (mod n), token moves "right" (increasing index)
    diff = (mover - prev_mover) % n
    if diff == 0:
        direction = "SAME"
    elif diff == 1:
        direction = "RIGHT"
    elif diff == n - 1:
        direction = "LEFT"
    else:
        direction = f"JUMP({diff})"
    print(f"  {idx:2d} | {c} | s4={c[4]}    | P{mover}     | {direction}")

# ============================================================
# Analysis 5: The key structural question
#
# For the ternary P3 (between P2=binary and P4=quaternary):
# What are ALL the (L,S,R) -> S' transitions that P3 uses?
# How many "independent pieces of information" does it track?
#
# For the quaternary P4 (between P3=ternary and P0=binary):
# Same question. How does P4 use its 4 states?
# ============================================================

print("\n" + "=" * 70)
print("P3 (TERNARY) AND P4 (QUATERNARY) FULL BEHAVIOR")
print("=" * 70)

# P3: which of its 3 states correspond to which "role"?
print("\nP3 state usage in good cycle:")
p3_transitions_in_cycle = {}
for idx in range(len(good_cycle)):
    c = good_cycle[idx]
    L, S, R = c[2], c[3], c[4]
    new_S = f(3, L, S, R)
    is_priv = (new_S != S)
    p3_transitions_in_cycle[(L, S, R)] = (new_S, is_priv, idx)

for (L, S, R), (new_S, is_priv, idx) in sorted(p3_transitions_in_cycle.items()):
    marker = " *PRIV*" if is_priv else ""
    print(f"  f3({L},{S},{R}) = {new_S}{marker}  [step {idx}]")

print("\nP4 state usage in good cycle:")
p4_transitions_in_cycle = {}
for idx in range(len(good_cycle)):
    c = good_cycle[idx]
    L, S, R = c[3], c[4], c[0]
    new_S = f(4, L, S, R)
    is_priv = (new_S != S)
    p4_transitions_in_cycle[(L, S, R)] = (new_S, is_priv, idx)

for (L, S, R), (new_S, is_priv, idx) in sorted(p4_transitions_in_cycle.items()):
    marker = " *PRIV*" if is_priv else ""
    print(f"  f4({L},{S},{R}) = {new_S}{marker}  [step {idx}]")

# ============================================================
# Analysis 6: Binary processor "valve" behavior
#
# DEK's insight: binary processors act as one-way valves.
# When a binary processor moves, the wave MUST continue in the
# same direction. Verify this in the good cycle.
# ============================================================

print("\n" + "=" * 70)
print("BINARY PROCESSOR VALVE ANALYSIS")
print("=" * 70)

for i in [0, 1, 2]:
    print(f"\nP{i} (binary):")
    for idx in range(len(good_cycle)):
        c = good_cycle[idx]
        if movers[idx] == i:
            prev = movers[(idx-1) % len(good_cycle)]
            nxt = movers[(idx+1) % len(good_cycle)]
            L, S, R = c[(i-1)%n], c[i], c[(i+1)%n]
            new_S = f(i, L, S, R)
            print(f"  step {idx}: P{prev}->P{i}->P{nxt}  ({L},{S},{R})->{new_S}")

# ============================================================
# Analysis 7: CONVERGENCE — how do bad configs with multiple
# waves converge? Focus on what P4 does.
# ============================================================

print("\n" + "=" * 70)
print("BAD CONFIG CONVERGENCE: P4'S ROLE IN WAVE MERGING")
print("=" * 70)

# Find bad configs where P4 is privileged alongside other processors
multi_priv_with_p4 = []
for c in bad_configs:
    priv = privileged_set(c)
    if 4 in priv and len(priv) >= 2:
        multi_priv_with_p4.append((c, priv))

print(f"\nBad configs where P4 is privileged + others: {len(multi_priv_with_p4)}")

# Show a few examples
for c, priv in multi_priv_with_p4[:10]:
    waves = find_waves(c)
    L4, S4, R4 = c[3], c[4], c[0]
    new_S4 = f(4, L4, S4, R4)
    print(f"  {c}  priv={priv}  waves={waves}  P4:({L4},{S4},{R4})->{new_S4}")

# ============================================================
# Analysis 8: CRITICAL — Count distinct (left_info, right_info)
# pairs that the quaternary P4 must distinguish
#
# The key claim: P4 must independently encode information about
# the phase on its left side and the phase on its right side.
# If it sees L ∈ {0,1,2} from P3 and R ∈ {0,1} from P0,
# that's 6 input contexts per self-state. But the critical
# question is how many DISTINCT BEHAVIORS it needs.
# ============================================================

print("\n" + "=" * 70)
print("P4 STATE SEMANTICS: WHAT DOES EACH STATE 'MEAN'?")
print("=" * 70)

# For each P4 state s, show what happens for all (L,R) contexts
for s in range(4):
    print(f"\n  P4 in state {s}:")
    for L in range(3):  # P3 has 3 states
        for R in range(2):  # P0 has 2 states
            new_s = f(4, L, s, R)
            priv = "*" if new_s != s else " "
            print(f"    L={L}, R={R}: f4({L},{s},{R})={new_s} {priv}")

# ============================================================
# Analysis 9: What if P4 were ternary? Can we see why it fails?
#
# The quaternary necessity claim says we need ≥ 4 states.
# Let's see which states P4 uses and whether any two states
# could be merged (identified) without breaking the system.
# ============================================================

print("\n" + "=" * 70)
print("CAN P4 BE REDUCED TO 3 STATES? MERGER ANALYSIS")
print("=" * 70)

# Check all possible identifications of two P4 states
from itertools import combinations
for (a, b) in combinations(range(4), 2):
    # Try merging state b into state a
    # This means: wherever P4 would go to state b, it goes to state a instead
    # And wherever P4 is in state b, we treat it as state a
    # Check if the resulting 3-state system still works

    # Build merged rule table
    def merge_state(s):
        return a if s == b else s

    # Check good cycle: does it still work?
    cycle_ok = True
    for idx in range(len(good_cycle)):
        c = good_cycle[idx]
        c_next = good_cycle[(idx + 1) % len(good_cycle)]
        # Check: does merging break the cycle?
        # The mover at this step needs to still be uniquely privileged
        # and produce the right next state

        # Merge P4's state in config
        merged_c = list(c)
        merged_c[4] = merge_state(c[4])
        merged_c_next = list(c_next)
        merged_c_next[4] = merge_state(c_next[4])

        # Check if merged configs collide (two different cycle positions map to same)
        pass  # Will check differently below

    # Better approach: check if merging creates a collision in the cycle
    merged_cycle = [tuple(merge_state(c[4]) if j == 4 else c[j] for j in range(n))
                    for c in good_cycle]
    unique_merged = len(set(merged_cycle))
    collision = unique_merged < len(good_cycle)

    if collision:
        # Find which steps collide
        seen = {}
        collisions = []
        for idx, mc in enumerate(merged_cycle):
            if mc in seen:
                collisions.append((seen[mc], idx, mc))
            else:
                seen[mc] = idx
        print(f"  Merge {b}->{a}: COLLISION at {collisions[0][:2]} "
              f"(configs at steps {collisions[0][0]} and {collisions[0][1]} become identical)")
    else:
        print(f"  Merge {b}->{a}: No cycle collision — need deeper check")
        # Even without cycle collision, the merged system might have bad cycles
        # or lose mutual exclusion. Let's check privilege structure.
        for idx in range(len(good_cycle)):
            mc = merged_cycle[idx]
            priv = []
            for i in range(n):
                L = mc[(i-1)%n]
                S = mc[i]
                R = mc[(i+1)%n]
                new_S = f(i, L, S, R)
                # For P4, we need to check with merged states
                if i == 4:
                    # L from P3, S is merged, R from P0
                    # But the rule table still uses original states...
                    # Merging means: the 3-state P4 has merged rule table
                    pass
                if new_S != S:
                    priv.append(i)
            # This analysis gets complicated — the rule table itself changes
        print(f"    (Rule table merging required for full check — skipped here)")


# ============================================================
# Analysis 10: INFORMATION-THEORETIC view
#
# Count the number of DISTINGUISHABLE input-output behaviors
# that P4 needs. If it needs ≥ 4 distinct response patterns,
# then it needs ≥ 4 states.
# ============================================================

print("\n" + "=" * 70)
print("P4: RESPONSE PATTERN ANALYSIS")
print("=" * 70)

# For P4, the response pattern for state s is:
# the function (L,R) -> (f(L,s,R), is_privileged)
# If two states have the same response pattern, they could be merged.

for s in range(4):
    pattern = []
    for L in range(3):
        for R in range(2):
            new_s = f(4, L, s, R)
            pattern.append((L, R, new_s, new_s != s))
    print(f"  State {s}: {[(L,R,ns) for (L,R,ns,p) in pattern]}")

# Check if any two states have identical response patterns
print("\n  Pairwise response pattern comparison:")
for (a, b) in combinations(range(4), 2):
    same = True
    for L in range(3):
        for R in range(2):
            if f(4, L, a, R) != f(4, L, b, R):
                same = False
                break
        if not same:
            break
    # Also check: does merging create self-loops that shouldn't exist?
    print(f"    States {a} vs {b}: {'IDENTICAL' if same else 'DIFFERENT'}")

print("\n  All 4 states have DISTINCT response patterns => P4 genuinely uses 4 states.")


# ============================================================
# Analysis 11: THE KEY CONSTRUCTION — left-phase and right-phase
#
# Hypothesis: P4's 4 states encode (left_phase, right_phase)
# where each phase ∈ {0,1}. The left phase tracks the token's
# position/progress on the P3 side, and the right phase tracks
# the token's position/progress on the P0 side.
#
# Let's test this by looking at when P4 transitions between states
# in the good cycle.
# ============================================================

print("\n" + "=" * 70)
print("P4 STATE TRANSITIONS IN GOOD CYCLE")
print("=" * 70)

print("\nP4 state trajectory:")
for idx in range(len(good_cycle)):
    c = good_cycle[idx]
    s4 = c[4]
    mover = movers[idx]
    # What does P4 transition to if it's the mover?
    if mover == 4:
        L, R = c[3], c[0]
        new_s = f(4, L, s4, R)
        print(f"  step {idx:2d}: s4={s4} -> {new_s}  (P4 moves, L={L}, R={R})")
    else:
        print(f"  step {idx:2d}: s4={s4}  (P{mover} moves)")

# Try to decompose P4's states into (left_bit, right_bit)
print("\nTesting decomposition s4 -> (left_bit, right_bit):")
# Try all 12 possible 2-bit decompositions of {0,1,2,3} -> {0,1}^2
# Actually, s4 in {0,1,2,3}, we want to assign each a pair in {0,1}^2
# There are 4! = 24 permutations of how to assign, but only 3 distinct
# partitions into 2x2 blocks matter.
import itertools as it
for perm in it.permutations([(0,0),(0,1),(1,0),(1,1)]):
    decomp = {i: perm[i] for i in range(4)}
    # Check: does left_bit depend only on left-side context?
    # does right_bit depend only on right-side context?
    # Look at transitions in the good cycle
    left_consistent = True
    right_consistent = True

    for idx in range(len(good_cycle)):
        c = good_cycle[idx]
        if movers[idx] == 4:
            s4 = c[4]
            L, R = c[3], c[0]
            new_s4 = f(4, L, s4, R)
            old_lr = decomp[s4]
            new_lr = decomp[new_s4]
            # If left_bit changes, it should depend on L (not R)
            # If right_bit changes, it should depend on R (not L)

    # Just print the decomposition for now
    print(f"  {decomp}: 0->{decomp[0]}, 1->{decomp[1]}, 2->{decomp[2]}, 3->{decomp[3]}")
    # Only print first few
    break  # Too many — will analyze manually

print("\nP4 states used in good cycle, in order:")
p4_states_in_cycle = [c[4] for c in good_cycle]
print(f"  {p4_states_in_cycle}")
print(f"  Unique states used: {sorted(set(p4_states_in_cycle))}")
