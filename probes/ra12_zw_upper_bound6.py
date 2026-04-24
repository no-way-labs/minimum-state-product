#!/usr/bin/env python3
"""
RA12 Part 6: Can L>2n walks produce distinct configs?

For a walk with L > 2n and ≥3 binary with fc(binary) even:
Check if state assignments exist making all configs distinct.

Example: n=5, binary at {0,1,2} (m=2), ternary at {3,4} (m=3).
Walk [0,4,3,2,1,0,1,2,3,3,4] has L=11, fc=[2,2,2,3,2].
Binary proc 0: fc=2, fires at steps where mover=0. Values toggle: v,1-v,...
Ternary proc 3: fc=3, fires at steps where mover=3. Values change each time.

Key question: with fc(binary)=2 and fc(ternary3)=3, can we assign values
such that all 11 configs are distinct?
"""

from itertools import product as cprod
from collections import Counter

def check_distinct_configs(n, ms, walk):
    """
    Given a walk (list of mover positions of length L), check if there exist
    value assignments at each proc such that:
    1. When proc p fires, its value changes (to something ≠ current)
    2. When proc p doesn't fire, its value stays the same
    3. All L configs are distinct
    4. Cycle closure: after all firings, each proc returns to original value

    Returns True if such an assignment exists, plus an example.
    """
    L = len(walk)

    # For each proc p, determine the firing steps
    fire_steps = {p: [] for p in range(n)}
    for i, p in enumerate(walk):
        fire_steps[p].append(i)

    # For each proc p, the value sequence:
    # Between consecutive firings, value is constant.
    # At each firing, value changes.
    # Must return to original after all firings (cycle closure).

    # For proc p with fc(p) firings:
    # Value sequence: v_0 (initial), then changes at each firing.
    # v_0, v_1, ..., v_{fc-1}, v_0 (returns to original).
    # Constraint: v_i ≠ v_{i+1} for each firing (value changes).
    # Also: v_{fc-1} ≠ v_0 (last firing changes value back doesn't mean equal).
    # Wait: v_{fc} = v_0 (cycle closure). And v_{fc-1} ≠ v_{fc} = v_0 (firing changes value).
    # So v_{fc-1} ≠ v_0. Also v_i ≠ v_{i+1} for i=0,...,fc-1 where v_{fc} = v_0.

    # For binary (m=2): values alternate 0,1,0,1,...
    # With even fc: returns to original. Sequence is determined by initial value.

    # For ternary (m=3): values change each time, many possible sequences.
    # With fc=3: v_0, v_1, v_2, v_0. Need v_0≠v_1, v_1≠v_2, v_2≠v_0. All distinct.
    # So exactly one sequence (up to labeling): 0,1,2,0 or 0,2,1,0 etc.
    # Actually 2 choices: 0→1→2→0 or 0→2→1→0 (cyclic orderings).

    # For ternary with fc=2: v_0, v_1, v_0. Need v_0≠v_1. 2 choices for v_1.

    # To check if distinct configs exist: enumerate all possible value sequence assignments
    # and check if any produces L distinct configs.

    # Each config at step i: (val_0(i), val_1(i), ..., val_{n-1}(i))
    # where val_p(i) depends on p's firing history.

    # For binary p: val_p(i) = initial_p XOR (number of firings of p before step i) mod 2.
    # Two choices for initial_p: 0 or 1.

    # For ternary p with fc=2: val_p alternates between v_0 and v_1.
    # Phase 0: steps before 1st firing → val = v_0
    # Phase 1: steps between 1st and 2nd firing → val = v_1
    # Phase 2: steps after 2nd firing → val = v_0 (cycle closure)
    # Choices: v_0 ∈ {0,1,2}, v_1 ∈ {0,1,2}\{v_0}. 3*2 = 6 choices.

    # For ternary p with fc=3: 3 phases.
    # Phase 0: val = v_0
    # Phase 1: val = v_1 (≠ v_0)
    # Phase 2: val = v_2 (≠ v_1, ≠ v_0)
    # Phase 3: val = v_0 (cycle closure, ≠ v_2)
    # v_0, v_1, v_2 all distinct. Choices: 3! = 6 permutations, but v_2 ≠ v_0 is auto.
    # Actually: v_0 ∈ {0,1,2}, v_1 ∈ {0,1,2}\{v_0}, v_2 = remaining value.
    # 3*2*1 = 6 choices.

    # Total choices = product of per-proc choices. For small n, enumerate all.

    # Build value sequences for each choice
    def build_value_sequence(p, initial, values_at_fires):
        """
        Build value sequence for proc p over the cycle.
        values_at_fires[j] = value of p AFTER the j-th firing (0-indexed).
        initial = value before first firing.
        """
        seq = [0] * L
        fc_p = len(fire_steps[p])
        if fc_p == 0:
            return [initial] * L

        # Assign values between firings
        curr_val = initial
        fire_idx = 0
        for i in range(L):
            if fire_idx < fc_p and i == fire_steps[p][fire_idx]:
                seq[i] = curr_val  # value AT this step (before firing)
                curr_val = values_at_fires[fire_idx]  # value AFTER firing
                fire_idx += 1
            else:
                seq[i] = curr_val

        return seq

    # Enumerate value choices
    proc_choices = []
    for p in range(n):
        fc_p = len(fire_steps[p])
        m = ms[p]

        if fc_p == 0:
            # Never fires: value is constant
            proc_choices.append([(v,) for v in range(m)])
        else:
            # Generate all valid value sequences
            # v_0 = initial, v_1, ..., v_{fc-1} = values after each firing
            # Constraint: consecutive differ, last returns to v_0
            choices = []
            for seq in generate_fire_sequences(m, fc_p):
                choices.append(seq)
            proc_choices.append(choices)

    # Count total combinations
    total_combos = 1
    for ch in proc_choices:
        total_combos *= len(ch)

    if total_combos > 100000:
        print(f"    Too many combos ({total_combos}), sampling...")
        return check_distinct_sampling(n, ms, walk, fire_steps, L, proc_choices)

    # Enumerate all combinations
    for combo in cprod(*proc_choices):
        configs = []
        for i in range(L):
            cfg = []
            for p in range(n):
                fc_p = len(fire_steps[p])
                if fc_p == 0:
                    cfg.append(combo[p][0])
                else:
                    val = get_value_at_step(p, i, fire_steps[p], combo[p])
                    cfg.append(val)
            configs.append(tuple(cfg))

        if len(set(configs)) == L:
            return True, configs

    return False, None

def get_value_at_step(p, step, fires, seq):
    """
    Get value of proc p at step `step`.
    fires: list of firing steps for p (sorted).
    seq: (initial, val_after_fire_0, val_after_fire_1, ...).
    """
    # How many firings of p have occurred by step `step` (not including step itself)?
    # Actually: at step i, if p fires, its value is the value BEFORE firing.
    # After firing (at step i+1), value changes.
    # So value at step i = initial if no firing yet, or value after last firing.

    # value at step i = seq[k] where k = number of fires at steps < i.
    # Wait: seq[0] = initial (before any fire).
    # seq[1] = value after 1st fire.
    # seq[j+1] = value after (j+1)-th fire.

    # At step i: value = seq[count of fires at steps strictly before i... no wait.
    # The step IS when the firing happens. At step i, config[i] has the value
    # BEFORE firing. After firing at step i, config[i+1] has the new value.

    # So value at step i = number of fires at steps 0, 1, ..., i-1 that belong to p.
    # No, value at step i:
    # - If p fires at steps a_0 < a_1 < ... < a_{k-1}:
    #   For i ≤ a_0: value = seq[0] = initial.
    #   For a_j < i ≤ a_{j+1}: value = seq[j+1] (after j+1 firings).
    #   Hmm wait. AT step a_0: value = initial (config[a_0] has the old value).
    #   Config[a_0 + 1] has p = seq[1] (just fired).
    #   For a_0 < i < a_1: value = seq[1].
    #   AT step a_1: value = seq[1] (config[a_1] has value from after first fire).
    #   Config[a_1 + 1] has p = seq[2].
    #   etc.

    # So: value at step i:
    # count = number of fires at steps strictly before i, PLUS:
    # if i is a fire step, the value is what it was BEFORE this fire.
    # So: count = number of fires at steps < i.
    # value = seq[count].

    # But for cyclic walk: step 0 follows step L-1.
    # At step 0: how many fires happened before? In a cyclic walk, the answer
    # depends on where we "start" the cycle. Let's say we start at step 0.
    # value at step 0 = seq[0] = initial.
    # Fires at step 0 (if any) mean config[0] has the pre-fire value.

    count = sum(1 for s in fires if s < step)
    # After all firings, value returns to initial = seq[0]
    if count >= len(seq):
        return seq[0]
    return seq[count]

def generate_fire_sequences(m, fc):
    """
    Generate all valid fire value sequences for a proc with m states and fc firings.
    Returns list of tuples (v_0, v_1, ..., v_fc) where:
    - v_0 = initial value
    - v_j = value after j-th firing
    - v_j ≠ v_{j-1} for j=1,...,fc
    - v_fc = v_0 (cycle closure, but we DON'T store v_fc since it equals v_0)

    Wait: the sequence is (initial, after_fire_0, after_fire_1, ..., after_fire_{fc-1}).
    Cycle closure: after_fire_{fc-1} should... no.
    The cycle is: initial, fire → after_fire_0, fire → after_fire_1, ...,
    fire → after_fire_{fc-1}. And after_fire_{fc-1} must equal initial (cycle closure).

    Actually: after fc firings, value returns to initial.
    seq = (v_0, v_1, ..., v_{fc}) where v_{fc} = v_0 and v_i ≠ v_{i-1}.
    We return (v_0, v_1, ..., v_{fc-1}) since v_{fc} = v_0 is implied.
    Wait, we need v_{fc} = v_0, meaning v_{fc-1} ≠ v_0 (since v_{fc} = v_0 ≠ v_{fc-1}).
    """
    results = []

    def backtrack(seq):
        if len(seq) == fc + 1:
            if seq[-1] == seq[0]:
                results.append(tuple(seq[:-1]))  # don't include the repeated v_0
            return
        for v in range(m):
            if v != seq[-1]:
                backtrack(seq + [v])

    for v0 in range(m):
        backtrack([v0])

    return results

# TEST: n=5, binary at {0,1,2} (m=2), ternary at {3,4} (m=3).
# Walk [0,4,3,2,1,0,1,2,3,3,4] has L=11.

n = 5
ms = [2, 2, 2, 3, 3]
walk = [0, 4, 3, 2, 1, 0, 1, 2, 3, 3, 4]

print("="*70)
print(f"Walk: {walk}")
print(f"n={n}, ms={ms}, L={len(walk)}")
fc = [0]*n
for p in walk:
    fc[p] += 1
print(f"fc = {fc}")
print()

# Fire steps for each proc
fire_steps = {p: [] for p in range(n)}
for i, p in enumerate(walk):
    fire_steps[p].append(i)
print("Fire steps:")
for p in range(n):
    print(f"  Proc {p}: fires at steps {fire_steps[p]}")

print()
print("Generating fire sequences...")
for p in range(n):
    seqs = generate_fire_sequences(ms[p], len(fire_steps[p]))
    print(f"  Proc {p} (m={ms[p]}, fc={len(fire_steps[p])}): {len(seqs)} sequences")

print()
print("Checking if distinct configs exist...")
result, configs = check_distinct_configs(n, ms, walk)
print(f"Result: {result}")
if configs:
    for i, c in enumerate(configs):
        mover = walk[i]
        print(f"  Step {i}: config={c}, mover={mover}")

# Try several more walks with L > 2n
print()
print("="*70)
print("Checking multiple L=11 walks for distinct configs")
print("="*70)

walks_to_test = [
    [0, 4, 3, 2, 1, 0, 1, 2, 3, 3, 4],
    [0, 4, 3, 2, 1, 0, 1, 2, 3, 4, 4],
    [0, 4, 3, 2, 1, 2, 3, 3, 4, 0, 1],
    [0, 4, 3, 2, 1, 2, 3, 4, 4, 0, 1],
    [0, 4, 3, 2, 3, 3, 4, 0, 1, 2, 1],
]

for w in walks_to_test:
    fc = [0]*n
    for p in w:
        fc[p] += 1
    result, configs = check_distinct_configs(n, ms, w)
    print(f"Walk {w}: fc={fc}, distinct configs: {result}")
    if configs:
        # Check: is this a valid good cycle?
        # Need: at each step, the mover's value CHANGES, others stay
        for i in range(len(w)):
            c = configs[i]
            c_next = configs[(i+1) % len(w)]
            mover = w[i]
            # Mover changes
            if c[mover] == c_next[mover]:
                print(f"  ERROR: mover {mover} didn't change at step {i}")
                break
            # Others stay
            for p in range(n):
                if p != mover and c[p] != c_next[p]:
                    print(f"  ERROR: non-mover {p} changed at step {i}")
                    break
        else:
            print(f"  Valid good cycle structure!")

# Now check L=12
print()
print("="*70)
print("Checking L=12 walks")
print("="*70)

walks_12 = [
    [0, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4],
    [0, 4, 3, 2, 1, 0, 1, 0, 1, 2, 3, 4],
    [0, 4, 3, 2, 1, 0, 1, 2, 3, 3, 4, 4],
]

for w in walks_12:
    fc = [0]*n
    for p in w:
        fc[p] += 1
    result, configs = check_distinct_configs(n, ms, w)
    print(f"Walk {w}: fc={fc}, distinct configs: {result}")
    if configs:
        for i in range(len(w)):
            c = configs[i]
            c_next = configs[(i+1) % len(w)]
            mover = w[i]
            if c[mover] == c_next[mover]:
                print(f"  ERROR at step {i}")
                break
            for p in range(n):
                if p != mover and c[p] != c_next[p]:
                    print(f"  ERROR: non-mover changed at step {i}")
                    break
        else:
            print(f"  Valid good cycle structure!")

def check_distinct_sampling(n, ms, walk, fire_steps, L, proc_choices, num_samples=100000):
    """Sample random value assignments and check for distinct configs."""
    import random
    for _ in range(num_samples):
        combo = tuple(random.choice(ch) for ch in proc_choices)
        configs = []
        for i in range(L):
            cfg = []
            for p in range(n):
                val = get_value_at_step(p, i, fire_steps[p], combo[p])
                cfg.append(val)
            configs.append(tuple(cfg))
        if len(set(configs)) == L:
            return True, configs
    return False, None
