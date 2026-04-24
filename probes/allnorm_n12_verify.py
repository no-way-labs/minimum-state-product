"""
Verification script: check the all-tight result more carefully.

Key questions:
1. Are the 4092 closable functions actually valid (privilege at every step)?
2. What do the 4 non-closable functions look like?
3. For the closable functions, do the fixed-point configs form actual good cycles
   (privilege maintained at every step)?
"""

from itertools import product as iter_product
from collections import Counter

n = 12
m_vals = [2,2,3,2,2,3,2,2,3,2,2,3]
ternary_positions = {2, 5, 8, 11}

# The all-tight mover sequence from the search
mover_seq = [2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 1, 9, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 1, 9]

# Enumerate ternary transition function inputs
ternary_inputs = []
ternary_valid_outputs = []
for L in range(2):
    for S in range(3):
        for R in range(2):
            ternary_inputs.append((L, S, R))
            ternary_valid_outputs.append([v for v in range(3) if v != S])

def make_ternary_func(choices):
    func = {}
    for inp, out in zip(ternary_inputs, choices):
        func[inp] = out
    return func

def simulate(config, mover_seq, ternary_func):
    """Simulate the mover sequence. Returns (final_config, privilege_ok).
    privilege_ok is True if f(L,S,R) != S at every step."""
    c = list(config)
    for step in range(24):
        p = mover_seq[step]
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]

        if p in ternary_positions:
            new_val = ternary_func[(L, S, R)]
        else:
            new_val = 1 - S  # binary: unique privileged function

        if new_val == S:
            return None, False  # privilege violation

        c[p] = new_val

    return tuple(c), True

# Generate all configs
binary_positions = [0, 1, 3, 4, 6, 7, 9, 10]
ternary_pos_list = [2, 5, 8, 11]

all_configs = []
for bvals in iter_product(range(2), repeat=8):
    for tvals in iter_product(range(3), repeat=4):
        config = [0] * n
        for i, pos in enumerate(binary_positions):
            config[pos] = bvals[i]
        for i, pos in enumerate(ternary_pos_list):
            config[pos] = tvals[i]
        all_configs.append(tuple(config))

print(f"Total configs: {len(all_configs)}")

# Check a few specific functions
print("\n=== Detailed check of first closable function ===")
# First function: all choices are the first valid output
first_choices = tuple(v[0] for v in ternary_valid_outputs)
func1 = make_ternary_func(first_choices)
print(f"Function: {func1}")

fixed_count = 0
privilege_violations = 0
non_fixed = 0

for config in all_configs:
    final, ok = simulate(config, mover_seq, func1)
    if not ok:
        privilege_violations += 1
    elif final == config:
        fixed_count += 1
    else:
        non_fixed += 1

print(f"Fixed points: {fixed_count}")
print(f"Privilege violations: {privilege_violations}")
print(f"Non-fixed (but valid): {non_fixed}")
print(f"Total: {fixed_count + privilege_violations + non_fixed}")

# Show a sample fixed-point config
print("\nSample fixed-point configs:")
sample_count = 0
for config in all_configs:
    final, ok = simulate(config, mover_seq, func1)
    if ok and final == config:
        print(f"  {list(config)}")
        # Show the step-by-step
        c = list(config)
        print(f"    Step-by-step:")
        for step in range(24):
            p = mover_seq[step]
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            if p in ternary_positions:
                new_val = func1[(L, S, R)]
            else:
                new_val = 1 - S
            print(f"    Step {step:2d}: proc {p:2d} fires, ({L},{S},{R}) -> {new_val}, config = {c}")
            c[p] = new_val
        print(f"    Final: {c}")
        print(f"    Match: {tuple(c) == config}")
        sample_count += 1
        if sample_count >= 2:
            break

# Now check: are there functions where the cycle is NON-TRIVIAL?
# (i.e., the config actually changes during the cycle and comes back)
print("\n=== Checking for non-trivial cycles ===")
# A trivial cycle would be one where each proc returns to its initial value
# after its 2 firings, but the intermediate states might vary.

# Actually, ALL valid cycles must return to the initial state. The question is
# whether each proc actually CHANGES state (privilege: f(L,S,R) != S means it
# does change). So every step changes a proc's state, and after 24 steps it
# must return. This is a non-trivial cycle (24 distinct configs).

# Let me verify that the 24 intermediate configs are all distinct for a fixed-point config.
print("\nChecking distinctness of intermediate configs:")
sample_count = 0
for config in all_configs:
    final, ok = simulate(config, mover_seq, func1)
    if ok and final == config:
        c = list(config)
        configs_seen = [tuple(c)]
        all_distinct = True
        for step in range(24):
            p = mover_seq[step]
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            if p in ternary_positions:
                new_val = func1[(L, S, R)]
            else:
                new_val = 1 - S
            c[p] = new_val
            tc = tuple(c)
            if tc in configs_seen[:-1]:  # allow last = first
                all_distinct = False
            configs_seen.append(tc)

        # Last config should equal first
        assert configs_seen[-1] == configs_seen[0], "Cycle doesn't close!"

        # Check if all 24 intermediate configs + initial are distinct
        unique_count = len(set(configs_seen[:-1]))

        if sample_count < 3:
            print(f"  Config {list(config)}: {unique_count} unique configs (should be 24 for good cycle)")
            if unique_count < 24:
                print(f"    WARNING: only {unique_count} distinct configs in cycle!")

        sample_count += 1
        if sample_count >= 100:
            break

# Count functions by fixed-point count
print("\n=== Distribution of fixed-point counts across all 4096 functions ===")
fp_counts = Counter()
non_closable_funcs = []

func_idx = 0
for choices in iter_product(*ternary_valid_outputs):
    func = make_ternary_func(choices)
    func_idx += 1

    fp = 0
    for config in all_configs:
        final, ok = simulate(config, mover_seq, func)
        if ok and final == config:
            fp += 1

    fp_counts[fp] += 1
    if fp == 0:
        non_closable_funcs.append((func_idx, func))

print(f"Fixed-point count distribution:")
for fp, count in sorted(fp_counts.items()):
    print(f"  {fp} fixed points: {count} functions")

print(f"\nNon-closable functions ({len(non_closable_funcs)}):")
for idx, func in non_closable_funcs:
    print(f"  Function #{idx}: {func}")

    # Check WHY it's not closable: privilege violations for all configs?
    priv_fail = 0
    non_fixed = 0
    for config in all_configs:
        final, ok = simulate(config, mover_seq, func)
        if not ok:
            priv_fail += 1
        elif final != config:
            non_fixed += 1

    print(f"    Privilege violations: {priv_fail}, Non-fixed: {non_fixed}")

# Check if the mover sequence is truly period-12 (first half = second half)
print(f"\n=== Mover sequence structure ===")
print(f"Full: {mover_seq}")
print(f"First half:  {mover_seq[:12]}")
print(f"Second half: {mover_seq[12:]}")
print(f"Halves equal: {mover_seq[:12] == mover_seq[12:]}")

# THE KEY ISSUE: if the mover sequence has period 12 (halves equal),
# then a "cycle of length 24" is really just 2 copies of a "cycle of length 12."
# Each proc fires once in each half-cycle. After the first half, we get some
# intermediate config. After the second half (identical operations), we apply
# the same map again. For the full cycle to close: T(T(c)) = c, i.e., T^2 = id.
# This is equivalent to T being an involution (T = T^{-1}).

# For binary procs, f(L,S,R) = 1-S, so firing toggles the state.
# Firing twice returns to the original state IF the context (L,R) is the same
# both times. But the context may differ between the two firings.

# With halves equal and the specific interleaving, the question is whether
# the first half-cycle map T satisfies T^2 = id.

print("\n=== Half-cycle analysis ===")
print("Since mover_seq[:12] == mover_seq[12:], the full cycle is T applied twice.")
print("T^2 = id iff T is an involution.")

# For each function, count configs where T(c) makes sense and T(T(c)) = c
sample_func = func1
t_map = {}
t_priv_ok = 0
for config in all_configs:
    c = list(config)
    ok = True
    for step in range(12):
        p = mover_seq[step]
        L = c[(p-1) % n]
        S = c[p]
        R = c[(p+1) % n]
        if p in ternary_positions:
            new_val = sample_func[(L, S, R)]
        else:
            new_val = 1 - S
        if new_val == S:
            ok = False
            break
        c[p] = new_val
    if ok:
        t_map[config] = tuple(c)
        t_priv_ok += 1

print(f"Configs where half-cycle T is privilege-valid: {t_priv_ok}/{len(all_configs)}")

# Check T^2 = id
involution_count = 0
for c, tc in t_map.items():
    if tc in t_map and t_map[tc] == c:
        involution_count += 1

print(f"Configs where T(T(c)) = c: {involution_count}")
print(f"T is involution on valid configs: {involution_count == t_priv_ok}")
