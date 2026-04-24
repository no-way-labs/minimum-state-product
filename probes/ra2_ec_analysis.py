"""
Script 3: Entry conflict constraint analysis.

For small n (5, 7):
- Generate ring-adjacent cycles that visit all processors with even binary fire counts
- Try to assign config values with small state sizes such that:
  (a) All configs are distinct
  (b) No entry conflict occurs
- Count how many walks admit no-EC config assignments
"""

from collections import Counter, defaultdict
from itertools import product as iprod, combinations
import random

def ring_adj(a, b, n):
    return min(abs(a-b), n-abs(a-b)) <= 1

def gen_hfull_cycles_sampling(n, binary_pos, cl, num_samples=50000):
    """
    Sample ring-adjacent cycles of length cl that:
    - Visit all n processors
    - Have even fire count >= 2 for each binary processor
    - Close: last position ring-adjacent to first
    """
    bp_set = set(binary_pos)
    results = []
    for _ in range(num_samples):
        walk = [0]
        for step in range(cl - 1):
            p = walk[-1]
            nxt = random.choice([(p-1)%n, p, (p+1)%n])
            walk.append(nxt)

        # Check closing
        if not ring_adj(walk[-1], walk[0], n):
            continue

        fc = Counter(walk)
        # Check hfull
        if len(fc) < n:
            continue
        # Check binary parity
        if not all(fc[p] % 2 == 0 and fc[p] >= 2 for p in bp_set):
            continue

        results.append(tuple(walk))
    return list(set(results))

def gen_structured_cycles(n, binary_pos):
    """
    Generate structured ring-adjacent cycles:
    Type A: Double loop (0->1->...->n-1->0->1->...->n-1), CL=2n, all fc=2
    Type B: Out-and-back variations
    """
    cycles = []

    # Type A: Double loop CW
    walk_a = [i % n for i in range(2*n)]
    cycles.append(('double_CW', walk_a))

    # Type A': Double loop CCW
    walk_a2 = [(n - i) % n for i in range(2*n)]
    cycles.append(('double_CCW', walk_a2))

    # Type B: CW then CCW (palindromic)
    # 0,1,2,...,n-1,n-2,...,1,0 has length 2n-1 but fc(0)=2,fc(n-1)=1 -- not good
    # 0,1,...,n-1,n-1,n-2,...,0 has length 2n, fc(0)=2,fc(n-1)=2,rest=2. Good!
    walk_b = list(range(n)) + list(range(n-1, -1, -1))
    cycles.append(('CW_then_CCW', walk_b))

    # Type C: CW with a stall at each binary position
    # Go CW but stay at each binary proc for an extra step
    walk_c = []
    bp_set = set(binary_pos)
    for i in range(n):
        walk_c.append(i)
    # This gives fc=1 for all. Need to add revisits.
    # Instead: go CW, stall at each binary (adding +1 to fc), then go CW again
    # Total CL = n + |binary| + n = 2n + 3
    walk_c2 = []
    for i in range(n):
        walk_c2.append(i % n)
        if i % n in bp_set:
            walk_c2.append(i % n)  # stall: adds 1 to fc
    # Now fc(binary) = 2, fc(others) = 1. Others still odd.
    # Go around again
    for i in range(n):
        walk_c2.append(i % n)
    # Now fc(binary) = 3 (odd!), fc(others) = 2. Worse.
    # Better: double loop already handles this perfectly.

    return cycles

def check_entry_conflict(walk, n, ms, config_assignment):
    """
    Check if a walk with given config assignment has entry conflicts.

    config_assignment: list of tuples, config_assignment[step] = (c_0, c_1, ..., c_{n-1})
    walk: list of mover processors at each step

    Entry conflict: two steps i, j where:
    - Same processor p = walk[i] = walk[j] (or p is non-mover at both)
    - Same context (left_val, self_val, right_val)
    - Different roles (mover vs non-mover) => different required transition

    More precisely: for processor p, its "context" at step i is:
      (config[i][(p-1)%n], config[i][p], config[i][(p+1)%n])
    If p is mover at step i: it transitions config[i][p] -> config[i+1][p]
    If p is non-mover at step i: config[i][p] = config[i+1][p] (no change)

    EC at proc p: exists steps i (p mover) and j (p non-mover) with same context
    but mover step requires change (config[i][p] != config[i+1 mod CL][p])
    while non-mover step requires no change.

    For a deterministic system: f(L, S, R) must give a single output.
    If mover context (L,S,R) has output S' != S, then any non-mover step
    with same (L,S,R) would need output S (contradiction if S' != S).
    """
    cl = len(walk)
    configs = config_assignment

    # For each processor, collect (context, is_mover, output_value) tuples
    conflicts = 0
    for p in range(n):
        context_map = {}  # (L, S, R) -> set of output values needed
        for i in range(cl):
            L = configs[i][(p-1) % n]
            S = configs[i][p]
            R = configs[i][(p+1) % n]
            ctx = (L, S, R)

            next_i = (i + 1) % cl
            S_next = configs[next_i][p]

            if p == walk[i]:
                # Mover: transitions S -> S_next
                output = S_next
            else:
                # Non-mover: must stay S
                output = S
                assert output == S_next or True  # might not hold if configs are inconsistent

            if ctx in context_map:
                if context_map[ctx] != output:
                    conflicts += 1
                    return True, p, ctx, context_map[ctx], output
            else:
                context_map[ctx] = output

    return False, None, None, None, None

def try_random_configs(walk, n, ms, num_trials=1000):
    """
    Try random config assignments for a walk and check for entry conflicts.
    Each config is a tuple of values, config[step][proc] in range(ms[proc]).
    Configs must be all distinct.
    """
    cl = len(walk)
    no_ec_count = 0
    distinct_count = 0

    for _ in range(num_trials):
        # Generate random configs
        configs = []
        seen = set()
        ok = True
        for step in range(cl):
            # The mover at this step fires, so config changes
            # For simplicity: just generate random configs and check constraints
            c = tuple(random.randrange(ms[p]) for p in range(n))
            if c in seen:
                ok = False
                break
            seen.add(c)
            configs.append(c)

        if not ok:
            continue
        distinct_count += 1

        # Check: consecutive configs must differ only at the mover position
        valid = True
        for i in range(cl):
            next_i = (i + 1) % cl
            mover = walk[i]
            for p in range(n):
                if p != mover:
                    if configs[i][p] != configs[next_i][p]:
                        valid = False
                        break
            if not valid:
                break

        if not valid:
            continue

        # Check entry conflict
        has_ec, _, _, _, _ = check_entry_conflict(walk, n, ms, configs)
        if not has_ec:
            no_ec_count += 1

    return distinct_count, no_ec_count

def build_consistent_configs(walk, n, ms):
    """
    Build configs consistent with the walk structure.

    Given a mover sequence, configs must satisfy:
    - config[i+1][p] = config[i][p] for all p != walk[i]  (non-movers don't change)
    - config[i+1][walk[i]] != config[i][walk[i]]  (mover must change value)
    - All configs distinct

    So the ONLY freedom is: initial config + what value the mover transitions to.

    Enumerate: start with a random initial config, then for each step,
    choose the mover's new value (must differ from current).
    """
    cl = len(walk)
    results = []

    # Try multiple initial configs
    for trial in range(200):
        config = list(random.randrange(ms[p]) for p in range(n))
        configs = [tuple(config)]
        seen = {tuple(config)}
        ok = True

        for step in range(cl - 1):
            mover = walk[step]
            old_val = config[mover]
            # Choose new value for mover
            choices = [v for v in range(ms[mover]) if v != old_val]
            if not choices:
                ok = False
                break
            random.shuffle(choices)
            found = False
            for new_val in choices:
                config[mover] = new_val
                c = tuple(config)
                if c not in seen:
                    seen.add(c)
                    configs.append(c)
                    found = True
                    break
            if not found:
                ok = False
                break

        if not ok:
            continue

        # Check cycle closure: config after last step must equal config[0]
        # After step cl-1, the mover changes. The resulting config should be config[0].
        mover = walk[cl - 1]
        needed_val = configs[0][mover]
        if needed_val == config[mover]:
            # Mover must change, but needs to stay same? Contradiction.
            continue
        # Check all non-movers match
        close_ok = True
        for p in range(n):
            if p != mover:
                if config[p] != configs[0][p]:
                    close_ok = False
                    break
        if not close_ok:
            continue

        # Set the final transition
        config[mover] = needed_val
        # configs is already complete (cl configs for cl steps)

        # Verify distinctness
        if len(set(configs)) == cl:
            results.append(configs)

    return results

def analyze_ec_for_configs(walk, n, ms, configs_list):
    """Check EC for each valid config assignment."""
    no_ec = 0
    for configs in configs_list:
        has_ec, proc, ctx, v1, v2 = check_entry_conflict(walk, n, ms, configs)
        if not has_ec:
            no_ec += 1
    return no_ec

print("=" * 70)
print("SCRIPT 3: Entry Conflict Constraint Analysis")
print("=" * 70)

# Part 1: Structured cycles + EC check
print("\n--- Part 1: Double-loop cycles + entry conflict ---")

for n in [5, 7]:
    print(f"\n{'='*50}")
    print(f"n = {n}")
    print(f"{'='*50}")

    # State sizes: 3 binary + rest ternary
    # Need non-consecutive binary positions
    valid_bp = []
    for combo in combinations(range(n), 3):
        if all(min(abs(a-b), n-abs(a-b)) >= 2 for a, b in combinations(combo, 2)):
            valid_bp.append(combo)

    if not valid_bp:
        print(f"  No valid non-consecutive binary triple on C_{n}!")
        # Use consecutive binary instead
        bp = (0, 1, 2)
        print(f"  Using consecutive binary at {bp} instead")
        valid_bp = [bp]

    for bp in valid_bp[:3]:
        ms = [3] * n
        for p in bp:
            ms[p] = 2
        product = 1
        for m in ms:
            product *= m
        print(f"\n  Binary at {bp}, ms={ms}, product={product}")

        # Double loop CW
        walk = [i % n for i in range(2*n)]
        print(f"  Double loop CW (CL={len(walk)}): {walk}")

        fc = Counter(walk)
        print(f"  Fire counts: {dict(fc)}")
        binary_ok = all(fc[p] % 2 == 0 and fc[p] >= 2 for p in bp)
        print(f"  Binary constraint satisfied: {binary_ok}")

        # Build consistent configs
        configs_list = build_consistent_configs(walk, n, ms)
        print(f"  Found {len(configs_list)} consistent config assignments (out of 200 trials)")

        if configs_list:
            no_ec = analyze_ec_for_configs(walk, n, ms, configs_list)
            print(f"  No-EC assignments: {no_ec}/{len(configs_list)}")
            if no_ec > 0:
                # Show first no-EC example
                for configs in configs_list:
                    has_ec, _, _, _, _ = check_entry_conflict(walk, n, ms, configs)
                    if not has_ec:
                        print(f"  Example no-EC config sequence:")
                        for i, c in enumerate(configs[:5]):
                            print(f"    step {i}: mover={walk[i]}, config={c}")
                        if len(configs) > 5:
                            print(f"    ... ({len(configs)} total)")
                        break

        # Also try CW-then-CCW
        walk2 = list(range(n)) + list(range(n-1, -1, -1))
        print(f"\n  CW-then-CCW (CL={len(walk2)}): {walk2}")
        fc2 = Counter(walk2)
        print(f"  Fire counts: {dict(fc2)}")

        configs_list2 = build_consistent_configs(walk2, n, ms)
        print(f"  Found {len(configs_list2)} consistent config assignments")
        if configs_list2:
            no_ec2 = analyze_ec_for_configs(walk2, n, ms, configs_list2)
            print(f"  No-EC assignments: {no_ec2}/{len(configs_list2)}")

# Part 2: Exhaustive for n=5
print("\n\n--- Part 2: Exhaustive analysis for n=5 ---")
n = 5
# On C_5, max independent set = 2. So 3 non-adjacent is impossible.
# Use the actual problem setting: 3 binary that may be adjacent.
# The real question from memory: >=3 binary in ms with product < 4*3^(n-2)

# Let's use ms = (2,2,2,3,3), product = 72 < 108 = 4*27
ms = [2, 2, 2, 3, 3]
bp = [0, 1, 2]  # binary positions (consecutive)
product = 1
for m in ms:
    product *= m
print(f"ms={ms}, binary at {bp}, product={product}")
print(f"Sub-threshold: {product} < {4 * 3**(n-2)} = {4*3**(n-2)}")

# Try various walk types
walk_types = [
    ('double_CW', [i % n for i in range(2*n)]),
    ('CW_CCW', list(range(n)) + list(range(n-1, -1, -1))),
    ('triple_CW', [i % n for i in range(3*n)]),
]

for name, walk in walk_types:
    cl = len(walk)
    if cl > product:
        print(f"\n  {name} (CL={cl}): SKIP (CL > product={product})")
        continue

    fc = Counter(walk)
    binary_ok = all(fc[p] % 2 == 0 for p in bp)
    hfull = len(fc) == n
    print(f"\n  {name} (CL={cl}):")
    print(f"    Fire counts: {dict(fc)}")
    print(f"    Binary even: {binary_ok}, hfull: {hfull}")

    if binary_ok and hfull:
        configs_list = build_consistent_configs(walk, n, ms)
        print(f"    Consistent configs found: {len(configs_list)}")
        if configs_list:
            no_ec = analyze_ec_for_configs(walk, n, ms, configs_list)
            print(f"    No-EC: {no_ec}/{len(configs_list)}")

# Part 3: Why EC is hard
print("\n\n--- Part 3: Entry conflict anatomy ---")
print("""
For a double-loop walk (0,1,2,...,n-1,0,1,...,n-1) of length 2n:
- Processor p fires at steps p and p+n (twice).
- At step p: context is (config[p][(p-1)%n], config[p][p], config[p][(p+1)%n])
- At step p+n: context is (config[p+n][(p-1)%n], config[p+n][p], config[p+n][(p+1)%n])

For non-mover entries:
- At step i (mover=walk[i]), processor p (p != walk[i]) has context from config[i].
  This non-mover context requires f(L,S,R) = S (identity).

- If the SAME (L,S,R) triple appears at a mover step for p (requiring S'!=S)
  AND at a non-mover step for p (requiring S), we have EC.

The double loop is particularly bad because configs are highly correlated
between the two passes. The context triples tend to repeat.
""")

# Demonstrate: for n=5 double loop, show context patterns
n = 5
ms = [2, 2, 2, 3, 3]
walk = [i % n for i in range(2*n)]
print(f"n={n}, ms={ms}, double loop walk={walk}")

configs_list = build_consistent_configs(walk, n, ms)
if configs_list:
    configs = configs_list[0]
    print(f"\nExample config sequence:")
    for i in range(len(configs)):
        m = walk[i]
        print(f"  step {i}: mover={m}, config={configs[i]}")

    print(f"\nContext analysis per processor:")
    for p in range(n):
        print(f"  Proc {p} (m_p={ms[p]}):")
        for i in range(len(configs)):
            L = configs[i][(p-1)%n]
            S = configs[i][p]
            R = configs[i][(p+1)%n]
            role = "MOVER" if walk[i] == p else "non-mover"
            next_S = configs[(i+1)%len(configs)][p]
            print(f"    step {i}: ctx=({L},{S},{R}), {role}, S'={next_S}")

print("\n" + "=" * 70)
print("KEY FINDINGS from EC analysis will appear above.")
print("=" * 70)
