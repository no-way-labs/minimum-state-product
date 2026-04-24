"""
Follow-up: Why does left²t (pos 2) ALWAYS have EC in tight cycles?
Key observation from run 1: ALL 437 ECs at pos 2 are in DIFFERENT pos2-phases.
And config[pos1] (left³t) is always the same at both steps (by EC definition).

Hypothesis: pos 2 is binary (m=2), so it fires exactly twice. Between those two firings,
pos 1 (ternary, m=3) must revisit some value. But the EC triple is (pos1, pos2, pos3).
Since pos 2 only has 2 values, and fires twice, the two mover-step triples at pos 2
have pos2 taking both values {0,1}. For a NON-mover step to match, pos 2 must be at
the same value as one of the mover steps.

Let's check: for each tight cycle, what are the two mover-step triples at pos 2?
And how many distinct non-mover triples match?
"""

import random
from collections import defaultdict

random.seed(42)

ms = (3, 3, 2, 2, 3, 2, 2, 3, 3)
n = len(ms)
PIVOT = 4

def random_transition(ms, n):
    f = []
    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n
        table = {}
        for L in range(ms[lp]):
            for S in range(ms[p]):
                for R in range(ms[rp]):
                    table[(L, S, R)] = random.randint(0, ms[p] - 1)
        f.append(table)
    return f

def apply_move(config, p, f):
    c = list(config)
    lp = (p - 1) % n
    rp = (p + 1) % n
    ctx = (c[lp], c[p], c[rp])
    c[p] = f[p][ctx]
    return tuple(c)

def find_good_cycles_systematic(f, max_cycles=200):
    from itertools import product as iterproduct
    cycles = []
    seen = set()
    all_configs = list(iterproduct(*[range(m) for m in ms]))
    random.shuffle(all_configs)
    for start in all_configs[:1000]:
        start = tuple(start)
        for _ in range(5):
            config = start
            history = [config]
            config_to_step = {config: 0}
            for step in range(1, 500):
                p = random.randint(0, n - 1)
                new_config = apply_move(config, p, f)
                if new_config == config:
                    config = new_config
                    continue
                if new_config in config_to_step:
                    cs = config_to_step[new_config]
                    cycle_configs = history[cs:]
                    if len(set(cycle_configs)) == len(cycle_configs) and len(cycle_configs) >= n:
                        movers = []
                        ok = True
                        for i in range(len(cycle_configs)):
                            c1 = cycle_configs[i]
                            c2 = cycle_configs[(i + 1) % len(cycle_configs)]
                            mover = None
                            for q in range(n):
                                if c1[q] != c2[q]:
                                    if mover is not None:
                                        ok = False
                                        break
                                    mover = q
                            if not ok or mover is None:
                                ok = False
                                break
                            movers.append(mover)
                        if ok:
                            cid = frozenset(cycle_configs)
                            if cid not in seen:
                                seen.add(cid)
                                cycles.append((cycle_configs, movers))
                                if len(cycles) >= max_cycles:
                                    return cycles
                    break
                history.append(new_config)
                config_to_step[new_config] = step
                config = new_config
    return cycles

# Analyze the mechanism behind pos 2 EC
NUM_TRIALS = 200
pos2_always_ec = 0
pos2_no_ec = 0
tight_count = 0

# Track: what value does pos1 (left³t) take at the mover steps of pos 2?
pos1_at_mover_steps = defaultdict(int)
# Track: does pos1 stay CONSTANT throughout the cycle?
pos1_constant_count = 0
# Track: how many distinct pos1 values appear at non-mover steps of pos2?
pos1_values_at_nonmover = []

# Track the "pigeonhole" argument
pigeonhole_stats = defaultdict(int)

for trial in range(NUM_TRIALS):
    random.seed(trial * 137 + 42)
    f = random_transition(ms, n)
    cycles = find_good_cycles_systematic(f, max_cycles=50)

    for (cc, movers) in cycles:
        fc_pivot = sum(1 for m in movers if m == PIVOT)
        if fc_pivot != 2:
            continue
        L = len(movers)
        has_tight = any(movers[k] == 2 and movers[(k+1) % L] == 3 for k in range(L))
        if not has_tight:
            continue
        tight_count += 1

        # Find mover steps for pos 2
        mover_steps_2 = [k for k in range(L) if movers[k] == 2]
        nonmover_steps_2 = [k for k in range(L) if movers[k] != 2]
        fc2 = len(mover_steps_2)

        # Get triples at mover steps
        mover_triples = []
        for k in mover_steps_2:
            c = cc[k]
            mover_triples.append((c[1], c[2], c[3]))  # (left³t, left²t, left t)

        # Get triples at non-mover steps
        nonmover_triples = set()
        for k in nonmover_steps_2:
            c = cc[k]
            nonmover_triples.add((c[1], c[2], c[3]))

        # Check for match
        has_ec = False
        for mt in mover_triples:
            if mt in nonmover_triples:
                has_ec = True
                break

        if has_ec:
            pos2_always_ec += 1
        else:
            pos2_no_ec += 1

        # Pigeonhole analysis:
        # pos 2 is binary (m=2), fires fc2 times
        # pos 1 is ternary (m=3)
        # pos 3 is binary (m=2)
        # Total possible triples for (pos1, pos2, pos3) = 3 * 2 * 2 = 12
        # But at mover steps, each triple is unique (from good cycle property)
        # At non-mover steps, there are L - fc2 steps

        # How many distinct triples at non-mover steps?
        n_distinct_nonmover = len(nonmover_triples)

        # How many of the mover triples also appear in non-mover?
        overlap = len(set(mover_triples) & nonmover_triples)

        pigeonhole_stats[f"fc2={fc2}, L={L}, nm_triples={n_distinct_nonmover}, overlap={overlap}"] += 1

        # Track pos1 values at mover steps
        pos1_vals = [cc[k][1] for k in mover_steps_2]
        pos1_at_mover_steps[tuple(sorted(pos1_vals))] += 1

        # How many distinct pos1 values across ALL steps?
        all_pos1 = set(cc[k][1] for k in range(L))
        if len(all_pos1) == 1:
            pos1_constant_count += 1

print(f"Tight cycles: {tight_count}")
print(f"  With EC at pos 2: {pos2_always_ec} ({100*pos2_always_ec/tight_count:.1f}%)")
print(f"  Without EC at pos 2: {pos2_no_ec} ({100*pos2_no_ec/tight_count:.1f}%)")

print(f"\npos1 (left³t) constant throughout cycle: {pos1_constant_count}/{tight_count}")

print(f"\npos1 values at pos2's mover steps:")
for vals, count in sorted(pos1_at_mover_steps.items(), key=lambda x: -x[1]):
    print(f"  {vals}: {count}")

print(f"\nPigeonhole stats (top 20):")
for desc, count in sorted(pigeonhole_stats.items(), key=lambda x: -x[1])[:20]:
    print(f"  {desc}: {count}")

# Now the key question: WHY does EC happen?
# pos 2 is binary. It fires exactly fc2 = 2 times (usually).
# At each firing, the mover triple is (pos1_val, pos2_val, pos3_val).
# Between firings of pos 2, pos2_val is FIXED (it's a non-mover).
# So if ANY other step has the SAME (pos1, pos2, pos3) triple as a mover step, it's EC.
#
# Key: pos 2 fires twice. After firing, pos 2's value changes.
# So the two mover-step triples have DIFFERENT pos2 values (0 vs 1 or 1 vs 0).
# Between the two firings, pos 2 is stuck at one value.
# The non-mover steps cover L-2 configurations, each with pos2 fixed at either val_a or val_b.
#
# For EC to happen: some non-mover step must match a mover triple.
# This means: at some non-mover step, (pos1, pos3) matches (pos1, pos3) at a mover step,
# AND pos2 is at the same value.

# Let's check: do pos1 and pos3 HAVE to revisit the same combo?
print("\n" + "=" * 50)
print("REVISIT ANALYSIS")
print("=" * 50)

revisit_count = 0
no_revisit_count = 0

for trial in range(NUM_TRIALS):
    random.seed(trial * 137 + 42)
    f = random_transition(ms, n)
    cycles = find_good_cycles_systematic(f, max_cycles=50)

    for (cc, movers) in cycles:
        fc_pivot = sum(1 for m in movers if m == PIVOT)
        if fc_pivot != 2:
            continue
        L = len(movers)
        has_tight = any(movers[k] == 2 and movers[(k+1) % L] == 3 for k in range(L))
        if not has_tight:
            continue

        mover_steps_2 = [k for k in range(L) if movers[k] == 2]
        fc2 = len(mover_steps_2)

        # For each mover step, look at (pos1, pos3) pair
        # Then check: in the "phase" after this firing (before next firing of pos 2),
        # does (pos1, pos3) revisit the same values?
        for idx, k1 in enumerate(mover_steps_2):
            c1 = cc[k1]
            target_pair = (c1[1], c1[3])  # (pos1, pos3) at mover step
            pos2_val = c1[2]  # pos 2's value at mover step

            # After firing, pos 2 changes to new value
            c_after = cc[(k1 + 1) % L]
            pos2_after = c_after[2]

            # Walk through non-mover steps in THIS phase
            if idx + 1 < fc2:
                next_fire = mover_steps_2[idx + 1]
            else:
                next_fire = mover_steps_2[0] + L

            found_revisit = False
            for step in range(k1 + 1, next_fire):
                s = step % L
                if movers[s] == 2:
                    continue  # shouldn't happen
                c = cc[s]
                if (c[1], c[3]) == target_pair and c[2] == pos2_val:
                    found_revisit = True
                    break

            # Also check across phases
            for step in range(L):
                if movers[step] == 2:
                    continue
                c = cc[step]
                if (c[1], c[3]) == target_pair and c[2] == pos2_val:
                    found_revisit = True
                    break

            if found_revisit:
                revisit_count += 1
            else:
                no_revisit_count += 1

print(f"\nMover-step (pos1,pos2,pos3) triple revisited at some non-mover step: {revisit_count}")
print(f"NOT revisited: {no_revisit_count}")
print(f"Revisit rate: {100*revisit_count/(revisit_count+no_revisit_count):.1f}%")

# Final: WHY does pos1 revisit?
# pos1 is ternary (m=3), fires fc1 times.
# pos3 is binary (m=2), fires fc3 times.
# Between pos2's firings, pos1 and pos3 can only take a limited number of combos.
# With m_1=3, m_3=2, there are only 6 possible (pos1,pos3) pairs.
# If the phase is long enough (> 6 steps with same pos2 value), pigeonhole forces revisit.

print("\n" + "=" * 50)
print("PHASE LENGTH VS PIGEONHOLE")
print("=" * 50)

phase_lengths = []
for trial in range(min(50, NUM_TRIALS)):
    random.seed(trial * 137 + 42)
    f = random_transition(ms, n)
    cycles = find_good_cycles_systematic(f, max_cycles=50)

    for (cc, movers) in cycles:
        fc_pivot = sum(1 for m in movers if m == PIVOT)
        if fc_pivot != 2:
            continue
        L = len(movers)
        has_tight = any(movers[k] == 2 and movers[(k+1) % L] == 3 for k in range(L))
        if not has_tight:
            continue

        mover_steps_2 = sorted([k for k in range(L) if movers[k] == 2])
        fc2 = len(mover_steps_2)

        for idx in range(fc2):
            start = mover_steps_2[idx]
            if idx + 1 < fc2:
                end = mover_steps_2[idx + 1]
            else:
                end = mover_steps_2[0] + L
            phase_len = end - start  # includes the firing step
            phase_lengths.append(phase_len)

if phase_lengths:
    from collections import Counter
    c = Counter(phase_lengths)
    print(f"Phase lengths (between consecutive pos2 firings):")
    for pl, cnt in sorted(c.items()):
        # Pigeonhole: need > 3*2 = 6 non-mover steps with same pos2 value
        # But actually, the triple is (pos1, pos2, pos3), and pos2 is fixed in the phase
        # So we need (pos1, pos3) to revisit: 3*2 = 6 combos
        # Phase has (pl - 1) non-mover steps with pos2 fixed
        marker = " <-- exceeds pigeonhole bound (6)" if (pl - 1) > 6 else ""
        print(f"  Length {pl}: {cnt}{marker}")
    print(f"\nNote: (pos1,pos3) has 3*2=6 possible pairs.")
    print(f"If phase has > 6 non-mover steps, pigeonhole guarantees (pos1,pos3) revisit.")
    print(f"But EC needs matching at pos2's MOVER step value, not just within phase.")
