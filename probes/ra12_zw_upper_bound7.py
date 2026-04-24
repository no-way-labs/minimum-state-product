#!/usr/bin/env python3
"""
RA12 Part 7: Can L>2n good cycles exist in VALID SYSTEMS?

From Part 6: L=11 walks with 3 binary procs at n=5 CAN produce distinct configs.
But we need to check: is there a transition function that makes this a valid
good cycle (with unique privilege at each config)?

For a good cycle to be valid:
1. At each config c, exactly one proc p is privileged: f_p(L, c[p], R) ≠ c[p]
2. All other procs q ≠ p: f_q(L, c[q], R) = c[q] (stable)
3. When p fires: c' = c with c'[p] = f_p(L, c[p], R)

The transition function is PART OF THE SYSTEM. We need to find transition tables
that are consistent with the good cycle.

From the good cycle, we can EXTRACT the required transition function values.
Then check consistency (no contradictions).
"""

from itertools import product as cprod
from collections import defaultdict

def extract_transition_constraints(n, ms, walk, configs):
    """
    From a good cycle, extract constraints on the transition function.

    At step k: mover = walk[k], config = configs[k], next_config = configs[(k+1)%L].
    For the mover p = walk[k]:
      f_p(configs[k][left(p)], configs[k][p], configs[k][right(p)]) = configs[(k+1)%L][p]
      (and configs[(k+1)%L][p] ≠ configs[k][p])
    For non-movers q ≠ p:
      f_q(configs[k][left(q)], configs[k][q], configs[k][right(q)]) = configs[k][q]
      (stable: output = current value)

    We collect all these constraints and check for contradictions.
    A contradiction occurs when: for proc p, context (L, S, R), we have two different
    required outputs.
    """
    L = len(walk)
    constraints = defaultdict(set)  # (proc, left, self, right) -> set of required outputs

    for k in range(L):
        c = configs[k]
        c_next = configs[(k + 1) % L]
        mover = walk[k]

        for p in range(n):
            left_val = c[(p - 1) % n]
            self_val = c[p]
            right_val = c[(p + 1) % n]
            key = (p, left_val, self_val, right_val)

            if p == mover:
                # Must fire: output ≠ self_val
                output = c_next[p]
                assert output != self_val, f"Mover didn't change at step {k}"
                constraints[key].add(output)
            else:
                # Must be stable: output = self_val
                constraints[key].add(self_val)

    # Check for contradictions
    contradictions = []
    for key, outputs in constraints.items():
        if len(outputs) > 1:
            contradictions.append((key, outputs))

    return constraints, contradictions

def get_value_at_step(p, step, fires, seq):
    count = sum(1 for s in fires if s < step)
    if count >= len(seq):
        return seq[0]
    return seq[count]

def generate_fire_sequences(m, fc):
    results = []
    def backtrack(seq):
        if len(seq) == fc + 1:
            if seq[-1] == seq[0]:
                results.append(tuple(seq[:-1]))
            return
        for v in range(m):
            if v != seq[-1]:
                backtrack(seq + [v])
    for v0 in range(m):
        backtrack([v0])
    return results

def build_configs(n, ms, walk, combo, fire_steps):
    """Build config sequence from value choices."""
    L = len(walk)
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
    return configs

# Test the L=11 walk that worked
n = 5
ms = [2, 2, 2, 3, 3]
walk = [0, 4, 3, 2, 1, 0, 1, 2, 3, 3, 4]
L = len(walk)

fire_steps = {p: [] for p in range(n)}
for i, p in enumerate(walk):
    fire_steps[p].append(i)

# Try all value assignments and check transition consistency
proc_choices = []
for p in range(n):
    fc_p = len(fire_steps[p])
    m = ms[p]
    if fc_p == 0:
        proc_choices.append([(v,) for v in range(m)])
    else:
        proc_choices.append(generate_fire_sequences(m, fc_p))

print("="*70)
print(f"Walk: {walk}, n={n}, ms={ms}, L={L}")
print("="*70)

valid_count = 0
consistent_count = 0

for combo in cprod(*proc_choices):
    configs = build_configs(n, ms, walk, combo, fire_steps)
    if len(set(configs)) != L:
        continue

    valid_count += 1
    constraints, contradictions = extract_transition_constraints(n, ms, walk, configs)

    if not contradictions:
        consistent_count += 1
        if consistent_count <= 3:
            print(f"\nConsistent assignment found!")
            for i, c in enumerate(configs):
                print(f"  Step {i}: config={c}, mover={walk[i]}")
            print(f"  Constraints: {len(constraints)}")
            # Show transition table entries
            for (p, l, s, r), outputs in sorted(constraints.items()):
                if len(outputs) == 1:
                    out = list(outputs)[0]
                    status = "STABLE" if out == s else "FIRES"
                    print(f"    f_{p}({l},{s},{r}) = {out} [{status}]")

print(f"\nTotal: {valid_count} distinct-config assignments, {consistent_count} transition-consistent")

# Now check ALL L=11 walks
print()
print("="*70)
print("EXHAUSTIVE CHECK: All L=11 ZW walks with fc≥2, binary at {0,1,2}")
print("="*70)

from ra12_zw_upper_bound5 import enumerate_closed_walks

all_walks = enumerate_closed_walks(5, 11, require_zw=True, require_fc2=True,
                                    binary_positions={0,1,2}, max_ternary_run=2)
print(f"Total L=11 walks: {len(all_walks)}")

total_consistent = 0
for w_idx, walk in enumerate(all_walks):
    fire_steps = {p: [] for p in range(n)}
    for i, p in enumerate(walk):
        fire_steps[p].append(i)

    proc_choices = []
    for p in range(n):
        fc_p = len(fire_steps[p])
        m = ms[p]
        if fc_p == 0:
            proc_choices.append([(v,) for v in range(m)])
        else:
            proc_choices.append(generate_fire_sequences(m, fc_p))

    for combo in cprod(*proc_choices):
        configs = build_configs(n, ms, walk, combo, fire_steps)
        if len(set(configs)) != len(walk):
            continue
        constraints, contradictions = extract_transition_constraints(n, ms, walk, configs)
        if not contradictions:
            total_consistent += 1
            if total_consistent <= 2:
                print(f"  Walk {walk}: CONSISTENT!")
                for i, c in enumerate(configs):
                    print(f"    Step {i}: config={c}, mover={walk[i]}")

print(f"\nTotal consistent L=11 good cycles: {total_consistent}")

# Also check L=12
print()
print("="*70)
print("L=12 ZW walks with fc≥2, binary at {0,1,2}")
print("="*70)

all_walks_12 = enumerate_closed_walks(5, 12, require_zw=True, require_fc2=True,
                                       binary_positions={0,1,2}, max_ternary_run=2)
print(f"Total L=12 walks: {len(all_walks_12)}")

total_consistent_12 = 0
for walk in all_walks_12:
    fire_steps = {p: [] for p in range(n)}
    for i, p in enumerate(walk):
        fire_steps[p].append(i)

    proc_choices = []
    for p in range(n):
        fc_p = len(fire_steps[p])
        m = ms[p]
        if fc_p == 0:
            proc_choices.append([(v,) for v in range(m)])
        else:
            proc_choices.append(generate_fire_sequences(m, fc_p))

    total_combos = 1
    for ch in proc_choices:
        total_combos *= len(ch)
    if total_combos > 50000:
        continue  # skip expensive cases

    for combo in cprod(*proc_choices):
        configs = build_configs(n, ms, walk, combo, fire_steps)
        if len(set(configs)) != len(walk):
            continue
        constraints, contradictions = extract_transition_constraints(n, ms, walk, configs)
        if not contradictions:
            total_consistent_12 += 1
            if total_consistent_12 <= 2:
                print(f"  Walk {walk}: CONSISTENT!")
                fc = [0]*n
                for p in walk:
                    fc[p] += 1
                print(f"    fc={fc}")

print(f"\nTotal consistent L=12 good cycles: {total_consistent_12}")
