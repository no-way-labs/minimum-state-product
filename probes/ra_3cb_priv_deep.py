#!/usr/bin/env python3
"""Deep analysis: WHY do 69/80 rules have no compatible cycle?
What mover contexts does each cycle require at proc 1?
Can we find cycles that work with ANY of the 69 incompatible rules?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian
from collections import defaultdict, Counter
import time

from verifier import all_configs, apply_move, privileged_set, verify_system

MS = (2, 2, 2, 3, 3, 3, 3, 4)
N = len(MS)

# Toggle pairs
toggle_pairs = []
for a in range(2):
    for c in range(2):
        toggle_pairs.append(((a, 0, c), (a, 1, c)))

# All 80 rules
priv_subsets = []
for choices in cartesian(range(3), repeat=4):
    subset = set()
    for pair_idx, choice in enumerate(choices):
        if choice == 1:
            subset.add(toggle_pairs[pair_idx][0])
        elif choice == 2:
            subset.add(toggle_pairs[pair_idx][1])
    if len(subset) == 0:
        continue
    priv_subsets.append(frozenset(subset))
priv_subsets = sorted(set(priv_subsets), key=lambda s: (len(s), sorted(s)))


def build_sweep_cycle(ms, order, targets, return_same):
    n = len(ms)
    config = [0] * n
    cycle = [tuple(config)]
    for p in order:
        config = list(cycle[-1])
        config[p] = 1 if ms[p] == 2 else targets[p]
        cycle.append(tuple(config))
    down = order if return_same else tuple(reversed(order))
    for p in down:
        config = list(cycle[-1])
        config[p] = 0
        cycle.append(tuple(config))
    if cycle[-1] != cycle[0]:
        return None
    cycle = cycle[:-1]
    if len(set(cycle)) != len(cycle):
        return None
    return cycle


def build_bounce_cycle(ms, base_pattern=None, max_reps=8):
    n = len(ms)
    if base_pattern is None:
        base_pattern = list(range(n)) + list(range(n-2, 0, -1))
    for reps in range(1, max_reps):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = list(base_pattern) * reps
        for step, mover in enumerate(full):
            config = list(cycle[-1])
            config[mover] = (config[mover] + 1) % ms[mover]
            nc = tuple(config)
            if nc == cycle[0]:
                return cycle, full[:step+1]
            if nc in visited:
                break
            visited.add(nc)
            cycle.append(nc)
    return None, None


def cyclic_orders(n):
    seen = set()
    for base in (list(range(n)), list(range(n-1, -1, -1))):
        for shift in range(n):
            order = tuple(base[shift:] + base[:shift])
            if order not in seen:
                seen.add(order)
                yield order


def extract_p1_requirements(cycle):
    """Extract what proc 1 must do in a cycle: which (L,S,R) must fire, which must stay."""
    n = N
    must_fire = set()  # triples where proc 1 MUST fire (it's the mover)
    must_stay = set()  # triples where proc 1 MUST stay (it's not mover)

    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        diffs = [p for p in range(n) if c[p] != c_next[p]]
        if len(diffs) != 1:
            return None, None
        mover = diffs[0]
        L = c[0]  # proc 0
        S = c[1]  # proc 1
        R = c[2]  # proc 2
        triple = (L, S, R)
        if mover == 1:
            must_fire.add(triple)
        else:
            must_stay.add(triple)
    return must_fire, must_stay


def is_rule_compatible(rule, must_fire, must_stay):
    """Check if a privilege rule is compatible with cycle requirements."""
    for triple in must_fire:
        if triple not in rule:
            return False
    for triple in must_stay:
        if triple in rule:
            return False
    return True


# Build all candidate cycles
non_binary = [p for p, m in enumerate(MS) if m > 2]
target_ranges = [range(1, MS[p]) for p in non_binary]

cycles_pool = []
cycle_set_dedup = set()

for combo in cartesian(*target_ranges):
    targets = {p: 1 for p, m in enumerate(MS) if m == 2}
    for idx, p in enumerate(non_binary):
        targets[p] = combo[idx]
    for order in cyclic_orders(N):
        for ret_same in (True, False):
            cycle = build_sweep_cycle(MS, order, targets, ret_same)
            if cycle is not None:
                key = frozenset(cycle)
                if key not in cycle_set_dedup:
                    cycle_set_dedup.add(key)
                    cycles_pool.append(cycle)

for base in [list(range(N)) + list(range(N-2, 0, -1)),
             list(range(N-1, -1, -1)) + list(range(1, N-1))]:
    for shift in range(len(base)):
        pattern = base[shift:] + base[:shift]
        cycle, movers = build_bounce_cycle(MS, pattern)
        if cycle is not None:
            key = frozenset(cycle)
            if key not in cycle_set_dedup:
                cycle_set_dedup.add(key)
                cycles_pool.append(cycle)

print(f"Total candidate cycles: {len(cycles_pool)}")

# Analyze each cycle's proc 1 requirements
print("\n" + "=" * 72)
print("CYCLE REQUIREMENTS AT PROC 1")
print("=" * 72)

req_counter = Counter()
cycle_requirements = []

for ci, cycle in enumerate(cycles_pool):
    must_fire, must_stay = extract_p1_requirements(cycle)
    if must_fire is None:
        continue
    req_key = (frozenset(must_fire), frozenset(must_stay))
    req_counter[req_key] += 1
    cycle_requirements.append((must_fire, must_stay))

print(f"\nDistinct requirement patterns: {len(req_counter)}")

# For each requirement pattern, check which rules are compatible
print("\n" + "=" * 72)
print("REQUIREMENT PATTERN ANALYSIS")
print("=" * 72)

all_patterns = sorted(req_counter.items(), key=lambda x: -x[1])
for (must_fire_fs, must_stay_fs), count in all_patterns[:20]:
    must_fire = set(must_fire_fs)
    must_stay = set(must_stay_fs)

    # Check toggle consistency of must_fire
    fire_toggle_ok = True
    for triple in must_fire:
        anti = (triple[0], 1-triple[1], triple[2])
        if anti in must_fire:
            fire_toggle_ok = False

    # Check if must_fire and must_stay conflict (same triple in both)
    conflict = must_fire & must_stay

    # Count compatible rules
    compat_rules = []
    for rule in priv_subsets:
        if is_rule_compatible(rule, must_fire, must_stay):
            compat_rules.append(rule)

    print(f"\nPattern ({count} cycles): fire={sorted(must_fire)}, stay={sorted(must_stay)}")
    print(f"  Toggle-consistent fire set: {fire_toggle_ok}")
    print(f"  Fire/stay conflict: {len(conflict)} triples")
    print(f"  Compatible rules: {len(compat_rules)}")
    if compat_rules:
        for r in compat_rules[:5]:
            print(f"    {sorted(r)}")

# Check: is there ANY cycle compatible with any of the 69 "impossible" rules?
print("\n" + "=" * 72)
print("CHECKING IMPOSSIBLE RULES")
print("=" * 72)

# The 11 compatible rules from exploration 1
compatible_indices = {13, 21, 24, 35, 43, 52, 53, 56, 60, 67, 76}

for rule_idx, rule in enumerate(priv_subsets):
    if rule_idx in compatible_indices:
        continue
    # Check if ANY cycle is compatible
    compat_count = 0
    for must_fire, must_stay in cycle_requirements:
        if is_rule_compatible(rule, must_fire, must_stay):
            compat_count += 1
    if compat_count > 0:
        print(f"  Rule {rule_idx} ({sorted(rule)}): {compat_count} compatible cycles!")

print("\nDone checking impossible rules.")

# Analyze WHY size-1 rules always fail
print("\n" + "=" * 72)
print("WHY SIZE-1 RULES FAIL")
print("=" * 72)

# For a cycle to use proc 1, there must be some step where proc 1 fires.
# If the rule has only one mover triple (a,b,c), then every time proc 1 fires,
# its context must be exactly (a,b,c).
# But in a valid good cycle, proc 1 must fire at least m_1=2 times (once for
# each state value). With binary proc 1, it fires exactly 2 times: once from
# state 0 (to state 1) and once from state 1 (to state 0).
# So we need contexts (L,0,R) and (L',1,R') both in the rule.
# But size-1 rule has only one triple, so one of b=0 or b=1 is never a mover.
# Hence proc 1 can only fire once (from one state), but it needs to fire from
# both states to complete a cycle.

print("A binary proc in a good cycle must fire from BOTH states (0 and 1).")
print("Size-1 rule has a single triple (a,b,c) with fixed b, so proc 1")
print("can only fire from state b. It can never return to state b after")
print("flipping to 1-b. Hence no fair cycle exists.")
print()
print("More precisely: in a fair cycle, proc 1 fires exactly 2 times")
print("(once 0->1, once 1->0). These two firings have contexts (L1,0,R1)")
print("and (L2,1,R2). The rule must contain BOTH triples. Size-1 rules")
print("contain exactly one triple, so they always fail.")

# Check size-2 rules that fail
print("\n" + "=" * 72)
print("WHY MOST SIZE-2 RULES FAIL")
print("=" * 72)

for rule_idx in range(8, 32):  # size-2 rules
    rule = priv_subsets[rule_idx]
    if rule_idx in compatible_indices:
        continue
    b_values = {t[1] for t in rule}
    if len(b_values) < 2:
        print(f"  Rule {rule_idx} {sorted(rule)}: BOTH triples have b={list(b_values)[0]} -> same state, can't cycle")
    else:
        # Both b=0 and b=1 present, but still no compatible cycle
        fire0 = [t for t in rule if t[1] == 0]
        fire1 = [t for t in rule if t[1] == 1]
        print(f"  Rule {rule_idx} {sorted(rule)}: fire-from-0={fire0}, fire-from-1={fire1}")
        # Check what cycle patterns would need
        for must_fire, must_stay in cycle_requirements:
            mf0 = [t for t in must_fire if t[1] == 0]
            mf1 = [t for t in must_fire if t[1] == 1]
            if all(t in rule for t in must_fire) and all(t not in rule for t in must_stay):
                print(f"    COMPATIBLE with cycle requiring fire={sorted(must_fire)}, stay={sorted(must_stay)}")
                break
        else:
            # Find the specific conflict
            best_fire = None
            best_score = -1
            for must_fire, must_stay in cycle_requirements:
                score = sum(1 for t in must_fire if t in rule)
                if score > best_score:
                    best_score = score
                    best_fire = must_fire
                    best_stay = must_stay
            if best_fire:
                missing = [t for t in best_fire if t not in rule]
                blocked = [t for t in best_stay if t in rule]
                print(f"    Best near-match: fire={sorted(best_fire)}, missing={missing}, blocked_by_stay={blocked}")

print("\n" + "=" * 72)
print("CONCLUSION")
print("=" * 72)
print("The obstruction at proc 1 is TWO-LAYERED:")
print("1. CYCLE EXISTENCE: most rules can't support any fair good cycle")
print("   (size-1: never fire from both states; many size-2+: cycle contexts")
print("   force non-mover triples that happen to be in the rule)")
print("2. CONVERGENCE: the 11 rules that DO support cycles all produce")
print("   identical bad SCC structure (384 nodes, 75 SCCs, 42 good)")
print("   This is INDEPENDENT of the proc 1 rule -- it's a structural")
print("   property of the (2,2,2,3,3,3,3,4) state vector.")
