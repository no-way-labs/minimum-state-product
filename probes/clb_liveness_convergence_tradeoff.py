#!/usr/bin/env python3
"""clb_liveness_convergence_tradeoff.py — Quantify the liveness-convergence tension.

Key insight from clb_convergence_obstruction.py:
- 1446 dead configs need liveness from free entries
- But making entries privileged creates SCCs (390 SCCs, 8597 trapped configs)
- This is a FUNDAMENTAL TENSION: every free entry you activate for liveness
  creates transitions that can form SCCs.

This script:
1. Builds the greedy liveness repair: activate free entries one at a time,
   tracking how many dead configs get fixed AND how many SCCs are created.
2. Finds the MINIMUM set of free entries needed for liveness.
3. Checks whether ANY minimal liveness set avoids SCCs.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
import random
import time


def build_bounce_cycle(ms, n, base_pattern=None, max_reps=5):
    if base_pattern is None:
        base_pattern = list(range(n-1, -1, -1)) + list(range(1, n))
    for reps in range(1, max_reps):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full = base_pattern * reps
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


def find_sccs(adj):
    """Iterative Tarjan SCC."""
    idx_counter = [0]
    stack = []
    on_stack = set()
    index_map = {}
    lowlink = {}
    sccs = []

    def strongconnect(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = idx_counter[0]
        idx_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        while work:
            node, si = work[-1]
            succs = adj.get(node, [])
            if si < len(succs):
                work[-1] = (node, si + 1)
                w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = idx_counter[0]
                    idx_counter[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index_map[w])
            else:
                if lowlink[node] == index_map[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    if len(scc) > 1 or (scc[0] in adj and scc[0] in adj[scc[0]]):
                        sccs.append(scc)
                work.pop()
                if work:
                    lowlink[work[-1][0]] = min(lowlink[work[-1][0]], lowlink[node])

    for v in adj:
        if v not in index_map:
            strongconnect(v)
    return sccs


n = 9
ms = (2, 3, 3, 3, 3, 3, 3, 3, 2)
up_down = list(range(n)) + list(range(n-2, 0, -1))
cycle, movers = build_bounce_cycle(ms, n, up_down)
good_set = set(cycle)

# Extract determined entries
det = {}
for idx in range(len(cycle)):
    c = cycle[idx]
    c_next = cycle[(idx + 1) % len(cycle)]
    mover = movers[idx]
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        key = (p, L, S, R)
        if p == mover:
            det[key] = c_next[p]
        else:
            det[key] = S

# Identify free entries
free_entries = []
for p in range(n):
    m_L = ms[(p-1)%n]; m_S = ms[p]; m_R = ms[(p+1)%n]
    for L in range(m_L):
        for S in range(m_S):
            for R in range(m_R):
                key = (p, L, S, R)
                if key not in det:
                    free_entries.append(key)

all_configs = list(cartesian(*(range(m) for m in ms)))
non_good = [c for c in all_configs if c not in good_set]
non_good_set = set(non_good)

print(f"Cycle len={len(cycle)}, determined={len(det)}, free={len(free_entries)}")
print(f"Total configs={len(all_configs)}, good={len(good_set)}, non-good={len(non_good)}")

# ============================================================
# Part 1: Which free entries are ESSENTIAL for liveness?
# ============================================================

print("\n" + "="*70)
print("Part 1: Essential free entries for liveness")
print("="*70)

# Build minimal completion (all free = non-privileged)
completion_min = dict(det)
for key in free_entries:
    p, L, S, R = key
    completion_min[key] = S  # non-privileged

# Find dead configs
def get_dead_configs(completion):
    dead = []
    for c in all_configs:
        has_priv = False
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            key = (p, L, S, R)
            if completion.get(key, S) != S:
                has_priv = True
                break
        if not has_priv:
            dead.append(c)
    return dead

dead_init = get_dead_configs(completion_min)
print(f"Dead configs under non-privileged free: {len(dead_init)}")

# For each dead config, find which free entries can save it
dead_to_saviors = {}
for c in dead_init:
    saviors = []
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        key = (p, L, S, R)
        if key not in det:
            saviors.append(key)
    dead_to_saviors[c] = saviors

# Find configs with only ONE possible savior (must be activated)
essential_entries = set()
for c, saviors in dead_to_saviors.items():
    if len(saviors) == 0:
        print(f"  UNSAVEABLE dead config: {''.join(str(x) for x in c)}")
    elif len(saviors) == 1:
        essential_entries.add(saviors[0])

print(f"\nEssential entries (only savior for some dead config): {len(essential_entries)}")
for key in sorted(essential_entries):
    p, L, S, R = key
    # How many dead configs does this save?
    saves = sum(1 for c, savs in dead_to_saviors.items() if key in savs)
    print(f"  P{p}({L},{S},{R}): essential, saves {saves} total")

# ============================================================
# Part 2: Greedy set cover for liveness
# ============================================================

print("\n" + "="*70)
print("Part 2: Greedy minimum cover for liveness")
print("="*70)

remaining_dead = set(dead_init)
activated = set(essential_entries)
completion_greedy = dict(completion_min)

# Activate essential entries first
for key in essential_entries:
    p, L, S, R = key
    choices = [v for v in range(ms[p]) if v != S]
    completion_greedy[key] = choices[0]

# Remove dead configs saved by essential entries
newly_alive = set()
for c in list(remaining_dead):
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        key = (p, L, S, R)
        if completion_greedy.get(key, S) != S:
            newly_alive.add(c)
            break
remaining_dead -= newly_alive
print(f"After essential entries: {len(remaining_dead)} dead remain")

# Greedy: activate the free entry that saves the most dead configs
step = 0
while remaining_dead:
    best_key = None
    best_saves = 0
    for key in free_entries:
        if key in activated:
            continue
        p, L, S, R = key
        saves = sum(1 for c in remaining_dead if key in dead_to_saviors.get(c, []))
        if saves > best_saves:
            best_saves = saves
            best_key = key

    if best_key is None or best_saves == 0:
        print(f"  STUCK: {len(remaining_dead)} unsaveable dead configs!")
        break

    activated.add(best_key)
    p, L, S, R = best_key
    choices = [v for v in range(ms[p]) if v != S]
    completion_greedy[best_key] = choices[0]

    # Remove saved configs
    newly_alive = set()
    for c in remaining_dead:
        for pp in range(n):
            LL = c[(pp-1)%n]; SS = c[pp]; RR = c[(pp+1)%n]
            k = (pp, LL, SS, RR)
            if completion_greedy.get(k, SS) != SS:
                newly_alive.add(c)
                break
    remaining_dead -= newly_alive
    step += 1
    if step <= 30 or len(remaining_dead) == 0:
        print(f"  Step {step}: activate P{p}({L},{S},{R}), "
              f"saves {len(newly_alive)}, {len(remaining_dead)} remain")

print(f"\nMinimal cover size: {len(activated)} entries activated")
print(f"Total free entries: {len(free_entries)}")
print(f"Fraction activated: {len(activated)/len(free_entries):.1%}")

# ============================================================
# Part 3: Check SCCs under greedy completion
# ============================================================

print("\n" + "="*70)
print("Part 3: SCCs under greedy minimal-liveness completion")
print("="*70)

def count_sccs(completion):
    bad_adj = defaultdict(list)
    for c in non_good:
        priv = []
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            key = (p, L, S, R)
            if completion.get(key, S) != S:
                priv.append(p)
        for p in priv:
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            key = (p, L, S, R)
            new_c = list(c)
            new_c[p] = completion[key]
            new_c = tuple(new_c)
            if new_c in non_good_set:
                bad_adj[c].append(new_c)

    sccs = find_sccs(dict(bad_adj))
    return sccs

sccs_greedy = count_sccs(completion_greedy)
if sccs_greedy:
    sizes = sorted([len(s) for s in sccs_greedy], reverse=True)
    total_trapped = sum(sizes)
    print(f"SCCs: {len(sccs_greedy)}, total trapped: {total_trapped}")
    print(f"Largest: {sizes[:10]}")
else:
    print("NO SCCs! Greedy completion might work!")

# ============================================================
# Part 4: Try ALL possible outputs for activated entries
# ============================================================

print("\n" + "="*70)
print("Part 4: Vary activated entry outputs to minimize SCCs")
print("="*70)

activated_list = sorted(activated)
print(f"Activated entries: {len(activated_list)}")

# For each activated entry, how many output choices do we have?
choices_per_entry = {}
for key in activated_list:
    p, L, S, R = key
    choices = [v for v in range(ms[p]) if v != S]
    choices_per_entry[key] = choices

total_combos = 1
for key in activated_list:
    total_combos *= len(choices_per_entry[key])
print(f"Total output combinations: {total_combos}")

if total_combos <= 100000:
    print("Exhaustive search feasible!")
    best_scc_count = float('inf')
    best_trapped = float('inf')
    best_combo = None
    tested_count = [0]

    def enumerate_combos(idx, completion):
        global best_scc_count, best_trapped, best_combo
        if idx == len(activated_list):
            tested_count[0] += 1
            sccs = count_sccs(completion)
            trapped = sum(len(s) for s in sccs)
            if trapped < best_trapped:
                best_trapped = trapped
                best_scc_count = len(sccs)
                best_combo = {k: completion[k] for k in activated_list}
                if trapped == 0:
                    print(f"  *** ZERO SCCs at combo #{tested_count[0]}! ***")
                elif tested_count[0] <= 20 or tested_count[0] % 1000 == 0:
                    print(f"  combo #{tested_count[0]}: {len(sccs)} SCCs, {trapped} trapped (best)")
            return trapped == 0

        key = activated_list[idx]
        for val in choices_per_entry[key]:
            completion[key] = val
            if enumerate_combos(idx + 1, completion):
                return True
        return False

    comp_test = dict(completion_min)
    for key in activated_list:
        p, L, S, R = key
        comp_test[key] = choices_per_entry[key][0]

    # If too many combos, use random sampling instead
    if total_combos > 10000:
        print(f"Too many combos ({total_combos}), using random sampling (10000 trials)...")
        random.seed(42)
        best_trapped_r = float('inf')
        for trial in range(10000):
            comp_trial = dict(completion_min)
            for key in activated_list:
                comp_trial[key] = random.choice(choices_per_entry[key])
            sccs = count_sccs(comp_trial)
            trapped = sum(len(s) for s in sccs)
            if trapped < best_trapped_r:
                best_trapped_r = trapped
                if trial < 20 or trial % 1000 == 0 or trapped == 0:
                    print(f"  trial {trial}: {len(sccs)} SCCs, {trapped} trapped (best)")
            if trapped == 0:
                print(f"  *** ZERO SCCs at trial {trial}! ***")
                break
        print(f"\nBest: {best_trapped_r} trapped configs")
    else:
        enumerate_combos(0, comp_test)
        print(f"\nExhaustive: best = {best_scc_count} SCCs, {best_trapped} trapped")
else:
    print(f"Too many combos ({total_combos}), sampling...")
    random.seed(42)
    best_trapped = float('inf')
    for trial in range(5000):
        comp_trial = dict(completion_min)
        for key in activated_list:
            comp_trial[key] = random.choice(choices_per_entry[key])
        sccs = count_sccs(comp_trial)
        trapped = sum(len(s) for s in sccs)
        if trapped < best_trapped:
            best_trapped = trapped
            if trial < 20 or trial % 500 == 0 or trapped == 0:
                print(f"  trial {trial}: {len(sccs)} SCCs, {trapped} trapped (best)")
        if trapped == 0:
            print(f"  *** ZERO SCCs at trial {trial}! ***")
            break
    print(f"\nBest: {best_trapped} trapped configs")

# ============================================================
# Part 5: Count the TENSION — how many free entries create
# transitions between non-good configs?
# ============================================================

print("\n" + "="*70)
print("Part 5: Transition density analysis")
print("="*70)

# For each free entry, if activated, how many non-good → non-good transitions?
entry_scc_risk = {}
for key in free_entries:
    p, L, S, R = key
    # Configs where this entry fires
    risk = 0
    for c in non_good:
        if c[(p-1)%n] == L and c[p] == S and c[(p+1)%n] == R:
            # Would move to...
            for new_s in range(ms[p]):
                if new_s != S:
                    new_c = list(c)
                    new_c[p] = new_s
                    if tuple(new_c) in non_good_set:
                        risk += 1
    entry_scc_risk[key] = risk

# Compare essential entries' risk vs non-essential
essential_risks = [entry_scc_risk[k] for k in essential_entries]
all_risks = [entry_scc_risk[k] for k in free_entries]

print(f"Essential entry SCC risk: min={min(essential_risks)}, max={max(essential_risks)}, "
      f"avg={sum(essential_risks)/len(essential_risks):.1f}")
print(f"All free entry SCC risk: min={min(all_risks)}, max={max(all_risks)}, "
      f"avg={sum(all_risks)/len(all_risks):.1f}")

# The KEY insight: are essential entries HIGH risk?
print(f"\nEssential entries and their risk:")
for key in sorted(essential_entries, key=lambda k: -entry_scc_risk[k]):
    p, L, S, R = key
    risk = entry_scc_risk[key]
    saves = sum(1 for c, savs in dead_to_saviors.items() if key in savs)
    print(f"  P{p}({L},{S},{R}): risk={risk}, saves={saves}")
