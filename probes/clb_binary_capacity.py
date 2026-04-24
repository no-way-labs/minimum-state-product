#!/usr/bin/env python3
"""clb_binary_capacity.py — Why does 2-binary endpoint fail at product 8748?

Compare working Sol3 v1 at ms=(2,3,...,3) with failing endpoint binary at
ms=(2,3,...,3,2). Focus on structural capacity constraints.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from verify_sol3v1_n9 import make_sol3v1_rules


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
    idx_counter = [0]
    stack = []; on_stack = set()
    index_map = {}; lowlink = {}; sccs = []

    def strongconnect(v):
        work = [(v, 0)]
        index_map[v] = lowlink[v] = idx_counter[0]
        idx_counter[0] += 1
        stack.append(v); on_stack.add(v)
        while work:
            node, si = work[-1]
            succs = adj.get(node, [])
            if si < len(succs):
                work[-1] = (node, si + 1)
                w = succs[si]
                if w not in index_map:
                    index_map[w] = lowlink[w] = idx_counter[0]
                    idx_counter[0] += 1
                    stack.append(w); on_stack.add(w)
                    work.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index_map[w])
            else:
                if lowlink[node] == index_map[node]:
                    scc = []
                    while True:
                        w = stack.pop(); on_stack.discard(w); scc.append(w)
                        if w == node: break
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

# ============================================================
# Build both systems
# ============================================================

# System A: Working Sol3 v1 at (2,3,...,3)
ms_A = (2,) + (3,)*8
fs_A = make_sol3v1_rules(ms_A)
all_A = list(cartesian(*(range(m) for m in ms_A)))

# Find good cycle for Sol3 v1 by simulation
config = tuple(0 for _ in range(n))
for p in range(n):
    L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
    new_S = fs_A[p](L, S, R)
    if new_S != S:
        print(f"(0,...,0): P{p}({L},{S},{R}) -> {new_S}")

# Try (1,0,...,0)
config = (1,) + (0,)*(n-1)
print(f"\nStarting from {config}:")
cycle_A = [config]
visited_A = {config}
for step in range(100):
    priv = []
    for p in range(n):
        L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
        new_S = fs_A[p](L, S, R)
        if new_S != S:
            priv.append((p, new_S))
    if not priv:
        print(f"  Step {step}: DEADLOCK at {config}")
        break
    p, new_S = priv[0]
    config = list(config)
    config[p] = new_S
    config = tuple(config)
    if step < 40:
        print(f"  Step {step}: P{p} moves -> {config}")
    if config == cycle_A[0]:
        print(f"  Cycle closed at step {step+1}!")
        break
    if config in visited_A:
        idx = cycle_A.index(config)
        cycle_A = cycle_A[idx:]
        print(f"  Revisited at step {step+1}, cycle from idx {idx}, len={len(cycle_A)}")
        break
    visited_A.add(config)
    cycle_A.append(config)

good_A = cycle_A
good_set_A = set(good_A)
print(f"\nSol3 v1: good cycle len={len(good_A)}")

# System B: Endpoint binary bounce
ms_B = (2, 3, 3, 3, 3, 3, 3, 3, 2)
up_down = list(range(n)) + list(range(n-2, 0, -1))
cycle_B, movers_B = build_bounce_cycle(ms_B, n, up_down)
all_B = list(cartesian(*(range(m) for m in ms_B)))
good_set_B = set(cycle_B)
print(f"Endpoint binary: good cycle len={len(cycle_B)}")

# ============================================================
# Part 1: Triple capacity comparison
# ============================================================

print("\n" + "=" * 70)
print("Part 1: Triple capacity per processor")
print("=" * 70)

for ms, fs, good_set, label in [
    (ms_A, fs_A, good_set_A, "Sol3 v1 (2,3^8)"),
]:
    print(f"\n{label}:")
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]

    for p in range(n):
        m_L = ms[(p-1)%n]; m_S = ms[p]; m_R = ms[(p+1)%n]
        total = m_L * m_S * m_R
        priv = 0
        ng_priv = 0
        to_good = 0
        for c in non_good:
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            if fs[p](L, S, R) != S:
                ng_priv += 1
                new_c = list(c)
                new_c[p] = fs[p](L, S, R)
                if tuple(new_c) in good_set:
                    to_good += 1
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    if fs[p](L, S, R) != S:
                        priv += 1
        print(f"  P{p} (m={ms[p]}): {total} triples, {priv} priv | "
              f"ng priv={ng_priv}, →good={to_good}")

# ============================================================
# Part 2: Binary state bottleneck
# ============================================================

print("\n" + "=" * 70)
print("Part 2: Binary processor vision comparison")
print("=" * 70)

print("P0 triple domain:")
print(f"  Sol3 v1 (2,3^8): P0 sees {ms_A[n-1]}×{ms_A[0]}×{ms_A[1]} = "
      f"{ms_A[n-1]*ms_A[0]*ms_A[1]} triples")
print(f"  Endpoint (2,3^7,2): P0 sees {ms_B[n-1]}×{ms_B[0]}×{ms_B[1]} = "
      f"{ms_B[n-1]*ms_B[0]*ms_B[1]} triples")

print(f"\nP8 triple domain:")
print(f"  Sol3 v1: P8 sees {ms_A[n-2]}×{ms_A[n-1]}×{ms_A[0]} = "
      f"{ms_A[n-2]*ms_A[n-1]*ms_A[0]} triples")
print(f"  Endpoint: P8 sees {ms_B[n-2]}×{ms_B[n-1]}×{ms_B[0]} = "
      f"{ms_B[n-2]*ms_B[n-1]*ms_B[0]} triples")

total_A = sum(ms_A[(p-1)%n] * ms_A[p] * ms_A[(p+1)%n] for p in range(n))
total_B = sum(ms_B[(p-1)%n] * ms_B[p] * ms_B[(p+1)%n] for p in range(n))
print(f"\nTotal triple capacity: Sol3={total_A}, Endpoint={total_B}, "
      f"diff={total_A-total_B} ({(total_A-total_B)/total_A*100:.1f}%)")

# ============================================================
# Part 3: Equivalence class analysis
# ============================================================

print("\n" + "=" * 70)
print("Part 3: Binary processor equivalence classes")
print("=" * 70)

# For a binary processor p, configs sharing the same (L,S,R) triple
# are INDISTINGUISHABLE to p. p must treat them identically.
# How many non-good configs share each triple?

for ms, good_set, all_configs, label in [
    (ms_A, good_set_A, all_A, "Sol3 v1"),
    (ms_B, good_set_B, all_B, "Endpoint binary"),
]:
    print(f"\n{label}:")
    for p in [0, n-1]:
        classes = defaultdict(list)
        for c in all_configs:
            if c in good_set:
                continue
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            classes[(L, S, R)].append(c)
        sizes = sorted([len(v) for v in classes.values()], reverse=True)
        print(f"  P{p} (m={ms[p]}): {len(classes)} classes, "
              f"max={sizes[0]}, median={sizes[len(sizes)//2]}, "
              f"total ng={sum(sizes)}")

# ============================================================
# Part 4: The DEEP question — convergence funnel width
# ============================================================

print("\n" + "=" * 70)
print("Part 4: Convergence funnel — good cycle neighborhood")
print("=" * 70)

# How many non-good configs are 1-step from the good cycle?
# This is the "entry funnel" — the maximum convergence bandwidth.

def good_cycle_neighbors(fs, ms, n, good_set, all_configs):
    """Configs that can reach good in 1 step under some daemon."""
    non_good = [c for c in all_configs if c not in good_set]
    neighbors = set()
    for c in non_good:
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            new_S = fs[p](L, S, R)
            if new_S != S:
                new_c = list(c)
                new_c[p] = new_S
                if tuple(new_c) in good_set:
                    neighbors.add(c)
                    break
    return neighbors

nbrs_A = good_cycle_neighbors(fs_A, ms_A, n, good_set_A, all_A)
non_good_A = len(all_A) - len(good_set_A)
print(f"Sol3 v1: {len(nbrs_A)} of {non_good_A} non-good reach good in 1 step "
      f"({len(nbrs_A)/non_good_A*100:.1f}%)")

# For system B, compute the MAXIMUM possible entry funnel
# (over all possible completions of free entries)
# Build completion that maximizes good-cycle neighbors
det_B = {}
for idx in range(len(cycle_B)):
    c = cycle_B[idx]
    c_next = cycle_B[(idx + 1) % len(cycle_B)]
    mover = movers_B[idx]
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        key = (p, L, S, R)
        if p == mover:
            det_B[key] = c_next[p]
        else:
            det_B[key] = S

# Count how many non-good configs could potentially reach good
# regardless of completion (if any transition function value could route them there)
potential_nbrs = set()
for c in all_B:
    if c in good_set_B:
        continue
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        # Try all possible new_S values
        for new_S in range(ms_B[p]):
            if new_S == S:
                continue
            new_c = list(c)
            new_c[p] = new_S
            if tuple(new_c) in good_set_B:
                potential_nbrs.add(c)
                break
        if c in potential_nbrs:
            break

non_good_B = len(all_B) - len(good_set_B)
print(f"Endpoint binary: MAX {len(potential_nbrs)} of {non_good_B} non-good could reach good in 1 step "
      f"({len(potential_nbrs)/non_good_B*100:.1f}%)")

# ============================================================
# Part 5: The PUNCHLINE — mutual exclusion constraint vs convergence
# ============================================================

print("\n" + "=" * 70)
print("Part 5: Mutual exclusion forces on the endpoint binary cycle")
print("=" * 70)

# In a valid system, the good cycle must have EXACTLY 1 token at all times.
# For the bounce cycle, extract which configs have tokens where.

# Good cycle configs and their tokens
print("Good cycle configs and tokens:")
for idx in range(len(cycle_B)):
    c = cycle_B[idx]
    mover = movers_B[idx]
    # Token = privileged processor
    print(f"  {idx:2d}: {''.join(str(x) for x in c)} -> P{mover} moves")

# Mutual exclusion: for each non-good config, how many processors are privileged?
# Under any valid completion, non-good configs must not be in the good cycle,
# but they CAN have 0, 1, or multiple tokens (liveness just requires ≥1).
# However, the system must ensure that from any config, execution eventually
# reaches the good cycle. If a non-good config has NO privilege (dead), the
# system fails liveness.

# ============================================================
# Part 6: Verify Sol3 v1 is actually valid
# ============================================================

print("\n" + "=" * 70)
print("Part 6: Verify Sol3 v1 properties")
print("=" * 70)

from verifier import verify_system
result_A = verify_system(list(ms_A), fs_A, verbose=False)
print(f"Sol3 v1 verification: valid={result_A['valid']}")
for prop, (ok, msg) in result_A['properties'].items():
    print(f"  {prop}: {ok} — {msg}")

# ============================================================
# Part 7: COUNTING argument — why product 8748 is insufficient
# ============================================================

print("\n" + "=" * 70)
print("Part 7: Counting argument for why product 8748 fails")
print("=" * 70)

# The good cycle has 25 configs. The system has 8748.
# For liveness, EVERY config must have at least one privileged processor.
# The privilege of a config c at processor p depends ONLY on triple (L,S,R).
# So the "privilege map" is determined by the transition functions.

# Total triples in the system:
# Each processor p has ms[(p-1)%n] * ms[p] * ms[(p+1)%n] triples.
# A triple is "privileged" if f(L,S,R) ≠ S.

# For the good cycle, the Triple Disjointness Lemma tells us:
# for each processor p, its mover triples and non-mover triples must be disjoint.
# So the good cycle PARTITIONS each processor's triple space into
# "must-be-privileged" and "must-be-non-privileged" zones.

# Count determined triples per processor:
det_triples = defaultdict(lambda: {'mover': set(), 'nonmover': set()})
for idx in range(len(cycle_B)):
    c = cycle_B[idx]
    mover = movers_B[idx]
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        triple = (L, S, R)
        if p == mover:
            det_triples[p]['mover'].add(triple)
        else:
            det_triples[p]['nonmover'].add(triple)

print("Determined triple partition from good cycle:")
for p in range(n):
    m_total = ms_B[(p-1)%n] * ms_B[p] * ms_B[(p+1)%n]
    nm = len(det_triples[p]['mover'])
    nn = len(det_triples[p]['nonmover'])
    free = m_total - nm - nn
    print(f"  P{p} (m={ms_B[p]}): {m_total} total, {nm} must-priv, "
          f"{nn} must-nonpriv, {free} free")

# How many non-good configs have ALL their triples in the "must-be-non-privileged" zone?
# These configs are DEAD under determined entries and need free entries for liveness.
dead_determined = 0
for c in all_B:
    if c in good_set_B:
        continue
    all_nonpriv = True
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        triple = (L, S, R)
        if triple in det_triples[p]['mover']:
            all_nonpriv = False
            break
    if all_nonpriv:
        dead_determined += 1

print(f"\nNon-good configs with ALL triples in must-nonpriv zone: {dead_determined}")
print(f"These need free entries activated for liveness.")
print(f"Fraction of non-good: {dead_determined/non_good_B*100:.1f}%")
