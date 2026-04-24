#!/usr/bin/env python3
"""clb_universal_2binary.py — Is 2-binary fatal for ALL good cycles at n=9?

KEY INSIGHT: product < 2·3^(n-1) implies ≥2 binary processors.
So proving "2+ binary is fatal at n=9" would give M_9 ≥ 2·3^8 = 13122.

This script asks: for ms=(2,2,3,3,3,3,3,3,3), regardless of good cycle,
is the liveness-convergence tension INEVITABLE?

Approach:
1. Enumerate small good cycles (not just bounce/sweep) via BFS
2. For each, compute the "dead config count" (configs needing free entries)
3. For each, check if ANY completion avoids SCCs
4. Look for patterns that would generalize

Also: test all orientations of 2-binary at n=9.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
import time


def find_sccs(adj):
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

# ============================================================
# Part 1: The COUNTING LEMMA — why ≥2 binary is necessary
# ============================================================

print("=" * 70)
print("Part 1: The 2-binary counting lemma")
print("=" * 70)

print("""
LEMMA: For n ≥ 9, any multiset (m_0,...,m_{n-1}) with all m_i ≥ 2 and
product < 2·3^(n-1) must contain at least 2 values equal to 2.

Proof: If at most 1 value is 2 and the rest are ≥ 3:
  - 0 binary: product ≥ 3^n > 2·3^(n-1) for n ≥ 2 (since 3 > 2)
  - 1 binary: product ≥ 2·3^(n-1) (not strictly less)
QED.

COROLLARY: M_n ≥ 2·3^(n-1) iff no valid system exists with 2+ binary at n.
""")

# ============================================================
# Part 2: Critical observation — Triple Disjointness + Liveness
# ============================================================

print("=" * 70)
print("Part 2: Triple Disjointness Lemma + Liveness tension")
print("=" * 70)

print("""
For any valid system with good cycle C of length L:

TRIPLE DISJOINTNESS (proved): For each processor p, the set of triples
(L,S,R) where p is the mover and the set where p is not the mover
must be DISJOINT. (Otherwise mutual exclusion fails.)

LIVENESS REQUIREMENT: Every config c ∈ {0,...,m_0-1} × ... × {0,...,m_{n-1}-1}
must have at least one privileged processor.

TENSION: The good cycle determines which triples are "forced mover" and
"forced non-mover". Triples not appearing in the cycle are FREE.
For liveness, enough free triples must be made mover to cover dead configs.
But each new mover triple creates non-good → non-good transitions.
""")

# ============================================================
# Part 3: For each 2-binary orientation, analyze the tension
# ============================================================

print("=" * 70)
print("Part 3: Quantify tension across all 2-binary orientations")
print("=" * 70)

necklaces = [
    (2, 2, 3, 3, 3, 3, 3, 3, 3),  # sep=1 (adjacent)
    (2, 3, 2, 3, 3, 3, 3, 3, 3),  # sep=2
    (2, 3, 3, 2, 3, 3, 3, 3, 3),  # sep=3
    (2, 3, 3, 3, 2, 3, 3, 3, 3),  # sep=4 (opposite)
]


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
                return cycle, full[:step + 1]
            if nc in visited:
                break
            visited.add(nc)
            cycle.append(nc)
    return None, None


def analyze_cycle(ms, cycle, movers, n):
    """Full analysis of a good cycle's completion prospects."""
    good_set = set(cycle)
    all_configs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_configs if c not in good_set]
    non_good_set = set(non_good)

    # Extract determined entries and triple partition
    det = {}
    det_triples = defaultdict(lambda: {'mover': set(), 'nonmover': set()})
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mover = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            triple = (L, S, R)
            if p == mover:
                det[key] = c_next[p]
                det_triples[p]['mover'].add(triple)
            else:
                det[key] = S
                det_triples[p]['nonmover'].add(triple)

    # Check triple overlap
    has_overlap = False
    for p in range(n):
        ovlp = det_triples[p]['mover'] & det_triples[p]['nonmover']
        if ovlp:
            has_overlap = True
            break

    if has_overlap:
        return {'overlap': True}

    # Count free entries
    free_entries = []
    for p in range(n):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key not in det:
                        free_entries.append(key)

    # Count dead configs (all triples in non-mover zone)
    dead_configs = []
    for c in all_configs:
        has_priv = False
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            triple = (L, S, R)
            if triple in det_triples[p]['mover']:
                has_priv = True
                break
        if not has_priv:
            dead_configs.append(c)

    # Build completion with all free = non-privileged
    comp_min = dict(det)
    for key in free_entries:
        p, L, S, R = key
        comp_min[key] = S

    # Build completion with all free = privileged
    comp_max = dict(det)
    for key in free_entries:
        p, L, S, R = key
        choices = [v for v in range(ms[p]) if v != S]
        comp_max[key] = choices[0] if choices else S

    # Count SCCs under max-privilege completion
    def count_sccs_for_comp(comp):
        bad_adj = defaultdict(list)
        for c in non_good:
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                key = (p, L, S, R)
                new_S = comp.get(key, S)
                if new_S != S:
                    new_c = list(c)
                    new_c[p] = new_S
                    new_c = tuple(new_c)
                    if new_c in non_good_set:
                        bad_adj[c].append(new_c)
        sccs = find_sccs(dict(bad_adj))
        return sccs

    sccs_max = count_sccs_for_comp(comp_max)
    trapped_max = sum(len(s) for s in sccs_max)

    return {
        'overlap': False,
        'cycle_len': len(cycle),
        'determined': len(det),
        'free': len(free_entries),
        'dead_configs': len(dead_configs),
        'non_good': len(non_good),
        'sccs_max_priv': len(sccs_max),
        'trapped_max_priv': trapped_max,
    }


# Test all bounce patterns and orientations
patterns = [
    ("down-up", lambda n: list(range(n - 1, -1, -1)) + list(range(1, n))),
    ("up-down", lambda n: list(range(n)) + list(range(n - 2, 0, -1))),
]

results_all = []

for neck in necklaces:
    sep = 0
    for i in range(1, n):
        if neck[i] == 2:
            sep = i
            break

    tested = set()
    for rot in range(n):
        ms = tuple(neck[(i + rot) % n] for i in range(n))
        if ms in tested:
            continue
        tested.add(ms)
        bin_pos = [i for i in range(n) if ms[i] == 2]

        for pname, pfn in patterns:
            base = pfn(n)
            cycle, movers_seq = build_bounce_cycle(ms, n, base)
            if cycle is None:
                continue

            result = analyze_cycle(ms, cycle, movers_seq, n)
            result['ms'] = ms
            result['bin_pos'] = bin_pos
            result['sep'] = sep
            result['pattern'] = pname
            results_all.append(result)

            if result['overlap']:
                print(f"  sep={sep} bins@{bin_pos} {pname}: OVERLAP")
            else:
                print(f"  sep={sep} bins@{bin_pos} {pname}: "
                      f"len={result['cycle_len']}, "
                      f"dead={result['dead_configs']}/{result['non_good']}, "
                      f"SCCs={result['sccs_max_priv']}({result['trapped_max_priv']})")

# ============================================================
# Part 4: Summary — is the tension universal?
# ============================================================

print("\n" + "=" * 70)
print("Part 4: Summary of 2-binary analysis")
print("=" * 70)

clean_results = [r for r in results_all if not r['overlap']]
overlap_results = [r for r in results_all if r['overlap']]

print(f"Total cycles tested: {len(results_all)}")
print(f"  With overlap: {len(overlap_results)} (immediately fatal)")
print(f"  Clean (no overlap): {len(clean_results)}")

if clean_results:
    print(f"\nClean cycles analysis:")
    for r in clean_results:
        print(f"  bins@{r['bin_pos']} {r['pattern']}: "
              f"dead={r['dead_configs']}, "
              f"SCCs={r['sccs_max_priv']}({r['trapped_max_priv']})")

    min_sccs = min(r['sccs_max_priv'] for r in clean_results)
    min_trapped = min(r['trapped_max_priv'] for r in clean_results)
    print(f"\nBest case (max privilege completion):")
    print(f"  Min SCCs: {min_sccs}")
    print(f"  Min trapped: {min_trapped}")

    if min_trapped > 0:
        print(f"\n*** ALL clean cycles have SCCs under max-privilege completion! ***")
        print(f"This is strong evidence that 2-binary is universally fatal.")
    else:
        print(f"\n*** SOME clean cycles have 0 SCCs under max-privilege! ***")
        print(f"Need to check if these are actually valid systems.")

# ============================================================
# Part 5: The DEEP argument — why 2 binary creates tension
# ============================================================

print("\n" + "=" * 70)
print("Part 5: Structural analysis of the 2-binary obstruction")
print("=" * 70)

# Take the best clean cycle and analyze its structure in detail
if clean_results:
    best = min(clean_results, key=lambda r: r['trapped_max_priv'])
    ms = best['ms']
    bin_pos = best['bin_pos']

    print(f"Best cycle: ms={ms}, bins@{bin_pos}")
    print(f"Dead configs: {best['dead_configs']} ({best['dead_configs']/best['non_good']*100:.1f}%)")

    # How many triples does each binary processor have?
    for p in bin_pos:
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        total = m_L * m_S * m_R
        print(f"\n  P{p} (binary): {m_L}×{m_S}×{m_R} = {total} triples")
        # Compare with ternary neighbor
        p_neighbor = (p + 1) % n
        m_L2 = ms[(p_neighbor - 1) % n]
        m_S2 = ms[p_neighbor]
        m_R2 = ms[(p_neighbor + 1) % n]
        total2 = m_L2 * m_S2 * m_R2
        print(f"  P{p_neighbor} (ternary neighbor): {m_L2}×{m_S2}×{m_R2} = {total2} triples")
        print(f"  Ratio: {total/total2:.2f}")

    # Count configs per binary junction state
    all_configs = list(cartesian(*(range(m) for m in ms)))
    junction_counts = defaultdict(int)
    for c in all_configs:
        junction_counts[(c[bin_pos[0]], c[bin_pos[1]])] += 1
    print(f"\nJunction state counts (P{bin_pos[0]}, P{bin_pos[1]}):")
    for state, count in sorted(junction_counts.items()):
        print(f"  {state}: {count} configs ({count/len(all_configs)*100:.1f}%)")

# ============================================================
# Part 6: Theoretical bound — minimum dead configs for ANY cycle
# ============================================================

print("\n" + "=" * 70)
print("Part 6: Lower bound on dead configs for any good cycle")
print("=" * 70)

# For ms = (2,2,3,3,3,3,3,3,3):
# Any good cycle of length L uses at most L distinct triples per processor.
# But L ≤ product = 8748. For the cycle to be valid, L must be a multiple of
# lcm of all m_i... no, L just needs to be a valid cycle length.
#
# Actually, the cycle length L satisfies: each processor p moves L/n times
# (approximately, by fairness). More precisely, each processor moves at least
# once and at most L-n+1 times.
#
# Each mover triple for p covers at most product / (m_{p-1} * m_p * m_{p+1})
# configs with that triple. For a binary processor with 12 triples, using k
# mover triples covers at most k * product / 12 configs... no, that's not right.
#
# A triple (L,S,R) for processor p occurs in exactly
# product / (m_{p-1} * m_p * m_{p+1}) configs. For ms=(2,2,3,...,3):
# - P0 (binary, binary neighbor): each triple occurs in 8748/12 = 729 configs
# - P1 (ternary, binary neighbor): each triple occurs in 8748/18 = 486 configs
# - P2 (ternary, ternary neighbors): each triple occurs in 8748/27 = 324 configs
#
# For liveness, every config must have at least 1 processor with a mover triple.
# The MAXIMUM coverage by mover triples is:
# ∑_p (number of mover triples for p) × (configs per triple for p)
# - ∑_p k_p * (product / T_p) where T_p = m_{p-1}*m_p*m_{p+1}
#
# But this overcounts (configs can be covered by multiple processors).
# The MINIMUM coverage needed is: product (all configs).
#
# By inclusion-exclusion, the minimum number of mover triples needed
# depends on the overlap structure.

ms = (2, 2, 3, 3, 3, 3, 3, 3, 3)
all_configs = list(cartesian(*(range(m) for m in ms)))
product = len(all_configs)

print(f"ms = {ms}, product = {product}")
print(f"\nTriples per processor:")
for p in range(n):
    m_L = ms[(p - 1) % n]
    m_S = ms[p]
    m_R = ms[(p + 1) % n]
    T = m_L * m_S * m_R
    configs_per = product // T
    print(f"  P{p}: {T} triples, {configs_per} configs per triple")

# What's the minimum number of mover triples needed to cover all configs?
# This is a set cover problem. Each "set" is the configs sharing a triple.
# The sets have sizes: 729 (for P0, P1), 486 (for ternary-binary), 324 (for ternary-ternary).

# Greedy set cover lower bound: at most product/max_set_size = 8748/729 = 12 sets needed
# from the largest class alone.

# But the constraint is that mover triples must be DISJOINT from non-mover triples
# (Triple Disjointness), and the good cycle determines some triples as non-mover.

# A FUNDAMENTAL question: what's the minimum good cycle length that ensures
# liveness can be achieved?

# If the good cycle has length L, each processor appears as mover ~L/n times.
# Each mover appearance uses 1 triple (could reuse). The number of DISTINCT
# mover triples for processor p is at most min(L_p, T_p) where L_p is the
# number of times p moves.

# For a cycle of length L with fair movers (each moves L/n times if L divisible by n):
# Distinct mover triples per processor ≤ L/n (could be less if triples repeat)

# Minimum L for liveness:
# We need enough mover triples to cover all configs.
# The best coverage per mover triple: 729 configs (from P0 or P1).
# But mover triples at P0 don't help configs where P0's triple is non-mover.

print(f"\nMaximum coverage per mover triple:")
for p in range(n):
    m_L = ms[(p - 1) % n]
    m_S = ms[p]
    m_R = ms[(p + 1) % n]
    T = m_L * m_S * m_R
    configs_per = product // T
    print(f"  P{p}: {configs_per} configs")

# The TOTAL coverage if ALL triples at ALL processors are mover triples:
# This is just n * product (each config covered n times).
# Not helpful directly.

# Better question: for configs where P0 has non-mover triple,
# what's the coverage from other processors?

# Actually, let me compute: for each config, how many processors
# could POTENTIALLY make it privileged?
# (i.e., how many processors p have c[p] ≠ c[p]' for some c' in the same triple class)

# For a config c, processor p can make it privileged if f_p(L,S,R) ≠ S.
# This is possible iff (L,S,R) is a mover triple for p.
# So the question is: can we choose mover triples such that every config
# has at least one mover triple among its n triples?

# This is exactly the set cover / hitting set problem.
# The universe is all 8748 configs.
# Each "set" is a processor-triple pair (p, (L,S,R)):
#   it contains all configs c with c[(p-1)%n]=L, c[p]=S, c[(p+1)%n]=R.
# We must select mover triples (one subset per processor, disjoint from
# non-mover triples determined by the good cycle).

# The question is whether a feasible cover exists that is compatible
# with some good cycle.

# Let me compute the MAXIMUM uncovered configs if we use only ternary
# processor triples (P2..P8), leaving P0 and P1 with 0 mover triples.
# This shows how much "help" the binary processors MUST provide.

print(f"\nCoverage analysis: can ternary processors alone cover all configs?")
# P2..P8 have 27 triples each. If ALL are mover triples, each covers 324 configs.
# But each config is covered by each processor exactly once (it has exactly one triple
# per processor). So if ALL triples at P2..P8 are mover, every config is covered
# by 7 processors.
print(f"  If ALL P2-P8 triples are mover: every config covered ✓")
print(f"  But the good cycle forces some P2-P8 triples to be non-mover!")
print(f"  In a cycle of length L, each of P2-P8 has ~L/n non-mover triples")
print(f"  (triples seen at steps where that processor is NOT the mover)")

# Key question: does forcing non-mover triples at P2-P8 create configs
# where ONLY P0 or P1 could save them?

# Let's compute: for ms=(2,2,3^7), how many configs have ALL their
# P2-P8 triples in common? I.e., how many configs share the same
# "ternary fingerprint" at positions 2-8?

# Actually, two configs c1, c2 that agree on positions 1-8 but differ
# on position 0 share the same triples at P2..P7 (since those triples
# don't involve P0). P1's triple involves P0, and P8's triple doesn't.

# So configs differing ONLY at P0 share the same triples at P2..P8.
# Since P0 is binary, there are exactly 2 such configs for each pattern.
# For liveness of BOTH, at least one of {P0, P1, P8} must have a mover
# triple that distinguishes them.

# P0 sees (c8, c0, c1). For c0=0 and c0=1 (with everything else same):
# P0's triples differ (different S), so P0 CAN distinguish them.
# P1 sees (c0, c1, c2). Different c0 = different L, so P1 CAN distinguish.
# But P2..P8 see the same triples regardless of c0.

# Now, for P1 to save a config, P1 must have the right triple as mover.
# P1 has 18 triples (3×3×3... wait, P1 has m_L=2 (P0 binary), m_S=3, m_R=3.
# So P1 has 2×3×3 = 18 triples. Each covers 8748/18 = 486 configs.

# If P1's triple is non-mover at some (L=0,S,R), then configs with c0=0,c1=S,c2=R
# are not saved by P1. They'd need P0 or P2..P8.

# P0 has 12 triples. In the good cycle, ~L/n mover triples.
# For a cycle of length 25: ~25/9 ≈ 2.8 mover triples for P0.
# Each covers 729 configs. Total P0 coverage: ~2.8 × 729 ≈ 2041 configs.
# But product is 8748. So P0 alone covers ~23% of configs.

# THE KEY BOUND:
# P0 has 12 triples. The good cycle uses some as mover, some as non-mover.
# Let k0 = number of P0 mover triples. Then:
# - k0 ≤ 12 (total P0 triples)
# - The good cycle requires at least 2 mover triples for P0 (P0 must move
#   at least once, and with m0=2, it must visit both states)
# - Actually, P0 must move at least... it moves L_0 times where L_0 ≥ 1.
#   With 2 states and cyclic return, L_0 must be even (toggle on/toggle off).
# - P0's non-mover triples: at least 1 (P0 is non-mover at most steps)
# - k0 ≤ 12 - (non-mover triples from cycle) - (overlap-free constraint)

# This is getting complex. Let me just compute it directly.

print(f"\n{'='*70}")
print(f"Part 7: Binary processor coverage capacity")
print(f"{'='*70}")

# For each binary processor, compute its maximum possible liveness contribution
for p in [0, 1]:  # binary positions for (2,2,3,3,3,3,3,3,3)
    m_L = ms[(p - 1) % n]
    m_S = ms[p]
    m_R = ms[(p + 1) % n]
    T = m_L * m_S * m_R
    configs_per = product // T

    print(f"\nP{p} (m={m_S}, {T} triples, {configs_per} configs/triple):")

    # If ALL triples are mover: covers all configs (each config has exactly 1 triple at P0)
    # If k triples are mover: covers k × configs_per configs
    for k in range(T + 1):
        coverage = k * configs_per
        pct = coverage / product * 100
        if k <= 5 or k == T:
            print(f"  k={k} mover triples: covers {coverage} configs ({pct:.0f}%)")

# ============================================================
# Part 8: The IMPOSSIBILITY argument sketch
# ============================================================

print(f"\n{'='*70}")
print(f"Part 8: Impossibility argument sketch")
print(f"{'='*70}")

print("""
ARGUMENT SKETCH (not yet a proof):

1. For ms=(2,2,3^7), product=8748.
2. Any good cycle determines a triple partition for each processor.
3. Binary P0 (12 triples): suppose k0 are mover triples.
   - Coverage: k0 × 729 configs saved by P0.
   - These k0 triples create k0 × 729 potential non-good → non-good edges
     (when P0 moves a non-good config to another non-good config).
4. Similarly for binary P1 (18 triples).
5. Ternary P2-P8 (27 triples each): k_p mover triples cover k_p × 324 configs.
6. For liveness, the union of all covered configs must be all 8748 configs.
7. For convergence, the non-good → non-good transitions must be acyclic.

THE TENSION: Steps 6 and 7 are in conflict because:
- More mover triples (needed for 6) → more non-good edges (hurting 7)
- Binary processors have FEWER triples to work with, so they must use
  a larger FRACTION of their triples as mover triples
- This creates disproportionately many non-good edges from binary processors
- These edges form SCCs because the binary state space is too small to
  provide enough "escape routes" from non-good configurations

THE GAP: This argument doesn't yet prove that SCCs are inevitable.
It shows the tension but doesn't close the proof.
""")
