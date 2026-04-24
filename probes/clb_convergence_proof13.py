#!/usr/bin/env python3
"""
CONVERGENCE PROOF 13: Non-linear frozen-rank potentials
========================================================

Test comprehensive battery of potential function candidates
based on frozen-rank data.

KEY QUESTION: Does the Dershowitz-Manna multiset ordering on frozen
ranks work? This is equivalent to the sorted-descending lex ordering
on the tuple (r_0,...,r_{n-1}). If so, it gives a clean termination
proof via multiset well-ordering.

Tests:
1. Scalar: max(r_p), sum(r_p), sum(sqrt), sum(log), product
2. Lex: sorted_desc, (max,sum), max+eps*sum
3. Dershowitz-Manna condition: r'_i < max_{j≠i} r_j(c)
4. Frozen-rank tuple injectivity
5. Violation structure analysis
"""

import sys
import os
import math
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, Counter


def compute_frozen_ranks(bad_list, bad_set, fs, ms, n):
    """Compute frozen rank for each position p.
    r_p(c) = longest path from c in the p-frozen DAG (transitions at pos != p).
    """
    all_ranks = {}
    for p in range(n):
        adj = {c: [] for c in bad_list}
        for c in bad_list:
            for i in range(n):
                if i == p:
                    continue
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                new_S = fs[i](L, S, R)
                if new_S != S:
                    lst = list(c)
                    lst[i] = new_S
                    succ = tuple(lst)
                    if succ in bad_set:
                        adj[c].append(succ)

        in_deg = {c: 0 for c in bad_list}
        for c in bad_list:
            for s in adj[c]:
                in_deg[s] += 1
        q = deque(c for c in bad_list if in_deg[c] == 0)
        topo = []
        while q:
            c = q.popleft()
            topo.append(c)
            for s in adj[c]:
                in_deg[s] -= 1
                if in_deg[s] == 0:
                    q.append(s)

        assert len(topo) == len(bad_list), f"p-frozen DAG not a DAG for p={p}!"

        rank = {}
        for c in reversed(topo):
            rank[c] = max((rank[s] + 1 for s in adj[c]), default=0)

        all_ranks[p] = rank

    return all_ranks


def analyze(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    print(f"\n{'=' * 70}")
    print(f"n = {n_val}: {len(bad_list)} bad configs")
    print(f"{'=' * 70}")

    # Compute frozen ranks
    frozen = compute_frozen_ranks(bad_list, bad_set, fs, ms, n)

    # Frozen-rank tuple for each config
    fr_tuple = {}
    for c in bad_list:
        fr_tuple[c] = tuple(frozen[p][c] for p in range(n))

    # Enumerate all transitions
    transitions = []
    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            new_S = fs[i](L, S, R)
            if new_S != S:
                lst = list(c)
                lst[i] = new_S
                succ = tuple(lst)
                if succ in bad_set:
                    transitions.append((c, succ, i))

    print(f"  {len(transitions)} transitions")
    nt = len(transitions)

    # Helper: lex comparison
    def lex_gt(a, b):
        for x, y in zip(a, b):
            if x > y:
                return True
            if x < y:
                return False
        return False

    # ═══════════════════════════════════════════════════════════
    # TEST 1: Scalar potentials
    # ═══════════════════════════════════════════════════════════
    potentials = {}

    # max(r_p)
    v = sum(1 for c, cp, i in transitions
            if max(fr_tuple[c]) <= max(fr_tuple[cp]))
    potentials['max_r'] = v

    # sum(r_p)
    v = sum(1 for c, cp, i in transitions
            if sum(fr_tuple[c]) <= sum(fr_tuple[cp]))
    potentials['sum_r'] = v

    # sum(sqrt(r+1))
    def fsqrt(t):
        return sum(math.sqrt(r + 1) for r in t)
    v = sum(1 for c, cp, i in transitions
            if fsqrt(fr_tuple[c]) <= fsqrt(fr_tuple[cp]) + 1e-9)
    potentials['sum_sqrt'] = v

    # sum(log(r+2))
    def flog(t):
        return sum(math.log(r + 2) for r in t)
    v = sum(1 for c, cp, i in transitions
            if flog(fr_tuple[c]) <= flog(fr_tuple[cp]) + 1e-9)
    potentials['sum_log'] = v

    # product(r+1)
    def fprod(t):
        p = 1
        for r in t:
            p *= (r + 1)
        return p
    v = sum(1 for c, cp, i in transitions
            if fprod(fr_tuple[c]) <= fprod(fr_tuple[cp]))
    potentials['product_r'] = v

    # sum(1/(r+1)) — HARMONIC, want INCREASE (= dual potential)
    def fharm(t):
        return sum(1.0 / (r + 1) for r in t)
    v = sum(1 for c, cp, i in transitions
            if fharm(fr_tuple[c]) >= fharm(fr_tuple[cp]) - 1e-9)
    potentials['harm_incr'] = v

    # ═══════════════════════════════════════════════════════════
    # TEST 2: Tuple/lex potentials
    # ═══════════════════════════════════════════════════════════

    # sorted desc lex (= Dershowitz-Manna multiset ordering)
    sdl_viols = []
    for c, cp, i in transitions:
        old = tuple(sorted(fr_tuple[c], reverse=True))
        new = tuple(sorted(fr_tuple[cp], reverse=True))
        if not lex_gt(old, new):
            sdl_viols.append((c, cp, i, old, new))
    potentials['sorted_desc_lex'] = len(sdl_viols)

    # (max, sum) lex
    ms_viols = []
    for c, cp, i in transitions:
        old = (max(fr_tuple[c]), sum(fr_tuple[c]))
        new = (max(fr_tuple[cp]), sum(fr_tuple[cp]))
        if not lex_gt(old, new):
            ms_viols.append((c, cp, i, old, new))
    potentials['(max,sum)_lex'] = len(ms_viols)

    # (max, -count_at_max, sum) lex
    def max_count_sum(t):
        mx = max(t)
        cnt = sum(1 for r in t if r == mx)
        return (mx, -cnt, sum(t))
    mcs_viols = []
    for c, cp, i in transitions:
        old = max_count_sum(fr_tuple[c])
        new = max_count_sum(fr_tuple[cp])
        if not lex_gt(old, new):
            mcs_viols.append((c, cp, i, old, new))
    potentials['(max,-cnt,sum)_lex'] = len(mcs_viols)

    # max + eps * sum
    eps = 0.001
    v = sum(1 for c, cp, i in transitions
            if max(fr_tuple[c]) + eps * sum(fr_tuple[c])
            <= max(fr_tuple[cp]) + eps * sum(fr_tuple[cp]) + 1e-12)
    potentials['max+eps*sum'] = v

    # ═══════════════════════════════════════════════════════════
    # TEST 3: Concave combinations (penalize large values less)
    # ═══════════════════════════════════════════════════════════

    # sum(r^alpha) for various alpha < 1
    for alpha in [0.3, 0.5, 0.7]:
        def falpha(t, a=alpha):
            return sum((r + 1) ** a for r in t)
        v = sum(1 for c, cp, i in transitions
                if falpha(fr_tuple[c]) <= falpha(fr_tuple[cp]) + 1e-9)
        potentials[f'sum_r^{alpha}'] = v

    # ═══════════════════════════════════════════════════════════
    # TEST 4: Minimum-over-all-except-mover
    # ═══════════════════════════════════════════════════════════

    # For each transition, min_{j!=i} r_j always decreases
    # (since each r_j for j!=i decreases by >=1)
    # So min_others is a valid potential IF we can identify the mover
    # This isn't a function of c alone, but let's check it
    v = sum(1 for c, cp, i in transitions
            if min(frozen[j][c] for j in range(n) if j != i)
            <= min(frozen[j][cp] for j in range(n) if j != i))
    potentials['min_others'] = v

    # But what about second_min(r_0,...,r_{n-1})?
    def second_min(t):
        s = sorted(t)
        return s[1] if len(s) > 1 else s[0]
    v = sum(1 for c, cp, i in transitions
            if second_min(fr_tuple[c]) <= second_min(fr_tuple[cp]))
    potentials['second_min'] = v

    # ═══════════════════════════════════════════════════════════
    # PRINT RESULTS
    # ═══════════════════════════════════════════════════════════
    print(f"\n  POTENTIAL FUNCTION TEST RESULTS:")
    print(f"  {'Potential':<25} {'Violations':>10} {'Pct':>8}")
    print(f"  {'-' * 48}")
    for name in ['max_r', 'sum_r', 'sorted_desc_lex', '(max,sum)_lex',
                  '(max,-cnt,sum)_lex', 'max+eps*sum',
                  'sum_sqrt', 'sum_log', 'product_r', 'harm_incr',
                  'sum_r^0.3', 'sum_r^0.5', 'sum_r^0.7',
                  'min_others', 'second_min']:
        v = potentials[name]
        pct = 100 * v / nt if nt > 0 else 0
        marker = " *** ZERO!" if v == 0 else ""
        print(f"  {name:<25} {v:>10} {pct:>7.2f}%{marker}")

    # ═══════════════════════════════════════════════════════════
    # Frozen-rank tuple injectivity
    # ═══════════════════════════════════════════════════════════
    fr_values = {}
    for c in bad_list:
        t = fr_tuple[c]
        if t not in fr_values:
            fr_values[t] = []
        fr_values[t].append(c)
    n_unique = len(fr_values)
    collisions = sum(1 for cs in fr_values.values() if len(cs) > 1)
    max_coll = max(len(cs) for cs in fr_values.values())
    print(f"\n  Frozen-rank tuple: {n_unique} unique / {len(bad_list)} configs "
          f"(injective: {'YES' if n_unique == len(bad_list) else 'NO'})")
    if collisions > 0:
        print(f"  Collisions: {collisions} tuples, max collision size {max_coll}")

    # ═══════════════════════════════════════════════════════════
    # Dershowitz-Manna condition
    # ═══════════════════════════════════════════════════════════
    dm_viols = []
    for c, cp, i in transitions:
        r_new_i = frozen[i][cp]
        max_others_old = max(frozen[j][c] for j in range(n) if j != i)
        if r_new_i >= max_others_old:
            dm_viols.append((c, cp, i, r_new_i, max_others_old))

    print(f"\n  Dershowitz-Manna condition (r'_i < max_{{j!=i}} r_j(c)):")
    print(f"    Violations: {len(dm_viols)} / {nt} ({100 * len(dm_viols) / nt:.2f}%)")
    if dm_viols:
        pos_counts = Counter(i for _, _, i, _, _ in dm_viols)
        print(f"    By mover: {dict(sorted(pos_counts.items()))}")
        if len(dm_viols) <= 15:
            for c, cp, i, rn, mx in dm_viols:
                print(f"    c={c} mover={i}: r'_i={rn}, max_others={mx}")
                print(f"      fr_old={fr_tuple[c]}, fr_new={fr_tuple[cp]}")

    # ═══════════════════════════════════════════════════════════
    # Violation structure for best candidates
    # ═══════════════════════════════════════════════════════════
    for name, viols in [('sorted_desc_lex', sdl_viols),
                        ('(max,sum)_lex', ms_viols),
                        ('(max,-cnt,sum)_lex', mcs_viols)]:
        if not viols:
            continue
        print(f"\n  VIOLATIONS for '{name}' ({len(viols)}):")
        pos_counts = Counter(i for _, _, i, _, _ in viols)
        print(f"    By mover: {dict(sorted(pos_counts.items()))}")
        # Show overlap with other potentials
        viol_set = set((id(c), id(cp)) for c, cp, i, _, _ in viols)
        if len(viols) <= 20:
            for c, cp, i, old, new in viols[:20]:
                print(f"    c={c} mover={i}")
                print(f"      old={old}, new={new}")
                print(f"      fr_old={fr_tuple[c]}, fr_new={fr_tuple[cp]}")

    # ═══════════════════════════════════════════════════════════
    # Check overlap: transitions violating BOTH max and sum
    # ═══════════════════════════════════════════════════════════
    max_viol_set = set()
    sum_viol_set = set()
    for c, cp, i in transitions:
        key = (c, cp, i)
        if max(fr_tuple[c]) <= max(fr_tuple[cp]):
            max_viol_set.add(key)
        if sum(fr_tuple[c]) <= sum(fr_tuple[cp]):
            sum_viol_set.add(key)
    overlap = max_viol_set & sum_viol_set
    print(f"\n  Violation overlap analysis:")
    print(f"    max violations: {len(max_viol_set)}")
    print(f"    sum violations: {len(sum_viol_set)}")
    print(f"    BOTH max AND sum: {len(overlap)}")
    print(f"    max-only: {len(max_viol_set - sum_viol_set)}")
    print(f"    sum-only: {len(sum_viol_set - max_viol_set)}")
    if overlap:
        print(f"    -> (max,sum)_lex has {len(overlap)} violations")
    else:
        print(f"    -> (max,sum)_lex has 0 violations! POTENTIAL PROOF!")

    return potentials


if __name__ == '__main__':
    for nv in [5, 6, 7, 8]:
        analyze(nv)
