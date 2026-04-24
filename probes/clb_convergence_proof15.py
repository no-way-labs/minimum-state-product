#!/usr/bin/env python3
"""
CONVERGENCE PROOF 15: The Two-Frozen-Rank Potential
====================================================

FROM PROOF14: When position 0 fires and r_0 increases, ALL other
frozen ranks strictly decrease. This is TRIVIALLY TRUE because for
transition at position i=0, every r_j with j≠0 decreases (j≠mover).

So the real question is: can we build a potential that handles the
r_0 increase at position 0?

NEW IDEA: Use r_0 as a SECONDARY key with a NEGATED sense.
Define φ(c) = (max_{j≠0} r_j(c), -r_0(c), sum_{j≠0} r_j(c))

For transition at position i≠0:
  - max_{j≠0} r_j: j≠0 and j≠i means these decrease. But j=i (if i≠0)
    has r_i which can increase. So max_{j≠0} might increase.
  - r_0 decreases (since 0≠mover), so -r_0 increases.

For transition at position i=0:
  - All r_j for j≠0 decrease → max_{j≠0} r_j decreases → first component decreases → DONE.

So the ONLY issue is transitions at position i≠0 where max_{j≠0} increases.

KEY TEST: For transitions at position i≠0, does max_{j≠0} r_j ALWAYS decrease?
If YES → φ(c) = (max_{j≠0} r_j, anything) works for all transitions.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque, Counter


def compute_frozen_ranks(bad_list, bad_set, fs, ms, n):
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
        assert len(topo) == len(bad_list)
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

    frozen = compute_frozen_ranks(bad_list, bad_set, fs, ms, n)

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

    nt = len(transitions)
    print(f"  {nt} transitions")

    def lex_gt(a, b):
        for x, y in zip(a, b):
            if x > y: return True
            if x < y: return False
        return False

    # ═══════════════════════════════════════════════════════════
    # TEST A: For each position p, check if excluding p from max
    # gives a valid first-level potential for non-p transitions
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST A: max_{{j≠p}} r_j as potential for transitions at i≠p")
    for p in range(n):
        viols = 0
        for c, cp, i in transitions:
            if i == p:
                continue
            old_max = max(frozen[j][c] for j in range(n) if j != p)
            new_max = max(frozen[j][cp] for j in range(n) if j != p)
            if old_max <= new_max:
                viols += 1
        print(f"    Exclude p={p}: {viols} violations among {sum(1 for _,_,i in transitions if i!=p)} non-p transitions")

    # ═══════════════════════════════════════════════════════════
    # TEST B: Two-phase potential
    # Phase 1 (i=0 transitions): max_{j≠0} r_j ALWAYS decreases
    # Phase 2 (i≠0 transitions): r_0 ALWAYS decreases
    # Combine: φ(c) = (max_{j≠0} r_j, r_0) if we can show both phases
    # Actually: (r_0, max_{j≠0} r_j) won't work if r_0 increases at i=0
    # But: for i=0: max_{j≠0} ALWAYS decreases? Check:
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST B: For i=0 transitions, does max_{{j≠0}} r_j always decrease?")
    viols_b = 0
    for c, cp, i in transitions:
        if i != 0:
            continue
        old_max = max(frozen[j][c] for j in range(1, n))
        new_max = max(frozen[j][cp] for j in range(1, n))
        if old_max <= new_max:
            viols_b += 1
    i0_count = sum(1 for _, _, i in transitions if i == 0)
    print(f"    Violations: {viols_b} / {i0_count}")

    # ═══════════════════════════════════════════════════════════
    # TEST C: Comprehensive exclude-one-position potential
    # φ_p(c) = (r_p(c), max_{j≠p} r_j(c), sum_{j≠p} r_j(c))
    # For i=p: r_p might increase, but max_{j≠p} decreases (all j≠p decrease)
    # For i≠p: r_p decreases → first component decreases → DONE
    # So the ONLY issue: for i=p, r_p increases → lex increases → violation
    # UNLESS: for i=p, max_{j≠p} always decreases MORE than r_p increases?
    # No — lex doesn't work that way.
    #
    # NEW IDEA: φ_p(c) = (max_{j≠p} r_j(c) - r_p(c), max_{j≠p} r_j(c))
    # For i≠p: r_p decreases by ≥1, max_{j≠p} may increase by at most r_i's jump.
    #   diff = max_{j≠p} - r_p. r_p decreases → diff increases.
    #   But max_{j≠p} might increase → diff changes unpredictably.
    # For i=p: r_p may increase, all j≠p decrease.
    #   max_{j≠p} decreases. r_p increases. diff decreases (good!).
    #   But we need STRICT decrease of the potential.
    # ═══════════════════════════════════════════════════════════

    # ═══════════════════════════════════════════════════════════
    # TEST D: THE KEY TEST
    # For each position p, define:
    #   φ_p(c) = n * max_{j≠p} r_j(c) - r_p(c)
    # For i=p: max_{j≠p} decreases by ≥1 (ALL j≠p decrease by ≥1).
    #   r_p increases by at most Δ.
    #   Δφ = n * (max_{j≠p} decrease) - (r_p increase) ≤ n*(-1) - Δ
    #   Wait: max_{j≠p} decreases by ≥1 when i=p? Let's verify.
    #   For i=p: all j≠p have r_j(c') ≤ r_j(c) - 1.
    #   So max_{j≠p} r_j(c') ≤ max_{j≠p} r_j(c) - 1? NO!
    #   max of decreased values ≤ max of original values - 1. YES!
    #   Because each value decreases by ≥1, max also decreases by ≥1.
    #
    # For i≠p: r_p decreases by ≥1. max_{j≠p} can increase (mover j=i has
    #   r_i increase). So n*Δmax - Δr_p = n*(increase) - (-1) = n*incr + 1.
    #   This could be positive (violation).
    #
    # So φ_p works for i=p but not necessarily for i≠p. Same old problem.
    # ═══════════════════════════════════════════════════════════

    # ═══════════════════════════════════════════════════════════
    # TEST E: PAIR potential — for each pair (p,q), define:
    #   φ_{p,q}(c) = (r_p(c), r_q(c))  [lex]
    # For transition at i:
    #   if i∉{p,q}: both r_p, r_q decrease → lex decrease ✓
    #   if i=p: r_p increases, r_q decreases → lex increase ✗
    #   if i=q: r_p decreases → lex decrease ✓ (regardless of r_q)
    # So violations only at i=p. And only when r_p increases.
    # The pair (p,q) has violation count = |{trans at p where r_p increases}|
    # This is the SAME as single position p. No improvement from pairs.
    # ═══════════════════════════════════════════════════════════

    # ═══════════════════════════════════════════════════════════
    # TEST F: NOVEL APPROACH — r_p for p = mover's LEFT NEIGHBOR
    # For transition at position i, the left neighbor is (i-1) mod n.
    # r_{(i-1)%n} always decreases (since (i-1)%n ≠ i for n≥3).
    # This gives a "mover-adapted" potential: always decreasing.
    # But it depends on the mover, so it's not a function of c alone.
    #
    # CAN we make it a function of c?
    # Define φ(c) = min over all privileged positions i of r_{(i-1)%n}(c)
    # This is a function of c alone. Does it always decrease?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST F: min over privileged positions of r_{{left_neighbor}}")
    viols_f = 0
    for c, cp, i in transitions:
        # Compute φ for c: min over all privileged i' of r_{(i'-1)%n}(c)
        priv_c = []
        for ii in range(n):
            L = c[(ii - 1) % n]; S = c[ii]; R = c[(ii + 1) % n]
            if fs[ii](L, S, R) != S:
                priv_c.append(ii)
        phi_c = min(frozen[(ii - 1) % n][c] for ii in priv_c)

        priv_cp = []
        for ii in range(n):
            L = cp[(ii - 1) % n]; S = cp[ii]; R = cp[(ii + 1) % n]
            if fs[ii](L, S, R) != S:
                priv_cp.append(ii)
        if cp in bad_set and priv_cp:
            phi_cp = min(frozen[(ii - 1) % n][cp] for ii in priv_cp)
        else:
            phi_cp = -1
        if phi_c <= phi_cp:
            viols_f += 1
    print(f"    Violations: {viols_f} / {nt} ({100 * viols_f / nt:.2f}%)")

    # ═══════════════════════════════════════════════════════════
    # TEST G: ACTUAL DAG RANK decomposition test
    # Compute the true DAG rank R(c). For each transition c→c',
    # R(c) > R(c') by definition. Can R(c) be expressed as
    # f(r_0(c), ..., r_{n-1}(c)) for some function f?
    # Check: is the map c → (r_0,...,r_{n-1}) compatible with DAG rank?
    # i.e., if fr_tuple(c) = fr_tuple(c'), is R(c) = R(c')?
    # ═══════════════════════════════════════════════════════════
    # Compute true DAG rank
    adj = {c: [] for c in bad_list}
    for c, cp, i in transitions:
        adj[c].append(cp)
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
    dag_rank = {}
    for c in reversed(topo):
        dag_rank[c] = max((dag_rank[s] + 1 for s in adj[c]), default=0)

    # Check if frozen-rank tuple determines DAG rank
    fr_to_ranks = {}
    for c in bad_list:
        t = tuple(frozen[p][c] for p in range(n))
        if t not in fr_to_ranks:
            fr_to_ranks[t] = set()
        fr_to_ranks[t].add(dag_rank[c])
    non_unique = sum(1 for ranks in fr_to_ranks.values() if len(ranks) > 1)
    max_spread = max(max(ranks) - min(ranks) for ranks in fr_to_ranks.values())
    print(f"\n  TEST G: Does frozen-rank tuple determine DAG rank?")
    print(f"    {len(fr_to_ranks)} unique tuples, {non_unique} with multiple DAG ranks")
    print(f"    Max DAG rank spread within same frozen tuple: {max_spread}")

    # ═══════════════════════════════════════════════════════════
    # TEST H: KEY STRUCTURAL TEST
    # For transition at position i, r_j decreases for all j≠i.
    # The SUM of decreases is Σ_{j≠i} (r_j(c) - r_j(c')) ≥ n-1.
    # The increase at position i is r_i(c') - r_i(c).
    # Check: is the increase ALWAYS < sum of decreases?
    # i.e., Σ_j (r_j(c) - r_j(c')) > 0 for all transitions?
    # This is the sum_r test from proof13 (8% violations). Already fails.
    #
    # But: is increase < (n-1) * min_{j≠i} decrease?
    # i.e., r_i(c')-r_i(c) < (n-1) * min_{j≠i}(r_j(c)-r_j(c'))
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST H: Increase vs (n-1)*min_decrease")
    viols_h = 0
    for c, cp, i in transitions:
        incr = frozen[i][cp] - frozen[i][c]
        if incr <= 0:
            continue
        min_decr = min(frozen[j][c] - frozen[j][cp] for j in range(n) if j != i)
        if incr >= (n - 1) * min_decr:
            viols_h += 1
    incr_count = sum(1 for c, cp, i in transitions if frozen[i][cp] > frozen[i][c])
    print(f"    Among {incr_count} transitions with r_i increase:")
    print(f"    increase ≥ (n-1)*min_decrease: {viols_h}")

    # ═══════════════════════════════════════════════════════════
    # TEST I: TWO-POSITION EXCLUDE potential
    # Exclude positions {0, i} for each i. max_{j∉{0,i}} always decreases
    # for transitions at 0 or i. Check for transitions at other positions.
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TEST I: Exclude two positions — max_{{j∉{{p,q}}}} r_j")
    best_pair = None
    best_viols = nt + 1
    for p in range(n):
        for q in range(p + 1, n):
            viols = 0
            for c, cp, i in transitions:
                if i == p or i == q:
                    # All j∉{p,q} have j≠mover, so r_j decreases.
                    # max also decreases. No violation.
                    continue
                # i ∉ {p,q}. Check if max_{j∉{p,q}} decreases.
                others = [j for j in range(n) if j != p and j != q]
                old_max = max(frozen[j][c] for j in others)
                new_max = max(frozen[j][cp] for j in others)
                if old_max <= new_max:
                    viols += 1
            if viols < best_viols:
                best_viols = viols
                best_pair = (p, q)
            if viols == 0:
                print(f"    Exclude {{p={p}, q={q}}}: 0 violations *** ZERO!")
    if best_viols > 0:
        print(f"    Best pair: {best_pair} with {best_viols} violations")

    return {}


if __name__ == '__main__':
    for nv in [5, 6, 7, 8]:
        analyze(nv)
