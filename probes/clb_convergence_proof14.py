#!/usr/bin/env python3
"""
CONVERGENCE PROOF 14: Permutation-lex potential search
======================================================

KEY INSIGHT FROM PROOF13: All sorted_desc_lex violations have c[0]=0.

This script investigates:
1. For each position p, count transitions at p where r_p INCREASES.
   If some position p₀ has 0 such transitions, then the permutation-lex
   (r_{p₀}, ...) is a valid potential function with 0 violations!

2. Verify ALL sorted_desc_lex violations have c[0]=0 for n=5..10.

3. Check: within the c[0]=1 partition, is sorted_desc_lex violation-free?
   Within c[0]=0 partition?

4. For T_bot (pos 0) transitions: analyze the rank jump structure.
   Can we bound the jump as a function of the current rank tuple?
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

    fr_tuple = {}
    for c in bad_list:
        fr_tuple[c] = tuple(frozen[p][c] for p in range(n))

    # Enumerate transitions
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

    # ═══════════════════════════════════════════════════════════
    # Q1: For each position p, count transitions at p where r_p INCREASES
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Q1: r_p increases when position p fires")
    print(f"  {'Pos':>4} {'Table':>8} {'#trans_at_p':>12} {'#r_p_incr':>10} {'Pct':>8}")
    print(f"  {'-' * 50}")

    table_names = {0: 'T_bot', 1: 'T_low', n - 2: 'T_high', n - 1: 'T_top'}
    for p in range(2, n - 2):
        table_names[p] = 'T_mid'

    for p in range(n):
        trans_at_p = [(c, cp, i) for c, cp, i in transitions if i == p]
        increases = [(c, cp) for c, cp, i in trans_at_p
                     if frozen[p][cp] > frozen[p][c]]
        pct = 100 * len(increases) / len(trans_at_p) if trans_at_p else 0
        marker = " *** ZERO!" if len(increases) == 0 and trans_at_p else ""
        print(f"  {p:>4} {table_names[p]:>8} {len(trans_at_p):>12} "
              f"{len(increases):>10} {pct:>7.1f}%{marker}")

    # ═══════════════════════════════════════════════════════════
    # Q2: Verify ALL sorted_desc_lex violations have c[0]=0
    # ═══════════════════════════════════════════════════════════
    def lex_gt(a, b):
        for x, y in zip(a, b):
            if x > y:
                return True
            if x < y:
                return False
        return False

    sdl_viols = []
    for c, cp, i in transitions:
        old = tuple(sorted(fr_tuple[c], reverse=True))
        new = tuple(sorted(fr_tuple[cp], reverse=True))
        if not lex_gt(old, new):
            sdl_viols.append((c, cp, i))

    c0_counts = Counter(c[0] for c, _, _ in sdl_viols)
    cn_counts = Counter(c[n - 1] for c, _, _ in sdl_viols)
    boundary_counts = Counter((c[0], c[n - 1]) for c, _, _ in sdl_viols)

    print(f"\n  Q2: sorted_desc_lex violations ({len(sdl_viols)} / {nt})")
    print(f"    By c[0]: {dict(c0_counts)}")
    print(f"    By c[n-1]: {dict(cn_counts)}")
    print(f"    By (c[0],c[n-1]): {dict(boundary_counts)}")
    all_c0_zero = all(c[0] == 0 for c, _, _ in sdl_viols)
    print(f"    ALL violations have c[0]=0: {all_c0_zero}")

    # ═══════════════════════════════════════════════════════════
    # Q3: Within each c[0] partition, check sorted_desc_lex
    # ═══════════════════════════════════════════════════════════
    for c0_val in [0, 1]:
        part_trans = [(c, cp, i) for c, cp, i in transitions
                      if c[0] == c0_val and cp[0] == c0_val]
        cross_trans = [(c, cp, i) for c, cp, i in transitions
                       if c[0] == c0_val and cp[0] != c0_val]
        viols_in = sum(1 for c, cp, i in part_trans
                       if not lex_gt(tuple(sorted(fr_tuple[c], reverse=True)),
                                     tuple(sorted(fr_tuple[cp], reverse=True))))
        viols_cross = sum(1 for c, cp, i in cross_trans
                          if not lex_gt(tuple(sorted(fr_tuple[c], reverse=True)),
                                        tuple(sorted(fr_tuple[cp], reverse=True))))
        print(f"\n    c[0]={c0_val} partition:")
        print(f"      Internal transitions: {len(part_trans)}, violations: {viols_in}")
        print(f"      Cross transitions (to c[0]={1 - c0_val}): {len(cross_trans)}, "
              f"violations: {viols_cross}")

    # ═══════════════════════════════════════════════════════════
    # Q4: For each transition at pos 0 (T_bot): what is the rank jump?
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Q4: T_bot (pos 0) rank jumps")
    bot_trans = [(c, cp, i) for c, cp, i in transitions if i == 0]

    # Categorize by direction (0→1 vs 1→0)
    for direction in ['0→1', '1→0']:
        old_val = int(direction[0])
        subset = [(c, cp) for c, cp, i in bot_trans if c[0] == old_val]
        if not subset:
            continue
        deltas = [frozen[0][cp] - frozen[0][c] for c, cp in subset]
        max_delta = max(deltas)
        min_delta = min(deltas)
        incr = sum(1 for d in deltas if d > 0)
        print(f"    {direction}: {len(subset)} transitions, "
              f"Δr_0 range [{min_delta}, {max_delta}], "
              f"increases: {incr}")

    # ═══════════════════════════════════════════════════════════
    # Q5: Permutation-lex search (best position to put first)
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Q5: Permutation-lex: violations with position p first")
    print(f"  (Violation occurs only at transitions where mover = p and r_p increases)")
    best_p = None
    best_v = nt + 1
    for p in range(n):
        # Violations: transitions at p where r_p increases
        v = sum(1 for c, cp, i in transitions
                if i == p and frozen[p][cp] > frozen[p][c])
        if v < best_v:
            best_v = v
            best_p = p
        print(f"    p={p} ({table_names[p]}): {v} violations")
    print(f"    BEST: p={best_p} ({table_names[best_p]}) with {best_v} violations")

    # ═══════════════════════════════════════════════════════════
    # Q6: TWO-LEVEL permutation-lex: (r_{p0}, r_{p1}, ...)
    # If r_{p0} increases (mover=p0), check if r_{p1} decreases
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Q6: Two-level permutation-lex search")
    # For the best p0, check which p1 resolves the most violations
    p0 = best_p
    # Get violation transitions (mover=p0, r_{p0} increases)
    viol_trans = [(c, cp, i) for c, cp, i in transitions
                  if i == p0 and frozen[p0][cp] > frozen[p0][c]]
    print(f"    Level 1: p0={p0}, {len(viol_trans)} violations")
    for p1 in range(n):
        if p1 == p0:
            continue
        # Among violation transitions (mover=p0, r_{p0} increases),
        # how many also have r_{p1} increase?
        # (r_{p1} for p1 ≠ p0=mover: r_{p1} always decreases!)
        remaining = sum(1 for c, cp, i in viol_trans
                        if frozen[p1][cp] >= frozen[p1][c])
        print(f"      p1={p1}: {remaining} remaining violations "
              f"(r_{p1} doesn't decrease)")

    # ═══════════════════════════════════════════════════════════
    # Q7: Check if violations form paths/cycles among themselves
    # ═══════════════════════════════════════════════════════════
    if sdl_viols:
        viol_sources = set(c for c, _, _ in sdl_viols)
        viol_targets = set(cp for _, cp, _ in sdl_viols)
        viol_chains = viol_sources & viol_targets
        print(f"\n  Q7: Violation chain analysis")
        print(f"    Violation source configs: {len(viol_sources)}")
        print(f"    Violation target configs: {len(viol_targets)}")
        print(f"    Configs that are BOTH source and target: {len(viol_chains)}")
        # Can violations chain? A violation c→c' where c' is also a
        # violation source means the sorted_desc_lex can increase twice
        if viol_chains:
            max_chain = 0
            for start in viol_sources:
                # Follow violation edges
                cur = start
                chain_len = 0
                visited = {start}
                while True:
                    nexts = [cp for c, cp, i in sdl_viols if c == cur]
                    if not nexts:
                        break
                    cur = nexts[0]
                    if cur in visited:
                        chain_len = -1  # cycle!
                        break
                    visited.add(cur)
                    chain_len += 1
                max_chain = max(max_chain, chain_len)
            print(f"    Max violation chain length: {max_chain}")
            if max_chain == -1:
                print(f"    WARNING: violation edges form a CYCLE!")
        else:
            print(f"    No violation chains (good: violations are isolated)")

    return len(sdl_viols)


if __name__ == '__main__':
    for nv in [5, 6, 7, 8, 9]:
        prod = 4 * 3 ** (nv - 2)
        if prod > 30000:
            print(f"\n  n={nv}: product {prod} too large, skipping")
            break
        analyze(nv)
