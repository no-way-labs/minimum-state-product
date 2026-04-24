#!/usr/bin/env python3
"""
CONVERGENCE PROOF 56: j-Double-Zero Subgraph Deep Analysis
==========================================================

Layer 2 is the j-double-zero subgraph: edges where
  Δint(2,1) = 0  AND  Δint_j(2,0) = 0

This subgraph is a DAG (verified n=5..12) but NO pair-count LP works (δ=0).
The DAG property must come from positional structure.

This script:
1. Analyze WHAT changes on j-double-zero edges
2. Look for value-position patterns (where is value 2? where is value 1?)
3. Test multiset orderings, lexicographic orderings
4. Test individual-value position measures
5. Look for the cascade mechanism (how does the Δfc≤0 path work?)
"""

import sys
import os
import time
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def build_excursion_graph(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0: dfc_le0_adj[c].append(succ)
                    if out != L and out != R: anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)

    exc_edges = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = set(); queue = [b]; visited.add(b); head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt); queue.append(nxt)

    return list(exc_edges), ms


def int_21(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 1)

def int_j_20(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1) % n] == 0)


def main():
    # ═══════════════════════════════════════════════════════════
    # STEP 1: What changes on j-double-zero edges?
    # ═══════════════════════════════════════════════════════════
    print("=" * 70)
    print("STEP 1: Changes on j-double-zero edges")
    print("=" * 70)

    for n_val in [8, 9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz_edges = []
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            jdz_edges.append((u, v))

        print(f"\n  n={n_val}: {len(jdz_edges)} j-double-zero edges ({time.time()-t0:.1f}s)")

        # How many positions differ?
        diff_counts = Counter()
        for u, v in jdz_edges:
            d = sum(1 for j in range(n) if u[j] != v[j])
            diff_counts[d] += 1
        print(f"    Hamming distances: {dict(sorted(diff_counts.items()))}")

        # Which positions change?
        pos_change = Counter()
        for u, v in jdz_edges:
            for j in range(n):
                if u[j] != v[j]:
                    pos_change[j] += 1
        print(f"    Position change frequency:")
        for j in sorted(pos_change.keys()):
            pct = 100 * pos_change[j] / len(jdz_edges) if jdz_edges else 0
            print(f"      pos {j}: {pos_change[j]:>6} ({pct:>5.1f}%)")

        # What value transitions occur at each position?
        val_trans = defaultdict(Counter)
        for u, v in jdz_edges:
            for j in range(n):
                if u[j] != v[j]:
                    val_trans[j][(u[j], v[j])] += 1
        print(f"    Value transitions (top 3 per position):")
        for j in sorted(val_trans.keys()):
            top = val_trans[j].most_common(3)
            parts = [f"{a}→{b}:{c}" for (a, b), c in top]
            print(f"      pos {j}: {', '.join(parts)}")

    # ═══════════════════════════════════════════════════════════
    # STEP 2: Candidate orderings for j-double-zero subgraph
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 2: Candidate orderings for j-double-zero subgraph")
    print("=" * 70)

    for n_val in [8, 9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz_edges = []
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            jdz_edges.append((u, v))

        measures = defaultdict(lambda: {'neg': 0, 'zero': 0, 'pos': 0})

        for u, v in jdz_edges:
            tests = {}

            # 1. Rightmost position of value 2
            rp2_u = max((j for j in range(n) if u[j] == 2), default=-1)
            rp2_v = max((j for j in range(n) if v[j] == 2), default=-1)
            tests['rightmost_2'] = rp2_v - rp2_u

            # 2. Leftmost position of value 2 (excluding pos 2)
            lp2_u = min((j for j in range(n) if u[j] == 2 and j != 2), default=n)
            lp2_v = min((j for j in range(n) if v[j] == 2 and j != 2), default=n)
            tests['leftmost_2_ex2'] = lp2_v - lp2_u

            # 3. Position-weighted count of 2s: Σ j·1[c[j]=2]
            pw2_u = sum(j for j in range(n) if u[j] == 2)
            pw2_v = sum(j for j in range(n) if v[j] == 2)
            tests['posweight_2'] = pw2_v - pw2_u

            # 4. Count of 2s
            c2_u = sum(1 for x in u if x == 2)
            c2_v = sum(1 for x in v if x == 2)
            tests['count_2'] = c2_v - c2_u

            # 5. Position-weighted count of 1s
            pw1_u = sum(j for j in range(n) if u[j] == 1)
            pw1_v = sum(j for j in range(n) if v[j] == 1)
            tests['posweight_1'] = pw1_v - pw1_u

            # 6. Count of 1s
            c1_u = sum(1 for x in u if x == 1)
            c1_v = sum(1 for x in v if x == 1)
            tests['count_1'] = c1_v - c1_u

            # 7. Rightmost non-zero position
            rnz_u = max((j for j in range(n) if u[j] != 0), default=-1)
            rnz_v = max((j for j in range(n) if v[j] != 0), default=-1)
            tests['rightmost_nz'] = rnz_v - rnz_u

            # 8. Leftmost non-zero position
            lnz_u = min((j for j in range(n) if u[j] != 0), default=n)
            lnz_v = min((j for j in range(n) if v[j] != 0), default=n)
            tests['leftmost_nz'] = lnz_v - lnz_u

            # 9. Config lexicographic
            tests['config_lex'] = 1 if v > u else (-1 if v < u else 0)

            # 10. Reverse-config lexicographic (comparing from right)
            ur = tuple(reversed(u))
            vr = tuple(reversed(v))
            tests['rev_config_lex'] = 1 if vr > ur else (-1 if vr < ur else 0)

            # 11. Interior sum
            isum_u = sum(u[j] for j in range(2, n-2))
            isum_v = sum(v[j] for j in range(2, n-2))
            tests['int_sum'] = isum_v - isum_u

            # 12. Position-weighted interior sum
            jpsum_u = sum(j * u[j] for j in range(2, n-2))
            jpsum_v = sum(j * v[j] for j in range(2, n-2))
            tests['int_jsum'] = jpsum_v - jpsum_u

            # 13. Multiset of interior values (sorted desc, lex)
            ms_u = tuple(sorted([u[j] for j in range(2, n-2)], reverse=True))
            ms_v = tuple(sorted([v[j] for j in range(2, n-2)], reverse=True))
            tests['multiset_desc'] = 1 if ms_v > ms_u else (-1 if ms_v < ms_u else 0)

            # 14. (count_2, count_1) lexicographic (fewer 2s, then fewer 1s)
            tests['lex_c2_c1'] = 1 if (c2_v, c1_v) > (c2_u, c1_u) else (
                -1 if (c2_v, c1_v) < (c2_u, c1_u) else 0)

            # 15. fc (frontier count)
            fc_u = sum(1 for j in range(n) if u[j] != u[(j+1)%n])
            fc_v = sum(1 for j in range(n) if v[j] != v[(j+1)%n])
            tests['fc'] = fc_v - fc_u

            # 16. Position-weighted fc
            pfc_u = sum(j for j in range(n) if u[j] != u[(j+1)%n])
            pfc_v = sum(j for j in range(n) if v[j] != v[(j+1)%n])
            tests['posweight_fc'] = pfc_v - pfc_u

            # 17. Number of "islands" (maximal runs of same value)
            def count_runs(c):
                runs = 1
                for j in range(1, n):
                    if c[j] != c[j-1]:
                        runs += 1
                return runs
            tests['n_runs'] = count_runs(v) - count_runs(u)

            # 18. Rightmost position of value 1
            rp1_u = max((j for j in range(n) if u[j] == 1), default=-1)
            rp1_v = max((j for j in range(n) if v[j] == 1), default=-1)
            tests['rightmost_1'] = rp1_v - rp1_u

            # 19. Spread of 2s (rightmost - leftmost)
            pos2_u = [j for j in range(n) if u[j] == 2]
            pos2_v = [j for j in range(n) if v[j] == 2]
            sp2_u = (max(pos2_u) - min(pos2_u)) if len(pos2_u) >= 2 else 0
            sp2_v = (max(pos2_v) - min(pos2_v)) if len(pos2_v) >= 2 else 0
            tests['spread_2'] = sp2_v - sp2_u

            # 20. Position-weighted descending pairs (a>b at (j,j+1))
            dpw_u = sum(j for j in range(2, n-2) if u[j] > u[(j+1)%n])
            dpw_v = sum(j for j in range(2, n-2) if v[j] > v[(j+1)%n])
            tests['posweight_desc'] = dpw_v - dpw_u

            for name, val in tests.items():
                if val > 0:
                    measures[name]['pos'] += 1
                elif val < 0:
                    measures[name]['neg'] += 1
                else:
                    measures[name]['zero'] += 1

        dt = time.time() - t0
        print(f"\n  n={n_val}: {len(jdz_edges)} jdz edges ({dt:.1f}s)")
        print(f"    {'Measure':>20} | {'neg':>6} | {'zero':>6} | {'pos':>6} | {'viol%':>6}")
        print(f"    {'-'*55}")

        # We want measures where 'pos' = 0 (always ≤ 0, decreasing)
        # or 'neg' = 0 (always ≥ 0, increasing)
        for name in sorted(measures.keys()):
            d = measures[name]
            total = d['neg'] + d['zero'] + d['pos']
            viol_pct = 100 * min(d['neg'], d['pos']) / total if total > 0 else 0
            tag = ""
            if d['pos'] == 0 and d['neg'] > 0:
                tag = " ← ALL≤0"
            elif d['neg'] == 0 and d['pos'] > 0:
                tag = " ← ALL≥0"
            print(f"    {name:>20} | {d['neg']:>6} | {d['zero']:>6} | {d['pos']:>6} | "
                  f"{viol_pct:>5.1f}%{tag}")

    # ═══════════════════════════════════════════════════════════
    # STEP 3: Analyze best candidates as next layer
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 3: Best candidates — deeper analysis")
    print("=" * 70)

    # Find which measures are monotone on jdz edges
    # Then build subgraph where they're zero and check DAG
    for n_val in [9, 10, 11]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz_edges = []
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            if int_j_20(v, n) - int_j_20(u, n) != 0:
                continue
            jdz_edges.append((u, v))

        # Test each best candidate
        candidates = {}
        for u, v in jdz_edges:
            # fc
            fc_u = sum(1 for j in range(n) if u[j] != u[(j+1)%n])
            fc_v = sum(1 for j in range(n) if v[j] != v[(j+1)%n])
            dfc = fc_v - fc_u

            # int_sum
            isum_u = sum(u[j] for j in range(2, n-2))
            isum_v = sum(v[j] for j in range(2, n-2))
            disum = isum_v - isum_u

            # int_jsum
            jpsum_u = sum(j * u[j] for j in range(2, n-2))
            jpsum_v = sum(j * v[j] for j in range(2, n-2))
            djpsum = jpsum_v - jpsum_u

            # count_2
            c2_u = sum(1 for x in u if x == 2)
            c2_v = sum(1 for x in v if x == 2)
            dc2 = c2_v - c2_u

            # posweight_2
            pw2_u = sum(j for j in range(n) if u[j] == 2)
            pw2_v = sum(j for j in range(n) if v[j] == 2)
            dpw2 = pw2_v - pw2_u

            for name, val in [('fc', dfc), ('int_sum', disum),
                              ('int_jsum', djpsum), ('count_2', dc2),
                              ('posweight_2', dpw2)]:
                if name not in candidates:
                    candidates[name] = {'min': val, 'max': val, 'pos': 0, 'neg': 0, 'zero': 0}
                candidates[name]['min'] = min(candidates[name]['min'], val)
                candidates[name]['max'] = max(candidates[name]['max'], val)
                if val > 0: candidates[name]['pos'] += 1
                elif val < 0: candidates[name]['neg'] += 1
                else: candidates[name]['zero'] += 1

        dt = time.time() - t0
        print(f"\n  n={n_val}: {len(jdz_edges)} jdz edges ({dt:.1f}s)")
        for name, d in sorted(candidates.items()):
            total = d['neg'] + d['zero'] + d['pos']
            viol = min(d['neg'], d['pos'])
            print(f"    {name:>15}: [{d['min']:>4},{d['max']:>4}]  "
                  f"neg={d['neg']:>6} zero={d['zero']:>6} pos={d['pos']:>6} "
                  f"viol={viol}")

    # ═══════════════════════════════════════════════════════════
    # STEP 4: Test COMBINED measures: lex(int_j(2,0), Q) on zero edges
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 4: Combined lex ordering on FULL zero-edge subgraph")
    print("=" * 70)
    print("Testing: lex(int_j(2,0), Q) where Q is a candidate for layer 2")

    for n_val in [9, 10, 11]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        zero_edges = []
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            zero_edges.append((u, v))

        # For each zero edge, compute (Δint_j(2,0), ΔQ)
        # The lex ordering (int_j(2,0), Q) is valid if:
        #   On ALL zero edges: Δint_j(2,0) < 0, OR (Δint_j(2,0)=0 AND ΔQ < 0)
        # We know Δint_j(2,0) ≤ 0 always.
        # So violations = edges where Δint_j(2,0) = 0 AND ΔQ ≥ 0.

        # Test candidates for Q
        cand_viols = defaultdict(int)
        cand_zeros = defaultdict(int)
        n_jdz = 0

        for u, v in zero_edges:
            dj20 = int_j_20(v, n) - int_j_20(u, n)
            if dj20 < 0:
                continue  # Already strictly decreasing in layer 1
            n_jdz += 1

            # Candidates for Q (should decrease on jdz edges)
            tests = {}

            # Interior sum
            tests['int_sum'] = sum(v[j] - u[j] for j in range(2, n-2))
            # Position-weighted sum
            tests['int_jsum'] = sum(j*(v[j] - u[j]) for j in range(2, n-2))
            # fc
            tests['fc'] = sum(int(v[j]!=v[(j+1)%n]) - int(u[j]!=u[(j+1)%n]) for j in range(n))
            # count_2
            tests['count_2'] = sum(int(v[j]==2) - int(u[j]==2) for j in range(n))
            # posweight_2
            tests['posweight_2'] = sum(j*(int(v[j]==2) - int(u[j]==2)) for j in range(n))
            # Config lex
            tests['config_lex'] = 1 if v > u else (-1 if v < u else 0)
            # Interior config lex
            ui = tuple(u[j] for j in range(2, n-2))
            vi = tuple(v[j] for j in range(2, n-2))
            tests['int_config_lex'] = 1 if vi > ui else (-1 if vi < ui else 0)

            for name, val in tests.items():
                if val > 0:
                    cand_viols[name] += 1
                elif val == 0:
                    cand_zeros[name] += 1

        dt = time.time() - t0
        print(f"\n  n={n_val}: {n_jdz} j-double-zero edges ({dt:.1f}s)")
        for name in sorted(cand_viols.keys()):
            v = cand_viols[name]
            z = cand_zeros[name]
            total = n_jdz
            pct = 100 * v / total if total > 0 else 0
            tag = " ← PERFECT LAYER 2" if v == 0 else ""
            print(f"    {name:>20}: {v:>6} violations, {z:>6} zeros ({pct:>5.1f}%){tag}")

    # ═══════════════════════════════════════════════════════════
    # STEP 5: Multi-layer chain extension
    # ═══════════════════════════════════════════════════════════
    print()
    print("=" * 70)
    print("STEP 5: Extending the chain with more layers")
    print("=" * 70)

    # On jdz edges, find best measure Q. On jdz+Q=0 edges, find next, etc.
    for n_val in [9, 10]:
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        # Start with zero edges
        current_edges = []
        for u, v in exc_edges:
            if int_21(v, n) - int_21(u, n) != 0:
                continue
            current_edges.append((u, v))

        layers = ["int(2,1)"]

        # Try to peel layers
        for layer_num in range(1, 10):
            if not current_edges:
                print(f"\n  n={n_val}: Layer {layer_num} — NO edges remaining! Done.")
                break

            # Test all measure on current edges
            best_name = None
            best_viols = len(current_edges)
            best_zeros = len(current_edges)
            results = {}

            for u, v in current_edges:
                tests = {}
                tests['int_j(2,0)'] = int_j_20(v, n) - int_j_20(u, n)
                tests['int_sum'] = sum(v[j] - u[j] for j in range(2, n-2))
                tests['int_jsum'] = sum(j*(v[j] - u[j]) for j in range(2, n-2))
                tests['fc'] = sum(int(v[j]!=v[(j+1)%n]) - int(u[j]!=u[(j+1)%n]) for j in range(n))
                tests['count_2'] = sum(int(v[j]==2) - int(u[j]==2) for j in range(n))
                tests['pw_2'] = sum(j*(int(v[j]==2) - int(u[j]==2)) for j in range(n))
                tests['count_1'] = sum(int(v[j]==1) - int(u[j]==1) for j in range(n))
                tests['pw_1'] = sum(j*(int(v[j]==1) - int(u[j]==1)) for j in range(n))

                # All 9 position-weighted pair counts
                for a in range(3):
                    for b in range(3):
                        key = f'int_j({a},{b})'
                        tests[key] = sum(j * (int(v[j]==a and v[(j+1)%n]==b) -
                                              int(u[j]==a and u[(j+1)%n]==b))
                                         for j in range(2, n-2))
                # All 9 unweighted pair counts
                for a in range(3):
                    for b in range(3):
                        key = f'int({a},{b})'
                        tests[key] = sum(int(v[j]==a and v[(j+1)%n]==b) -
                                         int(u[j]==a and u[(j+1)%n]==b)
                                         for j in range(2, n-2))

                for name, val in tests.items():
                    if name not in results:
                        results[name] = {'pos': 0, 'neg': 0, 'zero': 0}
                    if val > 0: results[name]['pos'] += 1
                    elif val < 0: results[name]['neg'] += 1
                    else: results[name]['zero'] += 1

            # Find measures with 0 violations (pos=0 for ≤0, or neg=0 for ≥0)
            monotone_le0 = []
            monotone_ge0 = []
            for name, d in results.items():
                if d['pos'] == 0 and d['neg'] > 0:
                    monotone_le0.append((name, d['zero'], d['neg']))
                if d['neg'] == 0 and d['pos'] > 0:
                    monotone_ge0.append((name, d['zero'], d['pos']))

            print(f"\n  n={n_val}, Layer {layer_num} ({len(current_edges)} edges):")
            print(f"    Monotone ≤0: {len(monotone_le0)}")
            for name, z, neg in sorted(monotone_le0, key=lambda x: x[1]):
                pct = 100 * z / len(current_edges) if current_edges else 0
                print(f"      {name:>15}: {neg:>6} strict, {z:>6} zero ({pct:>5.1f}%)")
            print(f"    Monotone ≥0: {len(monotone_ge0)}")
            for name, z, pos in sorted(monotone_ge0, key=lambda x: x[1]):
                pct = 100 * z / len(current_edges) if current_edges else 0
                print(f"      {name:>15}: {pos:>6} strict, {z:>6} zero ({pct:>5.1f}%)")

            # Choose best layer (least zeros among monotone measures)
            all_monotone = [(name, z, 'le0') for name, z, _ in monotone_le0] + \
                           [(name, z, 'ge0') for name, z, _ in monotone_ge0]

            if not all_monotone:
                print(f"    NO monotone measures found! Chain STUCK.")
                break

            all_monotone.sort(key=lambda x: x[1])
            best_name, best_z, best_dir = all_monotone[0]
            layers.append(f"{best_name}({'≤' if best_dir == 'le0' else '≥'}0)")
            print(f"    → Choosing: {best_name} ({best_dir}), {best_z} zeros")

            if best_z == 0:
                print(f"    PERFECT! All edges strict. Chain complete.")
                break

            # Filter to zero-edges of this layer
            new_edges = []
            for u, v in current_edges:
                tests = {}
                tests['int_j(2,0)'] = int_j_20(v, n) - int_j_20(u, n)
                tests['int_sum'] = sum(v[j] - u[j] for j in range(2, n-2))
                tests['int_jsum'] = sum(j*(v[j] - u[j]) for j in range(2, n-2))
                tests['fc'] = sum(int(v[j]!=v[(j+1)%n]) - int(u[j]!=u[(j+1)%n]) for j in range(n))
                tests['count_2'] = sum(int(v[j]==2) - int(u[j]==2) for j in range(n))
                tests['pw_2'] = sum(j*(int(v[j]==2) - int(u[j]==2)) for j in range(n))
                tests['count_1'] = sum(int(v[j]==1) - int(u[j]==1) for j in range(n))
                tests['pw_1'] = sum(j*(int(v[j]==1) - int(u[j]==1)) for j in range(n))
                for a in range(3):
                    for b in range(3):
                        key = f'int_j({a},{b})'
                        tests[key] = sum(j * (int(v[j]==a and v[(j+1)%n]==b) -
                                              int(u[j]==a and u[(j+1)%n]==b))
                                         for j in range(2, n-2))
                for a in range(3):
                    for b in range(3):
                        key = f'int({a},{b})'
                        tests[key] = sum(int(v[j]==a and v[(j+1)%n]==b) -
                                         int(u[j]==a and u[(j+1)%n]==b)
                                         for j in range(2, n-2))

                if tests[best_name] == 0:
                    new_edges.append((u, v))

            current_edges = new_edges

        print(f"\n  n={n_val}: Layer chain: {' → '.join(layers)}")


if __name__ == '__main__':
    main()
