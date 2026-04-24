#!/usr/bin/env python3
"""
CONVERGENCE PROOF 64: Structural analysis of jdz edges
=======================================================
What positions change? What anomalous types? Boundary vs interior?
Can we find a STRUCTURAL argument for DAG?
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system, T_mid, T_bot, T_low, T_high, T_top
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter

def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

def build_excursion_graph_detailed(n_val):
    """Returns excursion edges with anomalous step info."""
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    # Classify anomalous entries
    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n_val):
            L = c[(i-1) % n_val]; S = c[i]; R = c[(i+1) % n_val]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    if dfc <= 0: dfc_le0_adj[c].append(succ)
                    if out != L and out != R:
                        anom_edges.append((c, succ, i, dfc))

    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    anom_info_map = {}  # (src, target_of_anom_step) -> (position, L, S, R, out)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)
        anom_info_map[(c, succ)] = (i, c[(i-1)%n_val], c[i], c[(i+1)%n_val], succ[i])

    exc_edges = []
    for b in set(s for _, s, _, _ in anom_edges):
        visited = {b}; queue = [b]; head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.append((src, node, b))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt); queue.append(nxt)

    return exc_edges, ms, fs, anom_info_map

def int_21(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 1)
def int_j_20(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 0)

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 11):
        t0 = time.time()
        exc_edges, ms, fs, anom_info = build_excursion_graph_detailed(n_val)
        n = n_val

        # Filter to jdz
        jdz = []
        for u, v, b in exc_edges:
            if int_21(v,n)-int_21(u,n) != 0: continue
            if int_j_20(v,n)-int_j_20(u,n) != 0: continue
            jdz.append((u, v, b))
        jdz_unique = list(set((u,v) for u,v,b in jdz))

        print(f"\n{'='*60}", flush=True)
        print(f"n={n}: {len(jdz_unique)} jdz edges ({time.time()-t0:.1f}s)", flush=True)
        print(f"{'='*60}", flush=True)

        if not jdz_unique:
            print("  No jdz edges", flush=True)
            continue

        # 1. Which positions change?
        pos_change_count = Counter()
        n_positions_changed = Counter()
        boundary_change = Counter()  # does (c[0],c[n-1]) change?

        for u, v in jdz_unique:
            changed = [j for j in range(n) if u[j] != v[j]]
            n_positions_changed[len(changed)] += 1
            for j in changed:
                if j <= 1:
                    pos_change_count[f'P{j}(L)'] += 1
                elif j >= n-2:
                    pos_change_count[f'P{j}(R)'] += 1
                else:
                    pos_change_count[f'P{j}(int)'] += 1

            bdry_u = (u[0], u[n-1])
            bdry_v = (v[0], v[n-1])
            if bdry_u == bdry_v:
                boundary_change['same'] += 1
            else:
                boundary_change[f'{bdry_u}->{bdry_v}'] += 1

        print(f"\n  Positions changed per edge: {dict(n_positions_changed)}", flush=True)
        print(f"  Boundary (P0,P{n-1}) change:", flush=True)
        for k, v in sorted(boundary_change.items()):
            print(f"    {k}: {v} ({100*v/len(jdz_unique):.1f}%)", flush=True)
        print(f"  Position change frequency:", flush=True)
        for k, v in sorted(pos_change_count.items()):
            print(f"    {k}: {v}", flush=True)

        # 2. What value changes occur at each position type?
        val_changes = defaultdict(Counter)
        for u, v in jdz_unique:
            for j in range(n):
                if u[j] != v[j]:
                    ptype = 'bot' if j==0 else 'low' if j==1 else 'high' if j==n-2 else 'top' if j==n-1 else 'mid'
                    val_changes[ptype][(u[j], v[j])] += 1

        print(f"\n  Value changes by position type:", flush=True)
        for ptype in ['bot', 'low', 'mid', 'high', 'top']:
            if ptype in val_changes:
                print(f"    {ptype}: {dict(val_changes[ptype])}", flush=True)

        # 3. For edges where boundary doesn't change: what's the interior pattern?
        if boundary_change.get('same', 0) > 0:
            # Group by boundary type
            by_bdry = defaultdict(list)
            for u, v in jdz_unique:
                if (u[0], u[n-1]) == (v[0], v[n-1]):
                    by_bdry[(u[0], u[n-1])].append((u, v))

            print(f"\n  Boundary-preserving edges by boundary type:", flush=True)
            for bdry, edges in sorted(by_bdry.items()):
                print(f"    bdry={bdry}: {len(edges)} edges", flush=True)

        # 4. Interior diff pattern: how does the "diff string" look?
        diff_patterns = Counter()
        for u, v in jdz_unique[:min(5000, len(jdz_unique))]:
            diff = tuple(v[j] - u[j] for j in range(n))
            diff_patterns[diff] += 1

        n_unique_diffs = len(diff_patterns)
        print(f"\n  Unique diff patterns: {n_unique_diffs}", flush=True)
        if n_unique_diffs <= 30:
            for diff, count in diff_patterns.most_common(30):
                print(f"    {diff}: {count}", flush=True)
        else:
            print(f"    Most common:", flush=True)
            for diff, count in diff_patterns.most_common(10):
                print(f"      {diff}: {count}", flush=True)

        # 5. Key test: is sum(c[j]) monotone? sum(j*c[j])? sum(j²*c[j])?
        print(f"\n  Monotonicity tests on jdz edges:", flush=True)
        tests = {
            'Σc[j]': lambda c: sum(c),
            'Σj·c[j]': lambda c: sum(j*c[j] for j in range(n)),
            'Σj²·c[j]': lambda c: sum(j*j*c[j] for j in range(n)),
            'Σ(n-j)·c[j]': lambda c: sum((n-j)*c[j] for j in range(n)),
            '#zeros': lambda c: sum(1 for x in c if x == 0),
            '#twos': lambda c: sum(1 for x in c if x == 2),
            'Σ(c[j]==2)·j': lambda c: sum(j for j in range(n) if c[j] == 2),
            'Σ(c[j]==0)·j': lambda c: sum(j for j in range(n) if c[j] == 0),
            'max_pos_of_2': lambda c: max((j for j in range(n) if c[j] == 2), default=-1),
            'min_pos_of_2': lambda c: min((j for j in range(n) if c[j] == 2), default=n),
        }

        for tname, tfunc in tests.items():
            viol_dec = sum(1 for u, v in jdz_unique if tfunc(v) >= tfunc(u))
            viol_inc = sum(1 for u, v in jdz_unique if tfunc(v) <= tfunc(u))
            best_dir = 'dec' if viol_dec <= viol_inc else 'inc'
            best_viol = min(viol_dec, viol_inc)
            pct = 100 * best_viol / len(jdz_unique)
            marker = " ***" if best_viol == 0 else ""
            print(f"    {tname:20s}: {best_dir} {best_viol:>6}/{len(jdz_unique)} ({pct:.1f}%){marker}", flush=True)

        # 6. COMPOSITE test: lexicographic on (boundary, interior_measure)
        print(f"\n  Composite (boundary_type, measure):", flush=True)
        for mname, mfunc in [('Σj·c[j]', lambda c: sum(j*c[j] for j in range(n))),
                              ('Σj²·c[j]', lambda c: sum(j*j*c[j] for j in range(n))),
                              ('Σc[j]', lambda c: sum(c))]:
            # Lex order: (c[0], c[n-1], measure) decreasing
            viol = 0
            for u, v in jdz_unique:
                key_u = (u[0], u[n-1], mfunc(u))
                key_v = (v[0], v[n-1], mfunc(v))
                if key_v >= key_u: viol += 1
            pct = 100 * viol / len(jdz_unique)
            marker = " ***" if viol == 0 else ""
            print(f"    (c[0],c[n-1],{mname}) dec: {viol}/{len(jdz_unique)} ({pct:.1f}%){marker}", flush=True)

if __name__ == '__main__':
    main()
