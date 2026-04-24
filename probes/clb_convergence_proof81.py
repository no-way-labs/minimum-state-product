#!/usr/bin/env python3
"""
CONVERGENCE PROOF 81: Verify key monotonicity discoveries
==========================================================
1. Δ(intj20 + intj21) ≤ 0 on ALL excursion edges (KEY DISCOVERY)
2. Check FULL-ring int(2,1) (including boundary pairs) on excursion edges
3. Check FULL-ring versions of all invariants
4. Try to extend the combined monotonicity to stronger claims
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter

def delta_fc_val(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])

# Interior-only versions (positions 2..n-3)
def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def int_j_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def int_j_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

# FULL-ring versions (all positions)
def full_21(c, n):
    return sum(1 for j in range(n) if c[j] == 2 and c[(j + 1) % n] == 1)

def full_20(c, n):
    return sum(1 for j in range(n) if c[j] == 2 and c[(j + 1) % n] == 0)

def full_j_20(c, n):
    return sum(j for j in range(n) if c[j] == 2 and c[(j + 1) % n] == 0)

def full_j_21(c, n):
    return sum(j for j in range(n) if c[j] == 2 and c[(j + 1) % n] == 1)

# Combined quantity: position-weighted exposed 2's
def exposed_2_weight(c, n):
    """Sum of j where c[j]=2 and c[j+1] != 2. Interior only."""
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] != 2)

def full_exposed_2_weight(c, n):
    """Sum of j where c[j]=2 and c[j+1] != 2. Full ring."""
    return sum(j for j in range(n) if c[j] == 2 and c[(j + 1) % n] != 2)

def count_exposed_2(c, n):
    """Count of positions where c[j]=2 and c[j+1] != 2. Interior only."""
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] != 2)

def full_count_exposed_2(c, n):
    """Count of positions where c[j]=2 and c[j+1] != 2. Full ring."""
    return sum(1 for j in range(n) if c[j] == 2 and c[(j + 1) % n] != 2)

# Sum of positions of ALL 2's (not just exposed)
def sum_pos_2(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2)

def full_sum_pos_2(c, n):
    return sum(j for j in range(n) if c[j] == 2)


def build_exc_edges(n_val):
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
    n = n_val
    anom_edges = []
    dfc_le0_adj = defaultdict(list)
    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc_val(L, S, R, out)
                    if dfc <= 0:
                        dfc_le0_adj[c].append(succ)
                    if out != L and out != R:
                        anom_edges.append((c, succ, i, dfc))
    anom_sources = set(c for c, _, _, _ in anom_edges)
    anom_target_map = defaultdict(list)
    for c, succ, i, dfc in anom_edges:
        anom_target_map[succ].append(c)
    exc_edges = set()
    for b in set(s for _, s, _, _ in anom_edges):
        visited = {b}; queue = [b]; head = 0
        while head < len(queue):
            node = queue[head]; head += 1
            if node in anom_sources:
                for src in anom_target_map.get(b, []):
                    exc_edges.add((src, node))
            for nxt in dfc_le0_adj.get(node, []):
                if nxt not in visited:
                    visited.add(nxt); queue.append(nxt)
    return list(exc_edges)


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 13):
        t0 = time.time()
        exc = build_exc_edges(n_val)
        n = n_val
        if not exc:
            print(f"n={n}: no excursion edges")
            continue

        print(f"\n{'='*70}", flush=True)
        print(f"n={n}: {len(exc)} excursion edges ({time.time()-t0:.1f}s)", flush=True)

        # Define all quantities to test
        quantities = {
            # Interior-only
            'int_21': lambda c: int_21(c, n),
            'int_20': lambda c: int_20(c, n),
            'intj_20': lambda c: int_j_20(c, n),
            'intj_21': lambda c: int_j_21(c, n),
            'intj20+intj21': lambda c: int_j_20(c, n) + int_j_21(c, n),
            'int20+int21': lambda c: int_20(c, n) + int_21(c, n),
            'exposed2_wt': lambda c: exposed_2_weight(c, n),
            'count_exp2': lambda c: count_exposed_2(c, n),
            'sum_pos_2': lambda c: sum_pos_2(c, n),
            # Full-ring
            'FULL_21': lambda c: full_21(c, n),
            'FULL_20': lambda c: full_20(c, n),
            'FULL_j20': lambda c: full_j_20(c, n),
            'FULL_j21': lambda c: full_j_21(c, n),
            'FULL_j20+j21': lambda c: full_j_20(c, n) + full_j_21(c, n),
            'FULL_20+21': lambda c: full_20(c, n) + full_21(c, n),
            'FULL_exp2_wt': lambda c: full_exposed_2_weight(c, n),
            'FULL_cnt_exp2': lambda c: full_count_exposed_2(c, n),
            'FULL_sum_pos2': lambda c: full_sum_pos_2(c, n),
        }

        # Test each: is Δ≥0, ≤0, or neither?
        print(f"\n  Monotonicity on ALL excursion edges:", flush=True)
        for qname, qfunc in quantities.items():
            neg = 0; zer = 0; pos = 0
            for u, v in exc:
                d = qfunc(v) - qfunc(u)
                if d < 0: neg += 1
                elif d > 0: pos += 1
                else: zer += 1

            if neg == 0 and pos == 0:
                marker = " *** CONSTANT"
            elif neg == 0:
                marker = " *** ALWAYS ≥ 0"
            elif pos == 0:
                marker = " *** ALWAYS ≤ 0"
            else:
                marker = ""
            total = len(exc)
            print(f"    Δ{qname:20s}: neg={neg:>7d} zero={zer:>7d} pos={pos:>7d}{marker}", flush=True)

        # === Test combined quantities for potential ===
        # Lexicographic: (-FULL_21, intj20+intj21)
        # Since FULL_21 always ≥ 0 and intj20+intj21 always ≤ 0,
        # the lex order (-FULL_21, intj20+intj21) decreases when either
        # FULL_21 increases (strictly) or both preserved and intj20+intj21 decreases.
        # Remaining: both preserved.
        if n_val <= 12:
            both_preserved = 0
            for u, v in exc:
                d1 = full_21(v, n) - full_21(u, n)
                d2 = (int_j_20(v,n) + int_j_21(v,n)) - (int_j_20(u,n) + int_j_21(u,n))
                if d1 == 0 and d2 == 0:
                    both_preserved += 1
            print(f"\n  Both FULL_21 and intj20+intj21 preserved: "
                  f"{both_preserved}/{len(exc)} ({100*both_preserved/len(exc):.1f}%)", flush=True)

            # === What are the "double-zero" edges (both preserved)? ===
            # Check if this equals the jdz edges
            dz = [(u,v) for u,v in exc
                  if full_21(v,n)==full_21(u,n) and
                     int_j_20(v,n)+int_j_21(v,n)==int_j_20(u,n)+int_j_21(u,n)]
            jdz = [(u,v) for u,v in exc
                   if int_21(v,n)==int_21(u,n) and int_j_20(v,n)==int_j_20(u,n)]
            print(f"  Double-zero (FULL_21 + intj_combined): {len(dz)} edges", flush=True)
            print(f"  Original jdz (interior int_21 + intj_20): {len(jdz)} edges", flush=True)

            # Try FULL_21 ≥ 0 as the correct Layer 0
            full21_neg = sum(1 for u,v in exc if full_21(v,n) < full_21(u,n))
            full21_zer = sum(1 for u,v in exc if full_21(v,n) == full_21(u,n))
            full21_pos = sum(1 for u,v in exc if full_21(v,n) > full_21(u,n))
            print(f"\n  ΔFULL_21 on exc edges: neg={full21_neg} zero={full21_zer} pos={full21_pos}",
                  flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
