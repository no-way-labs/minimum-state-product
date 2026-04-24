#!/usr/bin/env python3
"""
CONVERGENCE PROOF 68: Hunt for additional jdz-preserved quantities
==================================================================
int(2,1) and int_j(2,0) are preserved on jdz edges by DEFINITION.
What OTHER quantities are preserved? If we find more, the decomposition
gets finer → smaller components → easier to prove DAG.

Also: verify that Δfc ≤ +2 universally on jdz edges.
Also: test whether fc-based measures work WITHIN (int21,intj20) components.
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter

def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

def build_excursion_graph(n_val):
    ms, fs = build_system(n_val)
    result = verify_system(ms, fs)
    assert result['valid']
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)
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
                    if out != L and out != R: anom_edges.append((c, succ, i, dfc))
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
    return list(exc_edges), ms

def int_21(c, n):
    return sum(1 for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 1)
def int_j_20(c, n):
    return sum(j for j in range(2, n-2) if c[j] == 2 and c[(j+1)%n] == 0)

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz = list(set((u,v) for u,v in exc_edges
                   if int_21(v,n)-int_21(u,n)==0
                   and int_j_20(v,n)-int_j_20(u,n)==0))

        if not jdz:
            print(f"n={n}: no jdz edges"); continue

        print(f"\n{'='*70}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges ({time.time()-t0:.1f}s)", flush=True)
        print(f"{'='*70}", flush=True)

        # === 1. Verify Δfc bound ===
        max_dfc = max(sum(1 for j in range(n) if v[j]!=v[(j+1)%n]) -
                      sum(1 for j in range(n) if u[j]!=u[(j+1)%n]) for u,v in jdz)
        min_dfc = min(sum(1 for j in range(n) if v[j]!=v[(j+1)%n]) -
                      sum(1 for j in range(n) if u[j]!=u[(j+1)%n]) for u,v in jdz)
        print(f"  Δfc range: [{min_dfc}, {max_dfc}]", flush=True)

        # === 2. Test ALL pair-count quantities for PRESERVATION (Δ=0) ===
        print(f"\n  Pair-count preservation test (Δ=0 on ALL jdz edges):", flush=True)
        for a in range(3):
            for b in range(3):
                # Full ring
                preserved = all(
                    sum(1 for j in range(n) if v[j]==a and v[(j+1)%n]==b) ==
                    sum(1 for j in range(n) if u[j]==a and u[(j+1)%n]==b)
                    for u,v in jdz)
                if preserved:
                    print(f"    pair({a},{b}) FULL: PRESERVED", flush=True)

                # Interior only
                preserved_int = all(
                    sum(1 for j in range(2, n-2) if v[j]==a and v[(j+1)%n]==b) ==
                    sum(1 for j in range(2, n-2) if u[j]==a and u[(j+1)%n]==b)
                    for u,v in jdz)
                if preserved_int:
                    print(f"    pair({a},{b}) INT:  PRESERVED", flush=True)

        # === 3. Test position-weighted pair counts for preservation ===
        print(f"\n  Position-weighted preservation:", flush=True)
        for a in range(3):
            for b in range(3):
                # j-weighted interior
                preserved = all(
                    sum(j for j in range(2, n-2) if v[j]==a and v[(j+1)%n]==b) ==
                    sum(j for j in range(2, n-2) if u[j]==a and u[(j+1)%n]==b)
                    for u,v in jdz)
                if preserved:
                    print(f"    j·pair({a},{b}) INT: PRESERVED", flush=True)

                # j²-weighted interior
                preserved2 = all(
                    sum(j*j for j in range(2, n-2) if v[j]==a and v[(j+1)%n]==b) ==
                    sum(j*j for j in range(2, n-2) if u[j]==a and u[(j+1)%n]==b)
                    for u,v in jdz)
                if preserved2:
                    print(f"    j²·pair({a},{b}) INT: PRESERVED", flush=True)

        # === 4. Value-count preservation ===
        print(f"\n  Value-count preservation:", flush=True)
        for val in range(3):
            preserved = all(sum(1 for x in v if x==val) == sum(1 for x in u if x==val) for u,v in jdz)
            if preserved:
                print(f"    #(={val}): PRESERVED", flush=True)
            # Interior only
            preserved_int = all(
                sum(1 for j in range(2, n-2) if v[j]==val) ==
                sum(1 for j in range(2, n-2) if u[j]==val)
                for u,v in jdz)
            if preserved_int:
                print(f"    int_#(={val}): PRESERVED", flush=True)
            # j-weighted
            preserved_j = all(
                sum(j for j in range(n) if v[j]==val) == sum(j for j in range(n) if u[j]==val)
                for u,v in jdz)
            if preserved_j:
                print(f"    Σj·[={val}]: PRESERVED", flush=True)

        # === 5. Boundary-related preservation ===
        print(f"\n  Boundary preservation:", flush=True)
        bdry_preserved = all(
            (u[0], u[1], u[n-2], u[n-1]) == (v[0], v[1], v[n-2], v[n-1])
            for u,v in jdz)
        print(f"    (c[0],c[1],c[n-2],c[n-1]): {'PRESERVED' if bdry_preserved else 'NOT preserved'}", flush=True)

        # Each boundary position
        for pos in [0, 1, n-2, n-1]:
            pres = all(u[pos] == v[pos] for u,v in jdz)
            if pres:
                print(f"    c[{pos}]: PRESERVED", flush=True)

        # Boundary sum
        bsum_pres = all(u[0]+u[n-1] == v[0]+v[n-1] for u,v in jdz)
        if bsum_pres:
            print(f"    c[0]+c[n-1]: PRESERVED", flush=True)

        # === 6. "Near-preserved" quantities (|Δ| ≤ 1) ===
        print(f"\n  Near-preserved (|Δ| ≤ 1):", flush=True)
        for a in range(3):
            for b in range(3):
                deltas = [sum(1 for j in range(n) if v[j]==a and v[(j+1)%n]==b) -
                          sum(1 for j in range(n) if u[j]==a and u[(j+1)%n]==b)
                          for u,v in jdz]
                if all(abs(d) <= 1 for d in deltas):
                    n_zero = sum(1 for d in deltas if d == 0)
                    print(f"    pair({a},{b}): |Δ|≤1, {n_zero}/{len(jdz)} exact ({100*n_zero/len(jdz):.0f}%)", flush=True)

        # === 7. Linear combinations that are preserved ===
        # Try: α·pair(a1,b1) + β·pair(a2,b2) = const
        # Since (2,1) and j·(2,0) are preserved, try combining others
        print(f"\n  Combined preservation (pair(a,b)+pair(c,d)=const):", flush=True)
        for a1 in range(3):
            for b1 in range(3):
                for a2 in range(a1, 3):
                    for b2 in range(b1 if a2==a1 else 0, 3):
                        if (a1,b1) == (a2,b2): continue
                        for sign in [1, -1]:
                            preserved = all(
                                (sum(1 for j in range(n) if v[j]==a1 and v[(j+1)%n]==b1) +
                                 sign * sum(1 for j in range(n) if v[j]==a2 and v[(j+1)%n]==b2)) ==
                                (sum(1 for j in range(n) if u[j]==a1 and u[(j+1)%n]==b1) +
                                 sign * sum(1 for j in range(n) if u[j]==a2 and u[(j+1)%n]==b2))
                                for u,v in jdz)
                            if preserved:
                                s = '+' if sign > 0 else '-'
                                print(f"    pair({a1},{b1}){s}pair({a2},{b2}): PRESERVED", flush=True)

        # === 8. Within (int21=1,intj20=0): test fc-related measures ===
        # This is the dominant component
        comp_edges = [(u,v) for u,v in jdz
                      if int_21(u,n)==1 and int_j_20(u,n)==0]
        if comp_edges:
            print(f"\n  Within (int21=1,intj20=0) [{len(comp_edges)} edges]:", flush=True)

            # fc strict decrease
            fc_strict = sum(1 for u,v in comp_edges
                           if sum(1 for j in range(n) if v[j]!=v[(j+1)%n]) <
                              sum(1 for j in range(n) if u[j]!=u[(j+1)%n]))
            print(f"    fc strictly decreasing: {fc_strict}/{len(comp_edges)}", flush=True)

            # fc + sum(c[j])
            for alpha in [1, 2, 3, -1, -2, -3]:
                measure = lambda c, a=alpha: sum(1 for j in range(n) if c[j]!=c[(j+1)%n]) + a * sum(c)
                viol = sum(1 for u,v in comp_edges if measure(v) >= measure(u))
                if viol < len(comp_edges) * 0.1:
                    print(f"    fc+{alpha}·Σc: {viol}/{len(comp_edges)} violations", flush=True)

            # Number of value 2 in interior
            for alpha in range(-3, 4):
                if alpha == 0: continue
                measure = lambda c, a=alpha: sum(1 for j in range(n) if c[j]!=c[(j+1)%n]) + a * sum(1 for j in range(2,n-2) if c[j]==2)
                viol = sum(1 for u,v in comp_edges if measure(v) >= measure(u))
                if viol < len(comp_edges) * 0.05:
                    print(f"    fc+{alpha}·#int2: {viol}/{len(comp_edges)} violations ({100*viol/len(comp_edges):.1f}%)", flush=True)

        elapsed = time.time() - t0
        print(f"\n  Time: {elapsed:.1f}s", flush=True)

if __name__ == '__main__':
    main()
