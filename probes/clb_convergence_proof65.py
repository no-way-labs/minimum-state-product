#!/usr/bin/env python3
"""
CONVERGENCE PROOF 65: Layer 4 search + 2-cycle check + cycle structure
======================================================================
1. Test ALL pair-count quantities for monotonicity on jdz edges
2. Test position-weighted pair counts: Σ j^k · [c[j]=a, c[j+1]=b]
3. Check for 2-cycles in the excursion/jdz subgraph
4. Compute DAG ranks of jdz subgraph
"""
import sys, os, time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter, deque

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

def pair_count(c, n, a, b, lo=0, hi=None):
    """Count pairs (c[j],c[j+1])=(a,b) for lo <= j < hi."""
    if hi is None: hi = n
    return sum(1 for j in range(lo, hi) if c[j] == a and c[(j+1)%n] == b)

def wpair_count(c, n, a, b, weight_pow=1, lo=0, hi=None):
    """Position-weighted pair count: Σ j^weight_pow · [c[j]=a,c[j+1]=b]."""
    if hi is None: hi = n
    return sum(j**weight_pow for j in range(lo, hi) if c[j] == a and c[(j+1)%n] == b)

def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 12):
        t0 = time.time()
        exc_edges, ms = build_excursion_graph(n_val)
        n = n_val

        jdz = list(set((u,v) for u,v in exc_edges
                   if int_21(v,n)-int_21(u,n)==0
                   and int_j_20(v,n)-int_j_20(u,n)==0))

        print(f"\n{'='*70}", flush=True)
        print(f"n={n}: {len(jdz)} jdz edges ({time.time()-t0:.1f}s)", flush=True)
        print(f"{'='*70}", flush=True)

        if not jdz: continue

        # === 1. ALL pair-count monotonicity on jdz edges ===
        print(f"\n  Pair-count monotonicity (full ring):", flush=True)
        for a in range(3):
            for b in range(3):
                deltas = [pair_count(v,n,a,b) - pair_count(u,n,a,b) for u,v in jdz]
                n_neg = sum(1 for d in deltas if d < 0)
                n_zero = sum(1 for d in deltas if d == 0)
                n_pos = sum(1 for d in deltas if d > 0)
                if n_neg == 0 or n_pos == 0:
                    marker = " *** MONOTONE" if n_neg == 0 or n_pos == 0 else ""
                    dir_str = "≥0" if n_neg == 0 else "≤0"
                    print(f"    ({a},{b}): {dir_str}  neg={n_neg} zero={n_zero} pos={n_pos}{marker}", flush=True)

        # === 2. Interior pair-count monotonicity ===
        print(f"\n  Interior pair-count monotonicity (pos 2..n-3):", flush=True)
        for a in range(3):
            for b in range(3):
                deltas = [pair_count(v,n,a,b,2,n-2) - pair_count(u,n,a,b,2,n-2) for u,v in jdz]
                n_neg = sum(1 for d in deltas if d < 0)
                n_zero = sum(1 for d in deltas if d == 0)
                n_pos = sum(1 for d in deltas if d > 0)
                if n_neg == 0 or n_pos == 0:
                    dir_str = "≥0" if n_neg == 0 else "≤0"
                    print(f"    ({a},{b}): {dir_str}  neg={n_neg} zero={n_zero} pos={n_pos} *** MONOTONE", flush=True)

        # === 3. Position-weighted pair counts ===
        print(f"\n  Position-weighted pair counts (j^k weighting):", flush=True)
        for k in [1, 2, 3]:
            best_name = None; best_viol = len(jdz)
            for a in range(3):
                for b in range(3):
                    deltas = [wpair_count(v,n,a,b,k) - wpair_count(u,n,a,b,k) for u,v in jdz]
                    n_neg = sum(1 for d in deltas if d < 0)
                    n_pos = sum(1 for d in deltas if d > 0)
                    viol = min(n_neg, n_pos)
                    if viol == 0:
                        dir_str = "≥0" if n_neg == 0 else "≤0"
                        print(f"    j^{k}·({a},{b}): {dir_str} *** MONOTONE", flush=True)
                    if viol < best_viol:
                        best_viol = viol; best_name = f"j^{k}·({a},{b})"
            if best_viol > 0:
                pct = 100*best_viol/len(jdz)
                print(f"    best j^{k}: {best_name} with {best_viol} violations ({pct:.1f}%)", flush=True)

        # === 4. Combined pair counts: Σ_{(a,b)} w(a,b) * pair_count(a,b) ===
        # This is equivalent to: is there a linear combination of pair counts that's monotone?
        # Already tested via LP in earlier scripts. Skip.

        # === 5. Value counts: #(c[j]=v) for v=0,1,2, weighted ===
        print(f"\n  Value count monotonicity:", flush=True)
        for val in range(3):
            # Unweighted
            d = [sum(1 for x in v if x==val) - sum(1 for x in u if x==val) for u,v in jdz]
            n_neg = sum(1 for x in d if x < 0); n_pos = sum(1 for x in d if x > 0)
            if n_neg == 0 or n_pos == 0:
                print(f"    #(={val}): {'≥0' if n_neg==0 else '≤0'} *** MONOTONE", flush=True)

            # j-weighted
            d2 = [sum(j for j in range(n) if v[j]==val) - sum(j for j in range(n) if u[j]==val) for u,v in jdz]
            n_neg2 = sum(1 for x in d2 if x < 0); n_pos2 = sum(1 for x in d2 if x > 0)
            if n_neg2 == 0 or n_pos2 == 0:
                print(f"    Σj·[c[j]={val}]: {'≥0' if n_neg2==0 else '≤0'} *** MONOTONE", flush=True)

            # j²-weighted
            d3 = [sum(j*j for j in range(n) if v[j]==val) - sum(j*j for j in range(n) if u[j]==val) for u,v in jdz]
            n_neg3 = sum(1 for x in d3 if x < 0); n_pos3 = sum(1 for x in d3 if x > 0)
            if n_neg3 == 0 or n_pos3 == 0:
                print(f"    Σj²·[c[j]={val}]: {'≥0' if n_neg3==0 else '≤0'} *** MONOTONE", flush=True)

        # === 6. 2-cycle check ===
        edge_set = set(jdz)
        two_cycles = [(u,v) for u,v in jdz if (v,u) in edge_set]
        print(f"\n  2-cycles in jdz: {len(two_cycles)//2}", flush=True)

        # === 7. DAG rank analysis ===
        adj = defaultdict(list)
        nodes = set()
        for u, v in jdz:
            adj[u].append(v); nodes.add(u); nodes.add(v)

        in_deg = defaultdict(int)
        for u, v in jdz: in_deg[v] += 1

        q = deque([u for u in nodes if in_deg[u] == 0])
        rank = {}
        while q:
            node = q.popleft()
            rank[node] = 0
            for nxt in adj[node]:
                in_deg[nxt] -= 1
                if in_deg[nxt] == 0: q.append(nxt)

        # BFS for rank
        rank2 = {}
        for u in nodes:
            if u not in rank2:
                rank2[u] = max((rank2.get(s, 0) + 1 for s in adj[u]), default=0)

        # Simpler: compute rank via reverse topo
        adj_r = defaultdict(list)
        for u, v in jdz: adj_r[v].append(u)
        in_deg2 = Counter()
        for u, v in jdz: in_deg2[v] += 1
        q = deque([u for u in nodes if in_deg2[u] == 0])
        topo = []
        while q:
            node = q.popleft(); topo.append(node)
            for nxt in adj[node]:
                in_deg2[nxt] -= 1
                if in_deg2[nxt] == 0: q.append(nxt)

        is_dag = len(topo) == len(nodes)
        max_rank = 0
        if is_dag:
            rk = {}
            for c in reversed(topo):
                rk[c] = max((rk[s]+1 for s in adj[c]), default=0)
            max_rank = max(rk.values()) if rk else 0
            rank_dist = Counter(rk.values())
            print(f"  DAG: max_rank={max_rank}, nodes={len(nodes)}", flush=True)
            if max_rank <= 20:
                print(f"  Rank distribution: {dict(sorted(rank_dist.items()))}", flush=True)
        else:
            print(f"  NOT DAG! ({len(topo)}/{len(nodes)} processed)", flush=True)

        # === 8. Layer 4 search: combine pair counts with integer coefficients ===
        # Try small integer combinations of pair-count deltas
        if len(jdz) <= 200000:
            print(f"\n  Layer 4 search (pair-count combinations):", flush=True)
            # Compute all pair-count deltas
            pair_deltas = {}
            for a in range(3):
                for b in range(3):
                    pair_deltas[(a,b)] = [pair_count(v,n,a,b) - pair_count(u,n,a,b) for u,v in jdz]

            # Also position-weighted
            wpair_deltas = {}
            for a in range(3):
                for b in range(3):
                    wpair_deltas[(a,b)] = [wpair_count(v,n,a,b,1) - wpair_count(u,n,a,b,1) for u,v in jdz]

            # Try: linear combination of pair deltas that's ≤ 0 on all jdz edges
            # This is what the LP does, but let me try small integer combos
            found_any = False
            for w21 in range(-3, 4):
                for w20 in range(-3, 4):
                    for w10 in range(-3, 4):
                        for w01 in range(-3, 4):
                            if w21 == 0 and w20 == 0 and w10 == 0 and w01 == 0: continue
                            combo = [w21*pair_deltas[(2,1)][i] + w20*pair_deltas[(2,0)][i]
                                     + w10*pair_deltas[(1,0)][i] + w01*pair_deltas[(0,1)][i]
                                     for i in range(len(jdz))]
                            if all(d <= 0 for d in combo):
                                n_strict = sum(1 for d in combo if d < 0)
                                print(f"    FOUND: {w21}·(2,1)+{w20}·(2,0)+{w10}·(1,0)+{w01}·(0,1) ≤ 0, {n_strict}/{len(jdz)} strict", flush=True)
                                found_any = True

            # Try with position-weighted pairs
            for w21 in range(-3, 4):
                for w20 in range(-3, 4):
                    if w21 == 0 and w20 == 0: continue
                    combo = [w21*wpair_deltas[(2,1)][i] + w20*wpair_deltas[(2,0)][i]
                             for i in range(len(jdz))]
                    if all(d <= 0 for d in combo):
                        n_strict = sum(1 for d in combo if d < 0)
                        print(f"    FOUND weighted: {w21}·j(2,1)+{w20}·j(2,0) ≤ 0, {n_strict}/{len(jdz)} strict", flush=True)
                        found_any = True

            if not found_any:
                print(f"    No small-integer pair-count combination found", flush=True)

if __name__ == '__main__':
    main()
