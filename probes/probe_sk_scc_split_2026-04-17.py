#!/usr/bin/env python3
"""Do SCCs of SK respect the p*-flip split?

At n=7 the SCC analysis found SK always decomposes into EXACTLY 2 SCCs.
Hypothesis: those 2 SCCs are precisely SK_0 and SK_1 — i.e., forced
moves within SK never cross the p* coordinate.

Measurements:
  (1) Count forced-move edges in SK that cross p*
      (edges where a config with c[p*]=v0 moves to one with c[p*]=v1).
  (2) Do SCCs of SK always have constant p* value? (inside-one-half)
  (3) If YES, and both halves have ≥1 SCC, each half ≥ 2^(n-2) follows
      from some per-half lower bound.
"""
from itertools import product as iproduct
from collections import Counter, defaultdict
import time
import sys


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product: out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product: break
            prefix.append(m); rec(i + 1, prefix, new_prod); prefix.pop()
    rec(0, [], 1)
    return out


def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen_cycles = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]; ki = (i,Li,Si,Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def compute_sk(vcng_set, move_entries, n):
    current = set(vcng_set)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                if ctx in move_entries:
                    nc = list(c); nc[p] = move_entries[ctx]; nc = tuple(nc)
                    if nc in current: has_forced = True; break
            if not has_forced: victims.add(c)
        if not victims: break
        current -= victims
    return current


def build_adj(nodes, move_entries, n):
    adj = defaultdict(list)
    for c in nodes:
        for p in range(n):
            ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if ctx in move_entries:
                nc = list(c); nc[p] = move_entries[ctx]; nc = tuple(nc)
                if nc in nodes:
                    adj[c].append((p, nc))
    return adj


def tarjan_sccs_iter(nodes, adj):
    idx = [0]; stack = []; on_stack = {}; indices = {}; lowlink = {}; sccs = []
    for v0 in nodes:
        if v0 in indices: continue
        work = [(v0, iter(adj.get(v0, [])))]
        indices[v0] = idx[0]; lowlink[v0] = idx[0]; idx[0] += 1
        stack.append(v0); on_stack[v0] = True
        while work:
            node, it = work[-1]
            nxt = None
            for pp, w in it:
                if w not in indices:
                    nxt = w
                    break
                elif on_stack.get(w, False):
                    lowlink[node] = min(lowlink[node], indices[w])
            if nxt is not None:
                indices[nxt] = idx[0]; lowlink[nxt] = idx[0]; idx[0] += 1
                stack.append(nxt); on_stack[nxt] = True
                work.append((nxt, iter(adj.get(nxt, []))))
            else:
                if lowlink[node] == indices[node]:
                    scc = []
                    while True:
                        w = stack.pop(); on_stack[w] = False; scc.append(w)
                        if w == node: break
                    sccs.append(scc)
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])
    return sccs


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    return V


def measure(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    fc = Counter(movers)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    if not SK: return None

    fc2_bin = [p for p in range(n) if fc[p] == 2 and len(V[p]) == 2]
    if not fc2_bin: return None

    out = []
    for p_star in fc2_bin:
        v0, v1 = sorted(V[p_star])
        adj = build_adj(SK, move_entries, n)
        # Count edges crossing p*
        cross_edges = 0
        total_edges = 0
        for c, succs in adj.items():
            for pp, nc in succs:
                total_edges += 1
                if c[p_star] != nc[p_star]:
                    cross_edges += 1
        # Adj ignoring p_star-flip edges (to check if SK is disconnected when p* edges removed)
        adj_nonflip = defaultdict(list)
        for c in SK:
            for pp, nc in adj[c]:
                if pp != p_star:
                    adj_nonflip[c].append((pp, nc))
        sccs_full = tarjan_sccs_iter(list(SK), adj)
        sccs_nonflip = tarjan_sccs_iter(list(SK), adj_nonflip)
        # Does every SCC in full graph have constant c[p*]?
        sccs_homogeneous = 0
        sccs_mixed = 0
        for scc in sccs_full:
            vals = {c[p_star] for c in scc}
            if len(vals) == 1: sccs_homogeneous += 1
            else: sccs_mixed += 1
        # SCC sizes
        scc_sizes = sorted([len(s) for s in sccs_full], reverse=True)
        out.append({
            'p_star': p_star,
            'SK_0': sum(1 for c in SK if c[p_star] == v0),
            'SK_1': sum(1 for c in SK if c[p_star] == v1),
            'n_sccs_full': len(sccs_full),
            'n_sccs_homogeneous': sccs_homogeneous,
            'n_sccs_mixed': sccs_mixed,
            'n_sccs_nonflip': len(sccs_nonflip),
            'cross_p_edges': cross_edges,
            'total_edges': total_edges,
            'scc_sizes': scc_sizes[:4],
        })
    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'per_p': out,
    }


def main():
    sys.setrecursionlimit(50000)
    plan = [
        (5, 1, 8, 2.0, 16),
        (6, 5, 5, 3.0, 17),
        (7, 30, 3, 5.0, 18),
        (8, 300, 2, 10.0, 22),
    ]
    by_n = {}
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets ===", flush=True)
        recs = []
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                if len(movers) < 2*n+2: continue
                r = measure(ms, n, cycle, movers, det)
                if r is None: continue
                recs.append(r)
            if (idx+1) % max(1, len(multisets)//5) == 0:
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s recs={len(recs)}", flush=True)
        by_n[n] = recs

    print(f"\n{'='*78}\nSCC p*-split results\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        print(f"\n  n={n}  records={total}")
        pairs = [(r, p) for r in recs for p in r['per_p']]
        # Cross-p* edge counts
        cross = [p['cross_p_edges'] for _, p in pairs]
        tot_e = [p['total_edges'] for _, p in pairs]
        no_cross = sum(1 for c in cross if c == 0)
        print(f"  pairs (rec, p*): {len(pairs)}")
        print(f"  cross-p*-edges in SK forced graph  min/avg/max: {min(cross)}/{sum(cross)/len(pairs):.2f}/{max(cross)}")
        print(f"  records with ZERO cross-p* edges:  {no_cross}/{len(pairs)} ({100*no_cross/len(pairs):.1f}%)")
        # Homogeneous SCCs
        hom = sum(p['n_sccs_homogeneous'] for _, p in pairs)
        mix = sum(p['n_sccs_mixed'] for _, p in pairs)
        all_hom = sum(1 for _, p in pairs if p['n_sccs_mixed'] == 0)
        print(f"  SCCs homogeneous vs mixed: {hom} / {mix}")
        print(f"  records with ALL-homogeneous SCCs: {all_hom}/{len(pairs)} ({100*all_hom/len(pairs):.1f}%)")
        # SCC count distribution
        n_sccs_full = [p['n_sccs_full'] for _, p in pairs]
        n_sccs_nonflip = [p['n_sccs_nonflip'] for _, p in pairs]
        print(f"  #SCCs full graph  min/avg/max: {min(n_sccs_full)}/{sum(n_sccs_full)/len(pairs):.2f}/{max(n_sccs_full)}")
        print(f"  #SCCs non-p* graph min/avg/max: {min(n_sccs_nonflip)}/{sum(n_sccs_nonflip)/len(pairs):.2f}/{max(n_sccs_nonflip)}")


if __name__ == "__main__":
    main()
