#!/usr/bin/env python3
"""Combined probe: (a) n=8 |SK| vs 2^(n-1), (b) directed-SCC cycle rank,
(c) axis-aligned slab decomposition of SK.

For each record:
  (a) |SK| ≥ 2^(n-1)?   extend to n=8 where peel(N_1(C)) route broke
  (b) directed cycle rank = sum over non-trivial SCCs of (E_scc - V_scc + 1).
      If this equals or tracks 2^(n-1) tighter than undirected b_1, it's
      a more faithful invariant.
  (c) For each position q and each value v, let Slab(q, v) = {c ∈ SK : c[q] = v}.
      - is any slab ≥ 2^(n-2)?
      - is the max-slab union ≥ 2^(n-1)?
      - is SK = union over q of (c[q] != v_cycle)?
      - balanced: are |Slab(q,v)| uniform across v for fixed q?
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product:
                out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced_out is not None and forced_out != new_val:
                    continue
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def compute_sk(vcng_set, move_entries, n):
    current = set(vcng_set)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if ctx in move_entries:
                    v = move_entries[ctx]
                    nc = list(c); nc[p] = v; nc = tuple(nc)
                    if nc in current:
                        has_forced = True
                        break
            if not has_forced:
                victims.add(c)
        if not victims:
            break
        current -= victims
    return current


def forced_edges(config_set, move_entries, n):
    """Directed edges: c → c' where c' is forced neighbor of c and c' ∈ set."""
    edges = []
    for c in config_set:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                v = move_entries[ctx]
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if tuple(nc) in config_set:
                    edges.append((c, tuple(nc)))
    return edges


def tarjan_scc(nodes, adj):
    index = {}
    low = {}
    stack = []
    on_stack = set()
    counter = [0]
    sccs = []
    def strong(v):
        index[v] = counter[0]; low[v] = counter[0]; counter[0] += 1
        stack.append(v); on_stack.add(v)
        for w in adj.get(v, []):
            if w not in index:
                strong(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop(); on_stack.discard(w)
                comp.append(w)
                if w == v: break
            sccs.append(comp)
    import sys
    sys.setrecursionlimit(100000)
    for v in nodes:
        if v not in index:
            strong(v)
    return sccs


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)

    # (b) directed cycle rank on SK
    sk_edges = forced_edges(SK, move_entries, n)
    adj = defaultdict(list)
    for u, v in sk_edges:
        adj[u].append(v)
    sccs = tarjan_scc(SK, adj)
    nontriv = [c for c in sccs if len(c) >= 2 or (len(c) == 1 and c[0] in adj.get(c[0], []))]
    # directed cycle rank per SCC = E_scc - V_scc + 1
    dir_rank = 0
    for comp in nontriv:
        comp_set = set(comp)
        V_scc = len(comp)
        E_scc = sum(1 for u in comp for v in adj.get(u, []) if v in comp_set)
        dir_rank += max(0, E_scc - V_scc + 1)

    # (c) slab decomposition: for each q, v count |{c ∈ SK : c[q] = v}|
    slab_counts = {}
    for q in range(n):
        for v in V[q]:
            slab_counts[(q, v)] = sum(1 for c in SK if c[q] == v)
    max_slab = max(slab_counts.values()) if slab_counts else 0
    # Union over q of Slab(q, non-cycle-value). For each q, slab(q,v) for v ∉ C_values_at_q.
    # But V_q IS C_values_at_q (they come from cycle). So this is empty.
    # Try: for each q, sum over v of slab(q,v) that covers SK.
    # Alternative: covering by "q-hyperplanes" — for each q, the min_v count_complement.
    # For each q: |SK| - max_v |Slab(q,v)| is the size of "cross-q" slab union.
    per_q_complement = []
    for q in range(n):
        vals = sorted(V[q])
        counts = [slab_counts[(q, v)] for v in vals]
        per_q_complement.append(len(SK) - max(counts))
    max_cross_q = max(per_q_complement) if per_q_complement else 0

    # (c-extra): SK = union of the slab-pairs where c[q] ≠ "dominant" value?
    # Check if |SK| ≤ sum_q max_slab(q) or if |SK| ≥ n · 2^(n-2) / something
    # Balanced check: for each q, is Slab(q,v) uniform in v?
    balanced_per_q = []
    for q in range(n):
        vals = sorted(V[q])
        counts = [slab_counts[(q, v)] for v in vals]
        balanced_per_q.append(len(set(counts)) == 1)

    return {
        'n': n, 'ms': ms, 'L': L,
        'SK_size': len(SK),
        'bound_2nm1': 2 ** (n - 1),
        'SK_ge_2nm1': len(SK) >= 2 ** (n - 1),
        # (b)
        'dir_cycle_rank': dir_rank,
        'dir_rank_ge_2nm1': dir_rank >= 2 ** (n - 1),
        'num_nontriv_sccs': len(nontriv),
        # (c)
        'max_slab': max_slab,
        'max_slab_ge_2nm2': max_slab >= 2 ** (n - 2),
        'max_cross_q': max_cross_q,
        'max_cross_q_ge_2nm1': max_cross_q >= 2 ** (n - 1),
        'all_balanced_q': all(balanced_per_q),
        'slab_distribution': sorted(slab_counts.values(), reverse=True)[:6],
    }


def main():
    print("=" * 72)
    print("Combined (a)+(b)+(c): n=8 SK, directed rank, slab decomposition")
    print("=" * 72)
    plan = [
        (5, 2, 80, 3.0, 16),
        (6, 5, 25, 3.0, 17),
        (7, 30, 12, 4.0, 17),
        (8, 300, 5, 15.0, 20),
    ]
    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets  L_max={L_max} ===", flush=True)
        t0 = time.time()
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:
                    continue
                r = analyze(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        bound = 2 ** (n - 1)
        bound2 = 2 ** (n - 2)
        a = sum(1 for r in recs if r['SK_ge_2nm1'])
        b = sum(1 for r in recs if r['dir_rank_ge_2nm1'])
        c_slab = sum(1 for r in recs if r['max_slab_ge_2nm2'])
        c_cross = sum(1 for r in recs if r['max_cross_q_ge_2nm1'])
        c_bal = sum(1 for r in recs if r['all_balanced_q'])
        sk_min = min(r['SK_size'] for r in recs)
        sk_avg = sum(r['SK_size'] for r in recs) / len(recs)
        dr_min = min(r['dir_cycle_rank'] for r in recs)
        dr_avg = sum(r['dir_cycle_rank'] for r in recs) / len(recs)
        ms_min = min(r['max_slab'] for r in recs)
        ms_avg = sum(r['max_slab'] for r in recs) / len(recs)

        print(f"\n  n={n}  records={len(recs)}  bound 2^(n-1)={bound}  2^(n-2)={bound2}")
        print(f"    (a) |SK| ≥ 2^(n-1):             {a}/{len(recs)} ({100*a/len(recs):.1f}%)  min={sk_min} avg={sk_avg:.1f}")
        print(f"    (b) dir cycle rank ≥ 2^(n-1):   {b}/{len(recs)} ({100*b/len(recs):.1f}%)  min={dr_min} avg={dr_avg:.1f}")
        print(f"    (c) max slab ≥ 2^(n-2):         {c_slab}/{len(recs)} ({100*c_slab/len(recs):.1f}%)  min={ms_min} avg={ms_avg:.1f}")
        print(f"    (c) max cross-q ≥ 2^(n-1):      {c_cross}/{len(recs)} ({100*c_cross/len(recs):.1f}%)")
        print(f"    (c) all q balanced:              {c_bal}/{len(recs)} ({100*c_bal/len(recs):.1f}%)")
        # Show a few sample slab distributions
        print(f"    sample slab_distributions: {[r['slab_distribution'] for r in recs[:3]]}")


if __name__ == "__main__":
    main()
