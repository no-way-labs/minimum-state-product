#!/usr/bin/env python3
"""CW / homological probe of the forced graph on VC-NG.

Structure:
  0-cells: configs in VC (or VC-NG)
  1-cells: forced moves (directed or undirected)
  2-cells: commuting squares — for positions p,q non-adjacent (|p-q| mod n ≥ 2),
           if c has forced moves at both p and q, then the square
             c → c[p:=vp] → c[p:=vp, q:=vq]
             c → c[q:=vq] → c[p:=vp, q:=vq]
           is a 2-cell.

Hypotheses:
  H_b1_undirected: b_1(undirected forced graph on VC-NG) ≥ 2^(n-1)
  H_b1_with2cells: b_1 with commuting 2-cells filled ≥ 2^(n-1)
  H_scc_count:     # non-trivial SCCs (directed) — does it structure 2^(n-1)?
  H_scc_size:      |SK| matches total size of non-trivial SCCs ∪ their basin
  H_euler:         Euler characteristic of (V, E, F) complex
"""
from itertools import product as iproduct, combinations
from collections import defaultdict, Counter
import time
import sys
sys.setrecursionlimit(20000)


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


def tarjan_scc(vertices, adj):
    """Tarjan's SCC. vertices: iterable. adj: dict node→list[node]."""
    idx = {}
    low = {}
    on_stack = set()
    stack = []
    sccs = []
    counter = [0]

    def strongconnect(v):
        stk = [(v, iter(adj.get(v, [])))]
        call_stack = [v]
        idx[v] = counter[0]; low[v] = counter[0]; counter[0] += 1
        stack.append(v); on_stack.add(v)
        while stk:
            node, it = stk[-1]
            found = False
            for w in it:
                if w not in idx:
                    idx[w] = counter[0]; low[w] = counter[0]; counter[0] += 1
                    stack.append(w); on_stack.add(w)
                    stk.append((w, iter(adj.get(w, []))))
                    call_stack.append(w)
                    found = True
                    break
                elif w in on_stack:
                    low[node] = min(low[node], idx[w])
            if not found:
                stk.pop()
                call_stack.pop()
                if low[node] == idx[node]:
                    comp = []
                    while True:
                        w = stack.pop(); on_stack.discard(w); comp.append(w)
                        if w == node:
                            break
                    sccs.append(comp)
                if stk:
                    parent, _ = stk[-1]
                    low[parent] = min(low[parent], low[node])
    for v in vertices:
        if v not in idx:
            strongconnect(v)
    return sccs


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = list(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = set(VC) - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # Directed forced edges c → c' within VC_NG
    adj = defaultdict(list)
    edges_dir = 0
    for c in VC_NG:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                v = move_entries[ctx]
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc in VC_NG:
                    adj[c].append(nc)
                    edges_dir += 1

    # SCC analysis
    sccs = tarjan_scc(list(VC_NG), dict(adj))
    nontriv_sccs = [s for s in sccs if len(s) > 1]
    scc_sizes = Counter(len(s) for s in sccs)

    # SK = configs that can reach a non-trivial SCC
    # equivalently: configs whose out-degree in SCC-condensation eventually hits non-trivial
    nontriv_nodes = set()
    for s in nontriv_sccs:
        nontriv_nodes.update(s)
    # Reverse BFS from nontriv_nodes
    radj = defaultdict(list)
    for u, ws in adj.items():
        for w in ws:
            radj[w].append(u)
    SK_set = set(nontriv_nodes)
    q = list(nontriv_nodes); qi = 0
    while qi < len(q):
        c = q[qi]; qi += 1
        for u in radj.get(c, []):
            if u not in SK_set:
                SK_set.add(u); q.append(u)

    # Undirected graph
    und_edges = set()
    for u, ws in adj.items():
        for w in ws:
            e = (u, w) if u < w else (w, u)
            und_edges.add(e)
    E_und = len(und_edges)
    V_und = len(VC_NG)
    # Connected components via union-find
    parent = {c: c for c in VC_NG}
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    def union(a, b):
        a = find(a); b = find(b)
        if a != b: parent[a] = b
    for (u, w) in und_edges:
        union(u, w)
    comps = len({find(c) for c in VC_NG})
    b_1_undirected = E_und - V_und + comps

    # 2-cells: commuting squares
    # For each c, for each pair of positions (p, q) with |p-q| mod n >= 2,
    # if both forced moves exist at c, and both moves commute (don't modify
    # the other's context), a 2-cell is formed.
    two_cells = 0
    for c in VC_NG:
        forced_at = {}
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                v = move_entries[ctx]
                nc = list(c); nc[p] = v; nc = tuple(nc)
                forced_at[p] = (v, nc)
        for p, q in combinations(forced_at.keys(), 2):
            d = min((p - q) % n, (q - p) % n)
            if d < 2:
                continue
            vp, ncp = forced_at[p]
            vq, ncq = forced_at[q]
            # Move at p in config nc_q still valid?
            ctx_p_from_nq = (p, ncq[(p - 1) % n], ncq[p], ncq[(p + 1) % n])
            ctx_q_from_np = (q, ncp[(q - 1) % n], ncp[q], ncp[(q + 1) % n])
            if (ctx_p_from_nq in move_entries and move_entries[ctx_p_from_nq] == vp
                and ctx_q_from_np in move_entries and move_entries[ctx_q_from_np] == vq):
                # And the target is same
                target = list(c); target[p] = vp; target[q] = vq; target = tuple(target)
                if target in VC_NG:
                    two_cells += 1

    # Euler characteristic
    chi = V_und - E_und + two_cells
    # With 2-cells, b_1 can be bounded: b_1 ≥ max(0, -(V - E + F)) ish
    # Actually: chi = b_0 - b_1 + b_2, so b_1 = b_0 + b_2 - chi ≥ b_0 - chi
    b_1_with_2cells_lb = max(0, comps - chi)  # lower bound assuming b_2 ≥ 0

    bound = 2 ** (n - 1)
    return {
        'n': n, 'ms': ms, 'L': L,
        'V_und': V_und, 'E_und': E_und, 'E_dir': edges_dir,
        'comps': comps, 'b_1_undirected': b_1_undirected,
        'two_cells': two_cells, 'chi': chi,
        'b_1_with_2cells_lb': b_1_with_2cells_lb,
        '|SK|': len(SK_set),
        'n_nontriv_SCCs': len(nontriv_sccs),
        'max_SCC_size': max((len(s) for s in nontriv_sccs), default=0),
        'b_1_ge_bound': b_1_undirected >= bound,
        'b_1_2c_ge_bound': b_1_with_2cells_lb >= bound,
        'SK_ge_bound': len(SK_set) >= bound,
    }


def main():
    print("=" * 72)
    print("CW / homological probe of forced graph")
    print("=" * 72)
    plan = [
        (5, 1, 100, 4.0, 16),
        (6, 3, 30, 3.5, 17),
        (7, 20, 10, 5.0, 17),
    ]
    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
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
            if (idx + 1) % 5 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        bound = 2 ** (n - 1)
        print(f"\n  n={n}  records={len(recs)}  bound 2^(n-1) = {bound}")
        print(f"    avg V={sum(r['V_und'] for r in recs)/len(recs):.1f}")
        print(f"    avg E_undirected={sum(r['E_und'] for r in recs)/len(recs):.1f}")
        print(f"    avg E_directed={sum(r['E_dir'] for r in recs)/len(recs):.1f}")
        print(f"    avg components={sum(r['comps'] for r in recs)/len(recs):.2f}")
        print(f"    avg b_1(undirected)={sum(r['b_1_undirected'] for r in recs)/len(recs):.1f}")
        print(f"    avg 2-cells={sum(r['two_cells'] for r in recs)/len(recs):.1f}")
        print(f"    avg Euler χ={sum(r['chi'] for r in recs)/len(recs):.1f}")
        print(f"    avg b_1 lb w/ 2-cells={sum(r['b_1_with_2cells_lb'] for r in recs)/len(recs):.1f}")
        print(f"    avg |SK|={sum(r['|SK|'] for r in recs)/len(recs):.1f}")
        print(f"    avg #nontriv SCCs={sum(r['n_nontriv_SCCs'] for r in recs)/len(recs):.2f}")
        print(f"    avg max SCC size={sum(r['max_SCC_size'] for r in recs)/len(recs):.1f}")
        b1_ok = sum(1 for r in recs if r['b_1_ge_bound'])
        b1_2c = sum(1 for r in recs if r['b_1_2c_ge_bound'])
        sk_ok = sum(1 for r in recs if r['SK_ge_bound'])
        print(f"    b_1(undirected) ≥ 2^(n-1):     {b1_ok}/{len(recs)} ({100*b1_ok/len(recs):.1f}%)")
        print(f"    b_1 lb w/ 2-cells ≥ 2^(n-1):   {b1_2c}/{len(recs)} ({100*b1_2c/len(recs):.1f}%)")
        print(f"    |SK| ≥ 2^(n-1):                {sk_ok}/{len(recs)} ({100*sk_ok/len(recs):.1f}%)")
        # Distribution of b_1 - bound
        gaps = [r['b_1_undirected'] - bound for r in recs]
        print(f"    b_1 - 2^(n-1) range: [{min(gaps)}, {max(gaps)}]  median={sorted(gaps)[len(gaps)//2]}")


if __name__ == "__main__":
    main()
