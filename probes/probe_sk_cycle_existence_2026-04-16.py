#!/usr/bin/env python3
"""Direct cycle existence probes.

Don't peel, don't count, don't use R1. Instead: does the NG forced
graph always contain SHORT directed cycles? If yes → SK ≠ ∅ via
direct witness, bypassing cascade analysis.

Tests:

  (A) 4-cycle via adjacent positions (Approach 3c from handoff):
      Exists c₀→c₁→c₂→c₃→c₀ where edges alternate between two
      adjacent positions p, q=right(p).

  (B) Shortest forced cycle length: for each (ms, cycle), find the
      SHORTEST directed cycle in the NG forced graph and record its
      length + position-move multiset.

  (C) 2-cycles at the same position: do any exist? (Expected: NO,
      per handoff "no local 2-cycles exist".)

  (D) Adjacent-entry pigeonhole: at each position p, how many move
      entries? Are there always ≥ 2 adjacent-positions (p, p+1)
      with unblocked entries (source+target in NG)?

  (E) Two-mover SCC: in the SK, what's the fraction of strongly
      connected components that use moves at only 2 positions?
      (Handoff "2 SCCs consistently at n=7".)

  (F) Strongly connected component structure: # SCCs, min SCC size,
      max SCC size, distribution.
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


def build_forced_graph(ms, n, cycle, det):
    cycle_set = set(cycle)
    V = value_sets(cycle, n)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    out_edges = defaultdict(set)
    edge_pos = {}
    for c in vc_ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in vc_ng:
                    out_edges[c].add(nc)
                    edge_pos[(c, nc)] = p
    return vc_ng, out_edges, edge_pos, move_entries


def scc(nodes, out_edges):
    """Tarjan's SCC."""
    index = [0]
    stack = []
    on_stack = {}
    idx = {}
    low = {}
    comps = []

    def strongconnect(v):
        work = [(v, iter(out_edges.get(v, [])))]
        idx[v] = low[v] = index[0]; index[0] += 1
        stack.append(v); on_stack[v] = True
        while work:
            v, it = work[-1]
            try:
                w = next(it)
                if w not in idx:
                    idx[w] = low[w] = index[0]; index[0] += 1
                    stack.append(w); on_stack[w] = True
                    work.append((w, iter(out_edges.get(w, []))))
                elif on_stack.get(w):
                    low[v] = min(low[v], idx[w])
            except StopIteration:
                work.pop()
                if work:
                    p = work[-1][0]
                    low[p] = min(low[p], low[v])
                if low[v] == idx[v]:
                    comp = []
                    while True:
                        x = stack.pop(); on_stack[x] = False
                        comp.append(x)
                        if x == v: break
                    comps.append(comp)
    for v in nodes:
        if v not in idx:
            strongconnect(v)
    return comps


def shortest_cycle_length(vc_ng, out_edges):
    """BFS from each node to find shortest cycle containing it."""
    best = None
    nodes = list(vc_ng)
    for start in nodes:
        # BFS
        dist = {start: 0}
        queue = [start]
        q_i = 0
        while q_i < len(queue):
            v = queue[q_i]; q_i += 1
            d = dist[v]
            if best is not None and d + 1 >= best:
                continue
            for w in out_edges.get(v, []):
                if w == start:
                    if best is None or d + 1 < best:
                        best = d + 1
                elif w not in dist:
                    dist[w] = d + 1
                    queue.append(w)
    return best


def has_4cycle_adjacent(vc_ng, out_edges, edge_pos, n):
    """Look for c0->c1->c2->c3->c0 with edges at positions p,q,p,q where q=(p+1)%n."""
    for c0 in vc_ng:
        for c1 in out_edges.get(c0, ()):
            p = edge_pos[(c0, c1)]
            q = (p + 1) % n
            for c2 in out_edges.get(c1, ()):
                if edge_pos[(c1, c2)] != q:
                    continue
                for c3 in out_edges.get(c2, ()):
                    if edge_pos[(c2, c3)] != p:
                        continue
                    if c0 in out_edges.get(c3, ()) and edge_pos[(c3, c0)] == q:
                        return (c0, c1, c2, c3)
    return None


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    vc_ng, out_edges, edge_pos, move_entries = build_forced_graph(ms, n, cycle, det)
    scc_list = scc(vc_ng, out_edges)
    nontriv_scc = [c for c in scc_list if len(c) >= 2 or any(v in out_edges.get(v, ()) for v in c)]

    # Shortest cycle
    shortest = shortest_cycle_length(vc_ng, out_edges) if nontriv_scc else None

    # 2-cycles at same position?
    twocycle_same_pos = 0
    for c1 in vc_ng:
        for c2 in out_edges.get(c1, ()):
            if c1 in out_edges.get(c2, ()):
                if edge_pos[(c1, c2)] == edge_pos[(c2, c1)]:
                    twocycle_same_pos += 1

    # 4-cycle adjacent-position test
    fc4_adj = has_4cycle_adjacent(vc_ng, out_edges, edge_pos, n)

    # Per-position unblocked entry count
    unblocked_per_pos = [0] * n
    for (p, Lv, Sv, Rv), val in move_entries.items():
        # Is this entry unblocked? Source + target both in NG?
        free_ranges = []
        for i in range(n):
            if i in ((p - 1) % n, p, (p + 1) % n):
                continue
            # Values: need c in VC so take V_i
            pass
        # Quick test: does there EXIST a c ∈ VC-NG matching this context with target in VC-NG?
        # We built out_edges using move_entries; count distinct source configs for this entry
        hit = 0
        for c in vc_ng:
            if c[(p - 1) % n] == Lv and c[p] == Sv and c[(p + 1) % n] == Rv:
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in vc_ng:
                    hit += 1
        if hit > 0:
            unblocked_per_pos[p] += 1

    # How many adjacent pairs (p, p+1) both have ≥1 unblocked entry?
    adjacent_unblocked_pairs = sum(
        1 for p in range(n)
        if unblocked_per_pos[p] >= 1 and unblocked_per_pos[(p + 1) % n] >= 1
    )
    # Also non-adjacent pairs
    total_unblocked_positions = sum(1 for x in unblocked_per_pos if x > 0)

    # SK via SCC (immune core = union of nontriv SCCs)
    sk_set = set()
    for c in nontriv_scc:
        sk_set.update(c)

    return {
        'n': n, 'ms': ms, 'L': L, 'vc_ng': len(vc_ng),
        'num_sccs': len(scc_list),
        'num_nontriv_sccs': len(nontriv_scc),
        'max_scc_size': max((len(c) for c in scc_list), default=0),
        'nontriv_scc_sizes': sorted([len(c) for c in nontriv_scc], reverse=True),
        'sk_size': len(sk_set),
        'shortest_cycle': shortest,
        'twocycle_same_pos': twocycle_same_pos,
        'has_4cycle_adjacent': fc4_adj is not None,
        'unblocked_per_pos': tuple(unblocked_per_pos),
        'adjacent_unblocked_pairs': adjacent_unblocked_pairs,
        'total_unblocked_positions': total_unblocked_positions,
    }


def main():
    print("=" * 72)
    print("Cycle existence probe — direct witnesses for SK ≠ ∅")
    print("=" * 72)

    plan = [
        (5, 1, 600, 4.0, 16),
        (6, 5, 200, 3.0, 16),
        (7, 30, 60, 2.0, 16),
    ]

    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets (of {len(multisets)}) ===", flush=True)
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
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nCycle existence results\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records:
        by_n[r['n']].append(r)

    for n, recs in sorted(by_n.items()):
        print(f"\n  n={n}  records={len(recs)}")
        sc = [r['shortest_cycle'] for r in recs if r['shortest_cycle'] is not None]
        print(f"    shortest_cycle: min={min(sc) if sc else None} max={max(sc) if sc else None}")
        sc_counter = Counter(sc)
        print(f"    shortest_cycle distribution: {dict(sc_counter)}")
        no_cycle = sum(1 for r in recs if r['num_nontriv_sccs'] == 0)
        print(f"    records with NO nontriv SCC (SK=∅): {no_cycle}")
        fc4 = sum(1 for r in recs if r['has_4cycle_adjacent'])
        print(f"    records with 4-cycle via adjacent positions: {fc4}/{len(recs)} ({100*fc4/len(recs):.1f}%)")
        tc = sum(r['twocycle_same_pos'] for r in recs)
        print(f"    total 2-cycles at same position (summed): {tc}")
        sz = [r['sk_size'] for r in recs]
        print(f"    sk_size: min={min(sz)} max={max(sz)} avg={sum(sz)/len(sz):.1f}")
        nss = [r['num_nontriv_sccs'] for r in recs]
        print(f"    nontriv_sccs: min={min(nss)} max={max(nss)} avg={sum(nss)/len(nss):.2f}")
        apc = [r['adjacent_unblocked_pairs'] for r in recs]
        print(f"    adjacent unblocked pairs: min={min(apc)} max={max(apc)} avg={sum(apc)/len(apc):.2f}")
        tup = [r['total_unblocked_positions'] for r in recs]
        print(f"    total unblocked positions: min={min(tup)} max={max(tup)} avg={sum(tup)/len(tup):.2f}")

    # Failures of adjacent 4-cycle
    print(f"\n{'='*72}")
    print(f"Records WITHOUT adjacent 4-cycle (counter-examples to Approach 3c)")
    print(f"{'='*72}")
    no_fc4 = [r for r in all_records if not r['has_4cycle_adjacent']]
    print(f"  Total: {len(no_fc4)} / {len(all_records)}")
    if no_fc4:
        for r in no_fc4[:5]:
            print(f"    n={r['n']} ms={r['ms']} L={r['L']} |SK|={r['sk_size']} shortest_cycle={r['shortest_cycle']}")

    # Is adjacent-unblocked-pairs always ≥ 1?
    print(f"\n{'='*72}")
    print(f"Does every record have ≥ 1 adjacent unblocked pair?")
    print(f"{'='*72}")
    no_adj_pair = [r for r in all_records if r['adjacent_unblocked_pairs'] == 0]
    print(f"  Records with NO adjacent unblocked pair: {len(no_adj_pair)} / {len(all_records)}")
    if no_adj_pair:
        for r in no_adj_pair[:5]:
            print(f"    n={r['n']} ms={r['ms']} L={r['L']} unblocked_per_pos={r['unblocked_per_pos']}")


if __name__ == "__main__":
    main()
