#!/usr/bin/env python3
"""Cross-reference shallow escapes (E7) with twist positions (2026-04-19).

Hypothesis (E8): shallow-escape vertices (cycle vertices from which a forced
fire lands in T\\S) concentrate at twist vertices (endpoints of Case-C edges
in the base girth threading).

If shallow-escape-vertex set ⊆ twist-vertex set with high fraction, shallow
escapes ≡ twist-structure remnant. Would license classifying shallow escapes
by twist-calculus terms (R/L/F generators) even though the twist-calculus
route is dead.

Runs both audits in ONE pass to avoid record-matching ambiguity.
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict, deque
from itertools import product as iproduct


def m_n(n):
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


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
            prefix.append(m); rec(i + 1, prefix, new_prod); prefix.pop()
    rec(0, [], 1)
    return out


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
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp); forced_out = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced_out is not None and forced_out != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
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


def build_tube(ms, n, cycle, movers, det):
    L = len(movers); V = [set() for _ in range(n)]
    for c in cycle:
        for q in range(n): V[q].add(c[q])
    V_list = [sorted(s) for s in V]; cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    T = set()
    for c in cycle:
        for q in range(n):
            for v in V_list[q]:
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set: T.add(nc)
    adj_edge = defaultdict(list)
    for c in T:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]; nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in T: adj_edge[c].append((nc, p))
    return T, dict(adj_edge), V_list, cycle_set, L, move_entries


def all_signatures(c, cycle, n):
    sigs = []
    for i, ci in enumerate(cycle):
        diffs = [q for q in range(n) if ci[q] != c[q]]
        if len(diffs) == 1:
            q = diffs[0]; v = c[q]; sigs.append((i, q, v))
    return sigs


def tarjan_scc(V, adj_plain):
    idx = {}; lowlink = {}; on_stack = set(); stack = []; counter = [0]; sccs = []
    def strongconnect(root):
        work = [(root, iter(adj_plain.get(root, [])))]
        idx[root] = counter[0]; lowlink[root] = counter[0]; counter[0] += 1
        stack.append(root); on_stack.add(root)
        while work:
            v, it = work[-1]
            try: w = next(it)
            except StopIteration:
                work.pop()
                if lowlink[v] == idx[v]:
                    comp = []
                    while True:
                        x = stack.pop(); on_stack.discard(x); comp.append(x)
                        if x == v: break
                    sccs.append(frozenset(comp))
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[v])
                continue
            if w not in idx:
                idx[w] = counter[0]; lowlink[w] = counter[0]; counter[0] += 1
                stack.append(w); on_stack.add(w)
                work.append((w, iter(adj_plain.get(w, []))))
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], idx[w])
    for v in V:
        if v not in idx: strongconnect(v)
    return sccs


def shortest_cycle_through(start, adj_plain, scc_set):
    dist = {start: 0}; parent = {start: None}; q = deque([start])
    while q:
        u = q.popleft()
        for w in adj_plain.get(u, []):
            if w not in scc_set: continue
            if w == start:
                seq = [start]; cur = u
                while cur is not None: seq.append(cur); cur = parent[cur]
                return list(reversed(seq))
            if w not in dist: dist[w] = dist[u] + 1; parent[w] = u; q.append(w)
    return None


def base_girth_cycle_with_firings(T, adj_edge):
    adj_plain = {c: [cp for (cp, _) in adj_edge.get(c, [])] for c in T}
    sccs = tarjan_scc(T, adj_plain)
    best_seq = None
    for s in sccs:
        if len(s) < 2: continue
        start = next(iter(s))
        seq = shortest_cycle_through(start, adj_plain, s)
        if seq is not None and (best_seq is None or len(seq) < len(best_seq)):
            best_seq = seq
    if best_seq is None: return None, None
    firings = []
    for t in range(len(best_seq) - 1):
        c, cp = best_seq[t], best_seq[t + 1]
        for (cpp, p) in adj_edge[c]:
            if cpp == cp: firings.append(p); break
        else: firings.append(None)
    return best_seq, firings


def classify_edge(sigma, sigma_next, p, movers, L):
    i, q, v = sigma; i_n, q_n, v_n = sigma_next
    if p == q and i_n == i and q_n == q: return 'A'
    if p == movers[i] and i_n == (i + 1) % L and q_n == q and v_n == v: return 'B'
    return 'C'


def min_case_C_thread(girth_seq, firing, sigs, L, movers):
    path = girth_seq[:-1]
    best_min = None; best_thread = None; best_types = None
    for sigma0 in sigs[path[0]]:
        dp_prev = {sigma0: 0}; backptr = [{sigma0: (None, None)}]
        for t in range(len(path)):
            c_next = path[(t + 1) % len(path)]; p = firing[t]
            dp_new = {}; back_new = {}
            for sigma, cc in dp_prev.items():
                for sigma_next in sigs[c_next]:
                    edge_type = classify_edge(sigma, sigma_next, p, movers, L)
                    new_cc = cc + (0 if edge_type != 'C' else 1)
                    if sigma_next not in dp_new or dp_new[sigma_next] > new_cc:
                        dp_new[sigma_next] = new_cc
                        back_new[sigma_next] = (sigma, edge_type)
            dp_prev = dp_new; backptr.append(back_new)
        if sigma0 in dp_prev:
            cc = dp_prev[sigma0]
            if best_min is None or cc < best_min:
                best_min = cc
                thread = [sigma0]; types = []; cur = sigma0
                for t in range(len(path), 0, -1):
                    prev_sigma, edge_t = backptr[t][cur]
                    thread.append(prev_sigma); types.append(edge_t); cur = prev_sigma
                thread.reverse(); types.reverse()
                best_thread = tuple(thread); best_types = tuple(types)
    return best_min, best_thread, best_types


def audit(ms, n, cycle, movers, det):
    T, adj_edge, V_list, cycle_set, L, move_entries = build_tube(
        ms, n, cycle, movers, det)
    if not T: return None
    girth_seq, firings = base_girth_cycle_with_firings(T, adj_edge)
    if girth_seq is None or any(f is None for f in firings): return None
    S = girth_seq[:-1]; S_set = set(S); S_index = {c: i for i, c in enumerate(S)}

    # Shallow escapes (into T\S)
    shallow_escape_vertices = set()  # c_idx values
    shallow_escape_firings = []  # (c_idx, p) pairs
    for c_idx, c in enumerate(S):
        for p in range(n):
            ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if ctx not in move_entries: continue
            val = move_entries[ctx]
            target = list(c); target[p] = val; target = tuple(target)
            if target in S_set or target in cycle_set: continue
            # target in T\S or outside T
            if target in T:
                shallow_escape_vertices.add(c_idx)
                shallow_escape_firings.append((c_idx, p))

    # Twist positions (Case-C edges)
    sigs = {c: all_signatures(c, cycle, n) for c in T}
    if any(len(sigs[c]) == 0 for c in T): return None
    min_cc, thread, types = min_case_C_thread(girth_seq, firings, sigs, L, movers)
    if thread is None or types is None: return None
    if min_cc < 4: return None  # restrict to twist-regime records

    # Case-C edge positions t ∈ {0..L-1}: edge from S[t] to S[(t+1) % L]
    c_positions = [t for t, ty in enumerate(types) if ty == 'C']
    # Twist vertex set: endpoints of C-edges (both source and target)
    twist_vertices = set()
    for t in c_positions:
        twist_vertices.add(t)             # source vertex index
        twist_vertices.add((t + 1) % L)   # target vertex index
    # Twist firings: firing processor at each C-edge
    twist_firings = [(t, firings[t]) for t in c_positions]

    # Correlation
    se_set = shallow_escape_vertices
    tw_set = twist_vertices
    intersect = se_set & tw_set
    se_in_tw = len(intersect) / len(se_set) if se_set else None
    tw_in_se = len(intersect) / len(tw_set) if tw_set else None

    # Firing-processor overlap at twist vs shallow
    tw_firing_procs = set(fp for (_, fp) in twist_firings)
    se_firing_procs = set(fp for (_, fp) in shallow_escape_firings)
    proc_intersect = tw_firing_procs & se_firing_procs

    return {
        'n': n, 'ms': list(ms), 'L': L, 'T_size': len(T), 'S_size': len(S),
        'min_case_C': min_cc,
        'n_shallow_escape': len(shallow_escape_firings),
        'n_shallow_escape_vertices': len(se_set),
        'n_twist_positions': len(c_positions),
        'n_twist_vertices': len(tw_set),
        'intersect_size': len(intersect),
        'se_in_tw_frac': se_in_tw,
        'tw_in_se_frac': tw_in_se,
        'tw_firing_procs': sorted(tw_firing_procs),
        'se_firing_procs': sorted(se_firing_procs),
        'proc_intersect_size': len(proc_intersect),
    }


def main():
    print("=" * 72, flush=True)
    print("Shallow-escape × Twist cross-reference (E8, 2026-04-20)", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (6, 4,  20, 3.0, 17),
        (7, 40, 10, 3.0, 19),
        (8, 200, 5, 4.0, 21),
    ]
    records = []; t_global = time.time()

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n(n); multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  sampled={len(sampled)} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cyc, movers, det in cycles:
                if len(movers) < 2 * n: continue
                r = audit(ms, n, cyc, movers, det)
                if r is not None: records.append(r)
            if (idx + 1) % max(1, len(sampled) // 5) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  t={time.time()-t0:.0f}s  "
                      f"records={len(records)}", flush=True)

    print(f"\n{'='*72}\nSummary ({len(records)} records, "
          f"{time.time()-t_global:.0f}s)\n{'='*72}")

    by_n = defaultdict(list)
    for r in records: by_n[r['n']].append(r)

    for n in sorted(by_n):
        recs = by_n[n]
        print(f"\n  n={n}  records (min_cc>=4): {len(recs)}")
        se_in_tw = [r['se_in_tw_frac'] for r in recs if r['se_in_tw_frac'] is not None]
        if se_in_tw:
            print(f"    shallow-escape vertex ⊆ twist vertex fraction:")
            print(f"      min={min(se_in_tw):.3f}  median={sorted(se_in_tw)[len(se_in_tw)//2]:.3f}  "
                  f"max={max(se_in_tw):.3f}  mean={sum(se_in_tw)/len(se_in_tw):.3f}")
            full = sum(1 for f in se_in_tw if f == 1.0)
            ge80 = sum(1 for f in se_in_tw if f >= 0.8)
            print(f"      records with shallow_vert ⊆ twist_vert: {full}/{len(se_in_tw)}")
            print(f"      records with fraction >= 0.8: {ge80}/{len(se_in_tw)}")
        n_se_v = Counter(r['n_shallow_escape_vertices'] for r in recs)
        n_tw_v = Counter(r['n_twist_vertices'] for r in recs)
        print(f"    #shallow_escape_vertices per record: {dict(sorted(n_se_v.items()))}")
        print(f"    #twist_vertices per record: {dict(sorted(n_tw_v.items()))}")

        # Firing-processor correlation
        proc_match = [r['proc_intersect_size'] / len(r['se_firing_procs'])
                      if r['se_firing_procs'] else None for r in recs]
        proc_match = [p for p in proc_match if p is not None]
        if proc_match:
            print(f"    shallow firing-procs ⊆ twist firing-procs fraction:")
            print(f"      min={min(proc_match):.3f}  mean={sum(proc_match)/len(proc_match):.3f}")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'shallow_twist_corr_2026-04-20.json')
    with open(out_path, 'w') as f: json.dump({'records': records, 'plan': plan}, f)
    print(f"\nWrote {out_path}.", flush=True)


if __name__ == "__main__":
    main()
