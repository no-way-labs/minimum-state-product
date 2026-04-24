#!/usr/bin/env python3
"""Positional characterisation of the 6 Case-C twist events.

Key finding from probe_sk_min_caseC_threading: min Case-C = 6 for n ≥ 6
universally.  This probe characterises those 6 twist positions on the
base girth cycle.

METRICS per record (only those with min_case_C >= 4)
  positions    : cyclic positions t ∈ {0..L-1} of each Case-C edge
  spacings     : cyclic gaps between consecutive C-positions
  defect_migrations : for each C-edge, the defect (q, v) before and after
                      and the "defect delta" = (Δq, Δv, Δi)
  firing_position_class : processor type at each C-edge
                          (binary / ternary / quaternary, by ms[p])
  same_mover_class : is every C-edge's firing position the same type?
  pairing     : do C-edges come in paired types (Δq_1 = -Δq_2)?
  adjacent_pairs : count of adjacent C-edge pairs
  q_change_edges: count of C-edges where defect position q changes
  i_change_edges: count of C-edges where slot index i jumps (|Δi| > 1)

Goal: determine whether 6 means
  (a) defect-migration count,
  (b) phase-crossing count,
  (c) paired twist events (6 = 3 pairs?),
  (d) processor-boundary crossings.
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict, deque
from itertools import product as iproduct
from statistics import median


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
                new_det = dict(det); new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def build_tube(ms, n, cycle, movers, det):
    L = len(movers)
    V = [set() for _ in range(n)]
    for c in cycle:
        for q in range(n):
            V[q].add(c[q])
    V_list = [sorted(s) for s in V]
    cycle_set = set(cycle)
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
                val = move_entries[ctx]
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in T:
                    adj_edge[c].append((nc, p))
    return T, dict(adj_edge), V_list, cycle_set, L


def all_signatures(c, cycle, n):
    sigs = []
    for i, ci in enumerate(cycle):
        diffs = [q for q in range(n) if ci[q] != c[q]]
        if len(diffs) == 1:
            q = diffs[0]; v = c[q]
            sigs.append((i, q, v))
    return sigs


def tarjan_scc(V, adj_plain):
    idx = {}; lowlink = {}; on_stack = set(); stack = []; counter = [0]; sccs = []

    def strongconnect(root):
        work = [(root, iter(adj_plain.get(root, [])))]
        idx[root] = counter[0]; lowlink[root] = counter[0]; counter[0] += 1
        stack.append(root); on_stack.add(root)
        while work:
            v, it = work[-1]
            try:
                w = next(it)
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
                while cur is not None:
                    seq.append(cur); cur = parent[cur]
                return list(reversed(seq))
            if w not in dist:
                dist[w] = dist[u] + 1; parent[w] = u; q.append(w)
    return None


def base_girth_cycle_with_positions(T, adj_edge):
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
    positions = []
    for t in range(len(best_seq) - 1):
        c, cp = best_seq[t], best_seq[t + 1]
        for (cpp, p) in adj_edge[c]:
            if cpp == cp:
                positions.append(p); break
        else:
            positions.append(None)
    return best_seq, positions


def classify_edge(sigma, sigma_next, p, c_next, movers, L):
    i, q, v = sigma
    i_n, q_n, v_n = sigma_next
    if p == q and i_n == i and q_n == q and v_n == c_next[p]:
        return 'A'
    if p == movers[i] and i_n == (i + 1) % L and q_n == q and v_n == v:
        return 'B'
    return 'C'


def min_case_C_thread(girth_seq, firing, sigs, cycle, movers, L):
    path = girth_seq[:-1]
    best_min = None; best_thread = None; best_types = None
    for sigma0 in sigs[path[0]]:
        dp_prev = {sigma0: 0}
        backptr = [{sigma0: (None, None)}]
        for t in range(len(path)):
            c_next = path[(t + 1) % len(path)]
            p = firing[t]
            dp_new = {}; back_new = {}
            for sigma, cc in dp_prev.items():
                for sigma_next in sigs[c_next]:
                    edge_type = classify_edge(sigma, sigma_next, p, c_next, movers, L)
                    new_cc = cc + (0 if edge_type != 'C' else 1)
                    if sigma_next not in dp_new or dp_new[sigma_next] > new_cc:
                        dp_new[sigma_next] = new_cc
                        back_new[sigma_next] = (sigma, edge_type)
            dp_prev = dp_new; backptr.append(back_new)
        if sigma0 in dp_prev:
            cc = dp_prev[sigma0]
            if best_min is None or cc < best_min:
                best_min = cc
                thread = [sigma0]; types = []
                cur = sigma0
                for t in range(len(path), 0, -1):
                    prev_sigma, edge_t = backptr[t][cur]
                    thread.append(prev_sigma); types.append(edge_t)
                    cur = prev_sigma
                thread.reverse(); types.reverse()
                best_thread = tuple(thread); best_types = tuple(types)
    return best_min, best_thread, best_types


def audit(ms, n, cycle, movers, det):
    T, adj_edge, V_list, cycle_set, L = build_tube(ms, n, cycle, movers, det)
    if not T: return None
    sigs = {c: all_signatures(c, cycle, n) for c in T}
    if any(len(sigs[c]) == 0 for c in T): return None
    girth_seq, firing = base_girth_cycle_with_positions(T, adj_edge)
    if girth_seq is None or any(p is None for p in firing): return None

    min_cc, thread, types = min_case_C_thread(
        girth_seq, firing, sigs, cycle, movers, L)
    if thread is None or types is None: return None

    # Positions of Case-C edges
    c_positions = [t for t, ty in enumerate(types) if ty == 'C']
    # Cyclic spacings between consecutive C's
    spacings = []
    for k in range(len(c_positions)):
        t0 = c_positions[k]
        t1 = c_positions[(k + 1) % len(c_positions)]
        gap = (t1 - t0) % L
        spacings.append(gap if gap > 0 else L)

    # Per-C-edge forensics
    c_forensics = []
    path = girth_seq[:-1]
    for t in c_positions:
        sigma = thread[t]; sigma_next = thread[t + 1]
        p = firing[t]
        c_now = path[t]; c_nxt = path[(t + 1) % len(path)]
        i, q, v = sigma
        i_n, q_n, v_n = sigma_next
        dq = (q_n - q) % n
        dv = v_n - v
        di = (i_n - i) % L
        # Processor class of firing position p (arity)
        p_arity = ms[p]
        # Is q change or i change or both?
        q_changed = (q_n != q)
        i_changed = (i_n != i)
        v_changed = (v_n != v)
        c_forensics.append({
            't': t, 'p': p, 'p_arity': p_arity,
            'q_before': q, 'v_before': v, 'i_before': i,
            'q_after': q_n, 'v_after': v_n, 'i_after': i_n,
            'dq_mod_n': dq, 'dv': dv, 'di_mod_L': di,
            'q_changed': q_changed, 'v_changed': v_changed, 'i_changed': i_changed,
            'sig_mult_before': len(sigs[c_now]),
            'sig_mult_after': len(sigs[c_nxt]),
        })

    # Adjacent C-pairs: consecutive t, t+1 both C
    adj_pairs = sum(1 for k in range(len(c_positions))
                    if c_positions[(k + 1) % len(c_positions)]
                       == (c_positions[k] + 1) % L)

    # Are all C-edges' firing positions the same arity?
    arities_at_C = [f['p_arity'] for f in c_forensics]
    arity_counts = Counter(arities_at_C)

    # Pairing signal: sum of all dq_mod_n; if 0 mod n, pairs cancel
    total_dq = sum(f['dq_mod_n'] for f in c_forensics) % n
    total_di = sum(f['di_mod_L'] for f in c_forensics) % L
    q_change_count = sum(1 for f in c_forensics if f['q_changed'])
    i_change_count = sum(1 for f in c_forensics if f['i_changed'])
    v_change_count = sum(1 for f in c_forensics if f['v_changed'])

    return {
        'n': n, 'ms': list(ms), 'L': L, 'T': len(T),
        'girth': len(girth_seq) - 1,
        'min_case_C': min_cc,
        'c_positions': c_positions,
        'c_spacings': spacings,
        'c_spacing_dist': dict(Counter(spacings)),
        'adjacent_C_pairs': adj_pairs,
        'arity_counts_at_C': dict(arity_counts),
        'total_dq_mod_n': total_dq,
        'total_di_mod_L': total_di,
        'q_change_count': q_change_count,
        'i_change_count': i_change_count,
        'v_change_count': v_change_count,
        'c_forensics': c_forensics,
    }


def main():
    print("=" * 72, flush=True)
    print("Twist geometry — where do the 6 Case-C events sit?", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (6, 4,  20, 3.0, 17),
        (7, 40, 10, 3.0, 19),
        (8, 200, 5, 4.0, 21),
    ]
    records = []
    t_global = time.time()

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  M_n={Mn}  sampled={len(sampled)} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cyc, movers, det in cycles:
                if len(movers) < 2 * n: continue
                r = audit(ms, n, cyc, movers, det)
                if r is not None: records.append(r)
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  t={time.time()-t0:.0f}s  "
                      f"records={len(records)}", flush=True)

    print(f"\n{'='*72}\nSummary ({len(records)} records, "
          f"{time.time()-t_global:.0f}s)\n{'='*72}")

    by_n = defaultdict(list)
    for r in records: by_n[r['n']].append(r)

    for n in sorted(by_n):
        recs = [r for r in by_n[n] if r['min_case_C'] == 6]
        other = [r for r in by_n[n] if r['min_case_C'] != 6]
        print(f"\n  n={n}  records_with_mcC=6: {len(recs)}  (other: {len(other)})")
        if not recs: continue

        # Spacing distribution (cyclic gaps between consecutive C's)
        all_spacings = [s for r in recs for s in r['c_spacings']]
        print(f"    C-spacing histogram (L∈{sorted({r['L'] for r in recs})}): "
              f"{Counter(all_spacings).most_common(8)}")

        # Adjacent pairs distribution
        adj = [r['adjacent_C_pairs'] for r in recs]
        print(f"    adjacent-C-pairs: {dict(sorted(Counter(adj).items()))}")

        # Arity of firing positions at C-edges
        arity_agg = Counter()
        for r in recs:
            for a, c in r['arity_counts_at_C'].items():
                arity_agg[a] += c
        print(f"    firing-position arity at C-steps: {dict(sorted(arity_agg.items()))}")

        # Defect change stats
        qc = [r['q_change_count'] for r in recs]
        ic = [r['i_change_count'] for r in recs]
        vc = [r['v_change_count'] for r in recs]
        print(f"    q_change count per record: {dict(sorted(Counter(qc).items()))}")
        print(f"    i_change count per record: {dict(sorted(Counter(ic).items()))}")
        print(f"    v_change count per record: {dict(sorted(Counter(vc).items()))}")

        # Total Δq mod n, Δi mod L — pairing invariants
        dq_tot = [r['total_dq_mod_n'] for r in recs]
        di_tot = [r['total_di_mod_L'] for r in recs]
        print(f"    total Δq mod n: {dict(sorted(Counter(dq_tot).items()))}")
        print(f"    total Δi mod L: {dict(sorted(Counter(di_tot).items()))}")

        # Multiplicity at C-steps
        sig_mult = Counter()
        for r in recs:
            for f in r['c_forensics']:
                sig_mult[f['sig_mult_before']] += 1
        print(f"    |Σ(c)| at C-steps (before): {dict(sorted(sig_mult.items()))}")

        # (q_before, q_after) transition pairs
        qq_pairs = Counter()
        for r in recs:
            for f in r['c_forensics']:
                qq_pairs[(f['q_before'], f['q_after'])] += 1
        top_qq = qq_pairs.most_common(10)
        print(f"    top (q_before, q_after) pairs: {top_qq}")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'r4b_twist_geometry_2026-04-19.json')
    with open(out_path, 'w') as f:
        json.dump({'records': records, 'plan': plan}, f)
    print(f"\nWrote {out_path}.", flush=True)


if __name__ == "__main__":
    main()
