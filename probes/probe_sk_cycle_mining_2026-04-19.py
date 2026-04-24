#!/usr/bin/env python3
"""R4b cycle-mining probe on D_tube = (N_1(C) ∩ VC-NG, tube-internal forced moves).

Reframe (2026-04-19 late):
    R4a (forest-bound closure) is DEAD — undirected forest bound does not
    apply to the directed tube graph (refuted by probe_sk_edge_sink_margin
    showing margin_inner < 0 in ~7% of n=5 records while peel ≠ ∅).
    R4b target: prove D_tube has a directed cycle. Cycle vertices serve as
    the nonempty forced-closed S ⊆ NG(C) the theorem interface consumes.

This probe mines the actual directed cycles to inform the new proof shape.

METRICS (per (n, ms, C)):
  structural
    |T|, |E|, |sinks|
  SCC
    number of SCCs, size distribution
    number of non-trivial SCCs (size ≥ 2, since no self-loops in G|_T)
    largest SCC size
    terminal SCC sizes (no outgoing edges to other SCCs)
  cycles
    girth — shortest directed cycle length in D_tube
    has_2cycle — a mutual flip c ↔ c' ever exists?
    has_L_cycle — does a length-L cycle exist? (L = |C|)
    distribution of girths across records
  shadow
    shadow_valid_qv — #(q, v) pairs where the full L-shadow
        (c_0[q←v] → c_1[q←v] → … → c_{L−1}[q←v] → c_0[q←v])
        stays inside T; requires far-q condition (q ∉ {p_i−1, p_i, p_i+1})
        to hold at EVERY step. Fairness ⟹ 0 for fair cycles when n ≤ 4 + |non-fire|.
    shadow_partial_max — max i-run where shadow lies in T (gives an
        upper bound on best shadow fragment length).
  signature of girth cycle
    vertex set: which cycle configs c, characterized by minimal (i, q, v) s.t.
    c = c_i[q←v]. Reported for the smallest non-trivial SCC's girth cycle.

PURPOSE
    - Confirm a directed cycle exists in every record (expected).
    - Identify the TYPE of cycle: small (2-cycle / 3-cycle), L-length (shadow-
      like), or medium.
    - Inform the proof shape (§acyclicity contradiction vs §self-map on core).
    - Test whether a uniform "canonical cycle family" exists that admits an
      analytical construction independent of per-record cycle discovery.

NOT IN SCOPE
    - Full cycle enumeration (exponential).
    - Margin inequalities (dead route).
    - Proof of directed-cycle existence (this is discovery, not proof).
"""
from __future__ import annotations

import json
import os
import sys
import time
from collections import Counter, defaultdict, deque
from itertools import product as iproduct


# ----- thresholds --------------------------------------------------------

def m_n(n):
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


# ----- multiset enumeration ----------------------------------------------

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


# ----- cycle enumeration -------------------------------------------------

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
            Lp = config[(p - 1) % n]
            Sp = config[p]
            Rp = config[(p + 1) % n]
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
                    Li = config[(i - 1) % n]
                    Si = config[i]
                    Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False
                        break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config)
                nc[p] = new_val
                nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


# ----- tube construction -------------------------------------------------

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
                if v == c[q]:
                    continue
                nc = list(c)
                nc[q] = v
                nc = tuple(nc)
                if nc not in cycle_set:
                    T.add(nc)

    adj = defaultdict(list)
    for c in T:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c)
                nc[p] = val
                nc = tuple(nc)
                if nc in T and nc not in adj[c]:
                    adj[c].append(nc)

    sinks = set(c for c in T if len(adj[c]) == 0)
    return T, dict(adj), sinks, V_list, cycle_set, L


# ----- Tarjan SCC (iterative) -------------------------------------------

def tarjan_scc(V, adj):
    """Return list of SCCs (each a frozenset of vertices)."""
    idx = {}
    lowlink = {}
    on_stack = set()
    stack = []
    counter = [0]
    sccs = []

    def strongconnect_iter(root):
        work = [(root, iter(adj.get(root, [])))]
        idx[root] = counter[0]
        lowlink[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        on_stack.add(root)

        while work:
            v, it = work[-1]
            try:
                w = next(it)
            except StopIteration:
                work.pop()
                if lowlink[v] == idx[v]:
                    comp = []
                    while True:
                        x = stack.pop()
                        on_stack.discard(x)
                        comp.append(x)
                        if x == v:
                            break
                    sccs.append(frozenset(comp))
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[v])
                continue
            if w not in idx:
                idx[w] = counter[0]
                lowlink[w] = counter[0]
                counter[0] += 1
                stack.append(w)
                on_stack.add(w)
                work.append((w, iter(adj.get(w, []))))
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], idx[w])

    for v in V:
        if v not in idx:
            strongconnect_iter(v)
    return sccs


# ----- shortest-cycle-through-vertex (BFS) ------------------------------

def shortest_cycle_in_scc(scc, adj):
    """Return length of shortest directed cycle entirely inside scc, or None."""
    scc_set = set(scc)
    best = None
    for start in scc:
        # BFS from start; looking for shortest path back to start of length ≥ 1.
        dist = {start: 0}
        q = deque([start])
        found = None
        while q:
            u = q.popleft()
            for w in adj.get(u, []):
                if w not in scc_set:
                    continue
                if w == start:
                    candidate = dist[u] + 1
                    if found is None or candidate < found:
                        found = candidate
                    continue
                if w not in dist:
                    dist[w] = dist[u] + 1
                    if best is not None and dist[w] + 1 >= best:
                        continue
                    q.append(w)
        if found is not None:
            if best is None or found < best:
                best = found
    return best


# ----- terminal-SCC detection -------------------------------------------

def terminal_sccs(sccs, adj):
    """Return SCCs with no outgoing edge to a different SCC."""
    scc_of = {}
    for i, s in enumerate(sccs):
        for v in s:
            scc_of[v] = i
    is_terminal = [True] * len(sccs)
    for i, s in enumerate(sccs):
        for v in s:
            for w in adj.get(v, []):
                if scc_of[w] != i:
                    is_terminal[i] = False
                    break
            if not is_terminal[i]:
                break
    return [sccs[i] for i in range(len(sccs)) if is_terminal[i]]


# ----- shadow coverage ---------------------------------------------------

def shadow_valid_counts(cycle, movers, V_list, T, n):
    """For each (q, v), count how many shadow steps c_i[q←v] → c_{i+1}[q←v]
    (with far-q at p_i) stay inside T. Also: did the full L-shadow close?"""
    L = len(movers)
    records = {}
    for q in range(n):
        for v in V_list[q]:
            full_shadow_in_T = True
            step_in_T = 0
            far_count = 0
            for i in range(L):
                p_i = movers[i]
                c_i = cycle[i]
                c_ip1 = cycle[(i + 1) % L]
                far = q not in {(p_i - 1) % n, p_i, (p_i + 1) % n}
                if v == c_i[q]:
                    # c_i[q←v] = c_i ∈ C; not in T.
                    full_shadow_in_T = False
                    continue
                if far:
                    far_count += 1
                src = list(c_i)
                src[q] = v
                src = tuple(src)
                dst = list(c_ip1)
                dst[q] = v
                dst = tuple(dst)
                if src in T and dst in T:
                    step_in_T += 1
                else:
                    full_shadow_in_T = False
            records[(q, v)] = {
                'steps_in_T': step_in_T,
                'far_steps': far_count,
                'full_shadow': full_shadow_in_T and far_count == L,
            }
    return records


# ----- signature extraction ----------------------------------------------

def signature(c, cycle, V_list, n):
    """Return the lex-min (i, q, v) s.t. c = cycle[i][q←v], or None if no match."""
    best = None
    for i, ci in enumerate(cycle):
        diff = [q for q in range(n) if ci[q] != c[q]]
        if len(diff) == 1:
            q = diff[0]
            v = c[q]
            key = (i, q, v)
            if best is None or key < best:
                best = key
    return best


# ----- analyze -----------------------------------------------------------

def analyze(ms, n, cycle, movers, det):
    T, adj, sinks, V_list, cycle_set, L = build_tube(ms, n, cycle, movers, det)
    if not T:
        return None
    sccs = tarjan_scc(T, adj)
    non_triv = [s for s in sccs if len(s) >= 2]
    term = terminal_sccs(sccs, adj)
    term_non_triv = [s for s in term if len(s) >= 2]

    # Girth of D_tube = min over non-trivial SCCs of shortest cycle in that SCC
    girth = None
    girth_scc = None
    for s in non_triv:
        g = shortest_cycle_in_scc(s, adj)
        if g is not None and (girth is None or g < girth):
            girth = g
            girth_scc = s

    # Has 2-cycle?
    has_2cycle = any(
        c in adj and any(c2 in adj.get(c1, []) for c1 in adj[c] for c2 in [c])
        for c in T
    )
    # Simpler: any (c, c') with c' in adj[c] and c in adj[c']
    two_cycles = []
    for c, succs in adj.items():
        for cp in succs:
            if c in adj.get(cp, []) and (cp, c) not in two_cycles:
                two_cycles.append((c, cp))

    # Has L-cycle? (smallest cycle has length exactly L)
    has_L_cycle = girth == L

    # Shadow data
    shadow_rec = shadow_valid_counts(cycle, movers, V_list, T, n)
    n_full_shadow = sum(1 for r in shadow_rec.values() if r['full_shadow'])
    max_partial = max((r['steps_in_T'] for r in shadow_rec.values()), default=0)
    # "far_coverage per step": how many distinct i have at least one (q, v)
    # with far and shadow step in T. Captures "shadow is always available
    # somewhere, though not universally".
    step_has_far_shadow = [False] * L
    for (q, v), r in shadow_rec.items():
        if r['far_steps'] > 0:
            for i in range(L):
                p_i = movers[i]
                if q in {(p_i - 1) % n, p_i, (p_i + 1) % n}:
                    continue
                if v == cycle[i][q]:
                    continue
                src = list(cycle[i]); src[q] = v; src = tuple(src)
                dst = list(cycle[(i+1) % L]); dst[q] = v; dst = tuple(dst)
                if src in T and dst in T:
                    step_has_far_shadow[i] = True
                    break
    shadow_step_coverage = sum(step_has_far_shadow)

    # Signature of girth cycle vertices
    girth_sig = []
    if girth_scc is not None and girth is not None:
        # BFS to recover an actual shortest cycle and record sigs
        start = next(iter(girth_scc))
        scc_set = set(girth_scc)
        parent = {start: None}
        dist = {start: 0}
        q = deque([start])
        cycle_vertices = None
        while q and cycle_vertices is None:
            u = q.popleft()
            for w in adj.get(u, []):
                if w not in scc_set:
                    continue
                if w == start and dist[u] + 1 == girth:
                    # reconstruct
                    seq = [start]
                    cur = u
                    while cur is not None:
                        seq.append(cur)
                        cur = parent[cur]
                    cycle_vertices = list(reversed(seq[:-1]))  # drop the dup
                    cycle_vertices.append(start)
                    break
                if w not in dist:
                    dist[w] = dist[u] + 1
                    parent[w] = u
                    q.append(w)
        if cycle_vertices:
            for c in cycle_vertices[:-1]:
                girth_sig.append(signature(c, cycle, V_list, n))

    return {
        'n': n, 'ms': list(ms), 'L': L,
        'T': len(T), 'sinks': len(sinks),
        'num_sccs': len(sccs),
        'scc_sizes': sorted([len(s) for s in sccs], reverse=True)[:5],
        'num_non_triv': len(non_triv),
        'largest_scc': max((len(s) for s in non_triv), default=0),
        'num_terminal_scc': len(term),
        'num_terminal_non_triv': len(term_non_triv),
        'girth': girth,
        'has_2cycle': len(two_cycles) > 0,
        'n_2cycles': len(two_cycles),
        'has_L_cycle': has_L_cycle,
        'n_full_shadow': n_full_shadow,
        'max_partial_shadow': max_partial,
        'shadow_step_coverage': shadow_step_coverage,  # ∈ [0, L]
        'girth_sig': girth_sig,
    }


# ----- driver ------------------------------------------------------------

def main():
    print("=" * 72, flush=True)
    print("R4b cycle-mining probe on D_tube", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1, 40, 2.0, 15),
        (6, 4, 20, 3.0, 17),
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
            for cycle, movers, det in cycles:
                if len(movers) < 2 * n:
                    continue
                r = analyze(ms, n, cycle, movers, det)
                if r is not None:
                    records.append(r)
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  t={time.time()-t0:.0f}s  "
                      f"records={len(records)}", flush=True)

    # --- summary ---------------------------------------------------------
    print(f"\n{'='*72}\nSummary ({len(records)} records, {time.time()-t_global:.0f}s)\n{'='*72}")
    by_n = defaultdict(list)
    for r in records:
        by_n[r['n']].append(r)

    cycle_dead = False
    for n in sorted(by_n):
        recs = by_n[n]
        girths = [r['girth'] for r in recs if r['girth'] is not None]
        no_girth = [r for r in recs if r['girth'] is None]
        two = sum(1 for r in recs if r['has_2cycle'])
        Lc = sum(1 for r in recs if r['has_L_cycle'])
        full_shadow = sum(1 for r in recs if r['n_full_shadow'] > 0)
        largest = [r['largest_scc'] for r in recs]
        term_nt = [r['num_terminal_non_triv'] for r in recs]
        step_cov = [r['shadow_step_coverage'] for r in recs]
        Ls = [r['L'] for r in recs]

        print(f"\n  n={n}  records={len(recs)}")
        print(f"    L:                  {min(Ls)}..{max(Ls)}  mean={sum(Ls)/len(Ls):.1f}")
        print(f"    records with girth: {len(girths)}/{len(recs)}")
        if girths:
            print(f"    girth:              {min(girths)}..{max(girths)}  "
                  f"mean={sum(girths)/len(girths):.2f}")
            girth_hist = Counter(girths)
            print(f"    girth histogram:    {dict(sorted(girth_hist.items()))}")
        print(f"    has 2-cycle:        {two}/{len(recs)} ({100*two/len(recs):.1f}%)")
        print(f"    has L-cycle:        {Lc}/{len(recs)} ({100*Lc/len(recs):.1f}%)")
        print(f"    has full shadow:    {full_shadow}/{len(recs)} ({100*full_shadow/len(recs):.1f}%)")
        print(f"    largest SCC size:   {min(largest)}..{max(largest)}  "
              f"mean={sum(largest)/len(largest):.1f}")
        print(f"    #terminal non-triv: {min(term_nt)}..{max(term_nt)}  "
              f"mean={sum(term_nt)/len(term_nt):.2f}")
        print(f"    shadow_step_cov/L:  "
              f"min={min(s/l for s,l in zip(step_cov,Ls)):.2f}  "
              f"max={max(s/l for s,l in zip(step_cov,Ls)):.2f}  "
              f"mean={sum(s/l for s,l in zip(step_cov,Ls))/len(recs):.2f}")

        if no_girth:
            print(f"    ⚠ CYCLE MISSING: {len(no_girth)} records with no directed cycle — R4b REFUTED")
            cycle_dead = True

    print(f"\n{'='*72}")
    if cycle_dead:
        print("VERDICT: R4b FAILS — some records have no directed cycle in D_tube.")
    else:
        print("VERDICT: R4b SURVIVES — every record has a directed cycle in D_tube.")
        # Canonical shape diagnosis:
        all_girths = [r['girth'] for r in records if r['girth'] is not None]
        all_2cycle = sum(1 for r in records if r['has_2cycle'])
        all_Lcycle = sum(1 for r in records if r['has_L_cycle'])
        print(f"  girth range: {min(all_girths)}..{max(all_girths)}  "
              f"mean={sum(all_girths)/len(all_girths):.2f}")
        print(f"  2-cycle present: {all_2cycle}/{len(records)}")
        print(f"  L-cycle present: {all_Lcycle}/{len(records)}")
        print(f"  total girth histogram: {dict(sorted(Counter(all_girths).items()))}")
    print(f"{'='*72}")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'r4b_cycle_mining_2026-04-19.json')
    with open(out_path, 'w') as f:
        # Strip the girth_sig tuples (not JSON-serialisable with defaults) via str
        safe = []
        for r in records:
            r2 = dict(r)
            r2['girth_sig'] = [list(s) if s else None for s in r2.get('girth_sig', [])]
            safe.append(r2)
        json.dump({'records': safe, 'plan': plan}, f)
    print(f"\nWrote {out_path} ({len(records)} records).", flush=True)


if __name__ == "__main__":
    main()
