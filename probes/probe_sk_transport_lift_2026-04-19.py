#!/usr/bin/env python3
"""Transport-lift probe for D_tube.

RENAMING (2026-04-19 late): "transport-lift route" replaces
"index-monotone return."  The cocycle audit (r4b_cocycle_audit) showed:
  - Σ(c) is multi-valued in 18-45% of tube vertices
  - edge δ sets often contain values ∉ {0, 1}
  - threaded-all-δ=1 choice exists in 0% of girth cycles
  - Σδ (mod L) = 0 on every lex-min girth cycle (1898/1898)
So the right object is not a scalar phase on V(D_tube); it is a lifted
graph D_lift whose vertices are (c, σ) with σ ∈ Σ(c), and whose edges
encode a transport relation T_e ⊆ Σ(c) × Σ(c') on each base edge.

THIS PROBE measures the lift structure under two transport definitions:

  T_strict:  (σ, σ') ∈ T_e  iff  (i'−i) mod L ∈ {0, 1}
             "physical" transport: one forced move advances by ≤ 1 slot.

  T_loose:   T_e = Σ(c) × Σ(c')
             maximally permissive — all pairs.

For each record, and each transport, report:
  |V(D_lift)|, |E(D_lift)|
  SCC count, largest SCC size
  terminal SCC count (SCCs with no outgoing edge to a different SCC)
  terminal SCC sizes (min/median/max)
  directed girth of D_lift
  whether the base-girth cycle projects from some lift cycle
  number of lift cycles projecting onto a fixed base girth cycle

These measurements answer:
  A1. Does D_lift have a nonempty terminal SCC ?
  A2. How big is it  (expect size ∈ {L, 2L, ... }) ?
  A3. Does the base girth cycle lift  (existence of ≥1 closed lift orbit) ?
  A4. Under T_strict, do we lose too many edges ?

NOT IN SCOPE
  - proving terminal SCC existence
  - Lean
  - any route selection before empirical verdict
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict, deque
from itertools import product as iproduct
from statistics import median


# ----- shared helpers (lifted from cocycle audit) ------------------------

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
    adj = defaultdict(list)
    for c in T:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in T and nc not in adj[c]: adj[c].append(nc)
    return T, dict(adj), V_list, cycle_set, L


def all_signatures(c, cycle, n):
    sigs = []
    for i, ci in enumerate(cycle):
        diffs = [q for q in range(n) if ci[q] != c[q]]
        if len(diffs) == 1:
            q = diffs[0]; v = c[q]
            sigs.append((i, q, v))
    return sigs


def tarjan_scc(V, adj):
    idx = {}; lowlink = {}; on_stack = set(); stack = []; counter = [0]; sccs = []

    def strongconnect(root):
        work = [(root, iter(adj.get(root, [])))]
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
                work.append((w, iter(adj.get(w, []))))
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], idx[w])

    for v in V:
        if v not in idx: strongconnect(v)
    return sccs


def shortest_cycle_through(start, adj, scc_set):
    dist = {start: 0}; parent = {start: None}; q = deque([start])
    while q:
        u = q.popleft()
        for w in adj.get(u, []):
            if w not in scc_set: continue
            if w == start:
                seq = [start]; cur = u
                while cur is not None:
                    seq.append(cur); cur = parent[cur]
                return list(reversed(seq))
            if w not in dist:
                dist[w] = dist[u] + 1; parent[w] = u; q.append(w)
    return None


def base_girth_cycle(V, adj):
    """Return a shortest directed cycle in the base graph, or None."""
    sccs = tarjan_scc(V, adj)
    best = None
    for s in sccs:
        if len(s) < 2: continue
        start = next(iter(s))
        seq = shortest_cycle_through(start, adj, s)
        if seq is not None and (best is None or len(seq) < len(best)):
            best = seq
    return best


# ----- lift construction -------------------------------------------------

def build_lift(T, adj, sigs, L, transport):
    """
    transport: 'strict' (δ ∈ {0,1}) or 'loose' (all pairs).
    Returns (V_lift, adj_lift) where vertices are (c, sig) tuples.
    """
    V_lift = []
    for c in T:
        for sig in sigs[c]:
            V_lift.append((c, sig))
    adj_lift = defaultdict(list)
    if transport == 'strict':
        def ok(i, ip):
            d = (ip - i) % L
            return d == 0 or d == 1
    else:
        def ok(i, ip):
            return True
    for c, succs in adj.items():
        for cp in succs:
            for sig in sigs[c]:
                i = sig[0]
                for sigp in sigs[cp]:
                    ip = sigp[0]
                    if ok(i, ip):
                        adj_lift[(c, sig)].append((cp, sigp))
    return V_lift, dict(adj_lift)


def terminal_sccs(V, adj, sccs):
    """Return list of SCCs with no outgoing edges to other SCCs."""
    scc_of = {}
    for i, s in enumerate(sccs):
        for v in s: scc_of[v] = i
    out_to_other = set()
    for v, succs in adj.items():
        sv = scc_of.get(v)
        if sv is None: continue
        for w in succs:
            sw = scc_of.get(w)
            if sw is not None and sw != sv:
                out_to_other.add(sv)
    return [s for i, s in enumerate(sccs) if i not in out_to_other]


def lift_cycles_over_base(base_seq, sigs, L, transport):
    """Count distinct lifts of a base cycle (closing the lift)."""
    if base_seq is None or len(base_seq) < 2: return 0
    # base_seq has start at both ends; strip the tail
    path = base_seq[:-1]
    closed = 0
    if transport == 'strict':
        def ok(i, ip):
            d = (ip - i) % L
            return d == 0 or d == 1
    else:
        def ok(i, ip):
            return True
    for start_sig in sigs[path[0]]:
        # BFS-like over signature threading
        # At each step t, we maintain set of reachable sigs for path[t].
        cur = {start_sig}
        for t in range(len(path)):
            nxt_vertex = path[(t + 1) % len(path)]
            nxt = set()
            for s in cur:
                for sp in sigs[nxt_vertex]:
                    if ok(s[0], sp[0]):
                        nxt.add(sp)
            cur = nxt
            if not cur: break
        if start_sig in cur:
            closed += 1
    return closed


# ----- per-record audit --------------------------------------------------

def audit(ms, n, cycle, movers, det):
    T, adj, V_list, cycle_set, L = build_tube(ms, n, cycle, movers, det)
    if not T: return None
    sigs = {c: all_signatures(c, cycle, n) for c in T}

    # Skip if any tube vertex has empty Σ (should never happen in tube, but
    # defend: vertices with diffs != 1 aren't in the tube by construction).
    if any(len(sigs[c]) == 0 for c in T): return None

    base_seq = base_girth_cycle(T, adj)
    base_girth = (len(base_seq) - 1) if base_seq is not None else None

    result = {
        'n': n, 'ms': list(ms), 'L': L, 'T': len(T),
        'base_girth': base_girth,
        'V_base': len(T),
    }
    result['sig_card_max'] = max(len(s) for s in sigs.values())
    result['V_lift_total'] = sum(len(s) for s in sigs.values())

    for name in ('strict', 'loose'):
        V_lift, adj_lift = build_lift(T, adj, sigs, L, name)
        n_edges = sum(len(v) for v in adj_lift.values())
        sccs = tarjan_scc(V_lift, adj_lift)
        sccs_sizes = sorted(len(s) for s in sccs)
        non_triv = [s for s in sccs if len(s) >= 2]
        terms = terminal_sccs(V_lift, adj_lift, sccs)
        term_non_triv = [s for s in terms if len(s) >= 2]
        term_sizes = sorted(len(s) for s in terms)
        term_non_triv_sizes = sorted(len(s) for s in term_non_triv)

        # Lift girth
        lift_girth = None
        for s in non_triv:
            start = next(iter(s))
            seq = shortest_cycle_through(start, adj_lift, s)
            if seq is not None:
                g = len(seq) - 1
                if lift_girth is None or g < lift_girth:
                    lift_girth = g

        # Lift cycles projecting onto base girth cycle
        base_proj_lifts = lift_cycles_over_base(base_seq, sigs, L, name)

        result[name] = {
            'V_lift': len(V_lift),
            'E_lift': n_edges,
            'scc_count': len(sccs),
            'scc_non_triv': len(non_triv),
            'largest_scc': max(sccs_sizes) if sccs_sizes else 0,
            'scc_size_top5': sccs_sizes[-5:] if sccs_sizes else [],
            'terminal_scc_count': len(terms),
            'terminal_non_triv': len(term_non_triv),
            'term_sizes': term_sizes[-10:] if term_sizes else [],
            'term_non_triv_min': term_non_triv_sizes[0] if term_non_triv_sizes else None,
            'term_non_triv_max': term_non_triv_sizes[-1] if term_non_triv_sizes else None,
            'term_non_triv_med': median(term_non_triv_sizes) if term_non_triv_sizes else None,
            'lift_girth': lift_girth,
            'base_girth_lift_closures': base_proj_lifts,
        }
    return result


# ----- driver ------------------------------------------------------------

def main():
    print("=" * 72, flush=True)
    print("Transport-lift probe on D_tube / D_lift", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1,  40, 2.0, 15),
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
        recs = by_n[n]
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    L distribution: {Counter(r['L'] for r in recs).most_common(3)}")
        print(f"    |T| range: [{min(r['T'] for r in recs)}, {max(r['T'] for r in recs)}]")
        print(f"    |V_lift| range: [{min(r['V_lift_total'] for r in recs)}, "
              f"{max(r['V_lift_total'] for r in recs)}]")
        print(f"    base girth match L: "
              f"{sum(1 for r in recs if r['base_girth'] == r['L'])}/{len(recs)}")

        for name, label in (('strict', 'T_strict (δ∈{0,1})'),
                            ('loose',  'T_loose (all pairs)')):
            print(f"\n    --- {label} ---")
            edges = [r[name]['E_lift'] for r in recs]
            print(f"    |E_lift| range: [{min(edges)}, {max(edges)}]  "
                  f"med={median(edges):.0f}")
            non_triv = [r[name]['scc_non_triv'] for r in recs]
            print(f"    non-trivial SCC count: "
                  f"{Counter(non_triv).most_common(5)}")
            term_nt = [r[name]['terminal_non_triv'] for r in recs]
            print(f"    terminal non-trivial SCC count: "
                  f"{Counter(term_nt).most_common(5)}")
            have_term = sum(1 for t in term_nt if t >= 1)
            print(f"    records with ≥1 terminal non-trivial SCC: "
                  f"{have_term}/{len(recs)} ({100*have_term/len(recs):.1f}%)")

            # terminal SCC size vs L
            size_vs_L = Counter()
            for r in recs:
                L = r['L']
                smax = r[name]['term_non_triv_max']
                if smax is None:
                    size_vs_L['no_term'] += 1
                elif smax == L:
                    size_vs_L['=L'] += 1
                elif smax == 2 * L:
                    size_vs_L['=2L'] += 1
                elif smax < L:
                    size_vs_L['<L'] += 1
                elif smax < 2 * L:
                    size_vs_L['L<·<2L'] += 1
                elif smax == 3 * L:
                    size_vs_L['=3L'] += 1
                else:
                    size_vs_L['>2L'] += 1
            print(f"    largest terminal SCC size vs L: "
                  f"{dict(sorted(size_vs_L.items()))}")

            girths = [r[name]['lift_girth'] for r in recs
                      if r[name]['lift_girth'] is not None]
            if girths:
                print(f"    lift girth range: [{min(girths)}, {max(girths)}]  "
                      f"med={median(girths):.1f}")
                eq_L = sum(1 for r in recs
                           if r[name]['lift_girth'] == r['L'])
                print(f"    lift girth == L: {eq_L}/{len(girths)} "
                      f"({100*eq_L/len(girths):.1f}%)")

            base_proj = [r[name]['base_girth_lift_closures'] for r in recs]
            print(f"    base girth lift closures: "
                  f"{Counter(base_proj).most_common(5)}")
            have_proj = sum(1 for x in base_proj if x >= 1)
            print(f"    records where base girth cycle lifts (≥1 closure): "
                  f"{have_proj}/{len(recs)} ({100*have_proj/len(recs):.1f}%)")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'r4b_transport_lift_2026-04-19.json')
    with open(out_path, 'w') as f:
        json.dump({'records': records, 'plan': plan}, f)
    print(f"\nWrote {out_path} ({len(records)} records).", flush=True)


if __name__ == "__main__":
    main()
