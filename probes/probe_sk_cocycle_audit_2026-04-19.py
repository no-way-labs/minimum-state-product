#!/usr/bin/env python3
"""R4b cocycle audit — edge increment distribution on D_tube.

Keston's consistency check (2026-04-19 late-late):
    If every tube edge has π-increment δ ∈ {0, 1} (my earlier Case A/B
    dichotomy), then on any L-cycle the sum Σδ_t ≡ 0 (mod L) with L
    summands from {0, 1} forces Σ ∈ {0, L}:
      Σ = 0 → all δ = 0 (never advances i)
      Σ = L → all δ = 1 (pure shadow)
    Empirically NEITHER holds (has_full_shadow = 0%, but cycles are not
    trapped at a single i).  So one of:
      (a) vertex signatures are multi-valued — same config has multiple
          valid (i, q, v), rescuing the dichotomy via re-indexing,
      (b) the edge law is broader than {0, 1},
      (c) signature threading along an L-cycle requires choosing a
          specific branch out of a multi-valued set.

This probe audits the cocycle BEFORE any theorem formalization.

METRICS (per record):
    signature multiplicity
        |Σ(c)| distribution over T — how many distinct (i, q, v) each
        tube vertex admits.
    edge increment set
        for every (c, c') ∈ E, the set Δ(c, c') := { (i' − i) mod L :
        (i, q, v) ∈ Σ(c), (i', q', v') ∈ Σ(c') }. Distribution of |Δ| and
        of min(Δ), max(Δ) across all edges.
    girth-cycle cocycle
        for one girth cycle per record: the sequence of Δ sets along the
        cycle. Σ (min selection) mod L. Also threaded: does there exist a
        consistent signature choice such that all δ_t = 1?
    Case classification
        for each edge (c, c'), classify by the canonical shadow relation:
        - case_A: ∃ (i, q, v) ∈ Σ(c), (i, q, v') ∈ Σ(c') same (i, q) — "slot stays"
        - case_B: ∃ (i, q, v) ∈ Σ(c), (i+1, q, v) ∈ Σ(c') — "shadow advance"
        - case_C: neither — something else (far-q broken, or anchor jump)

OUTPUT
    stdout per-n summary + sk_phase0_out/r4b_cocycle_audit_2026-04-19.json.

NOT IN SCOPE
    - proving the edge law
    - Lean work
    - any further reframing before the empirical verdict is in
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict, deque
from itertools import product as iproduct


# ----- shared helpers (duplicated from cycle-mining probe) ---------------

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


def all_signatures(c, cycle, n):
    sigs = []
    for i, ci in enumerate(cycle):
        diffs = [q for q in range(n) if ci[q] != c[q]]
        if len(diffs) == 1:
            q = diffs[0]; v = c[q]
            sigs.append((i, q, v))
    return sigs


# ----- audit -------------------------------------------------------------

def audit(ms, n, cycle, movers, det):
    T, adj, V_list, cycle_set, L = build_tube(ms, n, cycle, movers, det)
    if not T: return None
    sigs = {c: all_signatures(c, cycle, n) for c in T}
    sig_card = Counter(len(s) for s in sigs.values())

    # Edge cocycle audit
    edge_delta_multi = Counter()  # tuple(sorted(Δ)) → count
    edge_has_0 = 0; edge_has_1 = 0; edge_has_other = 0
    case_A = 0; case_B = 0; case_C = 0
    total_edges = 0
    for c, succs in adj.items():
        for cp in succs:
            total_edges += 1
            possible = set()
            for (i, q, v) in sigs[c]:
                for (ip, qp, vp) in sigs[cp]:
                    possible.add((ip - i) % L)
            key = tuple(sorted(possible))
            edge_delta_multi[key] += 1
            if 0 in possible: edge_has_0 += 1
            if 1 in possible: edge_has_1 += 1
            if any(d not in (0, 1) for d in possible): edge_has_other += 1
            # Case classification (shadow-relation)
            is_A = any((i, q, v) in sigs[c] and (i, q, vp) in sigs[cp]
                       for (i, q, v) in sigs[c]
                       for (_, _, vp) in [(ip2, qp2, vp2)
                                          for (ip2, qp2, vp2) in sigs[cp]
                                          if ip2 == i and qp2 == q])
            # Simpler restatement:
            is_A = any(ip == i and qp == q
                       for (i, q, v) in sigs[c]
                       for (ip, qp, vp) in sigs[cp])
            is_B = any((ip == (i + 1) % L) and qp == q and vp == v
                       for (i, q, v) in sigs[c]
                       for (ip, qp, vp) in sigs[cp])
            if is_B:    case_B += 1
            elif is_A:  case_A += 1
            else:       case_C += 1

    # Girth cycle cocycle
    sccs = tarjan_scc(T, adj)
    non_triv = [s for s in sccs if len(s) >= 2]
    girth = None; girth_seq = None
    for s in non_triv:
        start = next(iter(s))
        seq = shortest_cycle_through(start, adj, s)
        if seq is not None:
            g = len(seq) - 1  # seq has start at both ends
            if girth is None or g < girth:
                girth = g; girth_seq = seq
    girth_deltas = []
    girth_cases = []
    if girth_seq is not None:
        for t in range(len(girth_seq) - 1):
            c, cp = girth_seq[t], girth_seq[t + 1]
            poss = set()
            for (i, q, v) in sigs[c]:
                for (ip, qp, vp) in sigs[cp]:
                    poss.add((ip - i) % L)
            girth_deltas.append(sorted(poss))
            is_B = any((ip == (i + 1) % L) and qp == q and vp == v
                       for (i, q, v) in sigs[c]
                       for (ip, qp, vp) in sigs[cp])
            is_A = any(ip == i and qp == q
                       for (i, q, v) in sigs[c]
                       for (ip, qp, vp) in sigs[cp])
            girth_cases.append('B' if is_B else 'A' if is_A else 'C')

    # Threaded check: can we pick a signature per girth vertex such that
    # each δ_t = 1 and Σ = L?
    threaded_all_one = False
    if girth_seq is not None:
        g = len(girth_seq) - 1
        for start_sig in sigs[girth_seq[0]]:
            cur = start_sig; ok = True
            for t in range(g):
                c_next = girth_seq[t + 1]
                want_i = (cur[0] + 1) % L
                match = [s for s in sigs[c_next] if s[0] == want_i]
                if not match: ok = False; break
                cur = match[0]
            if ok and cur == start_sig:
                threaded_all_one = True; break

    # Σδ along girth cycle under LEX-MIN signature choice
    sigma_lexmin = None
    if girth_seq is not None:
        g = len(girth_seq) - 1
        total = 0
        for t in range(g):
            c, cp = girth_seq[t], girth_seq[t + 1]
            i = min(sigs[c])[0]; ip = min(sigs[cp])[0]
            total = (total + (ip - i)) % L
        sigma_lexmin = total

    return {
        'n': n, 'ms': list(ms), 'L': L,
        'T': len(T),
        'total_edges': total_edges,
        'sig_card_dist': dict(sig_card),
        'edge_delta_multi_top': edge_delta_multi.most_common(5),
        'edge_has_0': edge_has_0,
        'edge_has_1': edge_has_1,
        'edge_has_other': edge_has_other,
        'case_A': case_A, 'case_B': case_B, 'case_C': case_C,
        'girth': girth,
        'girth_deltas': girth_deltas,
        'girth_cases': girth_cases,
        'girth_cases_summary': Counter(girth_cases) if girth_cases else {},
        'threaded_all_one': threaded_all_one,
        'sigma_lexmin_mod_L': sigma_lexmin,
    }


# ----- driver ------------------------------------------------------------

def main():
    print("=" * 72, flush=True)
    print("R4b cocycle audit on D_tube", flush=True)
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

        # signature cardinality
        merged_sig = Counter()
        for r in recs:
            for k, v in r['sig_card_dist'].items():
                merged_sig[k] += v
        print(f"    |Σ(c)| over all tube vertices: {dict(sorted(merged_sig.items()))}")

        total_edges = sum(r['total_edges'] for r in recs)
        e_has_0 = sum(r['edge_has_0'] for r in recs)
        e_has_1 = sum(r['edge_has_1'] for r in recs)
        e_has_other = sum(r['edge_has_other'] for r in recs)
        print(f"    edges total: {total_edges}")
        print(f"      has 0 ∈ Δ:     {e_has_0}  ({100*e_has_0/max(total_edges,1):.1f}%)")
        print(f"      has 1 ∈ Δ:     {e_has_1}  ({100*e_has_1/max(total_edges,1):.1f}%)")
        print(f"      has d∉{{0,1}}:  {e_has_other}  ({100*e_has_other/max(total_edges,1):.1f}%)")

        cA = sum(r['case_A'] for r in recs)
        cB = sum(r['case_B'] for r in recs)
        cC = sum(r['case_C'] for r in recs)
        print(f"    case A (slot stay):     {cA}  ({100*cA/max(total_edges,1):.1f}%)")
        print(f"    case B (shadow advance):{cB}  ({100*cB/max(total_edges,1):.1f}%)")
        print(f"    case C (neither):       {cC}  ({100*cC/max(total_edges,1):.1f}%)")

        # girth cocycle
        threaded = sum(1 for r in recs if r['threaded_all_one'])
        print(f"    girth cycles with threaded-all-δ=1 choice: "
              f"{threaded}/{len(recs)} ({100*threaded/len(recs):.1f}%)")
        sigma_dist = Counter(r['sigma_lexmin_mod_L'] for r in recs
                             if r['sigma_lexmin_mod_L'] is not None)
        print(f"    Σδ (mod L) lex-min:  {dict(sorted(sigma_dist.items()))}")

        # girth case summaries (aggregated across records)
        total_girth_edges = 0
        gcA = gcB = gcC = 0
        for r in recs:
            gcs = r.get('girth_cases', [])
            total_girth_edges += len(gcs)
            gcA += sum(1 for c in gcs if c == 'A')
            gcB += sum(1 for c in gcs if c == 'B')
            gcC += sum(1 for c in gcs if c == 'C')
        if total_girth_edges > 0:
            print(f"    girth-edge cases: A={gcA} ({100*gcA/total_girth_edges:.1f}%)  "
                  f"B={gcB} ({100*gcB/total_girth_edges:.1f}%)  "
                  f"C={gcC} ({100*gcC/total_girth_edges:.1f}%)")

        # Top Δ patterns across all edges
        delta_patterns = Counter()
        for r in recs:
            for key, cnt in r['edge_delta_multi_top']:
                delta_patterns[key] += cnt
        print(f"    top Δ patterns: {delta_patterns.most_common(5)}")

    # Save one detailed record per n for inspection
    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'r4b_cocycle_audit_2026-04-19.json')
    with open(out_path, 'w') as f:
        safe = []
        for r in records:
            r2 = dict(r)
            r2['edge_delta_multi_top'] = [[list(k), v] for k, v in r2['edge_delta_multi_top']]
            r2['girth_cases_summary'] = dict(r2['girth_cases_summary'])
            safe.append(r2)
        json.dump({'records': safe, 'plan': plan}, f)
    print(f"\nWrote {out_path} ({len(records)} records).", flush=True)


if __name__ == "__main__":
    main()
