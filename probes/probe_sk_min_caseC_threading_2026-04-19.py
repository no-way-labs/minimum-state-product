#!/usr/bin/env python3
"""Minimum-Case-C closed threading on base girth cycle.

Strict Case-A/B transport (0/1898 close) and same-defect slot-reanchor
(0/1898 close) are both refuted.  Case-C edges are necessary at the
GIRTH level, not just the edge level.

This probe finds — for each base girth cycle of D_tube — a closed
anchored threading under T_loose that MINIMIZES the number of
Case-C edges (edges that are neither A: p==q nor B: p==movers[i]).

The min Case-C count answers:
  * if min==0 on 100% of records, strict A/B suffices (refuted).
  * if min>0, Case C is genuinely required — how many per cycle?
  * do Case-C edges have a structural pattern (always adjacent?  always
    where |Σ(c)|>1?  always at specific defect-position transitions?)

DP METHOD
  State: (t, σ_t).  Edge cost = 0 if strict A/B, else 1.
  Forward DP over path[0..L-1] with transitions via T_loose (any
  σ_{t+1} ∈ Σ(c_{t+1})).  Closure: dp[L][σ_0].

METRICS per record
  min_case_C : minimum Case-C edge count over all closed threadings
  case_C_locations_example: positions t where Case-C is forced
  sig_multiplicity_at_Case_C_steps: |Σ(c_t)| distribution at forced-C t

NOT IN SCOPE
  - Lean
  - transport relation derivation
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict, deque
from itertools import product as iproduct
from statistics import median


# ----- shared helpers ----------------------------------------------------

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


# ----- min Case-C DP -----------------------------------------------------

def classify_edge(sigma, sigma_next, p, c_next, movers, L):
    """Return 'A', 'B', or 'C' for this anchored transition."""
    i, q, v = sigma
    i_n, q_n, v_n = sigma_next
    if p == q and i_n == i and q_n == q and v_n == c_next[p]:
        return 'A'
    if p == movers[i] and i_n == (i + 1) % L and q_n == q and v_n == v:
        return 'B'
    return 'C'


def min_case_C_closed(girth_seq, firing, sigs, cycle, movers, L):
    """
    DP: for each σ_0 ∈ Σ(c_0), compute min Case-C count for closed
    threading ending at σ_L = σ_0.  Returns min over all σ_0 (or None).
    Also track an example threading achieving the min.
    """
    if girth_seq is None: return None, None, None
    path = girth_seq[:-1]
    best_min = None
    best_thread = None
    best_caseC_mask = None

    for sigma0 in sigs[path[0]]:
        # dp[sigma] = (min_cc, backptr_sigma_at_prev_step, edge_type_in)
        dp_prev = {sigma0: (0, None, None)}
        backptr = [{sigma0: (None, None)}]  # per-step: dict sigma -> (prev_sigma, edge_type)
        for t in range(len(path)):
            c_next = path[(t + 1) % len(path)]
            p = firing[t]
            dp_new = {}
            back_new = {}
            for sigma, (cc, _, _) in dp_prev.items():
                for sigma_next in sigs[c_next]:
                    edge_type = classify_edge(sigma, sigma_next, p, c_next, movers, L)
                    new_cc = cc + (0 if edge_type != 'C' else 1)
                    if sigma_next not in dp_new or dp_new[sigma_next][0] > new_cc:
                        dp_new[sigma_next] = (new_cc, sigma, edge_type)
                        back_new[sigma_next] = (sigma, edge_type)
            dp_prev = dp_new
            backptr.append(back_new)
        # closure: sigma_L = sigma_0
        if sigma0 in dp_prev:
            cc_close, _, _ = dp_prev[sigma0]
            if best_min is None or cc_close < best_min:
                best_min = cc_close
                # Recover threading
                thread = [sigma0]
                types = []
                cur = sigma0
                for t in range(len(path), 0, -1):
                    prev_sigma, edge_t = backptr[t][cur]
                    thread.append(prev_sigma)
                    types.append(edge_t)
                    cur = prev_sigma
                thread.reverse(); types.reverse()
                best_thread = tuple(thread)
                best_caseC_mask = tuple(1 if ty == 'C' else 0 for ty in types)
    return best_min, best_thread, best_caseC_mask


def audit(ms, n, cycle, movers, det):
    T, adj_edge, V_list, cycle_set, L = build_tube(ms, n, cycle, movers, det)
    if not T: return None
    sigs = {c: all_signatures(c, cycle, n) for c in T}
    if any(len(sigs[c]) == 0 for c in T): return None

    girth_seq, firing = base_girth_cycle_with_positions(T, adj_edge)
    if girth_seq is None or any(p is None for p in firing): return None

    min_cc, thread, cc_mask = min_case_C_closed(
        girth_seq, firing, sigs, cycle, movers, L)

    # Multiplicity of signatures at forced-C steps
    sig_mult_at_C = []
    if cc_mask is not None:
        path = girth_seq[:-1]
        for t, is_c in enumerate(cc_mask):
            if is_c:
                sig_mult_at_C.append(len(sigs[path[t]]))

    # |Σ(c)| distribution across girth cycle vertices
    path = girth_seq[:-1] if girth_seq else []
    sig_mult_all = [len(sigs[c]) for c in path]

    return {
        'n': n, 'ms': list(ms), 'L': L, 'T': len(T),
        'girth': len(girth_seq) - 1 if girth_seq else None,
        'min_case_C': min_cc,
        'case_C_count_over_L': (min_cc / L) if min_cc is not None else None,
        'sig_mult_at_C_steps': sig_mult_at_C,
        'sig_mult_all_steps': sig_mult_all,
        'cc_mask': list(cc_mask) if cc_mask is not None else None,
    }


# ----- driver ------------------------------------------------------------

def main():
    print("=" * 72, flush=True)
    print("Min Case-C closed threading on base girth cycles", flush=True)
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
        closed = [r for r in recs if r['min_case_C'] is not None]
        print(f"    records with at least one closed T_loose threading: "
              f"{len(closed)}/{len(recs)}")
        if not closed: continue
        mins = [r['min_case_C'] for r in closed]
        print(f"    min Case-C count distribution: "
              f"{Counter(mins).most_common(10)}")
        print(f"    min Case-C / L ratio: "
              f"min={min(r['case_C_count_over_L'] for r in closed):.3f}  "
              f"med={median(r['case_C_count_over_L'] for r in closed):.3f}  "
              f"max={max(r['case_C_count_over_L'] for r in closed):.3f}")
        # Σ multiplicity at C steps vs all steps
        mult_at_C = [m for r in closed for m in r['sig_mult_at_C_steps']]
        mult_all = [m for r in closed for m in r['sig_mult_all_steps']]
        if mult_at_C:
            print(f"    |Σ(c)| at C-steps: "
                  f"mean={sum(mult_at_C)/len(mult_at_C):.2f}  "
                  f"dist={Counter(mult_at_C).most_common(5)}")
        print(f"    |Σ(c)| at all girth steps: "
              f"mean={sum(mult_all)/len(mult_all):.2f}  "
              f"dist={Counter(mult_all).most_common(5)}")
        zero_cc = sum(1 for m in mins if m == 0)
        print(f"    records with min_case_C == 0 (strict A/B closes): "
              f"{zero_cc}/{len(closed)} ({100*zero_cc/len(closed):.1f}%)")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'r4b_min_caseC_2026-04-19.json')
    with open(out_path, 'w') as f:
        json.dump({'records': records, 'plan': plan}, f)
    print(f"\nWrote {out_path}.", flush=True)


if __name__ == "__main__":
    main()
