#!/usr/bin/env python3
"""Anchored-threading probe for D_tube girth cycles.

BOARD RESET (2026-04-19 late-late):
  The tube carries one-defect anchored presentations, not a scalar slot
  phase.  Edge transport is defined by the physical move, not by δ alone.
  Σδ ≡ 0 mod L is a consequence of closure, not a local edge law.

DEFINITIONS
  Σ(c)    = { (i, q, v) : c agrees with cycle[i] except at position q,
                          where c[q] = v ≠ cycle[i][q] }
  anchored vertex: (c, i, q, v) with (i,q,v) ∈ Σ(c)
  anchored transport at base edge e: c → c' firing at p, σ=(i,q,v)∈Σ(c):
     Case A (defect-hit):     p == q    → σ' = (i,   q, c'[p]),   δ = 0
     Case B (canonical lift): p == M[i] → σ' = (i+1, q, v),       δ = 1
     otherwise: undefined (transport empty).

THREADING on base girth cycle (c_0, c_1, …, c_{L-1}, c_0):
  choose σ_0 ∈ Σ(c_0); at each step, apply anchored transport;
  threading SUCCEEDS iff every step is defined AND σ_L = σ_0.

METRICS per record
  |#Σ(c_0)|  : starting signature options
  n_close    : number of σ_0 that close under anchored threading
  first_fail : for each failed σ_0, the step t where transport was
               undefined (and the reason: both p ≠ q AND p ≠ M[i])
  Σδ on threadings that closed (should be 0 mod L, by design)
  distinct   : number of distinct closed threadings (as sequences)
  multiplicity: 1/2/4/... pattern

If n_close ≥ 1 for 100% of girth cycles, the strict anchored transport is
exactly right.  If fewer, we will need to relax Case C into the transport.

NOT IN SCOPE
  - segment-length > 1 transport
  - Lean
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
    # adj with firing-position record: adj_edge[c] = [(cp, p), ...]
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
    """adj_plain: dict of str→list[str] (no edge data)"""
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
    """Return a shortest directed cycle with firing positions:
       returns (cycle_verts, firing_positions) or (None, None)."""
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
    # Recover firing position for each step
    positions = []
    for t in range(len(best_seq) - 1):
        c, cp = best_seq[t], best_seq[t + 1]
        for (cpp, p) in adj_edge[c]:
            if cpp == cp:
                positions.append(p); break
        else:
            positions.append(None)
    return best_seq, positions


# ----- anchored threading ------------------------------------------------

def anchored_step(sigma, c_next, p, cycle, movers, L):
    """
    Apply one anchored transport step.
    sigma = (i, q, v) ∈ Σ(c) on base edge firing at p, producing c_next.
    Returns sigma' or None if transport undefined (p ∉ {q, movers[i]}).
    """
    i, q, v = sigma
    if p == q:
        # Case A: move hits defect.  σ' = (i, q, c_next[p])
        w = c_next[p]
        if w == cycle[i][q]:
            return None  # defect healed; leaves tube (σ' ∉ Σ(c_next) at slot i)
        return (i, q, w)
    if p == movers[i]:
        # Case B: canonical advance.  σ' = (i+1, q, v)
        return ((i + 1) % L, q, v)
    return None


def thread_cycle(girth_seq, firing, cycle, movers, L, sigs):
    """
    Try threading over the base girth cycle.
    Returns list of (sigma_0, success, fail_step, fail_reason, Sigma_delta,
                     threading_tuple).
    """
    if girth_seq is None: return []
    path = girth_seq[:-1]  # without the repeated endpoint
    out = []
    for sigma0 in sigs[path[0]]:
        sigma = sigma0
        thread = [sigma0]
        success = True
        fail_step = None
        fail_reason = None
        delta_sum = 0
        for t in range(len(path)):
            c_next = path[(t + 1) % len(path)]
            p = firing[t]
            sigma_new = anchored_step(sigma, c_next, p, cycle, movers, L)
            if sigma_new is None:
                success = False; fail_step = t
                i, q, v = sigma
                fail_reason = (f"p={p} notin {{q={q}, M[i={i}]={movers[i]}}}"
                               if p != q and p != movers[i]
                               else f"defect_healed p=q={q}")
                break
            if sigma_new not in sigs[c_next]:
                # σ' claimed but not actually in Σ(c'): surface disagreement
                success = False; fail_step = t
                fail_reason = f"sigma'={sigma_new} not in Sigma(c_next)"
                break
            delta_sum += (sigma_new[0] - sigma[0]) % L
            sigma = sigma_new
            thread.append(sigma)
        if success and sigma != sigma0:
            success = False; fail_step = len(path); fail_reason = 'did_not_close'
        out.append({
            'sigma0': sigma0, 'success': success,
            'fail_step': fail_step, 'fail_reason': fail_reason,
            'Sigma_delta_mod_L': delta_sum % L if success else None,
            'thread': tuple(thread) if success else None,
        })
    return out


def audit(ms, n, cycle, movers, det):
    T, adj_edge, V_list, cycle_set, L = build_tube(ms, n, cycle, movers, det)
    if not T: return None
    sigs = {c: all_signatures(c, cycle, n) for c in T}
    if any(len(sigs[c]) == 0 for c in T): return None

    girth_seq, firing = base_girth_cycle_with_positions(T, adj_edge)
    if girth_seq is None: return None
    if any(p is None for p in firing): return None

    threadings = thread_cycle(girth_seq, firing, cycle, movers, L, sigs)
    closed = [t for t in threadings if t['success']]
    # Deduplicate closed threadings by thread tuple (symmetry counting)
    distinct = list({t['thread'] for t in closed})

    # When threading fails: tally reason types
    reason_counts = Counter()
    first_fails = []
    for t in threadings:
        if not t['success']:
            r = t['fail_reason'] or 'unknown'
            # bucket: p-not-in-{q,M[i]}   vs   defect_healed   vs   other
            if r.startswith('p='):
                reason_counts['p_not_in_qMi'] += 1
            elif r.startswith('defect_healed'):
                reason_counts['defect_healed'] += 1
            elif r == 'did_not_close':
                reason_counts['did_not_close'] += 1
            elif r.startswith("sigma'="):
                reason_counts['sigma_prime_not_in_target'] += 1
            else:
                reason_counts['other'] += 1
            first_fails.append(t['fail_step'])

    return {
        'n': n, 'ms': list(ms), 'L': L, 'T': len(T),
        'girth': len(girth_seq) - 1,
        'n_sigma0': len(sigs[girth_seq[0]]),
        'n_threadings_tried': len(threadings),
        'n_closed': len(closed),
        'n_distinct_closed': len(distinct),
        'reason_counts': dict(reason_counts),
        'first_fails': first_fails,
        'sigma_delta_on_closed': [t['Sigma_delta_mod_L'] for t in closed],
    }


# ----- driver ------------------------------------------------------------

def main():
    print("=" * 72, flush=True)
    print("Anchored-threading probe on base girth cycles of D_tube", flush=True)
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

    overall_closed = 0
    overall = 0
    for n in sorted(by_n):
        recs = by_n[n]
        print(f"\n  n={n}  records={len(recs)}")
        closed = [r for r in recs if r['n_closed'] >= 1]
        n_closed_dist = Counter(r['n_closed'] for r in recs)
        n_distinct_dist = Counter(r['n_distinct_closed'] for r in recs)
        print(f"    records with ≥1 closed anchored threading: "
              f"{len(closed)}/{len(recs)} ({100*len(closed)/len(recs):.1f}%)")
        print(f"    n_closed distribution: {dict(sorted(n_closed_dist.items()))}")
        print(f"    n_distinct_closed distribution: "
              f"{dict(sorted(n_distinct_dist.items()))}")

        # Reason-for-failure aggregate
        reason_total = Counter()
        for r in recs:
            for k, v in r['reason_counts'].items():
                reason_total[k] += v
        print(f"    failure reasons (summed across all σ_0 attempts): "
              f"{dict(reason_total)}")

        # Sigma_delta on closed threadings
        sd_dist = Counter()
        for r in recs:
            for sd in r['sigma_delta_on_closed']:
                sd_dist[sd] += 1
        print(f"    Σδ mod L on closed threadings: {dict(sorted(sd_dist.items()))}")

        overall_closed += len(closed); overall += len(recs)

    print(f"\n  OVERALL: closed on {overall_closed}/{overall} "
          f"({100*overall_closed/overall:.1f}%)")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'r4b_anchored_threading_2026-04-19.json')
    with open(out_path, 'w') as f:
        json.dump({'records': records, 'plan': plan}, f)
    print(f"\nWrote {out_path}.", flush=True)


if __name__ == "__main__":
    main()
