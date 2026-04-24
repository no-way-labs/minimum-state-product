#!/usr/bin/env python3
"""Anchored-threading with same-defect slot re-anchoring.

Strict Case-A/B transport (0/1898 close) is refuted.
Failure pattern was uniformly p ∉ {q, M[i]}, i.e. the move lands away
from both the current defect and the canonical mover at slot i.

Relaxation: at each vertex, allow re-anchoring
    σ = (i, q, v)   →   σ'' = (i'', q, v)   with (i'', q, v) ∈ Σ(c)
i.e., keep the SAME defect (q, v) but shift the anchoring slot.

Transport then:
    (σ, σ') ∈ T_e iff ∃ i'' with (i'', σ.q, σ.v) ∈ Σ(c_t)
    AND p ∈ {σ.q, movers[i'']}
    AND σ' = strict_step((i'', σ.q, σ.v), e_t)

Threading SUCCEEDS iff every step is defined AND σ_L = σ_0 after closure.

METRICS per record
  closed / not closed
  number of distinct closed threadings
  slot-drift: for each closed threading, track the cumulative shift
    σ_t.i relative to σ_0.i (Σδ now means slot-advance, not just +1)
  re-anchor count along threading: how often slot was shifted

NOT IN SCOPE
  - Case C as different-defect transitions
  - segment transport with length > 1
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict, deque
from itertools import product as iproduct
from statistics import median


# ----- shared helpers (identical to previous probes) ---------------------

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


# ----- relaxed anchored transport ----------------------------------------

def same_defect_alternates(sigma, sigs_c):
    """All σ'' = (i'', q, v) ∈ Σ(c) with same (q, v) as sigma."""
    i, q, v = sigma
    return [s for s in sigs_c if s[1] == q and s[2] == v]


def strict_step(sigma, c_next, p, cycle, movers, L):
    """One strict Case-A/B step, or None if p ∉ {q, M[i]} or defect heals."""
    i, q, v = sigma
    if p == q:
        w = c_next[p]
        if w == cycle[i][q]:
            return None
        return (i, q, w)
    if p == movers[i]:
        return ((i + 1) % L, q, v)
    return None


def thread_with_reanchor(girth_seq, firing, cycle, movers, L, sigs):
    """
    DFS over threadings with same-defect slot re-anchoring permitted.
    Returns list of closed threadings (each a tuple of σ_t sequence).
    Bounded DFS to cap search cost: each vertex's re-anchoring branches
    are at most |same-defect alternates| ≤ L.
    """
    if girth_seq is None: return []
    path = girth_seq[:-1]
    closed = []
    visited_per_start = {}

    for sigma0 in sigs[path[0]]:
        # DFS bounded by state (t, sigma)
        seen = set()
        stack = [(0, sigma0, (sigma0,))]
        while stack:
            t, sigma, thread = stack.pop()
            state_key = (t, sigma)
            if state_key in seen: continue
            seen.add(state_key)
            if t == len(path):
                if sigma == sigma0:
                    closed.append(thread)
                continue
            c_t = path[t]
            c_next = path[(t + 1) % len(path)]
            p = firing[t]
            # Try strict step from current sigma OR any same-defect reanchor at c_t
            alts = [sigma] + [s for s in same_defect_alternates(sigma, sigs[c_t]) if s != sigma]
            for alt in alts:
                sigma_new = strict_step(alt, c_next, p, cycle, movers, L)
                if sigma_new is None: continue
                if sigma_new not in sigs[c_next]: continue
                stack.append((t + 1, sigma_new, thread + (sigma_new,)))
                # Also try re-anchoring at c_next (propagating defect unchanged)
                for alt2 in same_defect_alternates(sigma_new, sigs[c_next]):
                    if alt2 != sigma_new:
                        stack.append((t + 1, alt2, thread + (alt2,)))

    return closed


def audit(ms, n, cycle, movers, det):
    T, adj_edge, V_list, cycle_set, L = build_tube(ms, n, cycle, movers, det)
    if not T: return None
    sigs = {c: all_signatures(c, cycle, n) for c in T}
    if any(len(sigs[c]) == 0 for c in T): return None

    girth_seq, firing = base_girth_cycle_with_positions(T, adj_edge)
    if girth_seq is None: return None
    if any(p is None for p in firing): return None

    closed = thread_with_reanchor(girth_seq, firing, cycle, movers, L, sigs)
    distinct_threads = set(closed)

    # Per-closed-threading: total slot drift Σδ, case-type counts, reanchor count
    Sdelta = []
    case_seqs = []
    for thread in distinct_threads:
        # Count δ = (i_{t+1} - i_t) mod L along the thread
        s = 0
        for t in range(len(thread) - 1):
            s = (s + (thread[t + 1][0] - thread[t][0])) % L
        Sdelta.append(s)

    return {
        'n': n, 'ms': list(ms), 'L': L, 'T': len(T),
        'girth': len(girth_seq) - 1,
        'n_sigma0_choices': len(sigs[girth_seq[0]]),
        'n_closed_threadings': len(closed),
        'n_distinct_threadings': len(distinct_threads),
        'Sigma_delta_distinct': Counter(Sdelta),
    }


# ----- driver ------------------------------------------------------------

def main():
    print("=" * 72, flush=True)
    print("Anchored-threading with slot re-anchoring", flush=True)
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

    overall_closed = 0; overall = 0
    for n in sorted(by_n):
        recs = by_n[n]
        print(f"\n  n={n}  records={len(recs)}")
        closed = [r for r in recs if r['n_distinct_threadings'] >= 1]
        nd = [r['n_distinct_threadings'] for r in recs]
        print(f"    records with ≥1 closed anchored threading: "
              f"{len(closed)}/{len(recs)} ({100*len(closed)/len(recs):.1f}%)")
        print(f"    n_distinct_threadings dist: "
              f"{dict(sorted(Counter(nd).items())) if len(nd) < 20 else Counter(nd).most_common(10)}")
        sd_agg = Counter()
        for r in recs:
            for sd, cnt in r['Sigma_delta_distinct'].items():
                sd_agg[sd] += cnt
        print(f"    Σδ over distinct closed threadings: "
              f"{dict(sorted(sd_agg.items()))}")
        overall_closed += len(closed); overall += len(recs)

    print(f"\n  OVERALL: closed on {overall_closed}/{overall} "
          f"({100*overall_closed/overall:.1f}%)")

    # Save without records[*].Sigma_delta_distinct (Counter not JSON-safe)
    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'r4b_anchored_reanchor_2026-04-19.json')
    safe = []
    for r in records:
        r2 = dict(r)
        r2['Sigma_delta_distinct'] = dict(r['Sigma_delta_distinct'])
        safe.append(r2)
    with open(out_path, 'w') as f:
        json.dump({'records': safe, 'plan': plan}, f)
    print(f"\nWrote {out_path}.", flush=True)


if __name__ == "__main__":
    main()
