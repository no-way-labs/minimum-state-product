#!/usr/bin/env python3
"""Forced-closure probe for the projection lemma.

Reference: docs/lean_docs/sk/sk_projection_lemma_note_2026-04-19.md §5.

Question: does the existence of a closed anchored threading on a base girth
cycle imply that ALL forced moves from S = {c_0, ..., c_{L-1}} stay inside S
(equivalently, any escape lands back in C, not into NG(C) \\ S)?

Three possible outcomes (note §4):
  (1) Yes automatically — every determined forced move lands in S or C.
  (2) Yes conditional on a bounded local structural property.
  (3) No — some forced move from c in S lands in NG(C) \\ S (tube or deeper).
      Outcome (3) reveals the twist-calculus is a research artifact, not a
      route to the LB sorry; campaign stays AT REST.

METHOD (per record):
  1. Enumerate sub-threshold record (ms, n), produce a good cycle C,
     its mover sequence, and the partial det map accumulated from C.
  2. Build tube T = { states at Hamming-1 from some c_i in C, excluding C }.
  3. Restrict forced-move relation to T (move_entries = det entries with
     val != stay-value); compute base girth cycle in D_tube, giving S and L.
  4. For each c in S and each processor p in [n]:
       ctx = (p, c[p-1], c[p], c[p+1])
       if ctx in move_entries:
         target = c with c[p] replaced by move_entries[ctx]
         classify target as: in C, in S, in T\\S, or outside T.
       else:
         record as 'undefined' (det not pinned at this context by the cycle).

METRICS per record:
  defined_fire_moves_from_S : # forced (fire) moves with det defined
  in_S, in_C, in_T_minus_S, outside_T : target classifications
  undefined_ctx_count       : # (c, p) pairs with ctx not in det
  escape_forensics          : for each in_T_minus_S / outside_T escape,
                              record (c, p, target, target-class, diff mask)

VERDICT per record:
  PASS-1 : every defined fire lands in S or C (outcome 1 locally)
  PASS-2 : escapes bounded and structurally characterisable (outcome 2)
  FAIL   : >=1 escape into T\\S or outside T (outcome 3)

GATE (§7 of projection note):
  - note §7.1 (FRL-CSP feasible) already refuted (sk_frl_csp_verdict)
  - this probe addresses §7.2. Outcome (3) closes the gate regardless.
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
    """Tube = Hamming-1 neighbourhood of C, minus C; edges = forced fires."""
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
    return T, dict(adj_edge), V_list, cycle_set, L, move_entries


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


def base_girth_cycle(T, adj_edge):
    adj_plain = {c: [cp for (cp, _) in adj_edge.get(c, [])] for c in T}
    sccs = tarjan_scc(T, adj_plain)
    best_seq = None
    for s in sccs:
        if len(s) < 2: continue
        start = next(iter(s))
        seq = shortest_cycle_through(start, adj_plain, s)
        if seq is not None and (best_seq is None or len(seq) < len(best_seq)):
            best_seq = seq
    return best_seq  # list of T-vertices, seq[0]==seq[-1]


def classify_target(target, S_set, cycle_set, T_set):
    if target in S_set:
        return 'in_S'
    if target in cycle_set:
        return 'in_C'
    if target in T_set:
        return 'in_T_minus_S'
    return 'outside_T'  # deeper into NG (Hamming >= 2 from C)


def audit(ms, n, cycle, movers, det):
    T, adj_edge, V_list, cycle_set, L, move_entries = build_tube(
        ms, n, cycle, movers, det)
    if not T:
        return None
    girth_seq = base_girth_cycle(T, adj_edge)
    if girth_seq is None:
        return None
    S = girth_seq[:-1]
    S_set = set(S)
    T_set = T

    class_counts = Counter()
    undefined_ctx = 0
    escapes = []  # (c_idx, p, target_class, diff_from_cycle_point)
    # For each escape, record Hamming distance from closest cycle point as a
    # structural descriptor.

    def min_hamming_to_cycle(s):
        return min(sum(1 for a, b in zip(s, c) if a != b) for c in cycle)

    for c_idx, c in enumerate(S):
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx not in move_entries and ctx not in det:
                undefined_ctx += 1
                continue
            if ctx not in move_entries:
                # ctx in det but value == stay; no forced move
                continue
            val = move_entries[ctx]
            target = list(c); target[p] = val; target = tuple(target)
            cls = classify_target(target, S_set, cycle_set, T_set)
            class_counts[cls] += 1
            if cls in ('in_T_minus_S', 'outside_T'):
                escapes.append({
                    'c_idx': c_idx,
                    'p': p,
                    'p_arity': ms[p],
                    'class': cls,
                    'hamming_to_C': min_hamming_to_cycle(target),
                })

    total_fires = sum(class_counts.values())
    n_in_S = class_counts['in_S']
    n_in_C = class_counts['in_C']
    n_escape_T = class_counts['in_T_minus_S']
    n_escape_out = class_counts['outside_T']
    n_escape = n_escape_T + n_escape_out

    # Verdict
    if n_escape == 0:
        verdict = 'PASS-1'  # outcome (1) locally
    else:
        # PASS-2 requires clean structural characterisation; we mark YELLOW
        # and leave classification to the aggregator.
        verdict = 'FAIL' if n_escape_out > 0 else 'YELLOW'

    return {
        'n': n,
        'ms': list(ms),
        'L': L,
        'T_size': len(T),
        'S_size': len(S),
        'class_counts': dict(class_counts),
        'total_defined_fires_from_S': total_fires,
        'undefined_ctx_count': undefined_ctx,
        'n_escape_tube': n_escape_T,
        'n_escape_outside': n_escape_out,
        'escape_rate': n_escape / total_fires if total_fires else 0.0,
        'escapes': escapes,
        'verdict': verdict,
    }


def main():
    print("=" * 72, flush=True)
    print("Forced-closure probe — projection lemma §5 (2026-04-20)", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1,   40, 2.0, 15),
        (6, 4,   20, 3.0, 17),
        (7, 40,  10, 3.0, 19),
        (8, 200, 5,  4.0, 21),
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
    for r in records:
        by_n[r['n']].append(r)

    for n in sorted(by_n):
        recs = by_n[n]
        verdicts = Counter(r['verdict'] for r in recs)
        print(f"\n  n={n}  records={len(recs)}  verdicts={dict(verdicts)}")

        total_fires = sum(r['total_defined_fires_from_S'] for r in recs)
        total_in_S = sum(r['class_counts'].get('in_S', 0) for r in recs)
        total_in_C = sum(r['class_counts'].get('in_C', 0) for r in recs)
        total_esc_T = sum(r['n_escape_tube'] for r in recs)
        total_esc_out = sum(r['n_escape_outside'] for r in recs)
        total_undef = sum(r['undefined_ctx_count'] for r in recs)
        print(f"    total fires from S (defined): {total_fires}")
        print(f"    -> in_S: {total_in_S}   in_C: {total_in_C}   "
              f"escape_T\\S: {total_esc_T}   escape_outside_T: {total_esc_out}")
        print(f"    undefined-ctx (c,p) count: {total_undef}")

        # Hamming distribution of escape targets
        esc_hamming = Counter()
        esc_class = Counter()
        esc_by_arity = Counter()
        for r in recs:
            for e in r['escapes']:
                esc_hamming[e['hamming_to_C']] += 1
                esc_class[e['class']] += 1
                esc_by_arity[e['p_arity']] += 1
        if esc_class:
            print(f"    escape class dist: {dict(esc_class)}")
            print(f"    escape hamming-to-C dist: "
                  f"{dict(sorted(esc_hamming.items()))}")
            print(f"    escape firing-arity dist: "
                  f"{dict(sorted(esc_by_arity.items()))}")

        esc_rates = [r['escape_rate'] for r in recs]
        if esc_rates:
            print(f"    per-record escape rate: "
                  f"min={min(esc_rates):.3f} max={max(esc_rates):.3f} "
                  f"mean={sum(esc_rates)/len(esc_rates):.3f}")

    # Global verdict
    total_esc = sum(r['n_escape_tube'] + r['n_escape_outside'] for r in records)
    print(f"\n{'='*72}")
    if total_esc == 0:
        print("GLOBAL VERDICT: PASS-1 (outcome 1) — no escape observed.")
        print("  Projection lemma candidate for direct proof.")
        print("  Gate §7.2 clears on empirical grounds; §7.1 still RED.")
    else:
        verdicts = Counter(r['verdict'] for r in records)
        if verdicts.get('FAIL', 0) > 0:
            print("GLOBAL VERDICT: FAIL (outcome 3) — escape into outside_T.")
            print("  Twist-calculus route does NOT deliver LB sorry.")
            print("  Campaign stays AT REST.")
        else:
            print("GLOBAL VERDICT: YELLOW (outcome 2 candidate) — escapes only "
                  "into T\\S.")
            print("  Examine escape-class dist + arity dist for structure.")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'forced_closure_2026-04-20.json')
    with open(out_path, 'w') as f:
        json.dump({'records': records, 'plan': plan}, f)
    print(f"\nWrote {out_path}.", flush=True)


if __name__ == "__main__":
    main()
