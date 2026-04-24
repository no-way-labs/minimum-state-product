#!/usr/bin/env python3
"""R4 gate probe — edge-sink margin on N_1(C) ∩ VC-NG tube.

Board reset (sk_board_reset_apr19.md) + primer §7.8.

GOAL
    Decide: is `|E| − (|T| − |sinks|) ≥ 1` uniform in (n, L, C, ms) at
    sub-threshold product? If yes, peel(N_1(C) ∩ VC-NG) ≠ ∅ closes by
    graph-pigeonhole; sorries #1 and #2 both fall under R4.

OBJECTS
    C        : fair simple closed good cycle on ms, movers covering all n.
    det      : det dict induced by C; move_entries = {ctx : val ≠ S} (firings).
    V_q      : set of values seen at position q across C.
    VC-NG    : value-consistent non-good = (∏_q V_q) \ C.
    T        : tube = N_1(C) ∩ VC-NG
               = { c_i[q←v] : i ∈ [L], q ∈ [n], v ∈ V_q \\ {c_i[q]}, c_i[q←v] ∉ C }
    E        : forced edges inside T. edge c → c' iff ∃ p, ctx=(p,L_p(c),c[p],R_p(c)) ∈
               move_entries and c' = c[p ← move_entries[ctx]] ∈ T.
    sinks    : { c ∈ T : no outgoing edge inside T }.
    margin   : |E| − (|T| − |sinks|).
    peel(T)  : fixpoint of "remove c with no successor in the set".

WHY margin ≥ 1 IMPLIES peel ≠ ∅
    On T' := T \\ sinks every vertex has ≥1 outgoing edge in T (possibly to
    a sink). If |E| − |T'| ≥ 1 then either (a) some v ∈ T' has out-degree
    ≥ 2, or (b) a strict directed cycle exists in G|_{T'}. In case (b)
    the cycle survives every peel step → peel ≠ ∅. In case (a) we gain
    robustness under peeling; the stronger claim we need is that the
    *subgraph restricted to non-sinks* contains a directed cycle, which
    is implied whenever the number of edges strictly inside T' exceeds
    |T'| − 1 (the forest bound on T'). We split and report BOTH margins:

    margin_total = |E|                   − (|T| − |sinks|)       (headline)
    margin_inner = |E ∩ (T'×T')|         − (|T'| − 1)            (cycle gate)

    margin_inner ≥ 1 is the graph-pigeonhole version and implies a
    directed cycle inside T' (peel ≠ ∅ by §8 primer argument).

TRIPWIRES (from §7.8, board §4 Box D)
    T1. Empirical: any record with margin_inner < 1 → R4 FAILS at Step 0.
    T2. Structural: compute "safe edges" = edges c_i[q←v] → c_{i+1}[q←v]
        where firing position p_i ∉ {q-1, q, q+1} (the shadow-style
        perturbation preserving p_i's ctx). If margin_inner is driven
        primarily by safe_edges and safe_edges themselves admit an
        analytical lower bound L × (n−3) × c_something (no per-triple det
        algebra needed), R4 route is clean. Otherwise STOP.
    T3. If a closed-form fit for margin_inner requires knowing det at
        non-cycle triples, stop — that's step-injectivity smell.

OUTPUT
    Per-record row + per-n summary (stdout); full JSON to
    sk_phase0_out/r4_edge_sink_margin_2026-04-19.json.

NOT IN SCOPE
    - Proving the inequality (this probe tests uniformity, not proof).
    - Any Lean port (gated on PASS verdict from this probe).
    - Any cycle-algebraic decomposition / Case B / step injectivity.
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict
from itertools import product as iproduct


# ----- thresholds --------------------------------------------------------

def m_n(n: int) -> int:
    """M_n sharp: 32·3^(n-4) for 5≤n≤8, 4·3^(n-2) for n≥9."""
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


# ----- multiset enumeration ----------------------------------------------

def enumerate_multisets(n: int, max_product: int):
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


# ----- cycle enumeration (seed-forced det, simple fair cycles) -----------

def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    """DFS copy of probe_sk_peel_n1_structure_2026-04-16.py cycle enumerator."""
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


# ----- tube / edges / sinks / peel ---------------------------------------

def analyze_tube(ms, n, cycle, movers, det):
    L = len(movers)
    V = [set() for _ in range(n)]
    for c in cycle:
        for q in range(n):
            V[q].add(c[q])
    V_list = [sorted(s) for s in V]
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # Tube T = N_1(C) ∩ VC-NG
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

    # Forced edges inside T
    adj = defaultdict(list)
    E_pairs = set()
    edges_by_pos = Counter()
    for c in T:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c)
                nc[p] = val
                nc = tuple(nc)
                if nc in T:
                    adj[c].append(nc)
                    if (c, nc) not in E_pairs:
                        E_pairs.add((c, nc))
                        edges_by_pos[p] += 1

    # Sinks (configs in T with no outgoing edge inside T)
    sinks = set(c for c in T if len(adj[c]) == 0)
    T_prime = T - sinks

    # Inner edges (both endpoints in T')
    inner_edges = sum(1 for (c, nc) in E_pairs if (c in T_prime and nc in T_prime))

    # Peel
    cur = set(T)
    peel_rounds = 0
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove:
            break
        cur -= to_remove
        peel_rounds += 1
    peel = cur

    # Safe edges: perturbation at q "far" from firing position p_i
    #   far-q := q ∉ {p_i-1, p_i, p_i+1} (ring distance ≥ 2)
    #   edge c_i[q←v] → c_{i+1}[q←v] inherits det entry at p_i from the
    #   cycle step itself (no off-cycle ctx required).
    safe_edges = 0
    safe_candidates = 0
    for i in range(L):
        p_i = movers[i]
        c_i = cycle[i]
        c_ip1 = cycle[(i + 1) % L]
        far_qs = [q for q in range(n)
                  if q not in {(p_i - 1) % n, p_i, (p_i + 1) % n}]
        for q in far_qs:
            for v in V_list[q]:
                if v == c_i[q]:
                    continue
                safe_candidates += 1
                src = list(c_i)
                src[q] = v
                src = tuple(src)
                dst = list(c_ip1)
                dst[q] = v
                dst = tuple(dst)
                if src in T and dst in T:
                    safe_edges += 1

    margin_total = len(E_pairs) - (len(T) - len(sinks))
    # margin_inner: edges within T' vs |T'|. Forest bound: cycle exists if
    # inner_edges ≥ |T'| (strict > |T'|−1). We report inner_edges − |T'|.
    margin_inner = inner_edges - len(T_prime)

    return {
        'n': n, 'ms': list(ms), 'L': L,
        'T': len(T),
        'E': len(E_pairs),
        'sinks': len(sinks),
        'Tprime': len(T_prime),
        'inner_edges': inner_edges,
        'peel': len(peel),
        'peel_rounds': peel_rounds,
        'peel_nonempty': len(peel) > 0,
        'margin_total': margin_total,
        'margin_inner': margin_inner,
        'safe_edges': safe_edges,
        'safe_candidates': safe_candidates,
        'edges_by_pos': dict(edges_by_pos),
        'Vsizes': [len(s) for s in V_list],
    }


# ----- driver ------------------------------------------------------------

def main():
    print("=" * 72, flush=True)
    print("R4 probe: edge-sink margin on N_1(C) ∩ VC-NG tube", flush=True)
    print("=" * 72, flush=True)

    # (n, stride, max_cycles_per_ms, time_budget_per_ms, L_max)
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
        print(f"\n=== n={n}  M_n={Mn}  multisets={len(multisets)}  "
              f"sampled={len(sampled)} ===", flush=True)
        t0 = time.time()
        rec_before = len(records)
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n:
                    continue
                r = analyze_tube(ms, n, cycle, movers, det)
                records.append(r)
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  t={time.time()-t0:.0f}s  "
                      f"records(+{len(records)-rec_before})", flush=True)

    # --- summary ---------------------------------------------------------
    print(f"\n{'='*72}\nSummary ({len(records)} records, {time.time()-t_global:.0f}s)\n{'='*72}")
    by_n = defaultdict(list)
    for r in records:
        by_n[r['n']].append(r)

    tripwire_fail = False
    for n in sorted(by_n):
        recs = by_n[n]
        Ts = [r['T'] for r in recs]
        Es = [r['E'] for r in recs]
        sinks = [r['sinks'] for r in recs]
        inner = [r['inner_edges'] for r in recs]
        Tprime = [r['Tprime'] for r in recs]
        mt = [r['margin_total'] for r in recs]
        mi = [r['margin_inner'] for r in recs]
        safes = [r['safe_edges'] for r in recs]
        peels = [r['peel'] for r in recs]
        peel_ne = sum(1 for r in recs if r['peel_nonempty'])
        Ls = [r['L'] for r in recs]

        print(f"\n  n={n}  records={len(recs)}")
        print(f"    L:            {min(Ls)}..{max(Ls)}  mean={sum(Ls)/len(Ls):.1f}")
        print(f"    |T|:          {min(Ts)}..{max(Ts)}  mean={sum(Ts)/len(Ts):.1f}")
        print(f"    |E|:          {min(Es)}..{max(Es)}  mean={sum(Es)/len(Es):.1f}")
        print(f"    |sinks|:      {min(sinks)}..{max(sinks)}  mean={sum(sinks)/len(sinks):.1f}")
        print(f"    |T'|:         {min(Tprime)}..{max(Tprime)}  mean={sum(Tprime)/len(Tprime):.1f}")
        print(f"    inner_edges:  {min(inner)}..{max(inner)}  mean={sum(inner)/len(inner):.1f}")
        print(f"    safe_edges:   {min(safes)}..{max(safes)}  mean={sum(safes)/len(safes):.1f}")
        print(f"    |peel|:       {min(peels)}..{max(peels)}  mean={sum(peels)/len(peels):.1f}")
        print(f"    margin_total: min={min(mt)}  max={max(mt)}  mean={sum(mt)/len(mt):.1f}")
        print(f"    margin_inner: min={min(mi)}  max={max(mi)}  mean={sum(mi)/len(mi):.1f}")
        print(f"    peel nonempty: {peel_ne}/{len(recs)}")

        below_inner = [r for r in recs if r['margin_inner'] < 1]
        below_total = [r for r in recs if r['margin_total'] < 1]
        empty_peel = [r for r in recs if not r['peel_nonempty']]
        if below_inner:
            print(f"    ⚠ T1 (inner): {len(below_inner)} records with margin_inner < 1")
        if below_total:
            print(f"    ⚠ T1 (total): {len(below_total)} records with margin_total < 1")
            tripwire_fail = True
        if empty_peel:
            print(f"    ⚠ EMPTY PEEL: {len(empty_peel)} records — R4 REFUTED")
            tripwire_fail = True

        sf_ratio = [(r['safe_edges'] / max(r['inner_edges'], 1)) for r in recs]
        print(f"    safe/inner:   min={min(sf_ratio):.2f}  max={max(sf_ratio):.2f}  "
              f"mean={sum(sf_ratio)/len(sf_ratio):.2f}")

        mi_over_L = [r['margin_inner'] / r['L'] for r in recs]
        print(f"    margin_inner/L: min={min(mi_over_L):.3f}  max={max(mi_over_L):.3f}  "
              f"mean={sum(mi_over_L)/len(mi_over_L):.3f}")

    print(f"\n{'='*72}")
    if tripwire_fail:
        print("VERDICT: FAIL — at least one tripwire fired. R4 does not pass Step 0.")
    else:
        all_mi = [r['margin_inner'] for r in records]
        all_mt = [r['margin_total'] for r in records]
        print("VERDICT: PROVISIONAL PASS")
        print(f"  margin_inner ≥ {min(all_mi)} uniformly over {len(records)} records.")
        print(f"  margin_total ≥ {min(all_mt)} uniformly over {len(records)} records.")
        print("  peel nonempty in every record.")
        print("  Next: check whether margin_inner/L has a clean closed form,")
        print("        and whether the derivation uses only cycle-ctx data")
        print("        (no per-triple det at non-cycle triples — T2/T3 tripwire).")
    print(f"{'='*72}")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'r4_edge_sink_margin_2026-04-19.json')
    with open(out_path, 'w') as f:
        json.dump({'records': records, 'plan': plan}, f)
    print(f"\nWrote {out_path} ({len(records)} records).", flush=True)


if __name__ == "__main__":
    main()
