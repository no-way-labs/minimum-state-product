#!/usr/bin/env python3
"""E16 — SCC structure of forced-NG subgraph on T_N1 = N_1(C) ∩ VC-NG.

Purpose
    Decide whether route R4 (peel-direct) admits a non-walk Lean-portable
    proof via the SCC structure. Specifically:

      (Q1) Does EVERY record have ≥ 1 non-trivial terminal SCC in the
           forced-NG subgraph on T_N1?
      (Q2) Is the peel fixpoint EXACTLY the union of non-trivial
           terminal SCCs? (Should be by definition of peel.)
      (Q3) What is the minimum non-trivial terminal SCC size?

    If (Q1)+(Q2) both hold and (Q3) gives a useful uniform bound, we have
    a candidate Lean-portable existence claim:
        "construct SCC DAG of forced-NG on T_N1; show ≥1 terminal SCC has
         size ≥ 2."

Infrastructure reused from probe_sk_edge_sink_margin_2026-04-19.py:
    - m_n, enumerate_multisets, enumerate_all_cycles
    - Tube construction (T = N_1(C) ∩ VC-NG) and forced-NG successor.

New logic
    - Tarjan's SCC algorithm (inline, iterative to avoid recursion depth).
    - Terminal-SCC detection in the SCC-DAG.
    - Peel fixpoint (reused) for cross-check.

Output
    - Per-record / per-n stdout summary.
    - JSON dump to sk_phase0_out/e16_scc_structure_2026-04-20.json.
    - Final GREEN / YELLOW / RED verdict.
"""
from __future__ import annotations

import json
import os
import sys
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


# ----- cycle enumeration (copy of edge-sink probe) -----------------------

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


# ----- Tarjan SCC (iterative) --------------------------------------------

def tarjan_scc(nodes, adj):
    """Iterative Tarjan. Returns list of SCCs, each a list of nodes.

    adj : dict node -> iterable of successor nodes (only successors that
          are themselves in `nodes` are traversed).
    """
    index_of = {}
    lowlink = {}
    on_stack = {}
    stack = []
    sccs = []
    idx_counter = [0]
    node_set = set(nodes)

    # iterative DFS: work stack entries are (v, iterator over successors)
    def strongconnect(v_start):
        work = [(v_start, iter(adj.get(v_start, ())))]
        index_of[v_start] = idx_counter[0]
        lowlink[v_start] = idx_counter[0]
        idx_counter[0] += 1
        stack.append(v_start)
        on_stack[v_start] = True

        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in node_set:
                    continue
                if w not in index_of:
                    index_of[w] = idx_counter[0]
                    lowlink[w] = idx_counter[0]
                    idx_counter[0] += 1
                    stack.append(w)
                    on_stack[w] = True
                    work.append((w, iter(adj.get(w, ()))))
                    advanced = True
                    break
                elif on_stack.get(w, False):
                    if index_of[w] < lowlink[v]:
                        lowlink[v] = index_of[w]
            if advanced:
                continue
            # finished exploring v
            work.pop()
            if lowlink[v] == index_of[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack[w] = False
                    comp.append(w)
                    if w == v:
                        break
                sccs.append(comp)
            if work:
                parent = work[-1][0]
                if lowlink[v] < lowlink[parent]:
                    lowlink[parent] = lowlink[v]

    for v in nodes:
        if v not in index_of:
            strongconnect(v)
    return sccs


# ----- analyze: tube + forced edges + SCCs + peel ------------------------

def analyze_record(ms, n, cycle, movers, det):
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

    # Forced-NG successor edges inside T
    adj = defaultdict(list)
    E_pairs = set()
    for c in T:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c)
                nc[p] = val
                nc = tuple(nc)
                if nc in T:
                    if (c, nc) not in E_pairs:
                        E_pairs.add((c, nc))
                        adj[c].append(nc)

    # --- peel fixpoint (cross-check) -------------------------------------
    cur = set(T)
    peel_rounds = 0
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove:
            break
        cur -= to_remove
        peel_rounds += 1
    peel = cur

    # --- Tarjan SCCs -----------------------------------------------------
    nodes = list(T)
    sccs = tarjan_scc(nodes, adj)

    # Node -> scc index
    scc_of = {}
    for i, comp in enumerate(sccs):
        for v in comp:
            scc_of[v] = i

    # SCC-DAG edges: scc_i -> scc_j for i != j
    scc_out = defaultdict(set)
    for u in adj:
        if u not in scc_of:
            continue
        i = scc_of[u]
        for v in adj[u]:
            if v not in scc_of:
                continue
            j = scc_of[v]
            if i != j:
                scc_out[i].add(j)

    num_sccs = len(sccs)
    scc_sizes = [len(c) for c in sccs]

    # A SCC is "non-trivial" if size ≥ 2 OR has a self-loop.
    # Here forced successor ≠ current (different config), so self-loops
    # cannot occur (verified by the size-1 branch below).
    nontrivial_idx = set()
    for i, comp in enumerate(sccs):
        if len(comp) >= 2:
            nontrivial_idx.add(i)
        else:
            # size-1: check self-loop
            v = comp[0]
            if v in adj and v in adj[v]:
                nontrivial_idx.add(i)

    # Terminal SCCs: no outgoing SCC-DAG edge
    terminal_idx = [i for i in range(num_sccs) if len(scc_out[i]) == 0]
    num_terminal = len(terminal_idx)
    num_nontrivial_terminal = sum(1 for i in terminal_idx if i in nontrivial_idx)
    terminal_sizes = sorted(scc_sizes[i] for i in terminal_idx)
    nontrivial_terminal_sizes = sorted(
        scc_sizes[i] for i in terminal_idx if i in nontrivial_idx)

    # Union of non-trivial terminal SCCs
    ntt_union = set()
    for i in terminal_idx:
        if i in nontrivial_idx:
            for v in sccs[i]:
                ntt_union.add(v)

    peel_equals_ntt = (peel == ntt_union)

    # Union of ALL non-trivial SCCs (these ALWAYS survive peel since
    # every vertex has an in-SCC successor). This is the cleaner object.
    nt_union = set()
    for i in nontrivial_idx:
        for v in sccs[i]:
            nt_union.add(v)
    # Check: peel ⊇ nt_union (should hold)
    peel_superset_nt = nt_union.issubset(peel)

    largest_scc_size = max(scc_sizes) if scc_sizes else 0
    num_nontrivial_sccs = len(nontrivial_idx)
    min_nontrivial_scc_size = (
        min(scc_sizes[i] for i in nontrivial_idx)
        if nontrivial_idx else 0)

    return {
        'n': n, 'ms': list(ms), 'L': L,
        'T': len(T),
        'E': len(E_pairs),
        'peel_size': len(peel),
        'peel_nonempty': len(peel) > 0,
        'peel_rounds': peel_rounds,
        'num_sccs': num_sccs,
        'num_nontrivial_sccs': num_nontrivial_sccs,
        'min_nontrivial_scc_size': min_nontrivial_scc_size,
        'largest_scc_size': largest_scc_size,
        'num_terminal_sccs': num_terminal,
        'num_nontrivial_terminal_sccs': num_nontrivial_terminal,
        'terminal_scc_sizes': terminal_sizes,
        'nontrivial_terminal_scc_sizes': nontrivial_terminal_sizes,
        'peel_equals_union_of_nontrivial_terminal_sccs': peel_equals_ntt,
        'peel_superset_of_all_nontrivial_sccs': peel_superset_nt,
        'ntt_union_size': len(ntt_union),
        'nt_union_size': len(nt_union),
    }


# ----- driver ------------------------------------------------------------

def main():
    print("=" * 72, flush=True)
    print("E16 probe: SCC structure of forced-NG subgraph on T_N1", flush=True)
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
                r = analyze_record(ms, n, cycle, movers, det)
                records.append(r)
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  t={time.time()-t0:.0f}s  "
                      f"records(+{len(records)-rec_before})", flush=True)

    # --- summary ---------------------------------------------------------
    print(f"\n{'='*72}\nSummary ({len(records)} records, "
          f"{time.time()-t_global:.0f}s)\n{'='*72}")

    by_n = defaultdict(list)
    for r in records:
        by_n[r['n']].append(r)

    agg = {}
    any_no_ntt = False
    any_no_nt = False  # no non-trivial SCC at all
    any_peel_mismatch = False
    any_peel_supset_violation = False
    global_min_ntt_size = None
    global_max_ntt_size = None
    global_min_nt_size = None
    global_max_nt_size = None
    global_min_num_nt = None

    for n in sorted(by_n):
        recs = by_n[n]
        n_recs = len(recs)

        has_ntt = [r for r in recs if r['num_nontrivial_terminal_sccs'] >= 1]
        no_ntt = [r for r in recs if r['num_nontrivial_terminal_sccs'] == 0]
        has_nt = [r for r in recs if r['num_nontrivial_sccs'] >= 1]
        no_nt = [r for r in recs if r['num_nontrivial_sccs'] == 0]
        peel_match = [r for r in recs
                      if r['peel_equals_union_of_nontrivial_terminal_sccs']]
        peel_mismatch = [r for r in recs
                         if not r['peel_equals_union_of_nontrivial_terminal_sccs']]
        peel_supset_ok = [r for r in recs
                          if r['peel_superset_of_all_nontrivial_sccs']]
        peel_supset_bad = [r for r in recs
                           if not r['peel_superset_of_all_nontrivial_sccs']]
        empty_peel = [r for r in recs if not r['peel_nonempty']]

        # min non-trivial terminal SCC size, aggregated over all recs that have one
        ntt_sizes_all = []
        for r in recs:
            ntt_sizes_all.extend(r['nontrivial_terminal_scc_sizes'])
        min_ntt = min(ntt_sizes_all) if ntt_sizes_all else None
        max_ntt = max(ntt_sizes_all) if ntt_sizes_all else None

        # min non-trivial SCC size (per record) and num-nontrivial-SCCs
        min_nt_sizes = [r['min_nontrivial_scc_size'] for r in recs
                        if r['num_nontrivial_sccs'] >= 1]
        min_nt = min(min_nt_sizes) if min_nt_sizes else None
        max_nt = (max(r['largest_scc_size'] for r in recs
                      if r['num_nontrivial_sccs'] >= 1)
                  if has_nt else None)
        num_nt_list = [r['num_nontrivial_sccs'] for r in recs]

        num_sccs_list = [r['num_sccs'] for r in recs]
        num_term_list = [r['num_terminal_sccs'] for r in recs]
        num_ntterm_list = [r['num_nontrivial_terminal_sccs'] for r in recs]
        largest_list = [r['largest_scc_size'] for r in recs]
        Ts = [r['T'] for r in recs]
        peels = [r['peel_size'] for r in recs]

        print(f"\n  n={n}  records={n_recs}")
        print(f"    |T|:                {min(Ts)}..{max(Ts)}  mean={sum(Ts)/n_recs:.1f}")
        print(f"    |peel|:             {min(peels)}..{max(peels)}  mean={sum(peels)/n_recs:.1f}")
        print(f"    empty peel:         {len(empty_peel)}/{n_recs}")
        print(f"    num_sccs:           {min(num_sccs_list)}..{max(num_sccs_list)}  "
              f"mean={sum(num_sccs_list)/n_recs:.1f}")
        print(f"    num_terminal_sccs:  {min(num_term_list)}..{max(num_term_list)}  "
              f"mean={sum(num_term_list)/n_recs:.1f}")
        print(f"    num_nontriv_term:   {min(num_ntterm_list)}..{max(num_ntterm_list)}  "
              f"mean={sum(num_ntterm_list)/n_recs:.2f}")
        print(f"    largest_scc_size:   {min(largest_list)}..{max(largest_list)}  "
              f"mean={sum(largest_list)/n_recs:.1f}")
        if ntt_sizes_all:
            print(f"    nontriv-term size:  min={min_ntt}  max={max_ntt}  "
                  f"(over {len(ntt_sizes_all)} ntt SCCs total)")
        print(f"    has ≥1 nontriv-term: {len(has_ntt)}/{n_recs}")
        print(f"    peel = ∪(ntt-term):  {len(peel_match)}/{n_recs}")
        print(f"    has ≥1 nontriv-SCC:  {len(has_nt)}/{n_recs}")
        print(f"    num_nontriv_sccs:   {min(num_nt_list)}..{max(num_nt_list)}  "
              f"mean={sum(num_nt_list)/n_recs:.2f}")
        if min_nt is not None:
            print(f"    nontriv-SCC size:   min={min_nt}  max={max_nt}")
        print(f"    peel ⊇ ∪(nt-SCC):    {len(peel_supset_ok)}/{n_recs}")

        if no_ntt:
            print(f"    note: {len(no_ntt)} record(s) with NO non-trivial "
                  f"terminal SCC (but may have non-terminal nontrivial SCC)")
            any_no_ntt = True
        if no_nt:
            print(f"    ⚠ {len(no_nt)} record(s) with NO non-trivial SCC AT ALL")
            any_no_nt = True
        if peel_mismatch:
            print(f"    note: {len(peel_mismatch)} record(s) with peel ≠ "
                  f"∪(ntt-term) (expected — non-terminal nt SCCs survive peel)")
            any_peel_mismatch = True
        if peel_supset_bad:
            print(f"    ⚠ {len(peel_supset_bad)} record(s) with peel ⊉ ∪(nt-SCC)")
            any_peel_supset_violation = True

        agg[n] = {
            'records': n_recs,
            'has_ntt': len(has_ntt),
            'no_ntt': len(no_ntt),
            'has_nt': len(has_nt),
            'no_nt': len(no_nt),
            'peel_match': len(peel_match),
            'peel_mismatch': len(peel_mismatch),
            'peel_supset_ok': len(peel_supset_ok),
            'peel_supset_bad': len(peel_supset_bad),
            'empty_peel': len(empty_peel),
            'min_ntt_size': min_ntt,
            'max_ntt_size': max_ntt,
            'min_nt_size': min_nt,
            'max_nt_size': max_nt,
            'num_nt_min': min(num_nt_list),
            'num_nt_max': max(num_nt_list),
            'num_sccs_min': min(num_sccs_list),
            'num_sccs_max': max(num_sccs_list),
            'largest_scc_min': min(largest_list),
            'largest_scc_max': max(largest_list),
        }

        if min_ntt is not None:
            if global_min_ntt_size is None or min_ntt < global_min_ntt_size:
                global_min_ntt_size = min_ntt
        if max_ntt is not None:
            if global_max_ntt_size is None or max_ntt > global_max_ntt_size:
                global_max_ntt_size = max_ntt
        if min_nt is not None:
            if global_min_nt_size is None or min_nt < global_min_nt_size:
                global_min_nt_size = min_nt
        if max_nt is not None:
            if global_max_nt_size is None or max_nt > global_max_nt_size:
                global_max_nt_size = max_nt
        this_num_nt_min = min(num_nt_list) if num_nt_list else 0
        if global_min_num_nt is None or this_num_nt_min < global_min_num_nt:
            global_min_num_nt = this_num_nt_min

    # --- verdict ---------------------------------------------------------
    print(f"\n{'='*72}")
    print("VERDICT")
    print(f"{'='*72}")

    total = len(records)
    all_have_ntt = not any_no_ntt
    all_have_nt = not any_no_nt
    all_peel_match = not any_peel_mismatch
    all_peel_supset = not any_peel_supset_violation

    # --- Track A: terminal SCC (original proposal) -----------------------
    print("TRACK A — 'non-trivial terminal SCC' (original proposal):")
    total_no_ntt = sum(agg[k]['no_ntt'] for k in agg)
    total_peel_mismatch = sum(agg[k]['peel_mismatch'] for k in agg)
    print(f"  records with ≥1 non-trivial terminal SCC: "
          f"{total - total_no_ntt}/{total}")
    print(f"  peel = ∪(non-trivial terminal SCC): "
          f"{total - total_peel_mismatch}/{total}")
    print(f"  global min nt-term SCC size: {global_min_ntt_size}")
    if all_have_ntt and all_peel_match:
        trackA = "PASS"
    else:
        trackA = "FAIL"
        print(f"  Track A FAILS: terminal-SCC characterization of peel is not")
        print(f"  universal. Non-terminal non-trivial SCCs can survive peel.")

    print()
    # --- Track B: any non-trivial SCC (corrected characterization) -------
    print("TRACK B — 'any non-trivial SCC' (corrected characterization):")
    print(f"  records with ≥1 non-trivial SCC: "
          f"{total - sum(agg[k]['no_nt'] for k in agg)}/{total}")
    print(f"  peel ⊇ ∪(all non-trivial SCCs): "
          f"{sum(agg[k]['peel_supset_ok'] for k in agg)}/{total}")
    print(f"  global min non-trivial SCC size: {global_min_nt_size}")
    print(f"  global min number of non-trivial SCCs per record: "
          f"{global_min_num_nt}")

    if all_have_nt and all_peel_supset and global_min_nt_size is not None \
            and global_min_nt_size >= 2:
        trackB = "PASS"
        print(f"  Track B PASSES: every record has ≥ 1 non-trivial SCC of")
        print(f"  size ≥ {global_min_nt_size}; this SCC ALWAYS survives peel.")
    else:
        trackB = "FAIL"
        print(f"  Track B FAILS: non-trivial SCC existence / size / peel-⊇ "
              f"broken somewhere.")

    # --- Overall verdict -------------------------------------------------
    if trackB == "PASS":
        if trackA == "PASS":
            verdict = "GREEN"
            msg = ("GREEN: both terminal and non-terminal tracks pass. Either "
                   "gives a Lean-portable existence claim.")
        else:
            verdict = "GREEN"
            msg = ("GREEN (via Track B): every record has a non-trivial SCC "
                   f"of size ≥ {global_min_nt_size}, which always survives "
                   "peel. Track A (terminal-SCC) fails — Lean proof must use "
                   "'non-trivial SCC' not 'terminal SCC' as the witness.")
    else:
        if trackA == "FAIL" and all_have_nt:
            # Shouldn't happen given Track B conditions, but keep explicit.
            verdict = "YELLOW"
            msg = ("YELLOW: non-trivial SCC exists universally but either "
                   "size < 2 somewhere or peel-⊇ violated.")
        else:
            verdict = "RED"
            msg = ("RED: some record has NO non-trivial SCC at all → peel "
                   "empty → R4 REFUTED.")

    print()
    print(f"  Q: Every record has a terminal SCC of size ≥ 2?")
    if all_have_ntt and global_min_ntt_size is not None \
            and global_min_ntt_size >= 2:
        print(f"  A: YES (min nt-term size = {global_min_ntt_size}).")
    else:
        print(f"  A: NO. {total_no_ntt}/{total} records have no non-trivial "
              f"terminal SCC (but their non-trivial non-terminal SCC still "
              f"survives peel).")
    print()
    print(f"  Q: Every record has a non-trivial SCC of size ≥ 2?")
    if all_have_nt and global_min_nt_size is not None \
            and global_min_nt_size >= 2:
        print(f"  A: YES (min non-trivial SCC size = {global_min_nt_size}).")
        print(f"     This IS a uniform Lean-portable existence claim for R4.")
    else:
        print(f"  A: NO.")

    print(f"\n{'='*72}")
    print(f"FINAL VERDICT: {verdict}")
    print(f"  {msg}")
    print(f"{'='*72}")

    # --- dump JSON -------------------------------------------------------
    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'e16_scc_structure_2026-04-20.json')
    with open(out_path, 'w') as f:
        json.dump({
            'records': records,
            'plan': plan,
            'aggregate': agg,
            'verdict': verdict,
            'trackA': trackA,
            'trackB': trackB,
            'global_min_ntt_size': global_min_ntt_size,
            'global_max_ntt_size': global_max_ntt_size,
            'global_min_nt_size': global_min_nt_size,
            'global_max_nt_size': global_max_nt_size,
            'global_min_num_nt': global_min_num_nt,
            'total_records': total,
        }, f)
    print(f"\nWrote {out_path} ({total} records).", flush=True)


if __name__ == "__main__":
    main()
