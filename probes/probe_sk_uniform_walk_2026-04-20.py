#!/usr/bin/env python3
"""Probe E14 — uniform forced-NG walk into a cycle inside T_N1.

GOAL
    Decide: from a *canonically chosen* starting config c0 in T_N1 (computable
    from cycle data alone, no case splits on cycle shape), does the
    canonical forced-NG walk pigeonhole into a cycle inside T_N1 before
    exiting T_N1?

WHY
    If yes uniformly: B2' (peelTube_nonempty) closes via a clean Lean
    construction.
      - Define c0 by fixed formula (e.g. lex-first valid Hamming-1
        perturbation of c_0).
      - Define canonical step f : T_N1 -> T_N1 ∪ {⊥}:
          f(c) = lex-first forced-NG successor of c in T_N1.
      - Walk (c0, f(c0), f^2(c0), ...) of length |T_N1| + 1.
      - If walk stays in T_N1, pigeonhole ⟹ two terms coincide ⟹
        cycle ⟹ forced-closed subset ⟹ SK nonempty via bridge.

    Lean obligation reduces to: "this specific c0 has infinite forced-NG
    walk in T_N1." Or equivalently: "walk of length |T_N1|+1 stays in
    T_N1."

CANDIDATE c0 RULES (cycle-structure-independent)
  R1. c0 = c_0[q* ← v*] with (q*, v*) lex-first s.t. c_0[q*←v*] ∈ T_N1.
  R2. For each cycle step k ∈ [0, L), try c0 = c_k[q ← v] lex-first
      yielding a c0 whose canonical walk stays in T_N1 long. Report the
      minimum walk-length-to-revisit and whether ANY (k,q,v) gives a
      walk of length ≥ |T_N1|+1.

CANONICAL STEP RULE
    f(c) := (first, in lex order on (p, val), forced-NG successor of c
             landing in T_N1).
    Lex on (p, val): iterate positions p=0..n-1, for each p check
    det[p, Lp, Sp, Rp]; if it yields v ≠ Sp with applyMove(c, p, v) ∈
    T_N1 ∩ NG, take it.

OUTCOMES
  PASS: for R1, every record has walk-length-to-revisit ≤ |T_N1|+1
        (guaranteed by pigeonhole) AND walk stays in T_N1 throughout.
        Means c0 produces a cycle deterministically.
  FAIL: some records have walk EXIT T_N1 (walk hits a config outside
        T_N1) before revisiting ⟹ the chosen c0 doesn't give a valid
        in-T_N1 pigeonhole cycle ⟹ R1 rule must be refined.
  If R1 fails but R2 always succeeds for SOME (k,q,v): the existence
        of a valid c0 is cycle-dependent; R4 route likely needs
        structural lemma rather than uniform construction.

Uses cycle enumerator from probe_sk_edge_sink_margin_2026-04-19.py.
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict
from itertools import product as iproduct


# ----- thresholds / enumeration (copied from edge-sink probe) -------------

def m_n(n: int) -> int:
    return 32 * 3 ** (n - 4) if 5 <= n <= 8 else 4 * 3 ** (n - 2)


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


# ----- tube + canonical walk ---------------------------------------------

def build_tube(ms, n, cycle, movers, det):
    """Return (T, V_list, move_entries, cycle_set)."""
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
    return T, V_list, move_entries, cycle_set


def canonical_fsucc(c, n, move_entries, T):
    """Lex-first (by position p, then new value v) forced-NG successor
    of c that lies in T. Returns None if no such successor."""
    for p in range(n):
        ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
        val = move_entries.get(ctx)
        if val is None:
            continue
        if val == c[p]:
            continue  # not a move
        nc = list(c)
        nc[p] = val
        nc = tuple(nc)
        if nc in T:
            return nc
    return None


def walk_until_revisit_or_exit(c0, n, move_entries, T, max_steps):
    """Walk canonical forced-NG successors from c0. Track until revisit
    (good) or exit to ⊥ (bad). Returns dict with outcome."""
    visited = {c0: 0}
    cur = c0
    for step in range(1, max_steps + 1):
        nxt = canonical_fsucc(cur, n, move_entries, T)
        if nxt is None:
            return {
                'outcome': 'exit',
                'walk_len': step,
                'visited_before_exit': len(visited),
            }
        if nxt in visited:
            return {
                'outcome': 'cycle',
                'walk_len': step,
                'cycle_start': visited[nxt],
                'cycle_len': step - visited[nxt],
            }
        visited[nxt] = step
        cur = nxt
    return {
        'outcome': 'max_steps',
        'walk_len': max_steps,
        'visited_before_exit': len(visited),
    }


# ----- probe drivers ------------------------------------------------------

def try_rule_R1(cycle, T, V_list, n, move_entries):
    """Rule R1: c0 = c_0[q* ← v*] lex-first with c_0[q*←v*] ∈ T."""
    c_0 = cycle[0]
    for q in range(n):
        for v in V_list[q]:
            if v == c_0[q]:
                continue
            nc = list(c_0)
            nc[q] = v
            nc = tuple(nc)
            if nc in T:
                return nc, (q, v)
    return None, None


def try_rule_R2(cycle, T, V_list, n, move_entries):
    """Rule R2 variant: try every (k, q, v) and return the FIRST giving
    a cycle via canonical walk. Used as existence check."""
    L = len(cycle)
    max_steps = len(T) + 2
    for k in range(L):
        c_k = cycle[k]
        for q in range(n):
            for v in V_list[q]:
                if v == c_k[q]:
                    continue
                nc = list(c_k)
                nc[q] = v
                nc = tuple(nc)
                if nc in T:
                    r = walk_until_revisit_or_exit(nc, n, move_entries, T,
                                                    max_steps)
                    if r['outcome'] == 'cycle':
                        return nc, (k, q, v), r['cycle_len']
    return None, None, None


def analyze(ms, n, cycle, movers, det):
    T, V_list, move_entries, cycle_set = build_tube(ms, n, cycle, movers, det)
    L = len(cycle)
    if not T:
        return None

    # R1 test: deterministic lex-first c0 from c_0
    c0_R1, anchor_R1 = try_rule_R1(cycle, T, V_list, n, move_entries)
    max_steps = len(T) + 2

    if c0_R1 is None:
        R1 = {'has_c0': False}
    else:
        r = walk_until_revisit_or_exit(c0_R1, n, move_entries, T, max_steps)
        R1 = {'has_c0': True, 'anchor': anchor_R1, **r}

    # R2 test: existence of ANY (k,q,v) giving a cycle
    c0_R2, anchor_R2, cyc_len = try_rule_R2(cycle, T, V_list, n, move_entries)
    if c0_R2 is None:
        R2 = {'any_c0_gives_cycle': False}
    else:
        R2 = {'any_c0_gives_cycle': True, 'anchor': anchor_R2,
              'cycle_len': cyc_len}

    return {
        'n': n, 'ms': list(ms), 'L': L, 'T_size': len(T),
        'R1': R1, 'R2': R2,
    }


def main():
    print("=" * 72, flush=True)
    print("E14 probe: uniform forced-NG walk into a cycle inside T_N1",
          flush=True)
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
        print(f"\n=== n={n}  M_n={Mn}  multisets={len(multisets)}  "
              f"sampled={len(sampled)} ===", flush=True)
        t0 = time.time()
        rec_before = len(records)
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
                      f"records(+{len(records)-rec_before})", flush=True)

    # ----- summary -------------------------------------------------------
    print(f"\n{'='*72}\nSummary ({len(records)} records, "
          f"{time.time()-t_global:.0f}s)\n{'='*72}")

    by_n = defaultdict(list)
    for r in records:
        by_n[r['n']].append(r)

    r1_fail_total = 0
    r2_fail_total = 0

    for n in sorted(by_n):
        recs = by_n[n]
        r1_has = sum(1 for r in recs if r['R1']['has_c0'])
        r1_cycle = sum(1 for r in recs
                       if r['R1']['has_c0'] and r['R1'].get('outcome') == 'cycle')
        r1_exit = sum(1 for r in recs
                      if r['R1']['has_c0'] and r['R1'].get('outcome') == 'exit')
        r2_has = sum(1 for r in recs if r['R2']['any_c0_gives_cycle'])

        print(f"\n  n={n}  records={len(recs)}")
        print(f"    R1 (lex-first c_0 perturbation):")
        print(f"      has_c0:      {r1_has}/{len(recs)}")
        print(f"      → cycle:     {r1_cycle}/{r1_has}")
        print(f"      → exit:      {r1_exit}/{r1_has}")
        if r1_cycle > 0:
            cyc_lens = [r['R1']['cycle_len'] for r in recs
                        if r['R1'].get('outcome') == 'cycle']
            print(f"      cycle_len:   {min(cyc_lens)}..{max(cyc_lens)}  "
                  f"mean={sum(cyc_lens)/len(cyc_lens):.1f}")
        print(f"    R2 (ANY (k,q,v) gives a cycle):")
        print(f"      ≥1 works:    {r2_has}/{len(recs)}")

        r1_fail_total += (len(recs) - r1_cycle)
        r2_fail_total += (len(recs) - r2_has)

    print(f"\n{'='*72}")
    all_n = len(records)
    if r1_fail_total == 0:
        print("VERDICT: R1 PASS — deterministic lex-first c0 always "
              "produces a cycle.")
        print("  → Lean port: ~200 lines. Construct c0, walk |T|+1 steps, "
              "pigeonhole.")
    elif r2_fail_total == 0:
        print(f"VERDICT: R1 fails on {r1_fail_total}/{all_n} records, "
              f"R2 passes universally.")
        print("  → Existence of a valid c0 is cycle-dependent but always "
              "guaranteed.")
        print("  → Lean port: need a SELECTOR (q*, v*) for c0 that works "
              "uniformly.")
        print("  → Or: prove 'some c0 works' abstractly via pigeonhole on "
              "T_N1 directly.")
    else:
        print(f"VERDICT: FAIL — R1 fails on {r1_fail_total}/{all_n}, "
              f"R2 fails on {r2_fail_total}/{all_n}.")
        print("  → Uniform walk construction doesn't close B2'. R4 needs "
              "a different lever.")
    print(f"{'='*72}")

    out_dir = os.path.join(os.path.dirname(__file__), 'sk_phase0_out')
    os.makedirs(out_dir, exist_ok=True)
    out_path = os.path.join(out_dir, 'e14_uniform_walk_2026-04-20.json')
    with open(out_path, 'w') as f:
        json.dump({'records': records, 'plan': plan}, f)
    print(f"\nWrote {out_path} ({len(records)} records).", flush=True)


if __name__ == "__main__":
    main()
