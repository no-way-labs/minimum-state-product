#!/usr/bin/env python3
"""Probe E15 — SMARTER walk heuristics for B2' closure.

After E14 (lex-first canonical walk) failed at 17% of records, test
whether smarter but still cycle-STRUCTURE-INDEPENDENT walk rules close
the gap. If any single rule works uniformly, we have a Lean-portable
construction.

RULES (all deterministic, cycle-independent, hash-free):
  S1. Lex-first forced-NG successor in T_N1 (= R1 baseline, for compare).
  S2. "DEGREE": successor with highest forced-NG out-degree in T_N1.
      Tie-break: lex order on (position, value).
  S3. "COVER": successor that maximizes |{next-next successors in T_N1}|.
      2-hop lookahead. Tie-break: lex.
  S4. "COVER-ALL-BOOST": successor that minimizes #sinks reachable in 2 hops.
  S5. "STAY": pick successor whose 'mover position' is different from current
      (encourages fresh contexts). Tie-break: lex.
  S6. "FURTHEST-FROM-SINKS": if computable cheaply, pick successor that's
      not a sink AND whose every successor is not a sink.

STARTING POINT: lex-first Hamming-1 perturbation of c_0 (same as R1).

Goal: find a single rule with 100% cycle coverage. If none works, report
the residue (records where ALL rules fail → structural residue).
"""
from __future__ import annotations

import json
import os
import time
from collections import Counter, defaultdict
from itertools import product as iproduct


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


def build_tube(ms, n, cycle, movers, det):
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


def adj_in_T(c, n, move_entries, T):
    """All forced-NG successors of c in T. Returns list of (p, nc)."""
    out = []
    for p in range(n):
        ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
        val = move_entries.get(ctx)
        if val is None or val == c[p]:
            continue
        nc = list(c)
        nc[p] = val
        nc = tuple(nc)
        if nc in T:
            out.append((p, nc))
    return out


def walk(c0, rule, n, move_entries, T, max_steps):
    """Walk under the given successor-selection rule. Return outcome dict."""
    visited = {c0: 0}
    cur = c0
    for step in range(1, max_steps + 1):
        choices = adj_in_T(cur, n, move_entries, T)
        if not choices:
            return {'outcome': 'exit', 'walk_len': step}
        nxt = rule(cur, choices, n, move_entries, T)
        if nxt in visited:
            return {'outcome': 'cycle', 'walk_len': step,
                    'cycle_start': visited[nxt],
                    'cycle_len': step - visited[nxt]}
        visited[nxt] = step
        cur = nxt
    return {'outcome': 'max_steps', 'walk_len': max_steps}


# ----- selection rules ----------------------------------------------------

def rule_S1(cur, choices, n, move_entries, T):
    """Lex by (p, val)."""
    return min((nc for (_, nc) in choices))


def rule_S2(cur, choices, n, move_entries, T):
    """Highest out-degree, tie-break lex."""
    best = None
    best_deg = -1
    for nc in sorted(nc for (_, nc) in choices):
        deg = len(adj_in_T(nc, n, move_entries, T))
        if deg > best_deg:
            best_deg = deg
            best = nc
    return best


def rule_S3(cur, choices, n, move_entries, T):
    """Maximize 2-hop reach size. Tie-break lex."""
    best = None
    best_cov = -1
    for nc in sorted(nc for (_, nc) in choices):
        reach2 = set()
        for (_, nc2) in adj_in_T(nc, n, move_entries, T):
            reach2.add(nc2)
        if len(reach2) > best_cov:
            best_cov = len(reach2)
            best = nc
    return best


def rule_S4(cur, choices, n, move_entries, T):
    """Minimize 2-hop sinks. Tie-break lex."""
    best = None
    best_sinks = 10**9
    for nc in sorted(nc for (_, nc) in choices):
        sinks2 = 0
        for (_, nc2) in adj_in_T(nc, n, move_entries, T):
            if not adj_in_T(nc2, n, move_entries, T):
                sinks2 += 1
        if sinks2 < best_sinks:
            best_sinks = sinks2
            best = nc
    return best


def rule_S5(cur, choices, n, move_entries, T):
    """Lex on (new-mover ≠ any previous? use differentiated order).
    Use position ≠ last-position if possible, else lex."""
    # Approximation: prefer successor with DIFFERENT firing position
    # from the last step. But we don't track last-step here, so use
    # position furthest from 0 (cyclic).
    best = None
    best_p = -1
    for (p, nc) in choices:
        if p > best_p:
            best_p = p
            best = nc
        elif p == best_p and (best is None or nc < best):
            best = nc
    return best


def try_rule_R1(cycle, T, V_list, n, move_entries):
    c_0 = cycle[0]
    for q in range(n):
        for v in V_list[q]:
            if v == c_0[q]:
                continue
            nc = list(c_0)
            nc[q] = v
            nc = tuple(nc)
            if nc in T:
                return nc
    return None


def analyze(ms, n, cycle, movers, det):
    T, V_list, move_entries, cycle_set = build_tube(ms, n, cycle, movers, det)
    if not T:
        return None

    c0 = try_rule_R1(cycle, T, V_list, n, move_entries)
    if c0 is None:
        return {'n': n, 'L': len(cycle), 'T_size': len(T), 'no_c0': True}

    max_steps = len(T) + 2
    rules = {
        'S1': rule_S1,
        'S2': rule_S2,
        'S3': rule_S3,
        'S4': rule_S4,
        'S5': rule_S5,
    }

    outcomes = {}
    for name, rule in rules.items():
        r = walk(c0, rule, n, move_entries, T, max_steps)
        outcomes[name] = r['outcome']

    return {
        'n': n, 'L': len(cycle), 'T_size': len(T),
        'outcomes': outcomes,
    }


def main():
    print("=" * 72, flush=True)
    print("E15 probe: smart walk rules for B2' closure", flush=True)
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

    print(f"\n{'='*72}\nSummary ({len(records)} records, "
          f"{time.time()-t_global:.0f}s)\n{'='*72}")

    rule_names = ['S1', 'S2', 'S3', 'S4', 'S5']
    by_n = defaultdict(list)
    for r in records:
        by_n[r['n']].append(r)

    global_fail = defaultdict(int)

    for n in sorted(by_n):
        recs = by_n[n]
        print(f"\n  n={n}  records={len(recs)}")
        for rule in rule_names:
            cycled = sum(1 for r in recs
                         if r.get('outcomes', {}).get(rule) == 'cycle')
            print(f"    {rule}:  cycled={cycled}/{len(recs)}  "
                  f"({100.0 * cycled / max(len(recs), 1):.1f}%)")
            global_fail[rule] += (len(recs) - cycled)

        # any rule works?
        any_cycle = sum(1 for r in recs
                        if any(r.get('outcomes', {}).get(s) == 'cycle'
                               for s in rule_names))
        all_fail = sum(1 for r in recs
                       if not any(r.get('outcomes', {}).get(s) == 'cycle'
                                  for s in rule_names))
        print(f"    ANY RULE works: {any_cycle}/{len(recs)}  "
              f"({100.0 * any_cycle / max(len(recs), 1):.1f}%)")
        print(f"    ALL FAIL:       {all_fail}/{len(recs)}")

    print(f"\n{'='*72}")
    for rule in rule_names:
        total = len(records)
        failed = global_fail[rule]
        print(f"  {rule}: {total - failed}/{total} passed  "
              f"({100.0 * (total - failed) / max(total, 1):.2f}%)")

    any_cycle = sum(1 for r in records
                    if any(r.get('outcomes', {}).get(s) == 'cycle'
                           for s in rule_names))
    print(f"\n  ANY OF S1..S5 works: {any_cycle}/{len(records)}  "
          f"({100.0 * any_cycle / max(len(records), 1):.2f}%)")
    print(f"{'='*72}")


if __name__ == "__main__":
    main()
