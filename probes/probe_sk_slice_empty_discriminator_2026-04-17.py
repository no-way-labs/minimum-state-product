#!/usr/bin/env python3
"""Probe B: Slice-peel EMPTY-vs-NONEMPTY discriminator for SK-nonemptiness.

Main theorem needs only (SK gc).Nonempty  (≥ 1), NOT the floor |SK|≥2^(n-1).

For each sub-sharp good cycle C at (n, ms), for EACH (p, v) coordinate slice
    S_{p,v} = {c ∈ VC_NG : c[p] = v}
compute  peel(S_{p,v})  (peel w.r.t. forced neighbors into S_{p,v}).

Report:
  §1 emptiness headline  — #cycles with ALL slices empty vs ≥1 nonempty.
  §2 per-(p,v) discrimination — empty / nonempty counts.
  §3 universal witness check — is there (p,v) pattern uniformly nonempty?
  §4 analytical hypothesis
  §5 Lean sketch
  §6 failure modes

Reuses scaffolding from probe_sk_slice_peel_2026-04-17.py and
probe_sk_binary_slice_universal_2026-04-17.py verbatim:
    enumerate_all_cycles, value_sets, compute_sk (peel), move_entries build.
"""
from __future__ import annotations
from itertools import product as iproduct
from collections import Counter, defaultdict
import json
import os
import time
import sys
from multiprocessing import Pool

sys.setrecursionlimit(200000)


# ---------- multiset enumeration (copy of binary_slice_universal) ---------

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


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


# ---------- cycle enumeration -----------------------------------------

def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles, L_min=None):
    """Enumerate good cycles; each cycle must exercise all n procs (L>=n)."""
    if L_min is None:
        L_min = 2 * n + 2  # sub-sharp regime requires long cycle
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
            if L < L_min:
                return
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
            forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp:
                    continue
                if forced is not None and forced != new_val:
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


# ---------- VC_NG + peel ----------------------------------------------

def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def peel_subset(subset, adj_ng):
    """Iteratively remove configs with no forced neighbor INSIDE subset."""
    remaining = set(subset)
    while True:
        victims = set()
        for c in remaining:
            has_forced = False
            for nc in adj_ng.get(c, ()):
                if nc in remaining:
                    has_forced = True
                    break
            if not has_forced:
                victims.add(c)
        if not victims:
            break
        remaining -= victims
    return remaining


def build_structures(ms, n, cycle, det):
    V = value_sets(cycle, n)
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    ng_list = [c for c in all_configs if c not in cycle_set]
    ng_set = set(ng_list)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj_ng = defaultdict(list)
    for c in ng_list:
        for p in range(n):
            Lp = c[(p - 1) % n]
            Sp = c[p]
            Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in ng_set:
                    adj_ng[c].append(nc)
    return V_sorted, ng_set, adj_ng


# ---------- per-cycle measurement -------------------------------------

def measure_cycle(ms, n, cycle, movers, det):
    V_sorted, ng_set, adj_ng = build_structures(ms, n, cycle, det)
    L = len(movers)
    fc = Counter(movers)

    # Per (p, v) slice: peel within that slice.
    slice_table = {}  # (p, v) -> |peel|
    for p in range(n):
        for v in V_sorted[p]:
            slice_S = {c for c in ng_set if c[p] == v}
            peel_S = peel_subset(slice_S, adj_ng)
            slice_table[(p, v)] = len(peel_S)

    # Also compute global SK size for reference.
    SK = peel_subset(ng_set, adj_ng)

    return {
        'ms': ms,
        'n': n,
        'L': L,
        'fc': dict(fc),
        'V_sizes': [len(V_sorted[i]) for i in range(n)],
        'ng_size': len(ng_set),
        'SK_size': len(SK),
        'slice_table': {f"{p},{v}": cnt for (p, v), cnt in slice_table.items()},
    }


# ---------- per-ms worker ---------------------------------------------

def process_ms(args):
    n, ms, L_max, time_budget, max_cycles = args
    try:
        cycles = enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles)
    except Exception as e:
        return (n, ms, [], f"error:{e}")
    results = []
    for cycle, movers, det in cycles:
        try:
            r = measure_cycle(ms, n, cycle, movers, det)
            results.append(r)
        except Exception as e:
            results.append({'error': str(e), 'ms': ms, 'n': n})
    return (n, ms, results, 'ok')


# ---------- plan --------------------------------------------------------

def build_plan():
    """For each n, pick ≥3 sub-sharp ms. Prefer diverse binary counts."""
    plan = []

    # n = 5: small; M_5 = 96.  Pick up to 8 ms.
    n = 5
    ms_list = [ms for ms in enumerate_multisets(n, m_n_sharp(n))
               if min(ms) == 2]   # has a binary
    # dedupe by sorted signature (cycles only depend on multiset up to rotation)
    seen = set()
    uniq = []
    for ms in ms_list:
        key = tuple(sorted(ms))
        if key in seen:
            continue
        seen.add(key)
        uniq.append(ms)
    # Sort so simplest first
    uniq.sort(key=lambda t: (t.count(2), sorted(t)))
    ms5 = uniq[:4] + uniq[-2:] if len(uniq) > 6 else uniq
    for ms in ms5:
        plan.append((n, ms, 22, 20.0, 10))

    # n = 6: M_6 = 96·3 = 288
    n = 6
    ms_list = enumerate_multisets(n, m_n_sharp(n))
    ms_list = [m for m in ms_list if min(m) == 2]
    seen = set()
    uniq = []
    for ms in ms_list:
        key = tuple(sorted(ms))
        if key in seen:
            continue
        seen.add(key)
        uniq.append(ms)
    uniq.sort(key=lambda t: (t.count(2), sorted(t)))
    ms6 = uniq[:3] + uniq[-2:] if len(uniq) > 5 else uniq[:5]
    for ms in ms6:
        plan.append((n, ms, 22, 30.0, 8))

    # n = 7: M_7 = 864
    n = 7
    ms7 = [(2, 2, 2, 3, 3, 3, 3),
           (2, 2, 3, 2, 3, 3, 3),
           (2, 3, 2, 3, 2, 3, 3),
           (2, 2, 2, 2, 3, 3, 3),
           (2, 2, 3, 3, 3, 3, 3)]  # last is at or over sharp — skip if prod≥864
    ms7 = [m for m in ms7 if 1 <= (lambda mm: __import__('math').prod(mm))(m) < m_n_sharp(7)]
    for ms in ms7:
        plan.append((n, ms, 24, 45.0, 5))

    # n = 8: M_8 = 32·3^4 = 2592
    n = 8
    ms8 = [(2, 2, 2, 3, 3, 3, 3, 3),
           (2, 2, 3, 2, 3, 3, 3, 3),
           (2, 2, 2, 2, 3, 3, 3, 3),
           (2, 3, 2, 3, 2, 3, 3, 3)]
    for ms in ms8:
        plan.append((n, ms, 26, 90.0, 3))

    # n = 9: M_9 = 8748
    n = 9
    ms9 = [(2, 2, 2, 3, 3, 3, 3, 3, 3),
           (2, 2, 3, 2, 3, 3, 3, 3, 3),
           (2, 2, 2, 2, 3, 3, 3, 3, 3)]
    for ms in ms9:
        plan.append((n, ms, 26, 180.0, 2))

    return plan


# ---------- main & reporting ------------------------------------------

def main():
    t_start = time.time()
    plan = build_plan()
    print(f"Plan: {len(plan)} (n, ms) jobs")
    for j in plan:
        print(f"  n={j[0]} ms={j[1]} L_max={j[2]} tb={j[3]}s max_cyc={j[4]}")
    sys.stdout.flush()

    # Parallel per ms.
    nproc = min(os.cpu_count() or 1, 8, len(plan))
    results = []
    with Pool(processes=nproc) as pool:
        for res in pool.imap_unordered(process_ms, plan):
            n, ms, rlist, status = res
            print(f"[done] n={n} ms={ms} status={status} cycles={len(rlist)}",
                  flush=True)
            results.append(res)

    # Flatten.
    all_records = []
    for n, ms, rlist, status in results:
        for r in rlist:
            if 'error' in r:
                continue
            all_records.append(r)

    print(f"\nTotal cycle-records: {len(all_records)}  "
          f"elapsed {time.time()-t_start:.0f}s")

    # ----- §1 Emptiness headline -----
    catastrophic = 0  # all slices empty
    survives = 0      # ≥1 nonempty slice
    for r in all_records:
        mx = max(r['slice_table'].values()) if r['slice_table'] else 0
        if mx == 0:
            catastrophic += 1
        else:
            survives += 1
    print("\n§1 EMPTINESS HEADLINE")
    print(f"  catastrophic (all slices empty): {catastrophic}/{len(all_records)}")
    print(f"  survives (>=1 slice nonempty):   {survives}/{len(all_records)}")

    # ----- §2 Per-(p, v) discrimination ------
    # Use structural roles: ('pos=first_binary', 'v=0'), etc.
    # To first approximation, index by (role, value) where role ∈ {binary, ternary, other}
    # and position type ∈ {endpoint, interior}.
    print("\n§2 PER-(p, v) DISCRIMINATION (by structural role)")

    role_stats = defaultdict(lambda: {'empty': 0, 'nonempty': 0,
                                      'min': None, 'max': 0})
    for r in all_records:
        n = r['n']
        ms = r['ms']
        for (kstr, cnt) in r['slice_table'].items():
            p_str, v_str = kstr.split(',')
            p = int(p_str)
            v = int(v_str)
            mod = ms[p]
            # Role: modulus + value type
            role = (mod, v)
            s = role_stats[role]
            if cnt == 0:
                s['empty'] += 1
            else:
                s['nonempty'] += 1
            s['min'] = cnt if s['min'] is None else min(s['min'], cnt)
            s['max'] = max(s['max'], cnt)

    print("  role (m_p, v):       empty / nonempty   min..max")
    for role in sorted(role_stats):
        s = role_stats[role]
        tot = s['empty'] + s['nonempty']
        rate = 100.0 * s['nonempty'] / tot if tot else 0.0
        print(f"    m_p={role[0]} v={role[1]:<2}  "
              f"{s['empty']:>5}  /  {s['nonempty']:>5}   "
              f"nonempty_rate={rate:5.1f}%   "
              f"min={s['min']} max={s['max']}")

    # ----- §3 Universal witness check ------
    # Test:  for EVERY cycle, is there a canonical (p,v) rule that is nonempty?
    # Candidates we'll test:
    #   A. ternary v=0 at first ternary position
    #   B. binary v=0 at first binary position
    #   C. binary v=1 at first binary position
    #   D. ternary v=0 anywhere
    #   E. ternary v=2 anywhere
    #   F. binary v=0 anywhere
    print("\n§3 UNIVERSAL WITNESS CHECK (canonical rules over all cycles)")

    def rule_A(r):  # first ternary at v=0
        ms = r['ms']
        for p, m in enumerate(ms):
            if m == 3:
                return r['slice_table'].get(f"{p},0", 0)
        return None

    def rule_B(r):
        ms = r['ms']
        for p, m in enumerate(ms):
            if m == 2:
                return r['slice_table'].get(f"{p},0", 0)
        return None

    def rule_C(r):
        ms = r['ms']
        for p, m in enumerate(ms):
            if m == 2:
                return r['slice_table'].get(f"{p},1", 0)
        return None

    def rule_D(r):  # any ternary at v=0
        ms = r['ms']
        best = 0
        for p, m in enumerate(ms):
            if m == 3:
                v = r['slice_table'].get(f"{p},0", 0)
                best = max(best, v)
        return best

    def rule_E(r):
        ms = r['ms']
        best = 0
        for p, m in enumerate(ms):
            if m == 3:
                v = r['slice_table'].get(f"{p},2", 0)
                best = max(best, v)
        return best

    def rule_F(r):
        ms = r['ms']
        best = 0
        for p, m in enumerate(ms):
            if m == 2:
                v = r['slice_table'].get(f"{p},0", 0)
                best = max(best, v)
        return best

    def rule_G(r):  # best over ALL (p,v)
        if not r['slice_table']:
            return 0
        return max(r['slice_table'].values())

    rules = [('A_first_ternary_v0', rule_A),
             ('B_first_binary_v0', rule_B),
             ('C_first_binary_v1', rule_C),
             ('D_any_ternary_v0', rule_D),
             ('E_any_ternary_v2', rule_E),
             ('F_any_binary_v0', rule_F),
             ('G_best_any_slice', rule_G)]
    print("  rule                     nonempty_frac  min  #cyc_empty")
    per_n_pass = defaultdict(lambda: defaultdict(lambda: {'n_ok': 0, 'n_bad': 0}))
    for name, rule in rules:
        n_ok = 0
        n_bad = 0
        min_val = None
        for r in all_records:
            val = rule(r)
            if val is None:
                continue
            if val >= 1:
                n_ok += 1
                per_n_pass[name][r['n']]['n_ok'] += 1
            else:
                n_bad += 1
                per_n_pass[name][r['n']]['n_bad'] += 1
            min_val = val if min_val is None else min(min_val, val)
        tot = n_ok + n_bad
        frac = 100.0 * n_ok / tot if tot else 0.0
        print(f"    {name:<24}  {frac:5.1f}%        min={min_val}  bad={n_bad}")

    print("\n  Per-n breakdown (rule -> n -> ok/total):")
    for name, _ in rules:
        pn = per_n_pass[name]
        line = f"    {name:<24}"
        for n in sorted(pn):
            d = pn[n]
            tot = d['n_ok'] + d['n_bad']
            line += f"  n{n}:{d['n_ok']}/{tot}"
        print(line)

    # ----- §3b minimum disjunction ------
    # Find minimum set of (m_p, v) structural classes (not exact positions)
    # that cover every cycle.
    print("\n§3b MINIMUM DISJUNCTION OF STRUCTURAL RULES")
    candidate_classes = [
        ('any_ternary_v0', lambda r: rule_D(r) >= 1),
        ('any_ternary_v1', lambda r: max(
            [r['slice_table'].get(f"{p},1", 0)
             for p, m in enumerate(r['ms']) if m == 3] + [0]) >= 1),
        ('any_ternary_v2', lambda r: rule_E(r) >= 1),
        ('any_binary_v0', lambda r: rule_F(r) >= 1),
        ('any_binary_v1', lambda r: max(
            [r['slice_table'].get(f"{p},1", 0)
             for p, m in enumerate(r['ms']) if m == 2] + [0]) >= 1),
    ]
    uncovered = list(all_records)
    chosen = []
    while uncovered:
        best = None
        best_cov = 0
        for name, pred in candidate_classes:
            cov = sum(1 for r in uncovered if pred(r))
            if cov > best_cov:
                best_cov = cov
                best = (name, pred)
        if best is None or best_cov == 0:
            print(f"  UNCOVERED cycles remain: {len(uncovered)} (no rule helps)")
            break
        chosen.append((best[0], best_cov))
        uncovered = [r for r in uncovered if not best[1](r)]
        print(f"    + {best[0]}  covers {best_cov}  remaining={len(uncovered)}")
    print(f"  minimum disjunction size: {len(chosen)}  rules: "
          f"{[c[0] for c in chosen]}")

    # ----- §4-§6: written in final report -----

    # Save raw data.
    out_path = "./probes/probe_sk_slice_empty_discriminator_2026-04-17.out.json"
    with open(out_path, 'w') as f:
        json.dump({
            'plan': [(n, list(ms), L, tb, mc) for (n, ms, L, tb, mc) in plan],
            'records': all_records,
            'role_stats': {f"{k[0]},{k[1]}": v for k, v in role_stats.items()},
            'catastrophic': catastrophic,
            'survives': survives,
        }, f, indent=2, default=str)
    print(f"\nRaw data: {out_path}")
    print(f"Total elapsed: {time.time()-t_start:.0f}s")


if __name__ == "__main__":
    main()
