#!/usr/bin/env python3
"""n=8 validation of the projection-floor hypothesis (Lemma C P1 route).

Lightweight sampling probe. Confirms max_p |proj_p(SK)| >= 2^(n-1) = 128
and that argmax_p is always a minimum-fire-count processor. Only
checks L = 2n+2 = 18 (the tightest bucket for Lemma C) at a small
stride-60 sample of sub-sharp-M_8 multisets.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import sys

sys.setrecursionlimit(20000)


def m_n_sharp(n):
    if n == 4: return 24
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


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
                new_det = dict(det)
                new_det[km] = new_val
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si:
                        ok = False; break
                    new_det[ki] = Si
                if not ok:
                    continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def compute_sk(ms, n, cycle, det):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    remaining = set(non_good)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt, _ in adj.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
    return remaining


def main():
    n = 8
    L_min = 2 * n + 2  # = 18
    L_max_bound = 20
    target = 2 ** (n - 1)  # = 128
    target_slice = 2 ** (n - 2)  # = 64
    stride = 100
    max_cycles_per_ms = 25
    tb_per_ms = 10.0

    print("=" * 80, flush=True)
    print(f"n={n} validation: projection-floor hypothesis at L in [{L_min}, {L_max_bound}]",
          flush=True)
    print(f"  target: max_p |proj_p(SK)| >= {target}", flush=True)
    print(f"  also: argmax_p == min-fc processor (100% predicted)", flush=True)
    print("=" * 80, flush=True)

    Mn = m_n_sharp(n)
    multisets = enumerate_multisets(n, Mn)
    sampled = multisets[::stride]
    print(f"\n  sub-M_{n} multisets: {len(multisets)}, sampled stride-{stride}: "
          f"{len(sampled)}", flush=True)

    records = 0
    hypo_violations = 0
    minfc_violations = 0
    min_slack = float('inf')
    by_L = defaultdict(int)
    t0 = time.time()

    for idx, ms in enumerate(sampled):
        cycles = enumerate_all_cycles(ms, n, L_max_bound, tb_per_ms, max_cycles_per_ms)
        for cycle, movers, det in cycles:
            L = len(movers)
            if L < L_min or L > L_max_bound:
                continue
            by_L[L] += 1
            sk = compute_sk(ms, n, cycle, det)
            if not sk:
                continue
            records += 1
            # fire vector
            fv_list = [0] * n
            for p in movers:
                fv_list[p] += 1
            min_fc = min(fv_list)

            # projections
            proj_sizes = []
            for p in range(n):
                proj = set()
                for c in sk:
                    proj.add(tuple(c[i] for i in range(n) if i != p))
                proj_sizes.append(len(proj))
            max_proj = max(proj_sizes)
            argmax_p = proj_sizes.index(max_proj)
            slack = max_proj - target
            if slack < min_slack:
                min_slack = slack
            if max_proj < target:
                hypo_violations += 1
                print(f"  !! violation: ms={ms} fv={fv_list} max_proj={max_proj} "
                      f"target={target}", flush=True)
            if fv_list[argmax_p] != min_fc:
                minfc_violations += 1
        if (idx + 1) % 2 == 0 or idx == len(sampled) - 1:
            elapsed = time.time() - t0
            print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s  "
                  f"records={records}  violations={hypo_violations}  "
                  f"min_slack={min_slack}", flush=True)

    print(f"\n=== Result ===", flush=True)
    print(f"  records: {records}", flush=True)
    print(f"  P1-proj violations: {hypo_violations}", flush=True)
    print(f"  min-fc argmax violations: {minfc_violations}", flush=True)
    print(f"  min_slack: {min_slack}", flush=True)
    print(f"  records by L: {dict(by_L)}", flush=True)
    if hypo_violations == 0 and records > 0:
        print(f"  -> HYPOTHESIS HOLDS at n={n}, L in [{L_min}, {L_max_bound}]", flush=True)


if __name__ == "__main__":
    main()
