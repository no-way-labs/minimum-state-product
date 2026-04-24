#!/usr/bin/env python3
"""SK projection floor at n=8 (extending 2026-04-15 probe).

P1-proj: max_p |pi_{drop-p}(SK)| >= 2^(n-1).
If TRUE, gives Lemma C cleanly: |SK| >= |projection| >= 2^(n-1).

Original probe only ran n=5,6,7. This extension tests n=8 directly.
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


def compute_sk(ms, n, cycle, det):
    # Restrict to V_p (values visited) cube, not full ms cube
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    remaining = set(non_good)
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt, _ in adj.get(c, [])):
                sinks.add(c)
        if not sinks: break
        remaining -= sinks
    return remaining


def analyze_cycle(ms, n, cycle, movers, det):
    sk = compute_sk(ms, n, cycle, det)
    sk_size = len(sk)
    # Projections by dropping each coord
    proj_sizes = []
    for p in range(n):
        proj = set()
        for c in sk:
            proj.add(tuple(c[i] for i in range(n) if i != p))
        proj_sizes.append(len(proj))
    return sk_size, max(proj_sizes), proj_sizes


def main():
    print("=" * 80, flush=True)
    print("SK projection floor @ n=8 (P1-proj test)", flush=True)
    print("=" * 80, flush=True)

    # n=8 only — larger L range, modest sampling
    plan = [
        (8, 30, 4, 20.0, 24),
    ]
    records = []
    worst_by_L = {}
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets  L range [{2*n+2}, {L_max}] ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2: continue
                sk_size, max_proj, proj_sizes = analyze_cycle(ms, n, cycle, movers, det)
                records.append({'n':n, 'L':L, 'ms':ms, 'sk':sk_size,
                                'max_proj': max_proj, 'proj_sizes': proj_sizes})
                key = (n, L)
                if key not in worst_by_L or max_proj < worst_by_L[key][0]:
                    worst_by_L[key] = (max_proj, sk_size, ms)
            if (idx + 1) % max(1, len(multisets)//6) == 0:
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s  records={len(records)}", flush=True)

    print(f"\n=== Projection floor analysis @ n=8 ===")
    print(f"  records: {len(records)}")
    print(f"  bound 2^(n-1) = 128")
    target = 128
    viols = 0
    for (n, L) in sorted(worst_by_L):
        mp, sk, ms = worst_by_L[(n, L)]
        cnt = sum(1 for r in records if r['n']==n and r['L']==L)
        slack = mp - target
        flag = " !!" if mp < target else ""
        print(f"  L={L:>2}  count={cnt:>4}  min_max_proj={mp}  slack={slack:+}  worst_ms={ms}{flag}")
        if mp < target: viols += 1
    print(f"\n  P1-proj @ n=8: {'HOLDS' if viols == 0 else f'VIOLATED ({viols} buckets)'}")

    # Also report min proj_size (all p) vs target to see if SUM is the bound
    print(f"\n=== All-p projection min @ each L ===")
    for (n, L) in sorted(worst_by_L):
        sub = [r for r in records if r['n']==n and r['L']==L]
        min_max = min(r['max_proj'] for r in sub)
        avg_max = sum(r['max_proj'] for r in sub)/len(sub)
        max_max = max(r['max_proj'] for r in sub)
        min_sk = min(r['sk'] for r in sub)
        print(f"  L={L}  min_max_proj/avg/max = {min_max}/{avg_max:.1f}/{max_max}"
              f"  min |SK|={min_sk}")


if __name__ == "__main__":
    main()
