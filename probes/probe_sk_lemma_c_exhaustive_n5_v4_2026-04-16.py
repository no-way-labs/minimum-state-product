#!/usr/bin/env python3
"""Exhaustive SK verification at n=5 — v4 (fast SK).

Key optimization: precompute ALL configs for the multiset once.
For each det, compute SK using precomputed config list + bitset peeling.
"""
from itertools import product as iproduct
from collections import defaultdict
import time
import sys


N = 5
TARGET = 2 ** (N - 1)  # 16
MN = 96
L_MAX = 30


def enumerate_mixed_multisets():
    out = []
    def rec(i, prefix, prod):
        if i == N:
            if prod < MN and max(prefix) >= 3:
                out.append(tuple(prefix))
            return
        for m in range(2, MN + 1):
            new_prod = prod * m
            min_remaining = 2 ** (N - i - 1)
            if new_prod * min_remaining >= MN:
                break
            prefix.append(m)
            rec(i + 1, prefix, new_prod)
            prefix.pop()
    rec(0, [], 1)
    return out


def compute_sk_fast(all_configs_set, n, det, cycle_set):
    """Fast SK computation using precomputed config set."""
    # Value sets from cycle
    V = [set() for _ in range(n)]
    for c in cycle_set:
        for i in range(n):
            V[i].add(c[i])

    # Move entries
    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # VC-NG: configs that are value-compatible and not in cycle
    vc_ng = []
    for c in all_configs_set:
        if c in cycle_set:
            continue
        if all(c[i] in V[i] for i in range(n)):
            vc_ng.append(c)

    if not vc_ng:
        return 0

    vc_ng_set = set(vc_ng)

    # Build adjacency as list of target indices
    # Map configs to indices for fast lookup
    cfg_to_idx = {c: i for i, c in enumerate(vc_ng)}
    adj = [[] for _ in range(len(vc_ng))]

    for i, c in enumerate(vc_ng):
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in cfg_to_idx:
                    adj[i].append(cfg_to_idx[nc])

    # Peeling with index-based sets
    alive = [True] * len(vc_ng)
    changed = True
    while changed:
        changed = False
        for i in range(len(vc_ng)):
            if not alive[i]:
                continue
            has_live_target = False
            for j in adj[i]:
                if alive[j]:
                    has_live_target = True
                    break
            if not has_live_target:
                alive[i] = False
                changed = True

    return sum(alive)


def run_multiset(ms):
    """Exhaustive enumeration + inline SK for one multiset."""
    n = N
    all_configs = list(iproduct(*[range(m) for m in ms]))
    all_configs_set = set(all_configs)

    seen_fps = set()  # just track which dets we've seen
    total_raw = 0
    total_unique = 0
    min_sk = float('inf')
    violations = 0
    L_counts = defaultdict(int)

    def det_fp(det):
        return frozenset((k, v) for k, v in det.items() if v != k[2])

    def dfs(start, config, det, path, movers, path_set):
        nonlocal total_raw, total_unique, min_sk, violations

        if len(path) > 1 and config == start:
            if set(movers) == set(range(n)):
                total_raw += 1
                fp = det_fp(det)
                if fp not in seen_fps:
                    seen_fps.add(fp)
                    total_unique += 1
                    L = len(movers)
                    L_counts[L] += 1
                    cycle_set = set(path[:L])
                    sk = compute_sk_fast(all_configs_set, n, det, cycle_set)
                    if sk < min_sk:
                        min_sk = sk
                    if sk < TARGET:
                        violations += 1
            return

        if len(path) >= L_MAX:
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
                if nc in path_set and nc != start:
                    continue

                new_ps = path_set | {nc} if nc != start else path_set
                dfs(start, nc, new_det, path + [nc], movers + [p], new_ps)

    t0 = time.time()
    for si, start in enumerate(all_configs):
        dfs(start, start, {}, [start], [], {start})
        if (si + 1) % 10 == 0 or si == len(all_configs) - 1:
            elapsed = time.time() - t0
            print(f"    [{si+1}/{len(all_configs)}] {elapsed:.0f}s  "
                  f"raw={total_raw}  unique={total_unique}  "
                  f"min_sk={min_sk}  viol={violations}", flush=True)

    return {
        'raw': total_raw,
        'unique': total_unique,
        'min_sk': min_sk,
        'violations': violations,
        'L_counts': dict(L_counts),
        'time': time.time() - t0,
    }


def main():
    print("=" * 72, flush=True)
    print(f"EXHAUSTIVE SK VERIFICATION v4: n={N}, 2^(n-1)={TARGET}", flush=True)
    print("=" * 72, flush=True)

    multisets = enumerate_mixed_multisets()
    print(f"Mixed sub-M_{N} multisets: {len(multisets)}", flush=True)

    grand_raw = 0
    grand_unique = 0
    grand_violations = 0
    grand_min_sk = float('inf')

    for mi, ms in enumerate(multisets):
        prod = 1
        for m in ms:
            prod *= m
        print(f"\n[{mi+1}/{len(multisets)}] ms={ms} product={prod}", flush=True)

        r = run_multiset(ms)
        grand_raw += r['raw']
        grand_unique += r['unique']
        grand_violations += r['violations']
        if r['min_sk'] < grand_min_sk:
            grand_min_sk = r['min_sk']

        Ls = ", ".join(f"L={L}:{c}" for L, c in sorted(r['L_counts'].items()))
        v = r['violations']
        print(f"  DONE: unique={r['unique']}  raw={r['raw']}  "
              f"min_SK={r['min_sk']}  "
              f"{'OK' if v == 0 else f'{v} VIOLATIONS!!'}  "
              f"({r['time']:.1f}s)", flush=True)
        print(f"  L: {Ls}", flush=True)

    print(f"\n{'='*72}", flush=True)
    print(f"FINAL: {len(multisets)} ms, {grand_unique} unique dets, "
          f"{grand_raw} raw", flush=True)
    print(f"  Min SK: {grand_min_sk}", flush=True)
    print(f"  Violations: {grand_violations}", flush=True)
    if grand_violations == 0:
        print(f"\n  *** LEMMA C VERIFIED AT n={N}: "
              f"|SK| >= {TARGET} for ALL {grand_unique} unique cycles ***",
              flush=True)
    else:
        print(f"\n  *** LEMMA C FAILED: {grand_violations} violations ***",
              flush=True)


if __name__ == "__main__":
    main()
