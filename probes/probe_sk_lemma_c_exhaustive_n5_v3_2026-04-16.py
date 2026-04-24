#!/usr/bin/env python3
"""Exhaustive SK verification at n=5 — v3 (memory-lean).

Computes SK inline during DFS. Only stores det fingerprints (set of
move entries) to avoid recomputing SK for the same det. Does NOT store
cycle configs or full dets.
"""
from itertools import product as iproduct
from collections import defaultdict
import time
import sys


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_mixed_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product and max(prefix) >= 3:
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


def compute_sk_inline(ms, n, det, cycle_list):
    """Compute |SK| from det and cycle list. Minimal memory."""
    cycle_set = set(map(tuple, cycle_list))
    V = [set() for _ in range(n)]
    for c in cycle_set:
        for i in range(n):
            V[i].add(c[i])

    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_ng = set(iproduct(*vc_ranges)) - cycle_set

    # Build out-targets as frozen sets for fast intersection
    out_targets = {}
    for c in vc_ng:
        targets = []
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c)
                nc[p] = move_entries[key]
                nc = tuple(nc)
                if nc in vc_ng:
                    targets.append(nc)
        out_targets[c] = targets

    # Peel
    remaining = set(vc_ng)
    while True:
        sinks = []
        for c in remaining:
            if not any(t in remaining for t in out_targets[c]):
                sinks.append(c)
        if not sinks:
            break
        for c in sinks:
            remaining.discard(c)

    return len(remaining)


def run_multiset(ms, n, L_max, target):
    """Exhaustive enumeration + inline SK check for one multiset."""
    all_starts = list(iproduct(*[range(m) for m in ms]))
    seen_fps = {}  # det_fingerprint -> SK value
    total_raw = 0
    violations = []
    min_sk = float('inf')
    L_counts = defaultdict(int)

    def det_fp(det):
        return frozenset((k, v) for k, v in det.items() if v != k[2])

    def dfs(start, config, det, path, movers, path_set):
        nonlocal total_raw, min_sk

        if len(path) > 1 and config == start:
            if set(movers) == set(range(n)):
                total_raw += 1
                fp = det_fp(det)
                if fp not in seen_fps:
                    L = len(movers)
                    sk = compute_sk_inline(ms, n, det, path[:L])
                    seen_fps[fp] = sk
                    L_counts[L] += 1
                    if sk < min_sk:
                        min_sk = sk
                    if sk < target:
                        violations.append((L, sk, tuple(ms)))
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
                if nc in path_set and nc != start:
                    continue

                new_ps = path_set | {nc} if nc != start else path_set
                dfs(start, nc, new_det, path + [nc], movers + [p], new_ps)

    t0 = time.time()
    for si, start in enumerate(all_starts):
        dfs(start, start, {}, [start], [], {start})
        if (si + 1) % 10 == 0 or si == len(all_starts) - 1:
            elapsed = time.time() - t0
            sys.stdout.write(
                f"\r    [{si+1}/{len(all_starts)}] {elapsed:.0f}s  "
                f"raw={total_raw}  dets={len(seen_fps)}  min_sk={min_sk}")
            sys.stdout.flush()
    print()

    return {
        'raw': total_raw,
        'dets': len(seen_fps),
        'min_sk': min_sk,
        'violations': violations,
        'L_counts': dict(L_counts),
        'time': time.time() - t0,
    }


def main():
    n = 5
    Mn = m_n_sharp(n)
    target = 2 ** (n - 1)
    L_max = 30

    print("=" * 72)
    print(f"EXHAUSTIVE SK VERIFICATION v3: n={n}, 2^(n-1)={target}")
    print("=" * 72)

    multisets = enumerate_mixed_multisets(n, Mn)
    print(f"Mixed sub-M_{n} multisets: {len(multisets)}")

    grand_raw = 0
    grand_dets = 0
    grand_violations = 0
    grand_min_sk = float('inf')
    grand_min_info = None
    by_L = defaultdict(lambda: {'count': 0, 'min_sk': float('inf')})

    for mi, ms in enumerate(multisets):
        prod = 1
        for m in ms:
            prod *= m
        print(f"\n[{mi+1}/{len(multisets)}] ms={ms} product={prod}")

        r = run_multiset(ms, n, L_max, target)
        grand_raw += r['raw']
        grand_dets += r['dets']
        grand_violations += len(r['violations'])

        if r['min_sk'] < grand_min_sk:
            grand_min_sk = r['min_sk']
            grand_min_info = ms

        for L, cnt in r['L_counts'].items():
            by_L[L]['count'] += cnt
            by_L[L]['min_sk'] = min(by_L[L]['min_sk'], r['min_sk'])

        Ls = ", ".join(f"L={L}:{c}" for L, c in sorted(r['L_counts'].items()))
        v = len(r['violations'])
        print(f"  dets={r['dets']}  raw={r['raw']}  min_SK={r['min_sk']}  "
              f"{'OK' if v == 0 else f'{v} VIOLATIONS'}  ({r['time']:.1f}s)")
        print(f"  L: {Ls}")

        for L, sk, ms2 in r['violations']:
            print(f"  *** VIOLATION: L={L} |SK|={sk} ***")

    print(f"\n{'='*72}")
    print(f"FINAL: {len(multisets)} multisets, {grand_dets} dets, "
          f"{grand_raw} raw cycles")
    print(f"  Min SK: {grand_min_sk} (at ms={grand_min_info})")
    print(f"  Violations: {grand_violations}")
    if grand_violations == 0:
        print(f"\n  *** LEMMA C VERIFIED AT n={n}: |SK| >= {target} ***")
    else:
        print(f"\n  *** LEMMA C FAILED ***")


if __name__ == "__main__":
    main()
