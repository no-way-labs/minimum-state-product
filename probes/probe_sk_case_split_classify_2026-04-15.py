#!/usr/bin/env python3
"""Verify 4-mechanism case-split exhaustiveness — task A.

For every fair simple closed cycle we can enumerate on every sub-M_n
multiset at n=5..7, classify the cycle into one of:

  Case 1: sweep (length 2n, mover seq is a rotation of [0,1,...,n-1,0,1,...,n-1])
  Case 2: non-sweep fc=2 (length 2n, not a sweep), ms has 3 consecutive binary
  Case 3: non-sweep fc=2 (length 2n, not a sweep), ms has >=3 binary but not 3-consecutive
  Case 4: length > 2n (wiggle or beyond)

Report:
  - cycles per case
  - any cycle that doesn't fit (shouldn't happen if exhaustiveness holds)
  - sub-classes of Case 4 by length

Key questions:
  - Are there length-(2n+2) "single wiggle" cycles? Case 4a.
  - Are there length-(2n+4) or longer "multi-wiggle" cycles? Case 4b (new!).
  - If Case 4b exists, the Wiggle Shadow Cycle theorem (single-wiggle only) doesn't cover them, revealing a 5th case.
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


def enumerate_all_cycles(ms, n, L_max, time_budget=20.0, max_cycles=10000):
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
            L = len(path)
            norm = min(tuple(path[i:] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path), list(movers), dict(det)))
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


def is_sweep(movers, n):
    """Is mover sequence a rotation of [0,1,...,n-1,0,1,...,n-1]?"""
    if len(movers) != 2 * n:
        return False
    canonical = list(range(n)) * 2
    for shift in range(2 * n):
        rotated = movers[shift:] + movers[:shift]
        if rotated == canonical:
            return True
    return False


def has_3_consecutive_binary(ms):
    """Does ms have 3 consecutive positions with m_i = 2?"""
    n = len(ms)
    for i in range(n):
        if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
            return True
    return False


def classify_cycle(cycle, movers, ms, n):
    """Return case name: 'sweep', 'fc2_3CB', 'fc2_non3CB', 'wiggle_plus2', 'multi_wiggle', or 'unclassified'.

    cycle is the path list [start, c1, ..., start] so len(cycle) = actual_length + 1.
    Use len(movers) as the true cycle length.
    """
    L = len(movers)
    fc = Counter(movers)
    max_fc = max(fc.values())

    if L == 2 * n:
        # Every proc fires exactly 2 times (fc=2)
        if is_sweep(movers, n):
            return 'sweep'
        if has_3_consecutive_binary(ms):
            return 'fc2_3CB'
        return 'fc2_non3CB'
    elif L == 2 * n + 2:
        return 'wiggle_plus2'  # single wiggle
    elif L > 2 * n + 2:
        return f'multi_wiggle_len{L}'
    else:
        return 'unclassified'  # L < 2n; shouldn't happen with fairness


def main():
    print("=" * 90, flush=True)
    print("Case-split exhaustiveness verification (task A)", flush=True)
    print("=" * 90, flush=True)

    overall_counts = Counter()
    unclassified_examples = []
    multi_wiggle_examples = []

    for n in [5, 6, 7]:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        # For n=5, exhaustive; n=6, half; n=7, sample
        if n == 6:
            multisets = multisets[::2]
        if n == 7:
            multisets = multisets[::8]  # 103 sampled, like prior
        print(f"\n=== n={n}  {len(multisets)} multisets  L_max=2n+4={2*n+4} ===", flush=True)
        counts = Counter()
        t0 = time.time()
        total = 0
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max=2*n+4, time_budget=10.0, max_cycles=5000)
            for cycle, movers, det in cycles:
                total += 1
                cls = classify_cycle(cycle, movers, ms, n)
                counts[cls] += 1
                overall_counts[(n, cls)] += 1
                if cls == 'unclassified':
                    if len(unclassified_examples) < 5:
                        unclassified_examples.append((n, ms, cycle, movers))
                if cls.startswith('multi_wiggle'):
                    if len(multi_wiggle_examples) < 10:
                        multi_wiggle_examples.append((n, ms, cycle, movers, cls))
            if (idx + 1) % 20 == 0:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(multisets)}]  {elapsed:.0f}s  total={total}  classes={dict(counts)}", flush=True)
        print(f"  n={n} final: total={total}  classes={dict(counts)}", flush=True)

    print("\n" + "=" * 90, flush=True)
    print("OVERALL", flush=True)
    print("=" * 90, flush=True)
    for (n, cls), cnt in sorted(overall_counts.items()):
        print(f"  n={n} {cls}: {cnt}")
    print(f"\n  unclassified total: {sum(v for (n,c),v in overall_counts.items() if c == 'unclassified')}", flush=True)
    print(f"  multi_wiggle total: {sum(v for (n,c),v in overall_counts.items() if c.startswith('multi_wiggle'))}", flush=True)

    if unclassified_examples:
        print("\n  UNCLASSIFIED examples:", flush=True)
        for n, ms, cycle, movers in unclassified_examples:
            print(f"    n={n} ms={ms} len={len(cycle)} movers={movers}", flush=True)

    if multi_wiggle_examples:
        print("\n  MULTI-WIGGLE examples (potential 5th case):", flush=True)
        for n, ms, cycle, movers, cls in multi_wiggle_examples:
            print(f"    n={n} ms={ms} cls={cls} movers={movers}", flush=True)


if __name__ == "__main__":
    main()
