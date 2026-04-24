#!/usr/bin/env python3
"""Test the 'extended binary projection' hypothesis for Lemma C-weak:

Hypothesis: at L >= 2n+2, SK contains the binary subcube (mod cycle + sinks)
with only O(L - 2n) extra sinks compared to the L=2n case.

For each cycle, compute:
  - binary_cycle_count = |C ∩ B(C)| where B(C) = binary subcube of the
    cycle's "most used" 2 values per position
  - binary_subcube_size = 2^n (the cube itself)
  - binary_sk = |SK ∩ B(C)|
  - diff = 2^n - 2n - 2*[n odd] - binary_sk  (deviation from Lemma A)

If diff is small (O(L-2n)), the extended projection works.
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


def compute_value_ranges(cycle, n):
    """V_i = set of values at position i across the cycle."""
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def compute_sk_with_projection(ms, n, cycle, det):
    """Compute full SK and project it to binary subspace defined by
    the 'most-visited' 2 values at each position."""
    V = compute_value_ranges(cycle, n)
    # For each position, pick the 2 most-visited values from V_i
    count_by_pos = [defaultdict(int) for _ in range(n)]
    for c in cycle:
        for i in range(n):
            count_by_pos[i][c[i]] += 1
    binary_choice = []
    for i in range(n):
        vals = sorted(count_by_pos[i].keys(), key=lambda v: -count_by_pos[i][v])[:2]
        if len(vals) < 2:
            # Only 1 distinct value (shouldn't happen if proc fires)
            vals = list(V[i]) + [v for v in range(ms[i]) if v not in V[i]]
            vals = vals[:2]
        binary_choice.append(tuple(sorted(vals)))
    # A config is 'binary' if each c[i] is in binary_choice[i]
    def is_binary(c):
        return all(c[i] in binary_choice[i] for i in range(n))

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

    sk = remaining
    binary_sk = {c for c in sk if is_binary(c)}
    binary_cycle_configs = {c for c in cycle if is_binary(c)}

    return len(sk), len(binary_sk), len(binary_cycle_configs)


def main():
    print("=" * 80, flush=True)
    print("Binary containment probe: does SK contain the binary subcube?", flush=True)
    print("=" * 80, flush=True)

    results = []
    plan = [
        (5, 1, 1000, 8.0, 16),
        (6, 3,  500, 6.0, 18),
    ]
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n:
                    continue
                sk, bin_sk, bin_cycle = compute_sk_with_projection(ms, n, cycle, det)
                results.append((n, ms, L, sk, bin_sk, bin_cycle))
            if (idx + 1) % 10 == 0:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s  results={len(results)}", flush=True)

    print(f"\n  total records: {len(results)}", flush=True)

    # Analysis: for each (n, L), compute:
    #   - min(bin_sk)   (worst case binary-SK size)
    #   - mean(bin_sk / 2^n)  (fraction of binary cube in SK)
    #   - Lemma A predicted value 2^n - 2n - 2[n odd] vs actual min
    by_nL = defaultdict(list)
    for n, ms, L, sk, bin_sk, bin_cycle in results:
        by_nL[(n, L)].append((sk, bin_sk, bin_cycle, ms))

    print(f"\n  === binary-SK analysis ===", flush=True)
    print(f"    n  L   count  min_bin_SK  max_bin_SK  mean  lemA  gap_bin_SK", flush=True)
    for (n, L) in sorted(by_nL.keys()):
        vs = by_nL[(n, L)]
        bin_sks = [v[1] for v in vs]
        mn = min(bin_sks); mx = max(bin_sks); mean = sum(bin_sks) / len(bin_sks)
        lemA = 2**n - 2*n - (2 if n % 2 == 1 else 0)
        gap = lemA - mn
        print(f"    {n}  {L:2d}  {len(vs):5d}  {mn:8d}  {mx:8d}  {mean:6.1f}  "
              f"{lemA:4d}  {gap:+4d}", flush=True)

    # Histogram: how often is bin_sk close to 2^n - 2n - 2[n odd]?
    print(f"\n  === binary SK vs Lemma A deviation ===", flush=True)
    deviations = Counter()
    for n, ms, L, sk, bin_sk, bin_cycle in results:
        lemA = 2**n - 2*n - (2 if n % 2 == 1 else 0)
        dev = lemA - bin_sk  # positive = bin_sk below Lemma A
        deviations[(n, dev)] += 1
    for (n, dev), cnt in sorted(deviations.items()):
        print(f"    n={n}  dev={dev:+4d}  count={cnt}", flush=True)


if __name__ == "__main__":
    main()
