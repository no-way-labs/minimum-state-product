#!/usr/bin/env python3
"""Exhaustive binary-ms SK enumeration — step 1 of 100% small-n SK.

For each n in {5,6,7,8,9}, at ms = (2,...,2), enumerate every fair
closed det-consistent cycle up to length L_max = k*n (k growing).
For each cycle, compute |SK| and verify it equals 2^n - 2n - eps(n).

This is the strongest empirical bedrock for the |SK|(n) closed form.
Probe 5 found 500 cycles per n with a max_found cap; this probe
removes the cap and pushes L_max up.

Goals:
  - n = 5, 6: reach L_max = 4n (= 20, 24), enumerate every fair
    closed cycle
  - n = 7, 8, 9: reach L_max = 3n (= 21, 24, 27), enumerate as many
    cycles as time allows
  - Report: (a) cycle count per n, (b) |SK| histogram, (c) any
    violations of |SK| = 2^n - 2n - eps(n).

If zero violations across 10k+ cycles, the empirical statement
strengthens to: every fair closed binary cycle of length <= k*n on
ms=(2,...,2) has |SK| = 2^n - 2n - eps(n). Combined with step 2's
rigorous Lemma A, this is a theorem on the all-binary multiset.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import math
import sys

sys.setrecursionlimit(10000)


def enumerate_all_binary_cycles(n, L_max, time_budget=600.0, progress_every=5000):
    """Exhaustive DFS over fair closed binary cycles up to length L_max."""
    ms = tuple([2] * n)
    all_starts = list(iproduct(*[range(2)] * n))
    found = []
    seen_cycles = set()
    t0 = time.time()
    steps = [0]

    def dfs(start, config, det, path, movers):
        if time.time() - t0 > time_budget:
            return
        steps[0] += 1
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)):
                return
            # normalize: pick lexicographically smallest rotation
            L = len(path)
            norm = min(tuple(path[i:] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path), list(movers), dict(det)))
                if len(found) % progress_every == 0:
                    print(f"    ... {len(found)} cycles found, {time.time()-t0:.1f}s elapsed", flush=True)
            return
        if len(path) >= L_max:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            new_val = 1 - Sp
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
        if time.time() - t0 > time_budget:
            print(f"    TIME BUDGET HIT after start {start}", flush=True)
            break
        dfs(start, start, {}, [start], [])
    return found, (time.time() - t0)


def build_forced_graph_and_sk(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
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
    return len(remaining), remaining


def expected_sk(n):
    return 2 ** n - 2 * n - (2 if n % 2 == 1 else 0)


def main():
    print("=" * 90, flush=True)
    print("Exhaustive binary-ms SK enumeration (step 1 — 100% small-n SK)", flush=True)
    print("=" * 90, flush=True)

    # n -> L_max; we pick feasible limits per n
    plans = [
        (5, 20),  # 4n
        (6, 24),  # 4n
        (7, 21),  # 3n
        (8, 24),  # 3n
        (9, 27),  # 3n
    ]

    overall_violations = []

    for n, L_max in plans:
        expected = expected_sk(n)
        ms = tuple([2] * n)
        print(f"\n=== n={n}  ms={ms}  L_max={L_max}  expected |SK|={expected} ===", flush=True)
        cycles, elapsed = enumerate_all_binary_cycles(n, L_max, time_budget=900.0)
        print(f"  enumerated {len(cycles)} distinct fair closed binary cycles in {elapsed:.1f}s", flush=True)

        sk_counts = Counter()
        violations = []
        length_dist = Counter()
        for cycle, movers, det in cycles:
            good = set(cycle)
            sk_size, _ = build_forced_graph_and_sk(ms, n, det, good)
            sk_counts[sk_size] += 1
            length_dist[len(cycle)] += 1
            if sk_size != expected:
                violations.append((cycle, movers, sk_size))

        print(f"  cycle length histogram: {dict(sorted(length_dist.items()))}", flush=True)
        print(f"  |SK| histogram: {dict(sorted(sk_counts.items()))}", flush=True)
        if violations:
            print(f"  !!! {len(violations)} violations of expected |SK|={expected}", flush=True)
            for c, m, sk in violations[:5]:
                print(f"      len={len(c)}  |SK|={sk}  movers={m}", flush=True)
            overall_violations.extend([(n, v) for v in violations])
        else:
            print(f"  ✓ all {len(cycles)} cycles have |SK| = {expected}", flush=True)

    print("\n" + "=" * 90, flush=True)
    print("SUMMARY", flush=True)
    print("=" * 90, flush=True)
    if not overall_violations:
        print("All cycles across all n match the closed form.", flush=True)
        print("Empirical statement: for every fair closed binary cycle of length <= k*n", flush=True)
        print("on ms=(2,...,2), |SK| = 2^n - 2n - 2*[n odd].", flush=True)
    else:
        print(f"VIOLATIONS FOUND: {len(overall_violations)}", flush=True)
        for n, (c, m, sk) in overall_violations[:10]:
            print(f"  n={n}  len={len(c)}  |SK|={sk}", flush=True)


if __name__ == "__main__":
    main()
