#!/usr/bin/env python3
"""Binary-cube exotic cycle enumeration for n=7,8 — task 5.

Rationale (from probe 4 / sk_binary_cube_lemma_2026-04-15.md Lemma A):
the forced graph of a SWEEP cycle on any ms reduces to the same
{0,1}^n structure as the all-binary ms. For EXOTIC cycles this is not
known to hold, so we need direct enumeration.

Probe 2 covered n=5,6 exotic cycles via free-DFS but skipped n=7,8
because of the branching factor. Here we exploit the structural
reduction: at ms = (2,…,2), each move has exactly one possible
new_val (the flip), so the branching factor in free-DFS is just n
(mover choice) per step, not n · max(m). This makes n=7,8 tractable
up to length ~2n+2.

This probe:
1. Enumerates every fair, det-consistent closed cycle at ms=(2,…,2)
   with length ≤ 2n+2 via free DFS.
2. Filters out sweep and bounce.
3. Computes SK for each; reports any |SK|=0.

Since at ms=(2,…,2) the SK has size 2^n - 2n - ε(n) > 0 for sweep+bounce
(verified at probe 3), the question is whether exotic cycles can
produce |SK|=0.

If no exotic cycle at ms=(2,…,2) gives |SK|=0, combined with Lemma A
(which extends SK structure from binary ms to general ms for SWEEP
cycles), we get a moderately strong statement:

> At n=7,8, no exotic short fair cycle (length ≤ 2n+2) on the
> all-binary multiset has empty SK. This does NOT directly rule out
> non-binary multisets, but it closes the most natural test.

Extended experiment: also run for n=9 to verify the trend.
"""
from itertools import product as iproduct
from collections import defaultdict
import time
import sys


def enumerate_free_binary_cycles(n, max_length, time_budget=60.0, max_found=200):
    """Fair closed cycles on ms=(2,…,2), free mover choice, length ≤ max_length."""
    ms = tuple([2] * n)
    all_starts = list(iproduct(*[range(2)] * n))
    found = []
    seen_cycles = set()
    t0 = time.time()

    def dfs(start, config, det, path, movers):
        if len(found) >= max_found or time.time() - t0 > time_budget:
            return
        if len(path) > 1 and config == start:
            # fairness filter
            if set(movers) != set(range(n)):
                return
            norm = min(tuple(path[i:] + path[:i]) for i in range(len(path)))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path), list(movers), dict(det)))
            return
        if len(path) >= max_length:
            return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp)
            forced_out = det.get(km)
            # At ms=(2,...,2), only one possible new_val: 1 - Sp
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
        if len(found) >= max_found or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def build_forced_graph(ms, n, det, good_set):
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
    return non_good, ng_set, adj


def sink_kernel(non_good, adj):
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


def is_sweep_or_bounce(movers, n):
    sweep = list(range(n)) * ((len(movers) + n - 1) // n)
    bounce = (list(range(n)) + list(range(n - 2, 0, -1))) * 2
    return movers == sweep[:len(movers)] or movers == bounce[:len(movers)]


def main():
    print("=" * 90, flush=True)
    print("Binary-cube exotic cycle enumeration (task 5) — n=7, 8, 9", flush=True)
    print("=" * 90, flush=True)

    for n in [7, 8, 9]:
        ms = tuple([2] * n)
        L_max = 2 * n + 2
        print(f"\n=== n={n}  ms={ms}  L_max={L_max} ===", flush=True)
        t0 = time.time()
        cycles = enumerate_free_binary_cycles(n, max_length=L_max, time_budget=120.0, max_found=500)
        elapsed = time.time() - t0
        print(f"  enumerated {len(cycles)} distinct fair closed cycles in {elapsed:.1f}s", flush=True)

        exotic_count = 0
        sweep_bounce_count = 0
        violations = []
        sk_sizes = []
        for cycle, movers, det in cycles:
            if is_sweep_or_bounce(movers, n):
                sweep_bounce_count += 1
                continue
            exotic_count += 1
            good = set(cycle)
            ng, _, adj = build_forced_graph(ms, n, det, good)
            sk = sink_kernel(ng, adj)
            sk_sizes.append(len(sk))
            if len(sk) == 0:
                violations.append((cycle, movers, det))

        print(f"  sweep/bounce: {sweep_bounce_count}  exotic: {exotic_count}", flush=True)
        if exotic_count:
            print(f"  exotic |SK| range: [{min(sk_sizes)}, {max(sk_sizes)}]", flush=True)
            from collections import Counter
            ct = Counter(sk_sizes)
            top = ct.most_common(5)
            print(f"  exotic |SK| histogram (top 5): {top}", flush=True)
        print(f"  violations (|SK|=0): {len(violations)}", flush=True)
        if violations:
            for c, m, d in violations[:3]:
                print(f"    FALSIFY: len={len(c)}  movers={m}", flush=True)

    print("\n" + "=" * 90, flush=True)
    print("INTERPRETATION", flush=True)
    print("=" * 90, flush=True)
    print("""
If exotic count > 0 and violations == 0: hypothesis 2 strengthens at
n=7,8,9 across short fair binary exotic cycles. Combined with Lemma A
(sk_binary_cube_lemma) this extends the sweep+bounce result from the
prior sub-M_n probe to the binary multiset on the exotic family.

If exotic count == 0: no short fair exotic binary cycles exist at
these n (length ≤ 2n+2). This would be a surprising structural fact:
the only fair short closed cycles on ms=(2,...,2) are sweep and bounce.

If violations > 0: hypothesis 2 is FALSE — inspect the reported
cycle.
""", flush=True)


if __name__ == "__main__":
    main()
