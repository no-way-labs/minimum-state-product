#!/usr/bin/env python3
"""Sub-cycle reduction test for Lemma C-weak.

Hypothesis: for every fair simple closed cycle C with |C| > 2n, there
exists a length-2n fair cycle C' on the same multiset with
det(C') ⊆ det(C).

By monotonicity of SK under det inclusion (adding entries can only
rescue sinks, never create them), |SK(C)| ≥ |SK(C')| = Lemma A
value = 2^n - 2n - 2*[n odd] ≥ 1.

Probe: for each C with L > 2n on small multisets at n=5, 6, enumerate
all length-2n fair cycles C' on the same multiset. Check if any
C' satisfies det(C') ⊆ det(C). Report:
  - coverage rate (fraction of L > 2n cycles that embed a length-2n cycle)
  - for any uncovered C, save as a counterexample
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


def enumerate_all_cycles(ms, n, L_min, L_max, time_budget, max_cycles):
    """Enumerate fair simple closed cycles with L_min <= L <= L_max."""
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


def det_firing_entries(det):
    """Return only the FIRING entries: (p, L, S, R) → S' with S' ≠ S.
    Non-firing entries (S' = S) are implicit from other positions being
    non-movers during a fire; we exclude them from sub-det comparison."""
    return frozenset(
        (k, v) for k, v in det.items() if v != k[2]
    )


def main():
    print("=" * 80, flush=True)
    print("Sub-cycle reduction test: L > 2n cycles embed length-2n cycles?", flush=True)
    print("=" * 80, flush=True)

    total_long = 0
    total_covered = 0
    counterexamples = []
    embed_stats = Counter()

    plan = [
        (5, 1,  500, 10.0, 16),
        (6, 5,  300,  8.0, 16),
    ]

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            # Enumerate all fair cycles, bucketed by length
            all_cycles = enumerate_all_cycles(
                ms, n, L_min=1, L_max=L_max, time_budget=tb, max_cycles=max_cycles)
            len_2n_cycles = [c for c in all_cycles if len(c[1]) == 2 * n]
            long_cycles = [c for c in all_cycles if len(c[1]) > 2 * n]

            sub_dets_2n = [det_firing_entries(det) for _, _, det in len_2n_cycles]
            if not sub_dets_2n:
                continue

            for cycle, movers, det in long_cycles:
                total_long += 1
                det_firings = det_firing_entries(det)
                # Check if any length-2n cycle's det is a subset
                covered = False
                for subdet in sub_dets_2n:
                    if subdet <= det_firings:
                        covered = True
                        break
                if covered:
                    total_covered += 1
                    embed_stats[('covered', n, len(movers))] += 1
                else:
                    embed_stats[('uncovered', n, len(movers))] += 1
                    if len(counterexamples) < 10:
                        counterexamples.append((n, ms, len(movers), list(movers)))

            if (idx + 1) % 5 == 0:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s  "
                      f"total_long={total_long}  covered={total_covered}", flush=True)

    print(f"\n  total L>2n cycles tested: {total_long}", flush=True)
    if total_long > 0:
        print(f"  covered (embed length-2n cycle): {total_covered} "
              f"({total_covered/total_long*100:.2f}%)", flush=True)
        print(f"  uncovered: {total_long - total_covered}", flush=True)

    print(f"\n  coverage by (n, L):", flush=True)
    all_nL = sorted(set((k[1], k[2]) for k in embed_stats.keys()))
    for n, L in all_nL:
        c = embed_stats.get(('covered', n, L), 0)
        u = embed_stats.get(('uncovered', n, L), 0)
        total = c + u
        if total > 0:
            print(f"    n={n}  L={L:2d}  covered={c:5d}  uncovered={u:5d}  "
                  f"({c/total*100:.1f}%)", flush=True)

    if counterexamples:
        print(f"\n  UNCOVERED counterexamples (first 10):", flush=True)
        for n, ms, L, mv in counterexamples:
            print(f"    n={n} ms={ms} L={L} movers={mv}", flush=True)


if __name__ == "__main__":
    main()
