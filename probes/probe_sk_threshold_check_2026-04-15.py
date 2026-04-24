#!/usr/bin/env python3
"""SK threshold sanity check: does SK detect invalidity at sub-4·3^(n-2)
for n=5..8, or only at sub-M_n?

For each n in {5..8}, we know the sharp M_n (32·3^(n-4)) and the SK
threshold I claimed (4·3^(n-2)). M_n < 4·3^(n-2) for n=5..8, so there
exist VALID systems with k ≥ 3 binary at products in (M_n, 4·3^(n-2)).
The classic example is ms=(2,2,2,3,4) at n=5, product 96 (= M_5).

If T2 (`tail_skeleton`) is correct as currently stated — "for any
sub-4·3^(n-2) candidate cycle with k ≥ 3 binary, SK contains the 4
pole edges" — then running SK on a sweep cycle for ms=(2,2,2,3,4) at
n=5 should find SK non-empty. But the system is VALID, which means
its actual good cycle has SK empty. If the actual good cycle is a
sweep, then T2 is empirically false at the 4·3^(n-2) threshold.

This probe checks: at n=5..8 with ms reaching for the M_n witness,
do sweep candidate cycles have empty or non-empty SK?

Output → updates SK targets doc and kickoff prompt.
"""

from itertools import product as iproduct
from collections import defaultdict
import time
import math


def enumerate_sweep_cycles(ms, n, max_found=3, time_budget=60.0):
    mover_seq = list(range(n)) * 2
    L = len(mover_seq)
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen = set()
    t0 = time.time()

    def dfs(step, config, det, path):
        if len(found) >= max_found or time.time() - t0 > time_budget:
            return
        if step == L:
            if config == path[0]:
                ct = tuple(path)
                if ct not in seen:
                    seen.add(ct)
                    found.append((list(path), list(mover_seq), dict(det)))
            return
        p = mover_seq[step]
        Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
        km = (p, Lp, Sp, Rp)
        forced_out = det.get(km)
        for new_val in range(ms[p]):
            if new_val == Sp: continue
            if forced_out is not None and forced_out != new_val: continue
            new_det = dict(det)
            new_det[km] = new_val
            ok = True
            for i in range(n):
                if i == p: continue
                Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    ok = False; break
                new_det[ki] = Si
            if not ok: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            if step + 1 < L and nc in set(path):
                continue
            dfs(step+1, nc, new_det, path + [nc])

    for start in all_starts:
        if len(found) >= max_found or time.time() - t0 > time_budget:
            break
        dfs(0, start, {}, [start])
    return found


def build_forced_graph(ms, n, det, good_set):
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]
    ng_set = set(non_good)
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p-1)%n]; Sp = c[p]; Rp = c[(p+1)%n]
            key = (p, Lp, Sp, Rp)
            if key in det and det[key] != Sp:
                nc = list(c); nc[p] = det[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append((nc, p))
    return non_good, ng_set, adj


def sink_kernel(non_good, adj):
    remaining = set(non_good)
    rounds = 0
    while True:
        sinks = set()
        for c in remaining:
            has_out = False
            for tgt, _ in adj.get(c, []):
                if tgt in remaining:
                    has_out = True
                    break
            if not has_out:
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
        rounds += 1
    return remaining, rounds


def m_n_sharp(n):
    """The conjectured/proved sharp M_n value."""
    if n == 4: return 24
    if 5 <= n <= 8: return 32 * 3**(n-4)
    return 4 * 3**(n-2)  # n >= 9


def main():
    cases = [
        # (ms, n, label, why-interesting)
        # n=5: M_5 = 96, sub-4·3^(n-2) bound is 108
        ((2,2,2,3,3),  5, "n5 (2,2,2,3,3)",  "product 72, sub-M_5 (k=3 binary)"),
        ((2,2,2,3,4),  5, "n5 (2,2,2,3,4)",  "product 96 = M_5 EXACT (k=3 binary, valid system)"),
        ((2,2,2,4,3),  5, "n5 (2,2,2,4,3)",  "product 96 = M_5, k=3 binary, alt placement"),
        # n=6: M_6 = 288, sub-4·3^(n-2) bound is 324
        ((2,2,2,3,3,3), 6, "n6 (2,2,2,3^3)",   "product 216, sub-M_6"),
        ((2,2,2,3,3,4), 6, "n6 (2,2,2,3,3,4)", "product 288 = M_6 EXACT"),
        ((2,2,2,3,4,3), 6, "n6 (2,2,2,3,4,3)", "product 288 = M_6 alt"),
        # n=7: M_7 = 864, sub-4·3^(n-2) bound is 972
        ((2,2,2,3,3,3,3), 7, "n7 (2,2,2,3^4)",     "product 648, sub-M_7"),
        ((2,2,2,3,3,3,4), 7, "n7 (2,2,2,3,3,3,4)", "product 864 = M_7 EXACT"),
        # n=8: M_8 = 2592, sub-4·3^(n-2) bound is 2916
        ((2,2,2,3,3,3,3,3), 8, "n8 (2,2,2,3^5)",       "product 1944, sub-M_8"),
        ((2,2,2,3,3,3,3,4), 8, "n8 (2,2,2,3,3,3,3,4)", "product 2592 = M_8 EXACT"),
        # n=9: M_9 = 8748 = 4·3^7
        ((2,3,3,3,3,3,3,3,2), 9, "n9 CLB witness", "product 8748 = M_9 (CLB witness, k=2)"),
    ]

    print("=" * 90)
    print("SK threshold sanity check at n=5..9")
    print("=" * 90)
    print()
    print(f"{'case':<25} {'n':<3} {'product':<8} {'M_n':<6} {'4·3^(n-2)':<10} "
          f"{'cycles':<7} {'min |SK|':<10} {'verdict'}")
    print("-" * 100)

    for ms, n, label, why in cases:
        product = math.prod(ms)
        Mn = m_n_sharp(n)
        sk_threshold = 4 * 3 ** (n - 2)
        cycles = enumerate_sweep_cycles(ms, n, max_found=5, time_budget=60.0)

        if not cycles:
            verdict = "no sweep cycle found"
            min_sk = "—"
            print(f"{label:<25} {n:<3} {product:<8} {Mn:<6} {sk_threshold:<10} "
                  f"{0:<7} {min_sk:<10} {verdict}")
            continue

        sk_sizes = []
        for cycle, movers, det in cycles:
            good_set = set(cycle)
            ng, _, adj = build_forced_graph(ms, n, det, good_set)
            sk, rounds = sink_kernel(ng, adj)
            sk_sizes.append(len(sk))
        min_sk = min(sk_sizes)

        # Verdict logic:
        #  - If product < M_n: expect |SK| > 0 always (system invalid)
        #  - If product = M_n: expect SOME cycle to have |SK| = 0 (valid system has empty SK on its actual cycle)
        #  - If product < 4·3^(n-2) but ≥ M_n: this is the gap zone
        if product < Mn:
            expected = "expect SK > 0 (invalid)"
            verdict = "OK" if min_sk > 0 else "??? all SK > 0"
            verdict = "OK" if min_sk > 0 else "MISMATCH (expected SK > 0)"
        elif product == Mn:
            verdict = ("OK valid: SK=0 on some cycle" if min_sk == 0
                       else f"BUG? all sweep SK > 0 (min {min_sk}) — actual cycle non-sweep?")
        else:
            verdict = "above M_n (not testable)"

        print(f"{label:<25} {n:<3} {product:<8} {Mn:<6} {sk_threshold:<10} "
              f"{len(cycles):<7} {str(sk_sizes):<10} {verdict}")
        print(f"    {'':23} {why}")

    print()
    print("=" * 90)
    print("INTERPRETATION GUIDE")
    print("=" * 90)
    print("""
For n=5..8:
  M_n is strictly less than 4·3^(n-2). The 'gap zone' contains products
  where the system COULD be valid (M_n witness lives there) but my old
  T6 statement claims they're sub-threshold by 4·3^(n-2).

  - At product = M_n with k ≥ 3 binary: if SOME sweep cycle has |SK| = 0,
    then T2 (current statement) is empirically wrong: a sub-4·3^(n-2)
    system with k ≥ 3 binary can have empty SK. This means T2 must use
    a stricter threshold (or n ≥ 9).

  - At product < M_n with k ≥ 3 binary: |SK| > 0 expected.

For n ≥ 9:
  M_n = 4·3^(n-2). The CLB witness has k=2 binary, so T2 doesn't apply
  to it. T6 should fire only for n ≥ 9 in its current form.
""")


if __name__ == "__main__":
    main()
