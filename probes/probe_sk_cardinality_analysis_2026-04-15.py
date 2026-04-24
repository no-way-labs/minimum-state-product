#!/usr/bin/env python3
"""|SK|(n) closed form — probe 3 for hypothesis 3.

The previous probe (probe_sk_sub_mn_smalln_2026-04-15.py) reported a
surprising per-n invariance: for every sub-M_n multiset at n = 5..8,
|SK| was constant at 20, 52, 112, 240 respectively. Adding n=9 (from
probe_sk_n9_witness_2026-04-14.py) gives 492.

Empirical sequence: 20, 52, 112, 240, 492, ...

This script:

1. Verifies the sequence by re-computing |SK| on a canonical sub-M_n
   multiset at each n in 5..10 (at n=10 this is a prediction test).
2. Tests the closed form |SK|(n) = 2^n - 4·⌈n/2⌉, equivalently
     |SK|(n) = 2^n - 2n       if n even
     |SK|(n) = 2^n - 2n - 2   if n odd.
3. Examines the structural content of SK. Since |SK| ≈ 2^n, SK should
   be close to the binary hypercube {0,1}^n. We compute:
     - the value-profile breakdown of SK (how many positions are 0,1,2,...)
     - the "missing" configs — elements of {0,1}^n that are NOT in SK
     - whether the forced graph collapses to the binary subcube
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import math
import time


def enumerate_sweep_cycles(ms, n, max_found=3, time_budget=10.0):
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
        Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
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
                Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    ok = False; break
                new_det[ki] = Si
            if not ok: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            if step + 1 < L and nc in set(path):
                continue
            dfs(step + 1, nc, new_det, path + [nc])

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


def canonical_ms(n):
    """Pick a canonical sub-M_n multiset: all binary."""
    return tuple([2] * n)


def predicted(n: int) -> int:
    return 2 ** n - 4 * math.ceil(n / 2)


def analyze(n):
    ms = canonical_ms(n)
    cycles = enumerate_sweep_cycles(ms, n, max_found=3, time_budget=30.0)
    if not cycles:
        print(f"n={n} ms={ms}: no sweep cycle found")
        return
    cycle, movers, det = cycles[0]
    good = set(cycle)
    ng, _, adj = build_forced_graph(ms, n, det, good)
    sk = sink_kernel(ng, adj)
    sk_size = len(sk)
    pred = predicted(n)
    ok = "✓" if sk_size == pred else "✗"
    print(f"n={n} ms={ms}: |SK|={sk_size}  pred={pred}  {ok}")

    # Structural breakdown
    # 1. value-profile histogram: count by (sum of positions)
    weights = Counter(sum(c) for c in sk)
    # 2. what fraction of {0,1}^n is in SK?
    all_binary = set(iproduct(*[range(2)] * n))
    in_sk = sk & all_binary
    missing = all_binary - sk
    print(f"    SK ∩ {{0,1}}^n: {len(in_sk)} / {2**n}")
    print(f"    missing from SK: {len(missing)}")
    if len(missing) <= 30:
        for c in sorted(missing, key=lambda x: (sum(x), x)):
            print(f"      missing: {c}  (weight {sum(c)})")
    else:
        print(f"    (too many to list)")
    # 3. value-profile in SK
    print(f"    SK weight histogram: {dict(sorted(weights.items()))}")
    # 4. good cycle profile
    cycle_weights = Counter(sum(c) for c in cycle)
    print(f"    cycle weight histogram: {dict(sorted(cycle_weights.items()))}")
    return sk_size, pred


def main():
    print("=" * 90)
    print("|SK|(n) cardinality analysis — probe 3")
    print("=" * 90)
    print()
    print("Hypothesized closed form: |SK|(n) = 2^n - 4·⌈n/2⌉")
    print("i.e. 2^n - 2n for n even, 2^n - 2n - 2 for n odd")
    print()
    print("Canonical multiset: ms = (2,2,...,2) (all binary).")
    print("NOTE: ms=(2,...,2) is sub-M_n for n ≥ 5 since 2^n < M_n for n ≥ 5.")
    print()

    for n in [5, 6, 7, 8, 9, 10]:
        analyze(n)
        print()


if __name__ == "__main__":
    main()
