#!/usr/bin/env python3
"""Parametric wavefront verification (n=10, 11) + n=9 tail variant check.

Part A: n=10 and n=11 witness SK + ternary-strip wavefront analysis.
        Target: confirm the three-phase wavefront with uniform
        value-0 and linearly-interpolated value-1/value-2 splits.

Part B: n=9 tail variants with k=3 binary at 3CB positions but
        different outer structure. Confirm that the SK binary-cube
        projection matches the canonical 10-edge skeleton
        *regardless* of which tail multiset at fixed n.

The point of both experiments is to isolate n-independent structural
claims suitable for the Lean proof.
"""

from itertools import product as iproduct
from collections import defaultdict, Counter
import time


def build_bounce_cycle(n):
    """Build the n≥9 CLB witness bounce cycle for ms=(2,3^(n-2),2).

    Returns (ms, cycle, movers) or (ms, None, None) if it doesn't close.
    """
    ms = tuple([2] + [3] * (n - 2) + [2])
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (n + 5)
    movers = None
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            movers = full[:step + 1]
            break
        if nc in visited:
            return ms, None, None
        visited.add(nc)
        cycle.append(nc)
    return ms, cycle, movers


def extract_det_from_cycle(cycle, movers, ms, n):
    det = {}
    L = len(cycle)
    for idx in range(L):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % L]
        mv = movers[idx]
        for p in range(n):
            Lm = c[(p - 1) % n]
            Sm = c[p]
            Rm = c[(p + 1) % n]
            key = (p, Lm, Sm, Rm)
            if p == mv:
                if key in det and det[key] != c_next[p]:
                    return None
                det[key] = c_next[p]
            else:
                if key in det and det[key] != Sm:
                    return None
                det[key] = Sm
    return det


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


# -------- Part A: n=10, 11 witness wavefront analysis --------
def analyze_witness(n):
    ms, cycle, movers = build_bounce_cycle(n)
    if cycle is None:
        print(f"  n={n}: bounce didn't close")
        return None
    print(f"\n===== WITNESS n={n}  ms={ms} =====")
    print(f"  cycle length: {len(cycle)}")
    print(f"  mover sequence: {movers}")

    det = extract_det_from_cycle(cycle, movers, ms, n)
    if det is None:
        print("  det extraction failed")
        return None
    good_set = set(cycle)
    ng, _, adj = build_forced_graph(ms, n, det, good_set)
    sk, rounds = sink_kernel(ng, adj)
    print(f"  |det|={len(det)}  |non-good|={len(ng)}  "
          f"|SK|={len(sk)}  (rounds={rounds})")

    # Per-position value distribution.
    tpos = [i for i, m in enumerate(ms) if m != 2]
    print(f"  ternary positions: {tpos}")
    print(f"  per-position value distribution:")
    L_0_values = []
    L_pair_values = []
    for idx, tp in enumerate(tpos):
        counts = Counter(c[tp] for c in cycle)
        print(f"    pos {tp}: {{0:{counts.get(0,0)}, 1:{counts.get(1,0)}, "
              f"2:{counts.get(2,0)}}}")
        L_0_values.append(counts.get(0, 0))
        L_pair_values.append((counts.get(1, 0), counts.get(2, 0)))

    l0_const = len(set(L_0_values)) == 1
    print(f"  value 0 constant across positions? {l0_const}  "
          f"(L_0 = {L_0_values[0] if l0_const else L_0_values})")

    pair_sum = [a + b for a, b in L_pair_values]
    pair_sum_const = len(set(pair_sum)) == 1
    print(f"  L_1 + L_2 constant? {pair_sum_const}  "
          f"(sum = {pair_sum[0] if pair_sum_const else pair_sum})")

    # Linearity check: L_1 should decrease by constant across positions.
    L_1s = [a for a, b in L_pair_values]
    diffs = [L_1s[i+1] - L_1s[i] for i in range(len(L_1s) - 1)]
    linear = len(set(diffs)) == 1
    print(f"  L_1 interpolation linear? {linear}  "
          f"(diffs = {diffs})")

    # Binary projection
    bpos = [i for i, m in enumerate(ms) if m == 2]
    bproj_good = Counter(tuple(c[i] for i in bpos) for c in cycle)
    print(f"  good cycle binary projection (k={len(bpos)}): {dict(bproj_good)}")

    return {
        "n": n, "cycle_len": len(cycle),
        "L_0": L_0_values[0] if l0_const else None,
        "L_1_seq": L_1s,
        "L_diffs": diffs,
        "sk_size": len(sk),
        "rounds": rounds,
    }


# -------- Part B: n=9 tail variants, canonical skeleton check --------
def enumerate_sweep_cycles(ms, n, max_found=5, time_budget=60.0):
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
                cycle_tup = tuple(path)
                if cycle_tup not in seen:
                    seen.add(cycle_tup)
                    found.append((list(path), list(mover_seq), dict(det)))
            return
        p = mover_seq[step]
        Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
        key_m = (p, Lp, Sp, Rp)
        forced_out = det.get(key_m)
        for new_val in range(ms[p]):
            if new_val == Sp: continue
            if forced_out is not None and forced_out != new_val: continue
            new_det = dict(det)
            new_det[key_m] = new_val
            consistent = True
            for i in range(n):
                if i == p: continue
                Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]
                ki = (i, Li, Si, Ri)
                if ki in new_det and new_det[ki] != Si:
                    consistent = False; break
                new_det[ki] = Si
            if not consistent: continue
            nc = list(config); nc[p] = new_val; nc = tuple(nc)
            if step + 1 < L and nc in set(path):
                continue
            dfs(step+1, nc, new_det, path + [nc])

    for start in all_starts:
        if len(found) >= max_found or time.time() - t0 > time_budget:
            break
        dfs(0, start, {}, [start])
    return found


CANON_6CYC_REV = [
    ((0,1,1),(0,0,1)), ((0,1,0),(0,1,1)), ((1,1,0),(0,1,0)),
    ((1,0,0),(1,1,0)), ((1,0,1),(1,0,0)), ((0,0,1),(1,0,1)),
]
CANON_UA = [
    ((0,0,1),(0,0,0)), ((0,0,0),(1,0,0)),
    ((1,1,0),(1,1,1)), ((1,1,1),(0,1,1)),
]


def analyze_tail(ms, label):
    n = len(ms)
    P = 1
    for m in ms: P *= m
    print(f"\n===== TAIL {label}  ms={ms}  n={n}  product={P} =====")

    cycles = enumerate_sweep_cycles(ms, n, max_found=5, time_budget=60.0)
    print(f"  sweep cycles found: {len(cycles)}")
    if not cycles:
        return None

    cycle, movers, det_c = cycles[0]
    good_set = set(cycle)
    ng, _, adj = build_forced_graph(ms, n, det_c, good_set)
    sk, rounds = sink_kernel(ng, adj)

    bpos = [i for i, m in enumerate(ms) if m == 2]
    verts = set()
    edges = set()
    kset = set(sk)
    for u in sk:
        verts.add(tuple(u[i] for i in bpos))
        for v, p in adj.get(u, ()):
            if v not in kset: continue
            if p in bpos:
                bu = tuple(u[i] for i in bpos)
                bv = tuple(v[i] for i in bpos)
                if bu != bv:
                    edges.add((bu, bv))
    print(f"  |SK|={len(sk)}  rounds={rounds}  |verts|={len(verts)}  "
          f"|edges|={len(edges)}")

    # Check canonical skeleton (only meaningful for k=3).
    k = len(bpos)
    if k == 3:
        rev6 = sum(1 for e in CANON_6CYC_REV if e in edges)
        ua = sum(1 for e in CANON_UA if e in edges)
        other = sum(1 for e in edges if e not in CANON_6CYC_REV
                    and e not in CANON_UA)
        print(f"  canonical skeleton: rev6={rev6}/6 ua={ua}/4 other={other}")
        print(f"  matches canonical? {rev6 == 6 and ua == 4 and other == 0}")
    return {"ms": ms, "sk": len(sk), "edges": len(edges)}


def main():
    print("=" * 70)
    print("PART A: n=10, n=11 witness wavefront extension")
    print("=" * 70)
    results_a = []
    for n in [10, 11]:
        r = analyze_witness(n)
        if r:
            results_a.append(r)

    print("\n" + "=" * 70)
    print("PARAMETRIC WAVEFRONT SUMMARY")
    print("=" * 70)
    print(f"{'n':<4}{'cycle_len':<12}{'|SK|':<8}{'rounds':<10}"
          f"{'L_0':<6}{'L_1_seq':<40}")
    # Also include n=9 from memory.
    known_n9 = {
        "n": 9, "cycle_len": 25, "sk_size": 0, "rounds": 18,
        "L_0": 9, "L_1_seq": [14,12,10,8,6,4,2], "L_diffs": [-2,-2,-2,-2,-2,-2]
    }
    all_results = [known_n9] + results_a
    for r in all_results:
        print(f"{r['n']:<4}{r['cycle_len']:<12}{r['sk_size']:<8}"
              f"{r['rounds']:<10}{str(r['L_0']):<6}{str(r['L_1_seq']):<40}")

    print("\n" + "=" * 70)
    print("PART B: n=9 tail variants — n-independent canonical skeleton check")
    print("=" * 70)

    variants = [
        # ms, label
        ((2,2,2,3,3,3,3,3,3), "pure-ternary (3CB at 0,1,2)"),
        ((2,2,2,3,3,3,3,3,4), "3CB at 0,1,2 + quaternary at 8"),
        ((2,2,2,3,3,3,3,4,3), "3CB at 0,1,2 + quaternary at 7"),
    ]
    results_b = []
    for ms, label in variants:
        r = analyze_tail(ms, label)
        if r:
            results_b.append(r)


if __name__ == "__main__":
    main()
