#!/usr/bin/env python3
"""Exploration 1: Binary subgraph decomposition for SK Lemma C.

Key questions:
1. Is the binary forced graph ({0,1}^n ∩ NG) closed under the det?
   (i.e., do all binary-to-binary forced edges stay in the binary cube?)
2. Are there cross-edges from binary configs to non-binary targets?
   (i.e., det entries with binary input triple but non-binary output?)
3. What is the immune core of the strictly-binary forced subgraph?
4. Is binary_immune_core >= 2^(n-1)?
5. Transfer matrix: what is the no-match count for strictly binary configs?

Separates the problem into:
  - binary core (always large, bounded by transfer matrix)
  - non-binary extension (adds immune configs on top)
"""
from itertools import product as iproduct
from collections import defaultdict
import time
import numpy as np


def m_n_sharp(n):
    if 5 <= n <= 8:
        return 32 * 3 ** (n - 4)
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
                if nc != start and nc in set(path):
                    continue
                dfs(start, nc, new_det, path + [nc], movers + [p])

    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget:
            break
        dfs(start, start, {}, [start], [])
    return found


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def build_transfer_matrix(uncovered_triples_at_p):
    """Build 4x4 transfer matrix for position p.

    State = (c[p], c[p+1]) in {0,1}^2, indexed as 2*a + b.
    Transition from (a,b) to (b',d): allowed iff b=b' and (a,b,d) in U_p.

    M[(a,b), (b',d)] = [b=b'] * [(a,b,d) in U_p]
    """
    M = np.zeros((4, 4), dtype=int)
    for a in range(2):
        for b in range(2):
            for d in range(2):
                if (a, b, d) in uncovered_triples_at_p:
                    src = 2 * a + b
                    dst = 2 * b + d
                    M[src, dst] = 1
    return M


def analyze_binary_core(ms, n, cycle, movers, det):
    """Decompose SK into strictly-binary and non-binary parts."""
    L = len(movers)
    cycle_set = set(cycle)

    # Value sets from cycle
    V = value_sets(cycle, n)

    # Move entries (fires that change value)
    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # Binary configs = {0,1}^n
    binary_configs = set(iproduct(*([range(2)] * n)))
    binary_cycle = binary_configs & cycle_set
    binary_ng = binary_configs - cycle_set

    # Fire counts and coverage
    fc = [0] * n
    for m in movers:
        fc[m] += 1

    # Classify det entries as binary vs non-binary
    binary_det_entries = {}  # binary input + binary output
    cross_det_entries = {}   # binary input + non-binary output
    nonbinary_det_entries = {}  # non-binary input

    for (p, Lv, Sv, Rv), val in move_entries.items():
        is_binary_input = (Lv in (0, 1) and Sv in (0, 1) and Rv in (0, 1))
        is_binary_output = (val in (0, 1))
        if is_binary_input:
            if is_binary_output:
                binary_det_entries[(p, Lv, Sv, Rv)] = val
            else:
                cross_det_entries[(p, Lv, Sv, Rv)] = val
        else:
            nonbinary_det_entries[(p, Lv, Sv, Rv)] = val

    # Build binary forced graph (using only binary det entries)
    binary_edges = defaultdict(list)
    binary_no_edge = set()
    for c in binary_ng:
        has_edge = False
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in binary_det_entries:
                nc = list(c)
                nc[p] = binary_det_entries[key]
                nc = tuple(nc)
                if nc in binary_ng:
                    binary_edges[c].append(nc)
                    has_edge = True
        if not has_edge:
            binary_no_edge.add(c)

    # Check for cross-edges from binary configs (via cross det entries)
    cross_edge_count = 0
    cross_edge_configs = set()
    for c in binary_ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in cross_det_entries:
                cross_edge_count += 1
                cross_edge_configs.add(c)

    # Peel the binary forced graph to get binary immune core
    remaining = set(binary_ng)
    rounds = 0
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt in binary_edges.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        remaining -= sinks
        rounds += 1

    binary_immune = remaining

    # Transfer matrix: count no-match binary configs analytically
    # At each position p, uncovered triples = {0,1}^3 \ covered_at_p
    covered = [set() for _ in range(n)]
    for (p, Lv, Sv, Rv), val in binary_det_entries.items():
        covered[p].add((Lv, Sv, Rv))
    # Also include non-move entries (where det says "stay", effectively blocking)
    for (p, Lv, Sv, Rv), val in det.items():
        if Lv in (0, 1) and Sv in (0, 1) and Rv in (0, 1):
            covered[p].add((Lv, Sv, Rv))

    uncovered = [set() for _ in range(n)]
    for p in range(n):
        for a in range(2):
            for b in range(2):
                for d in range(2):
                    if (a, b, d) not in covered[p]:
                        uncovered[p].add((a, b, d))

    # Compute transfer matrix product trace
    M = np.eye(4, dtype=int)
    for p in range(n):
        Tp = build_transfer_matrix(uncovered[p])
        M = M @ Tp

    tm_no_match = int(np.trace(M))

    return {
        'L': L,
        'fc': fc,
        'binary_cycle': len(binary_cycle),
        'binary_ng': len(binary_ng),
        'binary_det': len(binary_det_entries),
        'cross_det': len(cross_det_entries),
        'nonbinary_det': len(nonbinary_det_entries),
        'binary_no_edge': len(binary_no_edge),
        'cross_edge_count': cross_edge_count,
        'cross_edge_configs': len(cross_edge_configs),
        'binary_immune': len(binary_immune),
        'binary_peel_rounds': rounds,
        'tm_no_match': tm_no_match,
        'covered_per_pos': [len(covered[p]) for p in range(n)],
        'uncovered_per_pos': [len(uncovered[p]) for p in range(n)],
    }


def main():
    print("=" * 72)
    print("Exploration 1: Binary subgraph decomposition for SK Lemma C")
    print("=" * 72)

    plan = [
        (5, 1, 1500, 5.0, 16),
        (6, 2, 500, 3.0, 18),
        (7, 10, 200, 3.0, 18),
    ]

    by_nL = defaultdict(list)
    all_records = []

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===")
        t0 = time.time()
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n:
                    continue
                r = analyze_binary_core(ms, n, cycle, movers, det)
                r['n'] = n
                r['ms'] = ms
                by_nL[(n, L)].append(r)
                all_records.append(r)
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx + 1}/{len(sampled)}]  {elapsed:.0f}s")

    # === Summary tables ===
    print(f"\n{'=' * 72}")
    print("=== Binary immune core vs 2^(n-1) ===")
    print(f"  n  L   count  |bin_NG|  |bin_imm|  min_imm  2^(n-1)  slack"
          f"  tm_no_match  cross_det  cross_edges")
    for (n, L) in sorted(by_nL.keys()):
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda k: sum(r[k] for r in rs) / N
        mn_imm = min(r['binary_immune'] for r in rs)
        target = 2 ** (n - 1)
        slack = mn_imm - target
        max_cross_det = max(r['cross_det'] for r in rs)
        max_cross_edges = max(r['cross_edge_count'] for r in rs)
        max_tm = max(r['tm_no_match'] for r in rs)
        flag = " !" if mn_imm < target else ""
        print(f"  {n}  {L:2d}  {N:5d}  {avg('binary_ng'):7.0f}  "
              f"{avg('binary_immune'):8.1f}  {mn_imm:7d}  {target:6d}  {slack:+5d}"
              f"  {max_tm:12d}  {max_cross_det:9d}  {max_cross_edges:11d}{flag}")

    # === Cross-edge analysis ===
    total_cross_det = sum(r['cross_det'] for r in all_records)
    total_cross_edges = sum(r['cross_edge_count'] for r in all_records)
    print(f"\n=== Cross-edge totals ===")
    print(f"  Total cross det entries: {total_cross_det}")
    print(f"  Total cross edge count:  {total_cross_edges}")
    print(f"  Binary subgraph closed:  {'YES' if total_cross_edges == 0 else 'NO'}")

    # === Transfer matrix validation ===
    print(f"\n=== Transfer matrix no-match vs actual no-edge (binary only) ===")
    tm_mismatch = 0
    for r in all_records:
        if r['tm_no_match'] != r['binary_no_edge']:
            tm_mismatch += 1
    print(f"  Transfer matrix mismatches: {tm_mismatch} / {len(all_records)}")

    # === No-match monotonicity check ===
    print(f"\n=== No-match count at L=2n vs L=2n+k ===")
    for n_val in sorted(set(n for n, _ in by_nL.keys())):
        base_L = 2 * n_val
        if (n_val, base_L) not in by_nL:
            continue
        base_max = max(r['tm_no_match'] for r in by_nL[(n_val, base_L)])
        print(f"  n={n_val}: L=2n max_no_match={base_max}")
        for (n2, L2) in sorted(by_nL.keys()):
            if n2 != n_val or L2 <= base_L:
                continue
            ext_max = max(r['tm_no_match'] for r in by_nL[(n2, L2)])
            flag2 = " INCREASED!" if ext_max > base_max else ""
            print(f"    L={L2}: max_no_match={ext_max}{flag2}")

    # === Coverage per position ===
    print(f"\n=== Det coverage at positions (avg covered triples out of 8) ===")
    for (n, L) in sorted(by_nL.keys()):
        if L not in (2 * n, 2 * n + 2):
            continue
        rs = by_nL[(n, L)]
        avg_cov = [sum(r['covered_per_pos'][p] for r in rs) / len(rs) for p in range(n)]
        print(f"  n={n} L={L}: {[round(c, 1) for c in avg_cov]}")

    # === Violations check ===
    violations = sum(1 for r in all_records if r['binary_immune'] < 2 ** (r['n'] - 1))
    print(f"\n  BINARY IMMUNE CORE >= 2^(n-1): "
          f"{'HOLDS' if violations == 0 else f'VIOLATED ({violations})'} "
          f"({len(all_records)} records)")

    # === Hardest cases ===
    print(f"\n=== Hardest cases (lowest binary immune core relative to 2^(n-1)) ===")
    sorted_records = sorted(all_records,
                           key=lambda r: r['binary_immune'] - 2 ** (r['n'] - 1))
    for r in sorted_records[:5]:
        n = r['n']
        slack = r['binary_immune'] - 2 ** (n - 1)
        print(f"  n={n} L={r['L']} ms={r['ms']} binary_immune={r['binary_immune']} "
              f"slack={slack} fc={r['fc']} tm_no_match={r['tm_no_match']}")


if __name__ == "__main__":
    main()
