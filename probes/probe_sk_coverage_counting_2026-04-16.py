#!/usr/bin/env python3
"""Exploration 7: Precise coverage counting for SK ≥ 1.

The theorem reduces to: the forced graph on VC-NG has at least one edge.
Equivalently: at least one VC-NG config c has a det move entry at some
position p where the target c' (c with c[p] changed) is also in VC-NG.

For each det move entry (p, a, b, d) → e:
  - "source slab" = {c ∈ VC : c[p-1]=a, c[p]=b, c[p+1]=d}
  - "target slab" = {c' ∈ VC : c'[p-1]=a, c'[p]=e, c'[p+1]=d}
  - VC-NG sources = source_slab ∩ VC-NG
  - VC-NG targets = target_slab ∩ VC-NG
  - VC-NG edges from this entry = |{c ∈ VC-NG sources : target(c) ∈ VC-NG}|

The edge exists iff: some c in the source slab is not in C, AND its
target (same c but c[p]→e) is also not in C.

EQUIVALENT: for some det move entry, the source slab has a non-cycle config
whose image is also a non-cycle config. This fails only if: for every
source in the slab, either the source is in C or the target is in C.

KEY INSIGHT TO TEST: Can the cycle "block" all edges by placing configs
strategically in both source and target slabs?

If the cycle has L configs and each det entry's slab pair (source, target)
has S configs each, the cycle needs to block S pairs per entry. With L
configs total, it can block at most L pairs per entry (if all L are in
the source or target). But each config blocks at most n entries (one per
position). So total blocking capacity = L × n.

Total pairs to block = L × S (L entries, S pairs each).
Blocking capacity = L × n.
For blocking to succeed: L × S ≤ L × n, i.e., S ≤ n.

At n=5 with binary |V_i|=2: S = 2^{n-3} = 4. And n = 5. So S = 4 ≤ 5.
Blocking MIGHT succeed! This is why n=5 is tight.

At n=7: S = 2^{n-3} = 16. And n = 7. So S = 16 > 7. Blocking CANNOT
succeed by this counting argument. At least one edge must exist.

Let me verify this computationally and find the exact threshold.
"""
from itertools import product as iproduct
from collections import defaultdict
import time


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


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def analyze_coverage(ms, n, cycle, movers, det):
    """Precise coverage analysis for one cycle."""
    L = len(movers)
    cycle_set = set(cycle)
    V = value_sets(cycle, n)

    # Move entries
    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # VC configs
    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    # For each move entry: count source-in-NG and target-in-NG
    total_vcng_edges = 0
    entry_details = []

    for (p, a, b, d), e in move_entries.items():
        # Source slab: configs with c[p-1]=a, c[p]=b, c[p+1]=d
        # Target slab: configs with c[p-1]=a, c[p]=e, c[p+1]=d
        # Both in VC (since a,b,d,e are all values from the cycle)

        # Count VC-NG configs in source slab
        src_in_ng = 0
        edges_in_ng = 0

        # Enumerate source slab
        free_positions = [i for i in range(n) if i not in
                         {(p-1) % n, p, (p+1) % n}]
        free_ranges = [sorted(V[i]) for i in free_positions]

        for free_vals in iproduct(*free_ranges):
            # Build source config
            c = [0] * n
            c[(p-1) % n] = a
            c[p] = b
            c[(p+1) % n] = d
            for fi, fp in enumerate(free_positions):
                c[fp] = free_vals[fi]
            c = tuple(c)

            if c not in cycle_set:  # source is in VC-NG
                src_in_ng += 1
                # Build target
                ct = list(c)
                ct[p] = e
                ct = tuple(ct)
                if ct not in cycle_set:  # target is in VC-NG
                    edges_in_ng += 1
                    total_vcng_edges += 1

        slab_size = 1
        for i in free_positions:
            slab_size *= len(V[i])

        cycle_in_slab = slab_size - src_in_ng  # approximately

        entry_details.append({
            'pos': p,
            'triple': (a, b, d),
            'output': e,
            'slab_size': slab_size,
            'src_in_ng': src_in_ng,
            'edges_in_ng': edges_in_ng,
        })

    # How many entries have ≥ 1 edge in VC-NG?
    entries_with_edges = sum(1 for ed in entry_details if ed['edges_in_ng'] > 0)

    # Min slab size
    min_slab = min(ed['slab_size'] for ed in entry_details) if entry_details else 0
    max_slab = max(ed['slab_size'] for ed in entry_details) if entry_details else 0

    # Total coverage: sum of src_in_ng across all entries
    total_src_coverage = sum(ed['src_in_ng'] for ed in entry_details)

    return {
        'L': L,
        'vc_ng': len(vc_ng),
        'num_move_entries': len(move_entries),
        'total_vcng_edges': total_vcng_edges,
        'entries_with_edges': entries_with_edges,
        'min_slab': min_slab,
        'max_slab': max_slab,
        'total_src_coverage': total_src_coverage,
        'has_any_edge': total_vcng_edges > 0,
    }


def main():
    print("=" * 72, flush=True)
    print("Exploration 7: Precise coverage counting", flush=True)
    print("=" * 72, flush=True)

    for n in [5, 6, 7]:
        Mn = m_n_sharp(n)
        multisets = enumerate_mixed_multisets(n, Mn)

        # Sample representatives
        seen = set()
        sample = []
        for ms in multisets:
            key = tuple(sorted(ms))
            if key not in seen:
                seen.add(key)
                sample.append(ms)
        sample = sample[:4]

        print(f"\n=== n={n} ===", flush=True)
        print(f"  Slab size for binary positions: 2^(n-3) = {2**(n-3)}", flush=True)
        print(f"  n = {n}", flush=True)
        print(f"  Slab > n? {'YES' if 2**(n-3) > n else 'NO'} "
              f"({2**(n-3)} vs {n})", flush=True)

        for ms in sample:
            prod = 1
            for m in ms:
                prod *= m
            print(f"\n  ms={ms} product={prod}", flush=True)

            cycles = enumerate_all_cycles(ms, n, 20, 5.0, 500)
            if not cycles:
                print(f"    No cycles found", flush=True)
                continue

            min_edges = float('inf')
            min_entries_w = float('inf')
            zero_edge_count = 0
            total_tested = 0

            for cyc, movers, det in cycles[:200]:
                L = len(movers)
                if L < 2 * n:
                    continue
                total_tested += 1
                r = analyze_coverage(ms, n, cyc, movers, det)
                if r['total_vcng_edges'] < min_edges:
                    min_edges = r['total_vcng_edges']
                    min_edges_detail = r
                if r['entries_with_edges'] < min_entries_w:
                    min_entries_w = r['entries_with_edges']
                if not r['has_any_edge']:
                    zero_edge_count += 1

            if total_tested == 0:
                print(f"    No L >= 2n cycles", flush=True)
                continue

            print(f"    Tested {total_tested} cycles (L >= {2*n})", flush=True)
            print(f"    Min VC-NG edges: {min_edges}", flush=True)
            print(f"    Min entries with edges: {min_entries_w} / "
                  f"{min_edges_detail['num_move_entries']}", flush=True)
            print(f"    Zero-edge cycles: {zero_edge_count}", flush=True)
            print(f"    Slab sizes: {min_edges_detail['min_slab']}-"
                  f"{min_edges_detail['max_slab']}", flush=True)
            print(f"    Tightest case: L={min_edges_detail['L']}  "
                  f"VC-NG={min_edges_detail['vc_ng']}  "
                  f"edges={min_edges_detail['total_vcng_edges']}  "
                  f"src_coverage={min_edges_detail['total_src_coverage']}",
                  flush=True)

            if zero_edge_count > 0:
                print(f"    *** ZERO-EDGE CYCLE FOUND! ***", flush=True)

    # === Theoretical analysis ===
    print(f"\n{'='*72}", flush=True)
    print("=== Theoretical slab-size analysis ===", flush=True)
    print("At all-binary positions: slab_size = 2^(n-3)", flush=True)
    print("For SK >= 1: need at least one slab pair (source, target)", flush=True)
    print("where source has a VC-NG config whose target is also VC-NG.", flush=True)
    print("", flush=True)
    print("The cycle can block an edge by placing a config in the source", flush=True)
    print("OR the target. Each config blocks edges at up to n positions.", flush=True)
    print("", flush=True)
    for n in range(5, 13):
        slab = 2 ** (n - 3)
        print(f"  n={n:2d}: slab_size={slab:5d}  n={n}  "
              f"slab>n: {'YES → cycle can NOT block all edges' if slab > n else 'NO → tight'}", flush=True)


if __name__ == "__main__":
    main()
