#!/usr/bin/env python3
"""Sink budget probe: can peeling exhaust NG at sub-M_n?

The structural proof of |SK| ≥ 1 reduces to: peeling can't remove
everything. This probe tracks:

1. Round-0 sinks decomposed by TYPE:
   (a) "no-match" sinks: c doesn't match any det move entry at any p
       (= non-binary configs whose contexts never appear in det)
   (b) "all-targets-in-C" sinks: c matches ≥1 move entry but every
       forced target lands in C (the cycle)
   (c) "all-targets-outside-NG" sinks: targets land outside NG
       (in C or already removed)

2. Per-round cascade budget: how many configs does each peeling round
   remove, and what's their type?

3. Total peeled vs |NG|: does the budget leave room for SK ≥ 2^(n-1)?

The structural proof claim: "no-match" sinks account for almost all
removals. Their count = |non-binary configs| which is independent
of the cycle and bounded by M - 2^n. Binary configs almost never
become sinks.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time

def m_n_sharp(n):
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


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def analyze_sink_budget(ms, n, cycle, movers, det):
    """Decompose sinks by type and track the peeling budget."""
    all_configs = list(iproduct(*[range(m) for m in ms]))
    cycle_set = set(cycle)
    ng = [c for c in all_configs if c not in cycle_set]
    ng_set = set(ng)
    V = value_sets(cycle, n)

    # Identify move entries in det (entries where output ≠ input state)
    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    # Build forced graph
    adj = defaultdict(list)
    for c in ng:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append(nc)

    # Classify each NG config
    def is_binary(c):
        """Does c only use values that appear in the cycle at each position?"""
        return all(c[i] in V[i] for i in range(n))

    def has_any_match(c):
        """Does c match at least one move entry?"""
        for p in range(n):
            key = (p, c[(p-1)%n], c[p], c[(p+1)%n])
            if key in move_entries:
                return True
        return False

    # Round-0 analysis
    no_match_sinks = 0
    all_targets_in_C_sinks = 0
    binary_with_edges = 0
    nonbinary_with_edges = 0

    for c in ng:
        out_in_ng = adj.get(c, [])
        is_bin = is_binary(c)
        has_match = has_any_match(c)

        if len(out_in_ng) == 0:
            # Sink
            if not has_match:
                no_match_sinks += 1
            else:
                all_targets_in_C_sinks += 1
        else:
            if is_bin:
                binary_with_edges += 1
            else:
                nonbinary_with_edges += 1

    # Full peeling with round tracking
    remaining = set(ng)
    round_sizes = []
    while True:
        sinks = set()
        for c in remaining:
            if not any(tgt in remaining for tgt in adj.get(c, [])):
                sinks.add(c)
        if not sinks:
            break
        round_sizes.append(len(sinks))
        remaining -= sinks

    return {
        'ng_size': len(ng),
        'sk_size': len(remaining),
        'no_match_sinks': no_match_sinks,
        'all_targets_in_C': all_targets_in_C_sinks,
        'binary_with_edges': binary_with_edges,
        'nonbinary_with_edges': nonbinary_with_edges,
        'round_sizes': round_sizes,
        'total_peeled': sum(round_sizes),
        'binary_ng': sum(1 for c in ng if is_binary(c)),
    }


def main():
    print("=" * 72, flush=True)
    print("Sink budget probe: can peeling exhaust NG?", flush=True)
    print("=" * 72, flush=True)

    plan = [
        (5, 1, 1500, 5.0, 15),
        (6, 4, 500, 3.0, 17),
    ]

    by_nL = defaultdict(list)

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
                r = analyze_sink_budget(ms, n, cycle, movers, det)
                by_nL[(n, L)].append(r)
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                elapsed = time.time() - t0
                print(f"  [{idx+1}/{len(sampled)}]  {elapsed:.0f}s", flush=True)

    print(f"\n{'='*72}", flush=True)
    print(f"=== Sink decomposition (round 0) ===", flush=True)
    print(f"  n  L   count  avg_NG  avg_noMatch  avg_targInC  "
          f"avg_binEdges  avg_nonbinEdges  avg_SK", flush=True)
    for (n, L) in sorted(by_nL.keys()):
        rs = by_nL[(n, L)]
        N = len(rs)
        avg = lambda key: sum(r[key] for r in rs) / N
        print(f"  {n}  {L:2d}  {N:5d}  {avg('ng_size'):6.0f}  "
              f"{avg('no_match_sinks'):11.1f}  {avg('all_targets_in_C'):11.1f}  "
              f"{avg('binary_with_edges'):12.1f}  {avg('nonbinary_with_edges'):15.1f}  "
              f"{avg('sk_size'):6.1f}", flush=True)

    print(f"\n=== Binary NG vs total peeled ===", flush=True)
    print(f"  n  L   avg_binaryNG  avg_peeled  avg_SK  2^(n-1)  "
          f"binary_survives", flush=True)
    for (n, L) in sorted(by_nL.keys()):
        rs = by_nL[(n, L)]
        N = len(rs)
        avg_bin = sum(r['binary_ng'] for r in rs) / N
        avg_peeled = sum(r['total_peeled'] for r in rs) / N
        avg_sk = sum(r['sk_size'] for r in rs) / N
        target = 2 ** (n - 1)
        # How much of binary NG survives into SK?
        # binary_with_edges is round-0 only; some may get peeled later
        avg_bwe = sum(r['binary_with_edges'] for r in rs) / N
        print(f"  {n}  {L:2d}  {avg_bin:12.0f}  {avg_peeled:10.1f}  "
              f"{avg_sk:6.1f}  {target:6d}  "
              f"{avg_bwe:17.1f}", flush=True)

    print(f"\n=== Peeling round profile (L=2n and L=2n+2) ===", flush=True)
    for (n, L) in sorted(by_nL.keys()):
        if L not in (2*n, 2*n+2):
            continue
        rs = by_nL[(n, L)]
        # Aggregate round sizes
        max_rounds = max(len(r['round_sizes']) for r in rs) if rs else 0
        if max_rounds == 0:
            print(f"  n={n}  L={L}: no peeling needed (SK = NG)", flush=True)
            continue
        print(f"  n={n}  L={L}  max_rounds={max_rounds}:", flush=True)
        for rnd in range(min(max_rounds, 8)):
            sizes = [r['round_sizes'][rnd] for r in rs
                     if rnd < len(r['round_sizes'])]
            if sizes:
                print(f"    round {rnd}: avg={sum(sizes)/len(sizes):.1f}  "
                      f"max={max(sizes)}  cycles_with_this_round={len(sizes)}",
                      flush=True)


if __name__ == "__main__":
    main()
