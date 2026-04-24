#!/usr/bin/env python3
"""Diagnostic probe: WHY does |proj_{p*}(SK)| = 2^(n-1) at the tight case?

At (n=5, L=12), the projection floor has slack 0: max_proj = 16 = 2^4.
This probe dissects the structure to find the analytical handle:

For each tight-case cycle:
  1. What is proj_{p*}(SK) exactly? Is it the binary (n-1)-cube?
  2. How do cycle configs partition under projection?
  3. For each binary (n-1)-tuple c~, do both lifts (c~, v0) and (c~, v1)
     land in SK, or just one?
  4. What about non-binary (n-1)-tuples — are they ALL absent from proj(SK)?
  5. The "forced 2-cycle" at p*: when c~ has the right neighbor values,
     (c~, v0) → (c~, v1) and back. How often does this occur?
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import sys

sys.setrecursionlimit(20000)


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


def compute_sk(ms, n, cycle, det):
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
    return remaining


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n):
            V[i].add(c[i])
    return V


def main():
    n = 5
    L_target = 2 * n + 2  # = 12
    target = 2 ** (n - 1)  # = 16

    print("=" * 72, flush=True)
    print(f"Diagnostic: n={n}, L={L_target}, target proj = {target}", flush=True)
    print("=" * 72, flush=True)

    Mn = m_n_sharp(n)
    multisets = enumerate_multisets(n, Mn)
    print(f"  multisets: {len(multisets)}", flush=True)

    # Counters
    tight_count = 0      # cycles where max_proj == target exactly
    proj_is_binary_cube = 0  # proj(SK) == binary (n-1)-cube
    both_lifts_in_sk = Counter()  # how many (n-1)-tuples have BOTH lifts in SK
    one_lift_in_sk = Counter()
    zero_lifts_in_sk = Counter()
    nonbinary_in_proj = 0  # non-binary (n-1)-tuples in proj(SK)
    total_records = 0

    t0 = time.time()
    for idx, ms in enumerate(multisets):
        cycles = enumerate_all_cycles(ms, n, 15, 8.0, 2000)
        for cycle, movers, det in cycles:
            if len(movers) != L_target:
                continue
            sk = compute_sk(ms, n, cycle, det)
            if not sk:
                continue
            total_records += 1
            V = value_sets(cycle, n)

            # Find min-fc processor p*
            fv_list = [0] * n
            for p in movers:
                fv_list[p] += 1
            min_fc = min(fv_list)
            # Pick the first min-fc processor
            p_star = fv_list.index(min_fc)

            # Compute projection (drop p*)
            proj_sk = set()
            for c in sk:
                proj_sk.add(tuple(c[i] for i in range(n) if i != p_star))

            if len(proj_sk) != target:
                continue  # not the tight case
            tight_count += 1

            # Is proj(SK) exactly the binary (n-1)-cube?
            # Binary cube: for each non-p* position i, pick the 2 smallest values in V[i].
            binary_vals = []
            for i in range(n):
                if i == p_star:
                    continue
                vals = sorted(V[i])[:2]
                binary_vals.append(vals)
            binary_cube = set(iproduct(*binary_vals))

            is_binary = (proj_sk == binary_cube)
            if is_binary:
                proj_is_binary_cube += 1

            # For each binary (n-1)-tuple, check how many lifts are in SK
            v_vals = sorted(V[p_star])[:2]  # binary values at p*
            for c_tilde in binary_cube:
                lifts_in_sk = 0
                for v in v_vals:
                    full = list(c_tilde)
                    full.insert(p_star, v)
                    if tuple(full) in sk:
                        lifts_in_sk += 1
                if lifts_in_sk == 2:
                    both_lifts_in_sk[tight_count] += 1
                elif lifts_in_sk == 1:
                    one_lift_in_sk[tight_count] += 1
                else:
                    zero_lifts_in_sk[tight_count] += 1

            # Non-binary configs in projection
            nonbin = proj_sk - binary_cube
            if nonbin:
                nonbinary_in_proj += 1

        if (idx + 1) % 5 == 0:
            elapsed = time.time() - t0
            print(f"  [{idx+1}/{len(multisets)}]  {elapsed:.0f}s  "
                  f"records={total_records}  tight={tight_count}  "
                  f"binary_cube_match={proj_is_binary_cube}", flush=True)

    print(f"\n=== Summary ===", flush=True)
    print(f"  total records at L={L_target}: {total_records}", flush=True)
    print(f"  tight (proj == {target}): {tight_count}", flush=True)
    print(f"  of which proj == binary cube: {proj_is_binary_cube} "
          f"({100*proj_is_binary_cube/max(tight_count,1):.1f}%)", flush=True)
    print(f"  non-binary elements in proj: {nonbinary_in_proj} cycles", flush=True)

    # Lift analysis: across all tight cycles, aggregate
    total_both = sum(both_lifts_in_sk.values())
    total_one = sum(one_lift_in_sk.values())
    total_zero = sum(zero_lifts_in_sk.values())
    total_tuples = total_both + total_one + total_zero
    print(f"\n  Lift analysis (per binary (n-1)-tuple across {tight_count} tight cycles):",
          flush=True)
    print(f"    both lifts in SK: {total_both} ({100*total_both/max(total_tuples,1):.1f}%)",
          flush=True)
    print(f"    one lift in SK:   {total_one} ({100*total_one/max(total_tuples,1):.1f}%)",
          flush=True)
    print(f"    zero lifts in SK: {total_zero} ({100*total_zero/max(total_tuples,1):.1f}%)",
          flush=True)
    if tight_count > 0 and tight_count <= 5:
        for k in range(1, tight_count + 1):
            print(f"    cycle {k}: both={both_lifts_in_sk[k]}  "
                  f"one={one_lift_in_sk[k]}  zero={zero_lifts_in_sk[k]}", flush=True)


if __name__ == "__main__":
    main()
