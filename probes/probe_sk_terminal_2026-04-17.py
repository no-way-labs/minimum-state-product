#!/usr/bin/env python3
"""Terminal flush of injection (i) and recursion (iii) hypotheses.

(i) Injection candidates to exhaustively kill:
  i.1: Binary-position star: c_0 + flips of any subset of binary positions.
       If ≥ n-1 binary positions, this gives 2^(n-1) configs.
  i.2: "Twisted cycle": C + rotation of cycle by k for k ∈ {0,...,L-1}.
       Size L, too small.
  i.3: Forced preimage of any single config: backward cone. Size < |SK|.
  i.4: "Halfspace" in value cube: configs with c[p] ≤ threshold for some p.
       Size = half of V_sorted. Need to check forced closure.
  i.5: Graph products: pair of configs (c, τ(c)) for some involution τ.
       2x larger if injective.
  i.6: 2^(n-1) as # of paths of length n-1 in a binary tree = tempting
       but no obvious tree structure.

(iii) Recursion candidates to exhaustively kill:
  iii.1: Drop-position projection. For each p, does π_{drop-p}(SK_n) equal
         SK of some induced (n-1)-cycle?
  iii.2: Aggregate. For each p, |{d ∈ ∏V_{≠p} : (d, v) ∈ SK for some v}| — is
         this ≥ 2^(n-1)?
  iii.3: Value-equivalence quotient. Identify configs that differ only by a
         value permutation at some fixed position.
  iii.4: Ring decomposition. Split ring into two arcs of lengths k and n-k,
         check if SK decomposes accordingly.
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time
import math
import sys
sys.setrecursionlimit(100000)


def enumerate_cycles(ms, n, L_min, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            if L < L_min: return
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen:
                seen.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p - 1) % n]; Sp = config[p]; Rp = config[(p + 1) % n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i - 1) % n]; Si = config[i]; Ri = config[(i + 1) % n]
                    ki = (i, Li, Si, Ri)
                    if ki in new_det and new_det[ki] != Si: ok = False; break
                    new_det[ki] = Si
                if not ok: continue
                nc = list(config); nc[p] = new_val; nc = tuple(nc)
                if nc != start and nc in set(path): continue
                dfs(start, nc, new_det, path + [nc], movers + [p])
    for start in all_starts:
        if len(found) >= max_cycles or time.time() - t0 > time_budget: break
        dfs(start, start, {}, [start], [])
    return found


def compute_sk_and_adj(ms, n, cycle, det):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    V_sorted = [sorted(V[i]) for i in range(n)]
    all_configs = list(iproduct(*V_sorted))
    cycle_set = set(cycle)
    non_good = [c for c in all_configs if c not in cycle_set]
    ng_set = set(non_good)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    adj = defaultdict(list)
    for c in non_good:
        for p in range(n):
            Lp = c[(p - 1) % n]; Sp = c[p]; Rp = c[(p + 1) % n]
            key = (p, Lp, Sp, Rp)
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in ng_set:
                    adj[c].append(nc)
    remaining = set(non_good)
    while True:
        sinks = {c for c in remaining if not any(t in remaining for t in adj.get(c, []))}
        if not sinks: break
        remaining -= sinks
    return remaining, adj, V_sorted


def terminal_probe(n, ms, cycle, det, bound):
    sk, adj, V_sorted = compute_sk_and_adj(ms, n, cycle, det)
    if not sk: return None

    results = {'sk_size': len(sk), 'bound': bound,
               'n': n, 'ms': ms, 'L': len(cycle)}

    # ==========================================================================
    # (i.1) Binary-position star from each cycle config
    # ==========================================================================
    binary_positions = [p for p, m in enumerate(ms) if m == 2 and len(V_sorted[p]) == 2]
    if len(binary_positions) >= 1:
        # For each c0 in cycle, construct star = {c0 with any subset of binary positions flipped}
        max_star_size = 0
        star_in_sk_counts = []
        for c0 in cycle:
            star = set()
            k = len(binary_positions)
            for bits in range(2**k):
                c = list(c0)
                for j, p in enumerate(binary_positions):
                    V_p = V_sorted[p]
                    if (bits >> j) & 1:
                        c[p] = V_p[1] if c0[p] == V_p[0] else V_p[0]
                star.add(tuple(c))
            star_size = len(star)
            in_sk = star & sk
            star_in_sk_counts.append(len(in_sk))
            max_star_size = max(max_star_size, len(in_sk))
        results['i1_max_star_in_sk'] = max_star_size
        results['i1_binary_positions'] = len(binary_positions)
        results['i1_star_full_size'] = 2 ** len(binary_positions)

    # ==========================================================================
    # (i.2) Shift-orbit of cycle config under forward F iteration
    # ==========================================================================
    # Pick c0 ∈ cycle, follow neighbors outside cycle that are in SK
    orbits = []
    visited = set()
    for c0 in sk:
        if c0 in visited: continue
        orbit = [c0]
        cur = c0
        while True:
            nxt = None
            for t in adj.get(cur, []):
                if t in sk:
                    nxt = t; break
            if nxt is None: break
            if nxt in orbit:
                # reached cycle
                break
            orbit.append(nxt)
            visited.add(nxt)
            if len(orbit) > 3 * len(sk): break
        orbits.append(orbit)
    results['i2_num_orbits'] = len(orbits)
    results['i2_max_orbit_len'] = max(len(o) for o in orbits) if orbits else 0

    # ==========================================================================
    # (i.3) Forced preimage of cycle: configs c ∈ VC_NG with F^k(c) ∈ cycle_neighborhood
    # ==========================================================================
    # Skip — essentially backward cone already analyzed.

    # ==========================================================================
    # (i.4) Value-halfspace: configs with c[0] = v_min
    # ==========================================================================
    halfspace_sizes = []
    for p in range(n):
        for v_target in V_sorted[p]:
            sub = {c for c in sk if c[p] == v_target}
            halfspace_sizes.append((p, v_target, len(sub)))
    max_halfspace = max(s for _, _, s in halfspace_sizes)
    results['i4_max_halfspace'] = max_halfspace

    # ==========================================================================
    # (iii.1) Drop-position projection
    # ==========================================================================
    projections = []
    for p in range(n):
        proj = set()
        for c in sk:
            proj.add(tuple(c[i] for i in range(n) if i != p))
        projections.append((p, len(proj)))
    results['iii1_proj_sizes'] = projections
    results['iii1_max_proj'] = max(sz for _, sz in projections)

    # ==========================================================================
    # (iii.2) Aggregation: unique (n-1) prefix appearing
    # ==========================================================================
    # Same as iii.1 essentially

    # ==========================================================================
    # (iii.3) Value-permutation quotient
    # ==========================================================================
    # For each p, identify configs differing only in c[p] (i.e., same (c[0..p-1], c[p+1..n-1]))
    # Count # equivalence classes = # distinct "drop-p" profiles.
    # Same as projections basically.

    # ==========================================================================
    # (iii.4) Ring decomposition: does SK decompose by arc?
    # ==========================================================================
    # For each pair (i, j) with i+1 < j, let arc1 = [i..j-1], arc2 = [j..n-1, 0..i-1]
    # Compute Cartesian product of projections — is SK a subset of the product?
    # Too expensive; skip unless n is small.

    return results


def main():
    print("=" * 100)
    print("TERMINAL FLUSH: (i) injection candidates and (iii) recursion candidates")
    print("=" * 100)

    plan = [
        (5, [(2,2,2,3,3), (2,2,2,3,4), (2,2,3,3,3)], 15, 3, 20.0),
        (6, [(2,2,2,3,3,3), (2,2,3,3,3,3)], 17, 2, 30.0),
        (7, [(2,2,2,3,3,3,3)], 17, 1, 45.0),
        (8, [(2,2,2,3,3,3,3,3)], 19, 1, 60.0),
    ]

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n}  bound=2^{n-1}={bound} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for ci, (cycle, movers, det) in enumerate(cycles):
                r = terminal_probe(n, ms, cycle, det, bound)
                if r is None: continue
                print(f"\n  ms={ms} L={len(cycle)} cycle#{ci}  |SK|={r['sk_size']} bound={bound}")
                # (i.1)
                if 'i1_max_star_in_sk' in r:
                    bp = r['i1_binary_positions']
                    sfs = r['i1_star_full_size']
                    miss = r['i1_max_star_in_sk']
                    print(f"    (i.1) Binary-star: {bp} binary pos, 2^{bp}={sfs} full, max in SK={miss}  "
                          f"(≥{bound}? {'YES' if miss >= bound else 'NO'})")
                # (i.2)
                print(f"    (i.2) Forced orbit decomposition: {r['i2_num_orbits']} orbits, "
                      f"max orbit len={r['i2_max_orbit_len']}")
                # (i.4)
                print(f"    (i.4) Max halfspace (fix one (p,v)): {r['i4_max_halfspace']}  "
                      f"(≥{bound}? {'YES' if r['i4_max_halfspace'] >= bound else 'NO'})")
                # (iii.1)
                print(f"    (iii.1) Max drop-p projection size: {r['iii1_max_proj']}  "
                      f"(≥{bound}? {'YES' if r['iii1_max_proj'] >= bound else 'NO'})")
                # Full proj sizes to see pattern
                ps = [(p, sz) for p, sz in r['iii1_proj_sizes']]
                print(f"          full proj sizes: {ps}")


if __name__ == "__main__":
    main()
