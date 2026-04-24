#!/usr/bin/env python3
"""Structure of peel(N_1(C)) at n=7 where |peel| = 2^(n-1) = 64 exactly.

Hypotheses about WHY 64:
  S1: peel(N_1(C)) is exactly a half-cube {c ∈ {0,1}^n : Σ c_i ≡ parity}
  S2: peel(N_1(C)) is a union of L "parity slices" along the cycle
  S3: peel(N_1(C)) = all 1-flips c'[q]=v of cycle configs c with some parity condition

Tests:
  For each record (n=7):
  - is peel(N_1(C)) ⊆ binary cube {0,1}^n? (if multiset has all 2s at binary)
  - compute all parity sums of peel configs → distribution
  - project peel(N_1(C)) to each coord → what values appear?
  - for each (q, v) pair, count |{c ∈ peel : c[q] = v}| — compare to 2^(n-2)
  - is peel(N_1(C)) a product set?
  - distance from peel set to cycle — min/max/distribution
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time


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


def compute_sk(vcng_set, move_entries, n):
    current = set(vcng_set)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
                if ctx in move_entries:
                    v = move_entries[ctx]
                    nc = list(c); nc[p] = v; nc = tuple(nc)
                    if nc in current:
                        has_forced = True
                        break
            if not has_forced:
                victims.add(c)
        if not victims:
            break
        current -= victims
    return current


def neighborhood_1(cycle, V, n, ms):
    cycle_set = set(cycle)
    N1 = set()
    for c in cycle:
        for i in range(n):
            for v in V[i]:
                if v == c[i]: continue
                nc = list(c); nc[i] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)
    return N1


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = list(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = set(VC) - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    N1 = neighborhood_1(cycle, V, n, ms)
    N1_peel = compute_sk(N1, move_entries, n)
    # Parity: sum of coords mod m_i? Or mod 2 (treating each as bit)?
    parity_cnt = Counter(sum(c) % 2 for c in N1_peel)
    # Projection counts: for each (q, v), how many peel configs have c[q] = v?
    proj = [defaultdict(int) for _ in range(n)]
    for c in N1_peel:
        for q in range(n):
            proj[q][c[q]] += 1
    # Is peel a product? Check if |peel| = prod |proj[q]|
    projsize = 1
    for q in range(n):
        projsize *= len(proj[q])
    # Quick check: for each q in [n], is proj[q] balanced?
    balanced = all(len(set(proj[q].values())) == 1 for q in range(n))
    # Hamming distance distribution from peel set to cycle
    def hd(a, b): return sum(1 for i in range(n) if a[i] != b[i])
    hds = []
    for c in N1_peel:
        hds.append(min(hd(c, cc) for cc in cycle))
    hd_dist = Counter(hds)
    return {
        'n': n, 'ms': ms, 'L': L,
        'peel_size': len(N1_peel),
        'parity_counts': dict(parity_cnt),
        'proj_sizes': tuple(len(proj[q]) for q in range(n)),
        'balanced_proj': balanced,
        'is_all_binary_cube': all(m == 2 for m in ms),
        'proj_uniform_count': tuple(
            tuple(sorted(proj[q].values())) for q in range(n)
        ),
        'hd_dist': dict(hd_dist),
        'peel_set': N1_peel,
    }


def main():
    print("=" * 72)
    print("Peel structure at n=7 — why exactly 2^(n-1)?")
    print("=" * 72)
    n = 7
    Mn = m_n_sharp(n)
    multisets = enumerate_multisets(n, Mn)
    sampled = multisets[::30]
    print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
    all_records = []
    t0 = time.time()
    for idx, ms in enumerate(sampled):
        cycles = enumerate_all_cycles(ms, n, 17, 4.0, 12)
        for cycle, movers, det in cycles:
            L = len(movers)
            if L < 2 * n + 2:
                continue
            r = analyze(ms, n, cycle, movers, det)
            all_records.append(r)
        if (idx + 1) % 5 == 0 or idx == len(sampled) - 1:
            print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={len(all_records)}", flush=True)

    if not all_records:
        print("No records!"); return

    print(f"\n{'='*72}\nStructural analysis of peel(N_1(C)) at n={n}\n{'='*72}\n")
    sizes = Counter(r['peel_size'] for r in all_records)
    print(f"|peel(N_1(C))| distribution: {dict(sizes.most_common())}")
    parity_patterns = Counter(tuple(sorted(r['parity_counts'].items())) for r in all_records)
    print(f"\nParity-sum distribution (top 5):")
    for pat, c in parity_patterns.most_common(5):
        print(f"  {pat} → {c}")
    proj_patterns = Counter(r['proj_sizes'] for r in all_records)
    print(f"\nproj_sizes distribution (top 5):")
    for pat, c in proj_patterns.most_common(5):
        print(f"  {pat} → {c}")
    balanced_count = sum(1 for r in all_records if r['balanced_proj'])
    print(f"\nbalanced proj (each coord has uniform count): {balanced_count}/{len(all_records)}")
    proj_uniform = Counter(tuple(tuple(v) for v in r['proj_uniform_count']) for r in all_records)
    print(f"\nproj uniform_count distribution (top 5):")
    for pat, c in proj_uniform.most_common(5):
        print(f"  {pat} → {c}")
    binary_count = sum(1 for r in all_records if r['is_all_binary_cube'])
    print(f"\nall-binary multisets: {binary_count}/{len(all_records)}")
    hd_patterns = Counter(tuple(sorted(r['hd_dist'].items())) for r in all_records)
    print(f"\nHamming-distance from peel set to cycle (top 5):")
    for pat, c in hd_patterns.most_common(5):
        print(f"  {pat} → {c}")

    # For binary cube records specifically, check parity
    binary_recs = [r for r in all_records if r['is_all_binary_cube']]
    if binary_recs:
        print(f"\n--- binary-cube records: {len(binary_recs)}")
        par_split = Counter()
        for r in binary_recs:
            pc = r['parity_counts']
            par_split[(pc.get(0, 0), pc.get(1, 0))] += 1
        print(f"  (even, odd) split: {dict(par_split.most_common())}")


if __name__ == "__main__":
    main()
