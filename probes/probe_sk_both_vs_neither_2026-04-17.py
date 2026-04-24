#!/usr/bin/env python3
"""|both_in_SK| vs |neither_in_SK| across all binary p*.

τ involution at binary p* partitions ∏V into pairs. Categorize each pair:
  - both: both members in SK
  - one: exactly one in SK
  - neither: neither in SK

|SK| = 2·|both| + |one|.  |SK| ≥ 2^(n-1) ⟺ |both| ≥ |neither|.

This probe directly measures the |both|-vs-|neither| gap per (cycle, p*).
Look for: tightness, slack pattern, whether the gap is a clean function
of cycle length or ms structure.
"""
from itertools import product as iproduct
from collections import Counter, defaultdict
import time


def enumerate_multisets(n, max_product):
    out = []
    def rec(i, prefix, prod):
        if i == n:
            if prod < max_product: out.append(tuple(prefix))
            return
        for m in range(2, max_product + 1):
            new_prod = prod * m
            min_remaining = 2 ** (n - i - 1)
            if new_prod * min_remaining >= max_product: break
            prefix.append(m); rec(i + 1, prefix, new_prod); prefix.pop()
    rec(0, [], 1)
    return out


def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []; seen_cycles = set(); t0 = time.time()
    def dfs(start, config, det, path, movers):
        if len(found) >= max_cycles or time.time() - t0 > time_budget: return
        if len(path) > 1 and config == start:
            if set(movers) != set(range(n)): return
            L = len(movers)
            norm = min(tuple(path[i:L] + path[:i]) for i in range(L))
            if norm not in seen_cycles:
                seen_cycles.add(norm)
                found.append((list(path[:L]), list(movers), dict(det)))
            return
        if len(path) >= L_max: return
        for p in range(n):
            Lp = config[(p-1)%n]; Sp = config[p]; Rp = config[(p+1)%n]
            km = (p, Lp, Sp, Rp); forced = det.get(km)
            for new_val in range(ms[p]):
                if new_val == Sp: continue
                if forced is not None and forced != new_val: continue
                new_det = dict(det); new_det[km] = new_val; ok = True
                for i in range(n):
                    if i == p: continue
                    Li = config[(i-1)%n]; Si = config[i]; Ri = config[(i+1)%n]; ki = (i,Li,Si,Ri)
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


def compute_sk(vcng_set, move_entries, n):
    current = set(vcng_set)
    while True:
        victims = set()
        for c in current:
            has_forced = False
            for p in range(n):
                ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                if ctx in move_entries:
                    nc = list(c); nc[p] = move_entries[ctx]; nc = tuple(nc)
                    if nc in current: has_forced = True; break
            if not has_forced: victims.add(c)
        if not victims: break
        current -= victims
    return current


def value_sets(cycle, n):
    V = [set() for _ in range(n)]
    for c in cycle:
        for i in range(n): V[i].add(c[i])
    return V


def measure(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    if not SK: return None

    bin_ps = [p for p in range(n) if ms[p] == 2]
    if not bin_ps: return None

    out = []
    for p_star in bin_ps:
        v0, v1 = sorted(V[p_star])
        seen = set(); both = 0; one = 0; neither = 0
        for c in VC:
            if c in seen: continue
            tc = list(c); tc[p_star] = v1 if c[p_star] == v0 else v0; tc = tuple(tc)
            seen.add(c); seen.add(tc)
            in_sk_c = c in SK
            in_sk_tc = tc in SK
            if in_sk_c and in_sk_tc: both += 1
            elif in_sk_c or in_sk_tc: one += 1
            else: neither += 1
        pairs_total = len(VC) // 2
        assert both + one + neither == pairs_total
        # |SK| = 2·both + one. Bound 2^(n-1) requires both >= neither.
        gap = both - neither
        out.append({
            'p_star': p_star, 'both': both, 'one': one, 'neither': neither,
            'pairs_total': pairs_total, 'gap': gap,
            'SK_size_via_formula': 2*both + one,
        })
    return {'ms': ms, 'n': n, 'L': L, 'SK_size': len(SK),
            '|VC|': len(VC), 'per_p': out}


def main():
    plan = [
        (5, 1, 40, 8.0, 20),
        (6, 2, 15, 10.0, 20),
        (7, 10, 5, 15.0, 22),
        (8, 60, 3, 20.0, 24),
    ]
    by_n = defaultdict(list)
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets  L_max={L_max} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2*n+2: continue
                r = measure(ms, n, cycle, movers, det)
                if r is None: continue
                by_n[n].append(r)
            if (idx+1) % max(1, len(multisets)//5) == 0:
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s recs={len(by_n[n])}", flush=True)

    print(f"\n{'='*78}\n|both| vs |neither| (binary p* involution)\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        bound = 2 ** (n - 1)
        pairs = [(r, p) for r in recs for p in r['per_p']]
        # Count: gap >= 0?  gap distribution?
        gap_pos = sum(1 for _, p in pairs if p['gap'] >= 0)
        gap_neg = sum(1 for _, p in pairs if p['gap'] < 0)
        min_gap = min(p['gap'] for _, p in pairs)
        max_gap = max(p['gap'] for _, p in pairs)
        avg_gap = sum(p['gap'] for _, p in pairs) / len(pairs)
        # |SK| ≥ 2^(n-1) per pair
        sk_ok = sum(1 for _, p in pairs if p['SK_size_via_formula'] >= bound)
        # Tight cases: gap=0?
        gap0 = sum(1 for _, p in pairs if p['gap'] == 0)
        neither_0 = sum(1 for _, p in pairs if p['neither'] == 0)
        print(f"\n  n={n}  bound 2^(n-1)={bound}  records={len(recs)}  pairs={len(pairs)}")
        print(f"  |SK| ≥ 2^(n-1) via formula: {sk_ok}/{len(pairs)}")
        print(f"  gap (both - neither) range: min/avg/max = {min_gap}/{avg_gap:.1f}/{max_gap}")
        print(f"  gap ≥ 0: {gap_pos}  gap < 0: {gap_neg}  gap == 0 (tight): {gap0}")
        print(f"  |neither|==0: {neither_0}/{len(pairs)} ({100*neither_0/len(pairs):.1f}%)")
        # Show examples: smallest gap records
        sorted_pairs = sorted(pairs, key=lambda x: x[1]['gap'])[:5]
        for r, p in sorted_pairs:
            print(f"    min-gap ex: ms={r['ms']} L={r['L']} p*={p['p_star']}"
                  f"  both={p['both']} one={p['one']} neither={p['neither']}"
                  f"  gap={p['gap']}  |SK|={r['SK_size']}")


if __name__ == "__main__":
    main()
