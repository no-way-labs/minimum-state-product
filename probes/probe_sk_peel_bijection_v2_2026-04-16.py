#!/usr/bin/env python3
"""Given anchors = {min(V_q), max(V_q)} (96.7%) or some other 2-subset (3.3%),
extract: what IS the peel structure?

Hypothesis B: peel(N_1) ≅ a subset of ∏_q {min(V_q), max(V_q)}, specifically
  {c ∈ ∏_q {min, max} : c is close to some c_i ∈ cycle}

Tests:
  H_B1: Each peel config c_s has c_s[q] ∈ {min(V_q), max(V_q)} for ALL q (not just anchor q)
  H_B2: Each peel config c_s agrees with some c_i on all but 1 position
        — but what about positions q' where c_i[q'] is "mid" value?
        Check: c_s[q'] = c_i[q'] always, so if c_i has mid values, c_s[q'] is mid too
  H_B3: The cycle itself is always all-extreme (c_i[q] ∈ {min(V_q), max(V_q)} for all i, q)?
        If YES, then peel ⊆ {min, max}^n.
        If NO (cycle has mid values), peel extends beyond {min, max}^n.

The 3.3% exceptions where anchors ≠ {min, max}: what's their pattern?

At n=7, test: |peel| = 64 = 2^(n-1). 2^n = 128. What sign parity cuts this in half?
  Define sign_q(c) = 0 if c[q] = min(V_q), 1 if c[q] = max(V_q), undefined otherwise.
  If sign_q defined for all q on c ∈ peel, compute parity. Is it constant over peel?
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


def compute_peel(ms, n, cycle, movers, det):
    L = len(movers)
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    N1 = set()
    for c in cycle:
        for q in range(n):
            for v in range(ms[q]):
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)
    adj = defaultdict(list)
    for c in N1:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in N1:
                    adj[c].append(nc)
    cur = set(N1)
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove: break
        cur -= to_remove
    return cur


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    peel = compute_peel(ms, n, cycle, movers, det)
    if not peel: return None

    # B1: Are peel configs within ∏_q {min, max} of V_q?
    extreme_only_cycle = all(c[q] in {min(V[q]), max(V[q])} for c in cycle for q in range(n))
    extreme_only_peel = all(c[q] in {min(V[q]), max(V[q])} for c in peel for q in range(n))

    # B3: If cycle has no "mid" values, peel lives in {min, max}^n
    mid_positions = sum(1 for c in cycle for q in range(n) if c[q] not in {min(V[q]), max(V[q])})

    # Parity test: parity of sign vector on peel
    parities = []
    all_extreme = True
    for c in peel:
        par = 0
        ok = True
        for q in range(n):
            lo, hi = min(V[q]), max(V[q])
            if c[q] == lo: bit = 0
            elif c[q] == hi: bit = 1
            else: ok = False; break
            par ^= bit
        if ok:
            parities.append(par)
        else:
            all_extreme = False
    par_counts = Counter(parities)

    # Parity on cycle
    cyc_par = []
    for c in cycle:
        par = 0
        ok = True
        for q in range(n):
            lo, hi = min(V[q]), max(V[q])
            if c[q] == lo: bit = 0
            elif c[q] == hi: bit = 1
            else: ok = False; break
            par ^= bit
        if ok:
            cyc_par.append(par)
    cyc_par_counts = Counter(cyc_par)

    # Full cube count
    full_cube = 2 ** n

    # Bijection test at n=7 (|peel|=64=2^(n-1))
    peel_in_cube = sum(1 for c in peel if all(c[q] in {min(V[q]), max(V[q])} for q in range(n)))

    return {
        'n': n, 'ms': ms, 'L': L, 'peel_size': len(peel),
        'extreme_only_cycle': extreme_only_cycle,
        'extreme_only_peel': extreme_only_peel,
        'mid_in_cycle': mid_positions,
        'par_counts': dict(par_counts),
        'cyc_par_counts': dict(cyc_par_counts),
        'all_extreme': all_extreme,
        'peel_in_cube': peel_in_cube,
    }


def main():
    print("=" * 72, flush=True)
    print("peel ⊆ extreme-value cube?", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 40, 3.0, 16),
        (6, 8, 15, 3.0, 17),
        (7, 40, 8, 4.0, 17),
    ]
    all_records = []
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2: continue
                r = analyze(ms, n, cycle, movers, det)
                if r is None: continue
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 6) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        print(f"\n  n={n}  records={len(recs)}")
        psize = [r['peel_size'] for r in recs]
        print(f"    |peel|: min={min(psize)} max={max(psize)} avg={sum(psize)/len(psize):.1f}  2^(n-1)={2**(n-1)}")
        eoc = sum(1 for r in recs if r['extreme_only_cycle'])
        eop = sum(1 for r in recs if r['extreme_only_peel'])
        print(f"    cycle ⊆ {{min,max}}^n (all-extreme cycle): {eoc}/{len(recs)}")
        print(f"    peel ⊆ {{min,max}}^n: {eop}/{len(recs)}")
        # Parity: when all_extreme, look at parity split
        ae = [r for r in recs if r['all_extreme']]
        print(f"    all-extreme peel: {len(ae)}/{len(recs)}")
        # Aggregate parity
        par_agg = Counter()
        cyc_par_agg = Counter()
        for r in ae:
            for p, c in r['par_counts'].items():
                par_agg[p] += c
        for r in recs:
            for p, c in r['cyc_par_counts'].items():
                cyc_par_agg[p] += c
        print(f"    parity distribution in peel (all-extreme recs): {dict(par_agg)}")
        print(f"    parity distribution in cycle: {dict(cyc_par_agg)}")
        # Per-record parity: is it all one parity?
        single_par_peel = sum(1 for r in ae if len(r['par_counts']) == 1)
        print(f"    peel is single-parity: {single_par_peel}/{len(ae)} of all-extreme recs")
        single_par_cyc = sum(1 for r in recs if len(r['cyc_par_counts']) == 1 and sum(r['cyc_par_counts'].values()) > 0)
        print(f"    cycle is single-parity: {single_par_cyc}/{len(recs)}")


if __name__ == "__main__":
    main()
