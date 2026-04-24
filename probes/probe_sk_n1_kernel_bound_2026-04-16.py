#!/usr/bin/env python3
"""Is |peel(N_1(C))| ≥ 2^(n-1) always?

KEY: if yes, this proves Lemma C (|SK| ≥ 2^(n-1)) via:
  peel is monotone ⇒ peel(N_1(C)) ⊆ peel(VC-NG) = SK.

Tests:
  B1: |peel(N_1(C))| ≥ 2^(n-1)?
  B2: |peel(N_1(C))| == |N_1(C) ∩ SK|?  (would mean peel(N_1(C)) = N_1(C) ∩ SK)
  B3: Is peel(N_1(C)) the Hamming-1 slice of SK?
  B4: Distribution: min / median / max of |peel(N_1(C))| - 2^(n-1)
  B5: Per-position decomposition: for each q ∈ [n], |{c ∈ peel(N_1(C)) : c differs from C at q}|
"""
from itertools import product as iproduct
from collections import defaultdict
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
    VC_NG = set(iproduct(*[sorted(V[i]) for i in range(n)])) - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    N1 = neighborhood_1(cycle, V, n, ms)
    N1_peel = compute_sk(N1, move_entries, n)
    per_pos = [0] * n
    for c in N1_peel:
        for q in range(n):
            if c[q] not in {cc[q] for cc in cycle} or any(c[i] != cc[i] and i == q for cc in cycle for i in range(n)):
                pass
    # Count by differing position (using nearest cycle config)
    per_pos_count = [0] * n
    for c in N1_peel:
        found_q = None
        for cc in cycle:
            diff = [i for i in range(n) if c[i] != cc[i]]
            if len(diff) == 1:
                if found_q is None:
                    found_q = diff[0]
                elif diff[0] != found_q:
                    found_q = -1
        if found_q is not None and found_q >= 0:
            per_pos_count[found_q] += 1
    return {
        'n': n, 'ms': ms, 'L': L,
        'SK_size': len(SK),
        'N1_size': len(N1),
        'N1_peel_size': len(N1_peel),
        'bound_2nm1': 2 ** (n - 1),
        'peel_ge_2nm1': len(N1_peel) >= 2 ** (n - 1),
        'SK_ge_2nm1': len(SK) >= 2 ** (n - 1),
        'peel_eq_SK_cap_N1': N1_peel == (SK & N1),
        'per_pos': per_pos_count,
    }


def main():
    print("=" * 72)
    print("Is |peel(N_1(C))| ≥ 2^(n-1)?")
    print("=" * 72)
    plan = [
        (8, 400, 4, 20.0, 20),
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
                if L < 2 * n + 2:
                    continue
                r = analyze(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
            if (idx + 1) % 5 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs:
            continue
        b1 = sum(1 for r in recs if r['peel_ge_2nm1'])
        b2 = sum(1 for r in recs if r['peel_eq_SK_cap_N1'])
        b3 = sum(1 for r in recs if r['SK_ge_2nm1'])
        min_peel = min(r['N1_peel_size'] for r in recs)
        avg_peel = sum(r['N1_peel_size'] for r in recs) / len(recs)
        bound = 2 ** (n - 1)
        print(f"\n  n={n}  records={len(recs)}  bound 2^(n-1) = {bound}")
        print(f"    B1 |peel(N_1(C))| ≥ 2^(n-1):          {b1}/{len(recs)} ({100*b1/len(recs):.1f}%)")
        print(f"    B2 peel(N_1(C)) = SK ∩ N_1(C):        {b2}/{len(recs)} ({100*b2/len(recs):.1f}%)")
        print(f"    B3 |SK| ≥ 2^(n-1):                    {b3}/{len(recs)} ({100*b3/len(recs):.1f}%)")
        print(f"    min |peel|={min_peel}  avg={avg_peel:.1f}  (bound={bound})")


if __name__ == "__main__":
    main()
