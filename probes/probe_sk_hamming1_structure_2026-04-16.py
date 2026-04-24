#!/usr/bin/env python3
"""Hamming-1 structure probe.

Prior immune probe found: for every c in SK, the min Hamming distance
to C is exactly 1. This means SK ⊂ N_1(C) := {c ∈ VC-NG : Hamming(c,C) = 1}.

Tests:
  H1: Is SK ⊆ N_1(C)? (already 100% by immune probe; verify here.)
  H2: |N_1(C)| vs |SK| — is SK close to all of N_1(C)?
  H3: Structural characterization of which N_1(C) configs are in SK:
      is it exactly those c whose single differing coordinate value lies
      in a specific subset, e.g. "opposite side" of the cycle value?
  H4: Does every c ∈ N_1(C) have a forced neighbor in N_1(C) ∪ C?
      (closure property that would give SK ⊇ a specific subset of N_1(C))
  H5: Does N_1(C) itself have a forced cycle? Equivalent to asking if the
      1-Hamming neighborhood of C already contains the peeling fixed point.
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
    """Peeling: remove c if it has no forced edge to remaining set."""
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


def hamming(a, b):
    return sum(1 for i in range(len(a)) if a[i] != b[i])


def neighborhood_1(cycle, V, n, ms):
    """All c in VC with Hamming(c, C) = 1."""
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
    # VC-NG
    VC_NG = set(iproduct(*[sorted(V[i]) for i in range(n)])) - cycle_set
    # Move entries (mover-only forced triples)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    N1 = neighborhood_1(cycle, V, n, ms)

    SK_sub_N1 = SK.issubset(N1)
    SK_sup_N1_cap_VC = SK.issuperset(N1 & VC_NG)
    # How many N1 configs are in SK
    SK_cap_N1 = SK & N1
    # H4: closure — every c in N1 has a forced edge to N1 ∪ C
    closure_count = 0
    closure_fail = 0
    for c in N1:
        has_forced_to_N1_or_C = False
        has_forced = False
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                has_forced = True
                v = move_entries[ctx]
                nc = list(c); nc[p] = v; nc = tuple(nc)
                if nc in N1 or nc in cycle_set:
                    has_forced_to_N1_or_C = True
                    break
        if has_forced:
            if has_forced_to_N1_or_C:
                closure_count += 1
            else:
                closure_fail += 1

    # H5: does N1 itself peel to a nonempty kernel?
    N1_sk = compute_sk(N1, move_entries, n)
    return {
        'n': n, 'ms': ms, 'L': L,
        'SK_size': len(SK),
        'N1_size': len(N1),
        'VC_NG_size': len(VC_NG),
        'SK_in_N1': SK_sub_N1,
        'SK_cap_N1_size': len(SK_cap_N1),
        'N1_minus_SK_size': len(N1 - SK),
        'closure_pass': closure_count,
        'closure_fail': closure_fail,
        'N1_peels_nonempty': len(N1_sk) > 0,
        'N1_SK_size': len(N1_sk),
    }


def main():
    print("=" * 72)
    print("Hamming-1 structure probe — is SK ≈ N_1(C)?")
    print("=" * 72)
    plan = [
        (5, 1, 200, 3.0, 14),
        (6, 8, 60, 2.0, 14),
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
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs:
            continue
        h1 = sum(1 for r in recs if r['SK_in_N1'])
        h5 = sum(1 for r in recs if r['N1_peels_nonempty'])
        cl_all = sum(1 for r in recs if r['closure_fail'] == 0)
        avg_sk = sum(r['SK_size'] for r in recs) / len(recs)
        avg_n1 = sum(r['N1_size'] for r in recs) / len(recs)
        avg_cap = sum(r['SK_cap_N1_size'] for r in recs) / len(recs)
        avg_n1_minus = sum(r['N1_minus_SK_size'] for r in recs) / len(recs)
        avg_n1sk = sum(r['N1_SK_size'] for r in recs) / len(recs)
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    H1 SK ⊆ N_1(C):                       {h1}/{len(recs)} ({100*h1/len(recs):.1f}%)")
        print(f"    H5 N_1(C) peels to nonempty kernel:   {h5}/{len(recs)} ({100*h5/len(recs):.1f}%)")
        print(f"    H4 closure: 100% forced→N_1(C)∪C:     {cl_all}/{len(recs)} ({100*cl_all/len(recs):.1f}%)")
        print(f"    avg |SK|={avg_sk:.1f}  |N_1(C)|={avg_n1:.1f}  |SK∩N1|={avg_cap:.1f}")
        print(f"    avg |N_1(C) \\ SK|={avg_n1_minus:.1f}")
        print(f"    avg |peel(N_1(C))|={avg_n1sk:.1f}")


if __name__ == "__main__":
    main()
