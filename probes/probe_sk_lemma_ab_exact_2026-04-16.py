#!/usr/bin/env python3
"""Lemma A (L=2n) and Lemma B (L=2n+1) exact closed-form check.

Lemma A:  |SK(C)| = 2^n - 2n - 2·[n odd]   when L = 2n
Lemma B:  |SK(C)| = Lemma_A(n) + 2^(n-3) - 1  when L = 2n+1

If these are exact, we have a base case for the L=2n+2 reduction.
If they're off, the whole clouds reduction needs re-examination.

Also records:
 - records per L bucket
 - min/max/avg |SK| per (n, L)
 - violations of the closed form
"""
from itertools import product as iproduct
from collections import Counter, defaultdict
import time


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


def m_n_sharp(n):
    if 5 <= n <= 8: return 32 * 3 ** (n - 4)
    return 4 * 3 ** (n - 2)


def enumerate_all_cycles(ms, n, L_max, time_budget, max_cycles):
    all_starts = list(iproduct(*[range(m) for m in ms]))
    found = []
    seen_cycles = set()
    t0 = time.time()
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


def lemma_a_exact(n):
    """2^n - 2n - 2·[n odd]"""
    return 2**n - 2*n - (2 if n % 2 else 0)


def lemma_b_exact(n):
    """lemma_a(n) + 2^(n-3) - 1"""
    return lemma_a_exact(n) + 2**(n-3) - 1


def measure(ms, n, cycle):
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    # build move_entries from cycle: successive configs give one forced move per step
    move_entries = {}
    L = len(cycle)
    for t in range(L):
        c = cycle[t]; nxt = cycle[(t+1) % L]
        diffs = [i for i in range(n) if c[i] != nxt[i]]
        if len(diffs) != 1: return None
        p = diffs[0]
        ctx = (p, c[(p-1)%n], c[p], c[(p+1)%n])
        move_entries[ctx] = nxt[p]
    SK = compute_sk(VC_NG, move_entries, n)
    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'V_sizes': [len(v) for v in V],
        'VC_NG_size': len(VC_NG),
    }


def main():
    plan = [
        (5, 1, 20, 2.0, 12),   # Lemma A+B regime only: L ∈ {10, 11}
        (6, 1, 20, 3.0, 14),   # L ∈ {12, 13}
        (7, 1, 15, 5.0, 16),   # L ∈ {14, 15}
        (8, 20, 8, 10.0, 18),  # L ∈ {16, 17}, stride-20
    ]
    by_n_L = defaultdict(list)
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets  L_max={L_max} ===", flush=True)
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L not in (2*n, 2*n+1): continue
                r = measure(ms, n, cycle)
                if r is None: continue
                by_n_L[(n, L)].append(r)
            if (idx+1) % max(1, len(multisets)//5) == 0:
                cnt = sum(len(v) for (nn, _), v in by_n_L.items() if nn == n)
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s recs={cnt}", flush=True)

    print(f"\n{'='*78}\nResults — Lemma A (L=2n) and Lemma B (L=2n+1)\n{'='*78}")
    for n in sorted(set(nn for nn, _ in by_n_L)):
        A_pred = lemma_a_exact(n)
        B_pred = lemma_b_exact(n)
        print(f"\n  n={n}")
        print(f"    Lemma A predicts |SK| = {A_pred}  (= 2^{n} - 2·{n} - 2·[{n} odd])")
        print(f"    Lemma B predicts |SK| = {B_pred}  (= Lemma_A + 2^{n-3} - 1)")
        for L in (2*n, 2*n+1):
            recs = by_n_L.get((n, L), [])
            if not recs:
                print(f"    L={L}: NO RECORDS")
                continue
            pred = A_pred if L == 2*n else B_pred
            sks = sorted(r['SK_size'] for r in recs)
            matches = sum(1 for s in sks if s == pred)
            above = sum(1 for s in sks if s > pred)
            below = sum(1 for s in sks if s < pred)
            print(f"    L={L}: {len(recs)} recs  |SK| min/avg/max = {sks[0]}/{sum(sks)/len(sks):.1f}/{sks[-1]}")
            print(f"         vs predicted {pred}:  = {matches}   > {above}   < {below}")
            # Show deviations
            devs = Counter(s - pred for s in sks)
            print(f"         deviation dist: {dict(devs.most_common(10))}")
            if below:
                viol = [r for r in recs if r['SK_size'] < pred][:3]
                print(f"    !! Below-prediction samples:")
                for r in viol:
                    print(f"       ms={r['ms']}  |SK|={r['SK_size']} (short by {pred-r['SK_size']})")


if __name__ == "__main__":
    main()
