#!/usr/bin/env python3
"""Where does τ(fragile_0) land?

fragile_0 = configs c in SK with c[p*]=v0 and τ(c) ∉ SK_1.
τ(c) is in ∏V_p (binary p* so flip stays in V_p*). Where does it land?
  (A) cycle
  (B) VC_NG \ SK (peeled out)
  (C) nowhere else possible — τ(c) ∈ ∏V guaranteed

Conjecture: τ(fragile_0) ⊆ cycle (purely).
If TRUE, then |fragile_0| ≤ |cycle ∩ slice_1|, and similarly |fragile_1|.
Combined with slice balance at a binary p*, gives clean Lemma C.

Measure per (cycle, p*):
  - |fragile_0|, |fragile_1|
  - split of τ(fragile_0) into {cycle, peel_residue}
  - Same for fragile_1
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


def flip(c, p, v0, v1):
    nc = list(c); nc[p] = v1 if c[p] == v0 else v0; return tuple(nc)


def measure(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    fc = Counter(movers)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    SK = compute_sk(VC_NG, move_entries, n)
    if not SK: return None

    # Binary procs with |V|=2 — applies to any ms[p]=2 in a cycle
    bin_ps = [p for p in range(n) if ms[p] == 2]
    if not bin_ps: return None

    peel_residue = VC_NG - SK  # configs that got peeled out of VC_NG

    out = []
    for p_star in bin_ps:
        v0, v1 = sorted(V[p_star])
        SK_0 = {c for c in SK if c[p_star] == v0}
        SK_1 = {c for c in SK if c[p_star] == v1}
        matched_0 = {c for c in SK_0 if flip(c, p_star, v0, v1) in SK_1}
        fragile_0 = SK_0 - matched_0
        fragile_1 = {c for c in SK_1 if flip(c, p_star, v0, v1) not in SK_0}
        # Where does τ(fragile_0) land?
        f0_to_cycle = sum(1 for c in fragile_0 if flip(c, p_star, v0, v1) in cycle_set)
        f0_to_peel = sum(1 for c in fragile_0 if flip(c, p_star, v0, v1) in peel_residue)
        f1_to_cycle = sum(1 for c in fragile_1 if flip(c, p_star, v0, v1) in cycle_set)
        f1_to_peel = sum(1 for c in fragile_1 if flip(c, p_star, v0, v1) in peel_residue)
        out.append({
            'p_star': p_star, 'fc_p': fc[p_star],
            'SK0': len(SK_0), 'SK1': len(SK_1),
            'matched_0': len(matched_0),
            'fragile_0': len(fragile_0), 'fragile_1': len(fragile_1),
            'f0_to_cycle': f0_to_cycle, 'f0_to_peel': f0_to_peel,
            'f1_to_cycle': f1_to_cycle, 'f1_to_peel': f1_to_peel,
            'cycle_slice0': sum(1 for c in cycle_set if c[p_star] == v0),
            'cycle_slice1': sum(1 for c in cycle_set if c[p_star] == v1),
        })
    return {'ms': ms, 'n': n, 'L': L, 'SK_size': len(SK), 'per_p': out}


def main():
    plan = [
        (5, 1, 40, 8.0, 20),
        (6, 2, 15, 10.0, 22),
        (7, 10, 5, 15.0, 24),
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

    print(f"\n{'='*78}\nτ(fragile) destination analysis\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        pairs = [(r, p) for r in recs for p in r['per_p']]
        # How much of fragile lands in cycle vs peel?
        total_frag = sum(p['fragile_0'] + p['fragile_1'] for _, p in pairs)
        total_to_cycle = sum(p['f0_to_cycle'] + p['f1_to_cycle'] for _, p in pairs)
        total_to_peel = sum(p['f0_to_peel'] + p['f1_to_peel'] for _, p in pairs)
        n_all_cycle = sum(1 for _, p in pairs
                           if p['f0_to_peel'] == 0 and p['f1_to_peel'] == 0)
        # Key claim: |fragile_0| <= |cycle ∩ slice_1|?
        bound_ok = sum(1 for _, p in pairs
                        if p['fragile_0'] <= p['cycle_slice1']
                       and p['fragile_1'] <= p['cycle_slice0'])
        print(f"\n  n={n}  records={len(recs)}  pairs (rec, p*)={len(pairs)}")
        print(f"  total fragile: {total_frag}  → cycle: {total_to_cycle}"
              f"  → peel: {total_to_peel}")
        print(f"  pairs with τ(fragile) ⊆ cycle (no peel): {n_all_cycle}/{len(pairs)}"
              f"  ({100*n_all_cycle/max(1,len(pairs)):.1f}%)")
        print(f"  pairs with |fragile_v| ≤ |cycle ∩ slice_{{1-v}}|: {bound_ok}/{len(pairs)}"
              f"  ({100*bound_ok/max(1,len(pairs)):.1f}%)")
        # Show a few records
        for i, (r, p) in enumerate(pairs[:3]):
            print(f"    eg ms={r['ms']} L={r['L']} p*={p['p_star']} fc_p={p['fc_p']}"
                  f"  frag0={p['fragile_0']} (cy={p['f0_to_cycle']} pl={p['f0_to_peel']})"
                  f"  frag1={p['fragile_1']} (cy={p['f1_to_cycle']} pl={p['f1_to_peel']})"
                  f"  cycle_slice={p['cycle_slice0']}/{p['cycle_slice1']}")


if __name__ == "__main__":
    main()
