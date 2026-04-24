#!/usr/bin/env python3
"""(γ) Cleaner reformulations of Lemma C.

Candidates to test empirically:
  (A) P1-proj: ∃p. |π_{drop-p}(SK)| ≥ 2^(n-1)
  (B) P1-proj universal: ∀p. |π_{drop-p}(SK)| ≥ 2^(n-1)
  (C) Halfspace: ∃(p,v). |{c ∈ SK : c[p]=v}| ≥ 2^(n-1)
  (D) Halfspace universal: ∀p. ∃v. |{c ∈ SK : c[p]=v}| ≥ 2^(n-1)
  (E) Binary-slice: fix all but 2 positions p,q; how big is max 2D slice?
  (F) Union form: |π_p(SK) ∪ π_p(C)| ≥ 2^(n-1) for some p
  (G) Connected slice: fixed c[p]=v projection slice has SK-structure

For each reformulation, compute:
  - Does it hold?
  - Is the margin substantial (so the reformulation has slack)?
  - Is there a non-trivial reformulation with tight slack (indicating causal)?
"""
from itertools import product as iproduct, combinations
from collections import defaultdict, Counter
import time, sys
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


def compute_sk(ms, n, cycle, det):
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
    return remaining, V_sorted, cycle_set


def reform_probe(n, ms, cycle, det, bound):
    sk, V_sorted, cycle_set = compute_sk(ms, n, cycle, det)
    if not sk: return None

    # (A,B) P1-proj sizes
    proj_sizes = []
    for p in range(n):
        proj = {tuple(c[i] for i in range(n) if i != p) for c in sk}
        proj_sizes.append(len(proj))

    # (C,D) Halfspace sizes
    halfspace_per_p = {}
    for p in range(n):
        counts = {v: sum(1 for c in sk if c[p] == v) for v in V_sorted[p]}
        halfspace_per_p[p] = counts

    # (F) Union with π(C)
    union_sizes = []
    for p in range(n):
        proj_sk = {tuple(c[i] for i in range(n) if i != p) for c in sk}
        proj_c  = {tuple(c[i] for i in range(n) if i != p) for c in cycle_set}
        union_sizes.append(len(proj_sk | proj_c))

    # (E) Max 2D slice = |SK with 2 positions dropped|
    proj2_sizes = []
    for p, q in combinations(range(n), 2):
        proj = {tuple(c[i] for i in range(n) if i not in {p, q}) for c in sk}
        proj2_sizes.append((p, q, len(proj)))

    return {
        '|SK|': len(sk), 'bound': bound, 'n': n,
        'proj_sizes': proj_sizes,
        'halfspace_per_p': halfspace_per_p,
        'union_sizes': union_sizes,
        'proj2_max': max(s for _,_,s in proj2_sizes),
    }


def main():
    print("=" * 100)
    print("(γ) REFORMULATIONS: P1-proj, halfspace, union, 2D-slice")
    print("=" * 100)

    plan = [
        (5, [(2,2,2,3,3), (2,2,2,3,4), (2,2,3,3,3)], 15, 3, 15.0),
        (6, [(2,2,2,3,3,3), (2,2,3,3,3,3)], 17, 2, 25.0),
        (7, [(2,2,2,3,3,3,3)], 17, 1, 35.0),
        (8, [(2,2,2,3,3,3,3,3)], 19, 1, 50.0),
    ]

    summary_A = []; summary_B = []; summary_C = []; summary_D = []
    summary_F = []; summary_E = []

    for n, ms_list, L_max, max_cycles, tb in plan:
        bound = 2 ** (n - 1)
        print(f"\n=== n={n} bound={bound} ===")
        for ms in ms_list:
            cycles = enumerate_cycles(ms, n, L_min=2*n+2, L_max=L_max,
                                      time_budget=tb, max_cycles=max_cycles)
            for ci, (cycle, movers, det) in enumerate(cycles):
                r = reform_probe(n, ms, cycle, det, bound)
                if r is None: continue
                print(f"\n ms={ms} L={len(cycle)} cycle#{ci} |SK|={r['|SK|']}")

                # (A) ∃p |π_p(SK)| ≥ bound
                maxA = max(r['proj_sizes'])
                minA = min(r['proj_sizes'])
                print(f"  (A) ∃p |π_p|≥{bound}: max={maxA} min={minA}  "
                      f"({'YES' if maxA>=bound else 'NO'})")
                print(f"      proj sizes: {r['proj_sizes']}")
                # (B) ∀p
                print(f"  (B) ∀p |π_p|≥{bound}: {'YES' if minA>=bound else 'NO'}  "
                      f"(margin={minA-bound})")
                # (C) ∃(p,v) halfspace ≥ bound
                hs_all = [(p, v, c) for p, vs in r['halfspace_per_p'].items()
                          for v, c in vs.items()]
                maxhs = max(c for _,_,c in hs_all)
                print(f"  (C) ∃(p,v) halfspace≥{bound}: max={maxhs}  "
                      f"({'YES' if maxhs>=bound else 'NO'})")
                # (D) ∀p ∃v halfspace ≥ bound
                dhs_min = min(max(c for v,c in vs.items()) for vs in r['halfspace_per_p'].values())
                print(f"  (D) ∀p∃v halfspace≥{bound}: {'YES' if dhs_min>=bound else 'NO'}  "
                      f"(∀p max over v: min={dhs_min})")
                # (F) union π_p(SK)∪π_p(C) ≥ bound
                maxU = max(r['union_sizes']); minU = min(r['union_sizes'])
                print(f"  (F) ∃p |π_p(SK)∪π_p(C)|≥{bound}: max={maxU}  "
                      f"({'YES' if maxU>=bound else 'NO'})")
                print(f"      ∀p |π_p(SK)∪π_p(C)|≥{bound}: min={minU}  "
                      f"({'YES' if minU>=bound else 'NO'})")
                # (E) 2D slice
                print(f"  (E) max 2D-drop |π_{{pq}}|: {r['proj2_max']}  "
                      f"(vs 2^(n-2)={2**(n-2)}: {'≥' if r['proj2_max']>=2**(n-2) else '<'})")

                summary_A.append((n, ms, len(cycle), maxA, bound))
                summary_B.append((n, ms, len(cycle), minA, bound))
                summary_C.append((n, ms, len(cycle), maxhs, bound))
                summary_D.append((n, ms, len(cycle), dhs_min, bound))
                summary_F.append((n, ms, len(cycle), maxU, bound))

    print("\n" + "=" * 100)
    print("SUMMARY")
    print("=" * 100)
    print(f"(A) ∃p |π_p|≥bound: {sum(1 for a in summary_A if a[3]>=a[4])}/{len(summary_A)}")
    print(f"(B) ∀p |π_p|≥bound: {sum(1 for a in summary_B if a[3]>=a[4])}/{len(summary_B)}")
    print(f"(C) ∃(p,v) halfspace≥bound: {sum(1 for a in summary_C if a[3]>=a[4])}/{len(summary_C)}")
    print(f"(D) ∀p∃v halfspace≥bound: {sum(1 for a in summary_D if a[3]>=a[4])}/{len(summary_D)}")
    print(f"(F) ∃p |π_p(SK)∪π_p(C)|≥bound: {sum(1 for a in summary_F if a[3]>=a[4])}/{len(summary_F)}")


if __name__ == "__main__":
    main()
