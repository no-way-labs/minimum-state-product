#!/usr/bin/env python3
"""Does π_{p*}(SK) CONTAIN the binary (n-1)-cube at a fc-2 processor p*?

Three versions of Lemma C's projection claim, in increasing strength:
   (i)  |π_{p*}(SK)| ≥ 2^(n-1)                (what Lemma C states)
   (ii) π_{p*}(SK) ⊇ {0,1}^(n-1) ∩ ∏_{q≠p*} V_q   (binary cube covered)
   (iii) π_{p*}(SK) = ∏_{q≠p*} V_q              (every (n-1)-tuple covered)

Per-record we measure all three at each fc-2 processor p*, and report:
 - best p* for (ii) — always covers binary cube?
 - best p* for (iii) — always covers full product?
 - if ∃ p* with (ii): 100% ⇒ a clean analytical target
 - if NEVER ∃ p* with (ii) in some record: the proof approach via
   "find a good p* that surjects onto binary cube" is dead

Reuses infrastructure from probe_sk_floor_breadth_2026-04-16.
"""
from itertools import product as iproduct
from collections import Counter
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
    if not SK:
        return None

    # For each coord p, compute |π_p(SK)| and check (i), (ii), (iii)
    results = []
    for p in range(n):
        # The projection drops coordinate p
        proj = {tuple(c[:p] + c[p+1:]) for c in SK}
        proj_size = len(proj)

        # (ii) binary cube coverage: does proj ⊇ {0,1}^(n-1) ∩ ∏_{q≠p} V_q?
        # Only meaningful if every V_q (q≠p) contains both 0 and 1.
        binary_present = all(0 in V[q] and 1 in V[q] for q in range(n) if q != p)
        bin_cube_covered = False
        bin_cube_size = 2 ** (n - 1) if binary_present else 0
        if binary_present:
            bin_cube = set(iproduct(*[[0, 1] for _ in range(n - 1)]))
            bin_cube_covered = bin_cube.issubset(proj)

        # (iii) full product coverage
        full_prod_size = 1
        for q in range(n):
            if q != p: full_prod_size *= len(V[q])
        full_covered = (proj_size == full_prod_size)

        results.append({
            'p': p, 'fc_p': fc[p], 'Vp_size': len(V[p]),
            'proj_size': proj_size,
            'i_ge_2nm1': proj_size >= 2 ** (n - 1),
            'ii_bin_cube_covered': bin_cube_covered,
            'iii_full_covered': full_covered,
            'binary_present': binary_present,
            'full_prod_size': full_prod_size,
        })

    return {
        'ms': ms, 'n': n, 'L': L,
        'SK_size': len(SK),
        'V_sizes': [len(v) for v in V],
        'fc': dict(fc),
        'per_coord': results,
    }


def main():
    # Dense sampling at each n. Each record measures all n coords.
    plan = [
        (5, 1, 10, 2.0, 16),
        (6, 1, 10, 3.0, 17),
        (7, 20, 5, 4.0, 18),
        (8, 150, 4, 12.0, 22),
    ]
    by_n = {}
    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)[::stride]
        print(f"\n=== n={n}  {len(multisets)} multisets ===", flush=True)
        recs = []
        t0 = time.time()
        for idx, ms in enumerate(multisets):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                if len(movers) < 2*n+2: continue
                r = measure(ms, n, cycle, movers, det)
                if r is None: continue
                recs.append(r)
            if (idx+1) % max(1, len(multisets)//5) == 0:
                print(f"  [{idx+1}/{len(multisets)}] {time.time()-t0:.0f}s recs={len(recs)}", flush=True)
        by_n[n] = recs

    print(f"\n{'='*78}\nResults\n{'='*78}")
    for n in sorted(by_n):
        recs = by_n[n]
        if not recs: continue
        total = len(recs)
        # For each record, is there ANY p with (i), (ii), (iii)?
        any_i  = sum(1 for r in recs if any(pc['i_ge_2nm1']        for pc in r['per_coord']))
        any_ii = sum(1 for r in recs if any(pc['ii_bin_cube_covered'] for pc in r['per_coord']))
        any_iii = sum(1 for r in recs if any(pc['iii_full_covered']  for pc in r['per_coord']))
        # Restricted to fc-2 coords
        fc2_any_i  = sum(1 for r in recs if any(pc['i_ge_2nm1']        for pc in r['per_coord'] if pc['fc_p']==2))
        fc2_any_ii = sum(1 for r in recs if any(pc['ii_bin_cube_covered'] for pc in r['per_coord'] if pc['fc_p']==2))
        fc2_any_iii= sum(1 for r in recs if any(pc['iii_full_covered']  for pc in r['per_coord'] if pc['fc_p']==2))
        # Always: coord p with V_p=2 and fc=2 → binary fc-2 processor
        bin_fc2_any_ii = sum(1 for r in recs if any(
            pc['ii_bin_cube_covered'] for pc in r['per_coord']
            if pc['fc_p']==2 and pc['Vp_size']==2))
        has_any_bin_fc2 = sum(1 for r in recs if any(
            pc['fc_p']==2 and pc['Vp_size']==2 for pc in r['per_coord']))

        print(f"\n  n={n}  records={total}  bound 2^(n-1)={2**(n-1)}")
        print(f"    ∃ p : |π_p(SK)| ≥ 2^(n-1)      {any_i:>4}/{total} ({100*any_i/total:.1f}%)")
        print(f"    ∃ p : π_p(SK) ⊇ {{0,1}}^(n-1)     {any_ii:>4}/{total} ({100*any_ii/total:.1f}%)")
        print(f"    ∃ p : π_p(SK) = full prod       {any_iii:>4}/{total} ({100*any_iii/total:.1f}%)")
        print(f"    restricted to fc-2 coords:")
        print(f"      ∃ fc-2 p with (i)              {fc2_any_i:>4}/{total} ({100*fc2_any_i/total:.1f}%)")
        print(f"      ∃ fc-2 p with (ii) bin cube    {fc2_any_ii:>4}/{total} ({100*fc2_any_ii/total:.1f}%)")
        print(f"      ∃ fc-2 p with (iii) full       {fc2_any_iii:>4}/{total} ({100*fc2_any_iii/total:.1f}%)")
        print(f"    records with ≥1 binary fc-2 coord: {has_any_bin_fc2}/{total} ({100*has_any_bin_fc2/total:.1f}%)")
        print(f"    of those, bin-fc-2 covers bin cube: {bin_fc2_any_ii}/{has_any_bin_fc2 or 1} "
              f"({100*bin_fc2_any_ii/(has_any_bin_fc2 or 1):.1f}%)")

        # Failure-mode diagnostic: records where NO coord covers binary cube
        fail = [r for r in recs if not any(pc['ii_bin_cube_covered'] for pc in r['per_coord'])]
        if fail:
            print(f"    !! {len(fail)} records have NO coord covering binary cube")
            for r in fail[:3]:
                print(f"       ms={r['ms']} L={r['L']} |SK|={r['SK_size']} fc={r['fc']} V={r['V_sizes']}")
                for pc in r['per_coord']:
                    print(f"         p={pc['p']} fc={pc['fc_p']} |V|={pc['Vp_size']} "
                          f"|proj|={pc['proj_size']}/{pc['full_prod_size']} "
                          f"bin_ok={pc['ii_bin_cube_covered']}")


if __name__ == "__main__":
    main()
