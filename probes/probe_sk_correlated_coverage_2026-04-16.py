#!/usr/bin/env python3
"""R1 probe: correlated coverage bound on round-0 sinks.

Handoff doc flags this as an open candidate: the independent
coverage bound Σ_p fc(p)·2^(n-3) = L·2^(n-3) overcounts because
adjacent positions share coordinates (ring topology). The true
covered set is smaller than the sum — leaving more uncovered
round-0 sinks than a naive bound would suggest.

Question: does the GAP between L·2^(n-3) (naive coverage sum) and
|covered| (true union size) SYSTEMATICALLY LEAVE ROOM for the
immune core ≥ 2^(n-1)?

Quantitatively: for each (ms, cycle):
  - U = |uncovered| (round-0 sinks in VC, i.e. no forced edge)
  - NC = |covered| = |VC| - U
  - naive = L·2^(n-3) (would-be coverage if positions were independent)
  - overcount = naive - NC (how much adjacency saves us)
  - required_slack = NC - (|VC| - 2^(n-1)) (what we need ≤ for immune ≥ 2^(n-1) to work after covered-only peeling)

Also sample intersection structure:
  - For adjacent p, q: |cov(p) ∩ cov(q)| — how correlated are they?

Note: "round-0 sinks" = uncovered in the forced NG-graph. Cascade
adds more sinks. So uncovered bounds the NONDEG0 floor, not immune.
This probe tests whether an argument at the coverage/uncovered level
can give immune ≥ 2^(n-1).
"""
from itertools import product as iproduct
from collections import defaultdict, Counter
import time, sys


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


def analyze_coverage(ms, n, cycle, movers, det):
    L = len(movers)
    cycle_set = set(cycle)
    V = value_sets(cycle, n)

    # Extract MOVE entries only (output ≠ input)
    move_entries = {}
    for (p, Lv, Sv, Rv), val in det.items():
        if val != Sv:
            move_entries[(p, Lv, Sv, Rv)] = val

    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set
    vc_ng_size = len(vc_ng)

    # Per-position coverage: which configs have context at p in move_entries
    cov = [set() for _ in range(n)]
    for c in vc_ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                cov[p].add(c)

    covered = set().union(*cov)
    uncovered = vc_ng - covered

    # Count fire per position (move entries per position)
    fc = [0] * n
    for (p, Lv, Sv, Rv) in move_entries:
        fc[p] += 1
    assert sum(fc) == L

    # Naive independent bound: Σ fc(p) × |contexts with that p value|
    #   Each move entry at p covers configs matching (p-1,p,p+1) at given values;
    #   the other n-3 coordinates are free over value_set V_i.
    #   So one move entry at p covers ∏_{i ∉ {p-1,p,p+1}} |V_i| configs.
    naive_per_entry = 1
    # Use product over all positions first, then divide — but V_i sizes vary.
    # Compute per-entry: each entry at p fixes values at (p-1, p, p+1). Free = n-3 coords.
    def naive_cov_at_p(p):
        free_size = 1
        for i in range(n):
            if i not in ((p - 1) % n, p, (p + 1) % n):
                free_size *= len(V[i])
        return free_size

    naive_total = sum(fc[p] * naive_cov_at_p(p) for p in range(n))

    # Adjacent-pair overlap (to measure correlation)
    pair_overlap = sum(len(cov[p] & cov[(p + 1) % n]) for p in range(n))

    # |VC-NG| - 2^(n-1) = required slack (how many rounds-0 sinks we can afford)
    target = 2 ** (n - 1)
    afford = vc_ng_size - target
    excess_uncovered = len(uncovered) - afford
    # If uncovered ≤ afford, we have enough covered to SUPPORT a ≥ 2^(n-1) immune core
    # (modulo cascade).

    return {
        'L': L,
        'ms': ms,
        'n': n,
        'vc_ng': vc_ng_size,
        'covered': len(covered),
        'uncovered': len(uncovered),
        'naive_total': naive_total,
        'naive_overcount': naive_total - len(covered),
        'pair_overlap': pair_overlap,
        'target': target,
        'afford': afford,
        'uncov_over_afford': excess_uncovered,   # ≤ 0 means coverage alone gives 2^(n-1) floor
    }


def main():
    print("=" * 72)
    print("R1 probe: correlated coverage — covered vs uncovered in VC-NG")
    print("=" * 72)

    plan = [
        (5, 1, 1500, 5.0, 16),
        (6, 3, 300, 5.0, 16),
        (7, 12, 100, 4.0, 16),
    ]

    all_records = []
    worst_per_n = {}

    for n, stride, max_cycles, tb, L_max in plan:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets (of {len(multisets)}) ===")
        t0 = time.time()
        worst = None
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2:
                    continue
                r = analyze_coverage(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
                if worst is None or r['uncov_over_afford'] > worst['uncov_over_afford']:
                    worst = r
            if (idx + 1) % 20 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}")
        worst_per_n[n] = worst
        print(f"  n={n} done: {count} L≥2n+2 records")

    if not all_records:
        print("No records collected.")
        return

    print(f"\n{'='*72}")
    print(f"R1 results: does uncovered ≤ afford hold? (i.e. covered alone ≥ 2^(n-1))")
    print(f"{'='*72}")
    by_n = defaultdict(list)
    for r in all_records:
        by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        yes = sum(1 for r in recs if r['uncov_over_afford'] <= 0)
        no  = sum(1 for r in recs if r['uncov_over_afford'] > 0)
        max_excess = max(r['uncov_over_afford'] for r in recs)
        avg_uncov = sum(r['uncovered'] for r in recs) / len(recs)
        avg_afford = sum(r['afford'] for r in recs) / len(recs)
        avg_naive_over = sum(r['naive_overcount'] for r in recs) / len(recs)
        avg_pair_ov = sum(r['pair_overlap'] for r in recs) / len(recs)
        print(f"\n  n={n}  records={len(recs)}")
        print(f"    uncovered ≤ afford (covered suffices): {yes} / {len(recs)}")
        print(f"    uncovered > afford (cascade needed):   {no} / {len(recs)}")
        print(f"    max excess (uncov - afford):           {max_excess}")
        print(f"    avg uncovered:                         {avg_uncov:.1f}")
        print(f"    avg afford = |VC-NG| - 2^(n-1):        {avg_afford:.1f}")
        print(f"    avg naive overcount (naive - covered): {avg_naive_over:.1f}")
        print(f"    avg adjacent pair overlap Σ|cov(p)∩cov(p+1)|: {avg_pair_ov:.1f}")
        if worst_per_n[n] is not None:
            w = worst_per_n[n]
            print(f"    worst case: ms={w['ms']} L={w['L']}")
            print(f"      vc_ng={w['vc_ng']}  uncov={w['uncovered']}  afford={w['afford']}  excess={w['uncov_over_afford']}")

    # Concluding judgement
    print(f"\n{'='*72}")
    print("Interpretation")
    print(f"{'='*72}")
    any_excess = any(r['uncov_over_afford'] > 0 for r in all_records)
    if any_excess:
        print("COVERAGE-ALONE BOUND FAILS: ∃ records where uncovered > afford.")
        print("Meaning: round-0 sinks already exceed |VC-NG| - 2^(n-1).")
        print("Immune ≥ 2^(n-1) CANNOT be derived from coverage fraction alone.")
        print("Cascade analysis is essential — R1 as stated is insufficient.")
    else:
        print("COVERAGE-ALONE BOUND HOLDS: uncovered ≤ afford everywhere.")
        print("If we additionally prove covered configs survive peeling (no cascade),")
        print("we close Lemma C via coverage alone. Check cascade slack separately.")


if __name__ == "__main__":
    main()
