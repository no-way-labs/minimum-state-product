#!/usr/bin/env python3
"""Immune core structural invariant probe.

SK (immune core after peeling) is ALWAYS nonempty at sub-M_n. We
know |SK| ≥ 2^(n-1) empirically. What STRUCTURAL property do immune
configs share?

Tests:

  (I1) Value-parity: for each c ∈ SK, compute parity(sum c[i]).
      Does SK consist of ALL configs of one parity? Of neither?
      Ring orientation matters; test sum mod gcd(m_i).

  (I2) Shift invariance: is SK closed under the ring shift σ(c)[i] = c[i-1]?
      If yes, |SK| is a multiple of n.

  (I3) Reflection invariance: is SK closed under reversal?

  (I4) Hamming distance to C: distribution of min Hamming distance
      from each SK config to the closest cycle config.

  (I5) "Opposite" fiber: for each c ∈ SK and position p, does there
      exist c' ∈ SK with c'[p] ≠ c[p] but c'[i] = c[i] for i ≠ p?
      (Tests if SK is closed under value flips at each position.)

  (I6) Binary subset test: how many SK configs use ONLY the 2 "primary"
      values at each non-binary position? How many use extra values?
      (Handoff: "strictly-binary immune drops to 6 at n=5, extra-value
       pushes to 26.")

  (I7) SK via product structure: is SK = ∏_i S_i for some S_i ⊆ V_i?
      If yes, the proof reduces to "each S_i is nonempty" per-position.

  (I8) Intersection with binary cube: |SK ∩ binary_cube| vs 2^(n-1).
      Handoff says binary cube projection fails, but intersection might
      still have structure.
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


def compute_sk(vc_ng, out_edges):
    rem = set(vc_ng)
    while True:
        sinks = set()
        for c in rem:
            if not any(t in rem for t in out_edges[c]):
                sinks.add(c)
        if not sinks: break
        rem -= sinks
    return rem


def hamming(c1, c2):
    return sum(1 for a,b in zip(c1, c2) if a != b)


def analyze_immune(ms, n, cycle, movers, det):
    L = len(movers)
    cycle_set = set(cycle)
    V = value_sets(cycle, n)
    move_entries = {(p, Lv, Sv, Rv): val for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    vc_ranges = [sorted(V[i]) for i in range(n)]
    vc_all = set(iproduct(*vc_ranges))
    vc_ng = vc_all - cycle_set

    out_edges = defaultdict(set)
    for c in vc_ng:
        for p in range(n):
            key = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if key in move_entries:
                nc = list(c); nc[p] = move_entries[key]; nc = tuple(nc)
                if nc in vc_ng:
                    out_edges[c].add(nc)

    sk = compute_sk(vc_ng, out_edges)

    # I1 value parity (mod 2)
    par2 = Counter(sum(c) % 2 for c in sk)
    # I2 shift invariance: SK is shift-closed if σ(SK) ⊆ SK
    shift_sk = set(tuple(c[(i - 1) % n] for i in range(n)) for c in sk)
    shift_invariant = (shift_sk == sk)
    # I3 reflection: c reversed
    refl_sk = set(c[::-1] for c in sk)
    refl_invariant = (refl_sk == sk)
    # I4 Hamming distance
    hd = [min(hamming(c, g) for g in cycle) for c in sk] if sk else []
    hd_counter = Counter(hd) if hd else Counter()
    # I5 value-flip partner: for each c and each p, is there c' ∈ SK with c[i]=c'[i] ∀ i≠p?
    # Count fraction of (c, p) pairs that have such a partner
    partner_hits = 0
    partner_total = 0
    for c in sk:
        for p in range(n):
            partner_total += 1
            for v in V[p]:
                if v == c[p]: continue
                cprime = list(c); cprime[p] = v; cprime = tuple(cprime)
                if cprime in sk:
                    partner_hits += 1
                    break
    # I6 primary value use — primary = 2 most common values at position
    primary = []
    for i in range(n):
        # Count occurrences in cycle
        count_i = Counter(c[i] for c in cycle)
        top2 = set(v for v, _ in count_i.most_common(2))
        primary.append(top2)
    sb_count = sum(1 for c in sk if all(c[i] in primary[i] for i in range(n)))
    # I7 product test
    per_pos = [set(c[i] for c in sk) for i in range(n)] if sk else [set() for _ in range(n)]
    product_sk = set(iproduct(*[sorted(s) for s in per_pos]))
    is_product = (sk == product_sk)
    # I8 binary-cube intersection: configs using values {0,1} per position (if those exist)
    bcube = set()
    for c in sk:
        if all(v in (0, 1) for v in c):
            bcube.add(c)
    # I9 relation to cycle: is SK ⊂ "anti-cycle"? Measure density in VC
    density = len(sk) / len(vc_ng) if vc_ng else 0

    return {
        'n': n, 'ms': ms, 'L': L, 'vc_ng': len(vc_ng), 'sk_size': len(sk),
        'par2_0': par2.get(0, 0), 'par2_1': par2.get(1, 0),
        'shift_invariant': shift_invariant,
        'refl_invariant': refl_invariant,
        'hd_counter': dict(hd_counter),
        'hd_min': min(hd) if hd else None,
        'hd_max': max(hd) if hd else None,
        'partner_frac': partner_hits / partner_total if partner_total else 0,
        'sb_count': sb_count,
        'is_product': is_product,
        'per_pos_sizes': tuple(len(s) for s in per_pos),
        'bcube_count': len(bcube),
        'density': density,
    }


def main():
    print("=" * 72)
    print("SK structural invariant probe")
    print("=" * 72)

    plan = [
        (5, 1, 400, 4.0, 14),
        (6, 5, 150, 3.0, 14),
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
                r = analyze_immune(ms, n, cycle, movers, det)
                all_records.append(r)
                count += 1
            if (idx + 1) % 10 == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults per n\n{'='*72}")
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)

    for n, recs in sorted(by_n.items()):
        print(f"\n  n={n}  records={len(recs)}")
        # I1
        par0 = sum(1 for r in recs if r['par2_0'] > 0 and r['par2_1'] == 0)
        par1 = sum(1 for r in recs if r['par2_1'] > 0 and r['par2_0'] == 0)
        parboth = sum(1 for r in recs if r['par2_0'] > 0 and r['par2_1'] > 0)
        print(f"    I1 parity: only-even={par0}  only-odd={par1}  both={parboth}")
        # I2/I3
        shift_yes = sum(1 for r in recs if r['shift_invariant'])
        refl_yes = sum(1 for r in recs if r['refl_invariant'])
        print(f"    I2 shift-invariant SK:  {shift_yes}/{len(recs)}")
        print(f"    I3 refl-invariant SK:   {refl_yes}/{len(recs)}")
        # I5
        avg_partner = sum(r['partner_frac'] for r in recs) / len(recs)
        print(f"    I5 avg partner frac (c has partner at some p): {avg_partner:.3f}")
        # I7
        prod_yes = sum(1 for r in recs if r['is_product'])
        print(f"    I7 SK is product set:   {prod_yes}/{len(recs)}")
        # I6 binary
        sb_eq_sk = sum(1 for r in recs if r['sb_count'] == r['sk_size'])
        sb_lt_sk = sum(1 for r in recs if r['sb_count'] < r['sk_size'])
        print(f"    I6 SK = strictly-binary:  {sb_eq_sk}/{len(recs)} (sb==sk)")
        print(f"    I6 SK has extra values:   {sb_lt_sk}/{len(recs)} (sb<sk)")
        # I8
        avg_bcube = sum(r['bcube_count'] for r in recs) / len(recs)
        print(f"    I8 avg |SK ∩ binary_cube|: {avg_bcube:.1f}")
        # Density
        avg_den = sum(r['density'] for r in recs) / len(recs)
        print(f"    density |SK|/|VC-NG|: {avg_den:.3f}")
        # Hamming
        hd_min_counter = Counter(r['hd_min'] for r in recs if r['hd_min'] is not None)
        print(f"    Hamming-to-cycle: min distribution (over SK) {dict(hd_min_counter)}")


if __name__ == "__main__":
    main()
