#!/usr/bin/env python3
"""Structural characterization of peel(N_1(C) ∩ VC-NG).

At n=7 |peel(N_1)| is exactly 64 = 2^(n-1) in all records.
Is peel(N_1) characterized by a simple local rule?

For each c ∈ peel(N_1):
  c = c_i[q ← v] for some (q, v, i) with v ∈ V_q \ {c_i[q]}.

  Analyze:
    C1: What (q, v) pairs occur? (maybe only certain q)
    C2: What i values? (all L? some subset?)
    C3: Is (q, v, i) → c a bijection? Or is there collision?
    C4: Is the peel = {(q, v, i) : v ≠ c_i[q] AND some rule R(q, v, i)}?

For sinks (c ∈ N_1 \ peel):
  What's the local obstruction? (no forced move; or forced move exits N_1)
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


def analyze(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    VC = set(iproduct(*[sorted(V[i]) for i in range(n)]))
    VC_NG = VC - cycle_set
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # N_1(C) ∩ VC_NG
    N1 = set()
    qv_of = defaultdict(list)  # c -> list of (q, v, i) with c = c_i[q←v]
    for i, c in enumerate(cycle):
        for q in range(n):
            for v in V[q]:
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)
                    qv_of[nc].append((q, v, i))

    # Adjacency in N_1
    adj = defaultdict(list)
    for c in N1:
        for p in range(n):
            ctx = (p, c[(p - 1) % n], c[p], c[(p + 1) % n])
            if ctx in move_entries:
                val = move_entries[ctx]
                nc = list(c); nc[p] = val; nc = tuple(nc)
                if nc in N1:
                    adj[c].append(nc)

    # Peel
    cur = set(N1)
    while True:
        to_remove = {c for c in cur if not any(s in cur for s in adj[c])}
        if not to_remove: break
        cur -= to_remove
    peel_set = cur

    # Structural analysis of peel
    q_counts = Counter()
    for c in peel_set:
        for (q, v, i) in qv_of[c]:
            q_counts[q] += 1
    # Which (q, v) pairs cover peel?
    qv_counts = Counter()
    for c in peel_set:
        for (q, v, i) in qv_of[c]:
            qv_counts[(q, v)] += 1
    # Which i (cycle indices) participate?
    i_counts = Counter()
    for c in peel_set:
        for (q, v, i) in qv_of[c]:
            i_counts[i] += 1

    # Characterize: for peel configs, the firing position p of their NG-successor
    # is that p always ∉ {q-1, q, q+1}?
    fires_at_q_neighborhood = 0
    fires_away = 0
    for c in peel_set:
        if not adj[c]: continue  # shouldn't happen in peel
        # Pick any successor
        s = adj[c][0]
        p_fire = [i for i in range(n) if c[i] != s[i]][0]
        # (q, v, i) options for c
        if not qv_of[c]: continue
        q, v, i = qv_of[c][0]  # pick any
        if p_fire in {(q-1)%n, q, (q+1)%n}:
            fires_at_q_neighborhood += 1
        else:
            fires_away += 1

    # Is peel = {c_i[q←v] : ∀ i, (q, v) is 'persistent'} ?
    # Persistent = (q, v) such that for every cycle step i, c_i[q←v] is in peel?
    persistent_qv = set()
    for q in range(n):
        for v in V[q]:
            all_in_peel = True
            for i, c in enumerate(cycle):
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc in cycle_set: continue
                if nc not in peel_set:
                    all_in_peel = False; break
            if all_in_peel:
                persistent_qv.add((q, v))

    # Expected |peel| from persistent (q,v):
    expected = 0
    for (q, v) in persistent_qv:
        for i, c in enumerate(cycle):
            if v == c[q]: continue
            nc = list(c); nc[q] = v; nc = tuple(nc)
            if nc not in cycle_set:
                expected += 1  # over-counts if same c arises from multiple (q,v,i)
    # De-duplicate
    peel_from_pers = set()
    for (q, v) in persistent_qv:
        for i, c in enumerate(cycle):
            if v == c[q]: continue
            nc = list(c); nc[q] = v; nc = tuple(nc)
            if nc not in cycle_set:
                peel_from_pers.add(nc)

    return {
        'n': n, 'ms': ms, 'L': L,
        'N1_size': len(N1),
        'peel_size': len(peel_set),
        'q_distrib': dict(q_counts),
        'num_qv_contributing': len(qv_counts),
        'num_persistent_qv': len(persistent_qv),
        'peel_from_pers_size': len(peel_from_pers),
        'peel_eq_pers_set': peel_set == peel_from_pers,
        'peel_cov_by_pers': peel_set <= peel_from_pers,  # peel ⊆ pers
        'fires_away_frac': fires_away / max(fires_at_q_neighborhood + fires_away, 1),
    }


def main():
    print("=" * 72, flush=True)
    print("peel(N_1(C)) structural characterization", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 40, 3.0, 16),
        (6, 8, 15, 3.0, 17),
        (7, 40, 8, 3.0, 17),
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
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 10) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        print(f"\n  n={n}  records={len(recs)}")
        peels = [r['peel_size'] for r in recs]
        from_pers = [r['peel_from_pers_size'] for r in recs]
        npers = [r['num_persistent_qv'] for r in recs]
        eq_pers = sum(1 for r in recs if r['peel_eq_pers_set'])
        cov_pers = sum(1 for r in recs if r['peel_cov_by_pers'])
        print(f"    |peel|: min={min(peels)} max={max(peels)} avg={sum(peels)/len(peels):.1f}")
        print(f"    |peel_from_pers|: min={min(from_pers)} max={max(from_pers)} avg={sum(from_pers)/len(from_pers):.1f}")
        print(f"    #persistent (q, v): min={min(npers)} max={max(npers)} avg={sum(npers)/len(npers):.1f}")
        print(f"    peel == peel_from_pers: {eq_pers}/{len(recs)} ({100*eq_pers/len(recs):.1f}%)")
        print(f"    peel ⊆ peel_from_pers: {cov_pers}/{len(recs)} ({100*cov_pers/len(recs):.1f}%)")
        # NG move fires away from q-neighborhood?
        away = [r['fires_away_frac'] for r in recs]
        print(f"    frac of peel configs whose NG-succ fires away from {{q-1,q,q+1}}: avg={sum(away)/len(away):.3f}")
        # q distribution aggregated
        q_tot = Counter()
        for r in recs:
            for q, c in r['q_distrib'].items():
                q_tot[q] += c
        print(f"    aggregated q-distribution of peel configs: {dict(sorted(q_tot.items()))}")


if __name__ == "__main__":
    main()
