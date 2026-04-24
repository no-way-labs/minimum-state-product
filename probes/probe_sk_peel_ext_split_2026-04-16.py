#!/usr/bin/env python3
"""Distinguish records where peel = N_1^ext_all vs. not.

Finding at n=7: 74/96 records have peel = N_1^ext_all (extreme-anchor subset of N_1).
22/96 records have peel ⊊ N_1^ext_all (ext_all not closed).
What distinguishes them?

Conjectures:
  C1. # positions with |V_q| ≥ 3 (mid-values in cycle)
  C2. # firings where q fires with mid-input (c_i[q] ∈ mid(V_q))
  C3. Cycle length L modulo n or other arithmetic invariant
  C4. ms specifics
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


def classify(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # Build N_1
    N1_anchors = defaultdict(list)
    N1 = set()
    for c in cycle:
        for q in range(n):
            for v in range(ms[q]):
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)
                    N1_anchors[nc].append((q, v))

    # N_1^ext_all
    N1_ext_all = set()
    for nc, anchors in N1_anchors.items():
        if all(v in {min(V[q]), max(V[q])} for (q, v) in anchors):
            N1_ext_all.add(nc)

    # Adj
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
    peel = cur
    if not peel: return None

    peel_eq_ext_all = peel == N1_ext_all

    # Feature extraction
    n_nonbinary = sum(1 for q in range(n) if len(V[q]) >= 3)
    # Positions where |V_q| = m_q (q uses all its values)
    n_full_coverage = sum(1 for q in range(n) if len(V[q]) == ms[q])
    # # firings with mid-input
    n_mid_fires = 0
    for i in range(L):
        q = movers[i]
        Vq = V[q]
        if len(Vq) >= 3:
            if cycle[i][q] not in {min(Vq), max(Vq)}:
                n_mid_fires += 1
    # # firings with mid-output
    n_mid_outputs = 0
    for i in range(L):
        q = movers[i]
        Vq = V[q]
        if len(Vq) >= 3:
            if cycle[(i + 1) % L][q] not in {min(Vq), max(Vq)}:
                n_mid_outputs += 1

    # # cycle positions where some proc has mid-value
    n_mid_config = 0
    for c in cycle:
        if any(c[q] not in {min(V[q]), max(V[q])} for q in range(n)):
            n_mid_config += 1

    return {
        'n': n, 'ms': ms, 'L': L, 'peel_size': len(peel),
        'peel_eq_ext_all': peel_eq_ext_all,
        'n_nonbinary': n_nonbinary,
        'n_full_coverage': n_full_coverage,
        'n_mid_fires': n_mid_fires,
        'n_mid_outputs': n_mid_outputs,
        'n_mid_config': n_mid_config,
        'ms_tuple': ms,
        'N1_ext_all_size': len(N1_ext_all),
    }


def main():
    print("=" * 72, flush=True)
    print("What distinguishes peel=ext_all cases? (n=7)", flush=True)
    print("=" * 72, flush=True)
    records = []
    tb = 4.0; max_cycles = 8; L_max = 17
    n = 7
    Mn = m_n_sharp(n)
    multisets = enumerate_multisets(n, Mn)
    sampled = multisets[::40]
    print(f"n=7  {len(sampled)} multisets", flush=True)
    t0 = time.time()
    for idx, ms in enumerate(sampled):
        cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
        for cycle, movers, det in cycles:
            L = len(movers)
            if L < 2 * n + 2: continue
            r = classify(ms, n, cycle, movers, det)
            if r is None: continue
            records.append(r)
        if (idx + 1) % max(1, len(sampled) // 6) == 0 or idx == len(sampled) - 1:
            print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={len(records)}", flush=True)

    print(f"\n{'='*72}\nSplit analysis\n{'='*72}")
    good = [r for r in records if r['peel_eq_ext_all']]
    bad = [r for r in records if not r['peel_eq_ext_all']]
    print(f"peel = ext_all: {len(good)}; peel ⊊ ext_all (excess peeling): {len(bad)}")
    for label, grp in [('GOOD', good), ('BAD', bad)]:
        print(f"\n  [{label}]  n={len(grp)}")
        for key in ['n_nonbinary', 'n_full_coverage', 'n_mid_fires', 'n_mid_outputs', 'n_mid_config', 'N1_ext_all_size']:
            vals = [r[key] for r in grp]
            if vals:
                print(f"    {key}: min={min(vals)} max={max(vals)} avg={sum(vals)/len(vals):.2f}")
        # ms patterns
        ms_pat = Counter(r['ms_tuple'] for r in grp)
        print(f"    Top 5 ms patterns:")
        for ms_t, c in ms_pat.most_common(5):
            print(f"      {ms_t}: {c}")


if __name__ == "__main__":
    main()
