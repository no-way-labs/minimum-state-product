#!/usr/bin/env python3
"""Is peel(N_1) exactly N_1 restricted to v ∈ {min(V_q), max(V_q)}?

Test: Let N_1^ext = {c_i[q ← v] ∈ N_1 : v ∈ {min(V_q), max(V_q)}}.
  - Is N_1^ext closed under forced NG-edges (i.e., does each element have a successor in N_1^ext)?
  - Is peel = N_1^ext?
  - Is peel ⊆ N_1^ext?
  - Is peel ⊇ N_1^ext?

Also: |N_1^ext|. At n=7 we have 64 peel configs. What is |N_1^ext|?
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
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}

    # N_1 (Hamming-1 from cycle, excluding cycle itself) ∩ VC-NG = N_1
    N1 = set()
    N1_anchors = defaultdict(list)
    for c in cycle:
        for q in range(n):
            for v in range(ms[q]):
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)
                    N1_anchors[nc].append((q, v))

    # N_1^ext: nc has AT LEAST one anchor (q,v) with v ∈ {min(V_q), max(V_q)}
    # (Since multiple anchors possible.)
    N1_ext_any = set()
    for nc, anchors in N1_anchors.items():
        if any(v in {min(V[q]), max(V[q])} for (q, v) in anchors):
            N1_ext_any.add(nc)
    # Strict version: ALL anchors must be extreme
    N1_ext_all = set()
    for nc, anchors in N1_anchors.items():
        if all(v in {min(V[q]), max(V[q])} for (q, v) in anchors):
            N1_ext_all.add(nc)

    # Build adj over N_1
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
    peel = cur
    if not peel: return None

    # Tests
    # T1: peel ⊆ N1_ext_any (at least one anchor extreme)?
    peel_sub_ext_any = peel <= N1_ext_any
    # T2: peel ⊆ N1_ext_all (all anchors extreme)?
    peel_sub_ext_all = peel <= N1_ext_all
    # T3: peel = N1_ext_any?
    peel_eq_ext_any = peel == N1_ext_any
    peel_eq_ext_all = peel == N1_ext_all

    # Also test closure of N1_ext under forced edges: is every c ∈ N1_ext's NG-successor in N1_ext?
    # Closed-under-successor from perspective of peel logic
    any_ext_closed = True  # every c ∈ N1_ext_any has at least one successor in N1_ext_any
    for c in N1_ext_any:
        succs_in = [s for s in adj[c] if s in N1_ext_any]
        if not succs_in:
            any_ext_closed = False; break
    all_ext_closed = True
    for c in N1_ext_all:
        succs_in = [s for s in adj[c] if s in N1_ext_all]
        if not succs_in:
            all_ext_closed = False; break

    return {
        'n': n, 'ms': ms, 'L': L, 'peel_size': len(peel),
        'N1_size': len(N1),
        'N1_ext_any_size': len(N1_ext_any),
        'N1_ext_all_size': len(N1_ext_all),
        'peel_sub_ext_any': peel_sub_ext_any,
        'peel_sub_ext_all': peel_sub_ext_all,
        'peel_eq_ext_any': peel_eq_ext_any,
        'peel_eq_ext_all': peel_eq_ext_all,
        'any_ext_closed': any_ext_closed,
        'all_ext_closed': all_ext_closed,
    }


def main():
    print("=" * 72, flush=True)
    print("peel vs. N_1 restricted to extreme anchor v", flush=True)
    print("=" * 72, flush=True)
    plan = [
        (5, 3, 40, 3.0, 16),
        (6, 8, 15, 3.0, 17),
        (7, 40, 8, 4.0, 17),
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
                if r is None: continue
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 6) == 0 or idx == len(sampled) - 1:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        print(f"\n  n={n}  records={len(recs)}")
        for key in ['peel_size', 'N1_size', 'N1_ext_any_size', 'N1_ext_all_size']:
            vals = [r[key] for r in recs]
            print(f"    {key}: min={min(vals)} max={max(vals)} avg={sum(vals)/len(vals):.1f}")
        for flag in ['peel_sub_ext_any', 'peel_sub_ext_all', 'peel_eq_ext_any', 'peel_eq_ext_all',
                     'any_ext_closed', 'all_ext_closed']:
            cnt = sum(1 for r in recs if r[flag])
            print(f"    {flag}: {cnt}/{len(recs)} ({100*cnt/len(recs):.1f}%)")


if __name__ == "__main__":
    main()
