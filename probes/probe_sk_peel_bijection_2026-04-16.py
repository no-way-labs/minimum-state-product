#!/usr/bin/env python3
"""Find the canonical bijection peel(N_1) ↔ 2^(n-1) at n=7.

|peel(N_1)| = 64 = 2^6 exactly in all 96 records. Look for structure:
  H1: peel is Z/L-invariant? (L rotations of good cycle give same peel)
  H2: peel / L is small and structured? 64 / 16 = 4.
  H3: peel configs have a 'sign vector' binary invariant?
  H4: peel = {c_i[q←v] : (q,v) fixed AND v = c_{σ(i)}[q] for some σ}?
  H5: peel = Orb of a single config under good-cycle rotation + a parity flip?
  H6: peel is exactly {c : c ⊕ c_bin ∈ some affine subspace} where c_bin is projection?

Dump each peel and compare across records.
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


def compute_peel(ms, n, cycle, movers, det):
    L = len(movers)
    V = value_sets(cycle, n)
    cycle_set = set(cycle)
    move_entries = {(p, Lv, Sv, Rv): val
                    for (p, Lv, Sv, Rv), val in det.items() if val != Sv}
    N1 = set()
    anchors = defaultdict(list)  # c -> list of (i, q, v)
    for i, c in enumerate(cycle):
        for q in range(n):
            for v in V[q]:
                if v == c[q]: continue
                nc = list(c); nc[q] = v; nc = tuple(nc)
                if nc not in cycle_set:
                    N1.add(nc)
                    anchors[nc].append((i, q, v))
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
    return cur, anchors, L


def analyze_peel(ms, n, cycle, movers, det):
    peel, anchors, L = compute_peel(ms, n, cycle, movers, det)
    if not peel: return None

    # H1: Is peel invariant under good-cycle rotation?
    # Rotation: c_i → c_{i+1}. In config space, there's no obvious group action,
    # but we can check: for c_s ∈ peel with anchor (i, q, v), is c_{i+1}[q←v] ∈ peel?
    h1_rotation_closed = True
    for c_s in peel:
        for (i, q, v) in anchors[c_s]:
            # Next i
            i2 = (i + 1) % L
            if v == cycle[i2][q]: continue  # c_{i+1}[q←v] would equal c_{i+1}
            nc = list(cycle[i2]); nc[q] = v; nc = tuple(nc)
            if nc in set(cycle): continue
            if nc not in peel:
                h1_rotation_closed = False
                break
        if not h1_rotation_closed: break

    # H2: peel / L orbit count
    # Orbit = {c_{i+k}[q←v] : k ∈ Z/L} — closed under i-shift if (q, v) admissible
    orbit_count = defaultdict(set)
    for c_s in peel:
        for (i, q, v) in anchors[c_s]:
            orbit_count[(q, v)].add((i, c_s))

    # H3: Binary invariant?
    # Find all (q, v) such that some subset of {c_i[q←v] : i} is in peel.
    # Count per (q, v): how many i's have c_i[q←v] ∈ peel?
    qv_counts = Counter()
    for c_s in peel:
        for (i, q, v) in anchors[c_s]:
            qv_counts[(q, v)] += 1

    # H4: Does peel = {c_i[q←v] : (q, v, i) satisfying P(q, v, i)}?
    # P could be: v ≠ c_i[q] AND c_{i-1}[q] = c_i[q] (i.e., position q is NOT moving at step i-1)
    # Check various Ps
    tests = {}

    # Test A: v = c_{i-1}[q] but v ≠ c_i[q] (previous value at q)
    peelA = set()
    for i, c in enumerate(cycle):
        for q in range(n):
            v = cycle[(i - 1) % L][q]
            if v == c[q]: continue
            nc = list(c); nc[q] = v; nc = tuple(nc)
            if nc in peel: peelA.add(nc)
    tests['A: c_{i-1}[q] ≠ c_i[q]'] = (peelA, peelA == peel, peelA <= peel)

    # Test B: v = c_{i+1}[q] but v ≠ c_i[q] (next value at q)
    peelB = set()
    for i, c in enumerate(cycle):
        for q in range(n):
            v = cycle[(i + 1) % L][q]
            if v == c[q]: continue
            nc = list(c); nc[q] = v; nc = tuple(nc)
            if nc in peel: peelB.add(nc)
    tests['B: c_{i+1}[q] ≠ c_i[q]'] = (peelB, peelB == peel, peelB <= peel)

    # Test C: p_i = q (position q fires at step i) and v = c_{i-1}[q]
    peelC = set()
    for i, c in enumerate(cycle):
        p_i = movers[i]  # position that fires at step i, i.e., c_i → c_{i+1}
        q = p_i
        # Value before firing: c_i[q] (current), value after: c_{i+1}[q]
        # v = c_{(i-1)}[q] is the "previous" value at q
        v = cycle[(i - 1) % L][q]
        if v == c[q]: continue
        nc = list(c); nc[q] = v; nc = tuple(nc)
        if nc not in set(cycle) and nc in peel:
            peelC.add(nc)
    tests['C: p_i=q, v=c_{i-1}[q]'] = (peelC, peelC == peel, peelC <= peel)

    # Test D: All (i, q, v) with v appearing in V_q AND v ≠ c_i[q] AND i mod 2 = 0 or similar
    # The 2^(n-1) structure: maybe parity of Σ c[j] mod 2?

    # H5: rotation orbit of a specific config
    # Pick any c_0 ∈ peel, look at Orb_rot(c_0) = {c_s : c_s shares (q, v) with c_0's anchors but varies i}
    if peel:
        c0 = next(iter(peel))
        anc0 = anchors[c0][0]
        i0, q0, v0 = anc0
        orb = set()
        for i in range(L):
            if v0 == cycle[i][q0]: continue
            nc = list(cycle[i]); nc[q0] = v0; nc = tuple(nc)
            if nc in set(cycle): continue
            orb.add(nc)
        orb_in_peel = orb & peel
    else:
        orb_in_peel = set()

    return {
        'ms': ms, 'L': L, 'peel_size': len(peel),
        'h1_rotation_closed': h1_rotation_closed,
        'num_distinct_qv': len([k for k, v in qv_counts.items() if v > 0]),
        'max_qv_count': max(qv_counts.values()) if qv_counts else 0,
        'qv_counts': dict(Counter(qv_counts.values())),
        'testA_eq': tests['A: c_{i-1}[q] ≠ c_i[q]'][1],
        'testA_sub': tests['A: c_{i-1}[q] ≠ c_i[q]'][2],
        'testA_size': len(tests['A: c_{i-1}[q] ≠ c_i[q]'][0]),
        'testB_eq': tests['B: c_{i+1}[q] ≠ c_i[q]'][1],
        'testB_sub': tests['B: c_{i+1}[q] ≠ c_i[q]'][2],
        'testB_size': len(tests['B: c_{i+1}[q] ≠ c_i[q]'][0]),
    }


def main():
    print("=" * 72, flush=True)
    print("peel(N_1) canonical bijection probe (focus n=7)", flush=True)
    print("=" * 72, flush=True)
    all_records = []
    for n in [5, 6, 7]:
        Mn = m_n_sharp(n)
        multisets = enumerate_multisets(n, Mn)
        stride = {5: 3, 6: 8, 7: 10}[n]
        max_cycles = {5: 20, 6: 8, 7: 4}[n]
        tb = 3.0
        L_max = 17 if n >= 6 else 16
        sampled = multisets[::stride]
        print(f"\n=== n={n}  {len(sampled)} multisets ===", flush=True)
        t0 = time.time()
        count = 0
        for idx, ms in enumerate(sampled):
            cycles = enumerate_all_cycles(ms, n, L_max, tb, max_cycles)
            for cycle, movers, det in cycles:
                L = len(movers)
                if L < 2 * n + 2: continue
                r = analyze_peel(ms, n, cycle, movers, det)
                if r is None: continue
                r['n'] = n
                all_records.append(r)
                count += 1
            if (idx + 1) % max(1, len(sampled) // 5) == 0:
                print(f"  [{idx+1}/{len(sampled)}]  {time.time()-t0:.0f}s  records={count}", flush=True)

    print(f"\n{'='*72}\nResults\n{'='*72}", flush=True)
    by_n = defaultdict(list)
    for r in all_records: by_n[r['n']].append(r)
    for n, recs in sorted(by_n.items()):
        if not recs: continue
        print(f"\n  n={n}  records={len(recs)}")
        rc = sum(1 for r in recs if r['h1_rotation_closed'])
        print(f"    H1 rotation-closed: {rc}/{len(recs)}")
        nqv = [r['num_distinct_qv'] for r in recs]
        print(f"    # distinct (q, v) with some peel-anchor: min={min(nqv)} max={max(nqv)} avg={sum(nqv)/len(nqv):.1f}")
        mqv = [r['max_qv_count'] for r in recs]
        print(f"    max #i per (q,v): min={min(mqv)} max={max(mqv)} avg={sum(mqv)/len(mqv):.1f}")
        ta = sum(1 for r in recs if r['testA_eq'])
        tas = sum(1 for r in recs if r['testA_sub'])
        print(f"    Test A: peel = {{c_i[q←c_{{i-1}}[q]]}}: eq={ta}/{len(recs)} sub={tas}/{len(recs)}")
        ta_sz = [r['testA_size'] for r in recs]
        print(f"           Test A size in peel: min={min(ta_sz)} max={max(ta_sz)} avg={sum(ta_sz)/len(ta_sz):.1f}")
        tb = sum(1 for r in recs if r['testB_eq'])
        tbs = sum(1 for r in recs if r['testB_sub'])
        print(f"    Test B: peel = {{c_i[q←c_{{i+1}}[q]]}}: eq={tb}/{len(recs)} sub={tbs}/{len(recs)}")
        tb_sz = [r['testB_size'] for r in recs]
        print(f"           Test B size in peel: min={min(tb_sz)} max={max(tb_sz)} avg={sum(tb_sz)/len(tb_sz):.1f}")


if __name__ == "__main__":
    main()
