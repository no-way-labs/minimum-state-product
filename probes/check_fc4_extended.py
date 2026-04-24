#!/usr/bin/env python3
"""
Extended verification of the one-sided excursion + pigeonhole structure.
Check n=5,7,9 (and n=11 if fast enough).

Key claims to verify:
1. ALL excursions are same-side (LL or RR) — never LR or RL
2. Gate neighbor always has exactly 2 free (L,S) slots per R-bucket at fc=2
3. At fc=4, the gate neighbor would be forced into conflict

Also: does the one-sided property hold for NON-max-fc procs? (fc=0 procs
don't have excursions, but we should check all fc=2 procs.)
"""
from itertools import product as iproduct
from collections import Counter
import time

def analyze_n(n, max_path_len=None):
    if max_path_len is None:
        max_path_len = 2 * n + 4

    ms = [2] * n
    total = 2 ** n
    all_configs = list(iproduct(range(2), repeat=n))
    config_idx = {c: i for i, c in enumerate(all_configs)}

    def signed_step(a, b):
        d = (b - a) % n
        if d == 1: return 1
        elif d == n - 1: return -1
        return 0

    t0 = time.time()
    print(f"\n{'='*60}")
    print(f"n={n}, all binary, {total} configs, max_path_len={max_path_len}")

    all_cycles = []
    for start in range(total):
        stack = [(start, [start], [0]*n, 0, {}, [])]
        while stack:
            ci, path, fc, wind, cons, movs = stack.pop()
            if len(path) > max_path_len: continue
            c = all_configs[ci]
            for mover in range(n):
                L = c[(mover-1) % n]; S = c[mover]; R = c[(mover+1) % n]
                key = (mover, L, S, R)
                if key in cons and cons[key] == 'nonmover': continue
                valid = True
                new_cons = dict(cons)
                new_cons[key] = 'mover'
                for p in range(n):
                    if p == mover: continue
                    kp = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                    if kp in new_cons and new_cons[kp] == 'mover':
                        valid = False; break
                    new_cons[kp] = 'nonmover'
                if not valid: continue
                new_c = list(c); new_c[mover] = 1-S
                new_ci = config_idx[tuple(new_c)]
                new_fc = list(fc); new_fc[mover] += 1
                new_wind = wind
                if movs: new_wind += signed_step(movs[-1], mover)
                if new_ci == start and len(path) >= 3:
                    fw = new_wind + signed_step(mover, movs[0])
                    if fw == 0:
                        all_cycles.append({
                            'path': list(path), 'movers': movs + [mover],
                            'fc': list(new_fc)
                        })
                    continue
                if new_ci in path: continue
                stack.append((new_ci, path+[new_ci], new_fc, new_wind, new_cons, movs+[mover]))

    elapsed = time.time() - t0
    print(f"Found {len(all_cycles)} zero-winding cycles in {elapsed:.1f}s")

    if not all_cycles:
        return

    max_fc = max(max(c['fc']) for c in all_cycles)
    fc_dist = Counter(max(c['fc']) for c in all_cycles)
    print(f"Max fc across all cycles: {max_fc}")
    print(f"Max-fc distribution: {dict(sorted(fc_dist.items()))}")

    # Cycle length distribution
    len_dist = Counter(len(c['path']) for c in all_cycles)
    print(f"Cycle length distribution: {dict(sorted(len_dist.items()))}")

    # === CLAIM 1: All excursions same-side ===
    exc_pair_counts = Counter()
    exc_types_all = Counter()
    total_exc_pairs = 0
    mixed = 0

    for cyc in all_cycles:
        path = cyc['path']
        movers = cyc['movers']
        CL = len(path)

        for p in range(n):
            if cyc['fc'][p] != 2: continue
            fire_steps = [t for t in range(CL) if movers[t] == p]
            if len(fire_steps) != 2: continue
            t1, t2 = fire_steps

            types = []
            for (ta, tb) in [(t1, t2), (t2, t1 + CL)]:
                leave = movers[(ta + 1) % CL]
                ret = movers[(tb - 1) % CL]
                ls = 'L' if leave == (p-1)%n else ('R' if leave == (p+1)%n else '?')
                rs = 'L' if ret == (p-1)%n else ('R' if ret == (p+1)%n else '?')
                types.append(ls + rs)
                exc_types_all[ls+rs] += 1

            pair = tuple(types)
            exc_pair_counts[pair] += 1
            total_exc_pairs += 1
            if types[0][0] != types[1][0]:  # different leave sides
                mixed += 1

    print(f"\nCLAIM 1 — Excursion types:")
    for k in sorted(exc_types_all):
        print(f"  {k}: {exc_types_all[k]}")
    print(f"Excursion pair types:")
    for k in sorted(exc_pair_counts):
        print(f"  {k}: {exc_pair_counts[k]}")
    print(f"Mixed-side pairs: {mixed}/{total_exc_pairs}")
    if mixed == 0:
        print(f"  *** CONFIRMED: ALL excursions same-side at n={n} ***")

    # === CLAIM 2: Gate neighbor free slots ===
    free_slot_counts = Counter()
    for cyc in all_cycles:
        path = cyc['path']
        movers = cyc['movers']
        CL = len(path)

        for p in range(n):
            if cyc['fc'][p] != 2: continue
            fire_steps = [t for t in range(CL) if movers[t] == p]
            if len(fire_steps) != 2: continue
            gate = movers[(fire_steps[0] + 1) % CL]

            # Gate's contexts grouped by R (= p's value)
            nm_by_R = {}
            m_by_R = {}
            for t in range(CL):
                c = all_configs[path[t]]
                ctx_LS = (c[(gate-1)%n], c[gate])
                R = c[p]
                if movers[t] == gate:
                    m_by_R.setdefault(R, set()).add(ctx_LS)
                else:
                    nm_by_R.setdefault(R, set()).add(ctx_LS)

            min_free = 4
            for R in range(2):
                nm = len(nm_by_R.get(R, set()))
                m = len(m_by_R.get(R, set()))
                free = 4 - nm - m
                min_free = min(min_free, free)

            free_slot_counts[min_free] += 1

    print(f"\nCLAIM 2 — Gate neighbor min free slots per R-bucket:")
    for k in sorted(free_slot_counts):
        print(f"  {k} free: {free_slot_counts[k]}")

    # === CLAIM 3: Detailed gate usage ===
    # For each R-bucket: how many NM vs M entries?
    nm_m_profile = Counter()
    for cyc in all_cycles:
        path = cyc['path']
        movers = cyc['movers']
        CL = len(path)

        for p in range(n):
            if cyc['fc'][p] != 2: continue
            fire_steps = [t for t in range(CL) if movers[t] == p]
            if len(fire_steps) != 2: continue
            gate = movers[(fire_steps[0] + 1) % CL]

            nm_by_R = {}
            m_by_R = {}
            for t in range(CL):
                c = all_configs[path[t]]
                ctx_LS = (c[(gate-1)%n], c[gate])
                R = c[p]
                if movers[t] == gate:
                    m_by_R.setdefault(R, set()).add(ctx_LS)
                else:
                    nm_by_R.setdefault(R, set()).add(ctx_LS)

            for R in range(2):
                nm = len(nm_by_R.get(R, set()))
                m = len(m_by_R.get(R, set()))
                nm_m_profile[(R, nm, m)] += 1

    print(f"\nGate (R-bucket, |NM|, |M|) profile:")
    for k in sorted(nm_m_profile):
        print(f"  R={k[0]}, |NM|={k[1]}, |M|={k[2]}: {nm_m_profile[k]}")

    # === How many times does gate fire per excursion? ===
    gate_fires_per_exc = Counter()
    for cyc in all_cycles:
        path = cyc['path']
        movers = cyc['movers']
        CL = len(path)

        for p in range(n):
            if cyc['fc'][p] != 2: continue
            fire_steps = [t for t in range(CL) if movers[t] == p]
            if len(fire_steps) != 2: continue
            gate = movers[(fire_steps[0] + 1) % CL]
            t1, t2 = fire_steps

            # Excursion 1: t1+1 to t2-1
            gf1 = sum(1 for t in range(t1+1, t2) if movers[t] == gate)
            # Excursion 2: t2+1 to t1-1 (wrapping)
            gf2 = sum(1 for t in range(t2+1, t1 + CL) if movers[t % CL] == gate)

            gate_fires_per_exc[(gf1, gf2)] += 1

    print(f"\nGate fires per excursion (exc1, exc2):")
    for k in sorted(gate_fires_per_exc):
        print(f"  {k}: {gate_fires_per_exc[k]}")

    return all_cycles

# Run for n=5, 7, 9
for n in [5, 7]:
    analyze_n(n)

# n=9 might be slow, try with tighter bound
print("\n\n*** Attempting n=9 (may be slow) ***")
analyze_n(9, max_path_len=22)
