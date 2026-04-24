#!/usr/bin/env python3
"""
Key discovery: all excursions between p's firings are SAME-SIDE (LL or RR).
This means the mover bounces back and forth on one side of p.

For fc=4: there would be 4 excursions (or 3 between fires 1-2, 2-3, 3-4, plus
the wrap-around). If all same-side, say LL, then p-1 is the "gate" — the mover
always enters and exits through p-1.

This means p-1 fires at least once per excursion (it must let the mover through).
With 4 excursions: p-1 fires >= 4 times.

But wait: p-1 is also binary (fc must be even). And each excursion, p-1 sees
p's value as its R-component.

Let's verify: does the one-sided property hold at n=7 and n=9 too?
And: what exactly does p-1 see at the excursion entry/exit points?
"""
from itertools import product as iproduct

for n in [5, 7]:
    ms = [2] * n
    total = 2 ** n
    all_configs = list(iproduct(range(2), repeat=n))
    config_idx = {c: i for i, c in enumerate(all_configs)}

    def signed_step(a, b, n=n):
        d = (b - a) % n
        if d == 1: return 1
        elif d == n - 1: return -1
        return 0

    print(f"\n{'='*60}")
    print(f"n={n}, all binary")

    all_cycles = []
    for start in range(total):
        stack = [(start, [start], [0]*n, 0, {}, [])]
        while stack:
            ci, path, fc, wind, cons, movs = stack.pop()
            if len(path) > 2*n + 4: continue
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
                            'fc': list(new_fc), 'cons': dict(new_cons)
                        })
                    continue
                if new_ci in path: continue
                stack.append((new_ci, path+[new_ci], new_fc, new_wind, new_cons, movs+[mover]))

    print(f"Found {len(all_cycles)} zero-winding cycles")
    print(f"Max fc: {max(max(c['fc']) for c in all_cycles) if all_cycles else 'N/A'}")

    # Check excursion types for ALL procs with fc=2
    from collections import Counter
    exc_pair_counts = Counter()
    mixed_excursion = 0
    total_pairs = 0

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
            # Excursion 1: t1+1 to t2-1 (between fires)
            # Excursion 2: t2+1 to t1-1 (wrapping)
            for (ta, tb) in [(t1, t2), (t2, t1 + CL)]:
                leave = movers[(ta + 1) % CL]
                ret = movers[(tb - 1) % CL]
                ls = 'L' if leave == (p-1)%n else 'R'
                rs = 'L' if ret == (p-1)%n else 'R'
                types.append(ls + rs)

            pair = tuple(types)
            exc_pair_counts[pair] += 1
            total_pairs += 1
            if types[0] != types[1]:
                mixed_excursion += 1

    print(f"\nExcursion pair types:")
    for k in sorted(exc_pair_counts):
        print(f"  {k}: {exc_pair_counts[k]}")
    print(f"Mixed (different sides): {mixed_excursion}/{total_pairs}")

    # CRITICAL: For each fc=2 proc p, what is the neighbor's full entry conflict budget?
    # Focus on the "gate" neighbor (the one used by excursions).
    # At p's fire times: gate is non-mover with R = p's value.
    # During excursion: gate fires (mover) with R = p's value (p is constant).
    # So gate sees SAME R-value as mover AND non-mover.
    # Only (L_gate, S_gate) can differ.
    #
    # With binary gate: (L_gate, S_gate) ∈ {0,1}^2 = 4 options.
    # At 2 fires of p: gate has 2 non-mover entries with that R.
    # During 2 excursions: gate has some mover entries with that R.
    # If fc(p)=4: 4 non-mover entries with the SAME R (at same-parity fires).
    # But only 4 possible (L,S) pairs! So 4 entries use all 4 pairs.
    # Gate's mover entries during excursions also have the same R.
    # Gate fires at least once per excursion → at least 3 mover entries with same R.
    # With only 4 (L,S) slots and 4 non-mover + >=3 mover entries... PIGEONHOLE!

    print(f"\n--- PIGEONHOLE CHECK at gate neighbor ---")
    for cyc in all_cycles[:20]:
        path = cyc['path']
        movers = cyc['movers']
        CL = len(path)

        for p in range(n):
            if cyc['fc'][p] != 2: continue
            fire_steps = [t for t in range(CL) if movers[t] == p]
            t1, t2 = fire_steps

            # Determine gate neighbor
            leave1 = movers[(t1 + 1) % CL]
            gate = leave1  # same side for both excursions

            # At p's fires: what R does gate see?
            c1 = all_configs[path[t1]]
            c2 = all_configs[path[t2]]

            gate_R_at_fire1 = c1[p]  # gate's R = p's value
            gate_R_at_fire2 = c2[p]

            # Gate's non-mover entries (at p's fires)
            gate_nm_1 = (c1[(gate-1)%n], c1[gate], c1[p])
            gate_nm_2 = (c2[(gate-1)%n], c2[gate], c2[p])

            # Gate's mover entries (when gate fires during excursions)
            gate_mover_ctxs = []
            for t in range(CL):
                if movers[t] == gate:
                    c = all_configs[path[t]]
                    gate_mover_ctxs.append((c[(gate-1)%n], c[gate], c[p]))

            # Check overlap
            gate_nm_set = {gate_nm_1, gate_nm_2}
            gate_m_set = set(gate_mover_ctxs)

            # Group by R value
            nm_by_R = {}
            for ctx in gate_nm_set:
                nm_by_R.setdefault(ctx[2], set()).add((ctx[0], ctx[1]))
            m_by_R = {}
            for ctx in gate_m_set:
                m_by_R.setdefault(ctx[2], set()).add((ctx[0], ctx[1]))

            if cyc == all_cycles[0]:
                print(f"\n  Cycle 0, p={p}, gate={gate}")
                print(f"    Gate non-mover at p-fires: {gate_nm_set}")
                print(f"    Gate mover contexts: {gate_m_set}")
                print(f"    NM by R: {nm_by_R}")
                print(f"    M by R: {m_by_R}")
                for R in nm_by_R:
                    if R in m_by_R:
                        overlap = nm_by_R[R] & m_by_R[R]
                        free = 4 - len(nm_by_R[R]) - len(m_by_R[R]) + len(overlap)
                        print(f"    R={R}: NM (L,S) pairs={nm_by_R[R]}, M (L,S) pairs={m_by_R[R]}, overlap={overlap}, free_slots={free}")

    # SUMMARY: for each cycle, compute the tightest R-bucket
    print(f"\n--- TIGHTEST R-BUCKET SUMMARY ---")
    min_free_counts = Counter()
    for cyc in all_cycles:
        path = cyc['path']
        movers = cyc['movers']
        CL = len(path)
        for p in range(n):
            if cyc['fc'][p] != 2: continue
            fire_steps = [t for t in range(CL) if movers[t] == p]
            gate = movers[(fire_steps[0] + 1) % CL]

            # Collect all gate contexts
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

            # For each R: how many free (L,S) slots?
            min_free = 4
            for R in set(list(nm_by_R.keys()) + list(m_by_R.keys())):
                nm = len(nm_by_R.get(R, set()))
                m = len(m_by_R.get(R, set()))
                free = 4 - nm - m  # free if no overlap
                min_free = min(min_free, free)

            min_free_counts[min_free] += 1

    print(f"Minimum free (L,S) slots at gate by R-bucket: {dict(sorted(min_free_counts.items()))}")
    print(f"\nInterpretation: if min_free <= 0, the current fc=2 cycle is already near-saturated.")
    print(f"For fc=4: we'd need ~2x more entries per R-bucket → likely saturated → conflict.")
