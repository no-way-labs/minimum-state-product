#!/usr/bin/env python3
"""
Extract the "local entry profile" for non-consecutive binary cycles.

For each zero-winding good cycle with ≥3 non-consecutive binary processors
at sub-threshold product, extract the minimal data that determines which
of the 4 EC mechanisms fires:

1. M = number of "gaps" (maximal ternary runs between binary procs)
2. J, K = lengths of one-sided segments at each binary proc
3. Phase = which side the first mover comes from
4. The first nonmover context vs mover context at the conflicting proc

Goal: determine how many distinct "profiles" exist and whether a small
finite automaton covers all of them.

Test at n=5, ms=[2,3,2,3,2] (non-consecutive binary at 0,2,4).
"""
from itertools import product as iproduct
from collections import Counter
import time

def analyze_nonconsec(n, ms, max_path_len=None):
    if max_path_len is None:
        max_path_len = 2 * n + 6

    binary_procs = [i for i in range(n) if ms[i] == 2]
    # Check non-consecutive: no two binary procs adjacent
    consec = any((binary_procs[i] + 1) % n == binary_procs[(i+1) % len(binary_procs)]
                 for i in range(len(binary_procs)))

    all_configs = list(iproduct(*(range(m) for m in ms)))
    cidx = {c: i for i, c in enumerate(all_configs)}
    total = len(all_configs)

    def signed_step(a, b):
        d = (b - a) % n
        if d == 1: return 1
        elif d == n - 1: return -1
        return 0

    t0 = time.time()
    print(f"n={n}, ms={ms}, binary={binary_procs}, consecutive={consec}, configs={total}")

    # Find all zero-winding good cycles
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
                possible_vals = [v for v in range(ms[mover]) if v != S]
                for new_val in possible_vals:
                    new_c = list(c); new_c[mover] = new_val
                    new_ci = cidx[tuple(new_c)]
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
                    stack.append((new_ci, path+[new_ci], new_fc, new_wind,
                                  new_cons, movs+[mover]))

    elapsed = time.time() - t0
    print(f"Found {len(all_cycles)} zero-winding cycles in {elapsed:.1f}s")

    if not all_cycles:
        print("No cycles found!")
        return

    # Analyze: which proc has entry conflict? What's the profile?
    ec_procs = Counter()
    ec_binary = 0
    ec_ternary = 0
    profiles = Counter()

    for cyc in all_cycles:
        # Check entry conflict at each proc
        for p in range(n):
            mover_ctxs = set()
            nonmover_ctxs = set()
            has_ec = False
            for key, role in cyc['cons'].items():
                if key[0] != p: continue
                ctx = key[1:]
                if role == 'mover':
                    if ctx in nonmover_ctxs:
                        has_ec = True
                    mover_ctxs.add(ctx)
                else:
                    if ctx in mover_ctxs:
                        has_ec = True
                    nonmover_ctxs.add(ctx)
            if has_ec:
                ec_procs[p] += 1
                if ms[p] == 2:
                    ec_binary += 1
                else:
                    ec_ternary += 1

                # Extract profile
                fc_p = cyc['fc'][p]
                is_binary = ms[p] == 2
                profiles[(p, is_binary, fc_p)] += 1

    print(f"\nEntry conflict locations:")
    for p in sorted(ec_procs):
        print(f"  Proc {p} (m={ms[p]}): {ec_procs[p]} conflicts")
    print(f"Binary EC: {ec_binary}, Ternary EC: {ec_ternary}")

    # How many cycles have NO entry conflict at all?
    no_ec = 0
    for cyc in all_cycles:
        has_any_ec = False
        for p in range(n):
            mover_ctxs = set()
            nonmover_ctxs = set()
            for key, role in cyc['cons'].items():
                if key[0] != p: continue
                ctx = key[1:]
                if role == 'mover':
                    if ctx in nonmover_ctxs: has_any_ec = True
                    mover_ctxs.add(ctx)
                else:
                    if ctx in mover_ctxs: has_any_ec = True
                    nonmover_ctxs.add(ctx)
            if has_any_ec: break
        if not has_any_ec:
            no_ec += 1
    print(f"\nCycles with NO entry conflict at ANY proc: {no_ec}/{len(all_cycles)}")

    # FC distribution at binary procs
    binary_fc_dist = Counter()
    for cyc in all_cycles:
        for p in binary_procs:
            binary_fc_dist[cyc['fc'][p]] += 1
    print(f"\nBinary proc fire count distribution: {dict(sorted(binary_fc_dist.items()))}")

    # Mover word structure: how many direction changes?
    reversal_dist = Counter()
    for cyc in all_cycles:
        movers = cyc['movers']
        L = len(movers)
        reversals = 0
        for i in range(L):
            s1 = signed_step(movers[i], movers[(i+1) % L])
            s2 = signed_step(movers[(i+1) % L], movers[(i+2) % L])
            if s1 != 0 and s2 != 0 and s1 != s2:
                reversals += 1
        reversal_dist[reversals] += 1
    print(f"\nReversal count distribution: {dict(sorted(reversal_dist.items()))}")

    return all_cycles

# Test non-consecutive binary
print("="*60)
analyze_nonconsec(5, [2,3,2,3,2])

print("\n" + "="*60)
analyze_nonconsec(5, [2,3,2,2,3])  # 3 binary, 2 consecutive + 1 separate

print("\n" + "="*60)
analyze_nonconsec(6, [2,3,2,3,2,3])  # 3 non-consecutive binary on n=6
