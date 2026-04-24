#!/usr/bin/env python3
"""
Check: are zero-winding good cycles on MIXED systems (3 consecutive binary +
ternary/quaternary neighbors) also all length 4? Or do longer cycles exist?

This is the actual setting for the Lean proof: 3 consecutive binary procs
at positions 0,1,2, with non-binary procs elsewhere.

Test: n=5, ms=[2,2,2,3,3] and ms=[2,2,2,3,4]
"""
from itertools import product as iproduct
from collections import Counter

def analyze_mixed(n, ms, max_path_len=None):
    if max_path_len is None:
        max_path_len = 2 * n + 10

    total = 1
    for m in ms:
        total *= m

    all_configs = list(iproduct(*(range(m) for m in ms)))
    config_idx = {c: i for i, c in enumerate(all_configs)}

    def signed_step(a, b):
        d = (b - a) % n
        if d == 1: return 1
        elif d == n - 1: return -1
        return 0

    print(f"\n{'='*60}")
    print(f"n={n}, ms={ms}, total={total}, max_path={max_path_len}")

    import time
    t0 = time.time()

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
                new_c = list(c)
                # Transition: for binary, toggle. For non-binary, try all other values.
                possible_vals = [v for v in range(ms[mover]) if v != S]
                for new_val in possible_vals:
                    nc = list(new_c)
                    nc[mover] = new_val
                    new_ci = config_idx[tuple(nc)]
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
        print("No cycles found!")
        return

    max_fc = max(max(c['fc']) for c in all_cycles)
    fc_dist = Counter(max(c['fc']) for c in all_cycles)
    print(f"Max fc: {max_fc}")
    print(f"Max-fc distribution: {dict(sorted(fc_dist.items()))}")

    len_dist = Counter(len(c['path']) for c in all_cycles)
    print(f"Cycle length distribution: {dict(sorted(len_dist.items()))}")

    # fc at binary positions (0,1,2)
    binary_max_fc = Counter()
    for cyc in all_cycles:
        bmf = max(cyc['fc'][0], cyc['fc'][1], cyc['fc'][2])
        binary_max_fc[bmf] += 1
    print(f"Max fc at binary procs (0,1,2): {dict(sorted(binary_max_fc.items()))}")

    # Check excursion types for binary procs with fc >= 2
    exc_types = Counter()
    total_exc = 0
    mixed_exc = 0

    for cyc in all_cycles:
        path = cyc['path']
        movers = cyc['movers']
        CL = len(path)

        for p in range(3):  # binary procs only
            if cyc['fc'][p] < 2: continue
            fire_steps = [t for t in range(CL) if movers[t] == p]
            if len(fire_steps) < 2: continue

            # Check excursions between consecutive fires
            for i in range(len(fire_steps)):
                ta = fire_steps[i]
                tb = fire_steps[(i+1) % len(fire_steps)]
                if tb <= ta:
                    tb += CL

                if tb - ta <= 1: continue  # no excursion

                leave = movers[(ta + 1) % CL]
                ret = movers[(tb - 1) % CL]
                ls = 'L' if leave == (p-1)%n else ('R' if leave == (p+1)%n else '?')
                rs = 'L' if ret == (p-1)%n else ('R' if ret == (p+1)%n else '?')
                exc_types[ls+rs] += 1
                total_exc += 1
                if ls != rs:
                    mixed_exc += 1

    print(f"\nExcursion types at binary procs: {dict(sorted(exc_types.items()))}")
    print(f"Cross-ring excursions (LR or RL): {mixed_exc}/{total_exc}")

    # For longer cycles: show examples
    long_cycles = [c for c in all_cycles if len(c['path']) > 4]
    if long_cycles:
        print(f"\n--- LONGER CYCLES (>{4} steps) ---")
        for cyc in long_cycles[:5]:
            print(f"  len={len(cyc['path'])}, fc={cyc['fc']}, movers={cyc['movers'][:10]}...")

    # Check: for cycles where binary fc > 2
    high_fc = [c for c in all_cycles if max(c['fc'][0], c['fc'][1], c['fc'][2]) > 2]
    if high_fc:
        print(f"\n!!! FOUND {len(high_fc)} cycles with binary fc > 2 !!!")
        for cyc in high_fc[:5]:
            print(f"  len={len(cyc['path'])}, fc={cyc['fc']}")
    else:
        print(f"\nCONFIRMED: No binary fc > 2 at n={n}, ms={ms}")

# Test cases
analyze_mixed(5, [2,2,2,3,3], max_path_len=20)
analyze_mixed(5, [2,2,2,3,4], max_path_len=20)
analyze_mixed(5, [2,2,2,4,4], max_path_len=20)

# n=6 mixed
analyze_mixed(6, [2,2,2,3,3,3], max_path_len=20)

# n=7 mixed (might be slow)
analyze_mixed(7, [2,2,2,3,3,3,3], max_path_len=20)
