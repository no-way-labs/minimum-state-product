#!/usr/bin/env python3
"""Check zero-winding fc distribution at n=7 and n=9, all binary."""
from itertools import product as iproduct

for n in [7, 9]:
    ms = [2] * n
    total = 2 ** n
    print(f"\nn={n}, configs={total}")

    all_configs = list(iproduct(range(2), repeat=n))
    config_idx = {c: i for i, c in enumerate(all_configs)}

    def signed_step(a, b, n=n):
        d = (b - a) % n
        if d == 1: return 1
        elif d == n - 1: return -1
        return 0

    fc_dist = {}
    total_cycles = 0

    for start in range(total):
        stack = [(start, [start], [0]*n, 0, {}, [])]
        while stack:
            ci, path, fc, wind, cons, movs = stack.pop()
            if len(path) > 2*n + 4: continue  # reasonable bound
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
                        total_cycles += 1
                        mfc = max(new_fc)
                        fc_dist[mfc] = fc_dist.get(mfc, 0) + 1
                    continue
                if new_ci in path: continue
                stack.append((new_ci, path+[new_ci], new_fc, new_wind, new_cons, movs+[mover]))

    print(f"  Total zero-winding cycles: {total_cycles}")
    print(f"  Fire count distribution: {dict(sorted(fc_dist.items()))}")
    if all(k <= 2 for k in fc_dist):
        print(f"  ALL have max_fc <= 2!")
    else:
        print(f"  WARNING: fc > 2 found!")
