#!/usr/bin/env python3
"""
Fast non-consecutive binary profile extraction.
Only n=5, ms=[2,3,2,3,2], shorter max path.
"""
from itertools import product as iproduct
from collections import Counter
import time

n = 5
ms = [2, 3, 2, 3, 2]
binary_procs = [0, 2, 4]
max_path_len = 12  # shorter bound

all_configs = list(iproduct(*(range(m) for m in ms)))
cidx = {c: i for i, c in enumerate(all_configs)}
total = len(all_configs)

def signed_step(a, b):
    d = (b - a) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0

t0 = time.time()
print(f"n={n}, ms={ms}, binary={binary_procs}, configs={total}, max_path={max_path_len}")

cycles_found = 0
ec_at = Counter()
no_ec = 0

for start in range(total):
    stack = [(start, frozenset([start]), [0]*n, 0, {}, [])]
    while stack:
        ci, visited, fc, wind, cons, movs = stack.pop()
        if len(visited) > max_path_len: continue
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
                if new_ci == start and len(visited) >= 3:
                    fw = new_wind + signed_step(mover, movs[0])
                    if fw == 0:
                        cycles_found += 1
                        # Check EC at each proc
                        found_ec = False
                        for p in range(n):
                            m_set = set()
                            n_set = set()
                            has_ec = False
                            for k, role in new_cons.items():
                                if k[0] != p: continue
                                ctx = k[1:]
                                if role == 'mover':
                                    if ctx in n_set: has_ec = True
                                    m_set.add(ctx)
                                else:
                                    if ctx in m_set: has_ec = True
                                    n_set.add(ctx)
                            if has_ec:
                                ec_at[p] += 1
                                found_ec = True
                        if not found_ec:
                            no_ec += 1
                    continue
                if new_ci in visited: continue
                remaining = max_path_len - len(visited)
                if remaining < 2: continue
                stack.append((new_ci, visited | {new_ci}, new_fc, new_wind,
                              new_cons, movs+[mover]))

elapsed = time.time() - t0
print(f"\nFound {cycles_found} zero-winding cycles in {elapsed:.1f}s")
print(f"Cycles with NO EC at any proc: {no_ec}")
print(f"EC locations: {dict(sorted(ec_at.items()))}")
for p in sorted(ec_at):
    print(f"  Proc {p} (m={ms[p]}): {ec_at[p]} conflicts")
if no_ec == 0:
    print("\n*** ALL cycles have entry conflict! ***")
