#!/usr/bin/env python3
"""
CRITICAL: fc=4 at middle binary EXISTS with ternary boundaries when
we only check entry conflict at binary procs. Need to also check
entry conflict at ALL procs (including ternary boundaries).
"""
from itertools import product as iproduct
import time

def search_with_full_ec(n, ms, middle, target_fc, max_path_len):
    """DFS with entry conflict tracking at ALL procs."""
    all_configs = list(iproduct(*(range(m) for m in ms)))
    cidx = {c: i for i, c in enumerate(all_configs)}
    total = len(all_configs)

    # Context size for each proc
    ctx_sizes = {}
    for p in range(n):
        ctx_sizes[p] = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]

    def ctx_idx(p, c):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        return L * ms[p] * ms[(p+1)%n] + S * ms[(p+1)%n] + R

    def signed_step(a, b):
        d = (b - a) % n
        if d == 1: return 1
        elif d == n - 1: return -1
        return 0

    t0 = time.time()
    found = 0
    nodes = 0

    for start in range(total):
        init_mm = {p: 0 for p in range(n)}
        init_nm = {p: 0 for p in range(n)}

        stack = [(start, frozenset([start]), [0]*n, 0, dict(init_mm), dict(init_nm), [])]

        while stack:
            ci, visited, fc, wind, mm, nm, movs = stack.pop()
            nodes += 1

            if len(visited) > max_path_len: continue

            c = all_configs[ci]

            for mover in range(n):
                S = c[mover]
                possible_vals = [v for v in range(ms[mover]) if v != S]

                for new_val in possible_vals:
                    valid = True
                    new_mm = dict(mm)
                    new_nm = dict(nm)

                    # Mover: check and update
                    ci_m = ctx_idx(mover, c)
                    if nm[mover] & (1 << ci_m):
                        continue
                    new_mm[mover] = mm[mover] | (1 << ci_m)

                    # Non-movers: check and update
                    for p in range(n):
                        if p == mover: continue
                        ci_p = ctx_idx(p, c)
                        if mm[p] & (1 << ci_p):
                            valid = False; break
                        new_nm[p] = nm[p] | (1 << ci_p)

                    if not valid: continue

                    new_c = list(c)
                    new_c[mover] = new_val
                    new_ci = cidx[tuple(new_c)]
                    new_fc = list(fc); new_fc[mover] += 1
                    new_wind = wind
                    if movs: new_wind += signed_step(movs[-1], mover)

                    if new_ci == start and len(visited) >= 3:
                        fw = new_wind + signed_step(mover, movs[0])
                        if fw == 0 and new_fc[middle] >= target_fc:
                            found += 1
                            if found <= 5:
                                print(f"  FOUND: len={len(visited)}, fc={new_fc}")
                            if found > 100:
                                return found, time.time() - t0, nodes
                        continue

                    if new_ci in visited: continue

                    remaining = max_path_len - len(visited)
                    if new_fc[middle] + remaining < target_fc: continue

                    stack.append((new_ci, visited | {new_ci}, new_fc, new_wind,
                                  new_mm, new_nm, movs + [mover]))

    return found, time.time() - t0, nodes

# Test: all binary (sanity check)
print("=== All binary ms=[2,2,2,2,2], fc(2)>=3 ===")
f, t, nodes = search_with_full_ec(5, [2,2,2,2,2], 2, 3, 14)
print(f"Result: {f} found, {t:.1f}s, {nodes} nodes\n")

# Test: ternary boundaries
print("=== Ternary boundaries ms=[3,2,2,2,3], fc(2)>=3 ===")
f, t, nodes = search_with_full_ec(5, [3,2,2,2,3], 2, 3, 20)
print(f"Result: {f} found, {t:.1f}s, {nodes} nodes\n")

# If still found: try with tighter path bound
if f > 0:
    for mpl in [14, 12, 10]:
        print(f"=== Ternary boundaries, max_path={mpl} ===")
        f, t, nodes = search_with_full_ec(5, [3,2,2,2,3], 2, 3, mpl)
        print(f"Result: {f} found, {t:.1f}s, {nodes} nodes\n")
