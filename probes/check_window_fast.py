#!/usr/bin/env python3
"""
Fast window automaton: use frozenset for constraints and aggressive pruning.
Only test small boundary sizes first.
"""
from itertools import product as iproduct
import time

def search_ring(n, ms, target_proc, target_fc, max_path_len):
    total_configs_list = list(iproduct(*(range(m) for m in ms)))
    cidx = {c: i for i, c in enumerate(total_configs_list)}
    total_c = len(total_configs_list)

    def signed_step(a, b):
        d = (b - a) % n
        if d == 1: return 1
        elif d == n - 1: return -1
        return 0

    t0 = time.time()
    found = 0
    nodes_explored = 0

    for start in range(total_c):
        # Use tuples for constraints (faster than dicts)
        stack = [(start, frozenset([start]), [0]*n, 0, frozenset(), frozenset(), [])]
        # mover_set, nonmover_set as frozensets of (proc, L, S, R)

        while stack:
            ci, visited, fc, wind, mover_cons, nonmover_cons, movs = stack.pop()
            nodes_explored += 1

            if len(visited) > max_path_len: continue

            c = total_configs_list[ci]
            for mover in range(n):
                L = c[(mover-1) % n]; S = c[mover]; R = c[(mover+1) % n]
                key = (mover, L, S, R)

                # Check: this key must not be in nonmover set
                if key in nonmover_cons: continue

                # Check: all non-movers at this config must not be in mover set
                valid = True
                new_nm_keys = []
                for p in range(n):
                    if p == mover: continue
                    kp = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                    if kp in mover_cons:
                        valid = False; break
                    new_nm_keys.append(kp)
                if not valid: continue

                new_mover_cons = mover_cons | {key}
                new_nonmover_cons = nonmover_cons | frozenset(new_nm_keys)

                possible_vals = [v for v in range(ms[mover]) if v != S]
                for new_val in possible_vals:
                    new_c = list(c)
                    new_c[mover] = new_val
                    new_ci = cidx[tuple(new_c)]
                    new_fc = list(fc); new_fc[mover] += 1
                    new_wind = wind
                    if movs: new_wind += signed_step(movs[-1], mover)

                    if new_ci == start and len(visited) >= 3:
                        fw = new_wind + signed_step(mover, movs[0])
                        if fw == 0:
                            if new_fc[target_proc] >= target_fc:
                                found += 1
                                if found <= 5:
                                    print(f"  FOUND: len={len(visited)}, fc={new_fc}")
                        continue

                    if new_ci in visited: continue

                    # Prune: if target proc can't reach target_fc
                    remaining = max_path_len - len(visited)
                    if new_fc[target_proc] + remaining < target_fc: continue

                    stack.append((new_ci, visited | {new_ci}, new_fc, new_wind,
                                  new_mover_cons, new_nonmover_cons, movs+[mover]))

    elapsed = time.time() - t0
    return found, elapsed, nodes_explored

# Test with small systems
tests = [
    (5, [2,2,2,2,2], 2, 3, 14, "all binary"),
    (5, [3,2,2,2,3], 2, 3, 16, "ternary boundaries"),
    (5, [4,2,2,2,4], 2, 3, 16, "quaternary boundaries"),
    (5, [3,2,2,2,4], 2, 3, 16, "mixed 3/4 boundaries"),
]

for n, ms, tp, tf, mpl, desc in tests:
    total = 1
    for m in ms: total *= m
    print(f"=== n={n}, ms={ms} ({desc}), {total} configs, target: proc {tp} fc>={tf} ===")
    f, t, nodes = search_ring(n, ms, tp, tf, mpl)
    print(f"Result: {f} found, {t:.1f}s, {nodes} nodes explored\n")
