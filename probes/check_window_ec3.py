#!/usr/bin/env python3
"""
Quick check: do the fc>=3 cycles found with binary-only EC also
have entry conflict at ternary procs?

Strategy: find the fc>=3 cycles from the binary-EC search,
then retroactively check entry conflict at ALL procs.
"""
from itertools import product as iproduct
import time

n = 5
ms = [3, 2, 2, 2, 3]
middle = 2

all_configs = list(iproduct(*(range(m) for m in ms)))
cidx = {c: i for i, c in enumerate(all_configs)}
total = len(all_configs)

binary_procs = [1, 2, 3]

def signed_step(a, b):
    d = (b - a) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0

print(f"n={n}, ms={ms}, {total} configs")
print("Finding fc>=3 cycles (binary-only EC check)...")
print("Then checking if ternary procs have entry conflict.")

t0 = time.time()
found_cycles = []

for start in range(total):
    init_mm = {p: 0 for p in binary_procs}
    init_nm = {p: 0 for p in binary_procs}

    def ctx_idx_bin(p, c):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        return L * 2 * ms[(p+1)%n] + S * ms[(p+1)%n] + R

    stack = [(start, [start], [0]*n, 0, dict(init_mm), dict(init_nm), [])]

    while stack:
        ci, path, fc, wind, mm, nm, movs = stack.pop()

        if len(path) > 18: continue

        c = all_configs[ci]

        for mover in range(n):
            S = c[mover]
            possible_vals = [v for v in range(ms[mover]) if v != S]

            for new_val in possible_vals:
                valid = True
                new_mm = dict(mm)
                new_nm = dict(nm)

                # Check binary EC only
                if mover in binary_procs:
                    ci_m = ctx_idx_bin(mover, c)
                    if nm[mover] & (1 << ci_m):
                        continue
                    new_mm[mover] = mm[mover] | (1 << ci_m)

                for p in binary_procs:
                    if p == mover: continue
                    ci_p = ctx_idx_bin(p, c)
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

                if new_ci == start and len(path) >= 3:
                    fw = new_wind + signed_step(mover, movs[0])
                    if fw == 0 and new_fc[middle] >= 3:
                        found_cycles.append({
                            'path': list(path),
                            'movers': movs + [mover],
                            'fc': list(new_fc)
                        })
                        if len(found_cycles) <= 3:
                            print(f"  Found: len={len(path)}, fc={new_fc}")
                        if len(found_cycles) >= 50:
                            break
                    continue

                if new_ci in path: continue

                remaining = 18 - len(path)
                if new_fc[middle] + remaining < 3: continue

                stack.append((new_ci, path + [new_ci], new_fc, new_wind,
                              new_mm, new_nm, movs + [mover]))
            if len(found_cycles) >= 50: break
        if len(found_cycles) >= 50: break
    if len(found_cycles) >= 50: break

elapsed = time.time() - t0
print(f"\nFound {len(found_cycles)} cycles with fc(middle)>=3 in {elapsed:.1f}s")

# Now check each cycle for entry conflict at ALL procs (including ternary)
print("\nChecking entry conflict at ALL procs for each cycle...")
survivors = 0

for idx, cyc in enumerate(found_cycles):
    path = cyc['path']
    movers = cyc['movers']
    L = len(path)

    # Build mover/nonmover context sets for ALL procs
    mover_ctxs = {p: set() for p in range(n)}
    nonmover_ctxs = {p: set() for p in range(n)}

    has_conflict = False
    for t in range(L):
        c = all_configs[path[t]]
        m = movers[t]
        for p in range(n):
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if p == m:
                if ctx in nonmover_ctxs[p]:
                    has_conflict = True
                    if idx < 5:
                        print(f"  Cycle {idx}: CONFLICT at proc {p} (ternary={ms[p]>2}), ctx={ctx}")
                    break
                mover_ctxs[p].add(ctx)
            else:
                if ctx in mover_ctxs[p]:
                    has_conflict = True
                    if idx < 5:
                        print(f"  Cycle {idx}: CONFLICT at proc {p} (ternary={ms[p]>2}), ctx={ctx}")
                    break
                nonmover_ctxs[p].add(ctx)
        if has_conflict: break

    if not has_conflict:
        survivors += 1
        if survivors <= 5:
            print(f"  Cycle {idx}: NO CONFLICT! len={L}, fc={cyc['fc']}")
            print(f"    movers: {movers}")
            # Print mover/nonmover counts per proc
            for p in range(n):
                print(f"    proc {p} (m={ms[p]}): |M|={len(mover_ctxs[p])}, |N|={len(nonmover_ctxs[p])}")

print(f"\nSurvivors (no entry conflict at any proc): {survivors}/{len(found_cycles)}")
if survivors == 0:
    print("*** ALL fc>=3 cycles have entry conflict at ternary procs! ***")
    print("*** Entry conflict at binary procs alone is NOT sufficient! ***")
