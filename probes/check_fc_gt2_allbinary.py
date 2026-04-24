#!/usr/bin/env python3
"""
Check: at n=5, ms=[2,2,2,2,2] (all binary), do zero-winding good cycles with fc > 2 exist?

All processors binary: 2^5 = 32 configs. Each transition function f: {0,1}^3 -> {0,1}.
5 processors, each with 256 possible functions. 256^5 ≈ 10^12 — way too many to enumerate.

Instead: enumerate all 32-config state spaces and search for valid cycles directly.
Build the transition graph: for each config and each privileged processor, compute the successor.
Then search for zero-winding simple cycles with fc > 2 at some processor.
"""
from itertools import product as iproduct

n = 5
ms = [2] * n
total_configs = 2 ** n  # 32

all_configs = list(iproduct(range(2), repeat=n))
config_idx = {c: i for i, c in enumerate(all_configs)}

# For all-binary: each processor's function is f: {0,1}^3 -> {0,1}
# There are 256 possible functions per processor.
# For 5 processors: 256^5 ≈ 10^12 — can't enumerate.

# INSTEAD: enumerate all possible CYCLES directly.
# A cycle is a sequence of configs c_0, c_1, ..., c_{L-1} where:
# - Each c_k and c_{k+1} differ at exactly one position (the mover)
# - At the mover position: c_{k+1}[mover] = 1 - c_k[mover] (binary toggle)
# - The mover at c_k is privileged: f(L, S, R) != S, i.e., f(L, S, R) = 1-S
# - Non-movers at c_k are NOT privileged: f(L, S, R) = S
# - All configs are distinct
# - The cycle closes: c_L = c_0
# - Zero winding: total displacement = 0

# The non-mover constraint is CRUCIAL: it constrains the transition function.
# For each non-mover processor p at step k: f_p(L, S, R) = S.
# This means: the context (L, S, R) at p is in the "identity" set.

# For binary: f(L, S, R) ∈ {S, 1-S}. If identity: f = S. If privileged: f = 1-S.
# The same (L, S, R) can't be both identity and privileged (entry conflict = contradiction).

# So: for a valid good cycle, the transition function must be CONSISTENT:
# every (L, S, R) that appears at p as non-mover must have f_p = S,
# and every (L, S, R) that appears at p as mover must have f_p = 1-S.
# No (L, S, R) can appear as both mover and non-mover at p.

# This is exactly the entry conflict condition!

# SO: the existence of a good cycle is equivalent to:
# for each processor p, the set of (L,S,R) at mover steps and the set at non-mover steps are DISJOINT.

# For binary: (L,S,R) ∈ {0,1}^3, 8 possible contexts. The mover/non-mover sets partition {0,1}^3.

# With this constraint: just search for valid cycles by DFS.

print("Searching for zero-winding cycles with fc > 2 at n=5, all binary...")
print(f"Total configs: {total_configs}")

def signed_step(a, b):
    d = (b - a) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0

found = 0
max_len = 32  # at most 32 distinct configs

# For each starting config, do DFS
for start in range(total_configs):
    c0 = all_configs[start]

    # DFS: (config, path, fc, winding, constraints, movers)
    # constraints: dict (proc, L, S, R) -> 'mover' or 'nonmover'
    stack = [(start, [start], [0]*n, 0, {}, [])]

    while stack:
        ci, path, fc, wind, cons, movs = stack.pop()

        if len(path) > max_len:
            continue

        c = all_configs[ci]

        # Try each processor as mover
        for mover in range(n):
            L = c[(mover-1) % n]
            S = c[mover]
            R = c[(mover+1) % n]

            # Check mover constraint consistency
            key = (mover, L, S, R)
            if key in cons and cons[key] == 'nonmover':
                continue  # (L,S,R) already seen as non-mover at this proc

            # Check non-mover constraints for all OTHER processors
            valid = True
            new_cons = dict(cons)
            new_cons[key] = 'mover'

            for p in range(n):
                if p == mover:
                    continue
                Lp = c[(p-1) % n]
                Sp = c[p]
                Rp = c[(p+1) % n]
                kp = (p, Lp, Sp, Rp)
                if kp in new_cons and new_cons[kp] == 'mover':
                    valid = False
                    break
                new_cons[kp] = 'nonmover'

            if not valid:
                continue

            # Compute new config
            new_c = list(c)
            new_c[mover] = 1 - S
            new_ci = config_idx[tuple(new_c)]

            # Update fc and winding
            new_fc = list(fc)
            new_fc[mover] += 1
            new_wind = wind
            if movs:
                new_wind += signed_step(movs[-1], mover)

            # Check cycle closure
            if new_ci == start and len(path) >= 3:
                final_wind = new_wind + signed_step(mover, movs[0])
                if final_wind == 0:  # zero winding
                    if max(new_fc) > 2:
                        found += 1
                        if found <= 10:
                            print(f"FOUND: len={len(path)}, fc={new_fc}, wind={final_wind}")
                            print(f"  path: {[all_configs[i] for i in path[:6]]}...")
                continue

            # Don't revisit
            if new_ci in path:
                continue

            stack.append((new_ci, path + [new_ci], new_fc, new_wind, new_cons, movs + [mover]))

    if start % 4 == 0:
        print(f"  Checked start {start}/{total_configs}, found={found}")

print(f"\nDone. Found: {found}")
if found == 0:
    print("NO zero-winding fc>2 cycles exist at n=5, all binary!")
