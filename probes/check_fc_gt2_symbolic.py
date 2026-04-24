#!/usr/bin/env python3
"""
Symbolic search: does a zero-winding fc>2 good cycle exist at n=5?

Instead of enumerating 16M rule triples: search the 72-state global config space
for valid cycles. Each step constrains rule bits. Track constraints as we build
the cycle path.

n=5, ms=[2,2,2,3,3]. Total configs = 2^3 * 3^2 = 72.
"""
import sys
sys.path.insert(0, './claude')
from cup2_theorem import build_system
from itertools import product as iproduct

n = 5
ms = [2, 2, 2, 3, 3]
total_configs = 1
for m in ms:
    total_configs *= m
print(f"n={n}, ms={ms}, total configs={total_configs}")

# Enumerate all configs
all_configs = list(iproduct(*(range(m) for m in ms)))
config_idx = {c: i for i, c in enumerate(all_configs)}

# For each config and each possible mover: what's the result config?
# And what rule constraint does it impose?
# The constraint is: f_mover(L, S, R) must equal the new value (not S, since mover is privileged)
transitions = {}  # (config_idx, mover) -> (new_config_idx, new_val, old_val, L, S, R)

for ci, c in enumerate(all_configs):
    for mover in range(n):
        L = c[(mover - 1) % n]
        S = c[mover]
        R = c[(mover + 1) % n]
        # The mover is privileged iff f(L,S,R) != S
        # If privileged: new value = f(L,S,R) which is some value != S
        # For binary mover: new value = 1 - S
        # For ternary mover: new value could be (S+1)%3 or (S+2)%3
        possible_new_vals = [v for v in range(ms[mover]) if v != S]
        for new_val in possible_new_vals:
            new_c = list(c)
            new_c[mover] = new_val
            new_c = tuple(new_c)
            ni = config_idx[new_c]
            transitions[(ci, mover, new_val)] = (ni, L, S, R)

# Now: search for zero-winding cycles with fc > 2 at some binary processor
# using DFS with rule constraint tracking

# For binary processors (0,1,2): f : {0,1}^3 -> {0,1}
# Each has 8 entries. A rule constraint says: f_mover(L, S, R) = new_val.
# If new_val = S: NOT privileged (non-mover step). Contradiction with being chosen as mover.
# If new_val != S: privileged. Constraint: f(L,S,R) = new_val.

# For ternary: use CUP-2 fixed tables
ms_cup2, fs_cup2 = build_system(n)
ternary_tables = {}
for p in [3, 4]:
    table = {}
    for L in range(ms[(p-1) % n]):
        for S in range(ms[p]):
            for R in range(ms[(p+1) % n]):
                table[(L, S, R)] = fs_cup2[p](L, S, R)
    ternary_tables[p] = table

def signed_step(mover_curr, mover_next, n):
    d = (mover_next - mover_curr) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    else: return 0

# DFS for cycles
# State: (current_config_idx, path_of_config_indices, fire_counts, winding, rule_constraints)
# Rule constraints: dict (processor, L, S, R) -> required_output

found = 0
max_cycle_len = 20  # search up to this length

def search_cycles():
    global found
    # Try each starting config
    for start_ci in range(total_configs):
        start_c = all_configs[start_ci]
        # DFS
        stack = [(start_ci, [start_ci], [0]*n, 0, {}, [])]  # (ci, path, fc, winding, constraints, movers)

        while stack:
            ci, path, fc, winding, constraints, movers = stack.pop()

            if len(path) > max_cycle_len:
                continue

            c = all_configs[ci]

            # Try each possible mover
            for mover in range(n):
                L = c[(mover - 1) % n]
                S = c[mover]
                R = c[(mover + 1) % n]

                # For ternary: check if privileged under CUP-2
                if mover in [3, 4]:
                    if ternary_tables[mover][(L, S, R)] == S:
                        continue  # not privileged
                    new_val = ternary_tables[mover][(L, S, R)]
                else:
                    # Binary: new_val = 1 - S (only option)
                    new_val = 1 - S
                    # Check rule consistency
                    key = (mover, L, S, R)
                    if key in constraints:
                        if constraints[key] != new_val:
                            continue  # inconsistent
                    # Also check: this (L,S,R) must be privileged
                    # If we've seen this (L,S,R) as NON-mover: f(L,S,R) = S. But now f(L,S,R) = new_val != S. Contradiction.
                    # Track non-mover constraints too
                    # For non-mover at this config: all non-mover procs have f(L',S',R') = S'
                    # Check: do any non-mover procs at this config conflict with existing mover constraints?

                new_c = list(c)
                new_c[mover] = new_val
                new_ci = config_idx[tuple(new_c)]

                # Update fire count
                new_fc = list(fc)
                new_fc[mover] += 1

                # Update winding
                new_winding = winding
                if movers:
                    new_winding += signed_step(movers[-1], mover, n)

                # Check if cycle closes
                if new_ci == start_ci and len(path) >= 3:
                    # Close winding
                    final_winding = new_winding + signed_step(mover, movers[0] if movers else mover, n)
                    if final_winding == 0:  # zero winding
                        if max(new_fc[0], new_fc[1], new_fc[2]) > 2:  # fc > 2 at binary
                            found += 1
                            if found <= 5:
                                print(f"FOUND fc>2 zero-winding cycle!")
                                print(f"  Length: {len(path)}")
                                print(f"  Fire counts: {new_fc}")
                                print(f"  Winding: {final_winding}")
                            if found > 100:
                                return
                    continue

                # Don't revisit
                if new_ci in path:
                    continue

                # Update constraints for binary mover
                new_constraints = dict(constraints)
                if mover in [0, 1, 2]:
                    key = (mover, L, S, R)
                    new_constraints[key] = new_val

                new_movers = movers + [mover]
                stack.append((new_ci, path + [new_ci], new_fc, new_winding, new_constraints, new_movers))

    print(f"Search complete. Found: {found}")

print("Searching for zero-winding fc>2 cycles (max length 20)...")
search_cycles()
print(f"Total found: {found}")
if found == 0:
    print("NO fc>2 zero-winding cycles exist at n=5 with CUP-2 ternary tables!")
