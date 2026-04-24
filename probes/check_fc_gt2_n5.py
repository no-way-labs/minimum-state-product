#!/usr/bin/env python3
"""
Check: at n=5 with 3 consecutive binary, do zero-winding good cycles with fc > 2 exist?

Enumerate ALL possible transition functions for the 3 binary processors at {0,1,2}
and ternary processors at {3,4}. For each valid system: find the good cycle.
Check if it's zero-winding and if the middle binary fires > 2.
"""
from itertools import product as iproduct

n = 5
# ms = [2, 2, 2, 3, 3] — 3 binary at {0,1,2}, ternary at {3,4}
ms = [2, 2, 2, 3, 3]

def make_transition(m_left, m_self, m_right):
    """Enumerate all transition functions m_left x m_self x m_right -> m_self."""
    domain_size = m_left * m_self * m_right
    for outputs in iproduct(range(m_self), repeat=domain_size):
        table = {}
        idx = 0
        for L in range(m_left):
            for S in range(m_self):
                for R in range(m_right):
                    table[(L, S, R)] = outputs[idx]
                    idx += 1
        yield table

def is_privileged(table, L, S, R):
    return table[(L, S, R)] != S

def find_good_cycle(fs, ms, n):
    """Find the good cycle by simulating from all-zeros."""
    config = tuple([0] * n)
    visited = {config}
    cycle = [config]

    for _ in range(10000):  # max steps
        # Find privileged processors
        priv = []
        for p in range(n):
            L = config[(p - 1) % n]
            S = config[p]
            R = config[(p + 1) % n]
            if is_privileged(fs[p], L, S, R):
                priv.append(p)

        if not priv:
            return None  # deadlock

        # Fire the first privileged (deterministic scheduler)
        mover = priv[0]
        L = config[(mover - 1) % n]
        S = config[mover]
        R = config[(mover + 1) % n]
        new_val = fs[mover][(L, S, R)]

        new_config = list(config)
        new_config[mover] = new_val
        new_config = tuple(new_config)

        if new_config in visited:
            # Found a cycle — extract it
            start_idx = cycle.index(new_config)
            return cycle[start_idx:]

        visited.add(new_config)
        cycle.append(new_config)
        config = new_config

    return None  # didn't converge

def analyze_cycle(cycle, n):
    """Analyze a good cycle: fire counts, winding."""
    L = len(cycle)
    fire_count = [0] * n
    displacement = 0

    for k in range(L):
        c = cycle[k]
        c_next = cycle[(k + 1) % L]
        # Find mover
        mover = None
        for p in range(n):
            if c[p] != c_next[p]:
                mover = p
                break
        if mover is None:
            continue
        fire_count[mover] += 1

        # Displacement
        prev_mover = None
        if k > 0:
            c_prev = cycle[k - 1] if k > 0 else cycle[-1]
            for p in range(n):
                if cycle[(k-1) % L][p] != c[p]:
                    prev_mover = p
                    break

    # Zero winding: compute total displacement
    total_disp = 0
    movers = []
    for k in range(L):
        c = cycle[k]
        c_next = cycle[(k + 1) % L]
        for p in range(n):
            if c[p] != c_next[p]:
                movers.append(p)
                break

    for k in range(len(movers)):
        curr = movers[k]
        nxt = movers[(k + 1) % len(movers)]
        diff = (nxt - curr) % n
        if diff == 1:
            total_disp += 1
        elif diff == n - 1:
            total_disp -= 1

    return fire_count, total_disp, movers

# For n=5: the transition functions at each processor
# Binary: {0,1}^3 -> {0,1}: 2^8 = 256 each
# Ternary {3}: depends on neighbors. Proc 3: left=2 (binary), self=3 (ternary), right=4 (ternary)
#   f_3: {0,1} x {0,1,2} x {0,1,2} -> {0,1,2}: 2*3*3 = 18 inputs, 3^18 outputs = too many

# Simplify: just check CUP-2 and a few random systems
print("Checking CUP-2 system at n=5...")
from cup2_theorem import build_system
ms_cup2, fs_cup2 = build_system(5)

# Build table format
tables = []
for p in range(5):
    table = {}
    for L in range(ms_cup2[(p-1) % 5]):
        for S in range(ms_cup2[p]):
            for R in range(ms_cup2[(p+1) % 5]):
                table[(L, S, R)] = fs_cup2[p](L, S, R)
    tables.append(table)

# Find good cycle
config = tuple([0] * 5)
visited_set = set()
trace = []
for _ in range(10000):
    if config in visited_set:
        start = next(i for i, c in enumerate(trace) if c == config)
        cycle = trace[start:]
        break
    visited_set.add(config)
    trace.append(config)

    priv = []
    for p in range(5):
        L = config[(p-1) % 5]
        S = config[p]
        R = config[(p+1) % 5]
        if tables[p][(L, S, R)] != S:
            priv.append(p)

    if not priv:
        print("DEADLOCK")
        break

    mover = priv[0]
    L = config[(mover-1) % 5]
    S = config[mover]
    R = config[(mover+1) % 5]
    new_config = list(config)
    new_config[mover] = tables[mover][(L, S, R)]
    config = tuple(new_config)
else:
    print("Didn't converge in 10000 steps")
    cycle = []

if cycle:
    fc, disp, movers = analyze_cycle(cycle, 5)
    print(f"  Cycle length: {len(cycle)}")
    print(f"  Fire counts: {fc}")
    print(f"  Displacement: {disp}")
    print(f"  Zero winding: {disp == 0}")
    print(f"  Max fc at binary: {max(fc[0], fc[1], fc[2])}")
    if disp == 0 and max(fc[0], fc[1], fc[2]) > 2:
        print("  *** FC > 2 WITH ZERO WINDING FOUND! ***")
    else:
        print("  CUP-2 does NOT have fc > 2 zero-winding cycle")

# Now check: at n=5, ms=[2,2,2,3,3], enumerate ALL systems and check
# The ternary functions have 3^18 ≈ 387M possibilities each — too many.
# Instead: just enumerate all binary triples (256^3 = 16M) with FIXED ternary tables
print("\nChecking with CUP-2 ternary tables, varying binary tables...")
ternary_tables = {3: tables[3], 4: tables[4]}

fc_gt2_count = 0
zero_winding_count = 0
total = 0

for bits_0 in iproduct([0, 1], repeat=8):
    f0 = {}
    for idx, (L, S, R) in enumerate(iproduct(range(2), repeat=3)):
        f0[(L, S, R)] = bits_0[idx]

    for bits_1 in iproduct([0, 1], repeat=8):
        f1 = {}
        for idx, (L, S, R) in enumerate(iproduct(range(2), repeat=3)):
            f1[(L, S, R)] = bits_1[idx]

        for bits_2 in iproduct([0, 1], repeat=8):
            f2 = {}
            for idx, (L, S, R) in enumerate(iproduct(range(2), repeat=3)):
                f2[(L, S, R)] = bits_2[idx]

            total += 1
            all_tables = {0: f0, 1: f1, 2: f2, 3: ternary_tables[3], 4: ternary_tables[4]}

            # Quick simulation from all-zeros
            config = (0, 0, 0, 0, 0)
            seen = {}
            for step in range(200):
                if config in seen:
                    cycle_start = seen[config]
                    cycle_len = step - cycle_start
                    # Count fire counts in the cycle
                    # Re-simulate to get the cycle
                    c = config
                    fc_local = [0] * 5
                    movers_local = []
                    for _ in range(cycle_len):
                        priv = []
                        for p in range(5):
                            L = c[(p-1) % 5]
                            S = c[p]
                            R = c[(p+1) % 5]
                            if all_tables[p][(L, S, R)] != S:
                                priv.append(p)
                        if not priv:
                            break
                        mover = priv[0]
                        fc_local[mover] += 1
                        movers_local.append(mover)
                        L = c[(mover-1) % 5]
                        S = c[mover]
                        R = c[(mover+1) % 5]
                        new_c = list(c)
                        new_c[mover] = all_tables[mover][(L, S, R)]
                        c = tuple(new_c)

                    # Check zero winding
                    disp = 0
                    for k in range(len(movers_local)):
                        curr = movers_local[k]
                        nxt = movers_local[(k+1) % len(movers_local)]
                        d = (nxt - curr) % 5
                        if d == 1: disp += 1
                        elif d == 4: disp -= 1

                    if disp == 0:
                        zero_winding_count += 1
                        if max(fc_local[0], fc_local[1], fc_local[2]) > 2:
                            fc_gt2_count += 1
                            if fc_gt2_count <= 3:
                                print(f"  FC>2 FOUND: binary tables {bits_0[:4]}..., {bits_1[:4]}..., {bits_2[:4]}...")
                                print(f"    Fire counts: {fc_local}, disp={disp}, cycle_len={cycle_len}")
                    break

                seen[config] = step
                priv = []
                for p in range(5):
                    L = config[(p-1) % 5]
                    S = config[p]
                    R = config[(p+1) % 5]
                    if all_tables[p][(L, S, R)] != S:
                        priv.append(p)
                if not priv:
                    break
                mover = priv[0]
                L = config[(mover-1) % 5]
                S = config[mover]
                R = config[(mover+1) % 5]
                new_config = list(config)
                new_config[mover] = all_tables[mover][(L, S, R)]
                config = tuple(new_config)

            if total % 500000 == 0:
                print(f"  Checked {total}/16777216, zero_winding={zero_winding_count}, fc_gt2={fc_gt2_count}")

print(f"\nTotal: {total}, zero_winding: {zero_winding_count}, fc_gt2: {fc_gt2_count}")
