"""
ra11_binary_ec_detail.py — Detailed analysis of EC at binary procs
in odd-winding non-uniform all-isolated cycles.

The binary proc p has ternary neighbors. The gap-parity mechanism
requires 3 consecutive binary, which we don't have.

So what produces EC at the binary proc?

Hypothesis: the EC is between a MOVER step for p and a NON-MOVER step
for p where the mover is a NEIGHBOR of p. When the mover is at
left(p) or right(p), the context at p includes the neighbor's
pre-move value. If the neighbor's pre-move value matches across
two such steps (one where p fires, one where p doesn't), we get EC.

This is NOT the gap-parity mechanism. It's a direct context match
that doesn't require knowing the parity structure of the ternary neighbor.
"""

import random
import itertools

random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def total_displacement(movers, n):
    W = 0
    L = len(movers)
    for i in range(L):
        diff = (movers[(i+1) % L] - movers[i]) % n
        if diff == 0: pass
        elif diff <= n // 2: W += diff
        else: W -= (n - diff)
    return W

def has_isolated_firings(movers, p):
    L = len(movers)
    for i in range(L):
        if movers[i] == p and movers[(i+1) % L] == p:
            return False
    return True

def fire_count(movers, n):
    fc = [0] * n
    for m in movers: fc[m] += 1
    return fc

def random_transition_fn(n, ms):
    trans_fn = {}
    for p in range(n):
        f = {}
        lp = left(p, n)
        rp = right(p, n)
        for L_val in range(ms[lp]):
            for S_val in range(ms[p]):
                for R_val in range(ms[rp]):
                    f[(L_val, S_val, R_val)] = random.choice(range(ms[p]))
        trans_fn[p] = f
    return trans_fn

def find_good_cycles(n, ms, trans_fn, max_cycles=50):
    cycles = []
    for trial in range(10000):
        config = tuple(random.randint(0, ms[p]-1) for p in range(n))
        visited = {config: 0}
        path_configs = [config]
        path_movers = []
        for step in range(200):
            mover = random.randint(0, n-1)
            L_val = config[left(mover, n)]
            S_val = config[mover]
            R_val = config[right(mover, n)]
            new_S = trans_fn[mover][(L_val, S_val, R_val)]
            if new_S == S_val:
                continue
            new_config = list(config)
            new_config[mover] = new_S
            new_config = tuple(new_config)
            path_movers.append(mover)
            path_configs.append(new_config)
            if new_config in visited:
                start = visited[new_config]
                cycle_configs = path_configs[start:-1]
                cycle_movers = path_movers[start:]
                if len(cycle_movers) >= 2:
                    cycles.append((cycle_configs, cycle_movers))
                if len(cycles) >= max_cycles:
                    return cycles
                break
            visited[new_config] = len(path_configs) - 1
            config = new_config
    return cycles


def main():
    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    binary = [0, 3, 6]

    print(f"n={n}, ms={ms}")
    print(f"Binary: {binary}")
    print()

    # For each EC at a binary proc, analyze:
    # 1. The gap(s) of the binary proc that contain the EC pair
    # 2. Whether the non-mover step is in the same gap as the mover step
    # 3. Whether the non-mover step is in a DIFFERENT gap

    same_gap_count = 0
    diff_gap_count = 0
    binary_ec_total = 0

    # Also check: at the non-mover step, what is the mover?
    nonmover_mover_dist = {}  # distance from p to the mover at the non-mover step

    # Check: does the EC happen because both S-parity and neighbor values match?
    # S-parity: binary p fires even times → value returns
    # Neighbor value: depends on neighbor's fire count (ternary → mod 3)

    for sys_trial in range(5000):
        trans_fn = random_transition_fn(n, ms)
        cycles = find_good_cycles(n, ms, trans_fn, max_cycles=10)

        for configs, movers in cycles:
            W = total_displacement(movers, n)
            if abs(W) != n: continue
            L = len(movers)
            dirs = []
            for i in range(L):
                diff = (movers[(i+1) % L] - movers[i]) % n
                if diff == 0: d = 0
                elif diff <= n // 2: d = 1
                else: d = -1
                dirs.append(d)
            non_stay = [d for d in dirs if d != 0]
            if not non_stay or all(d == non_stay[0] for d in non_stay): continue
            fc = fire_count(movers, n)
            all_iso = True
            for p in binary:
                if fc[p] < 2 or not has_isolated_firings(movers, p):
                    all_iso = False
                    break
            if not all_iso: continue

            # Find EC at binary procs
            for p in binary:
                lp = left(p, n)
                rp = right(p, n)
                mover_data = {}  # ctx -> [(step, config)]
                nonmover_data = {}

                for i, m in enumerate(movers):
                    ctx = (configs[i][lp], configs[i][p], configs[i][rp])
                    if m == p:
                        mover_data.setdefault(ctx, []).append(i)
                    else:
                        nonmover_data.setdefault(ctx, []).append(i)

                for ctx in mover_data:
                    if ctx not in nonmover_data: continue
                    binary_ec_total += 1

                    # Identify gaps for p
                    fire_steps = sorted([i for i, m in enumerate(movers) if m == p])
                    gaps = []
                    for fi in range(len(fire_steps)):
                        a = fire_steps[fi]
                        b = fire_steps[(fi+1) % len(fire_steps)]
                        if b > a:
                            gap_steps = list(range(a+1, b))
                        else:
                            gap_steps = list(range(a+1, L)) + list(range(0, b))
                        gaps.append((a, b, set(gap_steps)))

                    # For each mover step / non-mover step pair:
                    ms_step = mover_data[ctx][0]
                    nms_step = nonmover_data[ctx][0]

                    # Which gap contains the mover step?
                    mover_gap_idx = None
                    for gi, (a, b, gs) in enumerate(gaps):
                        if a == ms_step:
                            mover_gap_idx = gi
                            break

                    # Which gap contains the non-mover step?
                    nms_gap_idx = None
                    for gi, (a, b, gs) in enumerate(gaps):
                        if nms_step in gs:
                            nms_gap_idx = gi
                            break
                        if nms_step == a:
                            nms_gap_idx = gi
                            break

                    if mover_gap_idx is not None and nms_gap_idx is not None:
                        if mover_gap_idx == nms_gap_idx:
                            same_gap_count += 1
                        else:
                            diff_gap_count += 1

                    # Distance from p to the mover at the non-mover step
                    nms_mover = movers[nms_step]
                    dist = min((nms_mover - p) % n, (p - nms_mover) % n)
                    nonmover_mover_dist[dist] = nonmover_mover_dist.get(dist, 0) + 1

    print(f"Binary EC instances: {binary_ec_total}")
    print(f"  Same gap: {same_gap_count}")
    print(f"  Different gap: {diff_gap_count}")
    print()
    print("Distance from p to mover at non-mover step:")
    for dist in sorted(nonmover_mover_dist):
        print(f"  dist={dist}: {nonmover_mover_dist[dist]}")

    print()
    print("INTERPRETATION:")
    print("If most ECs have the non-mover step in the SAME gap as the mover step,")
    print("then the mechanism is: within one gap of p, both p's fire (start)")
    print("and some interior step have the same context.")
    print()
    print("If most ECs have the non-mover step in a DIFFERENT gap,")
    print("then the mechanism is: p's value returns after an even number of fires")
    print("and the ternary neighbors also return to the same value.")

    print()
    print("=== PARITY ANALYSIS ===")
    print()

    # For EC at binary p: does the S-value match because of binary parity?
    # At mover step: p is about to fire. config[p] = X.
    # At non-mover step: p doesn't fire. config[p] = X (same).
    # For binary p: value is 0 or 1. Value returns after even fires.
    # If mover step is fire #k and non-mover step is in gap after fire #m:
    # config[p] at non-mover step = initial + (fires before this step) mod 2
    # config[p] at mover step = initial + (fires before this step) mod 2
    # These match iff the number of fires of p before each step has the same parity.

    # For the ternary neighbors: value depends on the full fire history,
    # not just parity. But if the neighbor fires 0 times between the two steps,
    # the neighbor value is unchanged → match.

    # CHECK: at the EC pair (mover step, non-mover step), how many times
    # does each ternary neighbor fire between the two steps?

    ternary_fires_between = {'left': [], 'right': []}

    random.seed(42)
    for sys_trial in range(5000):
        trans_fn = random_transition_fn(n, ms)
        cycles = find_good_cycles(n, ms, trans_fn, max_cycles=10)

        for configs, movers in cycles:
            W = total_displacement(movers, n)
            if abs(W) != n: continue
            L = len(movers)
            dirs = []
            for i in range(L):
                diff = (movers[(i+1) % L] - movers[i]) % n
                if diff == 0: d = 0
                elif diff <= n // 2: d = 1
                else: d = -1
                dirs.append(d)
            non_stay = [d for d in dirs if d != 0]
            if not non_stay or all(d == non_stay[0] for d in non_stay): continue
            fc = fire_count(movers, n)
            all_iso = True
            for p in binary:
                if fc[p] < 2 or not has_isolated_firings(movers, p):
                    all_iso = False
                    break
            if not all_iso: continue

            for p in binary:
                lp = left(p, n)
                rp = right(p, n)
                mover_data = {}
                nonmover_data = {}
                for i, m in enumerate(movers):
                    ctx = (configs[i][lp], configs[i][p], configs[i][rp])
                    if m == p:
                        mover_data.setdefault(ctx, []).append(i)
                    else:
                        nonmover_data.setdefault(ctx, []).append(i)

                for ctx in mover_data:
                    if ctx not in nonmover_data: continue
                    ms_step = mover_data[ctx][0]
                    nms_step = nonmover_data[ctx][0]

                    # Count fires of left and right neighbor between the two steps
                    if ms_step < nms_step:
                        between = range(ms_step + 1, nms_step)
                    else:
                        between = list(range(ms_step + 1, L)) + list(range(0, nms_step))

                    lp_fires = sum(1 for s in between if movers[s] == lp)
                    rp_fires = sum(1 for s in between if movers[s] == rp)

                    ternary_fires_between['left'].append(lp_fires)
                    ternary_fires_between['right'].append(rp_fires)

    from collections import Counter
    print("Left neighbor fires between EC pair:")
    c = Counter(ternary_fires_between['left'])
    for k in sorted(c):
        print(f"  {k} fires: {c[k]}")

    print("Right neighbor fires between EC pair:")
    c = Counter(ternary_fires_between['right'])
    for k in sorted(c):
        print(f"  {k} fires: {c[k]}")

    print()
    print("KEY: If 0 fires is dominant for both neighbors,")
    print("the EC is produced by the ternary neighbor NOT firing between the pair.")
    print("This is the 'zero-fire gap' mechanism.")
    print()
    print("If non-zero fires with matching values:")
    print("The ternary transition function maps to the same output from the same input,")
    print("which is automatic (deterministic transitions).")


if __name__ == "__main__":
    main()
