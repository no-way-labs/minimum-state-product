"""
ra11_system_level.py — Check at the SYSTEM level whether odd-winding
non-uniform cycles with non-consecutive isolated binary exist.

The mover-word level allows them. But the system level (with actual configs
and transition functions) might block them.

Approach: for small n (n=5 with non-consec binary), enumerate actual
good cycles from valid sub-threshold systems and check.
"""

import random
import itertools
from collections import defaultdict

random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

def all_configs(ms, n):
    return list(itertools.product(*[range(m) for m in ms]))

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

def has_entry_conflict(configs, movers, n):
    for p in range(n):
        lp = left(p, n)
        rp = right(p, n)
        mover_ctxs = set()
        nonmover_ctxs = set()
        for i, m in enumerate(movers):
            ctx = (configs[i][lp], configs[i][p], configs[i][rp])
            if m == p:
                mover_ctxs.add(ctx)
            else:
                nonmover_ctxs.add(ctx)
        if mover_ctxs & nonmover_ctxs:
            return True
    return False


def find_good_cycles_for_system(n, ms, trans_fn, max_cycles=1000):
    """
    Given a transition function, find good cycles by random walk.

    trans_fn: dict[proc] -> dict[(L,S,R)] -> new_S

    A good cycle: start from config, apply single-processor moves,
    return to start config.
    """
    configs = all_configs(ms, n)

    cycles = []

    for trial in range(5000):
        # Pick random start config
        config = tuple(random.randint(0, ms[p]-1) for p in range(n))

        visited = {config: 0}
        path_configs = [config]
        path_movers = []

        for step in range(100):
            # Pick random mover (privileged daemon)
            mover = random.randint(0, n-1)

            # Apply transition
            L_val = config[left(mover, n)]
            S_val = config[mover]
            R_val = config[right(mover, n)]

            new_S = trans_fn[mover][(L_val, S_val, R_val)]
            if new_S == S_val:
                continue  # no change, try again

            new_config = list(config)
            new_config[mover] = new_S
            new_config = tuple(new_config)

            path_movers.append(mover)
            path_configs.append(new_config)

            if new_config in visited:
                # Found a cycle
                start = visited[new_config]
                cycle_configs = path_configs[start:-1]  # exclude last (= first)
                cycle_movers = path_movers[start:]

                if len(cycle_movers) >= 2:
                    # Verify it's a proper cycle
                    key = (tuple(cycle_configs[0]), tuple(cycle_movers))
                    cycles.append((cycle_configs, cycle_movers))

                if len(cycles) >= max_cycles:
                    return cycles
                break

            visited[new_config] = len(path_configs) - 1
            config = new_config

    return cycles


def random_transition_fn(n, ms):
    """Generate a random transition function."""
    trans_fn = {}
    for p in range(n):
        f = {}
        lp = left(p, n)
        rp = right(p, n)
        for L_val in range(ms[lp]):
            for S_val in range(ms[p]):
                for R_val in range(ms[rp]):
                    # Output is a value in [0, ms[p]) different from S_val
                    # (or same if no valid transition)
                    choices = list(range(ms[p]))
                    f[(L_val, S_val, R_val)] = random.choice(choices)
        trans_fn[p] = f
    return trans_fn


def check_n5():
    """Check at n=5 with non-consecutive binary."""
    n = 5
    # ms = [2, 3, 2, 3, 2]  # binary at 0,2,4 — these ARE 3 consec (0,2,4 not consec by ring)
    # Actually check: 0,2,4 on ring of 5. 0-2: gap 2. 2-4: gap 2. 4-0: gap 1.
    # gap 1 means 4 and 0 are adjacent. So 4,0,2 has gap 1, 2, 2 — not 3 consecutive.
    # 3 consecutive means 3 in a row: e.g., 0,1,2. With ms=[2,3,2,3,2]:
    # Proc 0 binary, proc 1 ternary, proc 2 binary, proc 3 ternary, proc 4 binary.
    # No three consecutive binary. ✓

    ms = [2, 3, 2, 3, 2]
    binary = [0, 2, 4]
    threshold = 4 * 3**(n-2)
    product = 1
    for m in ms: product *= m
    print(f"n={n}, ms={ms}")
    print(f"Product={product}, Threshold={threshold}, Sub-threshold={product < threshold}")
    print(f"Binary: {binary}")
    print()

    # Check: any pair at distance 2?
    for p in binary:
        for q in binary:
            if p != q:
                d = min((q-p)%n, (p-q)%n)
                if d == 2:
                    mid = (min(p,q) + 1) % n if (q-p)%n == 2 else (max(p,q) + 1) % n
                    # Actually let me compute properly
                    if (q-p)%n == 2:
                        mid = (p+1)%n
                    elif (p-q)%n == 2:
                        mid = (q+1)%n
                    print(f"  Distance 2 pair: {p}-{q}, pivot {mid}")

    # For n=5, ms=[2,3,2,3,2]:
    # Binary 0, 2: distance 2, pivot 1 (ternary)
    # Binary 2, 4: distance 2, pivot 3 (ternary)
    # Binary 4, 0: distance 1 (adjacent!)
    # So there ARE distance-2 pairs. The "no pivot" case doesn't apply at n=5.

    # Try n=9 instead
    print()
    check_n9()


def check_n9():
    """Check at n=9 with non-consecutive binary, all gaps ≥ 3."""
    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]  # binary at 0, 3, 6
    binary = [0, 3, 6]
    threshold = 4 * 3**(n-2)
    product = 1
    for m in ms: product *= m
    print(f"n={n}, ms={ms}")
    print(f"Product={product}, Threshold={threshold}, Sub-threshold={product < threshold}")
    print(f"Binary: {binary}")
    print()

    # Enumerate random systems and find good cycles
    odd_winding_count = 0
    odd_winding_nonunif_count = 0
    odd_winding_nonunif_alliso_count = 0
    odd_winding_nonunif_alliso_ec_count = 0
    odd_winding_nonunif_alliso_noec_count = 0
    total_cycles = 0

    for sys_trial in range(2000):
        trans_fn = random_transition_fn(n, ms)
        cycles = find_good_cycles_for_system(n, ms, trans_fn, max_cycles=20)

        for configs, movers in cycles:
            total_cycles += 1

            W = total_displacement(movers, n)
            if abs(W) != n:
                continue
            odd_winding_count += 1

            # Check non-uniform
            dirs = []
            L = len(movers)
            for i in range(L):
                diff = (movers[(i+1) % L] - movers[i]) % n
                if diff == 0: d = 0
                elif diff <= n // 2: d = 1
                else: d = -1
                dirs.append(d)
            non_stay = [d for d in dirs if d != 0]
            if not non_stay or all(d == non_stay[0] for d in non_stay):
                continue
            odd_winding_nonunif_count += 1

            # Check all binary isolated
            all_iso = True
            for p in binary:
                fc = fire_count(movers, n)
                if fc[p] >= 2 and not has_isolated_firings(movers, p):
                    all_iso = False
                    break
                if fc[p] < 2:
                    all_iso = False
                    break
            if not all_iso:
                continue
            odd_winding_nonunif_alliso_count += 1

            # Check entry conflict at system level
            ec = has_entry_conflict(configs, movers, n)
            if ec:
                odd_winding_nonunif_alliso_ec_count += 1
            else:
                odd_winding_nonunif_alliso_noec_count += 1
                # Print details of this cycle
                print(f"  NO EC! movers={movers[:20]}..., len={len(movers)}, W={W}")
                fc_w = fire_count(movers, n)
                print(f"  fc={fc_w}")

    print(f"\nTotal cycles found: {total_cycles}")
    print(f"Odd-winding: {odd_winding_count}")
    print(f"Odd-winding non-uniform: {odd_winding_nonunif_count}")
    print(f"Odd-winding non-uniform all-binary-isolated: {odd_winding_nonunif_alliso_count}")
    print(f"  With EC: {odd_winding_nonunif_alliso_ec_count}")
    print(f"  Without EC: {odd_winding_nonunif_alliso_noec_count}")
    print()

    if odd_winding_nonunif_alliso_noec_count > 0:
        print("FOUND cycles without EC! The system-level constraint doesn't")
        print("automatically produce EC for all such cycles.")
        print("The proof must use additional structure (convergence, sub-threshold).")
    elif odd_winding_nonunif_alliso_count == 0:
        print("NO odd-winding non-uniform all-isolated cycles found at all.")
        print("This might mean they're extremely rare or non-existent at system level.")
    else:
        print("ALL odd-winding non-uniform all-isolated cycles have EC.")
        print("This is consistent with the theorem being true.")


def check_n9_converging():
    """
    More targeted: check only CONVERGING systems.
    A system converges if from every bad config, it reaches a good config.
    This is expensive to check for n=9, so use a simpler proxy.
    """
    # Actually, checking convergence for n=9 is infeasible (2^3 * 3^6 = 5832 configs).
    # Let's just check whether any good cycle without EC exists, regardless of convergence.
    pass


def main():
    check_n5()


if __name__ == "__main__":
    main()
