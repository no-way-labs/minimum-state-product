"""
ra5_real_systems.py — Test the 3-Arc Obstruction Lemma on REAL self-stabilizing systems.

The key difference: in a real SS system, the good cycle visits ALL good configs
and each step is determined by the transition function. The cycle structure is
highly constrained.

For real systems: the good cycle is the unique cycle through all good configs.
Each config has exactly one privileged processor (mutual exclusion), and that
processor fires deterministically.

This means:
1. The mover at each step is DETERMINED (the unique privileged proc in that config).
2. The cycle length = number of good configs.
3. The walk structure is completely determined by the transition functions.
"""

import sys
sys.path.insert(0, './claude')

import random
from collections import defaultdict
from itertools import product as iproduct


def ring_dist(a, b, n):
    d = abs(a - b)
    return min(d, n - d)


def find_good_cycle(ms, fs):
    """Find the good cycle of a self-stabilizing system."""
    n = len(ms)

    # Generate all configs
    all_cfgs = list(iproduct(*(range(m) for m in ms)))

    # For each config, find privileged processors
    priv_map = {}
    for c in all_cfgs:
        priv = []
        for i in range(n):
            L = c[(i-1) % n]
            S = c[i]
            R = c[(i+1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        priv_map[c] = priv

    # Good configs: exactly one privileged processor
    good_cfgs = set(c for c in all_cfgs if len(priv_map[c]) == 1)
    if not good_cfgs:
        return None

    # Follow the cycle from any good config
    start = next(iter(good_cfgs))
    path = [start]
    movers = []
    current = start

    while True:
        priv = priv_map[current]
        if len(priv) != 1:
            return None  # Not a valid SS system
        mover = priv[0]
        movers.append(mover)

        L = current[(mover-1) % n]
        S = current[mover]
        R = current[(mover+1) % n]
        new_S = fs[mover](L, S, R)

        new_config = list(current)
        new_config[mover] = new_S
        current = tuple(new_config)

        if current == start:
            break
        if current not in good_cfgs:
            return None  # Closure violation
        path.append(current)

    return path, movers


def make_sol3v1_system(n):
    """Construct Sol 3 v1 system: ms = (2, 3, 3, ..., 3)."""
    ms = [2] + [3]*(n-1)

    def f0(L, S, R):
        # Binary proc: toggle if L == S
        if L == S:
            return 1 - S
        return S

    def fi(L, S, R):
        # Ternary proc: increment if L != S
        if L != S:
            return (S + 1) % 3
        return S

    fs = [f0] + [fi]*(n-1)
    return ms, fs


def make_cup2_system(n):
    """Construct CUP-2 system: ms = (2, 3, 3, ..., 3, 2)."""
    ms = [2] + [3]*(n-2) + [2]

    # CUP-2 transition tables (from cup2_theorem.py)
    # T_low[i=0]: binary endpoint
    T_low = {
        (0, 0, 0): 0, (0, 0, 1): 0, (0, 0, 2): 0,
        (1, 0, 0): 1, (1, 0, 1): 1, (1, 0, 2): 1,
        (0, 1, 0): 0, (0, 1, 1): 0, (0, 1, 2): 0,
        (1, 1, 0): 1, (1, 1, 1): 1, (1, 1, 2): 1,
    }

    T_high = {
        (0, 0, 0): 0, (0, 0, 1): 0,
        (1, 0, 0): 1, (1, 0, 1): 1,
        (2, 0, 0): 0, (2, 0, 1): 0,
        (0, 1, 0): 0, (0, 1, 1): 0,
        (1, 1, 0): 1, (1, 1, 1): 1,
        (2, 1, 0): 0, (2, 1, 1): 1,
    }

    T_mid = {
        (0, 0, 0): 2, (0, 0, 1): 2, (0, 0, 2): 0,
        (1, 0, 0): 2, (1, 0, 1): 2, (1, 0, 2): 0,
        (2, 0, 0): 2, (2, 0, 1): 2, (2, 0, 2): 2,
        (0, 1, 0): 2, (0, 1, 1): 0, (0, 1, 2): 1,
        (1, 1, 0): 1, (1, 1, 1): 0, (1, 1, 2): 1,
        (2, 1, 0): 0, (2, 1, 1): 0, (2, 1, 2): 1,
        (0, 2, 0): 2, (0, 2, 1): 0, (0, 2, 2): 2,
        (1, 2, 0): 1, (1, 2, 1): 0, (1, 2, 2): 2,
        (2, 2, 0): 0, (2, 2, 1): 0, (2, 2, 2): 2,
    }

    T_mid_low = {
        (0, 0, 0): 2, (0, 0, 1): 2, (0, 0, 2): 0,
        (1, 0, 0): 2, (1, 0, 1): 2, (1, 0, 2): 0,
        (0, 1, 0): 2, (0, 1, 1): 0, (0, 1, 2): 1,
        (1, 1, 0): 1, (1, 1, 1): 0, (1, 1, 2): 1,
        (0, 2, 0): 2, (0, 2, 1): 0, (0, 2, 2): 2,
        (1, 2, 0): 1, (1, 2, 1): 0, (1, 2, 2): 2,
    }

    T_mid_high = {
        (0, 0, 0): 2, (0, 0, 1): 2,
        (1, 0, 0): 2, (1, 0, 1): 2,
        (2, 0, 0): 2, (2, 0, 1): 2,
        (0, 1, 0): 2, (0, 1, 1): 0,
        (1, 1, 0): 1, (1, 1, 1): 0,
        (2, 1, 0): 0, (2, 1, 1): 0,
        (0, 2, 0): 2, (0, 2, 1): 0,
        (1, 2, 0): 1, (1, 2, 1): 0,
        (2, 2, 0): 0, (2, 2, 1): 0,
    }

    def make_f(table):
        def f(L, S, R):
            return table.get((L, S, R), S)
        return f

    fs = []
    fs.append(make_f(T_low))     # proc 0 (binary)
    fs.append(make_f(T_mid_low)) # proc 1 (ternary, next to binary)
    for i in range(2, n-2):
        fs.append(make_f(T_mid))  # interior ternary procs
    fs.append(make_f(T_mid_high)) # proc n-2 (ternary, next to binary)
    fs.append(make_f(T_high))    # proc n-1 (binary)

    return ms, fs


def check_ec_in_3arc(path, movers, arc, n):
    """Check for EC at any of the 3 arc processors."""
    CL = len(movers)
    for q in arc:
        left = (q - 1) % n
        right = (q + 1) % n

        mt = {}
        nmt = {}
        for k in range(CL):
            triple = (path[k][left], path[k][q], path[k][right])
            if movers[k] == q:
                if triple not in mt:
                    mt[triple] = k
            else:
                if triple not in nmt:
                    nmt[triple] = k

        for t in mt:
            if t in nmt:
                return True, q, mt[t], nmt[t], t
    return False, None, None, None, None


def test_sol3v1():
    """Test on Sol 3 v1 systems."""
    print("=== Sol 3 v1 Systems ===")

    for n in range(5, 13):
        ms, fs = make_sol3v1_system(n)
        result = find_good_cycle(ms, fs)
        if result is None:
            print(f"n={n}: Failed to find good cycle")
            continue

        path, movers = result
        CL = len(movers)

        # Check ring-adjacency
        ra_ok = all(ring_dist(movers[i], movers[(i+1)%CL], n) <= 1 for i in range(CL))

        fire_counts = defaultdict(int)
        for m in movers:
            fire_counts[m] += 1

        print(f"n={n}: CL={CL}, ring-adjacent={ra_ok}, procs firing={len(set(movers))}")

        if not ra_ok:
            print(f"  NOT ring-adjacent — skip")
            continue

        # Check all 3-arcs
        total = 0
        ec_found = 0
        for p in range(n):
            arc = [p, (p+1)%n, (p+2)%n]
            if not all(fire_counts[q] > 0 for q in arc):
                continue
            total += 1
            found, q, k_m, k_nm, t = check_ec_in_3arc(path, movers, arc, n)
            if found:
                ec_found += 1

        print(f"  3-arcs: {total}, EC found: {ec_found}, "
              f"rate: {ec_found/total:.4f}" if total > 0 else "  No valid 3-arcs")


def test_cup2():
    """Test on CUP-2 systems."""
    print("\n=== CUP-2 Systems ===")

    for n in range(5, 10):
        ms, fs = make_cup2_system(n)
        result = find_good_cycle(ms, fs)
        if result is None:
            print(f"n={n}: Failed to find good cycle")
            continue

        path, movers = result
        CL = len(movers)

        ra_ok = all(ring_dist(movers[i], movers[(i+1)%CL], n) <= 1 for i in range(CL))

        fire_counts = defaultdict(int)
        for m in movers:
            fire_counts[m] += 1

        print(f"n={n}: CL={CL}, ring-adjacent={ra_ok}, procs firing={len(set(movers))}")
        print(f"  fire_counts: {dict(fire_counts)}")

        if not ra_ok:
            # Show violations
            violations = 0
            for i in range(CL):
                j = (i+1) % CL
                d = ring_dist(movers[i], movers[j], n)
                if d > 1:
                    violations += 1
                    if violations <= 3:
                        print(f"  Violation: step {i}→{j}: mover {movers[i]}→{movers[j]}, dist={d}")
            print(f"  Total violations: {violations}")
            print(f"  Skipping (not ring-adjacent)")
            continue

        total = 0
        ec_found = 0
        for p in range(n):
            arc = [p, (p+1)%n, (p+2)%n]
            if not all(fire_counts[q] > 0 for q in arc):
                continue
            total += 1
            found, q, k_m, k_nm, t = check_ec_in_3arc(path, movers, arc, n)
            if found:
                ec_found += 1
            else:
                print(f"  NO EC: arc={arc}, fc=({fire_counts[arc[0]]},{fire_counts[arc[1]]},{fire_counts[arc[2]]})")

        print(f"  3-arcs: {total}, EC found: {ec_found}, "
              f"rate: {ec_found/total:.4f}" if total > 0 else "  No valid 3-arcs")


def test_random_verified_systems():
    """
    Generate random transition functions, verify they form SS systems,
    then check the 3-arc obstruction on their good cycles.
    """
    print("\n=== Random Verified SS Systems ===")

    random.seed(42)
    total_arcs = 0
    total_ec = 0
    total_systems = 0

    for n in [5, 6, 7]:
        for ms in [[2]*n, [3]*n, [2,3,3,3,3][:n] + [3]*(n-5) if n > 5 else [2,3,3,3,3][:n]]:
            if len(ms) != n:
                ms = ms[:n]
            if len(ms) < n:
                ms = ms + [3]*(n - len(ms))

            systems_found = 0
            for trial in range(5000):
                # Random transition functions
                fs = []
                for i in range(n):
                    table = {}
                    for L in range(ms[(i-1)%n]):
                        for S in range(ms[i]):
                            for R in range(ms[(i+1)%n]):
                                table[(L, S, R)] = random.randint(0, ms[i]-1)
                    def make_f(t):
                        def f(L, S, R):
                            return t[(L, S, R)]
                        return f
                    fs.append(make_f(table))

                # Check if it's a valid SS system
                all_cfgs = list(iproduct(*(range(m) for m in ms)))

                # Check liveness (every config has at least 1 privileged proc)
                # Check mutual exclusion for good configs
                good = set()
                bad = set()
                live = True
                for c in all_cfgs:
                    priv = []
                    for i in range(n):
                        L = c[(i-1)%n]
                        S = c[i]
                        R = c[(i+1)%n]
                        if fs[i](L, S, R) != S:
                            priv.append(i)
                    if len(priv) == 0:
                        live = False
                        break
                    if len(priv) == 1:
                        good.add(c)
                    else:
                        bad.add(c)

                if not live or len(good) == 0:
                    continue

                # Check closure
                closure_ok = True
                for c in good:
                    priv = []
                    for i in range(n):
                        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
                        if fs[i](L, S, R) != S:
                            priv.append(i)
                    assert len(priv) == 1
                    mover = priv[0]
                    L = c[(mover-1)%n]; S = c[mover]; R = c[(mover+1)%n]
                    new_S = fs[mover](L, S, R)
                    nc = list(c); nc[mover] = new_S; nc = tuple(nc)
                    if nc not in good:
                        closure_ok = False
                        break

                if not closure_ok:
                    continue

                # Find good cycle
                start = next(iter(good))
                path = [start]
                movers = []
                current = start
                seen = {start}
                cycle_ok = True
                while True:
                    priv = []
                    for i in range(n):
                        L = current[(i-1)%n]; S = current[i]; R = current[(i+1)%n]
                        if fs[i](L, S, R) != S:
                            priv.append(i)
                    if len(priv) != 1:
                        cycle_ok = False
                        break
                    mover = priv[0]
                    movers.append(mover)
                    L = current[(mover-1)%n]; S = current[mover]; R = current[(mover+1)%n]
                    new_S = fs[mover](L, S, R)
                    nc = list(current); nc[mover] = new_S; current = tuple(nc)
                    if current == start:
                        break
                    if current in seen:
                        cycle_ok = False
                        break
                    seen.add(current)
                    path.append(current)

                if not cycle_ok or len(movers) != len(good):
                    continue

                CL = len(movers)

                # Check ring-adjacency
                ra_ok = all(ring_dist(movers[i], movers[(i+1)%CL], n) <= 1 for i in range(CL))
                if not ra_ok:
                    continue

                systems_found += 1
                total_systems += 1

                fire_counts = defaultdict(int)
                for m in movers:
                    fire_counts[m] += 1

                for p in range(n):
                    arc = [p, (p+1)%n, (p+2)%n]
                    if not all(fire_counts[q] > 0 for q in arc):
                        continue
                    total_arcs += 1
                    found, q, k_m, k_nm, t = check_ec_in_3arc(path, movers, arc, n)
                    if found:
                        total_ec += 1
                    else:
                        print(f"  NO EC: n={n}, ms={ms}, CL={CL}, arc={arc}")
                        arc_fc = tuple(fire_counts[q] for q in arc)
                        print(f"    arc fire counts: {arc_fc}")

            print(f"n={n}, ms={ms}: {systems_found} RA systems found")

    print(f"\nTotal RA SS systems: {total_systems}")
    print(f"Total 3-arcs: {total_arcs}")
    print(f"EC found: {total_ec}")
    if total_arcs > 0:
        print(f"EC rate: {total_ec/total_arcs:.6f}")


if __name__ == "__main__":
    test_sol3v1()
    test_cup2()
    test_random_verified_systems()
