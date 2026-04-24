#!/usr/bin/env python3
"""Check gap=1 implications for ALL zero-winding good cycles.

For each sub-threshold multiset with >= 3 binary at n=5,
enumerate ALL valid transition functions and good cycles.
For each zero-winding cycle, check:
1. Global min gap
2. If gap=1: does some binary proc have consecutive firings?
3. Can gap=1 even occur?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import all_configs, privileged_set, apply_move

def find_all_good_cycles(ms, fs):
    """Find all good cycles for a system."""
    n = len(ms)
    configs = list(all_configs(ms))
    single_priv = {c for c in configs if len(privileged_set(c, fs, ms)) == 1}

    # Build functional graph
    succ = {}
    mover_map = {}
    for c in single_priv:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            s = apply_move(c, priv[0], fs, ms)
            if s in single_priv:
                succ[c] = s
                mover_map[c] = priv[0]

    # Find all cycles
    visited_global = set()
    cycles = []
    for start in succ:
        if start in visited_global:
            continue
        path = []
        visited = set()
        c = start
        while c not in visited and c in succ:
            visited.add(c)
            path.append(c)
            c = succ[c]
        if c in visited:
            # Found cycle
            cycle_start_idx = path.index(c)
            cycle_configs = path[cycle_start_idx:]
            cycle = [(cfg, mover_map[cfg]) for cfg in cycle_configs]
            # Check it's a real cycle
            if len(cycle) >= 2 or (len(cycle) == 1 and succ[cycle[0][0]] == cycle[0][0]):
                cycles.append(cycle)
            visited_global.update(cycle_configs)
        visited_global.update(path)

    return cycles


def analyze_cycle_directions(cycle, n):
    """Get mover sequence and directions."""
    L = len(cycle)
    movers = [cycle[i][1] for i in range(L)]
    directions = []
    for i in range(L):
        m_now = movers[i]
        m_next = movers[(i+1) % L]
        if m_next == (m_now + 1) % n:
            directions.append('CW')
        elif m_next == (m_now - 1) % n:
            directions.append('CCW')
        else:
            directions.append('STAY')
    return movers, directions


def is_zero_winding(movers, directions, n, L):
    """Check zero winding."""
    for p in range(n):
        rp = (p + 1) % n
        cw = sum(1 for i in range(L) if movers[i] == p and directions[i] == 'CW')
        ccw = sum(1 for i in range(L) if movers[i] == rp and directions[i] == 'CCW')
        if cw != ccw:
            return False
    return True


def has_safe_proc(movers, n, L):
    """Check if there's a safe processor."""
    for q in range(n):
        lq = (q - 1) % n
        rq = (q + 1) % n
        if all(movers[i] != q and movers[i] != lq and movers[i] != rq for i in range(L)):
            return True
    return False


def global_min_gap(movers, directions, n, L):
    """Find global minimum gap across all edges."""
    min_gap = float('inf')
    for p in range(n):
        rp = (p + 1) % n
        crossings = []
        for i in range(L):
            if movers[i] == p and directions[i] == 'CW':
                crossings.append((i, 'CW'))
            elif movers[i] == rp and directions[i] == 'CCW':
                crossings.append((i, 'CCW'))

        for i1 in range(len(crossings)):
            for i2 in range(i1+1, len(crossings)):
                s1, d1 = crossings[i1]
                s2, d2 = crossings[i2]
                if d1 != d2:
                    has_between = any(s1 < crossings[i3][0] < s2 for i3 in range(len(crossings)))
                    if not has_between:
                        gap = s2 - s1
                        if gap < min_gap:
                            min_gap = gap
    return min_gap


def check_binary_consecutive(movers, binary_procs, L):
    """Check if any binary proc has consecutive firings."""
    for p in binary_procs:
        for i in range(L):
            if movers[i] == p and movers[(i+1) % L] == p:
                return True, p
    return False, None


def main():
    n = 5
    threshold = 4 * 3**(n-2)  # = 108

    print(f"n={n}, threshold={threshold}")
    print(f"Checking all sub-threshold multisets with >=3 binary\n")

    # All state vectors with product < 108, >= 3 binary, each state >= 2
    from itertools import product as cart
    max_s = 6  # states up to 6

    total_cycles_zw = 0
    gap1_cycles = 0
    gap1_no_consec = 0

    for ms_tuple in cart(*(range(2, max_s+1) for _ in range(n))):
        ms = list(ms_tuple)
        prod = 1
        for m in ms:
            prod *= m
        if prod >= threshold:
            continue
        binary_count = sum(1 for m in ms if m == 2)
        if binary_count < 3:
            continue

        binary_procs = [p for p in range(n) if ms[p] == 2]

        # Try building a system with incrementing transitions
        # f_i(L, S, R) = (S+1) % m_i if some condition
        # Actually, let's try ALL possible transition functions for small configs
        # For prod < 108, this is feasible

        # Generate all transition functions
        # Each processor i has m_{i-1} * m_i * m_{i+1} input tuples
        # Each maps to {0, ..., m_i - 1}

        # For prod < 108 and n=5, this is too many transition functions to enumerate
        # Let's just check a few specific systems

        # Try "copy left" system: f_i(L,S,R) = L % m_i
        fs_copy = [lambda L, S, R, m=ms[i]: L % m for i in range(n)]
        # Try "increment" system: f_i(L,S,R) = (S+1) % m_i
        fs_inc = [lambda L, S, R, m=ms[i]: (S+1) % m for i in range(n)]

        for fs in [fs_copy, fs_inc]:
            cycles = find_all_good_cycles(ms, fs)
            for cycle in cycles:
                L = len(cycle)
                if L < 2:
                    continue
                movers, dirs = analyze_cycle_directions(cycle, n)
                if not is_zero_winding(movers, dirs, n, L):
                    continue
                if has_safe_proc(movers, n, L):
                    continue
                cw_count = sum(1 for d in dirs if d == 'CW')
                if cw_count == 0:
                    continue

                total_cycles_zw += 1
                mg = global_min_gap(movers, dirs, n, L)
                if mg == 1:
                    gap1_cycles += 1
                    has_consec, proc = check_binary_consecutive(movers, binary_procs, L)
                    if not has_consec:
                        gap1_no_consec += 1
                        print(f"  GAP=1, NO CONSEC: ms={ms}, L={L}")
                        print(f"    movers={movers}")
                        print(f"    dirs={dirs}")

    print(f"\nSummary:")
    print(f"  Total zero-winding cycles (no safe, cw>0): {total_cycles_zw}")
    print(f"  Gap=1 cycles: {gap1_cycles}")
    print(f"  Gap=1 without binary consecutive: {gap1_no_consec}")


def main_exhaustive():
    """Exhaustively check ALL systems for small multisets."""
    n = 5

    # Focus on ms=[2,2,2,3,3] (product 72 < 108)
    # and ms=[2,2,2,2,3] (product 48 < 108)
    test_multisets = [
        [2,2,2,3,3],
        [2,2,2,2,3],
        [2,2,2,3,4],
    ]

    for ms in test_multisets:
        prod = 1
        for m in ms:
            prod *= m
        binary_procs = [p for p in range(n) if ms[p] == 2]
        print(f"\nms={ms}, prod={prod}, binary={binary_procs}")

        # Enumerate ALL transition functions
        # For ms=[2,2,2,3,3], total input space:
        # P0: m_L=ms[4]*ms[0]*ms[1] domain = 3*2*2=12 values, range {0,1}: 2^12 functions
        # P1: 2*2*2=8 values, range {0,1}: 2^8 functions
        # ...this is way too many

        # Instead, use the verifier to search for systems
        # Actually, let's just check some specific ones

        # The key question is really about good cycles.
        # For the LOWER BOUND, we need to show that for ANY system with ms < threshold,
        # every good cycle has an entry conflict.
        # The theorem gives: if there are 3 consecutive binary and zero winding + no safe + cw>0,
        # then there's an entry conflict.

        # So we need: in ANY good cycle satisfying these conditions,
        # if the global min gap is 1, derive False.

        # Let's instead check: does gap=1 at global min EVER occur
        # in zero-winding cycles? If not, gap=1 is impossible and the sorry is vacuously true.
        pass

    # Let's try a different approach: check if gap=1 is possible at all
    # in a zero-winding cycle with no safe processor
    print("\n\n=== Check: can gap=1 occur in zero-winding cycles? ===")
    print("Generating random good cycles via random transition functions...")

    import random
    random.seed(42)

    for ms in test_multisets:
        n = len(ms)
        prod = 1
        for m in ms:
            prod *= m
        binary_procs = [p for p in range(n) if ms[p] == 2]

        zw_count = 0
        gap1_count = 0

        for trial in range(10000):
            # Random transition functions
            fs = []
            for i in range(n):
                m_L = ms[(i-1) % n]
                m_S = ms[i]
                m_R = ms[(i+1) % n]
                table = {}
                for L in range(m_L):
                    for S in range(m_S):
                        for R in range(m_R):
                            table[(L, S, R)] = random.randint(0, m_S - 1)
                def f(L, S, R, t=table):
                    return t[(L, S, R)]
                fs.append(f)

            cycles = find_all_good_cycles(ms, fs)
            for cycle in cycles:
                L = len(cycle)
                if L < 3:
                    continue
                movers, dirs = analyze_cycle_directions(cycle, n)
                if not is_zero_winding(movers, dirs, n, L):
                    continue
                if has_safe_proc(movers, n, L):
                    continue
                cw_count = sum(1 for d in dirs if d == 'CW')
                if cw_count == 0:
                    continue

                zw_count += 1
                mg = global_min_gap(movers, dirs, n, L)
                if mg == 1:
                    gap1_count += 1
                    has_consec, proc = check_binary_consecutive(movers, binary_procs, L)
                    if not has_consec:
                        print(f"  FOUND: ms={ms}, L={L}, gap1, NO consec binary firings!")
                        print(f"    movers={movers}")
                        print(f"    dirs={dirs}")

        print(f"ms={ms}: {zw_count} zero-winding cycles, {gap1_count} with gap=1")


if __name__ == '__main__':
    main_exhaustive()
