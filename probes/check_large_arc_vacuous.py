#!/usr/bin/env python3
"""Check whether the large_arc_zeroWinding_ec axiom case is vacuous.

For sub-threshold systems (product < 4*3^(n-2)), does any valid system have
a good cycle that is:
  (1) zero winding
  (2) cwStepCount > 0
  (3) no safe processor (every proc within distance 1 of some mover)

We check CUP-2 systems for n=5..10, plus all sub-threshold multisets at n=5,6,7.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system, privileged_set, apply_move
from cup2_theorem import build_system, T_bot, T_low, T_mid, T_high, T_top


def extract_good_cycle(ms, fs):
    """Extract the good cycle: list of (config, mover, direction)."""
    n = len(ms)
    result = verify_system(ms, fs)
    if not result['valid']:
        return None, None
    good_set = result['good_configs']

    # Build successor map
    succ = {}
    for c in good_set:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            s = apply_move(c, priv[0], fs, ms)
            succ[c] = (s, priv[0])

    # Find cycle
    start = next(iter(good_set))
    visited = {}
    node = start
    step = 0
    while node not in visited:
        visited[node] = step
        if node not in succ:
            break
        node = succ[node][0]
        step += 1

    if node not in visited:
        return None, None

    cycle_start_step = visited[node]
    cycle = []
    cur = node
    while True:
        nxt, mover = succ[cur]
        cycle.append((cur, mover))
        cur = nxt
        if cur == node:
            break

    return cycle, good_set


def step_direction(config_now, config_next, mover_now, n):
    """Determine step direction: cw, ccw, or stay.

    CW: moverAt(next) = right(moverAt(now)) = (mover_now + 1) % n
    CCW: moverAt(next) = left(moverAt(now)) = (mover_now - 1) % n
    Stay: moverAt(next) = moverAt(now)
    """
    # We need the mover at the NEXT step
    # The next config's mover is determined by who is privileged there
    # But we have the cycle, so we know the next mover from the cycle data
    return None  # We'll compute differently


def analyze_cycle(cycle, ms, fs):
    """Analyze a good cycle for the axiom's hypotheses."""
    n = len(ms)
    L = len(cycle)

    # Extract movers
    movers = [m for (c, m) in cycle]

    # Compute step directions
    # stepDir(k) compares moverAt(k) with moverAt(nextIndex(k))
    # CW: mover moves right, CCW: mover moves left, Stay: mover stays
    cw_count = 0
    ccw_count = 0
    stay_count = 0
    for k in range(L):
        mover_k = movers[k]
        mover_next = movers[(k + 1) % L]
        right_k = (mover_k + 1) % n
        left_k = (mover_k - 1) % n
        if mover_next == right_k:
            cw_count += 1
        elif mover_next == left_k:
            ccw_count += 1
        else:
            stay_count += 1

    # Total displacement (winding number * n)
    # totalDisplacement = sum of step displacements
    # CW step contributes +1, CCW contributes -1, stay contributes 0
    total_disp = cw_count - ccw_count

    zero_winding = (total_disp == 0)

    # Check safe processor: q such that mover never equals q, left(q), or right(q)
    mover_set = set(movers)
    safe_proc = None
    for q in range(n):
        left_q = (q - 1) % n
        right_q = (q + 1) % n
        # Check: for ALL steps k, mover[k] != q AND mover[k] != left_q AND mover[k] != right_q
        is_safe = True
        for m in movers:
            if m == q or m == left_q or m == right_q:
                is_safe = False
                break
        if is_safe:
            safe_proc = q
            break

    has_safe = safe_proc is not None

    return {
        'length': L,
        'cw_count': cw_count,
        'ccw_count': ccw_count,
        'stay_count': stay_count,
        'total_disp': total_disp,
        'zero_winding': zero_winding,
        'has_safe': has_safe,
        'safe_proc': safe_proc,
        'mover_set': mover_set,
        'movers': movers,
    }


def check_system(ms, fs, label=""):
    """Check if a system triggers the axiom case."""
    cycle, good_set = extract_good_cycle(ms, fs)
    if cycle is None:
        return None

    info = analyze_cycle(cycle, ms, fs)

    triggers = (info['zero_winding'] and
                info['cw_count'] > 0 and
                not info['has_safe'])

    if triggers or True:  # Always print for debugging
        status = "TRIGGERS AXIOM" if triggers else "does NOT trigger"
        print(f"  {label}: L={info['length']}, CW={info['cw_count']}, "
              f"CCW={info['ccw_count']}, Stay={info['stay_count']}, "
              f"disp={info['total_disp']}, zeroW={info['zero_winding']}, "
              f"safe={info['safe_proc']}, movers={sorted(info['mover_set'])} "
              f"=> {status}")

    return triggers


def main():
    print("=" * 90)
    print("CHECK: Is large_arc_zeroWinding_ec vacuous?")
    print("=" * 90)

    # Part 1: CUP-2 systems
    print("\n--- CUP-2 systems (ms = (2,3,...,3,2)) ---")
    any_trigger = False
    for n in range(5, 11):
        ms, fs = build_system(n)
        result = check_system(ms, fs, f"CUP-2 n={n}")
        if result:
            any_trigger = True

    if not any_trigger:
        print("  => CUP-2 NEVER triggers the axiom case (all n=5..10)")

    # Part 2: Sol3 v1 systems (ms = (2,3,...,3))
    print("\n--- Sol3 v1 systems (ms = (2,3,...,3)) ---")
    # Build Sol3 v1 system for small n
    # Sol3 v1: ms=(2,3,...,3), product=2*3^(n-1)
    # This is ABOVE sub-threshold (4*3^(n-2)) for n >= 5 since 2*3^(n-1) = 6*3^(n-2) > 4*3^(n-2)
    # So Sol3 v1 is NOT sub-threshold. Skip.
    print("  Sol3 v1 has product 2*3^(n-1) > 4*3^(n-2) => NOT sub-threshold, skip.")

    # Part 3: Exhaustive at n=5
    print("\n--- All valid sub-threshold systems at n=5 (product < 108 = 4*3^3) ---")
    # Sub-threshold means product < 4*3^(n-2)
    # For n=5: product < 4*3^3 = 108
    # The minimum product system is ms=(2,2,2,3,4) with product=96
    # Need to enumerate all multisets with product < 108

    threshold_5 = 4 * 3**3  # 108
    # Enumerate all state vectors with product < 108
    # Each m_i >= 2, product < 108
    # Max possible m_i = 107/2 ~ 53, but practically small
    from itertools import product as cart

    found_valid = 0
    found_trigger = 0

    # Generate all ms with n=5, each m_i >= 2, product < 108
    # Brute force: m_i in [2, ..., 53]
    max_m = threshold_5 // 2  # 54
    for m0 in range(2, max_m + 1):
        if m0 >= threshold_5:
            break
        for m1 in range(2, max_m + 1):
            if m0 * m1 >= threshold_5:
                break
            for m2 in range(2, max_m + 1):
                if m0 * m1 * m2 >= threshold_5:
                    break
                for m3 in range(2, max_m + 1):
                    if m0 * m1 * m2 * m3 >= threshold_5:
                        break
                    for m4 in range(2, max_m + 1):
                        prod = m0 * m1 * m2 * m3 * m4
                        if prod >= threshold_5:
                            break
                        # This ms has product < threshold
                        # But we need to check ALL orientations (rotations)
                        # Actually, the ms is an ordered tuple (ring), so we check it as-is
                        # But to find valid systems we need transition functions
                        # This is COMBINATORIALLY HUGE - skip exhaustive for n=5
                        pass

    print("  Exhaustive search over all transition functions is infeasible.")
    print("  Instead, check: the CUP-2 axiom case analysis.")

    # Part 4: Deep analysis of CUP-2 cycle structure
    print("\n--- Detailed CUP-2 cycle analysis ---")
    for n in range(5, 11):
        ms, fs = build_system(n)
        cycle, good_set = extract_good_cycle(ms, fs)
        if cycle is None:
            continue
        info = analyze_cycle(cycle, ms, fs)

        # Count how many binary processors exist
        n_binary = sum(1 for i in range(n) if ms[i] == 2)

        # Check which case the cycle falls into
        if info['total_disp'] != 0:
            case = "NON-ZERO WINDING"
        elif info['cw_count'] == 0:
            case = "ALL-STAY"
        elif info['has_safe']:
            case = "SAFE-PROCESSOR"
        else:
            case = "LARGE-ARC (axiom case!)"

        print(f"  n={n}: binary={n_binary}, case={case}, "
              f"disp={info['total_disp']}, CW={info['cw_count']}, "
              f"movers={sorted(info['mover_set'])}")

    # Part 5: Check what happens with ALL sub-threshold product multisets for CUP-2 style
    # The key question: for ms=(2,3,...,3,2), is the cycle ALWAYS non-zero-winding?
    print("\n--- Winding analysis for CUP-2 ---")
    print("  CUP-2 cycle has displacement = cw - ccw.")
    print("  If displacement != 0, the cycle is non-zero-winding and the axiom case")
    print("  is NOT reached (it goes to nonZeroWinding_shadow instead).")
    print("  If displacement == 0 but cw == 0, it's all-stay case (handled by proved thm).")
    print("  If displacement == 0 and cw > 0 and has safe proc, small-arc case (handled).")
    print("  The axiom case requires: displacement == 0 AND cw > 0 AND no safe proc.")

    # Final check: for CUP-2 specifically, what is the displacement?
    print("\n--- CUP-2 displacement values ---")
    for n in range(4, 14):
        ms, fs = build_system(n)
        cycle, good_set = extract_good_cycle(ms, fs)
        if cycle is None:
            print(f"  n={n}: no valid system")
            continue
        info = analyze_cycle(cycle, ms, fs)
        print(f"  n={n}: L={info['length']}, disp={info['total_disp']}, "
              f"CW={info['cw_count']}, CCW={info['ccw_count']}")

    print("\n" + "=" * 90)
    print("CONCLUSION")
    print("=" * 90)


if __name__ == "__main__":
    main()
