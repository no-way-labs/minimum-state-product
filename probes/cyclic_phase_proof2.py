"""
Cyclic Phase Decomposition — Proof Design + Computational Verification

Uses the correct self-stabilizing model from verifier.py.
Tests rotation-based approach (Approach C) on real good cycles.
"""
import sys
sys.path.insert(0, './claude')

from itertools import product as iprod

# ============================================================================
# Core model (matches verifier.py)
# ============================================================================

def all_configs(ms):
    """All configurations for state vector ms."""
    return list(iprod(*[range(m) for m in ms]))

def is_privileged(config, i, n, ms, tables):
    """Check if processor i is privileged: tables[i](L,S,R) != S."""
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    return tables[i][(L, S, R)] != S

def move_config(config, i, n, ms, tables):
    """Fire processor i."""
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    new = list(config)
    new[i] = tables[i][(L, S, R)]
    return tuple(new)

def incrementing_tables(n, ms):
    """Incrementing transition: f(L,S,R) = (S+1) % m_i."""
    tables = []
    for i in range(n):
        table = {}
        for L in range(ms[(i-1) % n]):
            for S in range(ms[i]):
                for R in range(ms[(i+1) % n]):
                    table[(L, S, R)] = (S + 1) % ms[i]
        tables.append(table)
    return tables

def find_good_cycles(n, ms, tables):
    """Find good cycles: cycles where each config has exactly one privileged proc."""
    configs = all_configs(ms)

    # Map: config -> unique mover (or None)
    priv_map = {}
    for c in configs:
        privs = [i for i in range(n) if is_privileged(c, i, n, ms, tables)]
        if len(privs) == 1:
            priv_map[c] = privs[0]

    # Find cycles in the transition graph
    cycles = []
    visited_global = set()

    for start in priv_map:
        if start in visited_global:
            continue
        path = [start]
        visited = {start}
        current = start
        found = False
        while True:
            mover = priv_map[current]
            nxt = move_config(current, mover, n, ms, tables)
            if nxt not in priv_map:
                break
            if nxt == start:
                if len(path) >= 3:
                    cycles.append(path)
                    found = True
                break
            if nxt in visited:
                break
            path.append(nxt)
            visited.add(nxt)
            current = nxt
        visited_global.update(visited)

    return cycles, priv_map

# ============================================================================
# Phase decomposition
# ============================================================================

def get_mover_word(cycle, priv_map):
    return [priv_map[c] for c in cycle]

def get_fire_steps(mw, p):
    return [i for i, m in enumerate(mw) if m == p]

def fire_count(mw, p):
    return sum(1 for m in mw if m == p)

# ============================================================================
# Approach C: Rotation
# ============================================================================

def verify_rotation_approach(mw, t, n, CL):
    """
    Rotate the cycle so t fires at step 0.
    Then verify that all fc(t) phases are valid linear intervals.
    """
    t_steps = get_fire_steps(mw, t)
    fc_t = len(t_steps)
    if fc_t < 2:
        return None

    left_t = (t - 1) % n
    right_t = (t + 1) % n

    # Rotate
    rot = t_steps[0]
    rmw = mw[rot:] + mw[:rot]
    rt_steps = get_fire_steps(rmw, t)
    assert rt_steps[0] == 0, f"After rotation, t should fire at step 0, got {rt_steps[0]}"

    # fc_t phases:
    # Phase i (i=0..fc_t-2): interior, from rt_steps[i]+1 to rt_steps[i+1]-1
    #   TernaryPhase: a=rt_steps[i], s=rt_steps[i+1], a < s
    # Phase fc_t-1: "final", from rt_steps[-1]+1 to CL-1
    #   This extends to the cycle boundary. In the cyclic world, step CL = step 0.
    #   So this phase ends at the cyclic return to step 0, where t fires again.
    #   As a linear interval: a=rt_steps[-1], s=CL, a < CL. Valid!
    #   But CL is not a valid index in gc.configs (which has CL entries, indexed 0..CL-1).
    #   HOWEVER: we don't need s to be an index. The fire counts in [a+1, CL)
    #   are well-defined (they're just indices a+1, ..., CL-1).

    all_linear = True
    total_J = 0
    total_K = 0
    phase_details = []
    all_steps = set()

    for i in range(fc_t):
        a = rt_steps[i]
        if i < fc_t - 1:
            s = rt_steps[i + 1]  # next t-fire
            ptype = "interior"
        else:
            s = CL  # cycle boundary (conceptually step 0 of next period)
            ptype = "final"

        if a >= s:
            all_linear = False

        # Steps in this phase (excluding a, which is a t-fire, and s which is next t-fire)
        # Count fires of left_t and right_t in (a, s)
        # i.e., steps a+1, a+2, ..., s-1
        J = 0
        K = 0
        for k in range(a + 1, s):
            if k < CL:  # valid index
                all_steps.add(k)
                if rmw[k] == left_t:
                    J += 1
                if rmw[k] == right_t:
                    K += 1

        total_J += J
        total_K += K
        phase_details.append({
            'type': ptype,
            'a': a,
            's': s,
            'J': J,
            'K': K,
            'linear': a < s,
        })

    # Also count the t-fire steps themselves (they fire t, not left_t or right_t)
    # So total_J should account for ALL left_t fires in the entire cycle
    # The t-fire steps fire t. Non-t-fire steps are covered by phases.
    # BUT: step a (t-fire) is NOT in any phase's count interval.
    # Step s (next t-fire) is step a of the NEXT phase, also not counted.
    # So the phases cover exactly the non-t-fire steps.

    # Add t-fire steps to all_steps
    for s in rt_steps:
        all_steps.add(s)

    fc_left = fire_count(rmw, left_t)
    fc_right = fire_count(rmw, right_t)

    # Check: does left_t ever fire at a t-fire step? Only if left_t == t.
    # Since t is ternary and left_t is binary, they're different procs.
    # But could moverAt(step) == left_t at a t-fire step? No: at t-fire steps,
    # moverAt == t, not left_t. So no left_t fires are at t-fire steps.
    # Thus total_J should equal fc_left.

    return {
        'valid': True,
        'all_linear': all_linear,
        'fc_t': fc_t,
        'fc_left': fc_left,
        'fc_right': fc_right,
        'total_J': total_J,
        'total_K': total_K,
        'J_matches': total_J == fc_left,
        'K_matches': total_K == fc_right,
        'partition_complete': len(all_steps) == CL,
        'phases': phase_details,
    }

# ============================================================================
# Approach B: Pure modular (for comparison)
# ============================================================================

def verify_modular_approach(mw, t, n, CL):
    """fc_t cyclic phases indexed modularly."""
    t_steps = get_fire_steps(mw, t)
    fc_t = len(t_steps)
    if fc_t < 2:
        return None

    left_t = (t - 1) % n
    right_t = (t + 1) % n

    total_J = 0
    total_K = 0
    all_steps = set()
    phase_details = []

    for i in range(fc_t):
        a = t_steps[i]
        s = t_steps[(i + 1) % fc_t]

        # Count in cyclic interval (a, s] mod CL
        # Steps: (a+1)%CL, (a+2)%CL, ..., s
        J = 0
        K = 0
        k = (a + 1) % CL
        count = 0
        while True:
            all_steps.add(k)
            if mw[k] == left_t:
                J += 1
            if mw[k] == right_t:
                K += 1
            count += 1
            if k == s:
                break
            k = (k + 1) % CL
            if count > CL:
                break  # safety

        total_J += J
        total_K += K

        is_wrap = (a > s) or (a == t_steps[-1] and s == t_steps[0] and a > s)
        phase_details.append({
            'a': a, 's': s, 'J': J, 'K': K,
            'wraps': a >= s,
            'len': count,
        })

    fc_left = fire_count(mw, left_t)
    fc_right = fire_count(mw, right_t)

    return {
        'valid': True,
        'fc_t': fc_t,
        'fc_left': fc_left,
        'fc_right': fc_right,
        'total_J': total_J,
        'total_K': total_K,
        'J_matches': total_J == fc_left,
        'K_matches': total_K == fc_right,
        'partition_complete': len(all_steps) == CL,
        'phases': phase_details,
    }

# ============================================================================
# Approach D: Direct (no rotation, count wrap separately)
# ============================================================================

def verify_direct_approach(mw, t, n, CL):
    """
    Direct approach: fc_t-1 interior phases + 1 wrap-around.
    Prove wrap-around fire counts + interior fire counts = total.
    """
    t_steps = get_fire_steps(mw, t)
    fc_t = len(t_steps)
    if fc_t < 2:
        return None

    left_t = (t - 1) % n
    right_t = (t + 1) % n

    # Interior phases: between consecutive t-fires (linear, a < s)
    interior_J = 0
    interior_K = 0
    interior_phases = []
    for i in range(fc_t - 1):
        a = t_steps[i]
        s = t_steps[i + 1]
        J = sum(1 for k in range(a + 1, s) if mw[k] == left_t)
        K = sum(1 for k in range(a + 1, s) if mw[k] == right_t)
        interior_J += J
        interior_K += K
        interior_phases.append({'a': a, 's': s, 'J': J, 'K': K})

    # Wrap-around: steps NOT in any interior phase and NOT t-fire steps
    # These are: [0, t_steps[0]) ∪ (t_steps[-1], CL)
    wrap_J = 0
    wrap_K = 0
    wrap_steps = []
    for k in range(0, t_steps[0]):
        wrap_steps.append(k)
        if mw[k] == left_t:
            wrap_J += 1
        if mw[k] == right_t:
            wrap_K += 1
    for k in range(t_steps[-1] + 1, CL):
        wrap_steps.append(k)
        if mw[k] == left_t:
            wrap_J += 1
        if mw[k] == right_t:
            wrap_K += 1

    total_J = interior_J + wrap_J
    total_K = interior_K + wrap_K

    fc_left = fire_count(mw, left_t)
    fc_right = fire_count(mw, right_t)

    return {
        'valid': True,
        'fc_t': fc_t,
        'num_interior': fc_t - 1,
        'interior_J': interior_J,
        'interior_K': interior_K,
        'wrap_J': wrap_J,
        'wrap_K': wrap_K,
        'total_J': total_J,
        'total_K': total_K,
        'J_matches': total_J == fc_left,
        'K_matches': total_K == fc_right,
        'fc_left': fc_left,
        'fc_right': fc_right,
        'interior_phases': interior_phases,
        'wrap_steps': wrap_steps,
    }

# ============================================================================
# Main test
# ============================================================================

def run_tests(n, ms, label=""):
    tables = incrementing_tables(n, ms)
    cycles, priv_map = find_good_cycles(n, ms, tables)

    prod = 1
    for m in ms:
        prod *= m

    print(f"\n{'='*70}")
    print(f"{label}n={n}, ms={ms}, product={prod}")
    print(f"{'='*70}")
    print(f"  Good cycles found: {len(cycles)}")
    if not cycles:
        return

    total = 0
    rot_pass = 0
    mod_pass = 0
    dir_pass = 0
    has_wrap = 0

    for ci, cycle in enumerate(cycles):
        mw = get_mover_word(cycle, priv_map)
        CL = len(cycle)

        for t in range(n):
            t_steps = get_fire_steps(mw, t)
            fc_t = len(t_steps)
            if fc_t < 2:
                continue

            left_t = (t - 1) % n
            right_t = (t + 1) % n

            # Only test ternary t with binary neighbors
            if ms[t] < 3 or ms[left_t] != 2 or ms[right_t] != 2:
                continue

            total += 1

            # Approach C: Rotation
            res_rot = verify_rotation_approach(mw, t, n, CL)
            if res_rot and res_rot['valid'] and res_rot['J_matches'] and res_rot['K_matches'] and res_rot['all_linear']:
                rot_pass += 1
            else:
                print(f"  FAIL rotation: cycle {ci}, t={t}")
                if res_rot:
                    print(f"    {res_rot}")

            # Approach B: Modular
            res_mod = verify_modular_approach(mw, t, n, CL)
            if res_mod and res_mod['valid'] and res_mod['J_matches'] and res_mod['K_matches'] and res_mod['partition_complete']:
                mod_pass += 1
            else:
                print(f"  FAIL modular: cycle {ci}, t={t}")

            # Approach D: Direct
            res_dir = verify_direct_approach(mw, t, n, CL)
            if res_dir and res_dir['valid'] and res_dir['J_matches'] and res_dir['K_matches']:
                dir_pass += 1
                if res_dir['wrap_J'] > 0 or res_dir['wrap_K'] > 0:
                    has_wrap += 1
            else:
                print(f"  FAIL direct: cycle {ci}, t={t}")

    print(f"  Tests: {total}")
    print(f"  Rotation (C): {rot_pass}/{total}")
    print(f"  Modular  (B): {mod_pass}/{total}")
    print(f"  Direct   (D): {dir_pass}/{total}")
    print(f"  Has nonzero wrap fires: {has_wrap}/{total}")

    return total, rot_pass, mod_pass, dir_pass

def detailed_example(n, ms):
    """Show one detailed example."""
    tables = incrementing_tables(n, ms)
    cycles, priv_map = find_good_cycles(n, ms, tables)

    if not cycles:
        print(f"No cycles for n={n}, ms={ms}")
        return

    for ci, cycle in enumerate(cycles[:2]):
        mw = get_mover_word(cycle, priv_map)
        CL = len(cycle)
        print(f"\n  Cycle {ci}: CL={CL}, mover word = {mw}")

        for t in range(n):
            t_steps = get_fire_steps(mw, t)
            fc_t = len(t_steps)
            if fc_t < 2:
                continue
            left_t = (t - 1) % n
            right_t = (t + 1) % n
            if ms[t] < 3 or ms[left_t] != 2 or ms[right_t] != 2:
                continue

            print(f"\n    t={t} (ms[t]={ms[t]}), left={left_t} (ms={ms[left_t]}), right={right_t} (ms={ms[right_t]})")
            print(f"    t fires at steps: {t_steps}, fc(t)={fc_t}")

            # Direct approach
            res = verify_direct_approach(mw, t, n, CL)
            print(f"    Direct approach:")
            print(f"      Interior phases (fc_t-1 = {fc_t-1}):")
            for i, ph in enumerate(res['interior_phases']):
                print(f"        Phase {i}: [{ph['a']}, {ph['s']}), J={ph['J']}, K={ph['K']}")
            print(f"      Wrap-around: steps {res['wrap_steps']}, J={res['wrap_J']}, K={res['wrap_K']}")
            print(f"      Total: J={res['total_J']}=fc(L)={res['fc_left']}? {'YES' if res['J_matches'] else 'NO'}")
            print(f"             K={res['total_K']}=fc(R)={res['fc_right']}? {'YES' if res['K_matches'] else 'NO'}")

            # Rotation approach
            rot = t_steps[0]
            rmw = mw[rot:] + mw[:rot]
            rt_steps = get_fire_steps(rmw, t)
            print(f"    Rotation approach (rotate by {rot}):")
            print(f"      Rotated mw: {rmw}")
            print(f"      t fires at: {rt_steps}")

            res_rot = verify_rotation_approach(mw, t, n, CL)
            for i, ph in enumerate(res_rot['phases']):
                print(f"      Phase {i} ({ph['type']}): [{ph['a']}, {ph['s']}), "
                      f"J={ph['J']}, K={ph['K']}, linear={ph['linear']}")

            break
        break

if __name__ == '__main__':
    print("=" * 70)
    print("CYCLIC PHASE DECOMPOSITION — COMPREHENSIVE VERIFICATION")
    print("=" * 70)

    # n=5 test cases with ternary sandwiched between binary
    test_cases = [
        (5, [2, 2, 3, 2, 3], ""),     # t=2 is ternary between binary 1,3
        (5, [3, 2, 3, 2, 2], ""),     # t=2 ternary between binary 1,3
        (5, [2, 3, 2, 2, 3], ""),     # t=1 ternary between binary 0,2
    ]

    for n, ms, label in test_cases:
        run_tests(n, ms, label)

    # Detailed example
    print("\n" + "=" * 70)
    print("DETAILED EXAMPLE")
    print("=" * 70)
    detailed_example(5, [2, 2, 3, 2, 3])

    # n=7 test
    print("\n" + "=" * 70)
    print("n=7 TESTS")
    print("=" * 70)
    run_tests(7, [2, 2, 3, 3, 2, 3, 3])

    # n=9 is too large for exhaustive search with incrementing tables
    # Use a known sub-threshold multiset
    print("\n" + "=" * 70)
    print("n=9 TESTS (small multiset)")
    print("=" * 70)
    run_tests(9, [2, 2, 3, 2, 3, 3, 3, 3, 3])
