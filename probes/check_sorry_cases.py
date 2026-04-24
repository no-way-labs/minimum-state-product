#!/usr/bin/env python3
"""Check the 3 sorry cases in palindromic_phase_ec.

For each random system with sandwiched ternary phase in normal form:
1. Case B (J>=2, left NOT privileged): does it occur?
2. J<=1, K<=1: does it occur?
3. For Case B: does the parity EC argument work? What about edge case?
"""
import random
from itertools import product as iprod

def make_ring(n, ms):
    """Create a ring spec: list of moduli."""
    assert len(ms) == n
    return ms

def random_transition(m_left, m_self, m_right):
    """Random transition function f(L, S, R) -> Fin(m_self)."""
    f = {}
    for L in range(m_left):
        for S in range(m_self):
            for R in range(m_right):
                f[(L, S, R)] = random.randint(0, m_self - 1)
    return f

def privileged(config, sys_f, ms, n, i):
    """Is processor i privileged in config?"""
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    return sys_f[i][(L, S, R)] != S

def find_unique_privileged(config, sys_f, ms, n):
    """Find the unique privileged processor, or None."""
    privs = [i for i in range(n) if privileged(config, sys_f, ms, n, i)]
    if len(privs) == 1:
        return privs[0]
    return None

def apply_move(config, sys_f, ms, n, i):
    """Apply transition at processor i."""
    new_config = list(config)
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    new_config[i] = sys_f[i][(L, S, R)]
    return tuple(new_config)

def find_good_cycle(sys_f, ms, n, max_steps=10000):
    """Try to find a good cycle from a random starting config."""
    config = tuple(random.randint(0, ms[i]-1) for i in range(n))
    visited = {}
    for step in range(max_steps):
        if config in visited:
            # Found a cycle
            start = visited[config]
            cycle_configs = []
            c = config
            for _ in range(step - start):
                cycle_configs.append(c)
                p = find_unique_privileged(c, sys_f, ms, n)
                if p is None:
                    return None  # Not single-privileged
                c = apply_move(c, sys_f, ms, n, p)
            # Verify all configs are single-privileged
            for c in cycle_configs:
                if find_unique_privileged(c, sys_f, ms, n) is None:
                    return None
            return cycle_configs
        visited[config] = step
        p = find_unique_privileged(config, sys_f, ms, n)
        if p is None:
            return None
        config = apply_move(config, sys_f, ms, n, p)
    return None

def analyze_phase(cycle_configs, sys_f, ms, n, t):
    """Find phases for processor t and analyze fire counts."""
    L = len(cycle_configs)
    movers = []
    for k in range(L):
        p = find_unique_privileged(cycle_configs[k], sys_f, ms, n)
        movers.append(p)

    # Find fire steps for t
    fire_steps = [k for k in range(L) if movers[k] == t]
    if len(fire_steps) < 2:
        return []

    phases = []
    for idx in range(len(fire_steps)):
        s = fire_steps[idx]
        # Find previous fire (wrapping)
        prev = fire_steps[(idx - 1) % len(fire_steps)]
        if prev < s:
            a = prev + 1  # First step after previous fire
            # Check no t fires in [a, s)
            ok = all(movers[k] != t for k in range(a, s))
            if ok and a < s:
                lt = (t - 1) % n
                rt = (t + 1) % n
                J = sum(1 for k in range(a, s) if movers[k] == lt)
                K = sum(1 for k in range(a, s) if movers[k] == rt)
                phases.append({
                    'a': a, 's': s, 'J': J, 'K': K,
                    'movers': movers[a:s],
                    't': t, 'lt': lt, 'rt': rt
                })
    return phases

def check_normal_form(J, K):
    """Check if (J, K) is in normal form (none of 3 mechanisms fire)."""
    if J % 2 == 0 and K % 2 == 0:
        return False  # BothEven
    if J >= 2 and K == 0:
        return False  # ToggleFR-L
    if J == 0 and K >= 2:
        return False  # ToggleFR-R
    return True

def check_case_b(cycle_configs, sys_f, ms, n, phase):
    """Check if Case B occurs (left NOT privileged at k_max+1)."""
    t = phase['t']
    lt = phase['lt']
    a, s = phase['a'], phase['s']
    movers = [find_unique_privileged(cycle_configs[k], sys_f, ms, n) for k in range(len(cycle_configs))]

    # Find last left fire in [a, s)
    left_fires = [k for k in range(a, s) if movers[k] == lt]
    if not left_fires:
        return None
    k_max = max(left_fires)

    # Check if left(t) is privileged at k_max+1
    if k_max + 1 < len(cycle_configs):
        is_priv = privileged(cycle_configs[k_max + 1], sys_f, ms, n, lt)
        return not is_priv  # True = Case B
    return None

def check_parity_ec(cycle_configs, sys_f, ms, n, phase):
    """Check if parity EC works (intermediate parity match exists)."""
    t = phase['t']
    lt = phase['lt']
    rt = phase['rt']
    a, s = phase['a'], phase['s']
    J, K = phase['J'], phase['K']
    movers = [find_unique_privileged(cycle_configs[k], sys_f, ms, n) for k in range(len(cycle_configs))]

    target_j_parity = J % 2
    target_k_parity = K % 2

    # Track running fire counts
    j_count = 0
    r_count = 0

    intermediate_matches = []
    for k in range(a, s):
        if movers[k] == lt:
            j_count += 1
        elif movers[k] == rt:
            r_count += 1

        # Check parity at config k+1
        if k + 1 < s:  # Nonmover step for t
            if j_count % 2 == target_j_parity and r_count % 2 == target_k_parity:
                intermediate_matches.append(k + 1)

    return len(intermediate_matches) > 0, intermediate_matches

def main():
    random.seed(42)
    n = 9

    # Try many random systems with sandwiched ternary
    normal_form_count = 0
    case_b_count = 0
    j1k1_count = 0
    parity_fail_count = 0
    total_phases = 0

    for trial in range(50000):
        # Place binary at 0, 2 and ternary at 1 (sandwiched)
        # Rest ternary
        ms = [2, 3, 2] + [3] * (n - 3)

        # Random transitions
        sys_f = {}
        for i in range(n):
            m_left = ms[(i-1) % n]
            m_self = ms[i]
            m_right = ms[(i+1) % n]
            sys_f[i] = random_transition(m_left, m_self, m_right)

        # Find a good cycle
        cycle = find_good_cycle(sys_f, ms, n, max_steps=5000)
        if cycle is None:
            continue

        # Analyze phases for the sandwiched ternary (proc 1)
        t = 1  # Ternary sandwiched between binary 0 and 2
        phases = analyze_phase(cycle, sys_f, ms, n, t)

        for phase in phases:
            J, K = phase['J'], phase['K']
            if not check_normal_form(J, K):
                continue

            normal_form_count += 1
            total_phases += 1

            # Check J<=1, K<=1
            if J <= 1 and K <= 1:
                j1k1_count += 1
                print(f"  J<=1,K<=1 found! J={J}, K={K}, trial={trial}")

            # Check Case B for J>=2
            if J >= 2:
                is_case_b = check_case_b(cycle, sys_f, ms, n, phase)
                if is_case_b:
                    case_b_count += 1
                    print(f"  Case B found! J={J}, K={K}, trial={trial}")

            # Check parity EC
            has_match, matches = check_parity_ec(cycle, sys_f, ms, n, phase)
            if not has_match:
                parity_fail_count += 1
                # Check if last fire is at s-1
                movers_in_phase = phase['movers']
                last_neighbor_fire = None
                for k_idx in range(len(movers_in_phase) - 1, -1, -1):
                    if movers_in_phase[k_idx] in [phase['lt'], phase['rt']]:
                        last_neighbor_fire = phase['a'] + k_idx
                        break
                is_edge = (last_neighbor_fire == phase['s'] - 1) if last_neighbor_fire is not None else False
                if parity_fail_count <= 20:
                    print(f"  Parity fail: J={J}, K={K}, phase_len={phase['s']-phase['a']}, "
                          f"last_fire_at_s-1={is_edge}, trial={trial}")

    print(f"\n=== RESULTS ({total_phases} normal-form phases in {trial+1} trials) ===")
    print(f"Normal form phases: {normal_form_count}")
    print(f"Case B (J>=2, left NOT privileged): {case_b_count}")
    print(f"J<=1, K<=1: {j1k1_count}")
    print(f"Parity EC fails (no intermediate match): {parity_fail_count}")

if __name__ == '__main__':
    main()
