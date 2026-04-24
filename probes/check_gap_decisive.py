#!/usr/bin/env python3
"""
Check GapDecisive: for non-consecutive binary rings with n>=9,
does every sandwiched ternary always have a mechanism-triggering phase?

A sandwiched ternary t has both neighbors binary (left(t) and right(t) binary).
A TernaryPhase is an interval [a, s) where t doesn't fire, then fires at s.
The mechanisms are:
  - BothEven: J even AND K even (where J = left fires in [a,s), K = right fires in [a,s))
  - ToggleFR-L: J >= 2 AND K = 0
  - ToggleFR-R: J = 0 AND K >= 2

We check: for every good cycle, every sandwiched ternary, does at least ONE
phase trigger at least one mechanism?

If yes: gapDecisive_false can dispatch to phase_dispatch_ec without needing
Ring Alternation. The sorry in PhaseExtraction.lean becomes dead code.
"""

import sys
from itertools import product as cart_product


def make_ring(n, binary_positions):
    """Make modulus vector: 2 for binary, 3 for ternary."""
    m = [3] * n
    for p in binary_positions:
        m[p] = 2
    return m


def left(i, n):
    return (i - 1) % n


def right(i, n):
    return (i + 1) % n


def find_sandwiched_ternary(m, n):
    """Find all ternary procs with both neighbors binary."""
    result = []
    for t in range(n):
        if m[t] == 3 and m[left(t, n)] == 2 and m[right(t, n)] == 2:
            result.append(t)
    return result


def enumerate_good_cycles_brute(m, n, f_table):
    """
    Brute-force enumerate good cycles for a given system.
    f_table[i][(L,S,R)] = new value of proc i when it fires with context (L,S,R).
    A good cycle is a sequence of configs where each has exactly one privileged proc.

    This is exponential - only for small n.
    """
    from itertools import product as cprod

    all_configs = list(cprod(*[range(m[i]) for i in range(n)]))

    # For each config, find privileged processors
    priv = {}
    for c in all_configs:
        c = tuple(c)
        privs = []
        for i in range(n):
            L, S, R = c[left(i, n)], c[i], c[right(i, n)]
            if f_table[i].get((L, S, R), S) != S:
                privs.append(i)
        if len(privs) == 1:
            priv[c] = privs[0]

    # Find cycles among single-privileged configs
    cycles = []
    visited_global = set()

    for start in priv:
        if start in visited_global:
            continue
        path = [start]
        visited = {start}
        c = start
        while True:
            p = priv[c]
            # Fire p
            c_list = list(c)
            L, S, R = c[left(p, n)], c[p], c[right(p, n)]
            c_list[p] = f_table[p][(L, S, R)]
            c_next = tuple(c_list)
            if c_next == start:
                # Found a cycle
                cycles.append(path)
                visited_global.update(path)
                break
            if c_next not in priv or c_next in visited:
                break
            path.append(c_next)
            visited.add(c_next)
            c = c_next

    return cycles, priv


def check_phases_for_cycle(cycle, priv, t, n):
    """
    For a good cycle and sandwiched ternary t, extract all phases
    and check if at least one triggers a mechanism.
    """
    L = len(cycle)
    lt = left(t, n)
    rt = right(t, n)

    # Find firing steps of t
    fire_steps = [k for k in range(L) if priv[cycle[k]] == t]

    if len(fire_steps) < 2:
        return True, "fc<2"  # Not enough firings, skip

    # Extract phases: for each firing step s, find the preceding non-fire interval [a, s)
    phases = []
    for idx, s in enumerate(fire_steps):
        # a = step after previous firing of t (or wrap around)
        if idx == 0:
            a = (fire_steps[-1] + 1) % L
        else:
            a = (fire_steps[idx - 1] + 1) % L

        # Count J (left fires) and K (right fires) in [a, s)
        J = 0
        K = 0
        k = a
        while k != s:
            mover = priv[cycle[k]]
            if mover == lt:
                J += 1
            if mover == rt:
                K += 1
            k = (k + 1) % L

        phases.append((J, K))

    # Check if any phase triggers a mechanism
    for J, K in phases:
        if J % 2 == 0 and K % 2 == 0:  # BothEven
            return True, f"BothEven J={J} K={K}"
        if J >= 2 and K == 0:  # ToggleFR-L
            return True, f"ToggleFR-L J={J} K={K}"
        if J == 0 and K >= 2:  # ToggleFR-R
            return True, f"ToggleFR-R J={J} K={K}"

    return False, f"ALL NORMAL: {phases}"


def random_transition_table(m, n, seed=None):
    """Generate a random transition function."""
    import random
    if seed is not None:
        random.seed(seed)

    f = {}
    for i in range(n):
        f[i] = {}
        for L in range(m[left(i, n)]):
            for S in range(m[i]):
                for R in range(m[right(i, n)]):
                    # Random new value, could be same as S (non-privileged) or different
                    f[i][(L, S, R)] = random.randint(0, m[i] - 1)
    return f


def main():
    print("GapDecisive Phase Mechanism Check")
    print("=" * 60)

    # Test small cases exhaustively
    for n in [5, 7, 9]:
        # Generate a few binary placements with no 3 consecutive
        binary_placements = []
        for bits in range(1 << n):
            positions = [i for i in range(n) if bits & (1 << i)]
            if len(positions) < 3:
                continue
            # Check no 3 consecutive
            has_3consec = False
            for p in positions:
                if (p + 1) % n in positions and (p + 2) % n in positions:
                    has_3consec = True
                    break
            if has_3consec:
                continue
            binary_placements.append(positions)

        total_cycles = 0
        total_sandwiched = 0
        total_triggered = 0
        total_normal = 0

        for bp in binary_placements[:5]:  # Limit placements
            m = make_ring(n, bp)
            sandwiched = find_sandwiched_ternary(m, n)
            if not sandwiched:
                continue

            # Try random transition tables
            for seed in range(200):
                f = random_transition_table(m, n, seed=seed + n * 1000)
                try:
                    cycles, priv = enumerate_good_cycles_brute(m, n, f)
                except Exception:
                    continue

                for cycle in cycles:
                    if len(cycle) < 4:
                        continue
                    total_cycles += 1

                    for t in sandwiched:
                        total_sandwiched += 1
                        triggered, reason = check_phases_for_cycle(cycle, priv, t, n)
                        if triggered:
                            total_triggered += 1
                        else:
                            total_normal += 1
                            print(f"  !! NORMAL FORM at n={n} bp={bp} t={t}: {reason}")

        print(f"n={n}: {total_cycles} cycles, {total_sandwiched} sandwiched checks, "
              f"{total_triggered} triggered, {total_normal} all-normal")

    print("\nDone.")


if __name__ == "__main__":
    main()
