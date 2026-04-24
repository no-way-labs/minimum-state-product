#!/usr/bin/env python3
"""scc_dijkstra_verify.py — Verify Dijkstra's Sol 3 for n=9, K=3.

The SCC screen finds 30 SCCs in the COMPLETE transition graph.
Does Sol 3 actually converge? Check by:
1. Verifying with our verifier
2. Tracing a specific SCC cycle to see if it's real
3. Testing convergence from every non-legit config
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian


def dijkstra_sol3_rule(i, L, S, R, n, K=3):
    """Returns new value for processor i."""
    if i == 0:
        target = (L + 1) % K  # L = s_{n-1}
        if S != target:
            return target
        return S
    else:
        if S != L:
            return L
        return S


def main():
    n = 9
    K = 3
    print("=" * 70)
    print(f"DIJKSTRA SOL 3 VERIFICATION: n={n}, K={K}")
    print("=" * 70)

    # Build complete rule table
    all_configs = list(cartesian(*(range(K) for _ in range(n))))
    print(f"Total configs: {len(all_configs)}")

    # Test 1: Check for deadlocks (configs with 0 privileges)
    deadlocks = []
    for c in all_configs:
        has_priv = False
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            new_val = dijkstra_sol3_rule(i, L, S, R, n, K)
            if new_val != S:
                has_priv = True
                break
        if not has_priv:
            deadlocks.append(c)

    print(f"\nDeadlocks (0 privileges): {len(deadlocks)}")
    if len(deadlocks) > 0:
        print("  FATAL: deadlocks exist, system is broken!")
        for c in deadlocks[:5]:
            print(f"    {c}")

    # Test 2: Find legitimate configs (exactly 1 privilege)
    legitimate = []
    for c in all_configs:
        privs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if dijkstra_sol3_rule(i, L, S, R, n, K) != S:
                privs.append(i)
        if len(privs) == 1:
            legitimate.append(c)
    print(f"Legitimate (1 privilege): {len(legitimate)}")

    # Test 3: Convergence check — BFS/DFS from every non-legit config
    # For each non-legit config, check if ALL execution paths eventually reach legit
    # This is exponential, so instead: check if there exists a cycle in the
    # reachable graph

    # Actually, let's just check: from a specific config in the alleged SCC,
    # trace a random execution and see if it converges
    print(f"\n--- Convergence trace ---")

    # Pick a non-legit config
    test_config = (0, 1, 0, 1, 0, 1, 0, 1, 0)
    legit_set = set(legitimate)

    c = test_config
    steps = 0
    max_steps = 1000
    path = [c]

    while c not in legit_set and steps < max_steps:
        # Find all privileged processors
        privs = []
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if dijkstra_sol3_rule(i, L, S, R, n, K) != S:
                privs.append(i)

        if not privs:
            print(f"  DEADLOCK at step {steps}: {c}")
            break

        # Choose the FIRST privileged processor (deterministic)
        mover = privs[0]
        new_c = list(c)
        L = c[(mover-1) % n]; S = c[mover]; R = c[(mover+1) % n]
        new_c[mover] = dijkstra_sol3_rule(mover, L, S, R, n, K)
        c = tuple(new_c)
        steps += 1
        path.append(c)

    if c in legit_set:
        print(f"  Config {test_config} converged in {steps} steps")
    else:
        print(f"  Config {test_config} did NOT converge in {max_steps} steps")

    # Test 4: Try adversarial execution — always choose the processor that
    # keeps us in the alleged SCC
    print(f"\n--- Adversarial convergence test ---")

    # First, find a small SCC by tracing
    # Build successor graph
    non_legit = [c for c in all_configs if c not in legit_set]
    non_legit_set = set(non_legit)

    # Try to find a cycle by following a specific strategy
    # Strategy: at each step, choose the processor that maximizes the number
    # of privileges in the successor (keeps complexity high)
    c = (0, 1, 2, 0, 1, 2, 0, 1, 2)
    steps = 0
    seen = {}
    cycle_found = False

    while steps < 200:
        if c in legit_set:
            print(f"  Reached legit at step {steps}: {c}")
            break

        if c in seen:
            cycle_len = steps - seen[c]
            print(f"  CYCLE found at step {steps}, length {cycle_len}")
            print(f"  Config: {c}")
            cycle_found = True
            break

        seen[c] = steps

        # Find all privileged processors and their successors
        best_mover = None
        best_score = -1
        for i in range(n):
            L = c[(i-1) % n]; S = c[i]; R = c[(i+1) % n]
            if dijkstra_sol3_rule(i, L, S, R, n, K) != S:
                new_c = list(c)
                new_c[i] = dijkstra_sol3_rule(i, L, S, R, n, K)
                new_c = tuple(new_c)

                # Score: prefer successors that are non-legit and have many privs
                if new_c in non_legit_set:
                    n_privs = 0
                    for j in range(n):
                        Lj = new_c[(j-1) % n]; Sj = new_c[j]; Rj = new_c[(j+1) % n]
                        if dijkstra_sol3_rule(j, Lj, Sj, Rj, n, K) != Sj:
                            n_privs += 1
                    if n_privs > best_score:
                        best_score = n_privs
                        best_mover = i
                elif best_mover is None:
                    best_mover = i

        if best_mover is None:
            print(f"  DEADLOCK at step {steps}")
            break

        new_c = list(c)
        L = c[(best_mover-1) % n]; S = c[best_mover]; R = c[(best_mover+1) % n]
        new_c[best_mover] = dijkstra_sol3_rule(best_mover, L, S, R, n, K)
        c = tuple(new_c)
        steps += 1

    if not cycle_found and c not in legit_set:
        print(f"  No cycle found in 200 steps, but not converged either")
    elif c in legit_set:
        print(f"  Even adversarial strategy converged in {steps} steps")

    # Test 5: Exhaustive convergence — from EVERY non-legit config,
    # does EVERY execution converge? (Use bounded model checking)
    print(f"\n--- Exhaustive convergence check (bounded to 100 steps) ---")

    # For each non-legit config, check if there exists an execution that
    # doesn't converge in 100 steps. Use DFS with adversarial choices.
    max_depth = 100
    n_non_converging = 0
    non_converging_examples = []

    for ci, c in enumerate(non_legit[:500]):  # Sample first 500
        # Try adversarial execution
        cur = c
        converged = False
        for step in range(max_depth):
            if cur in legit_set:
                converged = True
                break

            # Find privileged processors
            best = None
            best_np = -1
            for i in range(n):
                L = cur[(i-1) % n]; S = cur[i]; R = cur[(i+1) % n]
                if dijkstra_sol3_rule(i, L, S, R, n, K) != S:
                    new_c = list(cur)
                    new_c[i] = dijkstra_sol3_rule(i, L, S, R, n, K)
                    new_c = tuple(new_c)
                    if new_c in non_legit_set:
                        np = sum(1 for j in range(n)
                                if dijkstra_sol3_rule(j, new_c[(j-1)%n], new_c[j], new_c[(j+1)%n], n, K) != new_c[j])
                        if np > best_np:
                            best_np = np
                            best = i
                    elif best is None:
                        best = i

            if best is None:
                break

            new_c = list(cur)
            L = cur[(best-1) % n]; S = cur[best]; R = cur[(best+1) % n]
            new_c[best] = dijkstra_sol3_rule(best, L, S, R, n, K)
            cur = tuple(new_c)

        if not converged:
            n_non_converging += 1
            if len(non_converging_examples) < 3:
                non_converging_examples.append(c)

    print(f"  Checked {min(500, len(non_legit))} configs (adversarial, max {max_depth} steps)")
    print(f"  Non-converging: {n_non_converging}")
    if non_converging_examples:
        for c in non_converging_examples:
            n_privs = sum(1 for i in range(n)
                         if dijkstra_sol3_rule(i, c[(i-1)%n], c[i], c[(i+1)%n], n, K) != c[i])
            print(f"    {c} ({n_privs} privileges)")

    # Test 6: Check our verifier
    print(f"\n--- Verifier check ---")
    try:
        from verifier import verify_dijkstra_solution3
        result = verify_dijkstra_solution3(n)
        print(f"  verify_dijkstra_solution3({n}): {result}")
    except Exception as e:
        print(f"  Verifier error: {e}")

    try:
        from verifier import verify_system
        # Build the rule table as ms = (K,)*n
        ms = (K,) * n

        # Build rule dict
        rules = {}
        for i in range(n):
            for L in range(K):
                for S in range(K):
                    for R in range(K):
                        rules[(i, L, S, R)] = dijkstra_sol3_rule(i, L, S, R, n, K)

        result = verify_system(ms, rules)
        print(f"  verify_system for Dijkstra Sol 3 n={n}: {result}")
    except Exception as e:
        print(f"  verify_system error: {e}")


if __name__ == "__main__":
    main()
