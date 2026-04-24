#!/usr/bin/env python3
"""CIC: Verify the Adjacent-Mover Lemma computationally.

Lemma: In any valid self-stabilizing token ring (Dijkstra model),
consecutive movers m_k and m_{k+1} in the good cycle satisfy
|m_{k+1} - m_k| <= 1 (mod n).

Proof sketch:
- At config g_k, only processor m_k is privileged (mutual exclusion)
- m_k fires, producing g_{k+1}
- Only m_k's state changes: g_{k+1}[i] = g_k[i] for i != m_k
- Processor p's privilege depends on (g[p-1], g[p], g[p+1])
- Only processors whose context changed can become newly privileged
- g_{k+1}[m_k] != g_k[m_k], all other states unchanged
- Only P_{m_k-1}, P_{m_k}, P_{m_k+1} have changed contexts
- At g_k, only m_k was privileged => m_{k+1} was NOT privileged at g_k
- At g_{k+1}, m_{k+1} IS privileged
- So m_{k+1} must have a changed context => m_{k+1} in {m_k-1, m_k, m_k+1}

Verification: Check ALL known valid systems (Sol 1, Sol 3, CLB)
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from verifier import (verify_system, verify_dijkstra_solution1,
                      verify_dijkstra_solution3)


def check_adjacent_movers(ms, fs, label=""):
    """Verify that all consecutive movers in the good cycle are adjacent."""
    result = verify_system(ms, fs, verbose=False)
    if not result['valid']:
        print(f"  {label}: NOT VALID")
        return

    cycle = result['cycle']
    n = len(ms)

    # Find movers: which processor changed between consecutive configs
    movers = []
    for k in range(len(cycle)):
        c0 = cycle[k]
        c1 = cycle[(k + 1) % len(cycle)]
        for p in range(n):
            if c0[p] != c1[p]:
                movers.append(p)
                break

    # Check adjacency
    violations = 0
    for k in range(len(movers)):
        m0 = movers[k]
        m1 = movers[(k + 1) % len(movers)]
        diff = min(abs(m1 - m0), n - abs(m1 - m0))
        if diff > 1:
            violations += 1
            print(f"  VIOLATION at step {k}: "
                  f"m_k={m0}, m_{k+1}={m1}, diff={diff}")

    if violations == 0:
        # Classify mover pattern
        steps = []
        for k in range(len(movers)):
            m0 = movers[k]
            m1 = movers[(k + 1) % len(movers)]
            d = (m1 - m0) % n
            if d > n // 2:
                d -= n
            steps.append(d)

        step_counts = {}
        for s in steps:
            step_counts[s] = step_counts.get(s, 0) + 1

        print(f"  {label}: OK. cycle_len={len(cycle)}, "
              f"movers={movers[:20]}{'...' if len(movers) > 20 else ''}")
        print(f"    Step distribution: {step_counts}")
        print(f"    (0=same, 1=right, -1=left)")


# =============================================================
# Test 1: Dijkstra's Solution 3 (all ternary)
# =============================================================
print("=" * 60)
print("Solution 3 (ms=[3]*n)")
print("=" * 60)
for n in [3, 4, 5, 6, 7]:
    ms = [3] * n

    def make_sol3_f(n):
        def f0(L, S, R):
            return (S + 1) % 3 if S == L else S

        def fi(L, S, R):
            return L if L != S else S
        return [f0] + [fi] * (n - 1)

    fs = make_sol3_f(n)
    check_adjacent_movers(ms, fs, f"n={n}")

# =============================================================
# Test 2: Dijkstra's Solution 1 (K-state, uniform)
# =============================================================
print(f"\n{'=' * 60}")
print("Solution 1 (ms=[K]*n)")
print("=" * 60)
for n, K in [(3, 3), (4, 4), (5, 5), (5, 6)]:
    ms = [K] * n

    def make_sol1_f(n, K):
        def f0(L, S, R):
            return (L + 1) % K if S == L else S

        def fi(L, S, R):
            return L if L != S else S
        return [f0] + [fi] * (n - 1)

    fs = make_sol1_f(n, K)
    check_adjacent_movers(ms, fs, f"n={n}, K={K}")

# =============================================================
# Test 3: CLB endpoint-binary (ms=(2,3,...,3,2))
# =============================================================
print(f"\n{'=' * 60}")
print("CLB endpoint-binary (ms=(2,3,...,3,2))")
print("=" * 60)

# Import the CLB witness builder
try:
    from clb_witness_8748 import build_clb_witness
    for n in [5, 6, 7, 8, 9]:
        ms_tuple, fs = build_clb_witness(n)
        check_adjacent_movers(list(ms_tuple), fs, f"n={n}")
except ImportError:
    # Build manually
    from itertools import product as cartesian
    from collections import defaultdict

    for n in [5, 6, 7]:
        ms = [2] + [3] * (n - 2) + [2]
        up_down = list(range(n)) + list(range(n - 2, 0, -1))

        def build_bounce_cycle(ms, n, base, max_reps=5):
            for reps in range(1, max_reps):
                config = [0] * n
                cycle = [tuple(config)]
                visited = {tuple(config)}
                full = base * reps
                for step, mover in enumerate(full):
                    config = list(cycle[-1])
                    config[mover] = (config[mover] + 1) % ms[mover]
                    nc = tuple(config)
                    if nc == cycle[0]:
                        return cycle, full[:step + 1]
                    if nc in visited:
                        break
                    visited.add(nc)
                    cycle.append(nc)
            return None, None

        cycle, movers_seq = build_bounce_cycle(ms, n, up_down)
        if cycle is None:
            print(f"  n={n}: no bounce cycle found")
            continue

        good_set = set(cycle)
        all_configs = list(cartesian(*(range(m) for m in ms)))
        non_good = [c for c in all_configs if c not in good_set]
        non_good_set = set(non_good)

        det = {}
        for idx in range(len(cycle)):
            c = cycle[idx]
            c_next = cycle[(idx + 1) % len(cycle)]
            mv = movers_seq[idx]
            for p in range(n):
                L = c[(p - 1) % n]
                S = c[p]
                R = c[(p + 1) % n]
                key = (p, L, S, R)
                if p == mv:
                    det[key] = c_next[p]
                else:
                    det[key] = S

        # Good-targeting completion
        free_entries = []
        for p in range(n):
            m_L = ms[(p - 1) % n]
            m_S = ms[p]
            m_R = ms[(p + 1) % n]
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        key = (p, L, S, R)
                        if key not in det:
                            free_entries.append(key)

        comp = dict(det)
        for key in free_entries:
            p, L, S, R = key
            best_out = S
            best_good = 0
            best_ng = float('inf')
            for out in range(ms[p]):
                ng = 0
                good_count = 0
                if out != S:
                    for c in non_good:
                        if (c[(p - 1) % n] == L and c[p] == S
                                and c[(p + 1) % n] == R):
                            new_c = list(c)
                            new_c[p] = out
                            nc = tuple(new_c)
                            if nc in good_set:
                                good_count += 1
                            elif nc in non_good_set:
                                ng += 1
                if (good_count > best_good
                        or (good_count == best_good and ng < best_ng)):
                    best_out = out
                    best_good = good_count
                    best_ng = ng
            comp[key] = best_out

        for c in all_configs:
            has_priv = any(
                comp.get((p, c[(p - 1) % n], c[p], c[(p + 1) % n]),
                         c[p]) != c[p]
                for p in range(n))
            if not has_priv:
                for p in range(n):
                    L2 = c[(p - 1) % n]
                    S2 = c[p]
                    R2 = c[(p + 1) % n]
                    key = (p, L2, S2, R2)
                    if key not in det:
                        for out in range(ms[p]):
                            if out != S2:
                                comp[key] = out
                                break
                        break

        def make_f(p_idx):
            def f(L, S, R):
                return comp.get((p_idx, L, S, R), S)
            return f

        fs = [make_f(p) for p in range(n)]
        check_adjacent_movers(ms, fs, f"n={n}")

# =============================================================
# Summary: the lemma
# =============================================================
print(f"\n{'=' * 60}")
print("ADJACENT-MOVER LEMMA")
print("=" * 60)
print("""
Theorem: In any valid self-stabilizing token ring (Dijkstra model),
if the good cycle visits configs g_0, g_1, ..., g_{L-1} with movers
m_0, m_1, ..., m_{L-1}, then for all k:

    |m_{k+1} - m_k| <= 1  (mod n)

Proof:
1. At g_k, only m_k is privileged (mutual exclusion)
2. m_k fires: g_{k+1}[m_k] != g_k[m_k], all other states unchanged
3. Only {m_k-1, m_k, m_k+1}'s contexts change (locality)
4. At g_k, m_{k+1} was NOT privileged (only m_k was)
5. At g_{k+1}, m_{k+1} IS privileged
6. m_{k+1}'s context must have changed => m_{k+1} in {m_k-1, m_k, m_k+1}  QED

Corollary: The mover sequence is a walk on Z_n with steps in {-1, 0, +1}.
This walk must visit all n processors (fairness), so it's a connected
walk covering the entire ring.
""")
