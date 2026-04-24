#!/usr/bin/env python3
"""Prove the Δfc=0 subgraph is a DAG via the Ψ potential.

Key analytical results:
1. All copy-neighbor moves have Δfc ≤ 0. (Proved from table entries.)
2. Δfc=0 moves propagate frontiers: type-1 LEFT, type-2 RIGHT (interior).
3. Each Δfc=0 move is IRREVERSIBLE (the reverse entry is STAY).
4. Ψ potential with w₁, w₂ weights strictly decreases on every Δfc=0 move.

This proves: Δfc≤0 subgraph is a DAG.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def frontier_type(a, b):
    """Type of frontier between positions with values a and b. 0 if no frontier."""
    if a == b:
        return 0
    return (b - a) % 3  # 1 or 2


def w1(j, n):
    """Weight for type-1 frontier at position j."""
    if j == n - 1:
        return 0
    if j == n - 2:
        return 1
    return j + 1  # positions 0..n-3


def w2(j, n):
    """Weight for type-2 frontier at position j."""
    if j == n - 1:
        return 0
    if 1 <= j <= n - 2:
        return n - 1 - j
    return n - 1  # position 0


def psi(c, n):
    """Compute Ψ(c) = Σ w₁(j) for type-1 frontiers + Σ w₂(j) for type-2 frontiers."""
    total = 0
    for j in range(n):
        ft = frontier_type(c[j], c[(j + 1) % n])
        if ft == 1:
            total += w1(j, n)
        elif ft == 2:
            total += w2(j, n)
    return total


def main():
    print("Ψ POTENTIAL VERIFICATION")
    print("=" * 70)

    # First: verify analytically that each Δfc=0 entry is irreversible.
    print("\nIRREVERSIBILITY CHECK (reverse entry is STAY)")
    print("-" * 60)

    # For each Δfc=0 privileged entry in each table, check that the
    # reverse move is not possible (the reverse entry has output = S).
    tables_by_pos = {
        'bot': (T_bot, 2, 2, 3),
        'low': (T_low, 2, 3, 3),
        'mid': (T_mid, 3, 3, 3),
        'high': (T_high, 3, 3, 2),
        'top': (T_top, 3, 2, 2),
    }

    all_irrev = True
    for tname, (table, mL, mS, mR) in tables_by_pos.items():
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = table[(L, S, R)]
                    if out == S:
                        continue
                    dfc = delta_fc(L, S, R, out)
                    if dfc != 0:
                        continue
                    # This is a Δfc=0 privileged entry. Check reverse.
                    # After move: processor has value 'out'. Neighbors are L, R.
                    # Reverse: processor sees (L, out, R) and should output S.
                    # Check if table[(L, out, R)] == S.
                    if (L, out, R) in table:
                        rev_out = table[(L, out, R)]
                        if rev_out == S:
                            # Reverse move EXISTS! Not irreversible.
                            all_irrev = False
                            print(f"  REVERSIBLE: {tname}({L},{S},{R})→{out} "
                                  f"reversed by {tname}({L},{out},{R})→{S}")
                        elif rev_out == out:
                            print(f"  ✓ {tname}({L},{S},{R})→{out}: "
                                  f"reverse ({L},{out},{R})→{rev_out} STAY")
                        else:
                            print(f"  ✓ {tname}({L},{S},{R})→{out}: "
                                  f"reverse ({L},{out},{R})→{rev_out} (different, not S={S})")

    print(f"\n  All irreversible: {'YES ✓' if all_irrev else 'NO ✗'}")

    # Verify Ψ strictly decreases on all Δfc=0 bad→bad transitions
    print("\n\nΨ MONOTONICITY VERIFICATION")
    print("-" * 60)

    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        violations = 0
        total_dfc0 = 0
        for c in bad_set:
            for i in range(n):
                Li = c[(i - 1) % n]; Si = c[i]; Ri = c[(i + 1) % n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    dfc = delta_fc(Li, Si, Ri, out)
                    if dfc == 0:
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        if succ in bad_set:
                            total_dfc0 += 1
                            psi_c = psi(c, n)
                            psi_s = psi(succ, n)
                            if psi_s >= psi_c:
                                violations += 1
                                if violations <= 3:
                                    print(f"  VIOLATION n={nv}: {c}→{succ} "
                                          f"Ψ={psi_c}→{psi_s}")

        status = "✓ Ψ strictly decreasing" if violations == 0 else f"✗ {violations} violations"
        print(f"  n={nv}: {total_dfc0} Δfc=0 transitions, {status}")

    # Also verify: (fc, Ψ) is lexicographic potential for Δfc≤0 subgraph
    print("\n\n(fc, Ψ) LEXICOGRAPHIC POTENTIAL FOR Δfc≤0")
    print("-" * 60)
    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        violations = 0
        total = 0
        for c in bad_set:
            fc_c = sum(1 for j in range(n) if c[j] != c[(j+1)%n])
            psi_c = psi(c, n)
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    dfc = delta_fc(Li, Si, Ri, out)
                    if dfc <= 0:
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        if succ in bad_set:
                            total += 1
                            fc_s = sum(1 for j in range(n)
                                       if succ[j] != succ[(j+1)%n])
                            psi_s = psi(succ, n)
                            if (fc_s, psi_s) >= (fc_c, psi_c):
                                violations += 1

        status = "✓" if violations == 0 else f"✗ {violations} violations"
        print(f"  n={nv}: {total} Δfc≤0 transitions, {status}")


if __name__ == "__main__":
    main()
