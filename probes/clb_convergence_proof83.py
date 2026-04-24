#!/usr/bin/env python3
"""
CONVERGENCE PROOF 83: Analytical per-step monotonicity proof
=============================================================
THEOREM: For the CUP-2 system, every step in the bad-config graph satisfies:
  (a) Δ(int_20 + int_21) ≤ 0  (count of exposed interior 2's never increases)
  (b) Δint_21 ≤ 0              (count of interior (2,1) pairs never increases)
  (c) Δ(intj20 + intj21) ≤ 0  (position-weighted exposed interior 2's never increases)

PROOF: By direct enumeration of all CUP-2 table entries.

For a step at position j changing c[j] from S to out = f(L,S,R):
- Interior pair at j-1: (L, S) → (L, out).  [only if j-1 ∈ [2,n-3]]
  Δexp2@(j-1) = [L=2] · ([out∈{0,1}] - [S∈{0,1}])
  Δi21@(j-1)  = [L=2] · ([out=1] - [S=1])

- Interior pair at j: (S, R) → (out, R).  [only if j ∈ [2,n-3]]
  Δexp2@j = [R∈{0,1}] · ([out=2] - [S=2])
  Δi21@j  = [R=1] · ([out=2] - [S=2])

Position ranges:
  T_bot (j=0), T_low (j=1), T_top (j=n-1): no interior pairs affected.
  T_high (j=n-2): only pair at j-1=n-3 is interior.
  T_mid (j=2..n-3): pair at j is always interior; pair at j-1 interior iff j≥3.

For (c), the position-weighted version:
  Δ(intj20+intj21) = (j-1)·Δexp2@(j-1) + j·Δexp2@j
  (with appropriate position-range restrictions)
"""
import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top


def analyze_entry(L, S, R, out, table_name, pos_type):
    """Analyze effect on interior quantities for one table entry.

    pos_type: 'bot'(j=0), 'low'(j=1), 'mid2'(j=2), 'mid'(j≥3), 'high'(j=n-2), 'top'(j=n-1)
    Returns (Δexp2, Δint21, Δwt_sign) where Δwt_sign is the sign constraint for weighted version.
    """
    if out == S:
        return 0, 0, '='  # Not privileged

    # Pair at j-1 changes
    A_exp2 = int(L == 2) * (int(out in (0, 1)) - int(S in (0, 1)))
    A_i21 = int(L == 2) * (int(out == 1) - int(S == 1))

    # Pair at j changes
    B_exp2 = int(R in (0, 1)) * (int(out == 2) - int(S == 2))
    B_i21 = int(R == 1) * (int(out == 2) - int(S == 2))

    if pos_type in ('bot', 'low', 'top'):
        # No interior pairs affected
        return 0, 0, '='

    if pos_type == 'high':
        # Only pair at j-1 = n-3 is interior
        return A_exp2, A_i21, ('<=' if A_exp2 <= 0 else '?')

    if pos_type == 'mid2':
        # j=2: pair at j-1=1 NOT interior, only pair at j
        return B_exp2, B_i21, ('<=' if B_exp2 <= 0 else '?')

    if pos_type == 'mid':
        # j≥3: both pairs interior
        d_exp2 = A_exp2 + B_exp2
        d_i21 = A_i21 + B_i21
        # Weighted: (j-1)*A + j*B. Need this ≤ 0 for all j≥3.
        # If A≤0 and B≤0: always ≤ 0
        # If A=+1, B=-1: (j-1) - j = -1 ≤ 0
        # If A=-1, B=+1: -(j-1) + j = +1 > 0  ← problematic
        if A_exp2 <= 0 and B_exp2 <= 0:
            wt = '<='
        elif A_exp2 == 1 and B_exp2 == -1:
            wt = '<='  # (j-1)*1 + j*(-1) = -1
        elif A_exp2 == -1 and B_exp2 == 1:
            wt = '!!!'  # Would be +1
        else:
            wt = '?'
        return d_exp2, d_i21, wt

    return 0, 0, '?'


def main():
    print("=" * 80)
    print("ANALYTICAL PROOF: Per-step monotonicity for CUP-2")
    print("=" * 80)

    tables = [
        ("T_bot", T_bot, 'bot'),
        ("T_low", T_low, 'low'),
        ("T_mid", T_mid, 'mid'),
        ("T_high", T_high, 'high'),
        ("T_top", T_top, 'top'),
    ]

    all_ok = True

    for tname, table, ttype in tables:
        print(f"\n{'─'*80}")
        print(f"Table: {tname} (position type: {ttype})")
        print(f"{'─'*80}")

        n_priv = 0
        n_violations = 0

        # Determine position types to check
        if ttype == 'mid':
            pos_types = ['mid2', 'mid']  # j=2 and j≥3
        else:
            pos_types = [ttype]

        for (L, S, R), out in sorted(table.items()):
            if out == S:
                continue
            n_priv += 1

            for ptype in pos_types:
                d_exp2, d_i21, wt = analyze_entry(L, S, R, out, tname, ptype)

                pos_label = {'bot': 'j=0', 'low': 'j=1', 'mid2': 'j=2',
                             'mid': 'j≥3', 'high': 'j=n-2', 'top': 'j=n-1'}[ptype]

                ok_exp2 = d_exp2 <= 0
                ok_i21 = d_i21 <= 0
                ok_wt = wt == '<=' or wt == '='

                if not (ok_exp2 and ok_i21 and ok_wt):
                    marker = " *** VIOLATION ***"
                    n_violations += 1
                    all_ok = False
                else:
                    marker = ""

                # Compute Δfc for context
                dfc = (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))

                print(f"  ({L},{S},{R})→{out}  [{pos_label}]  "
                      f"Δfc={dfc:+d}  Δexp2={d_exp2:+d}  Δint21={d_i21:+d}  "
                      f"wt:{wt}{marker}")

        print(f"  → {n_priv} privileged entries, {n_violations} violations")

    print(f"\n{'='*80}")
    if all_ok:
        print("THEOREM PROVED: All three per-step monotonicity properties hold.")
        print("  (a) Δ(int_20 + int_21) ≤ 0 on every step  ✓")
        print("  (b) Δint_21 ≤ 0 on every step             ✓")
        print("  (c) Δ(intj20 + intj21) ≤ 0 on every step  ✓")
    else:
        print("VIOLATIONS FOUND — theorem FAILS!")
    print("=" * 80)

    # === Implications for convergence ===
    print("\nIMPLICATIONS FOR CONVERGENCE:")
    print("─" * 80)
    print("1. int_20+int_21 ∈ {0,...,n-4} is non-increasing on every step.")
    print("   Any path of length > n-4 must have at least one strict decrease.")
    print("2. int_21 ∈ {0,...,n-4} is independently non-increasing.")
    print("3. A cycle must have Δ=0 on EVERY edge for BOTH quantities.")
    print("4. This means: every config in a cycle has int_20+int_21 = const")
    print("   and int_21 = const, hence int_20 = const.")
    print("5. For int_20+int_21 = 0: all interior 2's form a suffix (no exposed 2).")
    print("   On these configs, E3 (mid 2,1,1→0) CANNOT fire,")
    print("   so the only anomalous entries are E1, E2, E4, E5 (all boundary).")
    print("6. REMAINING: prove the 'both-preserved' subgraph is a DAG.")

    # === Count which entries have strict decrease ===
    print(f"\n{'─'*80}")
    print("STRICT DECREASE SUMMARY (T_mid, position j≥3):")
    print("─" * 80)
    for (L, S, R), out in sorted(T_mid.items()):
        if out == S:
            continue
        d_exp2, d_i21, _ = analyze_entry(L, S, R, out, 'T_mid', 'mid')
        dfc = (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))
        markers = []
        if d_exp2 < 0:
            markers.append("exp2↓")
        if d_i21 < 0:
            markers.append("i21↓")
        if d_exp2 == 0 and d_i21 == 0:
            markers.append("PRESERVED")
        desc = ", ".join(markers)
        anom = " [ANOMALOUS]" if dfc > 0 else ""
        print(f"  ({L},{S},{R})→{out}  Δfc={dfc:+d}  {desc}{anom}")

    # Do the same for T_high
    print(f"\n{'─'*80}")
    print("STRICT DECREASE SUMMARY (T_high, position n-2):")
    print("─" * 80)
    for (L, S, R), out in sorted(T_high.items()):
        if out == S:
            continue
        d_exp2, d_i21, _ = analyze_entry(L, S, R, out, 'T_high', 'high')
        dfc = (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))
        markers = []
        if d_exp2 < 0:
            markers.append("exp2↓")
        if d_i21 < 0:
            markers.append("i21↓")
        if d_exp2 == 0 and d_i21 == 0:
            markers.append("PRESERVED")
        desc = ", ".join(markers)
        anom = " [ANOMALOUS]" if dfc > 0 else ""
        print(f"  ({L},{S},{R})→{out}  Δfc={dfc:+d}  {desc}{anom}")


if __name__ == '__main__':
    main()
