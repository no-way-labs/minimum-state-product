#!/usr/bin/env python3
"""
CONVERGENCE PROOF 21: Anomalous-Decreasing Potential Search
============================================================

KEY OBSERVATION: All 5 anomalous entries decrease specific local counts.

Define Q(c) = #{adjacent pairs (j,j+1) where c[j]=c[(j+1)%n] and c[j] in {0,1}}
         = #(0,0) + #(1,1) adjacent pairs

Analytical check:
  T_bot(0,0,0)->1: ΔQ = -2 (two (0,0) pairs destroyed)
  T_bot(1,1,2)->0: ΔQ = -1 (one (1,1) pair destroyed)
  T_mid(2,1,1)->0: ΔQ = -1 (one (1,1) pair destroyed)
  T_high(1,1,1)->2: ΔQ = -2 (two (1,1) pairs destroyed)
  T_top(2,0,0)->1: ΔQ = 0 or -1 (destroys (0,0) at (n-1,0) = -1)

Wait, T_top: c[n-2]=2, c[n-1]=0, c[0]=0 -> c[n-1]=1.
  Pair (n-2,n-1): (2,0)->(2,1). Neither is same-{0,1}. ΔQ=0.
  Pair (n-1,0): (0,0)->(1,0). Was a (0,0) pair -> Q pair destroyed. ΔQ=-1.
  Total: ΔQ = -1.

So ALL 5 anomalous entries have ΔQ ≤ -1.

Now test: if we use (primary, fc, Ψ) where primary = -Q (decreasing Q ->
increasing -Q -> bad for lex)... or better, use Q as part of a combined potential
that works on ALL edges.

Test candidates:
1. (-Q, fc, Ψ) lex - fails if Q increases on any Δfc≤0 edge
2. (fc - Q, ...) - fc-Q increases on anomalous, unclear on Δfc≤0
3. Q as tiebreaker in (fc, Q, Ψ) or (fc, Ψ, Q)
4. A*fc + B*Q + C*Ψ for some coefficients
5. (fc + Q, Ψ) where fc+Q... unclear
6. (-Q, fc, Ψ) lex with fallback
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import Counter


def frontier_type(a, b):
    if a == b:
        return 0
    return (b - a) % 3


def w1(j, n):
    if j == n - 1:
        return 0
    if j == n - 2:
        return 1
    return j + 1


def w2(j, n):
    if j == n - 1:
        return 0
    if 1 <= j <= n - 2:
        return n - 1 - j
    return n - 1


def psi(c, n):
    total = 0
    for j in range(n):
        ft = frontier_type(c[j], c[(j + 1) % n])
        if ft == 1:
            total += w1(j, n)
        elif ft == 2:
            total += w2(j, n)
    return total


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def Q(c, n):
    """Count adjacent same-value pairs where value in {0,1}."""
    count = 0
    for j in range(n):
        a, b = c[j], c[(j + 1) % n]
        if a == b and a in (0, 1):
            count += 1
    return count


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def classify_entry(L, S, R, out):
    if out == S:
        return "stay"
    if out == L:
        return "copy_L"
    if out == R:
        return "copy_R"
    return "anomalous"


def analyze(n_val):
    ms, fs = build_system(n_val)
    n = n_val
    result = verify_system(ms, fs)
    assert result['valid']

    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_list = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_list)

    print(f"\n{'=' * 70}")
    print(f"n = {n_val}: {len(bad_list)} bad configs")
    print(f"{'=' * 70}")

    # Collect all transitions with metadata
    transitions = []
    for c in bad_list:
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            out = fs[i](L, S, R)
            if out != S:
                lst = list(c)
                lst[i] = out
                succ = tuple(lst)
                if succ in bad_set:
                    dfc = delta_fc(L, S, R, out)
                    cls = classify_entry(L, S, R, out)
                    transitions.append((c, succ, i, dfc, cls))

    n_trans = len(transitions)
    n_anom = sum(1 for _, _, _, _, cls in transitions if cls == "anomalous")
    print(f"  {n_trans} transitions, {n_anom} anomalous")

    # ═══════════════════════════════════════════════════════════
    # Verify Q decreases on ALL anomalous edges
    # ═══════════════════════════════════════════════════════════
    print(f"\n  VERIFY: Q decreases on anomalous edges")
    q_anom_deltas = Counter()
    for c, succ, i, dfc, cls in transitions:
        if cls == "anomalous":
            dq = Q(succ, n) - Q(c, n)
            q_anom_deltas[dq] += 1
    print(f"    ΔQ distribution on anomalous: {dict(sorted(q_anom_deltas.items()))}")
    all_neg = all(d < 0 for d in q_anom_deltas.keys())
    print(f"    ALL ΔQ < 0 on anomalous: {all_neg}")

    # ═══════════════════════════════════════════════════════════
    # Check Q on Δfc≤0 edges
    # ═══════════════════════════════════════════════════════════
    print(f"\n  Q behavior on Δfc≤0 edges:")
    q_fcle0_deltas = Counter()
    for c, succ, i, dfc, cls in transitions:
        if dfc <= 0:
            dq = Q(succ, n) - Q(c, n)
            q_fcle0_deltas[dq] += 1
    print(f"    ΔQ distribution: {dict(sorted(q_fcle0_deltas.items()))}")
    q_increases = sum(v for k, v in q_fcle0_deltas.items() if k > 0)
    print(f"    ΔQ > 0 on {q_increases}/{n_trans - n_anom} Δfc≤0 edges")

    # ═══════════════════════════════════════════════════════════
    # TEST CANDIDATE POTENTIALS
    # ═══════════════════════════════════════════════════════════

    def test_potential(name, phi_func):
        violations = 0
        viol_types = Counter()
        for c, succ, i, dfc, cls in transitions:
            if phi_func(succ) >= phi_func(c):
                violations += 1
                viol_types[cls] += 1
        pct = 100 * violations / n_trans if n_trans else 0
        print(f"    {name}: {violations}/{n_trans} ({pct:.1f}%) "
              f"types={dict(viol_types)}")
        return violations

    def test_lex_potential(name, phi_func):
        """phi_func returns a tuple for lex comparison."""
        violations = 0
        viol_types = Counter()
        for c, succ, i, dfc, cls in transitions:
            if phi_func(succ) >= phi_func(c):
                violations += 1
                viol_types[cls] += 1
        pct = 100 * violations / n_trans if n_trans else 0
        print(f"    {name}: {violations}/{n_trans} ({pct:.1f}%) "
              f"types={dict(viol_types)}")
        return violations

    print(f"\n  SCALAR POTENTIALS:")
    # Negative Q (want to be lex-decreasing, but Q alone won't work)
    test_potential("-Q (neg Q)", lambda c: -Q(c, n))

    # fc + Q: check if it always decreases
    # Anomalous: Δ(fc+Q) = Δfc + ΔQ = (+1 or +2) + (≤-1) = 0 or +1. Hmm...
    test_potential("fc + Q",
                   lambda c: fc(c, n) + Q(c, n))

    # fc - Q: increases on anomalous (Δfc > 0, ΔQ < 0 so -ΔQ > 0)
    test_potential("fc - Q",
                   lambda c: fc(c, n) - Q(c, n))

    # 2*fc + Q: anomalous gives Δ = 2*Δfc + ΔQ ≥ 2*1 + (-2) = 0. Bad.
    # Hmm but the max ΔQ = -1 for Δfc=+1, -2 for some Δfc=+2 entries
    test_potential("2*fc + Q",
                   lambda c: 2 * fc(c, n) + Q(c, n))

    # ψ - α*Q for various α
    for alpha in [1, 2, 3, 5, 10]:
        test_potential(f"Ψ - {alpha}*Q",
                       lambda c, a=alpha: psi(c, n) - a * Q(c, n))

    print(f"\n  LEX POTENTIALS:")

    # (-Q, fc, Ψ) lex
    test_lex_potential("(-Q, fc, Ψ) lex",
                       lambda c: (-Q(c, n), fc(c, n), psi(c, n)))

    # (fc, -Q, Ψ) lex
    test_lex_potential("(fc, -Q, Ψ) lex",
                       lambda c: (fc(c, n), -Q(c, n), psi(c, n)))

    # (fc, Ψ, -Q) lex
    test_lex_potential("(fc, Ψ, -Q) lex",
                       lambda c: (fc(c, n), psi(c, n), -Q(c, n)))

    # (-Q, Ψ) lex
    test_lex_potential("(-Q, Ψ) lex",
                       lambda c: (-Q(c, n), psi(c, n)))

    # (fc - Q, Ψ) lex
    test_lex_potential("(fc - Q, Ψ) lex",
                       lambda c: (fc(c, n) - Q(c, n), psi(c, n)))

    # (fc + Q, Ψ) lex — anomalous: Δ(fc+Q) = Δfc+ΔQ. If this is 0: need ΔΨ < 0.
    # But anomalous have ΔΨ ≥ 0... hmm.
    test_lex_potential("(fc + Q, Ψ) lex",
                       lambda c: (fc(c, n) + Q(c, n), psi(c, n)))

    # ═══════════════════════════════════════════════════════════
    # MORE EXOTIC: define Q22 = #(2,2) pairs, Z = #(0) values, etc.
    # ═══════════════════════════════════════════════════════════
    def Q22(c):
        return sum(1 for j in range(n) if c[j] == c[(j+1)%n] == 2)

    def n_zeros(c):
        return sum(1 for v in c if v == 0)

    def n_ones(c):
        return sum(1 for v in c if v == 1)

    def n_twos(c):
        return sum(1 for v in c if v == 2)

    def value_sum(c):
        return sum(c)

    print(f"\n  MORE EXOTIC POTENTIALS:")

    # (fc, Ψ, -Q22) — Q22 might behave differently
    test_lex_potential("(fc, Ψ, -Q22) lex",
                       lambda c: (fc(c, n), psi(c, n), -Q22(c)))

    # Frontier-weighted: -Σ w(j)*[c[j]=c[j+1] and c[j]∈{0,1}]
    def Qw(c):
        total = 0
        for j in range(n):
            a, b = c[j], c[(j + 1) % n]
            if a == b and a in (0, 1):
                total += w1(j, n) + w2(j, n)
        return total

    test_lex_potential("(-Qw, fc, Ψ) lex",
                       lambda c: (-Qw(c), fc(c, n), psi(c, n)))

    # ═══════════════════════════════════════════════════════════
    # KEY: Check (fc + Q, fc, Ψ) lex — or (M, fc, Ψ) where M = n - fc + Q
    # = number of same-value pairs where value in {0,1,2} gives n-fc, plus Q
    # ═══════════════════════════════════════════════════════════

    # The match count M = n - fc = #same-value pairs (all values)
    # M + Q = (n-fc) + Q. On anomalous: ΔM = -Δfc ≤ -1, ΔQ ≤ -1, so Δ(M+Q) ≤ -2.
    # On Δfc≤0: ΔM = -Δfc ≥ 0, ΔQ any.
    # -(M+Q) strictly increases on anomalous (since M+Q decreases).
    # -(M+Q) on Δfc≤0: -(ΔM + ΔQ) = Δfc - ΔQ.
    #   If ΔQ ≤ Δfc ≤ 0: then Δfc - ΔQ ≥ 0. -(M+Q) increases or stays. BAD.

    # Let's try: (-(M+Q), fc, Ψ) lex = (fc - n - Q, fc, Ψ) lex
    test_lex_potential("(-(M+Q), fc, Ψ) lex",
                       lambda c: (fc(c, n) - n - Q(c, n), fc(c, n), psi(c, n)))

    # Actually: -(M+Q) = -(n-fc+Q) = fc-n-Q. On anomalous: Δ = Δfc - ΔQ ≥ 1-(-1) = 2.
    # Hmm that INCREASES on anomalous. Wrong direction! Let me think...
    # We want -(M+Q) to DECREASE. -(M+Q) = fc - n - Q. Δ = Δfc - ΔQ.
    # On anomalous: Δfc > 0 and ΔQ < 0, so Δ = Δfc - ΔQ > 0. INCREASES. Bad.
    # We want M+Q to increase (so -(M+Q) decreases).
    # M+Q = n-fc+Q. Δ = -Δfc + ΔQ. On anomalous: -Δfc + ΔQ ≤ -1 + (-1) = -2. DECREASES.
    # So M+Q DECREASES on anomalous. That means -(M+Q) INCREASES on anomalous. Bad for lex first comp.

    # Flip: (M+Q, ...) as first component. Strictly decreasing on anomalous = M+Q decreases ✓.
    # On Δfc≤0: Δ(M+Q) = -Δfc + ΔQ.
    #   If Δfc=0: Δ(M+Q) = ΔQ. Can be positive or negative.
    #   If Δfc<0: Δ(M+Q) = -Δfc + ΔQ = |Δfc| + ΔQ. This is positive if |Δfc| > |ΔQ| when ΔQ<0.

    # (M+Q, fc, Ψ): on anomalous, M+Q strictly decreases -> lex first comp decreases -> good.
    # On Δfc≤0 with M+Q decrease: fine, lex first comp decreases.
    # On Δfc≤0 with M+Q increase: BAD, lex first comp increases.

    test_lex_potential("(M+Q, fc, Ψ) lex (M=n-fc)",
                       lambda c: (n - fc(c, n) + Q(c, n), fc(c, n), psi(c, n)))

    # ═══════════════════════════════════════════════════════════
    # SYSTEMATIC: try all (a*fc + b*Q + c*Ψ) for small a,b,c
    # ═══════════════════════════════════════════════════════════
    print(f"\n  SYSTEMATIC LINEAR SEARCH:")
    best_v = n_trans
    best_params = None
    for a in range(-5, 6):
        for b in range(-5, 6):
            for c_coeff in range(-5, 6):
                if a == 0 and b == 0 and c_coeff == 0:
                    continue
                v = 0
                for c_cfg, succ, i, dfc, cls in transitions:
                    phi_c = a * fc(c_cfg, n) + b * Q(c_cfg, n) + c_coeff * psi(c_cfg, n)
                    phi_s = a * fc(succ, n) + b * Q(succ, n) + c_coeff * psi(succ, n)
                    if phi_s >= phi_c:
                        v += 1
                if v < best_v:
                    best_v = v
                    best_params = (a, b, c_coeff)
    print(f"    Best linear: a*fc + b*Q + c*Ψ")
    print(f"    (a,b,c) = {best_params}, violations = {best_v}/{n_trans}")

    # ═══════════════════════════════════════════════════════════
    # SYSTEMATIC LEX: (a*fc + b*Q, c*fc + d*Q + e*Ψ)
    # First component must strictly decrease on anomalous.
    # On anomalous: Δ(a*fc + b*Q) = a*Δfc + b*ΔQ.
    # Need a*Δfc + b*ΔQ < 0 for all anomalous.
    # Δfc ∈ {1,2}, ΔQ ∈ {-1,-2}.
    # Need a*1 + b*(-1) < 0 → a < b
    # And a*2 + b*(-2) < 0 → a < b (same constraint!)
    # And a*1 + b*(-2) < 0 → a < 2b
    # And a*2 + b*(-1) < 0 → 2a < b
    # So need 2a < b (strongest) and a < b.
    # ═══════════════════════════════════════════════════════════
    print(f"\n  TWO-LEVEL LEX SEARCH:")
    # First level: a*fc + b*Q where 2a < b
    # Anomalous: Δ(first) < 0 guaranteed if 2a < b and (a,b) satisfies all combos.
    # Wait, anomalous has Δfc ∈ {+1, +2} and ΔQ ∈ {-1, -2}.
    # The combos (Δfc, ΔQ) are:
    #   T_bot(0,0,0)->1: Δfc=+2, ΔQ=-2 → need 2a-2b < 0 → a < b
    #   T_bot(1,1,2)->0: Δfc=+1, ΔQ=-1 → need a-b < 0 → a < b
    #   T_mid(2,1,1)->0: Δfc=+1, ΔQ=-1 → need a-b < 0 → a < b
    #   T_high(1,1,1)->2: Δfc=+2, ΔQ=-2 → need 2a-2b < 0 → a < b
    #   T_top(2,0,0)->1: Δfc=+1, ΔQ=-1 → need a-b < 0 → a < b
    # So just need a < b! (with b > 0)

    # Second level: need to handle edges where first level stays constant.
    # Try (fc, Ψ) as second level via lex.

    best_v2 = n_trans
    best_params2 = None
    for a in range(0, 6):
        for b in range(a + 1, a + 6):
            # First level: a*fc + b*Q
            # On anomalous: guaranteed to decrease (a < b)
            # On Δfc≤0: a*Δfc + b*ΔQ. Could be positive, zero, or negative.
            # When first level stays same: check (fc, Ψ) lex.
            v = 0
            for c_cfg, succ, _, _, _ in transitions:
                lv1_c = a * fc(c_cfg, n) + b * Q(c_cfg, n)
                lv1_s = a * fc(succ, n) + b * Q(succ, n)
                if lv1_s < lv1_c:
                    continue  # Good, first level decreases
                elif lv1_s == lv1_c:
                    # Check (fc, Ψ) as tiebreaker
                    pair_c = (fc(c_cfg, n), psi(c_cfg, n))
                    pair_s = (fc(succ, n), psi(succ, n))
                    if pair_s < pair_c:
                        continue  # Good
                    v += 1
                else:
                    v += 1  # First level INCREASED
            if v < best_v2:
                best_v2 = v
                best_params2 = (a, b)

    if best_params2:
        a, b = best_params2
        print(f"    Best 2-level: ({a}*fc + {b}*Q, fc, Ψ)")
        print(f"    Violations = {best_v2}/{n_trans}")
        if best_v2 > 0:
            # Show examples
            v_count = 0
            for c_cfg, succ, i, dfc, cls in transitions:
                lv1_c = a * fc(c_cfg, n) + b * Q(c_cfg, n)
                lv1_s = a * fc(succ, n) + b * Q(succ, n)
                if lv1_s < lv1_c:
                    continue
                elif lv1_s == lv1_c:
                    pair_c = (fc(c_cfg, n), psi(c_cfg, n))
                    pair_s = (fc(succ, n), psi(succ, n))
                    if pair_s < pair_c:
                        continue
                v_count += 1
                if v_count <= 5:
                    print(f"      {c_cfg}→{succ}: L1 {lv1_c}→{lv1_s}, "
                          f"fc {fc(c_cfg,n)}→{fc(succ,n)}, "
                          f"Q {Q(c_cfg,n)}→{Q(succ,n)}, "
                          f"Ψ {psi(c_cfg,n)}→{psi(succ,n)}, "
                          f"type={cls}")

    return best_v2


if __name__ == '__main__':
    all_results = {}
    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        v = analyze(nv)
        all_results[nv] = v

    print(f"\n{'=' * 70}")
    print(f"SUMMARY")
    print(f"{'=' * 70}")
    for nv, v in sorted(all_results.items()):
        status = "ZERO!" if v == 0 else f"{v} violations"
        print(f"  n={nv}: {status}")
