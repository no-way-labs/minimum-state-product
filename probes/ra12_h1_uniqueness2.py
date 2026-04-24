#!/usr/bin/env python3
"""
RA12 Part 2: Deeper analysis of forcedSucc_nonGood failure

Key finding from Part 1:
- H-1 uniqueness HOLDS universally (no non-adjacent H-1 pairs in any cycle tested)
- But pre-image uniqueness FAILS (many (p,L,R) contexts have multiple pre-images)
- Therefore NON-GOOD configs at H-1 distance DO map into the good cycle
- forcedSucc_nonGood is FALSE as stated

Now: understand the structure of these "dangerous" non-good configs.
- They are H-1 from some g_k, at position p
- They have f_p(L, v, R) = g_k[p] with v != g_k[p]
- But they have MULTIPLE privileged processors (not just p)
- So move(sys, c, p) = g_k... but p might not be the daemon's choice!

Wait — forcedSucc_nonGood says: if move(sys, c, p) = g_k, then c must be good.
The issue is that c has multiple privileged procs, so p is not "the" mover.
But the STATEMENT is about ANY move at position p, not just the unique mover.

Actually, let me re-read the claim more carefully.
The Lean statement `forcedSucc_nonGood` likely says:
  For any non-good config c and any privileged position p in c,
  move(sys, c, p) is NOT a good config.

Equivalently: if move(sys, c, p) IS a good config, then c IS good.

We found non-good c where move(sys, c, p) = g_k (a good config).
This means forcedSucc_nonGood is FALSE.

But wait — in these cases, c has MULTIPLE privileged procs.
If p is privileged in c, is it really true that move(sys, c, p) = g_k?

Let me verify this more carefully.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system, privileged_set, apply_move


def build_sol3(n):
    ms = [3] * n
    def f_bottom(L, S, R):
        if (S + 1) % 3 == R: return (S - 1) % 3
        return S
    def f_top(L, S, R):
        if L == R and (L + 1) % 3 != S: return (L + 1) % 3
        return S
    def f_middle(L, S, R):
        if (S + 1) % 3 == L: return L
        if (S + 1) % 3 == R: return R
        return S
    fs = [f_bottom] + [f_middle] * (n - 2) + [f_top]
    return ms, fs


def build_cup2(n):
    ms = [2] + [3] * (n - 2) + [2]
    T_bot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    T_low = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    T_mid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    T_high = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    T_top = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    def get_table(pos):
        if pos == 0: return T_bot
        if pos == 1: return T_low
        if pos == n-2: return T_high
        if pos == n-1: return T_top
        return T_mid
    fs = []
    for p in range(n):
        tbl = get_table(p)
        def make_f(t): return lambda L,S,R: t[(L,S,R)]
        fs.append(make_f(tbl))
    return ms, fs


def detailed_check(ms, fs, label):
    """Check: does any non-good config c have a privileged proc p
    such that move(sys, c, p) is a good config?"""
    n = len(ms)
    result = verify_system(ms, fs)
    if not result['valid']:
        print(f"{label}: system not valid, skipping")
        return

    cycle = result['cycle']
    good_set = set(cycle)
    cycle_index = {c: i for i, c in enumerate(cycle)}
    CL = len(cycle)

    # Extract movers
    movers = []
    for idx in range(CL):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % CL]
        for p in range(n):
            if c[p] != c_next[p]:
                movers.append(p)
                break

    all_cfgs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_cfgs if c not in good_set]

    violations = []
    for c in non_good:
        priv = privileged_set(c, fs, ms)
        for p in priv:
            moved = apply_move(c, p, fs, ms)
            if moved in good_set:
                k = cycle_index[moved]
                violations.append((c, p, moved, k, priv))

    print(f"\n{'='*60}")
    print(f"{label}")
    print(f"  Cycle length: {CL}, Good configs: {len(good_set)}")
    print(f"  Non-good configs: {len(non_good)}")
    print(f"  Violations (non-good c, priv p, move(c,p) in good): {len(violations)}")

    if violations:
        print(f"\n  *** forcedSucc_nonGood is FALSE ***")
        print(f"\n  Sample violations:")
        for c, p, moved, k, priv in violations[:15]:
            hd = sum(1 for i in range(n) if c[i] != moved[i])
            # Is the predecessor of g_k at position p?
            prev_k = (k - 1) % CL
            next_k = (k + 1) % CL
            prev_mover = movers[prev_k]
            this_mover = movers[k]
            print(f"    c={c}, priv={priv}, move(c,{p})=g[{k}]={moved}")
            print(f"      H-dist(c, g[{k}]) = {hd}")
            print(f"      moverAt({prev_k})={prev_mover}, moverAt({k})={this_mover}")

            # Check: is p privileged in c AND is moved = g_k?
            # What about: is p the ONLY privileged proc? (i.e., is c single-priv?)
            if len(priv) == 1:
                print(f"      *** SINGLE privileged! This is a hard violation. ***")

        # Count single-priv violations
        single_priv_viol = [v for v in violations if len(v[4]) == 1]
        multi_priv_viol = [v for v in violations if len(v[4]) > 1]
        print(f"\n  Single-priv violations: {len(single_priv_viol)}")
        print(f"  Multi-priv violations: {len(multi_priv_viol)}")

        if single_priv_viol:
            print(f"\n  *** HARD VIOLATIONS (single-priv non-good maps to good): ***")
            for c, p, moved, k, priv in single_priv_viol[:10]:
                print(f"    c={c}, sole priv={p}, move(c,{p})=g[{k}]={moved}")
                # This means c has exactly 1 priv proc, so c SHOULD be good...
                # but it's not in good_set. Why?
                # Because c is on a tail, or c leads outside the cycle
                succ = apply_move(c, p, fs, ms)
                succ_priv = privileged_set(succ, fs, ms)
                print(f"    succ={succ}, succ_priv={succ_priv}")
                if succ in good_set:
                    print(f"    succ IS good (g[{cycle_index[succ]}])")
                    # So c is single-priv, and succ is good.
                    # If c were added to good set, would it break anything?
                    # c -> g_k, then g_k -> g_{k+1}, etc.
                    # But is there something that maps to c?
                    print(f"    This c is on a TAIL into the good cycle!")
        else:
            print(f"\n  All violations are multi-priv (c has ≥2 privileged procs)")
            print(f"  These are 'soft' violations: c is genuinely non-good (multi-priv)")
            print(f"  The daemon could choose to fire p, landing in good cycle")
            print(f"  But the daemon could also choose another privileged proc")
    else:
        print(f"\n  forcedSucc_nonGood HOLDS!")

    return violations


# Test systems
print("=" * 70)
print("DETAILED forcedSucc_nonGood CHECK")
print("=" * 70)

# Sol3 n=5
ms5, fs5 = build_sol3(5)
v5 = detailed_check(ms5, fs5, "Sol3 n=5")

# Sol3 n=7
ms7, fs7 = build_sol3(7)
v7 = detailed_check(ms7, fs7, "Sol3 n=7")

# CUP-2 n=5
ms_c5, fs_c5 = build_cup2(5)
v_c5 = detailed_check(ms_c5, fs_c5, "CUP-2 n=5")

# CUP-2 n=7
ms_c7, fs_c7 = build_cup2(7)
v_c7 = detailed_check(ms_c7, fs_c7, "CUP-2 n=7")

# CUP-2 n=9
ms_c9, fs_c9 = build_cup2(9)
v_c9 = detailed_check(ms_c9, fs_c9, "CUP-2 n=9")


# ── KEY QUESTION: Is there a WEAKER statement that IS true? ──

print("\n" + "=" * 70)
print("ALTERNATIVE: Weaker statements that might be true")
print("=" * 70)

def check_weaker_statements(ms, fs, label):
    """Check weaker alternatives to forcedSucc_nonGood."""
    n = len(ms)
    result = verify_system(ms, fs)
    if not result['valid']:
        return

    cycle = result['cycle']
    good_set = set(cycle)
    CL = len(cycle)

    all_cfgs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_cfgs if c not in good_set]

    # Statement A: For non-good c with EXACTLY ONE priv proc p,
    # move(c, p) is never good.
    # (This is about single-priv non-good configs only)
    stmt_a_violations = 0
    single_priv_nongood = 0
    for c in non_good:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 1:
            single_priv_nongood += 1
            moved = apply_move(c, priv[0], fs, ms)
            if moved in good_set:
                stmt_a_violations += 1

    print(f"\n{label}:")
    print(f"  Statement A (single-priv non-good never maps to good):")
    print(f"    Single-priv non-good configs: {single_priv_nongood}")
    print(f"    Violations: {stmt_a_violations}")

    # Wait — single-priv non-good configs shouldn't exist!
    # If c has exactly 1 priv proc, c should be in good_set (or on a tail to good).
    # The verifier puts ALL configs reachable from the cycle (backward) into good.
    # Actually no — good_set = cycle + tails. And verify_system iteratively removes
    # configs whose successor leaves the closed set. So anything with single priv
    # whose successor is in good_set IS in good_set.
    # So... single-priv non-good configs exist only if their successor is NOT good.
    # But we just checked: move(c, p) is good! So how can c be non-good?

    if stmt_a_violations > 0:
        print(f"    *** This should be IMPOSSIBLE — investigate! ***")
        # Find one and analyze
        for c in non_good:
            priv = privileged_set(c, fs, ms)
            if len(priv) == 1:
                moved = apply_move(c, priv[0], fs, ms)
                if moved in good_set:
                    print(f"    c={c}, priv={priv}, move={moved}")
                    print(f"    moved is good: {moved in good_set}")
                    # Check if c is in good_candidates (single_priv)
                    print(f"    c has 1 priv proc, so c is in single_priv")
                    print(f"    c's successor is in good_set, so c should be in good_set!")
                    print(f"    BUG in verifier or understanding?")
                    break

    # Statement B: For non-good c (multi-priv), no daemon choice leads to
    # a config that is ALSO non-good and single-priv.
    # (Prevents daemon from "promoting" a non-good to the boundary of good)

    # Statement C (convergence reformulation):
    # The non-good configs form a DAG under ALL daemon choices.
    # This is just convergence, which we know holds.

    # Statement D: For the transition at the mover position in the good cycle,
    # the pre-image is exactly {g_{k-1}[p]} (unique predecessor value).
    # We already showed this fails. But maybe it holds at the mover position?
    cycle_idx = {c: i for i, c in enumerate(cycle)}
    movers = []
    for idx in range(CL):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % CL]
        for p in range(n):
            if c[p] != c_next[p]:
                movers.append(p)
                break

    mover_preimage_unique = True
    for k in range(CL):
        gk = cycle[k]
        prev_k = (k - 1) % CL
        p = movers[prev_k]  # mover that produced g_k
        L = gk[(p-1) % n]
        R = gk[(p+1) % n]
        target = gk[p]
        preimages = [v for v in range(ms[p]) if fs[p](L, v, R) == target]
        if len(preimages) > 1:
            mover_preimage_unique = False

    print(f"  Statement D (mover-position pre-image unique): {mover_preimage_unique}")

    # Statement E: The CORRECT formulation for the Lean proof.
    # What we actually need:
    # "In the non-deterministic transition graph, the non-good configs form a DAG"
    # This is exactly convergence, and it holds.
    #
    # For forcedSucc_nonGood specifically: maybe the Lean proof doesn't need it?
    # What does the Lean proof actually need?

    print(f"\n  Key insight: forcedSucc_nonGood is FALSE in general.")
    print(f"  Non-good configs CAN map into the good cycle when they have ≥2 priv procs.")
    print(f"  But convergence still holds because the non-good subgraph has no cycles.")

check_weaker_statements(ms5, fs5, "Sol3 n=5")
check_weaker_statements(ms_c5, fs_c5, "CUP-2 n=5")
check_weaker_statements(ms_c7, fs_c7, "CUP-2 n=7")

# ── Final: what DOES hold about H-1 configs? ──

print("\n" + "=" * 70)
print("FINAL: What does the H-1 structure tell us?")
print("=" * 70)

print("""
FINDINGS:

1. H-1 UNIQUENESS HOLDS in all tested systems:
   If g_j and g_k are at Hamming distance 1, then j = k±1 (mod CL).
   This is because each step changes exactly 1 position (the mover),
   and the cycle visits distinct configs.

   But WHY can't two non-adjacent configs differ at exactly one position?
   Because processor p fires m_p times in the cycle, cycling through
   m_p values. For g_j[p] != g_k[p] with agreement elsewhere,
   the "elsewhere" context must match exactly, which is very constrained.

   The number of H-1 pairs equals CL (one per step), and they're
   all adjacent. At each position p, the number of H-1 pairs
   equals the number of times p fires = m_p.

2. PRE-IMAGE UNIQUENESS FAILS:
   For many (p, L, R) contexts, f_p(L, ·, R) is not injective.
   Multiple values of S map to the same output.

3. forcedSucc_nonGood is FALSE:
   Non-good configs CAN have a privileged proc p such that
   move(sys, c, p) lands in the good cycle.
   These configs always have ≥2 privileged procs (they're multi-priv).

   Single-priv non-good configs whose successor is good are automatically
   included in good_set by the verifier, so single-priv violations
   cannot exist (by construction of the maximal closed set).

4. CORRECT APPROACH for the Lean proof:
   Instead of forcedSucc_nonGood, use CONVERGENCE directly:
   - Non-good configs form a DAG under all daemon choices
   - Every path from a non-good config eventually reaches a good config
   - This is the standard Dijkstra property, already verified

   OR: reformulate as "the good cycle is ATTRACTIVE":
   - Every config eventually reaches the good cycle
   - The good cycle is the unique terminal SCC
""")
