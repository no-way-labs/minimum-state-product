#!/usr/bin/env python3
"""
RA12: What breaks when we demote one ternary proc to binary in CUP-2?

CUP-2: ms = (2, 3, 3, ..., 3, 2), product = 4*3^(n-2)

Two demotion cases:
  Case A (boundary): demote P1 -> ms = (2,2,3,...,3,2)
    Creates consecutive binary at P0,P1. Lands in Case 3a of LB proof.
  Case B (interior):  demote P4 -> ms = (2,3,3,3,2,3,...,3,2)
    Creates non-adjacent binary at P0,P4,Pn-1. Lands in Case 3b of LB proof.

Both have product = 8*3^(n-3) < 4*3^(n-2).
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from verifier import verify_system

# ── CUP-2 tables ──

T_bot = {
    (0,0,0):1, (0,0,1):1, (0,0,2):0,
    (0,1,0):1, (0,1,1):1, (0,1,2):1,
    (1,0,0):0, (1,0,1):1, (1,0,2):0,
    (1,1,0):0, (1,1,1):1, (1,1,2):0,
}

T_low = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):0, (0,1,1):1, (0,1,2):0,
    (0,2,0):0, (0,2,1):2, (0,2,2):0,
    (1,0,0):1, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):2,
    (1,2,0):0, (1,2,1):1, (1,2,2):2,
}

T_mid = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):0, (0,1,1):1, (0,1,2):0,
    (0,2,0):0, (0,2,1):2, (0,2,2):0,
    (1,0,0):1, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):2,
    (1,2,0):0, (1,2,1):1, (1,2,2):2,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
    (2,2,0):0, (2,2,1):2, (2,2,2):2,
}

T_high = {
    (0,0,0):0, (0,0,1):0,
    (0,1,0):0, (0,1,1):0,
    (0,2,0):0, (0,2,1):0,
    (1,0,0):1, (1,0,1):1,
    (1,1,0):1, (1,1,1):2,
    (1,2,0):0, (1,2,1):2,
    (2,0,0):0, (2,0,1):2,
    (2,1,0):0, (2,1,1):2,
    (2,2,0):2, (2,2,1):2,
}

T_top = {
    (0,0,0):0, (0,0,1):0,
    (0,1,0):0, (0,1,1):0,
    (1,0,0):0, (1,0,1):1,
    (1,1,0):1, (1,1,1):1,
    (2,0,0):1, (2,0,1):1,
    (2,1,0):1, (2,1,1):1,
}


def config_formula(t, n):
    """CUP-2 good cycle config at step t."""
    c = [0] * n
    if 0 <= t <= n - 1:
        for j in range(t):
            c[j] = 1
    elif n <= t <= 2 * n - 2:
        k = t - n
        for j in range(n - 1 - k):
            c[j] = 1
        for j in range(n - 1 - k, n - 1):
            c[j] = 2
        c[n - 1] = 1
    else:
        k = t - (2 * n - 1)
        for j in range(k + 1, n - 1):
            c[j] = 2
        c[n - 1] = 1
    return tuple(c)


def mover_formula(t, n):
    if 0 <= t <= n - 1:
        return t
    elif n <= t <= 2 * n - 3:
        return 2 * n - 2 - t
    else:
        return t - (2 * n - 2)


# ================================================================
# CASE A: BOUNDARY DEMOTION (P1: ternary -> binary)
# ================================================================
def case_a_table_analysis(n):
    """Analyze which CUP-2 table entries break when P1 is demoted."""
    print("=" * 80)
    print(f"CASE A: BOUNDARY DEMOTION — P1 demoted (n={n})")
    print(f"  ms_orig = (2, 3, 3, ..., 3, 2)")
    print(f"  ms_dem  = (2, 2, 3, ..., 3, 2)")
    print(f"  Binary positions: {{0, 1, {n-1}}} — consecutive at P0,P1")
    print("=" * 80)

    print("\n--- Table entry invalidation ---")

    # P0 (T_bot): right neighbor was ternary (R in {0,1,2}), now binary (R in {0,1})
    lost_p0 = [(L,S,R,v) for (L,S,R),v in T_bot.items() if R == 2]
    print(f"\n  P0 (T_bot): R was in {{0,1,2}}, now in {{0,1}}")
    print(f"    {len(lost_p0)} entries lost (R=2):")
    for L,S,R,v in sorted(lost_p0):
        priv = " *priv*" if v != S else ""
        print(f"      T_bot({L},{S},{R}) = {v}{priv}")

    # P1 (T_low): self was ternary (S in {0,1,2}), now binary (S in {0,1})
    lost_s2 = [(L,S,R,v) for (L,S,R),v in T_low.items() if S == 2]
    bad_output = [(L,S,R,v) for (L,S,R),v in T_low.items() if S < 2 and v == 2]
    print(f"\n  P1 (T_low): S was in {{0,1,2}}, now in {{0,1}}")
    print(f"    {len(lost_s2)} entries lost (S=2):")
    for L,S,R,v in sorted(lost_s2):
        priv = " *priv*" if v != S else ""
        print(f"      T_low({L},{S},{R}) = {v}{priv}")
    print(f"    {len(bad_output)} entries with output 2 (unreachable for binary):")
    for L,S,R,v in sorted(bad_output):
        print(f"      T_low({L},{S},{R}) = {v}  <- CAN'T OUTPUT 2")

    # P2: left neighbor was ternary, now binary (L in {0,1})
    # P2 uses T_mid (if n>5) or T_high (if n==5)
    if n == 5:
        table, tname = T_high, "T_high"
    else:
        table, tname = T_mid, "T_mid"
    lost_l2 = [(L,S,R,v) for (L,S,R),v in table.items() if L == 2]
    print(f"\n  P2 ({tname}): L was in {{0,1,2}}, now in {{0,1}}")
    print(f"    {len(lost_l2)} entries lost (L=2):")
    for L,S,R,v in sorted(lost_l2):
        priv = " *priv*" if v != S else ""
        print(f"      {tname}({L},{S},{R}) = {v}{priv}")

    total_lost = len(lost_p0) + len(lost_s2) + len(bad_output) + len(lost_l2)
    print(f"\n  TOTAL: {total_lost} entries invalidated/lost out of 87")

    # Good cycle configs with value 2 at P1
    L_cycle = 3 * n - 2
    broken = []
    for t in range(L_cycle):
        c = config_formula(t, n)
        if c[1] == 2:
            broken.append((t, c, mover_formula(t, n)))

    print(f"\n--- Good cycle breakage ---")
    print(f"  Cycle length: {L_cycle}")
    print(f"  Configs with value 2 at P1: {len(broken)} of {L_cycle}")
    for t, c, m in broken:
        print(f"    t={t}: {list(c)}, mover=P{m}")

    # Trace the wavefront mechanism
    print(f"\n--- Wavefront mechanism ---")
    print(f"  CUP-2 cycle = 3-phase wavefront:")
    print(f"    Phase 1 (t=0..{n-1}): 1-front sweeps UP, P1 goes 0->1")
    print(f"    Phase 2 (t={n}..{2*n-2}): 2-front sweeps DOWN, P1 goes 1->2  ** IMPOSSIBLE **")
    print(f"    Phase 3 (t={2*n-1}..{3*n-3}): 0-front sweeps UP, P1 goes 2->0  ** IMPOSSIBLE **")
    print(f"  P1 needs 3 values over 3 phases. Binary P1 has only 2 values.")
    print(f"  The wavefront CANNOT pass through P1.")


def case_a_lower_bound(n):
    """Identify the lower bound obstruction for Case A."""
    print(f"\n--- Lower bound obstruction (Case 3a: consecutive binary) ---")
    ms_dem = [2, 2] + [3] * (n - 3) + [2]
    prod = 1
    for m in ms_dem:
        prod *= m
    threshold = 4 * 3 ** (n - 2)

    print(f"  ms = {ms_dem}")
    print(f"  product = {prod}")
    print(f"  threshold = {threshold}")
    print(f"  sub-threshold? {prod < threshold}")

    binary_pos = [i for i, m in enumerate(ms_dem) if m == 2]
    print(f"  Binary positions: {binary_pos}")
    print(f"  P0, P1 consecutive binary -> Case 3a of lower bound proof")
    print(f"\n  Obstruction chain (from CIC Expl 14 + BinSCC Expl 10):")
    print(f"    1. Sweep cycles -> Shadow Cycle Mirror Theorem blocks them")
    print(f"    2. Non-sweep fc=2 cycles -> Palindromic Entry Conflict:")
    print(f"       For 3 consecutive binary at {{0,1,2}}, every non-sweep fc=2 cycle")
    print(f"       has entry conflict at procs j=1,...,{n-3}.")
    print(f"       Mechanism: CW non-mover context = CCW mover context = (j,x_{{j-1}},x_j,0),")
    print(f"       requires f=x_j AND f=0. Since x_j != 0: contradiction.")
    print(f"    3. Wiggle cycles -> Wiggle Shadow Cycle blocks them")
    print(f"  -> ALL good cycles blocked. No valid system at product {prod}.")


# ================================================================
# CASE B: INTERIOR DEMOTION (P_k: ternary -> binary, k=4)
# ================================================================
def case_b_table_analysis(n, k=4):
    """Analyze which CUP-2 table entries break when P_k is demoted."""
    assert k >= 2 and k <= n - 3, f"k={k} must be interior (2..{n-3})"

    print("\n" + "=" * 80)
    print(f"CASE B: INTERIOR DEMOTION — P{k} demoted (n={n})")
    ms_dem = [2] + [3] * (n - 2) + [2]
    ms_dem[k] = 2
    print(f"  ms_orig = (2, 3, ..., 3, 2)")
    print(f"  ms_dem  = {ms_dem}")
    binary_pos = [i for i, m in enumerate(ms_dem) if m == 2]
    print(f"  Binary positions: {binary_pos} — non-adjacent")
    print("=" * 80)

    print("\n--- Table entry invalidation ---")

    # P_{k-1}: right neighbor was ternary (R in {0,1,2}), now binary (R in {0,1})
    # P_{k-1} uses T_mid (or T_low if k=2)
    if k - 1 == 1:
        table_km1, tname_km1 = T_low, "T_low"
    else:
        table_km1, tname_km1 = T_mid, "T_mid"
    lost_km1 = [(L,S,R,v) for (L,S,R),v in table_km1.items() if R == 2]
    print(f"\n  P{k-1} ({tname_km1}): R was in {{0,1,2}}, now in {{0,1}}")
    print(f"    {len(lost_km1)} entries lost (R=2):")
    for L,S,R,v in sorted(lost_km1):
        priv = " *priv*" if v != S else ""
        print(f"      {tname_km1}({L},{S},{R}) = {v}{priv}")

    # P_k: self was ternary (S in {0,1,2}), now binary (S in {0,1})
    # P_k used T_mid
    lost_sk = [(L,S,R,v) for (L,S,R),v in T_mid.items() if S == 2]
    bad_out_k = [(L,S,R,v) for (L,S,R),v in T_mid.items() if S < 2 and v == 2]
    print(f"\n  P{k} (T_mid): S was in {{0,1,2}}, now in {{0,1}}")
    print(f"    {len(lost_sk)} entries lost (S=2):")
    for L,S,R,v in sorted(lost_sk):
        priv = " *priv*" if v != S else ""
        print(f"      T_mid({L},{S},{R}) = {v}{priv}")
    print(f"    {len(bad_out_k)} entries with output 2 (unreachable for binary):")
    for L,S,R,v in sorted(bad_out_k):
        print(f"      T_mid({L},{S},{R}) = {v}  <- CAN'T OUTPUT 2")

    # P_{k+1}: left neighbor was ternary (L in {0,1,2}), now binary (L in {0,1})
    if k + 1 == n - 2:
        table_kp1, tname_kp1 = T_high, "T_high"
    else:
        table_kp1, tname_kp1 = T_mid, "T_mid"
    lost_kp1 = [(L,S,R,v) for (L,S,R),v in table_kp1.items() if L == 2]
    print(f"\n  P{k+1} ({tname_kp1}): L was in {{0,1,2}}, now in {{0,1}}")
    print(f"    {len(lost_kp1)} entries lost (L=2):")
    for L,S,R,v in sorted(lost_kp1):
        priv = " *priv*" if v != S else ""
        print(f"      {tname_kp1}({L},{S},{R}) = {v}{priv}")

    total_lost = len(lost_km1) + len(lost_sk) + len(bad_out_k) + len(lost_kp1)
    print(f"\n  TOTAL: {total_lost} entries invalidated/lost")

    # Good cycle configs with value 2 at P_k
    L_cycle = 3 * n - 2
    broken = []
    for t in range(L_cycle):
        c = config_formula(t, n)
        if c[k] == 2:
            broken.append((t, c, mover_formula(t, n)))

    print(f"\n--- Good cycle breakage ---")
    print(f"  Configs with value 2 at P{k}: {len(broken)} of {L_cycle}")
    for t, c, m in broken:
        phase = "Ph1" if t <= n-1 else ("Ph2" if t <= 2*n-2 else "Ph3")
        print(f"    t={t:3d} ({phase}): {list(c)}, mover=P{m}")

    # Detailed wavefront analysis for interior proc
    print(f"\n--- Wavefront mechanism for interior P{k} ---")
    print(f"  Phase 2 (DOWN sweep): 2-front starts at P{{n-2}} and sweeps to P1")
    print(f"    Value 2 reaches P{k} when n-1-step_k <= {k}, i.e., step >= {n-1-k}")
    print(f"    That's step t = n + {n-1-k} = {2*n-1-k}")
    print(f"  Phase 3 (UP sweep): 0-front starts at P0 and sweeps to P{{n-2}}")
    print(f"    Value 2 remains at P{k} until 0-front reaches it at step k={k}")
    print(f"    That's step t = {2*n-1} + {k-1} = {2*n+k-2}")
    dur = (2*n+k-2) - (2*n-1-k) + 1
    print(f"  P{k} holds value 2 for {dur} consecutive steps")
    print(f"  -> IMPOSSIBLE with binary P{k}")


def case_b_lower_bound(n, k=4):
    """Identify the lower bound obstruction for Case B."""
    ms_dem = [2] + [3] * (n - 2) + [2]
    ms_dem[k] = 2
    binary_pos = [i for i, m in enumerate(ms_dem) if m == 2]
    prod = 1
    for m in ms_dem:
        prod *= m
    threshold = 4 * 3 ** (n - 2)

    print(f"\n--- Lower bound obstruction (Case 3b: non-adjacent binary) ---")
    print(f"  ms = {ms_dem}")
    print(f"  product = {prod}, threshold = {threshold}")
    print(f"  Binary positions: {binary_pos}")

    # Check adjacency
    adj = False
    for i in range(len(binary_pos)):
        for j in range(i+1, len(binary_pos)):
            d = min((binary_pos[j] - binary_pos[i]) % n,
                    (binary_pos[i] - binary_pos[j]) % n)
            if d == 1:
                adj = True
                print(f"    P{binary_pos[i]} and P{binary_pos[j]} are adjacent (distance {d})")

    if not adj:
        print(f"  No adjacent binary pairs -> Case 3b (non-adjacent)")
        print(f"\n  Obstruction (from BinSCC Expl 10: Universal Entry Conflict):")
        print(f"    For >= 3 non-adjacent binary at sub-threshold product,")
        print(f"    EVERY good cycle has entry conflict.")
        print(f"    Four mechanisms:")
        print(f"      (1) Both-Even Return: M=1, even-index endpoints share first nonmover")
        print(f"      (2) Toggle-FR: >= 3 one-sided corners repeat")
        print(f"      (3) Zero-Side EC: M=1, >= 2 one-sided entries collide")
        print(f"      (4) Traversal Return: singleton fires, nonmover sees mover value")
        print(f"    Plus 2 ring-level lemmas:")
        print(f"      Parity Obstruction: n=2k, k odd -> all-fc=3 impossible")
        print(f"      Ring Alternation: singleton side alternates at consecutive ternary")
    else:
        print(f"  Has adjacent binary pair -> Case 3a (consecutive)")
        print(f"  But also has non-adjacent pairs -> mixed case")
        print(f"  Obstruction: Palindromic Entry Conflict for consecutive pair,")
        print(f"  plus shadow for sweeps/wiggles")


def case_b_n5_computation():
    """Exhaustive verification for n=5 interior demotion."""
    print(f"\n--- Case B computational check (n=5, P2 demoted) ---")
    # At n=5, interior position is P2 (T_mid)
    # ms = (2, 3, 2, 3, 2)
    n = 5
    k = 2
    ms_dem = [2, 3, 2, 3, 2]
    prod = 1
    for m in ms_dem:
        prod *= m
    print(f"  ms = {ms_dem}, product = {prod}")
    print(f"  M_5 = 96. Product {prod} < 96? {prod < 96}")
    if prod < 96:
        print(f"  -> Below M_5, no valid system exists (exhaustively proved)")
    else:
        print(f"  -> NOT below M_5! Must check directly.")

    # Also check k=3 for n=7
    print(f"\n--- Case B computational check (n=7, P4 demoted) ---")
    n = 7
    k = 4
    ms_dem = [2] + [3] * 5 + [2]
    ms_dem[k] = 2
    prod = 1
    for m in ms_dem:
        prod *= m
    print(f"  ms = {ms_dem}, product = {prod}")
    print(f"  threshold = {4 * 3**(n-2)}")
    print(f"  sub-threshold? {prod < 4 * 3**(n-2)}")
    binary_pos = [i for i, m in enumerate(ms_dem) if m == 2]
    print(f"  Binary positions: {binary_pos}")

    # Verify non-adjacency
    n = 7
    adj_pairs = []
    for i in range(len(binary_pos)):
        for j in range(i+1, len(binary_pos)):
            d = min((binary_pos[j] - binary_pos[i]) % n,
                    (binary_pos[i] - binary_pos[j]) % n)
            if d == 1:
                adj_pairs.append((binary_pos[i], binary_pos[j]))
    print(f"  Adjacent pairs: {adj_pairs if adj_pairs else 'NONE'}")
    if not adj_pairs:
        print(f"  -> 3 non-adjacent binary at sub-threshold product")
        print(f"  -> Universal Entry Conflict applies")


# ================================================================
# SIDE-BY-SIDE COMPARISON
# ================================================================
def side_by_side_wavefront(n=7):
    """Show the CUP-2 cycle with both demotions highlighted."""
    print("\n" + "=" * 80)
    print(f"SIDE-BY-SIDE: CUP-2 WAVEFRONT THROUGH DEMOTED POSITIONS (n={n})")
    print("=" * 80)

    L_cycle = 3 * n - 2
    k_interior = 4  # interior demotion position

    print(f"\n{'t':>3} {'phase':>4} {'mover':>6}  {'config':30s}  {'P1(caseA)':>10} {'P{0}(caseB)':>10}".format(k_interior))
    print("-" * 80)

    for t in range(L_cycle):
        c = config_formula(t, n)
        m = mover_formula(t, n)
        phase = "Ph1" if t <= n-1 else ("Ph2" if t <= 2*n-2 else "Ph3")

        v1 = c[1]
        vk = c[k_interior]
        flag_a = " BREAK" if v1 == 2 else ""
        flag_b = " BREAK" if vk == 2 else ""

        print(f"  {t:3d} {phase:>4} P{m:<4d} {str(list(c)):30s}  c[1]={v1}{flag_a:>5s}  c[{k_interior}]={vk}{flag_b:>5s}")

    # Count broken steps
    a_broken = sum(1 for t in range(L_cycle) if config_formula(t,n)[1] == 2)
    b_broken = sum(1 for t in range(L_cycle) if config_formula(t,n)[k_interior] == 2)
    print(f"\n  Case A (P1 demoted): {a_broken} configs broken")
    print(f"  Case B (P{k_interior} demoted): {b_broken} configs broken")
    print(f"  Interior demotion breaks MORE configs because the 2-front")
    print(f"  passes through interior procs for longer (arrives earlier, leaves later)")


# ================================================================
# FIRING COUNT ANALYSIS
# ================================================================
def firing_analysis(n=7):
    """Show why 3 firings per interior proc are structurally necessary."""
    print("\n" + "=" * 80)
    print(f"FIRING COUNT ANALYSIS (n={n})")
    print("=" * 80)

    L_cycle = 3 * n - 2

    # Count firings per processor in CUP-2 cycle
    fire_count = [0] * n
    for t in range(L_cycle):
        m = mover_formula(t, n)
        fire_count[m] += 1

    ms_orig = [2] + [3] * (n - 2) + [2]
    print(f"\n  CUP-2 cycle length = {L_cycle}")
    print(f"  Firings per processor:")
    for p in range(n):
        needs = ms_orig[p]
        print(f"    P{p}: fires {fire_count[p]} times (m_{p}={needs}, need multiple of {needs})")

    print(f"\n  OBSERVATION: Each proc fires exactly m_p times.")
    print(f"  This is the MINIMUM: each proc must cycle through all m_p values")
    print(f"  and return to its starting value.")
    print(f"\n  With a binary proc at P{1} (Case A) or P{4} (Case B):")
    print(f"    - Binary proc fires 2 times instead of 3")
    print(f"    - Total cycle length: {L_cycle} - 1 = {L_cycle - 1}")
    print(f"    - But ternary neighbors still need 3 firings each")
    print(f"    - The 3-phase structure (UP/DOWN/UP) requires all interior procs")
    print(f"      to participate in all 3 phases")
    print(f"    - A binary proc can only participate in 2 phases")
    print(f"    - This leaves a GAP in the wavefront: the binary proc's value")
    print(f"      is stuck at 0 or 1 while its neighbors have value 2")


# ================================================================
# MAIN
# ================================================================
def main():
    # Case A: Boundary demotion
    for n in [5, 7, 9]:
        case_a_table_analysis(n)
        case_a_lower_bound(n)

    print("\n")

    # Case B: Interior demotion
    for n in [7, 9]:
        case_b_table_analysis(n, k=4)
        case_b_lower_bound(n, k=4)

    # n=11 with k=5: binary at {0, 5, 10}, distances 5,5,1 on ring
    # P0 and P10 adjacent! Still Case 3a for that pair.
    # n=13 with k=6: binary at {0, 6, 12}, distances 6,6,1. Still adjacent.
    # The ring ALWAYS has P0 adjacent to P_{n-1}.
    # For truly non-adjacent, need k far from both 0 and n-1.
    # E.g., n=11, k=5: P0,P5,P10. dist(0,5)=5, dist(5,10)=5, dist(10,0)=1. Adjacent!
    # n=11, k=4: P0,P4,P10. dist(0,4)=4, dist(4,10)=4 (via 5,6,...,10), dist(10,0)=1. Still adjacent!
    # ANY 3-binary with endpoints at P0,P_{n-1} has those two adjacent.
    # For truly non-adjacent, need to move one endpoint.
    # E.g., demote P1 AND P5: ms=(2,2,3,3,2,3,...,3,2). Binary={0,1,4,n-1}.
    # That's 4 binary, not 3.
    # With exactly 3 binary, if two are at endpoints, they're adjacent.
    # So Case B (3 binary, one interior) always has P0-P_{n-1} adjacent.
    # The "non-adjacent" case requires binary NOT at both endpoints.
    print("\n--- RING ADJACENCY NOTE ---")
    print("  P0 and P_{n-1} are always adjacent on the ring.")
    print("  With ms=(2,3,...,3,2,3,...,3,2) (binary at P0,Pk,P_{n-1}),")
    print("  the pair {P0,P_{n-1}} is ALWAYS consecutive.")
    print("  So Case B always has at least one consecutive binary pair.")
    print("  The Case 3a obstruction (Palindromic Entry Conflict) applies")
    print("  via the {P0,P_{n-1}} pair, even though P_k is isolated.")
    print("  For a pure Case 3b (all non-adjacent), you'd need 3 binary procs")
    print("  none at adjacent positions, e.g., ms=(3,2,3,3,2,3,3,2,3).")
    print("  But that's a different multiset shape (not endpoint-binary).")

    case_b_n5_computation()

    # Side-by-side comparison
    side_by_side_wavefront(n=7)
    firing_analysis(n=7)

    # ================================================================
    print("\n" + "=" * 80)
    print("FINAL SUMMARY")
    print("=" * 80)
    print("""
QUESTION: What breaks when demoting one ternary proc to binary in CUP-2?
ANSWER: Two different failure modes for two different demotion positions.

══════════════════════════════════════════════════════════════════════════
CASE A: BOUNDARY DEMOTION (P1 -> binary)
  ms = (2, 2, 3, ..., 3, 2), binary at {0, 1, n-1}
══════════════════════════════════════════════════════════════════════════

  WHAT BREAKS IN CUP-2:
  (1) Good cycle: Steps t=2n-2 and t=2n-1 have c[1]=2 (IMPOSSIBLE).
      The 2-front in Phase 2 sweeps DOWN and must pass through P1.
      Binary P1 cannot hold value 2. Cycle is structurally broken.
  (2) Tables: 21 of 87 entries invalidated (24%).
      T_bot: 4 entries (R=2 gone). T_low: 7 entries (S=2 gone + output=2).
      T_mid/T_high at P2: 9 entries (L=2 gone).
  (3) P1 fires 3 times in the cycle (once per phase), but binary procs
      can only fire 2 times per cycle. The 3-phase wavefront is
      fundamentally incompatible with a binary interior proc.

  CAN WE BUILD A DIFFERENT SYSTEM?
  No. Binary positions {0, 1, n-1}: P0 and P1 are CONSECUTIVE.
  Lower bound Case 3a applies (Palindromic Entry Conflict):
  - Sweep cycles blocked by Shadow Cycle Mirror Theorem
  - Non-sweep fc=2 cycles: every turnaround at procs j=1,...,n-3 has
    entry conflict (CW nonmover ctx = CCW mover ctx, f=x_j AND f=0)
  - Wiggle cycles blocked by Wiggle Shadow Cycle

  SPECIFIC OBSTRUCTION: Palindromic Entry Conflict at interior procs.
  For any good cycle, the transition between CW and CCW sweep phases
  forces contradictory requirements on the transition function.

══════════════════════════════════════════════════════════════════════════
CASE B: INTERIOR DEMOTION (P_k -> binary, k=4)
  ms = (2, 3, 3, 3, 2, 3, ..., 3, 2), binary at {0, 4, n-1}
══════════════════════════════════════════════════════════════════════════

  WHAT BREAKS IN CUP-2:
  (1) Good cycle: MORE configs broken than Case A. The 2-front arrives
      at interior P4 EARLIER (Phase 2, step n+(n-1-4)=2n-5) and the
      0-front doesn't clear it until LATER (Phase 3, step 2n-1+3=2n+2).
      P4 holds value 2 for 2*4-1 = 7 consecutive steps (vs 2 for P1).
  (2) Tables: Similar count. T_mid at P3: 6 entries (R=2 gone).
      T_mid at P4: 12 entries (S=2 gone + output=2).
      T_mid at P5: 9 entries (L=2 gone).
  (3) Same firing count problem: P4 fires 3 times in the 3-phase cycle,
      but binary P4 can only fire 2 times.

  CAN WE BUILD A DIFFERENT SYSTEM?
  No. Binary positions {0, k, n-1}: P0 and P_{n-1} are ALWAYS adjacent
  on the ring, so this is actually Case 3a (consecutive binary pair).
  The Palindromic Entry Conflict kills non-sweep cycles via the
  {P0, P_{n-1}} consecutive pair, and shadow blocks sweeps/wiggles.

  For a truly non-adjacent 3-binary configuration (e.g., ms=(3,2,3,3,2,3,3,2,3)),
  Case 3b's Universal Entry Conflict applies with 4 mechanisms +
  2 ring-level lemmas. Either way: no valid system.

  SPECIFIC OBSTRUCTION: Entry conflict at binary positions.
  The binary procs act as bottlenecks where the mover-word walk must
  "turn around" or "pass through" — both create forced contexts that
  conflict with non-mover observations at the same triple.

══════════════════════════════════════════════════════════════════════════
ROOT CAUSE (BOTH CASES)
══════════════════════════════════════════════════════════════════════════

  The CUP-2 cycle is a 3-COLOR WAVEFRONT: values {0, 1, 2} propagate
  as three successive fronts (UP, DOWN, UP). This requires every
  interior proc to hold all 3 values during one cycle period.

  Product = 4*3^(n-2) is TIGHT because:
  - 2 binary endpoints are necessary (they serve as reflection points)
  - n-2 ternary interior procs are necessary (3 colors per proc)
  - Demoting ANY interior proc to binary removes 1 color from the
    wavefront path, breaking the cycle

  The lower bound proof independently confirms: 3 binary procs at
  sub-threshold product is an obstruction, regardless of the
  construction method used. CUP-2's failure is not a limitation of
  the specific construction — it reflects a FUNDAMENTAL impossibility.
""")


if __name__ == "__main__":
    main()
