#!/usr/bin/env python3
"""
Check whether Exp2Weight is redundant given Exp2Count + Int21Count preservation.

Claim: For positions j where both adjacent Exp2 edges are in the interior range
(2 <= j-1 and j+2 < n), preserving Exp2Count automatically implies preserving
Exp2Weight (and Int21Count is not even needed).

Proof sketch: localExp2Before = bit(left(j), L, S) + bit(j, S, R)
              localExp2After  = bit(left(j), L, out) + bit(j, out, R)
              localExp2WeightBefore = (j-1)*bit(left(j), L, S) + j*bit(j, S, R)
              localExp2WeightAfter  = (j-1)*bit(left(j), L, out) + j*bit(j, out, R)

If count preserved: Dbit_left + Dbit_right = 0
Weight change = (j-1)*Dbit_left + j*Dbit_right = (j-1)*Dbit_left + j*(-Dbit_left) = -Dbit_left
So weight preserved iff Dbit_left = 0 iff both bits unchanged.

But that's only when BOTH edges are in range. At boundary positions, one edge
may be out of range (always 0), so Dbit for that edge is forced to 0, and
the count equation Dbit_left + Dbit_right = 0 forces the other to 0 too.
So it should STILL work. Let's verify exhaustively.

This script checks ALL position types, ALL (L, S, R, out) combinations,
for n = 9..15.
"""

# ---- CUP-2 transition tables (from Tables.lean) ----

def TBotVal(L, S, R):
    t = {
        (0,0,0):1, (0,0,1):1, (0,0,2):0,
        (0,1,0):1, (0,1,1):1, (0,1,2):1,
        (1,0,0):0, (1,0,1):1, (1,0,2):0,
        (1,1,0):0, (1,1,1):1, (1,1,2):0,
    }
    return t.get((L,S,R), 0)

def TLowVal(L, S, R):
    t = {
        (0,0,0):0, (0,0,1):0, (0,0,2):0,
        (0,1,0):0, (0,1,1):1, (0,1,2):0,
        (0,2,0):0, (0,2,1):2, (0,2,2):0,
        (1,0,0):1, (1,0,1):1, (1,0,2):1,
        (1,1,0):1, (1,1,1):1, (1,1,2):2,
        (1,2,0):0, (1,2,1):1, (1,2,2):2,
    }
    return t.get((L,S,R), 0)

def TMidVal(L, S, R):
    t = {
        (0,0,0):0, (0,0,1):0, (0,0,2):0,
        (0,1,0):0, (0,1,1):1, (0,1,2):0,
        (0,2,0):0, (0,2,1):2, (0,2,2):0,
        (1,0,0):1, (1,0,1):1, (1,0,2):1,
        (1,1,0):1, (1,1,1):1, (1,1,2):2,
        (1,2,0):0, (1,2,1):1, (1,2,2):2,
        (2,0,0):0, (2,0,1):0, (2,0,2):2,
        (2,1,0):1, (2,1,1):2, (2,1,2):2,
        (2,2,0):0, (2,2,1):2, (2,2,2):2,
    }
    return t.get((L,S,R), 0)

def THighVal(L, S, R):
    t = {
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
    return t.get((L,S,R), 0)

def TTopVal(L, S, R):
    t = {
        (0,0,0):0, (0,0,1):0,
        (0,1,0):0, (0,1,1):0,
        (1,0,0):0, (1,0,1):1,
        (1,1,0):1, (1,1,1):1,
        (2,0,0):1, (2,0,1):1,
        (2,1,0):1, (2,1,1):1,
    }
    return t.get((L,S,R), 0)


# ---- Ring structure ----

def left_val(n, i):
    return (i + n - 1) % n

def cup2M(n, i):
    """State count at position i in ring of size n."""
    if i == 0 or i == n - 1:
        return 2
    else:
        return 3

def cup2OutVal(n, i, L, S, R):
    """Transition function output at position i."""
    if i == 0:
        return TBotVal(L, S, R)
    elif i == 1:
        return TLowVal(L, S, R)
    elif i == n - 1:
        return TTopVal(L, S, R)
    elif i == n - 2:
        return THighVal(L, S, R)
    else:
        return TMidVal(L, S, R)


# ---- Exp2 bit definitions ----

def cup2Exp2BitVal(n, j, a, b):
    """1 if edge (j, j+1) is an Exp2 edge: 2 <= j, j+2 < n, a=2, b!=2."""
    if 2 <= j and j + 2 < n and a == 2 and b != 2:
        return 1
    return 0

def cup2Int21BitVal(n, j, a, b):
    """1 if edge (j, j+1) is an Int21 edge: 2 <= j, j+2 < n, a=2, b=1."""
    if 2 <= j and j + 2 < n and a == 2 and b == 1:
        return 1
    return 0


# ---- Local quantities at mover position i ----
# The two affected edges are at positions left(i) and i.
# Edge at position left(i): connects c[left(i)] -> c[i] (values: L -> S, becomes L -> out)
# Edge at position i: connects c[i] -> c[right(i)] (values: S -> R, becomes out -> R)

def localExp2Before(n, i, L, S, R):
    li = left_val(n, i)
    return cup2Exp2BitVal(n, li, L, S) + cup2Exp2BitVal(n, i, S, R)

def localExp2After(n, i, L, S, R, out):
    li = left_val(n, i)
    return cup2Exp2BitVal(n, li, L, out) + cup2Exp2BitVal(n, i, out, R)

def localInt21Before(n, i, L, S, R):
    li = left_val(n, i)
    return cup2Int21BitVal(n, li, L, S) + cup2Int21BitVal(n, i, S, R)

def localInt21After(n, i, L, S, R, out):
    li = left_val(n, i)
    return cup2Int21BitVal(n, li, L, out) + cup2Int21BitVal(n, i, out, R)

def localExp2WeightBefore(n, i, L, S, R):
    li = left_val(n, i)
    return li * cup2Exp2BitVal(n, li, L, S) + i * cup2Exp2BitVal(n, i, S, R)

def localExp2WeightAfter(n, i, L, S, R, out):
    li = left_val(n, i)
    return li * cup2Exp2BitVal(n, li, L, out) + i * cup2Exp2BitVal(n, i, out, R)


# ---- Main check ----

def position_type(n, i):
    """Human-readable position type."""
    if i == 0: return "Bot(0)"
    if i == 1: return "Low(1)"
    if i == n - 1: return f"Top({i})"
    if i == n - 2: return f"High({i})"
    return f"Mid({i})"

def edge_status(n, j):
    """Whether edge at position j is in Exp2 range."""
    if 2 <= j and j + 2 < n:
        return "IN_RANGE"
    return "OUT_OF_RANGE"

def main():
    print("=" * 80)
    print("Exp2Weight redundancy check")
    print("=" * 80)
    print()

    # Part 1: For each boundary position, show which edges are in range
    print("--- Part 1: Edge range analysis for n=9 ---")
    n = 9
    for i in range(n):
        li = left_val(n, i)
        left_edge = li   # edge at position left(i)
        right_edge = i    # edge at position i
        print(f"  Mover j={i} ({position_type(n,i)}): "
              f"left edge at pos {left_edge} [{edge_status(n,left_edge)}], "
              f"right edge at pos {right_edge} [{edge_status(n,right_edge)}]")
    print()

    # Part 2: Exhaustive check
    print("--- Part 2: Exhaustive (L,S,R,out) check ---")
    print()

    total_checks = 0
    total_count_preserved = 0
    total_int21_preserved = 0
    counterexamples_count_only = []  # count preserved but weight not
    counterexamples_count_and_int21 = []  # count+int21 preserved but weight not
    redundancy_proven = []  # positions where count alone implies weight

    for n in range(9, 16):
        n_checks = 0
        n_count_pres = 0
        n_both_pres = 0
        n_cx_count = []
        n_cx_both = []

        for i in range(n):
            mL = cup2M(n, left_val(n, i))  # state range for L
            mS = cup2M(n, i)                # state range for S (and out)
            mR = cup2M(n, (i + 1) % n)     # state range for R

            out_val = None  # will compute from table

            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        out = cup2OutVal(n, i, L, S, R)

                        eb = localExp2Before(n, i, L, S, R)
                        ea = localExp2After(n, i, L, S, R, out)
                        ib = localInt21Before(n, i, L, S, R)
                        ia = localInt21After(n, i, L, S, R, out)
                        wb = localExp2WeightBefore(n, i, L, S, R)
                        wa = localExp2WeightAfter(n, i, L, S, R, out)

                        n_checks += 1
                        total_checks += 1

                        count_pres = (ea == eb)
                        int21_pres = (ia == ib)
                        weight_pres = (wa == wb)

                        if count_pres:
                            n_count_pres += 1
                            total_count_preserved += 1
                            if not weight_pres:
                                cx = (n, i, position_type(n,i), L, S, R, out,
                                      eb, ea, wb, wa)
                                n_cx_count.append(cx)
                                counterexamples_count_only.append(cx)

                        if count_pres and int21_pres:
                            n_both_pres += 1
                            total_int21_preserved += 1
                            if not weight_pres:
                                cx = (n, i, position_type(n,i), L, S, R, out,
                                      eb, ea, ib, ia, wb, wa)
                                n_cx_both.append(cx)
                                counterexamples_count_and_int21.append(cx)

        print(f"  n={n}: {n_checks} triples, "
              f"{n_count_pres} count-preserved, "
              f"cx(count-only)={len(n_cx_count)}, "
              f"cx(count+int21)={len(n_cx_both)}")

        if n_cx_count:
            for cx in n_cx_count[:5]:
                print(f"    COUNTEREXAMPLE (count only): "
                      f"pos={cx[1]}({cx[2]}) L={cx[3]} S={cx[4]} R={cx[5]} out={cx[6]} "
                      f"exp2: {cx[7]}->{cx[8]} weight: {cx[9]}->{cx[10]}")

        if n_cx_both:
            for cx in n_cx_both[:5]:
                print(f"    COUNTEREXAMPLE (count+int21): "
                      f"pos={cx[1]}({cx[2]}) L={cx[3]} S={cx[4]} R={cx[5]} out={cx[6]} "
                      f"exp2: {cx[7]}->{cx[8]} int21: {cx[9]}->{cx[10]} "
                      f"weight: {cx[11]}->{cx[12]}")

    print()
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"Total checks: {total_checks}")
    print(f"Total count-preserved: {total_count_preserved}")
    print(f"Counterexamples (count preserved => weight preserved): "
          f"{len(counterexamples_count_only)}")
    print(f"Counterexamples (count+int21 preserved => weight preserved): "
          f"{len(counterexamples_count_and_int21)}")

    if not counterexamples_count_only:
        print()
        print("RESULT: Exp2Count preservation ALONE implies Exp2Weight preservation")
        print("        for ALL positions, ALL (L,S,R) triples, n=9..15.")
        print("        Int21Count is NOT needed for this implication.")
        print("        Exp2Weight IS redundant in the TP invariant.")
    elif not counterexamples_count_and_int21:
        print()
        print("RESULT: Exp2Count preservation alone is NOT sufficient,")
        print("        but Exp2Count + Int21Count preservation DOES imply")
        print("        Exp2Weight preservation for ALL positions, n=9..15.")
        print("        Exp2Weight IS redundant given the other two components.")
    else:
        print()
        print("RESULT: Exp2Weight is NOT redundant -- counterexamples exist!")

    # Part 3: Analytical explanation
    print()
    print("--- Part 3: Analytical explanation per position type ---")
    print()
    n = 9
    for i in range(n):
        li = left_val(n, i)
        left_in = (2 <= li and li + 2 < n)
        right_in = (2 <= i and i + 2 < n)
        ptype = position_type(n, i)

        if not left_in and not right_in:
            reason = "Both edges OUT_OF_RANGE => both bits always 0 => count=0=weight trivially"
        elif left_in and not right_in:
            reason = (f"Only left edge (pos {li}) in range. "
                      f"Count eq: Dbit_left + 0 = 0 => Dbit_left=0 => weight change = {li}*0 = 0")
        elif not left_in and right_in:
            reason = (f"Only right edge (pos {i}) in range. "
                      f"Count eq: 0 + Dbit_right = 0 => Dbit_right=0 => weight change = {i}*0 = 0")
        else:
            reason = (f"Both edges in range. Count eq: Dbit_left + Dbit_right = 0. "
                      f"Weight change = {li}*Dbit_left + {i}*Dbit_right = "
                      f"{li}*Dbit_left + {i}*(-Dbit_left) = "
                      f"({li}-{i})*Dbit_left = (-1)*Dbit_left. "
                      f"So weight preserved iff Dbit_left=0.")

        print(f"  j={i} ({ptype}): {reason}")

    # Part 4: Check whether count preservation forces both bits to be unchanged
    print()
    print("--- Part 4: Does count preservation force Dbit_left = Dbit_right = 0? ---")
    print()
    any_nonzero = False
    for n in range(9, 16):
        for i in range(n):
            li = left_val(n, i)
            mL = cup2M(n, li)
            mS = cup2M(n, i)
            mR = cup2M(n, (i + 1) % n)

            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        out = cup2OutVal(n, i, L, S, R)
                        eb = localExp2Before(n, i, L, S, R)
                        ea = localExp2After(n, i, L, S, R, out)
                        if ea != eb:
                            continue

                        # Check individual bits
                        bl = cup2Exp2BitVal(n, li, L, S)
                        al = cup2Exp2BitVal(n, li, L, out)
                        br = cup2Exp2BitVal(n, i, S, R)
                        ar = cup2Exp2BitVal(n, i, out, R)

                        dbl = al - bl
                        dbr = ar - br

                        if dbl != 0 or dbr != 0:
                            any_nonzero = True
                            print(f"  n={n} j={i} ({position_type(n,i)}): "
                                  f"L={L} S={S} R={R} out={out} "
                                  f"Dbit_left={dbl} Dbit_right={dbr} "
                                  f"(both-in-range: left={2<=li and li+2<n}, right={2<=i and i+2<n})")

    if not any_nonzero:
        print("  All count-preserved transitions have Dbit_left = Dbit_right = 0.")
        print("  This is STRONGER than what we need: not only is weight preserved,")
        print("  but each individual Exp2 bit is unchanged.")


if __name__ == "__main__":
    main()
