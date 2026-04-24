#!/usr/bin/env python3
"""
Phase 0l: sanity check for Sub-lemma 3 Case C'3 contradiction.

Case C'3: fc_run[r_b] = fc_run[l_c] = 1 ⟹ fc_comp[r_b] = fc_comp[l_c] = 2.
Under double-bounce, walker in middle-traj has fc_middle-traj[b] = 1
and fc_middle-traj[c] = 1 (both singletons). This forces at most 2
crossings, hence exactly 1 outside visit.

Two scenarios:

A1: exit via (l_c, c), enter via (b, r_b).
  - Gap visit 1: walker l_c → ... → l_c (closed loop in gap).
    Net ring cw−ccw = 0 (closed walk on path graph has net 0).
  - Gap visit 2: walker r_b → ... → r_b. Net = 0.
  - Crossing (l_c, c) at exit: ring direction l_c → c = cw, +1.
  - Crossing (b, r_b) at enter: ring direction b → r_b = cw, +1.
  - Outside arc from c to b: net = n − I − 1 (monotone cw, forced).
  Total middle cw−ccw = 0 + 0 + 1 + 1 + (n − I − 1) = n − I + 1.
  Required by ZW: 1 − I.
  Discrepancy: n. Contradiction for n ≥ 1.

A4: exit via (r_b, b), enter via (c, l_c).
  - Gap visit 1: walker l_c → ... → r_b (open walk in gap).
    Walker visits mids on the way, min I − 2 mid fires (pass-through).
  - Gap visit 2: walker l_c → ... → r_b (second traversal). Again I − 2
    mid fires minimum.
  - Total min mid fires required = 2(I − 2) = 2I − 4.
  - Available fc_middle-traj[mid_total] = 3(I − 2) − (R_e − 3) =
    3I − R_e − 3, max at R_e = I + 3 (min oscillatory) gives 2I − 6.
  - 2I − 4 > 2I − 6. Insufficient mids. Contradiction.

Therefore Case C'3 is infeasible for all I ≥ 2.
"""


def check_A1(n, I):
    """A1 scenario: ZW line displacement contradiction."""
    middle_ccw_cw = (n - I + 1)  # gap0 + gap0 + crossing1 + crossing1 + outside
    required = 1 - I
    contradict = middle_ccw_cw != required
    return (middle_ccw_cw, required, contradict)


def check_A4_mids(n, I, R_e):
    """A4 scenario: min mid fires vs available."""
    min_mid_required = 2 * (I - 2)
    fc_middle_mid_total = 3 * (I - 2) - (R_e - 3)
    contradict = min_mid_required > fc_middle_mid_total
    return (min_mid_required, fc_middle_mid_total, contradict)


if __name__ == "__main__":
    print("=== Sub-lemma 3 Case C'3: A1 ZW contradiction ===")
    for n, I in [(9, 3), (9, 4), (9, 6), (11, 3), (11, 4), (11, 6), (11, 8)]:
        m, req, cont = check_A1(n, I)
        tag = "CONTRADICT" if cont else "OK"
        print(f"  n={n}, I={I}: middle cw-ccw = {m}, required = {req}  [{tag}]")

    print("\n=== Sub-lemma 3 Case C'3: A4 mid-fire budget contradiction ===")
    for n, I in [(9, 3), (9, 4), (9, 6), (11, 3), (11, 4), (11, 6), (11, 8)]:
        R_e = I + 3  # min oscillatory
        need, have, cont = check_A4_mids(n, I, R_e)
        tag = "CONTRADICT" if cont else "OK"
        print(f"  n={n}, I={I}, R_e={R_e}: need {need} mid fires, "
              f"have {have}  [{tag}]")
