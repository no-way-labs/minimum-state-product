#!/usr/bin/env python3
"""
Phase 0i: budget analysis for Sub-lemma 2 bad case.

Sub-lemma 2 right-side bad case:
  ii_other (rho_3 in (e, s-1))  AND  b_2 in (e, rho_3]  AND
  word[rho_3 + 1] = r_b + 1.

Under this, the walker from step rho_3+1 to s-1 must avoid r_b (fc_run
maxed) AND avoid b (fc maxed at b_2 and s). So the walker is confined
to ring \\ {r_b, b} = reduced line {r_b+1, r_b+2, ..., l_b}, with
endpoints r_b+1 and l_b. The walker starts at r_b+1 (forced) and ends
at l_b (only other endpoint adjacent to b).

Computing net line displacement:
  j''(r_b+1) = 0, j''(l_b) = n-3. So walker's line displacement = n-3.
  Ring cw <-> line +1, ring ccw <-> line -1.
  So (ring cw - ring ccw) on interior late-comp edges = n - 3.
  Plus entry edge (rho_3, rho_3+1) = r_b -> r_b+1 = cw = +1.
  Plus exit edge (s-1, s) = l_b -> b = cw = +1.
  Total late segment net = n - 1.

ZW on cycle: run_net + early_net + late_net = 0.
  run_net = I + 1 (non-wrapping run from b to c).
  So early_net = -(I + 1) - (n - 1) = -(I + n).

Early segment edge count bound: |early_net| <= (rho_3 - e) edges, so
  rho_3 - e >= I + n.

Late segment edge count bound: |late_net| = n - 1 <= (s - rho_3) edges,
  so s - rho_3 >= n - 1.

Total comp edge count: L - R_e >= (I + n) + (n - 1) = I + 2n - 1.
  R_e <= L - I - 2n + 1 = (3n - B) - I - 2n + 1 = n - B - I + 1.

For oscillatory runs, R_e >= I + 3. So:
  I + 3 <= n - B - I + 1  <=>  B + 2I + 2 <= n.

This is the partial bound. When B + 2I + 2 > n, the sub-lemma 2 bad
case is ruled out.
"""

FAMILIES = [
    (9,  "n9  all-odd-gap",       [2, 3, 3, 2, 3, 3, 2, 3, 3],    2),
    (9,  "n9  3-consec-binary",   [2, 2, 2, 3, 3, 3, 3, 3, 3],    6),
    (9,  "n9  pivot alt",         [2, 3, 2, 3, 2, 3, 3, 3, 3],    4),
    (9,  "n9  3-all-spaced",      [2, 3, 3, 3, 2, 3, 3, 3, 2],    3),
    (9,  "n9  gap-(2,3,4) small", [2, 3, 2, 3, 3, 2, 3, 3, 3],    2),
    (9,  "n9  gap-(2,3,4) large", [2, 3, 2, 3, 3, 2, 3, 3, 3],    3),
    (9,  "n9  4-bin alternating", [2, 3, 2, 3, 2, 3, 2, 3, 3],    2),
    (11, "n11 all-odd-gap small", [2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3], 2),
    (11, "n11 all-odd-gap large", [2, 3, 3, 2, 3, 3, 2, 3, 3, 3, 3], 4),
    (11, "n11 3-consec-binary",   [2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3], 8),
    (11, "n11 pivot 3bin",        [2, 3, 2, 3, 2, 3, 3, 3, 3, 3, 3], 6),
    (11, "n11 4-bin spaced",      [2, 3, 3, 2, 3, 3, 2, 3, 3, 2, 3], 2),
]

def bound_check(n, label, ms, I):
    B = ms.count(2)
    L = sum(ms)
    lhs = B + 2 * I + 2
    ruled_out = lhs > n
    verdict = "CONTRADICTED" if ruled_out else "NOT CONTRADICTED"
    print(f"  {label:35s}  L={L:3d}  B={B}  I={I}  "
          f"B+2I+2={lhs}  vs  n={n}   [{verdict}]")
    return ruled_out


if __name__ == "__main__":
    print("Sub-lemma 2 right-side bad case — B + 2I + 2 <= n bound:")
    results = {}
    for n, label, ms, I in FAMILIES:
        ruled = bound_check(n, label, ms, I)
        results[(n, label, I)] = ruled
    print()
    total = len(results)
    ruled_count = sum(1 for v in results.values() if v)
    print(f"Families ruled out: {ruled_count}/{total}")
