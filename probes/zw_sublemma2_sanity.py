#!/usr/bin/env python3
"""
Phase 0i: sanity check for Sub-lemma 2 (right-side) proof.

Claim: under the bad case
  rho_3 in (e, s-1), b_2 in (e, rho_3], word[rho_3+1] = r_b+1,
the early-comp walker must achieve line displacement (I + n) on the
line (ring minus {r_b}), but the maximum achievable displacement given
start in {l_c, c, r_c} and end in {b, r_b+1} is only I. Contradiction.

This script computes both bounds for several (n, I, b) cases.
"""


def check_right(n, I, b):
    r_b = (b + 1) % n
    c = (b + I + 1) % n
    l_c = (c - 1) % n
    r_c = (c + 1) % n
    l_b = (b - 1) % n
    r_b_plus_1 = (r_b + 1) % n

    # j(p) = (b - p) mod n for p != r_b (line = ring \ {r_b}).
    def j(p):
        if p == r_b:
            return None
        return (b - p) % n

    start_opts = [l_c, c, r_c]
    end_opts = [b, r_b_plus_1]

    max_disp = max(j(e) - j(s) for e in end_opts for s in start_opts)
    required = I + n

    print(f"  n={n}, I={I}, b={b}: "
          f"j(start) in {[j(p) for p in start_opts]}, "
          f"j(end) in {[j(p) for p in end_opts]}")
    print(f"    max achievable line displacement: {max_disp}")
    print(f"    required line displacement:      {required}")
    print(f"    contradiction? {required > max_disp}")
    return required > max_disp


if __name__ == "__main__":
    cases = [
        (9, 2, 0),
        (9, 3, 0),
        (9, 4, 0),
        (9, 6, 0),
        (11, 2, 0),
        (11, 4, 0),
        (11, 6, 0),
        (11, 8, 0),
        (11, 8, 2),  # 3-consec-binary pair
    ]
    print("=== Sub-lemma 2 right-side bad case ===")
    all_ok = True
    for n, I, b in cases:
        if not check_right(n, I, b):
            all_ok = False
    print(f"\nAll cases contradicted: {all_ok}")
