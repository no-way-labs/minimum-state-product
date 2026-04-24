#!/usr/bin/env python3
"""
Phase 0j: sanity check for Sub-lemma 3 Case C argument.

Under double-bounce (word[s-1]=r_b, word[e+1]=l_c) + Case C
(fc_run[r_b]=fc_run[l_c]=2), walker in middle-middle comp avoids both
r_b and l_c. For I=2, r_b and l_c are ring-adjacent, so ring\\{r_b,l_c}
is a single path (component 2, containing b and c). For I>=3, removing
both splits the ring into component 1 (interior others, size I-2) and
component 2 (containing b, c, outside, size n-I).

Sub-case C2: walker entirely in component 2. Walker starts at word[e+2]
= c (adjacent to l_c) and ends at word[s-2] = b (adjacent to r_b), both
in component 2. Forced line displacement vs ZW contradiction.

Sub-case C1: walker entirely in component 1 (I>=3 only). Walker at
word[e+2]=l_c-1, word[s-2]=r_b+1, both in component 1. Contradicted by
absence of b_2 / c_2 in middle-middle (component 1 has no b or c).
"""


def check_C2(n, I, b):
    """C2: walker from c to b on component 2 line."""
    r_b = (b + 1) % n
    c = (b + I + 1) % n
    l_c = (c - 1) % n

    # Component 2 = {c, c+1, ..., n-1, 0, ..., b} (cw from c, skipping l_c).
    # Line from c to b, length n - I - 1 edges, n - I positions.
    # k(c) = 0, k(c+1) = 1, ..., k(b) = n - I - 1.

    # Line direction: ring cw = line +1 (c -> c+1 is line +1).
    # mmnet (middle-middle net, ring cw - ring ccw) under Case C sub-case C2:
    #   edge e+1 = (l_c, c) = cw = +1
    #   edge s-2 = (b, r_b) = cw = +1
    #   ZW: -(I+1) total comp = -1 (e) + (+1) + mmnet + (+1) + -1 (s-1)
    #   mmnet = -(I+1) + 2 - 1 - 1 = -(I+1)
    # Line disp forced by geometry: k(b) - k(c) = n - I - 1.
    # Required mmnet (as line disp, since ring cw = line +1): n - I - 1.
    # vs computed: -(I+1).

    line_disp = n - I - 1
    required = -(I + 1)
    print(f"  n={n}, I={I}: C2 line disp = {line_disp}, "
          f"required = {required}, "
          f"contradiction? {line_disp != required}")
    return line_disp != required


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
    ]
    print("=== Sub-lemma 3 Case C sub-case C2 ===")
    all_ok = all(check_C2(n, I, b) for n, I, b in cases)
    print(f"\nAll cases contradicted: {all_ok}")
