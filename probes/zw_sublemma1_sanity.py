#!/usr/bin/env python3
"""
Phase 0h: sanity check for the Sub-lemma 1 proof.

Proof claim:
  Under Case (i) [fc_run[r_b] = 3], the comp walk is confined to
  ring - {r_b}. ZW requires net line displacement = +(I + 1).
  But word[e+1] in {l_c, c, r_c} (line j in {n-I, n-I-1, n-I-2}) and
  word[s-1] in {b, l_b} (line j in {0, 1}), so
    net = j(word[s-1]) - j(word[e+1]) in [0 - (n - I), 1 - (n - I - 2)]
        = [I - n, I - n + 3]
  which is negative for n >= 3, contradicting required +(I + 1) > 0.

Symmetric for left-side (Case I): net = -(I + 1) required, achievable
range is non-negative, contradiction.

This script just double-checks the algebra for several (n, I, b) choices
by directly computing line indices.
"""


def check_right(n, I, b):
    r_b = (b + 1) % n
    c = (b + I + 1) % n
    l_c = (c - 1) % n
    r_c = (c + 1) % n
    l_b = (b - 1) % n

    # Line = ring \ {r_b}, walking from b in ring-ccw direction.
    # j(b) = 0, j(b-1) = 1, j(b-2) = 2, ..., j(r_b+1) = n-2.
    def j(p):
        if p == r_b:
            return None
        return (b - p) % n

    word_e1_opts = [l_c, c, r_c]
    word_s_minus_1_opts = [b, l_b]  # r_b excluded under Case (i)

    print(f"  n={n}, I={I}, b={b}, c={c}, r_b={r_b}, l_c={l_c}, l_b={l_b}")
    print(f"  j(l_c)={j(l_c)}, j(c)={j(c)}, j(r_c)={j(r_c)}")
    print(f"  j(b)={j(b)}, j(l_b)={j(l_b)}")

    nets = []
    for e1 in word_e1_opts:
        for sm1 in word_s_minus_1_opts:
            net = j(sm1) - j(e1)
            nets.append(net)
    print(f"  achievable j(end) - j(start): {nets}")
    max_net = max(nets)
    required = I + 1
    print(f"  max achievable: {max_net}, required: {required}")
    print(f"  contradiction? {max_net < required}")
    return max_net < required


def check_left(n, I, b):
    r_b = (b + 1) % n
    c = (b + I + 1) % n
    l_c = (c - 1) % n
    r_c = (c + 1) % n
    l_b = (b - 1) % n

    # Line = ring \ {l_c}. Walking from c in ring-cw direction.
    # j'(c) = 0, j'(c+1) = 1, ..., j'(l_c - 1) = n - 2.
    def jp(p):
        if p == l_c:
            return None
        return (p - c) % n

    word_e1_opts = [c, r_c]  # l_c excluded under Case (I)
    word_s_minus_1_opts = [l_b, b, r_b]

    print(f"  [LEFT] n={n}, I={I}, b={b}, c={c}, l_c={l_c}, r_c={r_c}")
    print(f"  j'(c)={jp(c)}, j'(r_c)={jp(r_c)}")
    print(f"  j'(l_b)={jp(l_b)}, j'(b)={jp(b)}, j'(r_b)={jp(r_b)}")

    nets = []
    for e1 in word_e1_opts:
        for sm1 in word_s_minus_1_opts:
            net = jp(sm1) - jp(e1)
            nets.append(net)
    print(f"  achievable j'(end) - j'(start): {nets}")
    min_net = min(nets)
    required = -(I + 1)
    print(f"  min achievable: {min_net}, required: {required}")
    print(f"  contradiction? {min_net > required}")
    return min_net > required


if __name__ == "__main__":
    cases = [
        (9, 2, 0),
        (9, 3, 0),
        (9, 6, 0),
        (11, 2, 0),
        (11, 4, 0),
        (11, 6, 0),
        (11, 8, 0),
        (9, 2, 3),   # non-zero b
        (11, 8, 2),  # matches 3-consec-binary pair (2, 0)
    ]
    print("=== RIGHT-SIDE (Case i) ===")
    for n, I, b in cases:
        print(f"\n  Case n={n}, I={I}, b={b}:")
        check_right(n, I, b)
    print("\n=== LEFT-SIDE (Case I) ===")
    for n, I, b in cases:
        print(f"\n  Case n={n}, I={I}, b={b}:")
        check_left(n, I, b)
