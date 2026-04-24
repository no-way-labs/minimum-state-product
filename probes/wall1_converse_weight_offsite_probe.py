#!/usr/bin/env python3
"""Probe the `converse_weight_offsite` sorry in `CPhiDelete.lean`.

This script hard-codes the Lean definitions of:
  - `cup2OutVal`
  - `cup2Exp2BitVal`
  - `localExp2Before/After`
  - `localExp2WeightBefore/After`

and checks the offsite projection situation for all
  n in [7, 40],
  deep deletions 3 <= k and k + 4 <= n,
  offsite movers p with p != k-1, k, k+1,
  all valid local triples (L,S,R).

The key question is:
  if the projected `(n-1)` move is TP-preserving, does the original `n` move
  preserve local weight?

The script reports:
  1. whether `cup2OutVal` matches between `p` and `projP`,
  2. whether projected local weight equality alone is enough,
  3. whether projected local Exp2-count equality + projected local weight
     equality imply original local weight equality,
  4. the exact arithmetic identity behind the coefficient shift.
"""

from __future__ import annotations


def t_bot(L: int, S: int, R: int) -> int:
    table = {
        (0, 0, 0): 1,
        (0, 0, 1): 1,
        (0, 0, 2): 0,
        (0, 1, 0): 1,
        (0, 1, 1): 1,
        (0, 1, 2): 1,
        (1, 0, 0): 0,
        (1, 0, 1): 1,
        (1, 0, 2): 0,
        (1, 1, 0): 0,
        (1, 1, 1): 1,
        (1, 1, 2): 0,
    }
    return table.get((L, S, R), 0)


def t_low(L: int, S: int, R: int) -> int:
    table = {
        (0, 0, 0): 0,
        (0, 0, 1): 0,
        (0, 0, 2): 0,
        (0, 1, 0): 0,
        (0, 1, 1): 1,
        (0, 1, 2): 0,
        (0, 2, 0): 0,
        (0, 2, 1): 2,
        (0, 2, 2): 0,
        (1, 0, 0): 1,
        (1, 0, 1): 1,
        (1, 0, 2): 1,
        (1, 1, 0): 1,
        (1, 1, 1): 1,
        (1, 1, 2): 2,
        (1, 2, 0): 0,
        (1, 2, 1): 1,
        (1, 2, 2): 2,
    }
    return table.get((L, S, R), 0)


def t_mid(L: int, S: int, R: int) -> int:
    table = {
        (0, 0, 0): 0,
        (0, 0, 1): 0,
        (0, 0, 2): 0,
        (0, 1, 0): 0,
        (0, 1, 1): 1,
        (0, 1, 2): 0,
        (0, 2, 0): 0,
        (0, 2, 1): 2,
        (0, 2, 2): 0,
        (1, 0, 0): 1,
        (1, 0, 1): 1,
        (1, 0, 2): 1,
        (1, 1, 0): 1,
        (1, 1, 1): 1,
        (1, 1, 2): 2,
        (1, 2, 0): 0,
        (1, 2, 1): 1,
        (1, 2, 2): 2,
        (2, 0, 0): 0,
        (2, 0, 1): 0,
        (2, 0, 2): 2,
        (2, 1, 0): 1,
        (2, 1, 1): 0,
        (2, 1, 2): 2,
        (2, 2, 0): 0,
        (2, 2, 1): 2,
        (2, 2, 2): 2,
    }
    return table.get((L, S, R), 0)


def t_high(L: int, S: int, R: int) -> int:
    table = {
        (0, 0, 0): 0,
        (0, 0, 1): 0,
        (0, 1, 0): 0,
        (0, 1, 1): 0,
        (0, 2, 0): 0,
        (0, 2, 1): 0,
        (1, 0, 0): 1,
        (1, 0, 1): 1,
        (1, 1, 0): 1,
        (1, 1, 1): 2,
        (1, 2, 0): 0,
        (1, 2, 1): 2,
        (2, 0, 0): 0,
        (2, 0, 1): 2,
        (2, 1, 0): 0,
        (2, 1, 1): 2,
        (2, 2, 0): 2,
        (2, 2, 1): 2,
    }
    return table.get((L, S, R), 0)


def t_top(L: int, S: int, R: int) -> int:
    table = {
        (0, 0, 0): 0,
        (0, 0, 1): 0,
        (0, 1, 0): 0,
        (0, 1, 1): 0,
        (1, 0, 0): 0,
        (1, 0, 1): 1,
        (1, 1, 0): 1,
        (1, 1, 1): 1,
        (2, 0, 0): 1,
        (2, 0, 1): 1,
        (2, 1, 0): 1,
        (2, 1, 1): 1,
    }
    return table.get((L, S, R), 0)


def left(n: int, i: int) -> int:
    return (i + n - 1) % n


def right(n: int, i: int) -> int:
    return (i + 1) % n


def cup2_m(n: int, i: int) -> int:
    return 2 if i == 0 or i + 1 == n else 3


def cup2_out_val(n: int, i: int, L: int, S: int, R: int) -> int:
    if i == 0:
        return t_bot(L, S, R)
    if i == 1:
        return t_low(L, S, R)
    if i + 1 == n:
        return t_top(L, S, R)
    if i + 2 == n:
        return t_high(L, S, R)
    return t_mid(L, S, R)


def exp2_bit(n: int, j: int, a: int, b: int) -> int:
    return 1 if 2 <= j and j + 2 < n and a == 2 and b != 2 else 0


def local_exp2_before(n: int, i: int, L: int, S: int, R: int) -> int:
    return exp2_bit(n, left(n, i), L, S) + exp2_bit(n, i, S, R)


def local_exp2_after(n: int, i: int, L: int, S: int, R: int, out: int) -> int:
    return exp2_bit(n, left(n, i), L, out) + exp2_bit(n, i, out, R)


def local_weight_before(n: int, i: int, L: int, S: int, R: int) -> int:
    return left(n, i) * exp2_bit(n, left(n, i), L, S) + i * exp2_bit(n, i, S, R)


def local_weight_after(n: int, i: int, L: int, S: int, R: int, out: int) -> int:
    return left(n, i) * exp2_bit(n, left(n, i), L, out) + i * exp2_bit(n, i, out, R)


def proj_mover(k: int, p: int) -> int:
    return p if p < k else p - 1


def valid_local_triples(n: int, p: int):
    for L in range(cup2_m(n, left(n, p))):
        for S in range(cup2_m(n, p)):
            for R in range(cup2_m(n, right(n, p))):
                yield L, S, R


def main() -> None:
    checked = 0
    out_mismatch = None
    below_rewrite_fail = None
    above_shift_fail = None
    full_tp_fail = None
    proj_weight_orig_fail_examples = []
    proj_weight_orig_fail_count = 0
    proj_weight_no_exp_examples = []
    proj_weight_no_exp_count = 0
    full_tp_success_count = 0
    below_cases = 0
    above_cases = 0

    for n in range(7, 41):
        for k in range(3, n - 3):
            for p in range(n):
                if p in (k - 1, k, k + 1):
                    continue
                proj = proj_mover(k, p)
                below = p < k
                for L, S, R in valid_local_triples(n, p):
                    checked += 1

                    out_n = cup2_out_val(n, p, L, S, R)
                    out_proj = cup2_out_val(n - 1, proj, L, S, R)
                    if out_n != out_proj and out_mismatch is None:
                        out_mismatch = (n, k, p, proj, L, S, R, out_proj, out_n)

                    proj_exp_before = local_exp2_before(n - 1, proj, L, S, R)
                    proj_exp_after = local_exp2_after(n - 1, proj, L, S, R, out_proj)
                    proj_w_before = local_weight_before(n - 1, proj, L, S, R)
                    proj_w_after = local_weight_after(n - 1, proj, L, S, R, out_proj)

                    orig_exp_before = local_exp2_before(n, p, L, S, R)
                    orig_exp_after = local_exp2_after(n, p, L, S, R, out_n)
                    orig_w_before = local_weight_before(n, p, L, S, R)
                    orig_w_after = local_weight_after(n, p, L, S, R, out_n)

                    if below:
                        below_cases += 1
                        if (
                            proj_w_before != orig_w_before
                            or proj_w_after != orig_w_after
                        ) and below_rewrite_fail is None:
                            below_rewrite_fail = (
                                n,
                                k,
                                p,
                                proj,
                                L,
                                S,
                                R,
                                proj_w_before,
                                orig_w_before,
                                proj_w_after,
                                orig_w_after,
                            )
                    else:
                        above_cases += 1
                        if (
                            orig_w_before - proj_w_before != orig_exp_before
                            or orig_w_after - proj_w_after != orig_exp_after
                        ) and above_shift_fail is None:
                            above_shift_fail = (
                                n,
                                k,
                                p,
                                proj,
                                L,
                                S,
                                R,
                                proj_w_before,
                                orig_w_before,
                                proj_w_after,
                                orig_w_after,
                                proj_exp_before,
                                orig_exp_before,
                                proj_exp_after,
                                orig_exp_after,
                            )

                    proj_weight_eq = proj_w_after == proj_w_before
                    proj_exp_eq = proj_exp_after == proj_exp_before
                    orig_weight_eq = orig_w_after == orig_w_before

                    if proj_weight_eq and not orig_weight_eq:
                        proj_weight_orig_fail_count += 1
                        if len(proj_weight_orig_fail_examples) < 5:
                            proj_weight_orig_fail_examples.append(
                                (
                                    n,
                                    k,
                                    p,
                                    proj,
                                    L,
                                    S,
                                    R,
                                    proj_exp_before,
                                    proj_exp_after,
                                    proj_w_before,
                                    proj_w_after,
                                    orig_w_before,
                                    orig_w_after,
                                )
                            )

                    if proj_weight_eq and not proj_exp_eq:
                        proj_weight_no_exp_count += 1
                        if len(proj_weight_no_exp_examples) < 5:
                            proj_weight_no_exp_examples.append(
                                (
                                    n,
                                    k,
                                    p,
                                    proj,
                                    L,
                                    S,
                                    R,
                                    proj_exp_before,
                                    proj_exp_after,
                                    proj_w_before,
                                    proj_w_after,
                                )
                            )

                    if proj_weight_eq and proj_exp_eq:
                        full_tp_success_count += 1
                        if not orig_weight_eq and full_tp_fail is None:
                            full_tp_fail = (
                                n,
                                k,
                                p,
                                proj,
                                L,
                                S,
                                R,
                                proj_exp_before,
                                proj_exp_after,
                                proj_w_before,
                                proj_w_after,
                                orig_w_before,
                                orig_w_after,
                            )

    print("Wall 1: converse_weight_offsite probe")
    print(f"checked local tuples: {checked}")
    print(f"below cases (p < k): {below_cases}")
    print(f"above cases (p > k): {above_cases}")
    print()

    print("1. Position-type/output matching")
    if out_mismatch is None:
        print("   OK: cup2OutVal(projP) = cup2OutVal(p) in every tested offsite case.")
    else:
        print(f"   FAIL: first mismatch {out_mismatch}")
    print()

    print("2. Direct rewrite below the deletion")
    if below_rewrite_fail is None:
        print("   OK: for p < k, projected and original local weights are literally identical.")
    else:
        print(f"   FAIL: first mismatch {below_rewrite_fail}")
    print()

    print("3. Coefficient-shift identity above the deletion")
    if above_shift_fail is None:
        print("   OK: for p > k,")
        print("       weight_n(before) = weight_(n-1)(before) + exp2_before")
        print("       weight_n(after)  = weight_(n-1)(after)  + exp2_after")
    else:
        print(f"   FAIL: first mismatch {above_shift_fail}")
    print()

    print("4. Is projected weight equality alone enough?")
    print(f"   projected weight equality but original weight failure: {proj_weight_orig_fail_count}")
    if proj_weight_orig_fail_examples:
        print("   Sample counterexamples:")
        for ex in proj_weight_orig_fail_examples:
            print(f"     {ex}")
    print(f"   projected weight equality but projected Exp2 failure: {proj_weight_no_exp_count}")
    if proj_weight_no_exp_examples:
        print("   Sample projected-weight-only cases:")
        for ex in proj_weight_no_exp_examples:
            print(f"     {ex}")
    print()

    print("5. Under the projected TP hypothesis (Exp2 equality + weight equality)")
    print(f"   tested TP-local tuples: {full_tp_success_count}")
    if full_tp_fail is None:
        print("   OK: no counterexample. Projected Exp2 equality cancels the weight shift.")
    else:
        print(f"   FAIL: first counterexample {full_tp_fail}")


if __name__ == "__main__":
    main()
