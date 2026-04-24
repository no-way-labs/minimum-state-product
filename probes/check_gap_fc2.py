#!/usr/bin/env python3
"""
Check: with fc ≥ 2 for ALL processors (including binary neighbors),
can all phases of a sandwiched ternary be in normal form?

Normal form = NOT (BothEven OR ToggleFR-L OR ToggleFR-R)
BothEven: J even AND K even
ToggleFR-L: J >= 2 AND K = 0
ToggleFR-R: J = 0 AND K >= 2

If ALL-NORMAL is impossible with fc ≥ 2 for all procs:
→ gapDecisive_false is provable by COUNTING, no Ring Alternation needed!
"""

def is_mechanism_triggering(J, K):
    """Check if (J, K) triggers BothEven, ToggleFR-L, or ToggleFR-R."""
    if J % 2 == 0 and K % 2 == 0:
        return True  # BothEven
    if J >= 2 and K == 0:
        return True  # ToggleFR-L
    if J == 0 and K >= 2:
        return True  # ToggleFR-R
    return False


def check_all_normal_possible(q, sum_J, sum_K):
    """
    Check if it's possible to have q phases, all in normal form,
    with ∑J = sum_J and ∑K = sum_K.

    Returns True if such an assignment exists.
    """
    # Enumerate all possible (J, K) assignments for q phases
    # with ∑J = sum_J and ∑K = sum_K
    # and no phase triggering a mechanism.

    # For efficiency, use recursion with memoization
    from functools import lru_cache

    @lru_cache(maxsize=None)
    def can_fill(phases_left, j_left, k_left):
        if phases_left == 0:
            return j_left == 0 and k_left == 0
        for J in range(j_left + 1):
            for K in range(k_left + 1):
                if not is_mechanism_triggering(J, K):
                    if can_fill(phases_left - 1, j_left - J, k_left - K):
                        return True
        return False

    return can_fill(q, sum_J, sum_K)


def main():
    print("Checking: can ALL phases be normal form with fc ≥ 2 for all procs?")
    print("=" * 70)

    # For a sandwiched ternary t with binary neighbors:
    # q = fireCount(t) >= 2
    # sum_J = fireCount(left t) >= 2 (binary, even)
    # sum_K = fireCount(right t) >= 2 (binary, even)

    found_any = False

    for q in range(2, 8):  # fireCount of ternary
        for sum_J in range(2, 20, 2):  # binary fire count (even, ≥ 2)
            for sum_K in range(2, 20, 2):
                if check_all_normal_possible(q, sum_J, sum_K):
                    found_any = True
                    if q <= 4 and sum_J <= 8 and sum_K <= 8:
                        print(f"  ALL-NORMAL POSSIBLE: q={q}, ∑J={sum_J}, ∑K={sum_K}")

    if not found_any:
        print("  *** ALL-NORMAL IS IMPOSSIBLE with fc ≥ 2 for all procs! ***")
        print("  → gapDecisive_false provable by COUNTING, no Ring Alternation!")
    else:
        print(f"\n  ALL-NORMAL IS POSSIBLE in some cases.")
        print("  Ring Alternation still needed.")

    # Specifically check small cases
    print("\nDetailed check for small (q, ∑J, ∑K):")
    for q in [2, 3, 4]:
        for sJ in [2, 4]:
            for sK in [2, 4]:
                result = check_all_normal_possible(q, sJ, sK)
                print(f"  q={q}, ∑J={sJ}, ∑K={sK}: {'POSSIBLE' if result else 'IMPOSSIBLE'}")


if __name__ == "__main__":
    main()
