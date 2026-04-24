#!/usr/bin/env python3
from collections import Counter

from zw_palindromic_ec_proof_FINAL import (
    classify_word,
    enumerate_zw_fc2,
    full_traverse_word,
    verify_case_a,
    verify_case_b,
)


def exact_case_b_pair(word, n):
    """Check the prose's specific Case B witness: ms=n+3, nms=n at proc 3."""
    if n < 5 or len(word) != 2 * n:
        return False
    ms = n + 3
    nms = n
    if word[ms] != 3 or word[nms] != 2:
        return False
    fires = Counter(word[i] for i in range(nms, ms))
    return fires.get(3, 0) == 0 and fires.get(2, 0) == 2 and fires.get(4 % n, 0) == 0


def step_string(word, n):
    steps, cw, ccw = classify_word(word, n)
    symbols = {1: "R", -1: "L", 0: "S", None: "?"}
    return "".join(symbols[s] for s in steps), cw, ccw


def main():
    print("Palindromic EC proof review checks")
    print("=" * 72)
    print("Range: n = 5..12")
    print()

    for n in range(5, 13):
        words = enumerate_zw_fc2(n)
        state_sizes = [2 if p < 3 else 3 for p in range(n)]

        case_a_words = []
        case_b_words = []
        a_fail_words = []
        uncovered_words = []

        for word in words:
            ok_a = verify_case_a(word, n, [0, 1, 2], state_sizes)[0]
            ok_b = verify_case_b(word, n, state_sizes)[0]
            if ok_a:
                case_a_words.append(word)
            if ok_b:
                case_b_words.append(word)
            if not ok_a:
                a_fail_words.append(word)
            if not (ok_a or ok_b):
                uncovered_words.append(word)

        print(
            f"n={n:2d} total={len(words):2d} "
            f"caseA={len(case_a_words):2d} "
            f"caseB_general={len(case_b_words):2d} "
            f"A_fail={len(a_fail_words)} "
            f"uncovered={len(uncovered_words)}"
        )

        for word in a_fail_words:
            steps, cw, ccw = step_string(word, n)
            print(f"  failA word      : {word}")
            print(f"  step pattern    : {steps} (cw={cw}, ccw={ccw})")
            print(f"  exact_full_trav : {word == full_traverse_word(n)}")
            print(f"  exact_caseB_pair: {exact_case_b_pair(word, n)}")
            print(f"  general_caseB   : {verify_case_b(word, n, state_sizes)[0]}")

        print()


if __name__ == "__main__":
    main()
