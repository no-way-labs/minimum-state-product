#!/usr/bin/env python3
"""
Check the seam-triple matching question for deletion at site k.

For the seam deleted movers:
  - p' = k - 1   (left seam)
  - p' = k       (right seam)

the deleted local triple differs from the obvious original local triple unless a
copy relation at k collapses the mismatch.

This script checks which copy-pair orientation(s) force equality of the
relevant triples.
"""

from itertools import product


def left_seam_match(a, b, c, d):
    # original c has local values:
    #   c[k-2] = a, c[k-1] = b, c[k] = c, c[k+1] = d
    # deleted p' = k-1 sees (a, b, d)
    # original lift p = k-1 sees (a, b, c)
    return (a, b, d) == (a, b, c)


def right_seam_match(a, b, c, d):
    # deleted p' = k sees (b, d, ?), original lift p = k+1 sees (c, d, ?)
    # the mismatch is at the left input: b vs c
    return b == c


def analyze():
    vals = [0, 1, 2]
    left_cases = []
    right_cases = []
    for a, b, c, d in product(vals, repeat=4):
        lmatch = left_seam_match(a, b, c, d)
        rmatch = right_seam_match(a, b, c, d)
        cond_ck_eq_ckm1 = (c == b)
        cond_ck_eq_ckp1 = (c == d)
        if lmatch:
            left_cases.append((a, b, c, d, cond_ck_eq_ckm1, cond_ck_eq_ckp1))
        if rmatch:
            right_cases.append((a, b, c, d, cond_ck_eq_ckm1, cond_ck_eq_ckp1))

    print("Left seam: deleted triple (a,b,d) vs original lift (a,b,c)")
    print(f"  matches in {len(left_cases)} / 81 cases")
    print(f"  all matches imply c=d? {all(c == d for _, _, c, d, _, _ in left_cases)}")
    print(f"  all matches imply c=b? {all(c == b for _, b, c, _, _, _ in left_cases)}")
    print()
    print("Right seam: deleted left input b vs original left input c")
    print(f"  matches in {len(right_cases)} / 81 cases")
    print(f"  all matches imply c=b? {all(c == b for _, b, c, _, _, _ in right_cases)}")
    print(f"  all matches imply c=d? {all(c == d for _, _, c, d, _, _ in right_cases)}")
    print()
    print("Sample left-seam matches:")
    for row in left_cases[:10]:
        print(" ", row)
    print("Sample right-seam matches:")
    for row in right_cases[:10]:
        print(" ", row)


if __name__ == "__main__":
    analyze()
