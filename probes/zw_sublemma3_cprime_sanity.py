#!/usr/bin/env python3
"""
Phase 0k: sanity check for Sub-lemma 3 Case C' matching sub-cases.

Case C'1 (fc_run[r_b]=1, fc_run[l_c]=2):
  Walker on line (ring \\ {l_c}) from word[e+2] in {l_c-1, c} to
  word[s-2] in {b, r_b, r_b+1}.
  Six sub-cases (three contradict by line displacement, three "match").

For the three matching sub-cases (word[e+2] = l_c-1 + any word[s-2]),
the walker must visit c (for c_2 fire) because fc_comp[c] = 1 and c_2
is in middle-middle (not at a bounce).

Claim: any walk on the path graph (line) from k=0 to k(word[s-2]) in
{I-1, I-2, I-3} that visits k=n-2 (= c) must pass through k=I-1 (= b)
at least twice: once on the forward pass to c, and once on the return
to near-r_b. But fc_middle-middle[b] = 1. Contradiction.

Actually more precisely: walker visits k=I-1 on forward pass (since
0 < I-1 < n-2 and line is simple path). If end position has k <= I-1,
walker doesn't necessarily pass through k=I-1 on return. Let's check:
  - k(end) = I-1 (b): walker ends AT b; must visit b at least once on
    the way forward AND the end. So at least 1 visit to b on forward
    (through) and 1 at end (stop). Wait, if walker goes forward all
    the way to c and comes back to b, then walker visits b TWICE:
    once at k=I-1 on the way to c, once at the end.
  - k(end) = I-2 (r_b): walker visits b on forward (k=I-1 > k(end))
    and on return path (going from c back through b to r_b). Twice.
  - k(end) = I-3 (r_b+1): same, twice.

In all three matching sub-cases, walker visits b >= 2 times, but
fc_middle-middle[b] = 1. Contradiction.
"""


def check_C_prime_1(n, I):
    """
    Count min visits to b on a path-graph walk from k=0 (l_c-1)
    to k_end in {I-1, I-2, I-3}, passing through k=n-2 (c).
    """
    if I < 3:
        return None  # Case C' doesn't apply at I=2
    k_start = 0       # l_c - 1
    k_c = n - 2       # c
    k_b = I - 1       # b
    results = {}
    for end_name, k_end in [("b", I - 1), ("r_b", I - 2), ("r_b+1", I - 3)]:
        # Simple path walk from k_start to k_end visiting k_c:
        # must go forward to k_c (visiting k_b on the way since 0 < k_b < k_c),
        # then back from k_c to k_end.
        # Count visits to k_b:
        visits_fwd = 1 if k_start <= k_b <= k_c else 0
        # Return path: from k_c to k_end; visits k_b if k_end <= k_b <= k_c.
        visits_ret = 1 if k_end <= k_b <= k_c else 0
        total_b_visits = visits_fwd + visits_ret
        allowed_b_visits = 1  # fc_middle-middle[b] = 1
        contradict = total_b_visits > allowed_b_visits
        results[end_name] = (total_b_visits, allowed_b_visits, contradict)
    return results


if __name__ == "__main__":
    print("=== Sub-lemma 3 Case C'1 matching sub-cases ===")
    for n, I in [(9, 3), (9, 4), (9, 6), (11, 4), (11, 6), (11, 8)]:
        print(f"\n  n={n}, I={I}:")
        res = check_C_prime_1(n, I)
        for end, (tv, av, cont) in res.items():
            tag = "CONTRADICT" if cont else "OK"
            print(f"    word[s-2]={end}:  b-visits = {tv}, "
                  f"allowed = {av}  [{tag}]")
