#!/usr/bin/env python3
"""
CONVERGENCE PROOF 91: Agreement set analysis for TP subgraph
=============================================================
Test whether |A(c)| = #{j in [a,b] : c[j]=c[j-1]} is non-decreasing
on TP edges, for various ranges [a,b].

Key insight from analysis:
- Interior copy_L at j>=3: always Δ|A| >= 0
- Interior copy_R (1,1,2)->2 at j: Δ|A| = 0 (j leaves, j+1 enters)
- But boundary effects at j=2 or j=n-3 can cause decrease

Test multiple range choices and boundary corrections.
"""
import sys
import os
import time
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter


def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)

def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)

def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)

def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)

def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def agree_count(c, n, lo, hi):
    """Count #{j in [lo,hi] : c[j] = c[j-1]}."""
    return sum(1 for j in range(lo, hi + 1) if c[j] == c[j - 1])


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 13):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build TP edges
        tp_edges = []
        for c in bad_list:
            e2c = exp2_count(c, n)
            i21c = int_21(c, n)
            ewc = exp2_weight(c, n)
            for i in range(n):
                L = c[(i - 1) % n]; S = c[i]; R = c[(i + 1) % n]
                out = fs[i](L, S, R)
                if out != S:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        e2s = exp2_count(succ, n)
                        i21s = int_21(succ, n)
                        ews = exp2_weight(succ, n)
                        if e2s == e2c and i21s == i21c and ews == ewc:
                            tp_edges.append((c, succ, i))

        print(f"\n{'='*70}")
        print(f"n={n}: {len(tp_edges)} TP edges")

        # Test various agreement ranges
        ranges_to_test = [
            (3, n - 3, "A[3,n-3]"),
            (2, n - 3, "A[2,n-3]"),
            (3, n - 2, "A[3,n-2]"),
            (2, n - 2, "A[2,n-2]"),
            (2, n - 1, "A[2,n-1]"),  # extending to top boundary
        ]

        for lo, hi, label in ranges_to_test:
            if hi < lo:
                continue
            violations = 0
            viol_by_pos = Counter()
            viol_details = []
            for c, succ, pos in tp_edges:
                a_old = agree_count(c, n, lo, hi)
                a_new = agree_count(succ, n, lo, hi)
                if a_new < a_old:
                    violations += 1
                    viol_by_pos[pos] += 1
                    if len(viol_details) < 5:
                        L = c[(pos - 1) % n]; S = c[pos]; R = c[(pos + 1) % n]
                        out = succ[pos]
                        viol_details.append((pos, L, S, R, out, a_old, a_new))

            if violations == 0:
                print(f"  {label}: MONOTONE (0 violations) ✓")
            else:
                print(f"  {label}: {violations} violations")
                top3 = viol_by_pos.most_common(5)
                print(f"    By position: {top3}")
                for pos, L, S, R, out, ao, an in viol_details[:3]:
                    print(f"    pos={pos} ({L},{S},{R})->{out} agree {ao}->{an}")

        # Now test: agreement set + fc combination
        # Φ = C * agree + something_else
        # Test: does (agree, fc) decrease lexicographically?
        # i.e., agree increases OR (agree same AND fc decreases)
        for lo, hi, label in [(2, n - 3, "A[2,n-3]"), (3, n - 3, "A[3,n-3]")]:
            if hi < lo:
                continue
            viol_lex = 0
            for c, succ, pos in tp_edges:
                a_old = agree_count(c, n, lo, hi)
                a_new = agree_count(succ, n, lo, hi)
                fc_old = fc(c, n)
                fc_new = fc(succ, n)
                # Lex: (-agree, fc) should decrease
                if (-a_new, fc_new) >= (-a_old, fc_old):
                    viol_lex += 1
            print(f"  Lex(-{label}, fc): {viol_lex} violations")

        # Test: weighted agreement Σ j * [c[j]=c[j-1]]
        for lo, hi, label in [(2, n - 3, "wA[2,n-3]"), (3, n - 3, "wA[3,n-3]")]:
            if hi < lo:
                continue
            def w_agree(c):
                return sum(j for j in range(lo, hi + 1) if c[j] == c[j - 1])
            violations = 0
            for c, succ, pos in tp_edges:
                if w_agree(succ) < w_agree(c):
                    violations += 1
            print(f"  Weighted {label}: {violations} violations")

        # Test: reverse weighted Σ (n-j) * [c[j]=c[j-1]]
        for lo, hi, label in [(2, n - 3, "rwA[2,n-3]"), (3, n - 3, "rwA[3,n-3]")]:
            if hi < lo:
                continue
            def rw_agree(c):
                return sum((n - j) for j in range(lo, hi + 1) if c[j] == c[j - 1])
            violations = 0
            for c, succ, pos in tp_edges:
                if rw_agree(succ) < rw_agree(c):
                    violations += 1
            print(f"  Rev-weighted {label}: {violations} violations")

        # Test: disagreement count (complement of agreement)
        # dis[lo,hi] = (hi - lo + 1) - agree[lo,hi]
        # Δdis = -Δagree. So if agree is non-decreasing, dis is non-increasing.

        # Test: position of leftmost disagreement
        def leftmost_disagree(c, lo, hi):
            for j in range(lo, hi + 1):
                if c[j] != c[j - 1]:
                    return j
            return hi + 1  # all agree

        for lo, hi, label in [(2, n - 3, "LD[2,n-3]"), (3, n - 3, "LD[3,n-3]")]:
            if hi < lo:
                continue
            viol = 0
            for c, succ, pos in tp_edges:
                ld_old = leftmost_disagree(c, lo, hi)
                ld_new = leftmost_disagree(succ, lo, hi)
                if ld_new < ld_old:  # leftmost disagreement moves left = bad
                    viol += 1
            print(f"  Leftmost disagree {label}: {viol} violations (want non-decreasing)")

        # Test: rightmost agreement
        def rightmost_agree(c, lo, hi):
            for j in range(hi, lo - 1, -1):
                if c[j] == c[j - 1]:
                    return j
            return lo - 1  # none agree

        for lo, hi, label in [(2, n - 3, "RA[2,n-3]"), (3, n - 3, "RA[3,n-3]")]:
            if hi < lo:
                continue
            viol = 0
            for c, succ, pos in tp_edges:
                ra_old = rightmost_agree(c, lo, hi)
                ra_new = rightmost_agree(succ, lo, hi)
                if ra_new < ra_old:
                    viol += 1
            print(f"  Rightmost agree {label}: {viol} violations")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
