#!/usr/bin/env python3
"""
CONVERGENCE PROOF 85: Find monotone quantity in triple-preserved subgraph
=========================================================================
The TP subgraph (Δexp2=0, Δint21=0, Δexp2_wt=0) is verified as DAG n=5..12.
Goal: find a quantity that strictly decreases on EVERY TP edge → analytical DAG proof.

Key structural facts (from proof83):
- T_mid at j≥3: only 7 TP entries, ALL have L∈{0,1}, Δfc≤0
  6 are copy_L (out=L), 1 is copy_R (1,1,2)→2
- T_mid at j=2: 9 TP entries (7 + (2,0,2)→2 and (2,1,1)→0)
- T_high: 8 TP entries, all L∈{0,1}
- T_bot/T_low/T_top: all privileged entries are TP
- Anomalous (Δfc>0) TP entries: only at positions 0, 2, n-2, n-1

Test many candidates for monotonicity within the TP subgraph.
"""
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import defaultdict, Counter


def int_21(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)


def int_20(c, n):
    return sum(1 for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)


def intj_20(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 0)


def intj_21(c, n):
    return sum(j for j in range(2, n - 2) if c[j] == 2 and c[(j + 1) % n] == 1)


def exp2_count(c, n):
    return int_20(c, n) + int_21(c, n)


def exp2_weight(c, n):
    return intj_20(c, n) + intj_21(c, n)


def fc(c, n):
    return sum(1 for j in range(n) if c[j] != c[(j + 1) % n])


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in range(5, 11):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build triple-preserved subgraph
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

        elapsed = time.time() - t0
        print(f"\n{'='*70}")
        print(f"n={n}: {len(tp_edges)} TP edges ({elapsed:.1f}s)")

        # Define candidate quantities
        def interior_fc(c):
            return sum(1 for j in range(2, n - 2) if c[j] != c[(j + 1) % n])

        def deep_interior_fc(c):
            return sum(1 for j in range(3, n - 3) if c[j] != c[(j + 1) % n])

        def boundary_fc(c):
            return fc(c, n) - interior_fc(c)

        def cnt_2_interior(c):
            return sum(1 for j in range(2, n - 2) if c[j] == 2)

        def cnt_2_full(c):
            return sum(1 for j in range(n) if c[j] == 2)

        def cnt_0_interior(c):
            return sum(1 for j in range(2, n - 2) if c[j] == 0)

        def cnt_1_interior(c):
            return sum(1 for j in range(2, n - 2) if c[j] == 1)

        def spos_2_interior(c):
            return sum(j for j in range(2, n - 2) if c[j] == 2)

        def spos_01_interior(c):
            return sum(j for j in range(2, n - 2) if c[j] in (0, 1))

        def weighted_sum(c):
            return sum(j * c[j] for j in range(n))

        def weighted_sum_int(c):
            return sum(j * c[j] for j in range(2, n - 2))

        def inv_weighted_sum(c):
            return sum((n - 1 - j) * c[j] for j in range(n))

        def lex_lr(c):
            """Lex order left-to-right (tuple comparison)."""
            return c

        def lex_rl(c):
            """Lex order right-to-left."""
            return tuple(reversed(c))

        def pair_sum(c):
            """Sum of (j * pair_code) for interior pairs."""
            return sum(j * (3 * c[j] + c[(j + 1) % n])
                      for j in range(2, n - 2))

        def boundary_state(c):
            return (c[0], c[1], c[n - 2], c[n - 1])

        def cnt_disagree_left(c):
            """Count of interior j where c[j] != c[j-1]."""
            return sum(1 for j in range(2, n - 2) if c[j] != c[j - 1])

        def cnt_disagree_right(c):
            """Count of interior j where c[j] != c[j+1]."""
            return sum(1 for j in range(2, n - 2) if c[j] != c[(j + 1) % n])

        def wt_disagree_left(c):
            """Sum of j where c[j] != c[j-1], interior."""
            return sum(j for j in range(2, n - 2) if c[j] != c[j - 1])

        def wt_disagree_right(c):
            """Sum of j where c[j] != c[j+1], interior."""
            return sum(j for j in range(2, n - 2) if c[j] != c[(j + 1) % n])

        def inv_wt_disagree_left(c):
            """Sum of (n-1-j) where c[j] != c[j-1], interior."""
            return sum((n - 1 - j) for j in range(2, n - 2) if c[j] != c[j - 1])

        # Lex-based: fc, then tie-break
        def fc_lex_lr(c):
            return (fc(c, n),) + c

        def fc_lex_rl(c):
            return (fc(c, n),) + tuple(reversed(c))

        def neg_fc_lex_lr(c):
            return (-fc(c, n),) + c

        # fc + interior disagree combinations
        def fc_plus_dis(c):
            return fc(c, n) * 100 + cnt_disagree_left(c)

        def fc_plus_wdis(c):
            return fc(c, n) * 10000 + wt_disagree_left(c)

        quantities = {
            'fc': lambda c: fc(c, n),
            'int_fc': interior_fc,
            'deep_int_fc': deep_interior_fc,
            'bnd_fc': boundary_fc,
            'cnt2_int': cnt_2_interior,
            'cnt2_full': cnt_2_full,
            'cnt0_int': cnt_0_interior,
            'cnt1_int': cnt_1_interior,
            'spos2_int': spos_2_interior,
            'spos01_int': spos_01_interior,
            'wt_sum': weighted_sum,
            'wt_sum_int': weighted_sum_int,
            'inv_wt_sum': inv_weighted_sum,
            'pair_sum': pair_sum,
            'dis_L': cnt_disagree_left,
            'dis_R': cnt_disagree_right,
            'wt_dis_L': wt_disagree_left,
            'wt_dis_R': wt_disagree_right,
            'inv_wt_dis_L': inv_wt_disagree_left,
        }

        # Also test lex orderings
        lex_quantities = {
            'lex_LR': lex_lr,
            'lex_RL': lex_rl,
            'fc_lex_LR': fc_lex_lr,
            'fc_lex_RL': fc_lex_rl,
            'neg_fc_lex_LR': neg_fc_lex_lr,
        }

        print(f"\n  Scalar monotonicity tests:")
        for qname, qfunc in quantities.items():
            neg = zer = pos = 0
            for u, v, _ in tp_edges:
                d = qfunc(v) - qfunc(u)
                if d < 0: neg += 1
                elif d > 0: pos += 1
                else: zer += 1
            if pos == 0 and neg > 0:
                marker = " *** ALWAYS <= 0"
            elif neg == 0 and pos > 0:
                marker = " *** ALWAYS >= 0"
            elif neg == 0 and pos == 0:
                marker = " *** CONSTANT"
            else:
                marker = ""
            print(f"    {qname:20s}: neg={neg:>6d} zero={zer:>6d} pos={pos:>6d}{marker}")

        print(f"\n  Lex monotonicity tests:")
        for qname, qfunc in lex_quantities.items():
            neg = zer = pos = 0
            for u, v, _ in tp_edges:
                qu = qfunc(u)
                qv = qfunc(v)
                if qv < qu: neg += 1
                elif qv > qu: pos += 1
                else: zer += 1
            if pos == 0 and neg > 0:
                marker = " *** ALWAYS DECREASING"
            elif neg == 0 and pos > 0:
                marker = " *** ALWAYS INCREASING"
            else:
                marker = ""
            print(f"    {qname:20s}: dec={neg:>6d} same={zer:>6d} inc={pos:>6d}{marker}")

        # Test 2D lex: (q1 dec, then q2 dec on q1-preserved edges)
        print(f"\n  2D lex tests (q1, q2) where q1 non-increasing:")
        good_q1 = [qn for qn, qf in quantities.items()
                    if all(qf(v) - qf(u) <= 0 for u, v, _ in tp_edges)]
        for q1name in good_q1:
            q1f = quantities[q1name]
            # Check preserved edges
            preserved = [(u, v, p) for u, v, p in tp_edges if q1f(v) == q1f(u)]
            if not preserved:
                print(f"    ({q1name}, *): q1 STRICT on all edges!")
                continue
            for q2name, q2f in quantities.items():
                if q2name == q1name:
                    continue
                neg2 = zer2 = pos2 = 0
                for u, v, _ in preserved:
                    d = q2f(v) - q2f(u)
                    if d < 0: neg2 += 1
                    elif d > 0: pos2 += 1
                    else: zer2 += 1
                if pos2 == 0 and neg2 > 0:
                    pct_strict = 100 * (len(tp_edges) - len(preserved) + neg2) / len(tp_edges)
                    pct_remain = 100 * zer2 / len(tp_edges)
                    print(f"    ({q1name}, {q2name}): q2 ALWAYS <= 0 on q1-preserved. "
                          f"Strict: {pct_strict:.1f}%, remain: {pct_remain:.1f}%")

        print(f"  Time: {time.time()-t0:.1f}s")

    print(f"\n{'='*70}")
    print("DONE")


if __name__ == '__main__':
    main()
