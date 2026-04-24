#!/usr/bin/env python3
"""
CONVERGENCE PROOF 96: Exhaustive search for 4th monotone quantity
=================================================================
We have 3 monotone quantities (exp2_count, int_21, exp2_weight) that
partition bad→bad edges into TP edges (all 3 preserved) and non-TP
edges (at least one decreases).

Within the TP subgraph, we need a 4th quantity that's monotone.
No pair-weight or triple-weight potential exists (LP infeasible).
But maybe a DIFFERENT type of quantity works.

Search strategy: test many candidate quantities for monotonicity
on TP edges. For each candidate, count violations. Find the one
with fewest violations. Even if not zero, the pattern of violations
may suggest the right correction.

Key constraint: position 1 and positions 3..n-3 have Δfc ≤ 0,
so fc is "almost monotone" — violations only at {0, 2, n-2, n-1}.

Also: verify the max fc gain = 4 vs 2 discrepancy.
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


def main():
    sys.stdout.reconfigure(line_buffering=True)

    for n_val in [7, 8, 9]:
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

        # Verify max fc gain across ALL TP components
        tp_adj = defaultdict(list)
        tp_adj_ge0 = defaultdict(list)
        tp_nodes = set()
        for c, s, p in tp_edges:
            dfc = fc(s, n) - fc(c, n)
            tp_adj[c].append((s, dfc))
            tp_nodes.add(c)
            tp_nodes.add(s)
            if dfc >= 0:
                tp_adj_ge0[c].append(s)

        # Max fc gain on Δfc≥0 paths (check ALL starting configs)
        max_fc_gain = 0
        for c in tp_nodes:
            if not tp_adj_ge0.get(c):
                continue
            fc_c = fc(c, n)
            stack = [(c, 0)]
            visited = {c: 0}
            while stack:
                node, gain = stack.pop()
                if gain > max_fc_gain:
                    max_fc_gain = gain
                for s in tp_adj_ge0.get(node, []):
                    new_gain = gain + (fc(s, n) - fc(node, n))
                    if s not in visited or new_gain > visited[s]:
                        visited[s] = new_gain
                        if new_gain <= 20:
                            stack.append((s, new_gain))

        print(f"  Max fc gain on Δfc≥0 path (all starts): {max_fc_gain}")

        # Max fc gain on ANY path
        max_any_gain = 0
        for c in list(tp_nodes)[:500]:  # sample
            stack = [(c, 0)]
            visited = {c: 0}
            while stack:
                node, gain = stack.pop()
                if gain > max_any_gain:
                    max_any_gain = gain
                for s, dfc in tp_adj.get(node, []):
                    new_gain = gain + dfc
                    if s not in visited or new_gain > visited[s]:
                        visited[s] = new_gain
                        if new_gain <= 20 and abs(new_gain) <= 20:
                            stack.append((s, new_gain))
        print(f"  Max fc gain on ANY path (500 starts): {max_any_gain}")

        # Now search for 4th monotone quantity
        # Candidates based on boundary + interior structure
        def q_fc(c):
            return fc(c, n)

        def q_bnd_state(c):
            """Boundary state as a number."""
            return c[0] + 2*c[1] + 6*c[n-2] + 18*c[n-1]

        def q_interior_sum(c):
            return sum(c[j] for j in range(2, n-2))

        def q_cnt0(c):
            return sum(1 for j in range(2, n-2) if c[j] == 0)

        def q_cnt2(c):
            return sum(1 for j in range(2, n-2) if c[j] == 2)

        def q_agree(c):
            return sum(1 for j in range(2, n-2) if c[j] == c[j-1])

        def q_int_fc(c):
            """Interior face changes."""
            return sum(1 for j in range(2, n-3) if c[j] != c[j+1])

        def q_pair20(c):
            """Count of (2,0) pairs in interior."""
            return sum(1 for j in range(2, n-3) if c[j] == 2 and c[j+1] == 0)

        def q_pair12(c):
            """Count of (1,2) pairs in interior."""
            return sum(1 for j in range(2, n-3) if c[j] == 1 and c[j+1] == 2)

        def q_pair01(c):
            """Count of (0,1) pairs in interior."""
            return sum(1 for j in range(2, n-3) if c[j] == 0 and c[j+1] == 1)

        def q_pair10(c):
            return sum(1 for j in range(2, n-3) if c[j] == 1 and c[j+1] == 0)

        # Weighted sums
        def q_wt_pair_RL(c):
            """Σ j * [c[j]=c[j-1]] in interior."""
            return sum(j for j in range(2, n-2) if c[j] == c[j-1])

        def q_wt_pair_LR(c):
            """Σ (n-j) * [c[j]=c[j-1]] in interior."""
            return sum((n-j) for j in range(2, n-2) if c[j] == c[j-1])

        def q_max_run(c):
            """Length of longest run of same value in interior."""
            if n <= 4: return 0
            max_run = 1
            cur = 1
            for j in range(3, n-2):
                if c[j] == c[j-1]:
                    cur += 1
                    max_run = max(max_run, cur)
                else:
                    cur = 1
            return max_run

        def q_left_run(c):
            """Length of leftmost run starting at position 2."""
            if n <= 4: return 0
            run = 1
            for j in range(3, n-2):
                if c[j] == c[j-1]:
                    run += 1
                else:
                    break
            return run

        # Combo: fc * large + secondary
        C = 2 * n  # large enough
        def q_fc_agree(c):
            return C * fc(c, n) - q_agree(c)

        def q_fc_cnt2(c):
            return C * fc(c, n) + q_cnt2(c)

        def q_fc_intsum(c):
            return C * fc(c, n) - q_interior_sum(c)

        def q_fc_wt(c):
            return C * fc(c, n) + q_wt_pair_LR(c)

        def q_fc_leftrun(c):
            return C * fc(c, n) - q_left_run(c)

        # Pair-count combos
        def q_pair_combo1(c):
            """p12 + p01 - p20 - p10."""
            return q_pair12(c) + q_pair01(c) - q_pair20(c) - q_pair10(c)

        candidates = [
            ("fc", q_fc, "dec"),
            ("cnt0", q_cnt0, "inc"),
            ("cnt2", q_cnt2, "dec"),
            ("agree", q_agree, "inc"),
            ("int_fc", q_int_fc, "dec"),
            ("pair20", q_pair20, "dec"),
            ("pair12", q_pair12, "dec"),
            ("pair01", q_pair01, "dec"),
            ("pair10", q_pair10, "dec"),
            ("interior_sum", q_interior_sum, "dec"),
            ("wt_pair_RL", q_wt_pair_RL, "inc"),
            ("wt_pair_LR", q_wt_pair_LR, "inc"),
            ("max_run", q_max_run, "inc"),
            ("left_run", q_left_run, "inc"),
            ("fc*C-agree", q_fc_agree, "dec"),
            ("fc*C+cnt2", q_fc_cnt2, "dec"),
            ("fc*C-intsum", q_fc_intsum, "dec"),
            ("fc*C+wt_LR", q_fc_wt, "dec"),
            ("fc*C-leftrun", q_fc_leftrun, "dec"),
            ("pair_combo1", q_pair_combo1, "dec"),
        ]

        print(f"\n  Candidate 4th quantities (within TP subgraph):")
        results = []
        for name, qfn, direction in candidates:
            viol = 0
            for c, s, p in tp_edges:
                qc = qfn(c)
                qs = qfn(s)
                if direction == "dec" and qs >= qc:
                    viol += 1
                elif direction == "inc" and qs <= qc:
                    viol += 1
            pct = 100 * viol / len(tp_edges) if tp_edges else 0
            results.append((viol, name, direction))
            if viol == 0:
                print(f"    {name} ({direction}): 0 violations ✓✓✓")
            elif pct < 10:
                print(f"    {name} ({direction}): {viol} viol ({pct:.1f}%)")

        # Show top 5 by fewest violations
        results.sort()
        print(f"\n  Top 5 candidates:")
        for viol, name, direction in results[:5]:
            pct = 100 * viol / len(tp_edges)
            print(f"    {name} ({direction}): {viol} viol ({pct:.1f}%)")

        # For the best candidate, analyze WHERE violations occur
        best_name = results[0][1]
        best_dir = results[0][2]
        best_fn = [qfn for name, qfn, d in candidates if name == best_name][0]
        viol_by_pos = Counter()
        for c, s, p in tp_edges:
            qc = best_fn(c)
            qs = best_fn(s)
            if (best_dir == "dec" and qs >= qc) or (best_dir == "inc" and qs <= qc):
                viol_by_pos[p] += 1
        if viol_by_pos:
            print(f"\n  Best ({best_name}) violations by position: {dict(sorted(viol_by_pos.items()))}")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
