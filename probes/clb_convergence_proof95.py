#!/usr/bin/env python3
"""
CONVERGENCE PROOF 95: Tighter Δfc budget — per-group analysis
==============================================================
The budget argument: in a TP cycle, total Δfc = 0.

KEY FACTS:
1. Interior positions j ∈ {3,...,n-3}: ALL entries have Δfc ≤ 0.
   So D_j = Σ Δfc (over all firings at j in cycle) ≤ 0.
2. Position 1: ALL entries have Δfc ≤ 0. D_1 ≤ 0.
3. Position 2: entries have Δfc ∈ {-2,-1,0,+1}. D_2 can be > 0.
4. Positions 0, n-2, n-1: some entries have Δfc > 0.

CLAIM (Rightmost Anchor): For the rightmost interior position k
that fires, D_k ≤ -1 because:
- R = c[k+1] is constant (k+1 doesn't fire, or is boundary).
- The best value cycle with constant R has max Δfc = -1 (for R=2)
  or -2 (for R=0).

CLAIM (Group Structure): For every group of p consecutive interior
positions ending at k, total D ≤ -1 (the group pays -1 collectively).
This means positions j < k can achieve D_j = 0 by using the 3-cycle.

QUESTION: How many groups fit into the interior? How many -1 anchors?

Test this computationally: for each TP component (fixed triple), compute
the MINIMUM total Δfc over ALL paths from each config to each other
config. If no cycle has Δfc = 0, we have the proof.
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

    for n_val in range(5, 12):
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build TP edges with Δfc annotation
        tp_edges = []
        tp_adj = defaultdict(list)
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
                            dfc_val = fc(succ, n) - fc(c, n)
                            tp_edges.append((c, succ, i, dfc_val))
                            tp_adj[c].append((succ, dfc_val))

        print(f"\n{'='*70}")
        print(f"n={n}: {len(tp_edges)} TP edges")

        # KEY TEST: for each position, verify D ≤ 0 for complete value cycles.
        # A "complete value cycle at position j" is: a path in the TP graph
        # where position j returns to its start value, and we track the total Δfc.

        # Instead of enumerating cycles, verify the claim directly:
        # "Interior positions 3..n-3 have ALL entries with Δfc ≤ 0"
        for pos in range(n):
            max_dfc = max(dfc for _, _, p, dfc in tp_edges if p == pos)
            min_dfc = min(dfc for _, _, p, dfc in tp_edges if p == pos) if any(p == pos for _, _, p, _ in tp_edges) else 0
            if max_dfc > 0:
                print(f"  pos {pos}: max Δfc = {max_dfc:+d}  *** POSITIVE ***")

        # For the STRICT budget argument:
        # Partition TP edges by firing position into "interior non-positive" and "boundary/anomalous"
        int_neg = [(c, s, p, d) for c, s, p, d in tp_edges
                   if 3 <= p <= n-3 and d < 0]
        int_zero = [(c, s, p, d) for c, s, p, d in tp_edges
                    if 3 <= p <= n-3 and d == 0]
        bnd_pos = [(c, s, p, d) for c, s, p, d in tp_edges
                   if d > 0]
        print(f"  Interior Δfc<0: {len(int_neg)}, Interior Δfc=0: {len(int_zero)}, Boundary Δfc>0: {len(bnd_pos)}")

        # Which positions fire Δfc > 0 edges?
        pos_with_positive = set(p for _, _, p, d in tp_edges if d > 0)
        print(f"  Positions with Δfc > 0: {sorted(pos_with_positive)}")

        # STRONGEST TEST: For each TP component (group with same triple),
        # find the max total Δfc along any path. If max = -∞ for all
        # paths returning to start, no cycle exists.

        # Group configs by (exp2_count, int_21, exp2_weight)
        triple_groups = defaultdict(list)
        for c in bad_list:
            key = (exp2_count(c, n), int_21(c, n), exp2_weight(c, n))
            triple_groups[key].append(c)

        # For each component, use Bellman-Ford to find max total Δfc
        # from each node (looking for positive cycles = bad).
        # Since we know it's a DAG, Bellman-Ford will converge.
        # Use LONGEST PATH (max Δfc) to find closest to a cycle.

        # Actually, simpler: use BFS/DFS with fc tracking to find
        # max fc accumulation from any config back to itself.
        # We know this is impossible (DAG), but let's track how close
        # we get to returning with same or higher fc.

        # For each component, compute max and min total Δfc over all paths
        max_total_pos = 0  # max total positive Δfc on any path
        max_path_len = 0

        for key, configs in triple_groups.items():
            if len(configs) < 2:
                continue
            config_set = set(configs)
            # BFS tracking accumulated Δfc
            for start in configs:
                if start not in tp_adj:
                    continue
                # Track max accumulated Δfc from start
                visited = {start: 0}
                stack = [(start, 0)]
                while stack:
                    node, acc_dfc = stack.pop()
                    for succ, dfc_val in tp_adj.get(node, []):
                        new_acc = acc_dfc + dfc_val
                        if succ not in visited or new_acc > visited[succ]:
                            visited[succ] = new_acc
                            max_total_pos = max(max_total_pos, new_acc)
                            max_path_len = max(max_path_len, abs(new_acc))
                            if new_acc <= 20:  # safety limit
                                stack.append((succ, new_acc))
                break  # Just check one start per component for speed

        print(f"  Max accumulated Δfc on any path: {max_total_pos}")

        # NEW: Count how many TP edges fire at positions with D ≤ 0 only
        # vs positions that can have D > 0.
        # In a cycle, sum of ALL edge Δfc = 0.
        # Edges at positions {3..n-3}: Δfc ≤ 0.
        # Edges at position 1: Δfc ≤ 0.
        # So edges at {1, 3..n-3}: total ≤ 0.
        # Edges at {0, 2, n-2, n-1}: must compensate.

        # What's the total Δfc budget from {0, 2, n-2, n-1}?
        # Count max Δfc per firing for these positions.
        for p in sorted(pos_with_positive):
            entries_pos = [(d, c[(p-1)%n], c[p], c[(p+1)%n], s[p])
                           for c, s, pp, d in tp_edges if pp == p and d > 0]
            if entries_pos:
                print(f"  Anomalous entries at pos {p}:")
                entry_types = Counter()
                for d, L, S, R, out in entries_pos:
                    entry_types[(L, S, R, out, d)] += 1
                for (L, S, R, out, d), cnt in sorted(entry_types.items()):
                    print(f"    ({L},{S},{R})->{out} Δfc={d:+d}: {cnt}")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
