#!/usr/bin/env python3
"""
CONVERGENCE PROOF 94: Minimum Δfc per interior value cycle
============================================================
KEY ARGUMENT: In any cycle of the TP subgraph, each interior position j
must fire and return to its value. The net Δfc per complete value cycle
at j is bounded below. If this bound times the number of interior positions
exceeds the boundary Δfc budget (+4), no cycle exists.

Test: what is the minimum net Δfc for a single complete value cycle at
an interior position j, considering that R = c[j+1] may change?

Interior TP entries and their Δfc:
  (0,1,0)→0: Δfc=-2    (0,1,2)→0: Δfc=-1    (0,2,2)→0: Δfc=0
  (1,0,0)→1: Δfc=0     (1,0,1)→1: Δfc=-2    (1,0,2)→1: Δfc=-1
  (1,1,2)→2: Δfc=0

Value cycles and their MINIMUM net Δfc:
  0→1→0: -2 or -1 (depends on R)
  0→1→2→0: -1 or 0 (depends on R changes; 0 requires R=0 then R=2)
  etc.

Also: compute the actual minimum-Δfc paths from each config back toward
itself in the TP DAG. If no short return path exists, the cycle argument
strengthens.
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

    # Part 1: Enumerate all possible value cycles at an interior position
    # and compute min Δfc for each, assuming R can change freely.
    print("="*70)
    print("PART 1: Value cycle Δfc analysis")
    print("="*70)

    # Interior TP entries: (L, S, R) → out, with Δfc
    tp_entries = {
        (0,1,0,0): -2, (0,1,2,0): -1, (0,2,2,0): 0,
        (1,0,0,1): 0,  (1,0,1,1): -2, (1,0,2,1): -1,
        (1,1,2,2): 0,
    }

    # Build value transition graph with (L, R) context
    # Edge: (S, L, R) → out, Δfc
    trans = {}  # trans[S] = list of (L, R, out, dfc)
    for (L, S, R, out), dfc in tp_entries.items():
        if S not in trans:
            trans[S] = []
        trans[S].append((L, R, out, dfc))

    print("\nValue transition graph:")
    for S in sorted(trans.keys()):
        for L, R, out, dfc in trans[S]:
            print(f"  {S}→{out}  L={L} R={R}  Δfc={dfc:+d}")

    # Find all minimal value cycles and their minimum Δfc
    # A value cycle: sequence of values v0→v1→...→vk=v0
    # At each step, we choose (L, R) freely.
    # Min Δfc = sum of chosen Δfc values.

    print("\n\nAll value cycles at a single position (min Δfc each):")
    # Enumerate cycles up to length 6
    for start_val in [0, 1, 2]:
        # BFS/DFS for cycles
        # State: current value. Track path and accumulated Δfc.
        stack = [(start_val, [start_val], 0)]  # (val, path, total_dfc)
        seen_cycles = set()
        while stack:
            val, path, total_dfc = stack.pop()
            for L, R, out, dfc in trans.get(val, []):
                new_dfc = total_dfc + dfc
                new_path = path + [out]
                if out == start_val and len(new_path) > 2:
                    # Found a cycle
                    cycle_key = tuple(new_path[:-1])
                    if cycle_key not in seen_cycles:
                        seen_cycles.add(cycle_key)
                        # Find min Δfc for this cycle shape
                        # by choosing best (L,R) at each step
                        min_dfc = compute_min_cycle_dfc(new_path[:-1], trans)
                        max_dfc = compute_max_cycle_dfc(new_path[:-1], trans)
                        print(f"  Cycle {new_path}: min_Δfc={min_dfc}, max_Δfc={max_dfc}")
                elif len(new_path) <= 6:
                    stack.append((out, new_path, new_dfc))

    # Part 2: For each n, compute the total Δfc budget
    print("\n" + "="*70)
    print("PART 2: Cycle Δfc budget analysis per n")
    print("="*70)

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
                            tp_edges.append((c, succ, i))
                            tp_adj[c].append((succ, i, fc(succ, n) - fc(c, n)))

        # Count Δfc > 0 edges and max boundary Δfc contribution
        dfc_pos_edges = [(c, s, p) for c, s, p in tp_edges
                         if fc(s, n) > fc(c, n)]
        max_single_dfc = max((fc(s, n) - fc(c, n)) for c, s, p in tp_edges) if tp_edges else 0
        total_dfc_pos = sum(fc(s, n) - fc(c, n) for c, s, p in dfc_pos_edges)

        # For each position, what Δfc values are possible?
        dfc_by_pos = defaultdict(set)
        for c, s, p in tp_edges:
            dfc_by_pos[p].add(fc(s, n) - fc(c, n))

        # Count interior positions (using T_mid, positions 2 to n-3)
        n_interior = max(0, n - 4)  # positions 2, 3, ..., n-3

        print(f"\nn={n}: {len(tp_edges)} TP edges, {n_interior} interior positions")
        print(f"  Δfc range by position:")
        for p in range(n):
            dfc_vals = sorted(dfc_by_pos.get(p, set()))
            pos_type = ["T_bot", "T_low"] + ["T_mid"]*(n-4) + ["T_high", "T_top"]
            print(f"    pos {p} ({pos_type[p]}): Δfc ∈ {dfc_vals}")

        # KEY: what is the maximum Δfc > 0 along ANY path?
        # We know this is ≤ 4 (from rank-3 Δfc>0 subgraph).
        # Verify:
        max_fc_gain = 0
        tp_adj_ge0 = defaultdict(list)
        tp_nodes = set()
        for c, s, p in tp_edges:
            dfc_val = fc(s, n) - fc(c, n)
            tp_nodes.add(c)
            tp_nodes.add(s)
            if dfc_val >= 0:
                tp_adj_ge0[c].append(s)

        # BFS for max fc gain on Δfc≥0 paths
        for c in tp_nodes:
            if not tp_adj_ge0.get(c):
                continue
            fc_c = fc(c, n)
            stack = [(c, 0)]
            visited = {c: 0}
            while stack:
                node, gain = stack.pop()
                max_fc_gain = max(max_fc_gain, gain)
                for s in tp_adj_ge0.get(node, []):
                    new_gain = gain + (fc(s, n) - fc(node, n))
                    if s not in visited or new_gain > visited[s]:
                        visited[s] = new_gain
                        if new_gain <= 20:
                            stack.append((s, new_gain))

        # Minimum net Δfc per interior position in cycle
        # With rightmost position having constant R:
        # - R=0: min net = -2 (cycle 0→1→0)
        # - R=1: can't cycle (only 0→1, stuck)
        # - R=2: min net = -1 (cycle 0→1→2→0)
        # With non-rightmost (R changes): min net = 0 (if R reaches 2)

        # LOWER BOUND on total interior Δfc:
        # At least the rightmost contributes -1.
        # Each "layer" of the 2-wave propagation allows one more position
        # to achieve 0, but requires one more position below to contribute -1.
        # Net: about half the positions contribute -1.

        # ACTUAL minimum: test by finding longest path with max total Δfc
        # This gives the CLOSEST to a cycle (minimum total |Δfc|)

        # Find paths with total Δfc closest to 0
        # BFS tracking (config, total_Δfc) — looking for configs reachable
        # from themselves with total Δfc close to 0
        # For efficiency, just track max and min total Δfc per config

        print(f"  Max fc gain on Δfc≥0 path: {max_fc_gain}")
        print(f"  Budget analysis: boundary can contribute at most +{max_fc_gain}")
        print(f"  Interior positions: {n_interior}")
        print(f"  If each interior pos contributes ≥ -1: total interior ≥ -{n_interior}")
        print(f"  Cycle possible only if {n_interior} ≤ {max_fc_gain}:"
              f" n ≤ {max_fc_gain + 4}")
        print(f"  Currently n={n}:"
              f" {'POTENTIALLY possible' if n_interior <= max_fc_gain else 'IMPOSSIBLE by budget'}")

        print(f"  Time: {time.time()-t0:.1f}s")


def compute_min_cycle_dfc(cycle_values, trans):
    """Compute minimum total Δfc for a cycle, choosing best (L,R) at each step."""
    total = 0
    for i in range(len(cycle_values)):
        S = cycle_values[i]
        out = cycle_values[(i + 1) % len(cycle_values)]
        # Find minimum Δfc entry with S→out
        min_dfc = float('inf')
        for L, R, o, dfc in trans.get(S, []):
            if o == out:
                min_dfc = min(min_dfc, dfc)
        if min_dfc == float('inf'):
            return float('inf')  # impossible
        total += min_dfc
    return total


def compute_max_cycle_dfc(cycle_values, trans):
    """Compute maximum total Δfc for a cycle, choosing best (L,R) at each step."""
    total = 0
    for i in range(len(cycle_values)):
        S = cycle_values[i]
        out = cycle_values[(i + 1) % len(cycle_values)]
        max_dfc = float('-inf')
        for L, R, o, dfc in trans.get(S, []):
            if o == out:
                max_dfc = max(max_dfc, dfc)
        if max_dfc == float('-inf'):
            return float('-inf')
        total += max_dfc
    return total


if __name__ == '__main__':
    main()
