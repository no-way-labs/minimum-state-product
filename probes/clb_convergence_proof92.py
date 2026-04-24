#!/usr/bin/env python3
"""
CONVERGENCE PROOF 92: Interior value-transition analysis
=========================================================
Analyze the TP subgraph's interior dynamics:

1. At each interior position j, what are the possible value transitions?
   - From 0: only 0→1 (copy_L with L=1)
   - From 1: 1→0 (copy_L, L=0) or 1→2 (copy_R, L=1,R=2)
   - From 2: only 2→0 (copy_L, L=0)

2. In a cycle, each position must return to its value. The transitions form
   cycles in {0,1,2}: either 0→1→0 (length 2) or 0→1→2→0 (length 3).

3. For position j to fire, it needs specific L = c[j-1] values.
   Track the "left-neighbor requirement chain": if j fires, what does j-1
   need to be? And for j-1 to provide that, what did j-1 fire to/from?

Also: compute the total number of firings per position in the DAG.
For a cycle to exist, need total in-degree = total out-degree at each node.
"""
import sys
import os
import time
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system, T_mid, T_bot, T_low, T_high, T_top
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


def get_tp_entry_type(c, pos, succ, n, ms, fs):
    """Classify a TP edge by its entry type."""
    L = c[(pos - 1) % n]
    S = c[pos]
    R = c[(pos + 1) % n]
    out = succ[pos]
    # Determine table
    if pos == 0:
        table_name = "T_bot"
    elif pos == 1:
        table_name = "T_low"
    elif pos == n - 2:
        table_name = "T_high"
    elif pos == n - 1:
        table_name = "T_top"
    else:
        table_name = "T_mid"
    return table_name, L, S, R, out


def main():
    sys.stdout.reconfigure(line_buffering=True)

    # First: analyze interior value transitions
    print("Interior TP entries (T_mid) — value transition graph:")
    print("  From 0:")
    for L in range(3):
        for R in range(3):
            out = T_mid[(L, 0, R)]
            if out != 0:
                print(f"    ({L},0,{R})->{out}  [0→{out}]")
    print("  From 1:")
    for L in range(3):
        for R in range(3):
            out = T_mid[(L, 1, R)]
            if out != 1:
                print(f"    ({L},1,{R})->{out}  [1→{out}]")
    print("  From 2:")
    for L in range(3):
        for R in range(3):
            out = T_mid[(L, 2, R)]
            if out != 2:
                print(f"    ({L},2,{R})->{out}  [2→{out}]")

    # Which of these are TP entries?
    # TP entries at j >= 3: the 7 known ones
    print("\nTP-preserved entries at interior j>=3 (all 7):")
    tp_entries = [
        (0,1,0,0), (0,1,2,0), (0,2,2,0),
        (1,0,0,1), (1,0,1,1), (1,0,2,1),
        (1,1,2,2),
    ]
    for L, S, R, out in tp_entries:
        kind = "copy_L" if out == L else ("copy_R" if out == R else "other")
        print(f"  ({L},{S},{R})->{out} [{S}→{out}] {kind}")

    # All T_mid firing entries (out != S)
    print("\nAll T_mid privileged entries:")
    all_priv = []
    for L in range(3):
        for S in range(3):
            for R in range(3):
                out = T_mid[(L, S, R)]
                if out != S:
                    is_tp = (L, S, R, out) in [(e[0],e[1],e[2],e[3]) for e in tp_entries]
                    kind = "copy_L" if out == L else ("copy_R" if out == R else "other")
                    print(f"  ({L},{S},{R})->{out} [{S}→{out}] {kind}"
                          f" {'TP' if is_tp else 'non-TP'}")
                    all_priv.append((L, S, R, out, is_tp))

    # Check: can position j return to its value through interior-only transitions?
    # Possible value cycles: 0→1→0 requires L going 1→0
    #                       0→1→2→0 requires L going 1→1→0
    #                       1→0→1 requires L going ? →1
    #                       1→2→0→1 requires L going 1→0→1
    print("\n\nValue cycles at an interior position:")
    print("  0→1→0: need entries (1,0,?)→1 then (0,1,?)→0")
    print("    L chain: L=1 for 0→1, L=0 for 1→0")
    print("    j-1 values: 1 then 0. j-1 must go 1→0.")
    print("    j-1 goes 1→0: entry (0,1,?)→0 [L of j-1 = 0]")
    print("    j-2 values: 0 then stay 0. j-2 must be 0 throughout.")
    print()
    print("  0→1→2→0: entries (1,0,?)→1, (1,1,2)→2, (0,2,2)→0")
    print("    L chain: L=1 for 0→1, L=1 for 1→2, L=0 for 2→0")
    print("    j-1 values: 1, 1, 0. j-1 must go 1→1→0.")
    print("    j-1 fires 1→0: entry (0,1,?)→0, L of j-1 = 0")
    print("    j-2 values while j-1=1: must be (anything, then 0)")
    print()
    print("  Key observation: to complete a cycle at position j,")
    print("  j-1 must change, requiring j-2 to provide contexts.")
    print("  This creates a LEFT-PROPAGATING CHAIN of requirements.")
    print("  But interior copy_L only propagates RIGHT.")
    print("  The chain must eventually reach the left boundary (pos 0 or 1).")

    # Now: for each n, analyze the TP edge types at each position
    for n_val in [5, 6, 7, 8]:
        t0 = time.time()
        ms, fs = build_system(n_val)
        result = verify_system(ms, fs)
        assert result['valid']
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_list = [c for c in all_configs if c not in good_set]
        bad_set = set(bad_list)
        n = n_val

        # Build TP edges with full info
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

        # Count firings at each position
        fire_count = Counter()
        entry_count = Counter()
        for c, succ, pos in tp_edges:
            fire_count[pos] += 1
            L = c[(pos - 1) % n]; S = c[pos]; R = c[(pos + 1) % n]
            out = succ[pos]
            entry_count[(pos, L, S, R, out)] += 1

        print(f"\n  Firings per position: {dict(sorted(fire_count.items()))}")

        print(f"\n  Entry types per position:")
        for pos in range(n):
            entries = [(L, S, R, out, cnt) for (p, L, S, R, out), cnt
                       in sorted(entry_count.items()) if p == pos]
            if entries:
                print(f"    pos {pos}:")
                for L, S, R, out, cnt in entries:
                    kind = "copy_L" if out == L else ("copy_R" if out == R else "other")
                    dfc_val = fc(list(range(n)), n)  # placeholder
                    # Compute actual Δfc for a sample edge with this entry
                    sample_dfc = None
                    for c, succ, p in tp_edges:
                        if p == pos:
                            cL = c[(pos-1)%n]; cS = c[pos]; cR = c[(pos+1)%n]
                            if (cL, cS, cR, succ[pos]) == (L, S, R, out):
                                sample_dfc = fc(succ, n) - fc(c, n)
                                break
                    print(f"      ({L},{S},{R})->{out} {kind:6s} Δfc={sample_dfc:+d}: {cnt}")

        # KEY TEST: for each interior position j >= 3, how many times does
        # it fire vs how many times does position j-1 fire?
        # If j fires k times and j-1 fires fewer, information is "stuck"
        print(f"\n  Fire count ratio (pos j vs j-1) for interior:")
        for j in range(3, n - 2):
            f_j = fire_count.get(j, 0)
            f_jm1 = fire_count.get(j - 1, 0)
            print(f"    pos {j}: {f_j}, pos {j-1}: {f_jm1}, ratio: "
                  f"{f_j/f_jm1:.2f}" if f_jm1 > 0 else f"    pos {j}: {f_j}, pos {j-1}: 0")

        # How many edges fire at BOUNDARY positions (0, 1, n-2, n-1)?
        bnd_edges = sum(1 for _, _, p in tp_edges if p in {0, 1, n - 2, n - 1})
        int_edges = len(tp_edges) - bnd_edges
        print(f"\n  Boundary edges: {bnd_edges}, Interior edges: {int_edges}")

        # What fraction of TP edges are copy_L vs copy_R at interior positions?
        cl_count = 0
        cr_count = 0
        for c, succ, pos in tp_edges:
            if 2 <= pos <= n - 3:
                L = c[(pos - 1) % n]; out = succ[pos]; R = c[(pos + 1) % n]
                if out == L:
                    cl_count += 1
                elif out == R:
                    cr_count += 1
        print(f"  Interior: {cl_count} copy_L, {cr_count} copy_R")

        print(f"  Time: {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
