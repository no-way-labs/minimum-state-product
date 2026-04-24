#!/usr/bin/env python3
"""Check whether non-zero-winding good cycles can have a safe processor.

A "safe processor" q means: for all steps k, moverAt(k) not in {q, left(q), right(q)}.
Equivalently, q and both neighbors never fire.

KEY ANALYTICAL RESULT:
  If q is safe, then edgeNetFlow at the edge (q, q+1) is 0 (since neither q
  nor q+1 is ever a mover). But edgeNetFlow is constant across ALL edges
  (proved in CycleTypes.lean). So totalDisplacement = n * 0 = 0.

  Contrapositive: non-zero winding => NO safe processor exists.

  Therefore, nonZeroWinding_shadow CANNOT be proved via safe-processor argument.

This script verifies the analytical argument by examining actual good cycles
for small n systems.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system, all_configs, privileged_set, apply_move

def analyze_good_cycles(n, ms, fs):
    """Analyze good cycles for safe processor and winding properties."""
    total = 1
    for m in ms:
        total *= m

    configs = list(all_configs(ms))
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)

    # Find good configs (single privilege, forming a cycle)
    single_priv = {c for c in configs if len(priv_map[c]) == 1}

    # Build successor map for single-priv configs
    succ = {}
    mover_map = {}
    for c in single_priv:
        p = priv_map[c][0]
        s = apply_move(c, p, fs, ms)
        if s in single_priv:
            succ[c] = s
            mover_map[c] = p

    # Find cycles in the successor map
    visited = set()
    cycles = []
    for start in succ:
        if start in visited:
            continue
        path = []
        curr = start
        path_set = set()
        while curr not in visited and curr not in path_set and curr in succ:
            path_set.add(curr)
            path.append(curr)
            curr = succ[curr]
        if curr in path_set:
            # Found a cycle
            idx = next(i for i, c in enumerate(path) if c == curr)
            cycle = path[idx:]
            cycles.append(cycle)
            visited.update(cycle)
        visited.update(path_set)

    return cycles, mover_map

def compute_winding(cycle, mover_map, n):
    """Compute total displacement (winding) and check safe processors."""
    L = len(cycle)
    movers = [mover_map[cycle[k]] for k in range(L)]

    # Compute step directions and total displacement
    total_disp = 0
    cw_count = 0
    ccw_count = 0
    stay_count = 0
    for k in range(L):
        curr = movers[k]
        nxt = movers[(k + 1) % L]
        diff = (nxt - curr) % n
        if diff == 1:  # cw
            total_disp += 1
            cw_count += 1
        elif diff == n - 1:  # ccw
            total_disp -= 1
            ccw_count += 1
        elif diff == 0:  # stay
            stay_count += 1
        else:
            # Non-local step - shouldn't happen in a valid good cycle
            pass

    # Check safe processors
    mover_set = set(movers)
    safe_procs = []
    for q in range(n):
        q_left = (q + n - 1) % n
        q_right = (q + 1) % n
        if q not in mover_set and q_left not in mover_set and q_right not in mover_set:
            safe_procs.append(q)

    return total_disp, cw_count, ccw_count, stay_count, safe_procs, mover_set

def check_edge_net_flow_argument(n):
    """Verify the analytical argument: if safe proc exists, winding = 0.

    edgeNetFlow(p) = cwMoveCountAt(p) - ccwMoveCountAt(right(p))
    If neither p nor right(p) is ever a mover:
      cwMoveCountAt(p) = 0 (no step with moverAt=p and dir=cw)
      ccwMoveCountAt(right(p)) = 0 (no step with moverAt=right(p) and dir=ccw)
    So edgeNetFlow(p) = 0.
    Since edgeNetFlow is constant, totalDisplacement = n * 0 = 0.
    """
    print(f"\n{'='*70}")
    print(f"ANALYTICAL ARGUMENT: safe processor => zero winding")
    print(f"{'='*70}")
    print()
    print("If q is a safe processor, then {q-1, q, q+1} ∩ moverSet = ∅.")
    print("Consider edge (q, q+1): neither q nor q+1 is ever a mover.")
    print("  cwMoveCountAt(q) = 0  (q never fires)")
    print("  ccwMoveCountAt(q+1) = 0  (q+1 never fires)")
    print("  => edgeNetFlow(q) = 0")
    print()
    print("By edgeNetFlow_constant (proved in CycleTypes.lean):")
    print("  edgeNetFlow is the same at all edges.")
    print("  totalDisplacement = n * edgeNetFlow = n * 0 = 0.")
    print()
    print("Contrapositive: non-zero winding => no safe processor.")
    print()
    print("CONCLUSION: nonZeroWinding_shadow CANNOT be proved via safe-processor.")
    print("The nonZeroWinding case genuinely needs a separate axiom (shadow/EC).")

def main():
    # Import CUP-2 tables for building systems
    from cup2_theorem import build_system

    print("=" * 70)
    print("SAFE PROCESSOR ANALYSIS FOR GOOD CYCLES")
    print("=" * 70)

    for n in range(5, 10):
        ms, fs = build_system(n)
        product = 1
        for m in ms:
            product *= m
        threshold = 4 * 3 ** (n - 2)

        print(f"\n--- n={n}, ms={ms}, product={product}, threshold={threshold} ---")
        print(f"  System is {'sub' if product < threshold else 'at/above'}-threshold")

        result = verify_system(ms, fs, verbose=False)
        if not result['valid']:
            print(f"  System not valid! Skipping.")
            continue

        cycles, mover_map = analyze_good_cycles(n, ms, fs)

        for ci, cycle in enumerate(cycles):
            disp, cw, ccw, stay, safe, mset = compute_winding(cycle, mover_map, n)
            zero_winding = (disp == 0)
            has_safe = len(safe) > 0

            print(f"  Cycle {ci}: len={len(cycle)}, displacement={disp}, "
                  f"cw={cw}, ccw={ccw}, stay={stay}")
            print(f"    Mover positions: {sorted(mset)} ({len(mset)}/{n} procs)")
            print(f"    Zero winding: {zero_winding}")
            print(f"    Safe processors: {safe if safe else 'NONE'}")

            if not zero_winding and has_safe:
                print(f"    *** COUNTEREXAMPLE: non-zero winding WITH safe processor! ***")
            elif zero_winding and not has_safe:
                print(f"    Note: zero winding but no safe processor (large arc)")
            elif not zero_winding:
                print(f"    Consistent: non-zero winding => no safe proc (as expected)")

    check_edge_net_flow_argument(9)

    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")
    print()
    print("The analytical argument proves:")
    print("  safe processor exists => edgeNetFlow = 0 at some edge")
    print("  => edgeNetFlow = 0 everywhere (constant)")
    print("  => totalDisplacement = 0 (zero winding)")
    print()
    print("Therefore nonZeroWinding_shadow genuinely needs the shadow/EC axiom.")
    print("It cannot be eliminated via small_arc_contradicts_convergence.")
    print()
    print("The split should be:")
    print("  1. large_arc_zeroWinding_ec (axiom) - zero winding, no safe proc")
    print("  2. nonZeroWinding_shadow (axiom) - non-zero winding")
    print()
    print("subThreshold_obstruction becomes a THEOREM via:")
    print("  zero winding + cwCount=0 => all_stay (proved)")
    print("  zero winding + cwCount>0 + safe proc => small_arc (proved)")
    print("  zero winding + cwCount>0 + no safe proc => large_arc_zeroWinding_ec (axiom)")
    print("  non-zero winding => nonZeroWinding_shadow (axiom)")

if __name__ == '__main__':
    main()
