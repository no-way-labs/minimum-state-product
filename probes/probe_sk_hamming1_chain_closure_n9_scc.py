#!/usr/bin/env python3
"""Deeper n=9 diagnostic: does c_star lie in a closed-forced-set T ⊆ VC_NG?

The lex-first chain hits a dead-end — but c_star has ≥1 NG forced
successor, so c_star might still be in SK if we follow the RIGHT branch.

For each cycle, compute:
  (a) Forward reachable NG configs from c_star (T(c*)).
  (b) Peel T(c*) the same way peel(N_1) is peeled: remove configs with
      NO NG-forced successor inside T. Iterate.
  (c) If the resulting peeled set is nonempty, c_star is in SK (if c_star
      itself survives the peel). If empty, c_star is NOT in SK.
"""
import importlib.util, os, sys
from collections import Counter, deque
sys.setrecursionlimit(100000)

_HERE = os.path.dirname(os.path.abspath(__file__))
_A = os.path.join(_HERE, "probe_sk_hamming1_empty_discriminator_2026-04-17.py")
_C = os.path.join(_HERE, "probe_sk_hamming1_chain_closure_2026-04-17.py")
spa = importlib.util.spec_from_file_location("probe_a", _A)
pa = importlib.util.module_from_spec(spa); spa.loader.exec_module(pa)
spc = importlib.util.spec_from_file_location("probe_c", _C)
pc = importlib.util.module_from_spec(spc); spc.loader.exec_module(pc)


def peel_global(ms, n, cycle, det):
    """SK-style peel on the entire VC_NG: compute configs that eventually
    have a forced neighbor in SK.

    Instead of enumerating VC_NG (exponential), we approximate by
    forward closure from c_star then peel.
    """
    cycle_set = set(cycle)
    c_star = None
    N1, adj, peel_set, provenance, V, me, cs = pa.build_N1_and_peel(
        ms, n, cycle, det)
    if not peel_set:
        return None
    c_star = sorted(peel_set)[0]

    # Forward closure (NG) from c_star via forced moves
    T = {c_star}
    frontier = deque([c_star])
    while frontier:
        c = frontier.popleft()
        for (kind, p, nc) in pc.forced_successors(c, det, n, cycle_set):
            if kind == 'ng' and nc not in T:
                T.add(nc)
                frontier.append(nc)
                if len(T) > 500000:
                    return {'T_size': len(T), 'truncated': True}

    # Also include any NG configs reachable in reverse that are needed?
    # No — SK requires forward closure of forced edges (forced neighbor in SK).
    # The peel on T: iteratively remove configs with no forced NG neighbor in current set.
    cur = set(T)
    rounds = 0
    while True:
        rounds += 1
        to_remove = set()
        for c in cur:
            has_in = False
            for (kind, p, nc) in pc.forced_successors(c, det, n, cycle_set):
                if kind == 'ng' and nc in cur:
                    has_in = True; break
            if not has_in:
                to_remove.add(c)
        if not to_remove:
            break
        cur -= to_remove
    # Now cur = SK ∩ (forward closure of c_star)
    # If c_star ∈ cur, c_star ∈ SK.
    return {
        'T_size': len(T),
        'SK_local_size': len(cur),
        'c_star_in_SK': c_star in cur,
        'peel_rounds': rounds,
        'c_star': c_star,
    }


def main():
    ms = (2,2,2,2,3,3,3,3,3)
    n = 9
    cycles = pa.enumerate_cycles_multistart(ms, n, L_min=2*n+2, L_max=22,
                                              time_budget=60.0, max_cycles=4)
    print(f"n=9  ms={ms}  cycles found: {len(cycles)}")
    for idx, (cycle, movers, det) in enumerate(cycles):
        print(f"\n  cycle {idx}: L={len(movers)}")
        res = peel_global(ms, n, cycle, det)
        if res is None:
            print("    no peel (probe A says empty)")
            continue
        print(f"    T_size = {res['T_size']}")
        print(f"    SK_local (peeled) size = {res['SK_local_size']}")
        print(f"    c_star in SK?         = {res['c_star_in_SK']}")
        print(f"    peel_rounds           = {res['peel_rounds']}")
        print(f"    c_star                = {res['c_star']}")

    # Also rerun on n=8 to sanity check (should all be c_star in SK)
    print("\n\n== Sanity at n=8 ==")
    ms8 = (2,2,2,3,3,3,3,3)
    n = 8
    cycles = pa.enumerate_cycles_multistart(ms8, n, L_min=2*n+2, L_max=19,
                                              time_budget=45.0, max_cycles=5)
    print(f"n=8  ms={ms8}  cycles found: {len(cycles)}")
    for idx, (cycle, movers, det) in enumerate(cycles):
        res = peel_global(ms8, n, cycle, det)
        if res is None:
            print(f"  cycle {idx}: no peel"); continue
        print(f"  cycle {idx}: T={res['T_size']} SK_loc={res['SK_local_size']} "
              f"c*∈SK={res['c_star_in_SK']}")


if __name__ == "__main__":
    main()
