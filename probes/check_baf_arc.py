#!/usr/bin/env python3
"""
Check whether the hypotheses of large_arc_zeroWinding_ec are satisfiable,
and if so, whether a BAFArcAdj witness exists.

Uses CUP-2 system (ms = [2,3,...,3,2]).
"""
import sys
sys.path.insert(0, '.')
from itertools import product as iproduct
from claude.cup2_theorem import build_system

def find_good_cycle(n, ms, fs):
    """Find the good cycle for the system."""
    all_configs = list(iproduct(*(range(m) for m in ms)))

    # Find privileged processors for each config
    def get_privileged(c):
        privs = []
        for p in range(n):
            lp = (p + n - 1) % n
            rp = (p + 1) % n
            if fs[p](c[lp], c[p], c[rp]) != c[p]:
                privs.append(p)
        return privs

    # Find good configs (exactly one privileged)
    good_configs = []
    for c in all_configs:
        privs = get_privileged(c)
        if len(privs) == 1:
            good_configs.append(c)

    # Find good cycles: follow the unique move from each good config
    good_set = set(good_configs)
    visited = set()
    cycles = []

    for start in good_configs:
        if start in visited:
            continue
        path = [start]
        visited.add(start)
        c = start
        while True:
            privs = get_privileged(c)
            assert len(privs) == 1
            p = privs[0]
            c_next = list(c)
            c_next[p] = fs[p](c[(p-1)%n], c[p], c[(p+1)%n])
            c_next = tuple(c_next)
            if c_next == start:
                cycles.append(path)
                break
            if c_next in visited or c_next not in good_set:
                break
            path.append(c_next)
            visited.add(c_next)
            c = c_next

    return cycles

def analyze_good_cycle(n, ms, fs, gc_configs):
    """Analyze a good cycle for BAFArcAdj witnesses."""
    L = len(gc_configs)

    # Extract mover word
    movers = []
    for k in range(L):
        c = gc_configs[k]
        c_next = gc_configs[(k + 1) % L]
        mover = None
        for p in range(n):
            if c[p] != c_next[p]:
                mover = p
                break
        if mover is None:
            # stay step - find privileged proc
            for p in range(n):
                lp = (p + n - 1) % n
                rp = (p + 1) % n
                val = fs[p](c[lp], c[p], c[rp])
                if val != c[p]:
                    mover = p
                    break
        movers.append(mover)

    # Compute step directions
    step_dirs = []
    for k in range(L):
        curr = movers[k]
        nxt = movers[(k + 1) % L]
        if nxt == (curr + 1) % n:
            step_dirs.append('cw')
        elif nxt == curr:
            step_dirs.append('stay')
        elif nxt == (curr + n - 1) % n:
            step_dirs.append('ccw')
        else:
            step_dirs.append('???')

    # Check winding
    cw_count = step_dirs.count('cw')
    ccw_count = step_dirs.count('ccw')
    total_disp = cw_count - ccw_count
    is_zero_winding = (total_disp == 0)

    # Check safe processors
    safe_procs = []
    for q in range(n):
        lq = (q + n - 1) % n
        rq = (q + 1) % n
        is_safe = all(movers[k] != q and movers[k] != lq and movers[k] != rq for k in range(L))
        if is_safe:
            safe_procs.append(q)
    has_safe = len(safe_procs) > 0

    # Find BAFArcAdj witnesses (only if hypotheses match)
    found_arcs = []
    for p in range(n):
        rp = (p + 1) % n
        lp = (p + n - 1) % n

        # Find CW crossings of edge (p, rp)
        cw_steps = [k for k in range(L) if movers[k] == p and step_dirs[k] == 'cw']
        # Find CCW crossings
        ccw_steps = [k for k in range(L) if movers[k] == rp and step_dirs[k] == 'ccw']

        if not cw_steps or not ccw_steps:
            continue

        # Find minimum-gap CW-then-CCW pair with no crossings between
        for a in cw_steps:
            for b in ccw_steps:
                if b <= a:
                    continue
                # Check no crossing between
                no_cross = True
                for k in range(a+1, b):
                    if (movers[k] == p and step_dirs[k] == 'cw') or \
                       (movers[k] == rp and step_dirs[k] == 'ccw'):
                        no_cross = False
                        break
                if not no_cross:
                    continue

                gap = b - a

                # Check BAFArcAdj conditions for gap >= 2
                if gap < 2 or b + 1 >= L:
                    continue

                # Check mover identities
                if movers[(a+1) % L] != rp:
                    continue
                if movers[(b+1) % L] != p:
                    continue

                # Adjacency: ccwProcStep = ccwNeighborStep + 1
                # ccwNeighborStep = b, ccwProcStep = b+1
                # b+1 = b + 1 -> automatic

                # Check proc doesn't fire in [a+1, b+1)
                proc_ok = all(movers[k] != p for k in range(a+1, b+1))
                # Check left(proc) doesn't fire in [a+1, b+1)
                left_ok = all(movers[k] != lp for k in range(a+1, b+1))
                # Check right(proc) doesn't fire in (a+1, b)
                right_ok = all(movers[k] != rp for k in range(a+2, b))

                if proc_ok and left_ok and right_ok:
                    is_binary_right = (ms[rp] == 2)
                    found_arcs.append({
                        'proc': p,
                        'cw_proc': a,
                        'cw_neighbor': a+1,
                        'ccw_neighbor': b,
                        'ccw_proc': b+1,
                        'gap': gap,
                        'binary_right': is_binary_right
                    })

    return {
        'movers': movers,
        'step_dirs': step_dirs,
        'cw_count': cw_count,
        'ccw_count': ccw_count,
        'is_zero_winding': is_zero_winding,
        'safe_procs': safe_procs,
        'has_safe': has_safe,
        'arcs': found_arcs
    }

def main():
    for n in [5, 6, 7, 8, 9, 10]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        ms, fs = build_system(n)
        prod = 1
        for m in ms:
            prod *= m
        print(f"  ms={ms}, product={prod}")

        cycles = find_good_cycle(n, ms, fs)
        print(f"  Found {len(cycles)} good cycles")

        for ci, gc in enumerate(cycles):
            print(f"\n  Cycle {ci}: length={len(gc)}")
            result = analyze_good_cycle(n, ms, fs, gc)
            print(f"    CW={result['cw_count']}, CCW={result['ccw_count']}, disp={result['cw_count']-result['ccw_count']}")
            print(f"    Zero winding: {result['is_zero_winding']}")
            print(f"    Safe procs: {result['safe_procs']}")
            print(f"    Movers: {result['movers'][:30]}{'...' if len(result['movers'])>30 else ''}")

            hyps_ok = result['is_zero_winding'] and result['cw_count'] > 0 and not result['has_safe']

            if hyps_ok:
                print(f"    *** ALL HYPOTHESES SATISFIED ***")
                print(f"    BAFArcAdj witnesses: {len(result['arcs'])}")
                for arc in result['arcs'][:10]:
                    print(f"      proc={arc['proc']}, gap={arc['gap']}, binary_right={arc['binary_right']}")
                    if arc['binary_right']:
                        print(f"        -> GIVES CONTRADICTION via elim_of_binary_right")

main()
