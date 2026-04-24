#!/usr/bin/env python3
"""Check: do good configs have forced moves to NG configs?
If so, the VC forced graph has edges LEAVING the good cycle into NG.
Also: does f_VC (smallest-position forced move) diverge from the good cycle?"""

import itertools, random
from collections import defaultdict

def left(i,n): return (i-1)%n
def right(i,n): return (i+1)%n

def find_cycles_simple(ms, max_attempts=100):
    n = len(ms)
    cycles = []
    for _ in range(max_attempts):
        f = {}
        for i in range(n):
            for l in range(ms[left(i,n)]):
                for s in range(ms[i]):
                    for r in range(ms[right(i,n)]):
                        f[(i,l,s,r)] = random.randint(0, ms[i]-1)
        c = tuple(random.randint(0,m-1) for m in ms)
        visited = {}; path = []
        for step in range(500):
            if c in visited:
                cyc = path[visited[c]:]
                if len(cyc) >= 2 and len(set(cyc)) == len(cyc):
                    movers = []
                    ok = True
                    for k in range(len(cyc)):
                        d = [i for i in range(n) if cyc[k][i] != cyc[(k+1)%len(cyc)][i]]
                        if len(d) != 1: ok = False; break
                        movers.append(d[0])
                    if ok and len(set(movers)) == n:
                        cycles.append((cyc, movers, f))
                break
            visited[c] = len(path); path.append(c)
            privs = [i for i in range(n) if f[(i, c[left(i,n)], c[i], c[right(i,n)])] != c[i]]
            if not privs: break
            mover = random.choice(privs)
            new_c = list(c)
            new_c[mover] = f[(mover, c[left(mover,n)], c[mover], c[right(mover,n)])]
            c = tuple(new_c)
        else:
            continue
    seen = set()
    unique = []
    for cyc, movers, f in cycles:
        key = frozenset(cyc)
        if key not in seen:
            seen.add(key)
            unique.append((cyc, movers, f))
    return unique

def build_det(cycle, movers, n):
    det = {}
    for k in range(len(cycle)):
        p = movers[k]
        c_k = cycle[k]; c_next = cycle[(k+1)%len(cycle)]
        key = (p, c_k[left(p,n)], c_k[p], c_k[right(p,n)])
        if key not in det:
            det[key] = c_next[p]
    return det

def forced_output(det, c, p, n):
    key = (p, c[left(p,n)], c[p], c[right(p,n)])
    if key in det:
        v = det[key]
        if v != c[p]: return v
    return None

def apply_move(c, p, v):
    return c[:p] + (v,) + c[p+1:]

random.seed(42)

print("PART 1: GOOD CONFIGS WITH FORCED NG-NEIGHBORS")
print("=" * 60)

for n, ms_list in [(5, [(2,2,2,2,2), (2,2,2,2,3), (2,2,2,3,3)]),
                    (6, [(2,2,2,2,2,2), (2,2,2,2,2,3), (2,2,2,2,3,3)]),
                    (7, [(2,2,2,2,2,2,2), (2,2,2,2,2,2,3)])]:
    for ms in ms_list:
        cycles = find_cycles_simple(ms, max_attempts=200)
        if not cycles: continue
        total_good_to_ng = 0
        total_good_configs = 0
        total_good_with_ng_forced = 0
        nc = min(10, len(cycles))
        for cyc, movers, f in cycles[:nc]:
            cycle_set = set(cyc)
            det = build_det(cyc, movers, n)
            good_to_ng = 0
            good_with_ng = 0
            for k, c_k in enumerate(cyc):
                has_ng = False
                for p in range(n):
                    if p == movers[k]: continue
                    v = forced_output(det, c_k, p, n)
                    if v is not None:
                        target = apply_move(c_k, p, v)
                        if target not in cycle_set:
                            good_to_ng += 1
                            has_ng = True
                if has_ng:
                    good_with_ng += 1
            total_good_to_ng += good_to_ng
            total_good_configs += len(cyc)
            total_good_with_ng_forced += good_with_ng

        print(f"  n={n} ms={ms}: {nc} cycles, "
              f"avg good→NG edges={total_good_to_ng/nc:.1f}, "
              f"avg good w/ NG forced={total_good_with_ng_forced/nc:.1f}/{total_good_configs/nc:.0f}")

print("\nPART 2: f_VC ORBIT ANALYSIS")
print("=" * 60)
print("f_VC = pick forced move at smallest matching position")
print("Question: does f_VC follow the good cycle, or diverge into NG?")
print()

for n, ms in [(5, (2,2,2,2,2)), (5, (2,2,2,2,3)), (5, (2,2,2,3,3)),
              (6, (2,2,2,2,2,2)), (6, (2,2,2,2,2,3)), (6, (2,2,2,2,3,3))]:
    cycles = find_cycles_simple(ms, max_attempts=300)
    if not cycles: continue

    for cyc, movers, f_sys in cycles[:5]:
        cycle_set = set(cyc)
        det = build_det(cyc, movers, n)

        def f_vc(c):
            for p in range(n):
                v = forced_output(det, c, p, n)
                if v is not None:
                    return apply_move(c, p, v), p
            return c, -1

        # Check divergence from good cycle
        diverges = 0
        for k, c_k in enumerate(cyc):
            f_ck, _ = f_vc(c_k)
            c_next = cyc[(k+1) % len(cyc)]
            if f_ck != c_next:
                diverges += 1

        # Full orbit from good[0]
        c = cyc[0]
        orbit = [c]
        orbit_positions = []
        visited_set = {c}
        for _ in range(200):
            c_new, pos = f_vc(c)
            orbit.append(c_new)
            orbit_positions.append(pos)
            if c_new in visited_set:
                # Found the cycle
                cycle_start = orbit.index(c_new)
                orbit_cycle = orbit[cycle_start:-1]
                break
            visited_set.add(c_new)
            c = c_new
        else:
            orbit_cycle = []

        ng_in_orbit = sum(1 for x in orbit if x not in cycle_set)
        good_in_orbit = sum(1 for x in orbit if x in cycle_set)

        if orbit_cycle:
            ng_in_cycle = sum(1 for x in orbit_cycle if x not in cycle_set)
            good_in_cycle = sum(1 for x in orbit_cycle if x in cycle_set)
            print(f"  n={n} ms={ms} L={len(cyc)}: "
                  f"diverges={diverges}/{len(cyc)}, "
                  f"orbit tail={len(orbit)-len(orbit_cycle)-1}, "
                  f"orbit cycle len={len(orbit_cycle)} "
                  f"(good={good_in_cycle}, NG={ng_in_cycle})")
        else:
            print(f"  n={n} ms={ms} L={len(cyc)}: "
                  f"diverges={diverges}/{len(cyc)}, "
                  f"orbit len={len(orbit)} (no cycle found in 200 steps)")

print("\nPART 3: CAN WE ALWAYS FIND AN f_VC CYCLE WITH NG CONFIGS?")
print("=" * 60)

for n, ms in [(5, (2,2,2,2,2)), (5, (2,2,2,2,3)), (6, (2,2,2,2,2,2)), (6, (2,2,2,2,2,3))]:
    cycles = find_cycles_simple(ms, max_attempts=300)
    if not cycles: continue

    always_has_ng_cycle = True
    for cyc, movers, f_sys in cycles[:20]:
        cycle_set = set(cyc)
        det = build_det(cyc, movers, n)
        all_cfgs = list(itertools.product(*[range(m) for m in ms]))

        def f_vc_simple(c):
            for p in range(n):
                v = forced_output(det, c, p, n)
                if v is not None:
                    return apply_move(c, p, v)
            return c

        # Find ALL cycles of f_vc in VC
        visited_global = set()
        ng_cycles_found = 0
        pure_good_cycles = 0
        mixed_cycles = 0

        for start in all_cfgs:
            if start in visited_global: continue
            orbit = []
            c = start
            orbit_set = set()
            while c not in orbit_set and c not in visited_global:
                orbit_set.add(c)
                orbit.append(c)
                c = f_vc_simple(c)

            if c in orbit_set:
                # Found a new cycle
                idx = orbit.index(c)
                cyc_part = orbit[idx:]
                has_ng = any(x not in cycle_set for x in cyc_part)
                has_good = any(x in cycle_set for x in cyc_part)

                if has_ng and not has_good:
                    ng_cycles_found += 1
                elif has_good and not has_ng:
                    pure_good_cycles += 1
                elif has_ng and has_good:
                    mixed_cycles += 1

            visited_global.update(orbit_set)

        if ng_cycles_found == 0 and mixed_cycles == 0:
            always_has_ng_cycle = False
            print(f"  !! n={n} ms={ms} L={len(cyc)}: NO NG cycle under f_vc! "
                  f"pure_good={pure_good_cycles}")
        # else: silently ok

    if always_has_ng_cycle:
        nc = min(20, len(cycles))
        print(f"  n={n} ms={ms}: ALL {nc} cycles have NG orbits under f_vc "
              f"(pure_NG or mixed)")
