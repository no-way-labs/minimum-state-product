"""
RA12 v3: The bad cycle anatomy.

KEY FINDING from v2:
- Sub-threshold systems with Sol1 have bad cycles in the NONDETERMINISTIC graph
- All bad cycle configs are MULTI-PRIVILEGED
- All have ESCAPES (can reach good cycle via some move)
- The bad cycles have exactly 14 configs (!!) across ms=(2,2,2,3,3), (2,2,2,2,3), (2,2,2,2,2)

Questions:
1. What do these 14 bad-cycle configs look like?
2. Why exactly 14 in all three cases?
3. For the M_5=96 VALID witness: are there really NO bad cycles? What changed?
4. Is 14 a universal constant, or does it depend on something?
5. Can we prove bad cycles MUST exist for any transition function at sub-threshold?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
from collections import defaultdict, deque, Counter
from verifier import all_configs, privileged_set, apply_move


def build_sol1_style(ms):
    n = len(ms)
    fs = []
    for i in range(n):
        m = ms[i]
        if i == 0:
            def f(L, S, R, m=m):
                if L == S: return (S + 1) % m
                return S
        else:
            def f(L, S, R, m=m):
                if L != S: return L % m
                return S
        fs.append(f)
    return fs


def build_m5_96_witness():
    ms = [2, 2, 2, 3, 4]
    tables = [
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,
         (1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0,
         (3,0,0):0,(3,0,1):0,(3,1,0):0,(3,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):1,(0,1,1):0,(0,1,2):1,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,0,3):0,
         (0,1,0):1,(0,1,1):2,(0,1,2):1,(0,1,3):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):2,(0,2,3):2,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,
         (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,1,3):1,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):2,(0,1,1):1,(0,2,0):2,(0,2,1):2,(0,3,0):0,(0,3,1):1,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):0,(1,3,0):3,(1,3,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):3,(2,2,1):0,(2,3,0):3,(2,3,1):0},
    ]
    fs = []
    for table in tables:
        def make_f(t):
            def f(L, S, R): return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    return ms, fs


def find_bad_cycles_detailed(ms, fs, label=""):
    """Find and fully characterize bad cycles."""
    n = len(ms)
    P = 1
    for m in ms:
        P *= m

    configs = list(all_configs(ms))
    priv_map = {c: privileged_set(c, fs, ms) for c in configs}

    # Find good cycle
    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    succ = {}
    for c in single_priv:
        s = apply_move(c, priv_map[c][0], fs, ms)
        succ[c] = (s, priv_map[c][0])

    good_candidates = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = {c for c in good_candidates if succ.get(c, (None,))[0] not in good_candidates}
        if to_remove:
            good_candidates -= to_remove
            changed = True

    visited = set()
    cycles = []
    for c in good_candidates:
        if c in visited:
            continue
        path, path_set = [], set()
        node = c
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            cycles.append(path[path.index(node):])
        visited.update(path)

    if not cycles:
        print(f"\n{label}: No good cycle")
        return

    cycle = max(cycles, key=len)
    cycle_set = set(cycle)
    CL = len(cycle)

    print(f"\n{'='*70}")
    print(f"{label}: ms={list(ms)}, P={P}")
    print(f"{'='*70}")
    print(f"Good cycle length: {CL}")
    print(f"Good cycle configs:")
    mover_seq = [succ[c][1] for c in cycle]
    for t, c in enumerate(cycle):
        print(f"  {t:2d}: {c}  mover={mover_seq[t]}")

    # Find ALL bad cycles in nondeterministic graph
    bad = set(configs) - cycle_set
    bad_succs = defaultdict(set)
    for c in bad:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            if s in bad:
                bad_succs[c].add(s)

    # Find SCCs
    # Simple: find all configs that are in some cycle
    # A config is in a cycle iff it can reach itself
    in_cycle = set()
    for c in bad:
        if not bad_succs[c]:
            continue
        # BFS from c, see if we can return
        reachable = set()
        queue = deque(bad_succs[c])
        for s in bad_succs[c]:
            reachable.add(s)
        while queue:
            node = queue.popleft()
            if node == c:
                in_cycle.add(c)
                break
            for s in bad_succs[node]:
                if s not in reachable:
                    reachable.add(s)
                    queue.append(s)

    print(f"\nBad configs in cycles: {len(in_cycle)}")
    if in_cycle:
        print(f"\nBAD CYCLE CONFIGS:")
        for c in sorted(in_cycle):
            priv = priv_map[c]
            succs_in_bad = bad_succs[c]
            succs_to_good = []
            for p in priv:
                s = apply_move(c, p, fs, ms)
                if s in cycle_set:
                    succs_to_good.append((p, s))
                elif s not in bad:
                    succs_to_good.append((p, s, "single-priv-tail"))

            print(f"  {c}  priv={priv}  bad_succs={len(succs_in_bad)}  escapes={len(succs_to_good)}")

        # Find actual cycles (not just configs in cycles)
        # Follow paths from bad cycle configs
        print(f"\nActual bad cycle paths:")
        found_cycles = []
        for start in sorted(in_cycle):
            # Try each privileged move
            for p_start in priv_map[start]:
                s = apply_move(start, p_start, fs, ms)
                if s not in bad:
                    continue
                # Follow deterministically (picking first priv) to find a cycle
                path = [start]
                node = s
                seen = {start}
                while node not in seen:
                    seen.add(node)
                    path.append(node)
                    # Pick a move that stays in bad
                    moved = False
                    for pp in priv_map[node]:
                        ss = apply_move(node, pp, fs, ms)
                        if ss in in_cycle:
                            node = ss
                            moved = True
                            break
                    if not moved:
                        break
                if node in seen:
                    idx = path.index(node)
                    cyc = path[idx:]
                    cyc_frozen = frozenset(cyc)
                    if cyc_frozen not in [frozenset(fc) for fc in found_cycles]:
                        found_cycles.append(cyc)
                        if len(found_cycles) <= 10:
                            print(f"  Cycle of length {len(cyc)}:")
                            for cc in cyc:
                                print(f"    {cc}")

        print(f"  Total distinct bad cycles found: {len(found_cycles)}")

    # ─── Structural analysis of bad cycle configs ───
    if in_cycle:
        print(f"\n--- Structural Analysis of Bad Cycle Configs ---")

        # What's special about these configs?
        # Compare to good cycle configs
        # Look at local patterns: for each position, what contexts appear?

        # Privilege pattern
        priv_patterns = Counter(tuple(sorted(priv_map[c])) for c in in_cycle)
        print(f"Privilege patterns in bad cycles: {dict(priv_patterns)}")

        priv_patterns_good = Counter(tuple(sorted(priv_map[c])) for c in cycle)
        print(f"Privilege patterns in good cycle: {dict(priv_patterns_good)}")

        # Value distribution at each position
        for i in range(n):
            bad_vals = Counter(c[i] for c in in_cycle)
            good_vals = Counter(c[i] for c in cycle_set)
            print(f"  Pos {i} (m={ms[i]}): bad={dict(bad_vals)}, good={dict(good_vals)}")

    return in_cycle


def main():
    print("=" * 70)
    print("BAD CYCLE ANATOMY")
    print("=" * 70)

    # 1. Sub-threshold cases
    for ms_test in [(2,2,2,2,2), (2,2,2,2,3), (2,2,2,3,3)]:
        fs = build_sol1_style(list(ms_test))
        find_bad_cycles_detailed(list(ms_test), fs, f"Sol1 sub-threshold")

    # 2. At-threshold valid system
    ms96, fs96 = build_m5_96_witness()
    find_bad_cycles_detailed(ms96, fs96, "M_5=96 VALID")

    # 3. Sol1 K=3 (valid, at threshold 3^5=243)
    from verifier import verify_system
    ms_s1 = [3]*5
    def f_dist(L, S, R):
        if L == S: return (S+1)%3
        return S
    def f_other(L, S, R):
        if L != S: return L
        return S
    fs_s1 = [f_dist] + [f_other]*4
    find_bad_cycles_detailed(ms_s1, fs_s1, "Sol1 K=3 n=5")

    # 4. Try DIFFERENT privilege rules on sub-threshold to see if bad cycles persist
    print("\n\n" + "=" * 70)
    print("TESTING ALTERNATIVE PRIVILEGE RULES ON SUB-THRESHOLD")
    print("=" * 70)

    ms_sub = [2, 2, 2, 3, 3]

    # Rule 1: L==S (Sol1 distinguished at P0)
    # Already tested above

    # Rule 2: R==S
    fs2 = []
    for i in range(5):
        m = ms_sub[i]
        def f(L, S, R, m=m):
            if R == S: return (S+1) % m
            return S
        fs2.append(f)
    find_bad_cycles_detailed(ms_sub, fs2, "R==S privilege")

    # Rule 3: L+S+R == 0 mod 3 (for ternary), L==S for binary
    fs3 = []
    for i in range(5):
        m = ms_sub[i]
        mL = ms_sub[(i-1)%5]
        mR = ms_sub[(i+1)%5]
        if m == 2:
            def f(L, S, R, m=m):
                if L == S: return 1 - S
                return S
        else:
            def f(L, S, R, m=m):
                if (L + S + R) % 3 == 0 and S != (S+1)%m:
                    return (S+1) % m
                return S
        fs3.append(f)
    find_bad_cycles_detailed(ms_sub, fs3, "Mixed privilege")

    # Rule 4: Dijkstra Sol3 on (2,2,2,3,3) - bottom/middle/top
    def f_bottom_2(L, S, R):
        if (S + 1) % 2 == R % 2:
            return (S - 1) % 2
        return S
    def f_middle_2(L, S, R):
        if (S + 1) % 2 == L % 2:
            return L % 2
        if (S + 1) % 2 == R % 2:
            return R % 2
        return S
    def f_middle_3(L, S, R):
        if (S + 1) % 3 == L % 3:
            return L % 3
        if (S + 1) % 3 == R % 3:
            return R % 3
        return S
    def f_top_3(L, S, R):
        if L % 3 == R % 3 and (L + 1) % 3 != S % 3:
            return (L + 1) % 3
        return S

    fs4 = [f_bottom_2, f_middle_2, f_middle_2, f_middle_3, f_top_3]
    find_bad_cycles_detailed(ms_sub, fs4, "Sol3-style on (2,2,2,3,3)")

    # 5. EXHAUSTIVE at n=4 (small enough)
    print("\n\n" + "=" * 70)
    print("n=4 EXHAUSTIVE: ALL sub-threshold multisets")
    print("=" * 70)
    threshold_n4 = 4 * 3**(4-2)  # = 36

    from itertools import combinations_with_replacement
    for combo in sorted(combinations_with_replacement([2,3,4,5], 4)):
        P = 1
        for x in combo: P *= x
        bin_count = sum(1 for x in combo if x == 2)
        if P < threshold_n4 and bin_count >= 3:
            ms_test = list(combo)
            fs_test = build_sol1_style(ms_test)
            configs = list(all_configs(ms_test))
            priv_map = {c: privileged_set(c, fs_test, ms_test) for c in configs}

            # Quick check for bad cycles
            single = {c for c in configs if len(priv_map[c]) == 1}
            succ = {}
            for c in single:
                s = apply_move(c, priv_map[c][0], fs_test, ms_test)
                succ[c] = (s, priv_map[c][0])

            good_cand = set(single)
            changed = True
            while changed:
                changed = False
                to_rm = {c for c in good_cand if succ.get(c,(None,))[0] not in good_cand}
                if to_rm:
                    good_cand -= to_rm
                    changed = True

            # Find cycle
            visited = set()
            cycle_set = set()
            for c in good_cand:
                if c in visited: continue
                path, ps = [], set()
                node = c
                while node not in visited and node not in ps:
                    path.append(node); ps.add(node)
                    node = succ[node][0]
                if node in ps:
                    cycle_set.update(path[path.index(node):])
                visited.update(path)

            if not cycle_set:
                print(f"  ms={ms_test} P={P}: no good cycle")
                continue

            bad = set(configs) - cycle_set
            bad_succs = defaultdict(set)
            for c in bad:
                for p in priv_map[c]:
                    s = apply_move(c, p, fs_test, ms_test)
                    if s in bad:
                        bad_succs[c].add(s)

            # Quick cycle check
            in_cycle = set()
            for c in bad:
                if not bad_succs[c]: continue
                reachable = set(bad_succs[c])
                queue = deque(bad_succs[c])
                while queue:
                    node = queue.popleft()
                    if node == c:
                        in_cycle.add(c)
                        break
                    for s in bad_succs[node]:
                        if s not in reachable:
                            reachable.add(s)
                            queue.append(s)

            print(f"  ms={ms_test} P={P}: CL={len(cycle_set)}, bad_in_cycles={len(in_cycle)}, "
                  f"all_multi={'yes' if all(len(priv_map[c])>1 for c in in_cycle) else 'NO'}")


if __name__ == "__main__":
    main()
