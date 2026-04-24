"""
RA12 v5: Final summary analysis.

Key structural findings from v1-v4:

1. DRAINAGE BASIN:
   - For valid systems: full basin = P (all configs drain to good cycle)
   - The single-priv deterministic tree is tiny (5-30% of P)
   - The remaining 70-95% of configs have MULTIPLE privileged procs
   - Convergence works through the NONDETERMINISTIC graph:
     the daemon can't find a bad cycle, so every path eventually reaches good

2. BAD CYCLES:
   - For Sol1 on sub-threshold: bad cycles ALWAYS exist in the nondeterministic graph
   - All bad-cycle configs are MULTI-privileged
   - They all have ESCAPES (some move leads toward good cycle)
   - The daemon CAN cycle by always choosing the "wrong" move
   - Sol1 K=3 (above threshold) ALSO has bad cycles! (15 configs)

3. BINARY FLIP:
   - Flipping a binary proc ALWAYS breaks single-privilege at some step
   - No position is "always far" from all movers (fairness requires all movers)
   - Even at distance 2+, flip changes privilege at LATER steps
   - The parallel sheet / shadow trap idea DOES NOT WORK

4. STRUCTURE:
   - Good cycle: contiguous blocks (wavefront), adj_diffs ≤ 1
   - Bad cycle configs: scattered patterns, adj_diffs ≥ 2
   - All-binary n=5: good cycle = 10 configs, bad cycle = 20 configs,
     remaining 2 = fully alternating (adj_diffs=4)

CONCLUSION: The drainage basin approach does NOT provide a simpler unified argument.
The issue is that convergence is about the NONDETERMINISTIC graph having no bad cycles,
not about the deterministic basin being large. Multi-priv configs are the battleground.

Let's quantify more precisely what changes between valid and invalid systems.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
from collections import defaultdict, deque, Counter
from verifier import all_configs, privileged_set, apply_move, verify_system


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


def build_sol1(n, K):
    ms = [K]*n
    def f_dist(L, S, R):
        if L == S: return (S+1)%K
        return S
    def f_other(L, S, R):
        if L != S: return L
        return S
    return ms, [f_dist] + [f_other]*(n-1)


def nondeterministic_analysis(ms, fs, label=""):
    """Count the nondeterministic structure precisely."""
    n = len(ms)
    P = 1
    for m in ms: P *= m

    configs = list(all_configs(ms))
    priv_map = {c: privileged_set(c, fs, ms) for c in configs}

    # Find good cycle
    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    succ = {}
    for c in single_priv:
        s = apply_move(c, priv_map[c][0], fs, ms)
        succ[c] = (s, priv_map[c][0])

    good_cand = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_rm = {c for c in good_cand if succ.get(c,(None,))[0] not in good_cand}
        if to_rm:
            good_cand -= to_rm
            changed = True

    visited = set()
    cycle_configs = []
    for c in good_cand:
        if c in visited: continue
        path, ps = [], set()
        node = c
        while node not in visited and node not in ps:
            path.append(node); ps.add(node)
            node = succ[node][0]
        if node in ps:
            cycle_configs = path[path.index(node):]
        visited.update(path)

    cycle_set = set(cycle_configs)
    CL = len(cycle_set)

    if CL == 0:
        print(f"{label}: ms={list(ms)}, P={P} — no good cycle")
        return

    # Nondeterministic graph on bad configs
    bad = set(configs) - cycle_set
    # Total edges in bad subgraph
    bad_edges = 0
    escape_edges = 0
    for c in bad:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            if s in bad:
                bad_edges += 1
            else:
                escape_edges += 1

    # Configs with ALL successors in bad (no escape)
    fully_trapped = 0
    for c in bad:
        all_in_bad = all(apply_move(c, p, fs, ms) in bad for p in priv_map[c])
        if all_in_bad:
            fully_trapped += 1

    # Bad SCCs
    bad_succs = defaultdict(set)
    for c in bad:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            if s in bad:
                bad_succs[c].add(s)

    in_cycle = set()
    for c in bad:
        if not bad_succs[c]: continue
        reachable = set(bad_succs[c])
        queue = deque(bad_succs[c])
        found = False
        while queue:
            node = queue.popleft()
            if node == c:
                in_cycle.add(c)
                found = True
                break
            for s in bad_succs[node]:
                if s not in reachable:
                    reachable.add(s)
                    queue.append(s)

    print(f"\n{label}: ms={list(ms)}, P={P}, CL={CL}")
    print(f"  Bad configs: {len(bad)}")
    print(f"  Bad edges: {bad_edges}, escape edges: {escape_edges}")
    print(f"  Fully trapped (ALL succs in bad): {fully_trapped}")
    print(f"  In bad cycles: {len(in_cycle)}")
    print(f"  Escape ratio: {escape_edges/(bad_edges+escape_edges):.3f}" if bad_edges+escape_edges > 0 else "  No edges")

    # For valid systems, fully_trapped should be 0 and in_cycle should be 0
    return {
        'P': P, 'CL': CL, 'bad': len(bad), 'bad_edges': bad_edges,
        'escape_edges': escape_edges, 'trapped': fully_trapped,
        'in_cycle': len(in_cycle)
    }


def main():
    print("=" * 70)
    print("RA12 v5: FINAL SUMMARY")
    print("=" * 70)

    # Valid systems
    print("\n### VALID SYSTEMS ###")
    ms96, fs96 = build_m5_96_witness()
    nondeterministic_analysis(ms96, fs96, "M_5=96 VALID")

    ms_s1, fs_s1 = build_sol1(5, 4)
    nondeterministic_analysis(ms_s1, fs_s1, "Sol1 n=5 K=4")

    ms_s3, fs_s3 = build_sol1(5, 3)
    r = nondeterministic_analysis(ms_s3, fs_s3, "Sol1 n=5 K=3")

    ms_s7, fs_s7 = build_sol1(7, 3)
    nondeterministic_analysis(ms_s7, fs_s7, "Sol1 n=7 K=3")

    # Sub-threshold with Sol1
    print("\n### SOL1 ON SUB-THRESHOLD ###")
    for ms_test in [[2]*5, [2,2,2,2,3], [2,2,2,3,3], [2,2,2,3,4]]:
        fs_test = []
        n = len(ms_test)
        K_max = max(ms_test)
        for i in range(n):
            m = ms_test[i]
            if i == 0:
                def f(L, S, R, m=m):
                    if L == S: return (S+1) % m
                    return S
            else:
                def f(L, S, R, m=m):
                    if L != S: return L % m
                    return S
            fs_test.append(f)
        nondeterministic_analysis(ms_test, fs_test, f"Sol1-style")

    # ─── KEY COMPARISON TABLE ───
    print("\n\n" + "=" * 70)
    print("COMPARISON TABLE")
    print("=" * 70)
    print(f"{'System':<30} {'P':>5} {'CL':>4} {'Bad':>5} {'BadEdge':>7} {'EscEdge':>7} {'Trapped':>7} {'InCycle':>7}")
    print("-" * 92)

    systems = [
        ("M_5=96 VALID", *build_m5_96_witness()),
        ("Sol1 n=5 K=4", *build_sol1(5, 4)),
        ("Sol1 n=5 K=3", *build_sol1(5, 3)),
    ]

    # Add Sol1-style on sub-threshold
    for ms_test in [[2]*5, [2,2,2,2,3], [2,2,2,3,3]]:
        n = len(ms_test)
        fs_test = []
        for i in range(n):
            m = ms_test[i]
            if i == 0:
                def f(L, S, R, m=m):
                    if L == S: return (S+1)%m
                    return S
            else:
                def f(L, S, R, m=m):
                    if L != S: return L % m
                    return S
            fs_test.append(f)
        systems.append((f"Sol1 {ms_test}", ms_test, fs_test))

    for label, ms, fs in systems:
        n = len(ms)
        P = 1
        for m in ms: P *= m
        configs = list(all_configs(ms))
        priv_map = {c: privileged_set(c, fs, ms) for c in configs}

        single_priv = {c for c in configs if len(priv_map[c]) == 1}
        succ = {}
        for c in single_priv:
            s = apply_move(c, priv_map[c][0], fs, ms)
            succ[c] = (s, priv_map[c][0])

        good_cand = set(single_priv)
        changed = True
        while changed:
            changed = False
            to_rm = {c for c in good_cand if succ.get(c,(None,))[0] not in good_cand}
            if to_rm:
                good_cand -= to_rm
                changed = True

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

        CL = len(cycle_set)
        bad = set(configs) - cycle_set

        bad_edges = 0
        escape_edges = 0
        bad_succs = defaultdict(set)
        for c in bad:
            for p in priv_map[c]:
                s = apply_move(c, p, fs, ms)
                if s in bad:
                    bad_edges += 1
                    bad_succs[c].add(s)
                else:
                    escape_edges += 1

        trapped = sum(1 for c in bad if all(apply_move(c, p, fs, ms) in bad for p in priv_map[c]))

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

        print(f"{label:<30} {P:>5} {CL:>4} {len(bad):>5} {bad_edges:>7} {escape_edges:>7} {trapped:>7} {len(in_cycle):>7}")

    # ─── FINAL CONCLUSIONS ───
    print("\n\n" + "=" * 70)
    print("CONCLUSIONS")
    print("=" * 70)
    print("""
1. DRAINAGE BASIN SIZE is NOT the differentiator.
   Both valid and invalid systems have full reachability basin = P.
   The single-priv deterministic tree is always tiny (5-30% of P).

2. BAD CYCLES IN THE NONDETERMINISTIC GRAPH are the differentiator.
   - Valid systems: 0 configs in bad cycles, 0 fully trapped
   - Invalid systems: 14-20+ configs in bad cycles
   - Sol1 K=3 n=5 (VALID, P=243): HAS 15 bad cycle configs!
     But it's valid because the daemon MUST eventually escape.
     Wait — this contradicts convergence. Let me check...

3. The binary flip / parallel sheet approach FAILS because:
   - No position is always far from all movers (fairness)
   - Even distant flips change privilege at later steps
   - Transition functions are value-dependent at binary procs

4. The REAL question is: why does the M_5=96 witness have NO bad cycles
   while Sol1 K=3 HAS bad cycles (yet both are valid)?
   Answer: Sol1 K=3 is valid because the 15 bad cycle configs all have
   ESCAPES — every config in the bad cycle can also reach the good cycle.
   Actually wait, let me re-examine: convergence requires NO bad cycles
   at all (adversarial daemon). If bad cycles exist, the system is INVALID.

5. RE-CHECK Sol1 K=3: the verify_system function says it's valid.
   But we found 15 configs in bad cycles. Something is wrong.
   Let me verify...
""")

    # Double-check Sol1 K=3
    ms_check, fs_check = build_sol1(5, 3)
    result = verify_system(ms_check, fs_check, verbose=False)
    print(f"  Sol1 K=3 n=5 verify_system: valid={result['valid']}")
    if result['valid']:
        print(f"  Cycle length: {result.get('cycle_length', 'N/A')}")

    # The issue: our bad cycle detection might include configs that are
    # in the GOOD set (not just the cycle, but the tails too)
    # Let me check: are those 15 "bad" configs actually in the good set?
    configs_check = list(all_configs(ms_check))
    priv_check = {c: privileged_set(c, fs_check, ms_check) for c in configs_check}

    # Get the actual good set from verify_system
    if result['valid'] and 'good_configs' in result:
        good_set = result['good_configs']
        print(f"  Good configs: {len(good_set)}")

        # Recompute bad cycles excluding ALL good configs
        bad_check = set(configs_check) - good_set
        bad_succs_check = defaultdict(set)
        for c in bad_check:
            for p in priv_check[c]:
                s = apply_move(c, p, fs_check, ms_check)
                if s in bad_check:
                    bad_succs_check[c].add(s)

        in_cycle_check = set()
        for c in bad_check:
            if not bad_succs_check[c]: continue
            reachable = set(bad_succs_check[c])
            queue = deque(bad_succs_check[c])
            while queue:
                node = queue.popleft()
                if node == c:
                    in_cycle_check.add(c)
                    break
                for s in bad_succs_check[node]:
                    if s not in reachable:
                        reachable.add(s)
                        queue.append(s)

        print(f"  Bad configs (outside good set): {len(bad_check)}")
        print(f"  Bad cycles (outside good set): {len(in_cycle_check)}")
    else:
        print(f"  (good_configs not available in result)")

    # Also check: the 15 "bad cycle" configs we found earlier — are they in good_cand?
    # They should be if verify_system says the system is valid
    print(f"\n  Let me trace: are the 15 configs in good_candidates or cycle_set?")
    configs_s1 = list(all_configs(ms_check))
    priv_s1 = {c: privileged_set(c, fs_check, ms_check) for c in configs_s1}
    single_s1 = {c for c in configs_s1 if len(priv_s1[c]) == 1}
    succ_s1 = {}
    for c in single_s1:
        s = apply_move(c, priv_s1[c][0], fs_check, ms_check)
        succ_s1[c] = (s, priv_s1[c][0])

    gc = set(single_s1)
    changed = True
    while changed:
        changed = False
        to_rm = {c for c in gc if succ_s1.get(c,(None,))[0] not in gc}
        if to_rm:
            gc -= to_rm
            changed = True

    visited = set()
    cyc_set = set()
    for c in gc:
        if c in visited: continue
        path, ps = [], set()
        node = c
        while node not in visited and node not in ps:
            path.append(node); ps.add(node)
            node = succ_s1[node][0]
        if node in ps:
            cyc_set.update(path[path.index(node):])
        visited.update(path)

    print(f"  Our cycle_set: {len(cyc_set)}")
    print(f"  Our good_candidates: {len(gc)}")

    # The 15 bad cycle configs from Sol1 K=3
    bad_s1 = set(configs_s1) - cyc_set
    bad_succs_s1 = defaultdict(set)
    for c in bad_s1:
        for p in priv_s1[c]:
            s = apply_move(c, p, fs_check, ms_check)
            if s in bad_s1:
                bad_succs_s1[c].add(s)

    in_cycle_s1 = set()
    for c in bad_s1:
        if not bad_succs_s1[c]: continue
        reachable = set(bad_succs_s1[c])
        queue = deque(bad_succs_s1[c])
        while queue:
            node = queue.popleft()
            if node == c:
                in_cycle_s1.add(c)
                break
            for s in bad_succs_s1[node]:
                if s not in reachable:
                    reachable.add(s)
                    queue.append(s)

    print(f"  Bad cycle configs (our method): {len(in_cycle_s1)}")
    for c in sorted(list(in_cycle_s1)[:5]):
        in_gc = c in gc
        in_cycle = c in cyc_set
        print(f"    {c}  in_good_cand={in_gc}  in_cycle={in_cycle}  priv={priv_s1[c]}")

    # Check verify_system's good set
    if result['valid'] and 'good_configs' in result:
        good_vfy = result['good_configs']
        for c in sorted(list(in_cycle_s1)[:5]):
            in_good_vfy = c in good_vfy
            print(f"    {c}  in_verify_good={in_good_vfy}")


if __name__ == "__main__":
    main()
