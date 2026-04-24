"""
RA12: Drainage Basin Analysis for Self-Stabilizing Token Rings

Key question: Can we bound the drainage basin capacity and show it's too small
for sub-threshold systems? If so, some configs must form "puddles" (bad cycles).

Uses REAL verified systems (M_5=96 witness, Dijkstra Sol1/Sol3, CUP-2).
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
import itertools
from collections import defaultdict, deque
from verifier import verify_system, all_configs, privileged_set, apply_move


# ─── Known system builders ───

def build_m5_96_witness():
    """M_5=96 witness: ms=[2,2,2,3,4], valid system."""
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
            def f(L, S, R):
                return t[(L, S, R)]
            return f
        fs.append(make_f(table))
    return ms, fs

def build_dijkstra_sol1(n, K):
    """Dijkstra's Solution 1: n procs, all K states."""
    ms = [K] * n
    def f_distinguished(L, S, R):
        if L == S:
            return (S + 1) % K
        return S
    def f_other(L, S, R):
        if L != S:
            return L
        return S
    fs = [f_distinguished] + [f_other] * (n - 1)
    return ms, fs

def build_dijkstra_sol3(n):
    """Dijkstra's Solution 3: n procs, all 3 states."""
    ms = [3] * n
    def f_bottom(L, S, R):
        if (S + 1) % 3 == R:
            return (S - 1) % 3
        return S
    def f_top(L, S, R):
        if L == R and (L + 1) % 3 != S:
            return (L + 1) % 3
        return S
    def f_middle(L, S, R):
        if (S + 1) % 3 == L:
            return L
        if (S + 1) % 3 == R:
            return R
        return S
    fs = [f_bottom] + [f_middle] * (n - 2) + [f_top]
    return ms, fs


# ─── Functional graph analysis ───

def full_analysis(ms, fs, label=""):
    """Complete functional graph + drainage basin + binary flip analysis."""
    n = len(ms)
    P = 1
    for m in ms:
        P *= m

    configs = list(all_configs(ms))
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)

    # Build successor for single-priv configs
    succ = {}
    for c in configs:
        if len(priv_map[c]) == 1:
            s = apply_move(c, priv_map[c][0], fs, ms)
            succ[c] = (s, priv_map[c][0])

    single_priv = {c for c in configs if len(priv_map[c]) == 1}

    # Find closed set
    good_candidates = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in good_candidates:
            s, _ = succ[c]
            if s not in good_candidates:
                to_remove.add(c)
        if to_remove:
            good_candidates -= to_remove
            changed = True

    # Find cycles
    visited = set()
    cycles = []
    for c in good_candidates:
        if c in visited:
            continue
        path = []
        node = c
        path_set = set()
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            cycle_start = path.index(node)
            cycle = path[cycle_start:]
            cycles.append(cycle)
        visited.update(path)

    # Pick the fair cycle if any
    fair_cycle = None
    for cycle in cycles:
        movers = set()
        for c in cycle:
            _, p = succ[c]
            movers.add(p)
        if movers == set(range(n)):
            fair_cycle = cycle
            break

    if not fair_cycle and cycles:
        fair_cycle = max(cycles, key=len)  # use longest

    print(f"\n{'='*70}")
    print(f"SYSTEM: ms={list(ms)}, P={P}, n={n}  {label}")
    print(f"{'='*70}")
    print(f"  Single-priv: {len(single_priv)}, Multi-priv: {sum(1 for c in configs if len(priv_map[c]) > 1)}, Dead: {sum(1 for c in configs if len(priv_map[c]) == 0)}")
    print(f"  Cycles found: {len(cycles)}")

    if not fair_cycle:
        print("  No cycle found!")
        return None

    cycle = fair_cycle
    cycle_set = set(cycle)
    CL = len(cycle)
    mover_seq = [succ[c][1] for c in cycle]
    movers_used = set(mover_seq)
    fair = movers_used == set(range(n))

    print(f"  Cycle length: {CL}, fair: {fair}")
    print(f"  Mover sequence: {mover_seq}")

    # ─── Basin analysis ───
    rev = defaultdict(list)
    for c in single_priv:
        s, _ = succ[c]
        rev[s].append(c)

    basin = set(cycle_set)
    queue = deque(cycle_set)
    while queue:
        node = queue.popleft()
        for pred in rev[node]:
            if pred not in basin:
                basin.add(pred)
                queue.append(pred)

    # In-degree stats
    cycle_indeg = [len(rev[c]) for c in cycle]
    max_indeg = max(len(rev[c]) for c in configs if c in single_priv) if single_priv else 0

    print(f"\n  --- Drainage Basin ---")
    print(f"  Basin size (single-priv tree): {len(basin)} / {P} = {len(basin)/P:.4f}")
    print(f"  Cycle in-degrees: min={min(cycle_indeg)}, max={max(cycle_indeg)}, sum={sum(cycle_indeg)}, avg={sum(cycle_indeg)/CL:.1f}")
    print(f"  Max in-degree anywhere: {max_indeg}")

    # Compute FULL basin including multi-priv configs that can reach basin
    # BFS: from basin, find all configs that can reach it (via any privileged move)
    full_basin = set(basin)
    queue = deque(basin)
    # Reverse map for ALL configs (not just single-priv)
    rev_all = defaultdict(list)
    for c in configs:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            rev_all[s].append(c)

    while queue:
        node = queue.popleft()
        for pred in rev_all[node]:
            if pred not in full_basin:
                full_basin.add(pred)
                queue.append(pred)

    print(f"  Full basin (multi-priv included): {len(full_basin)} / {P} = {len(full_basin)/P:.4f}")
    non_basin = set(configs) - full_basin
    print(f"  Configs outside basin: {len(non_basin)}")

    # ─── Bad cycle detection ───
    # SCC in the bad region
    bad_succs = defaultdict(set)
    for c in non_basin:
        for p in priv_map[c]:
            s = apply_move(c, p, fs, ms)
            if s in non_basin:
                bad_succs[c].add(s)

    # Iterative Tarjan
    sccs = tarjan_scc(non_basin, bad_succs)
    nontrivial_sccs = [scc for scc in sccs if len(scc) > 1 or (len(scc) == 1 and list(scc)[0] in bad_succs.get(list(scc)[0], set()))]

    print(f"  Bad SCCs (puddles): {len(nontrivial_sccs)}")
    total_in_puddles = sum(len(s) for s in nontrivial_sccs)
    print(f"  Total configs in puddles: {total_in_puddles}")
    for i, scc in enumerate(nontrivial_sccs[:5]):
        print(f"    Puddle {i}: size={len(scc)}")

    # ─── Binary flip analysis ───
    binary_procs = [i for i in range(n) if ms[i] == 2]
    if binary_procs:
        print(f"\n  --- Binary Flip Analysis ---")
        print(f"  Binary procs: {binary_procs}")

        # Positions near each mover
        near_any_mover = set()
        for p in mover_seq:
            near_any_mover |= {(p-1)%n, p, (p+1)%n}

        always_far = set(range(n)) - near_any_mover
        print(f"  Positions never near any mover: {sorted(always_far)}")
        always_far_binary = [b for b in binary_procs if b in always_far]
        print(f"  Always-far binary: {always_far_binary}")

        for b in binary_procs:
            # Per-step analysis: how many steps is b near the mover?
            near_count = sum(1 for p in mover_seq if min(abs(b-p)%n, abs(p-b)%n) <= 1)

            # Flip b in every cycle config
            flipped = []
            for c in cycle:
                lst = list(c)
                lst[b] = (lst[b] + 1) % ms[b]  # flip for binary, +1 mod m for others
                flipped.append(tuple(lst))
            flipped_set = set(flipped)

            # Check if flipped set forms a cycle
            is_cycle = True
            for fc in flipped:
                priv = privileged_set(fc, fs, ms)
                if len(priv) != 1:
                    is_cycle = False
                    break
                s = apply_move(fc, priv[0], fs, ms)
                if s not in flipped_set:
                    is_cycle = False
                    break

            # How many flipped configs are in the good cycle? In the basin?
            in_good = len(flipped_set & cycle_set)
            in_basin = len(flipped_set & full_basin)
            in_bad = len(flipped_set - full_basin)

            status = "SHADOW TRAP!" if is_cycle and in_good == 0 else "not a trap"
            print(f"  Binary {b}: near_mover={near_count}/{CL}, in_good={in_good}, in_basin={in_basin}, outside_basin={in_bad} [{status}]")

            if is_cycle and in_good == 0:
                # Verify cycle length
                node = flipped[0]
                vis = set()
                clen = 0
                while node not in vis:
                    vis.add(node)
                    clen += 1
                    priv = privileged_set(node, fs, ms)
                    node = apply_move(node, priv[0], fs, ms)
                print(f"    *** Shadow trap cycle length: {clen} ***")

        # DEEP: step-by-step flip preservation
        print(f"\n  --- Step-by-Step Flip Preservation ---")
        for b in binary_procs:
            preserved = 0
            for t in range(CL):
                c_orig = cycle[t]
                p = mover_seq[t]
                c_next_orig = cycle[(t+1) % CL]

                # Flip b
                c_flip = list(c_orig); c_flip[b] = 1 - c_flip[b]; c_flip = tuple(c_flip)
                c_next_flip = list(c_next_orig); c_next_flip[b] = 1 - c_next_flip[b]; c_next_flip = tuple(c_next_flip)

                # Does the flipped config follow the same transition?
                priv_flip = privileged_set(c_flip, fs, ms)
                if len(priv_flip) == 1 and priv_flip[0] == p:
                    actual_next = apply_move(c_flip, p, fs, ms)
                    if actual_next == c_next_flip:
                        preserved += 1

            print(f"  Binary {b}: {preserved}/{CL} steps perfectly preserved by flip")

    # ─── Capacity bound analysis ───
    print(f"\n  --- Capacity Bound Analysis ---")
    # Each cycle config can have at most D predecessors (in-degree bound)
    # Total basin ≤ CL + CL*D + CL*D^2 + ... (tree of depth T)
    # But D varies per config.

    # Compute actual tree depth
    depth = {}
    for c in cycle:
        depth[c] = 0
    queue = deque(cycle)
    while queue:
        node = queue.popleft()
        for pred in rev[node]:
            if pred not in depth:
                depth[pred] = depth[node] + 1
                queue.append(pred)

    max_depth = max(depth.values()) if depth else 0
    depth_hist = defaultdict(int)
    for d in depth.values():
        depth_hist[d] += 1

    print(f"  Max tree depth: {max_depth}")
    print(f"  Depth distribution: ", end="")
    for d in sorted(depth_hist.keys()):
        print(f"d={d}:{depth_hist[d]} ", end="")
    print()

    # Branching factor by depth
    for d in range(min(max_depth+1, 10)):
        configs_at_d = [c for c, dd in depth.items() if dd == d]
        if not configs_at_d:
            break
        total_children = sum(1 for c in configs_at_d for p in rev[c] if p in depth and depth[p] == d+1)
        avg_branch = total_children / len(configs_at_d) if configs_at_d else 0
        print(f"    Depth {d}: {len(configs_at_d)} configs, avg branching={avg_branch:.2f}")

    return {
        'P': P, 'CL': CL, 'basin': len(basin), 'full_basin': len(full_basin),
        'puddles': len(nontrivial_sccs), 'max_depth': max_depth, 'fair': fair
    }


def tarjan_scc(nodes, succs):
    """Iterative Tarjan's SCC algorithm."""
    index_map = {}
    lowlink = {}
    on_stack = set()
    stack = []
    sccs = []
    idx = [0]

    def strongconnect(v):
        work = [(v, iter(succs.get(v, set())), False)]
        index_map[v] = lowlink[v] = idx[0]
        idx[0] += 1
        stack.append(v)
        on_stack.add(v)

        while work:
            node, children, returning = work[-1]
            if returning:
                work.pop()
                if work:
                    parent = work[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])
                if lowlink[node] == index_map[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    sccs.append(scc)
                continue

            try:
                w = next(children)
                if w not in index_map:
                    index_map[w] = lowlink[w] = idx[0]
                    idx[0] += 1
                    stack.append(w)
                    on_stack.add(w)
                    work[-1] = (node, children, False)
                    work.append((w, iter(succs.get(w, set())), False))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], index_map[w])
            except StopIteration:
                work[-1] = (node, children, True)

    for v in nodes:
        if v not in index_map:
            strongconnect(v)

    return sccs


# ─── Main ───

def main():
    print("=" * 70)
    print("DRAINAGE BASIN ANALYSIS FOR SELF-STABILIZING TOKEN RINGS")
    print("=" * 70)

    # 1. M_5=96 valid witness (AT threshold — this is a valid system)
    print("\n\n### 1. M_5=96 WITNESS (VALID, AT THRESHOLD) ###")
    ms96, fs96 = build_m5_96_witness()
    r96 = full_analysis(ms96, fs96, "M_5=96 VALID witness")

    # 2. Dijkstra Sol1 at n=5, K=4 (product=1024, way above threshold)
    print("\n\n### 2. DIJKSTRA SOL1 n=5, K=4 (ABOVE THRESHOLD) ###")
    ms_d1, fs_d1 = build_dijkstra_sol1(5, 4)
    r_d1 = full_analysis(ms_d1, fs_d1, "Dijkstra Sol1 K=4")

    # 3. Dijkstra Sol3 at n=5 (product=243, above threshold)
    print("\n\n### 3. DIJKSTRA SOL3 n=5 (ABOVE THRESHOLD) ###")
    ms_d3, fs_d3 = build_dijkstra_sol3(5)
    r_d3 = full_analysis(ms_d3, fs_d3, "Dijkstra Sol3")

    # 4. Dijkstra Sol1 at n=7, K=3 (product=2187, threshold=108 => above)
    print("\n\n### 4. DIJKSTRA SOL1 n=7, K=3 ###")
    ms_d1_7, fs_d1_7 = build_dijkstra_sol1(7, 3)
    r_d1_7 = full_analysis(ms_d1_7, fs_d1_7, "Dijkstra Sol1 n=7 K=3")

    # 5. Now test SUB-THRESHOLD systems
    # Build systems with ms=(2,2,2,3,3), P=72 < 108
    # These CANNOT be valid (proven), so we examine their drainage structure
    print("\n\n### 5. SUB-THRESHOLD SYSTEMS ###")
    print("These cannot be valid self-stabilizing systems.")
    print("Question: what's the max possible good cycle basin?")

    # Use Dijkstra Sol3 privilege rule on sub-threshold state vectors
    # Sol3 uses different privilege at bottom/middle/top
    ms_sub = [2, 2, 2, 3, 3]
    P_sub = 72

    # Try ALL possible "incrementing" privilege rules
    # Privileged if f(L,S,R) != S. Simplest: L==S privilege (Sol1 style)
    print("\n  --- Sub-threshold with Sol1-style privilege ---")
    def f_dist(L, S, R, m=None):
        if L == S: return (S + 1) % m
        return S
    def f_other(L, S, R, m=None):
        if L != S: return L
        return S

    for K_base in [2, 3]:
        ms_test = [2, 2, 2, 3, 3]
        n = 5

        # Sol1-style: first proc distinguished
        def make_sol1_fs(ms):
            n = len(ms)
            fs = []
            for i in range(n):
                m = ms[i]
                mL = ms[(i-1) % n]
                if i == 0:
                    def f(L, S, R, m=m):
                        if L == S: return (S + 1) % m
                        return S
                else:
                    def f(L, S, R, m=m):
                        if L != S: return L % m  # copy left, mod own state count
                        return S
                fs.append(f)
            return fs

        fs_test = make_sol1_fs(ms_test)
        r = full_analysis(ms_test, fs_test, f"Sol1-style sub-threshold")

    # Test more permutations of ms
    print("\n  --- Different placements of binary procs ---")
    from itertools import permutations
    seen = set()
    for perm in permutations([2, 2, 2, 3, 3]):
        if perm in seen:
            continue
        seen.add(perm)
        ms_p = list(perm)
        fs_p = make_sol1_fs(ms_p)
        r = full_analysis(ms_p, fs_p, f"Sol1-style")

    # ─── PART 7: Binary flip on the M_5=96 VALID witness ───
    print("\n\n### PART 7: BINARY FLIP DEEP DIVE ON M_5=96 ###")
    # The M_5=96 witness has ms=[2,2,2,3,4], binary at 0,1,2
    # It IS valid. So basin = P = 96. All configs drain to good cycle.
    # Flipping a binary proc should NOT produce a shadow trap.
    # But WHY NOT? Understanding this reveals the mechanism.

    ms96, fs96 = build_m5_96_witness()
    configs96 = list(all_configs(ms96))
    priv96 = {c: privileged_set(c, fs96, ms96) for c in configs96}

    # Get the good cycle
    result = verify_system(ms96, fs96)
    print(f"  System valid: {result['valid']}")

    # Find the cycle directly
    # Start from (0,0,0,0,0) and follow
    start = (0,0,0,0,0)
    if len(priv96[start]) == 1:
        node = start
        cycle96 = []
        visited = set()
        while node not in visited:
            visited.add(node)
            cycle96.append(node)
            p = priv96[node][0]
            node = apply_move(node, p, fs96, ms96)
        print(f"  Cycle from (0,0,0,0,0): length={len(cycle96)}")

        # For each binary proc, flip and trace
        for b in [0, 1, 2]:
            print(f"\n  Flipping binary proc {b}:")
            for t in range(len(cycle96)):
                c = cycle96[t]
                p = priv96[c][0]  # mover
                c_next = cycle96[(t+1) % len(cycle96)]

                # Flip b
                cf = list(c); cf[b] = 1 - cf[b]; cf = tuple(cf)
                cf_next = list(c_next); cf_next[b] = 1 - cf_next[b]; cf_next = tuple(cf_next)

                # What happens to flipped config?
                priv_f = priv96[cf]
                if len(priv_f) == 1:
                    actual_next = apply_move(cf, priv_f[0], fs96, ms96)
                    same_mover = priv_f[0] == p
                    follows_flip = actual_next == cf_next
                    dist = min(abs(b-p)%5, abs(p-b)%5)
                    if not follows_flip:
                        print(f"    t={t}: c={c}, mover={p}, dist(b,p)={dist}, "
                              f"flip_mover={priv_f[0]}, follows_flip={follows_flip}")
                else:
                    dist = min(abs(b - priv96[c][0]) % 5, abs(priv96[c][0] - b) % 5)
                    print(f"    t={t}: c={c}, flip has {len(priv_f)} privs (BREAKS single-priv), dist={dist}")

    # ─── Summary statistics ───
    print("\n\n### SUMMARY ###")
    print("Key question: For sub-threshold systems with >=3 binary,")
    print("can we bound the drainage basin capacity?")
    print()
    print("Observations from the analysis above:")
    print("- Valid systems (M_5=96, Sol1, Sol3): basin = P (all configs drain)")
    print("- Sub-threshold with Sol1 privilege: either no cycle or basin << P")
    print("- Binary flip at distance > 1 from mover preserves step structure")
    print("- But fairness requires ALL procs to be movers => every position")
    print("  is near some mover => no position is always-far")
    print("- The key is: does flipping BREAK single-privilege at some step?")


if __name__ == "__main__":
    main()
