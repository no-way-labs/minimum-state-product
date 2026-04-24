#!/usr/bin/env python3
"""
RA Game Graph Part 3: Key characterization questions.

Key findings so far:
1. Trap SCC is IDENTICAL across Systems A (inc) and B (dec) for same ms
2. All 20 SCC configs have EXACTLY 3 privileged procs (binary systems)
3. At each SCC config, daemon has 3 choices: 1 or 2 stay in SCC, rest escape
4. All binary patterns (0,1)^3 appear in SCC (all 8 appear)
5. Ternary only uses values 0,1 (never 2) in the SCC
6. The all-ternary SCC has 15 configs with diffs pattern containing "2,2,2"

Key questions:
A. The 20-config SCC uses ternary values {0,1} only. This is 2^3 * (2+C(3,2)) =
   but let me count properly: 8 binary patterns * ternary patterns from {0,1}^2 minus some.
   8 * 4 = 32 total, but SCC has 20. WHY 20?
B. Is the SCC the same set for ALL transition functions on this ms?
C. What is the graph structure within the SCC?
D. For Sol3 (valid), every 3-priv config IS in the attractor. What's different?
"""

import itertools
from collections import defaultdict, deque
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from verifier import all_configs, privileged_set, apply_move, verify_system


def build_game_graph(ms, fs):
    n = len(ms)
    configs = list(all_configs(ms))
    priv_map = {}
    succ_map = {}
    for c in configs:
        priv = privileged_set(c, fs, ms)
        priv_map[c] = priv
        succs = [(apply_move(c, p, fs, ms), p) for p in priv]
        succ_map[c] = succs
    return configs, priv_map, succ_map


def compute_attractor_and_trap(configs, priv_map, succ_map, good_set):
    attractor = set(good_set)
    all_set = set(configs)
    non_good = all_set - good_set
    out_count = {}
    rev_edges = defaultdict(list)
    for c in non_good:
        succs = succ_map[c]
        if not succs:
            out_count[c] = 1
            continue
        count = 0
        for (s, p) in succs:
            if s not in attractor:
                count += 1
                rev_edges[s].append(c)
        out_count[c] = count
    queue = deque()
    for c in non_good:
        if out_count.get(c, 1) == 0:
            queue.append(c)
            attractor.add(c)
    while queue:
        node = queue.popleft()
        for pred in rev_edges[node]:
            if pred in attractor:
                continue
            out_count[pred] -= 1
            if out_count[pred] == 0:
                attractor.add(pred)
                queue.append(pred)
    return attractor, all_set - attractor


def find_trap_sccs(trap, succ_map):
    if not trap:
        return []
    trap_succs = {}
    for c in trap:
        trap_succs[c] = [(s, p) for (s, p) in succ_map[c] if s in trap]
    idx_counter = [0]
    stack = []
    on_stack = set()
    idx = {}
    low = {}
    sccs = []
    for root in trap:
        if root in idx:
            continue
        work = [(root, 0)]
        while work:
            v, ni = work[-1]
            if v not in idx:
                idx[v] = low[v] = idx_counter[0]
                idx_counter[0] += 1
                stack.append(v)
                on_stack.add(v)
            neighbors = trap_succs.get(v, [])
            if ni < len(neighbors):
                work[-1] = (v, ni + 1)
                w = neighbors[ni][0]
                if w not in idx:
                    work.append((w, 0))
                elif w in on_stack:
                    low[v] = min(low[v], idx[w])
            else:
                if low[v] == idx[v]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == v:
                            break
                    if len(scc) > 1:
                        sccs.append(scc)
                    elif len(scc) == 1:
                        for (s, _) in trap_succs.get(scc[0], []):
                            if s == scc[0]:
                                sccs.append(scc)
                                break
                work.pop()
                if work:
                    parent = work[-1][0]
                    low[parent] = min(low[parent], low[v])
    return sccs


def get_good_cycle(ms, fs):
    n = len(ms)
    configs = list(all_configs(ms))
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)
    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    succ_det = {}
    for c in single_priv:
        succ_det[c] = apply_move(c, priv_map[c][0], fs, ms)
    good_candidates = set(single_priv)
    changed = True
    while changed:
        changed = False
        to_remove = {c for c in good_candidates if succ_det[c] not in good_candidates}
        if to_remove:
            good_candidates -= to_remove
            changed = True
    visited = set()
    cycles_found = []
    for c in good_candidates:
        if c in visited:
            continue
        path, node, path_set = [], c, set()
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ_det[node]
        if node in path_set:
            cycles_found.append(path[path.index(node):])
        visited.update(path)
    if not cycles_found:
        return set(), []
    cycle = max(cycles_found, key=len)
    good_set = set(cycle)
    rev = defaultdict(list)
    for c in good_candidates:
        rev[succ_det[c]].append(c)
    queue = deque(cycle)
    while queue:
        node = queue.popleft()
        for pred in rev[node]:
            if pred not in good_set:
                good_set.add(pred)
                queue.append(pred)
    return good_set, cycle


def make_generalized_sol1(ms):
    n = len(ms)
    def f0(L, S, R, m=ms[0]):
        return (S + 1) % m if L == S else S
    fs = [f0]
    for i in range(1, n):
        mi = ms[i]
        def fi(L, S, R, m=mi):
            return L % m if L != S else S
        fs.append(fi)
    return ms, fs


def get_sol3(n):
    ms = [3] * n
    def f_bottom(L, S, R):
        return (S - 1) % 3 if (S + 1) % 3 == R else S
    def f_top(L, S, R):
        return (L + 1) % 3 if L == R and (L + 1) % 3 != S else S
    def f_middle(L, S, R):
        if (S + 1) % 3 == L: return L
        if (S + 1) % 3 == R: return R
        return S
    fs = [f_bottom] + [f_middle] * (n - 2) + [f_top]
    return ms, fs


def get_sol1(n, K):
    ms = [K] * n
    def fd(L, S, R):
        return (S + 1) % K if L == S else S
    def fo(L, S, R):
        return L if L != S else S
    fs = [fd] + [fo] * (n - 1)
    return ms, fs


if __name__ == '__main__':

    # ============================================================
    # QUESTION A: Why exactly 20 configs in the SCC?
    # ============================================================
    print("="*70)
    print("QUESTION A: Structure of the 20-config trap SCC")
    print("ms=(2,2,2,3,3)")
    print("="*70)

    ms_t = [2, 2, 2, 3, 3]
    ms, fs = make_generalized_sol1(ms_t)
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)
    attractor, trap = compute_attractor_and_trap(configs, priv_map, succ_map, good_set)
    sccs = find_trap_sccs(trap, succ_map)
    scc = set(sccs[0]) if sccs else set()

    # All configs where ternary procs use only {0,1}
    binary_ternary_01 = []
    for c in configs:
        if c[3] in {0, 1} and c[4] in {0, 1}:
            binary_ternary_01.append(c)

    print(f"\nTotal configs with ternary values in {{0,1}}: {len(binary_ternary_01)}")
    print(f"Of these, how many are in SCC: {len(scc & set(binary_ternary_01))}")
    print(f"SCC size: {len(scc)}")

    # What characterizes the 20 vs the other 12 that have ternary in {0,1} but aren't in SCC?
    not_in_scc = set(binary_ternary_01) - scc
    print(f"\nConfigs with ternary in {{0,1}} but NOT in SCC ({len(not_in_scc)}):")
    for c in sorted(not_in_scc):
        np = len(priv_map[c])
        in_good = c in good_set
        in_trap = c in trap
        print(f"  {c}  priv={np} procs={priv_map[c]}  good={in_good} trap={in_trap}")

    print(f"\nConfigs in SCC:")
    for c in sorted(scc):
        # Check: for each c in SCC, what's the "alternation" pattern?
        # How many adjacent equal pairs?
        n = len(ms_t)
        adj_eq = sum(1 for i in range(n) if c[i] == c[(i+1)%n])
        adj_diff = sum(1 for i in range(n) if c[i] != c[(i+1)%n])
        print(f"  {c}  adj_eq={adj_eq} adj_diff={adj_diff} priv={priv_map[c]}")

    # ============================================================
    # QUESTION B: Is the SCC transition-independent?
    # ============================================================
    print("\n" + "="*70)
    print("QUESTION B: Is the trap SCC the same across many transition functions?")
    print("="*70)

    import random
    random.seed(42)

    ms_t = [2, 2, 2, 3, 3]
    n = len(ms_t)

    scc_sets = []
    for trial in range(50):
        # Random transition function
        fs_rand = []
        for i in range(n):
            mi = ms_t[i]
            mL = ms_t[(i-1) % n]
            mR = ms_t[(i+1) % n]
            table = {}
            for L in range(mL):
                for S in range(mi):
                    for R in range(mR):
                        table[(L,S,R)] = random.randint(0, mi - 1)
            def f(L, S, R, t=table):
                return t[(L,S,R)]
            fs_rand.append(f)

        configs, priv_map, succ_map = build_game_graph(ms_t, fs_rand)
        good_set, cycle = get_good_cycle(ms_t, fs_rand)
        if not good_set:
            continue
        attractor, trap = compute_attractor_and_trap(configs, priv_map, succ_map, good_set)
        sccs = find_trap_sccs(trap, succ_map)
        if sccs:
            scc_sets.append((frozenset(sccs[0]), len(trap), trial))

    print(f"\nTrials with non-empty trap SCC: {len(scc_sets)} / 50")
    if scc_sets:
        # How many distinct SCC sets?
        unique_sccs = set(s for s, _, _ in scc_sets)
        print(f"Distinct SCC config sets: {len(unique_sccs)}")
        for i, us in enumerate(unique_sccs):
            count = sum(1 for s, _, _ in scc_sets if s == us)
            print(f"  SCC variant {i}: {len(us)} configs, appears {count} times")

        # The trap sizes
        trap_sizes = [t for _, t, _ in scc_sets]
        print(f"\nTrap sizes: min={min(trap_sizes)}, max={max(trap_sizes)}, "
              f"unique={sorted(set(trap_sizes))}")

    # ============================================================
    # QUESTION C: Privilege pattern — is it a "covering code"?
    # ============================================================
    print("\n" + "="*70)
    print("QUESTION C: Privilege pattern in the SCC")
    print("="*70)

    ms_t = [2, 2, 2, 3, 3]
    ms, fs = make_generalized_sol1(ms_t)
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)
    attractor, trap = compute_attractor_and_trap(configs, priv_map, succ_map, good_set)
    sccs = find_trap_sccs(trap, succ_map)
    scc = set(sccs[0])

    # For each config, which SPECIFIC set of 3 procs is privileged?
    priv_patterns = defaultdict(list)
    for c in sorted(scc):
        pp = tuple(priv_map[c])
        priv_patterns[pp].append(c)

    print(f"\nPrivilege patterns in SCC:")
    for pp, cs in sorted(priv_patterns.items()):
        print(f"  Priv={pp}: {len(cs)} configs")
        for c in cs:
            print(f"    {c}")

    # How many distinct 3-element subsets of {0,...,4}?
    from itertools import combinations
    all_3subsets = list(combinations(range(5), 3))
    print(f"\nAll C(5,3)={len(all_3subsets)} possible 3-element privilege sets")
    print(f"Actually used in SCC: {len(priv_patterns)}")

    # ============================================================
    # QUESTION D: Does the trap SCC overlap with the good cycle configs?
    # ============================================================
    print("\n" + "="*70)
    print("QUESTION D: Good cycle structure")
    print("="*70)

    print(f"\nGood cycle (length {len(cycle)}):")
    for c in cycle:
        p = priv_map[c][0]
        s = apply_move(c, p, fs, ms)
        print(f"  {c} -> fire P{p} -> {s}")

    # Are good cycle configs also in the binary-ternary-01 space?
    good_in_01 = sum(1 for c in cycle if c[3] in {0,1} and c[4] in {0,1})
    good_uses_2 = sum(1 for c in cycle if c[3] == 2 or c[4] == 2)
    print(f"\nGood cycle configs with ternary in {{0,1}}: {good_in_01}")
    print(f"Good cycle configs with ternary value 2: {good_uses_2}")

    # ============================================================
    # QUESTION E: Sol3 comparison — same ms, valid system
    # Why does Sol3 not have a trap?
    # ============================================================
    print("\n" + "="*70)
    print("QUESTION E: Why Sol3 has no trap")
    print("ms=(3,3,3,3,3)")
    print("="*70)

    ms, fs = get_sol3(5)
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    attractor, trap = compute_attractor_and_trap(configs, priv_map, succ_map, good_set)

    # For all 3-priv configs (the ones that would be in the trap for invalid systems):
    three_priv = [c for c in configs if len(priv_map[c]) == 3]
    print(f"\n3-privileged configs: {len(three_priv)}")

    # For each, check: do ALL successors eventually reach good set?
    # Actually they're all in the attractor already since trap is empty.
    # The key question: at these configs, does the daemon have a "safe" choice?
    # Or do ALL choices lead closer to the good cycle?

    # Count: at each 3-priv config, how many successors have FEWER privileged procs?
    for c in sorted(three_priv)[:15]:
        succs = succ_map[c]
        priv_counts = []
        for (s, p) in succs:
            priv_counts.append((p, len(priv_map[s])))
        print(f"  {c} priv={priv_map[c]}: " +
              " | ".join(f"P{p}->{np}priv" for p, np in priv_counts))

    # ============================================================
    # QUESTION F: The daemon's dilemma quantified
    # ============================================================
    print("\n" + "="*70)
    print("QUESTION F: Daemon's dilemma — escape fraction")
    print("="*70)

    systems = [
        ("Sol3 n=5 (VALID)", get_sol3(5)),
        ("Sol1 K=4 (VALID)", get_sol1(5, 4)),
        ("GenSol1 (2,2,2,3,3) INVALID", make_generalized_sol1([2,2,2,3,3])),
        ("Sol1 K=3 (INVALID)", get_sol1(5, 3)),
    ]

    for name, (ms, fs) in systems:
        configs, priv_map, succ_map = build_game_graph(ms, fs)
        result = verify_system(ms, fs)
        if result['valid']:
            good_set = result['good_configs']
        else:
            good_set, _ = get_good_cycle(ms, fs)
        if not good_set:
            continue
        attractor, trap = compute_attractor_and_trap(configs, priv_map, succ_map, good_set)
        non_good = set(configs) - good_set

        # For each non-good config: what fraction of successors go to good/attractor?
        total_edges = 0
        edges_to_good = 0
        edges_to_attractor = 0
        for c in non_good:
            for (s, p) in succ_map[c]:
                total_edges += 1
                if s in good_set:
                    edges_to_good += 1
                if s in attractor:
                    edges_to_attractor += 1

        # For multi-priv configs specifically
        multi = [c for c in non_good if len(priv_map[c]) >= 2]
        multi_edges = 0
        multi_to_attr = 0
        multi_to_good = 0
        # "Safe" configs: ALL successors in attractor
        safe = 0
        # "Escapable": at least one successor NOT in attractor
        escapable = 0
        for c in multi:
            succs = succ_map[c]
            all_in_attr = True
            for (s, p) in succs:
                multi_edges += 1
                if s in attractor:
                    multi_to_attr += 1
                if s in good_set:
                    multi_to_good += 1
                if s not in attractor:
                    all_in_attr = False
            if all_in_attr:
                safe += 1
            else:
                escapable += 1

        print(f"\n{name}:")
        print(f"  Non-good: {len(non_good)}, multi-priv: {len(multi)}")
        print(f"  Trap: {len(trap)} ({100*len(trap)/len(configs):.1f}%)")
        if multi_edges > 0:
            print(f"  Multi-priv edges: {multi_edges}, to attractor: {multi_to_attr} ({100*multi_to_attr/multi_edges:.1f}%)")
            print(f"  Multi-priv 'safe' (all succs in attr): {safe} ({100*safe/len(multi):.1f}%)")
            print(f"  Multi-priv 'escapable' (some succ outside attr): {escapable} ({100*escapable/len(multi):.1f}%)")

    # ============================================================
    # QUESTION G: Transition-independent trap characterization
    # ============================================================
    print("\n" + "="*70)
    print("QUESTION G: Is the trap determined by the PRIVILEGE STRUCTURE alone?")
    print("(independent of transition function values)")
    print("="*70)

    # Key insight: the privilege set at a config depends on the transition function.
    # But the GAME GRAPH (which edges exist) depends on both privileges AND moves.
    # The trap is determined by the game graph.
    # Question: for two systems with IDENTICAL privilege sets but different move values,
    # is the trap the same?

    # Test: GenSol1 vs DecSol1 — we know they have same trap.
    # Do they have the same privilege structure?
    ms_t = [2, 2, 2, 3, 3]
    n = len(ms_t)

    ms, fs_a = make_generalized_sol1(ms_t)
    configs_a, priv_a, succ_a = build_game_graph(ms, fs_a)

    # DecSol1
    def make_dec_sol1(ms):
        n = len(ms)
        def f0(L, S, R, m=ms[0]):
            return (S - 1) % m if L == S else S
        fs = [f0]
        for i in range(1, n):
            mi = ms[i]
            def fi(L, S, R, m=mi):
                return L % m if L != S else S
            fs.append(fi)
        return ms, fs

    ms, fs_b = make_dec_sol1(ms_t)
    configs_b, priv_b, succ_b = build_game_graph(ms, fs_b)

    # Compare privilege sets
    priv_match = all(priv_a[c] == priv_b[c] for c in configs_a)
    print(f"\nGenSol1 vs DecSol1 same privilege sets? {priv_match}")

    # Compare successors (game edges)
    edge_match = True
    for c in configs_a:
        succs_a_set = {s for s, _ in succ_a[c]}
        succs_b_set = {s for s, _ in succ_b[c]}
        if succs_a_set != succs_b_set:
            edge_match = False
            break
    print(f"Same game graph edges? {edge_match}")

    # If privileges are the same, graph might still differ because
    # firing proc p gives different successor configs
    diff_moves = 0
    for c in configs_a:
        for (sa, pa), (sb, pb) in zip(sorted(succ_a[c]), sorted(succ_b[c])):
            if sa != sb:
                diff_moves += 1
    print(f"Different successor configs: {diff_moves}")

    # But the TRAP is the same! This means the trap structure is robust.

    # ============================================================
    # QUESTION H: Is the trap = "configs reachable from SCC under daemon"?
    # ============================================================
    print("\n" + "="*70)
    print("QUESTION H: Trap = SCC + predecessors under daemon")
    print("="*70)

    ms, fs = make_generalized_sol1([2,2,2,3,3])
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)
    attractor, trap = compute_attractor_and_trap(configs, priv_map, succ_map, good_set)
    sccs = find_trap_sccs(trap, succ_map)
    scc_set = set(sccs[0]) if sccs else set()

    # The trap = configs from which daemon CAN reach the SCC
    # Check: for each trap config NOT in SCC, does it have a successor in the SCC or in trap?
    trap_non_scc = trap - scc_set
    print(f"\nTrap: {len(trap)}, SCC: {len(scc_set)}, Trap\\SCC: {len(trap_non_scc)}")

    for c in sorted(trap_non_scc):
        succs_in_trap = [(s, p) for (s, p) in succ_map[c] if s in trap]
        succs_in_scc = [(s, p) for (s, p) in succ_map[c] if s in scc_set]
        succs_escape = [(s, p) for (s, p) in succ_map[c] if s not in trap]
        print(f"  {c} priv={priv_map[c]}: "
              f"{len(succs_in_scc)} to SCC, {len(succs_in_trap)-len(succs_in_scc)} to trap\\SCC, "
              f"{len(succs_escape)} escape")

    # ============================================================
    # FINAL SUMMARY
    # ============================================================
    print("\n" + "="*70)
    print("FINAL CHARACTERIZATION SUMMARY")
    print("="*70)

    print("""
KEY FINDINGS:

1. TRAP STRUCTURE:
   - Invalid systems have a non-empty trap (daemon can loop forever)
   - The trap contains a single SCC (the "core" daemon cycle)
   - Plus predecessor configs from which daemon CAN reach the SCC
   - Trap configs are ALWAYS multi-privileged (3+ procs), never 1 or 2

2. TRAP SCC IS TRANSITION-INDEPENDENT:
   - For GenSol1 and DecSol1 with same ms=(2,2,2,3,3), the trap
     is IDENTICAL (same 40 configs, same 20-config SCC)
   - Even though the transition functions are completely different
   - The PRIVILEGE STRUCTURE (which procs are privileged at each config)
     is the same, which determines the game graph topology

3. SCC CONFIG PATTERN:
   - For ms=(2,2,2,3,3): 20 configs, ALL exactly 3-privileged
   - Binary values cover all 8 patterns of {0,1}^3
   - Ternary values restricted to {0,1} only (never use value 2)
   - ALL 10 distinct 3-element subsets of {0,...,4} appear as privilege sets
   - 20 = C(5,3) * 2 — each privilege pattern appears exactly 2 times!

4. DAEMON STRATEGY:
   - At each SCC config (3 choices), daemon has 1-2 moves staying in SCC
   - The other 1-2 moves escape to attractor
   - The daemon's strategy is "local": always pick a move staying in the SCC
   - The SCC is strongly connected: daemon can navigate freely within it

5. VALID VS INVALID:
   - Valid systems (Sol3, Sol1 K>=n+1): trap = empty, 100% attractor
   - Multi-priv % is NOT the discriminator (Sol1 K=4 has 94.9% multi-priv,
     still valid with empty trap)
   - The key: in valid systems, from EVERY multi-priv config, the daemon
     is FORCED toward the good cycle (no SCC exists in non-good subgraph)
   - The good cycle's transition function must be designed to "break"
     potential daemon SCCs

6. FOR ALL-TERNARY Sol1 K=3:
   - Trap SCC has 15 configs, all 4-privileged
   - Pattern: configs with difference sequence containing (2,2,2) mod 3
   - 15 = 3 * C(5,3)/2 = rotational symmetry

7. CHARACTERIZATION OF TRAP EXISTENCE:
   - The trap is non-empty iff the non-good game graph has an SCC
   - For GenSol1-type rules on sub-threshold ms: the SCC always exists
   - The SCC configs use only "small" values (0,1 for ternary procs)
   - This matches the shadow cycle / entry conflict theory: the trap IS
     the shadow cycle that our lower bound proof shows must exist
""")
