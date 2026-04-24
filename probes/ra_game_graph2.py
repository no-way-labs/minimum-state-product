#!/usr/bin/env python3
"""
RA Game Graph Part 2: Deep trap structure analysis.

Key findings from Part 1:
- Valid systems: trap = empty, attractor = 100% of configs
- Invalid systems: non-empty trap with daemon-winning cycles
- Trap configs are ALL highly-privileged (3+ procs privileged)
- All 2-priv configs land in attractor, not trap
- Remarkable: the SCC size is exactly 20 for binary systems, 15 for all-ternary

Questions:
1. What IS this 20-config SCC? Is it the same configs across different systems?
2. How does the trap SCC relate to the good cycle structure?
3. What is the minimum privilege count in the trap?
4. Is there a transition function that BREAKS the trap for these ms?
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


def compute_attractor(configs, priv_map, succ_map, good_set):
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
    trap = all_set - attractor
    return attractor, trap


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
    """Get best good cycle and good set."""
    n = len(ms)
    configs = list(all_configs(ms))
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)

    single_priv = {c for c in configs if len(priv_map[c]) == 1}
    succ_det = {}
    for c in single_priv:
        p = priv_map[c][0]
        succ_det[c] = apply_move(c, p, fs, ms)

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
        path = []
        node = c
        path_set = set()
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ_det[node]
        if node in path_set:
            i = path.index(node)
            cycles_found.append(path[i:])
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
        if L == S:
            return (S + 1) % m
        return S
    fs = [f0]
    for i in range(1, n):
        mi = ms[i]
        def fi(L, S, R, m=mi):
            if L != S:
                return L % m
            return S
        fs.append(fi)
    return ms, fs


def get_sol3(n):
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


def get_sol1(n, K):
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


if __name__ == '__main__':
    # ============================================================
    # DEEP ANALYSIS 1: Compare trap configs across different systems
    # with the same ms=(2,2,2,3,3)
    # ============================================================
    print("="*70)
    print("DEEP ANALYSIS 1: Trap config identity across transition functions")
    print("ms = (2,2,2,3,3), product = 72")
    print("="*70)

    ms_target = [2, 2, 2, 3, 3]

    # System A: GenSol1
    ms, fs_a = make_generalized_sol1(ms_target)
    configs, priv_a, succ_a = build_game_graph(ms, fs_a)
    good_a, cycle_a = get_good_cycle(ms, fs_a)
    attr_a, trap_a = compute_attractor(configs, priv_a, succ_a, good_a)

    # System B: different transition (decrementing for proc 0)
    def make_dec_sol1(ms):
        n = len(ms)
        def f0(L, S, R, m=ms[0]):
            if L == S:
                return (S - 1) % m  # DECREMENT instead of increment
            return S
        fs = [f0]
        for i in range(1, n):
            mi = ms[i]
            def fi(L, S, R, m=mi):
                if L != S:
                    return L % m
                return S
            fs.append(fi)
        return ms, fs

    ms, fs_b = make_dec_sol1(ms_target)
    configs, priv_b, succ_b = build_game_graph(ms, fs_b)
    good_b, cycle_b = get_good_cycle(ms, fs_b)
    attr_b, trap_b = compute_attractor(configs, priv_b, succ_b, good_b)

    # System C: right-neighbor trigger instead of left
    def make_right_trigger(ms):
        n = len(ms)
        def f0(L, S, R, m=ms[0]):
            if R == S:
                return (S + 1) % m
            return S
        fs = [f0]
        for i in range(1, n):
            mi = ms[i]
            def fi(L, S, R, m=mi):
                if R != S:
                    return R % m
                return S
            fs.append(fi)
        return ms, fs

    ms, fs_c = make_right_trigger(ms_target)
    configs, priv_c, succ_c = build_game_graph(ms, fs_c)
    good_c, cycle_c = get_good_cycle(ms, fs_c)
    attr_c, trap_c = compute_attractor(configs, priv_c, succ_c, good_c)

    print(f"\nSystem A (GenSol1): trap={len(trap_a)}, good={len(good_a)}")
    print(f"System B (DecSol1): trap={len(trap_b)}, good={len(good_b)}")
    print(f"System C (RightTrigger): trap={len(trap_c)}, good={len(good_c)}")

    if trap_a and trap_b:
        overlap_ab = trap_a & trap_b
        print(f"\nTrap overlap A∩B: {len(overlap_ab)} configs (out of A={len(trap_a)}, B={len(trap_b)})")
    if trap_a and trap_c:
        overlap_ac = trap_a & trap_c
        print(f"Trap overlap A∩C: {len(overlap_ac)} configs (out of A={len(trap_a)}, C={len(trap_c)})")

    # SCCs
    if trap_a:
        sccs_a = find_trap_sccs(trap_a, succ_a)
        if sccs_a:
            scc_set_a = set(sccs_a[0])
            print(f"\nSystem A trap SCC configs ({len(sccs_a[0])}):")
            for c in sorted(sccs_a[0]):
                priv = priv_a[c]
                print(f"  {c}  priv_count={len(priv)} procs={priv}")

    if trap_b:
        sccs_b = find_trap_sccs(trap_b, succ_b)
        if sccs_b:
            scc_set_b = set(sccs_b[0])
            print(f"\nSystem B trap SCC configs ({len(sccs_b[0])}):")
            for c in sorted(sccs_b[0]):
                priv = priv_b[c]
                print(f"  {c}  priv_count={len(priv)} procs={priv}")

    # ============================================================
    # DEEP ANALYSIS 2: Configs in the trap SCC — what pattern?
    # ============================================================
    print("\n" + "="*70)
    print("DEEP ANALYSIS 2: Pattern in trap SCC configs")
    print("="*70)

    if trap_a and sccs_a:
        scc = sccs_a[0]
        print(f"\nTrap SCC for GenSol1 (2,2,2,3,3):")

        # Check: are all configs in the SCC such that binary procs alternate?
        # i.e., for procs with m=2, do the values follow a specific pattern?
        print("\nBinary proc values in SCC configs:")
        binary_procs = [i for i, m in enumerate(ms_target) if m == 2]
        ternary_procs = [i for i, m in enumerate(ms_target) if m > 2]
        print(f"Binary procs: {binary_procs}")
        print(f"Ternary procs: {ternary_procs}")

        for c in sorted(scc):
            binary_vals = tuple(c[i] for i in binary_procs)
            ternary_vals = tuple(c[i] for i in ternary_procs)
            print(f"  {c}  binary={binary_vals}  ternary={ternary_vals}  priv={priv_a[c]}")

        # Count unique ternary patterns
        ternary_patterns = defaultdict(list)
        for c in scc:
            tp = tuple(c[i] for i in ternary_procs)
            ternary_patterns[tp].append(c)
        print(f"\nUnique ternary patterns: {len(ternary_patterns)}")
        for tp, configs_with in sorted(ternary_patterns.items()):
            print(f"  ternary={tp}: {len(configs_with)} configs")

        # Count unique binary patterns
        binary_patterns = defaultdict(list)
        for c in scc:
            bp = tuple(c[i] for i in binary_procs)
            binary_patterns[bp].append(c)
        print(f"\nUnique binary patterns: {len(binary_patterns)}")
        for bp, configs_with in sorted(binary_patterns.items()):
            print(f"  binary={bp}: {len(configs_with)} configs")

    # ============================================================
    # DEEP ANALYSIS 3: All-ternary trap (Sol1 K=3)
    # ============================================================
    print("\n" + "="*70)
    print("DEEP ANALYSIS 3: All-ternary trap (Sol1 n=5 K=3)")
    print("="*70)

    ms, fs = get_sol1(5, 3)
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)
    attractor, trap = compute_attractor(configs, priv_map, succ_map, good_set)

    sccs = find_trap_sccs(trap, succ_map)
    if sccs:
        scc = sccs[0]
        print(f"\nTrap SCC ({len(scc)} configs):")
        for c in sorted(scc):
            priv = priv_map[c]
            print(f"  {c}  priv_count={len(priv)} procs={priv}")

        # Check: are these the "uniform" configs (all same value)?
        uniform = [c for c in scc if len(set(c)) == 1]
        print(f"\nUniform configs in SCC: {len(uniform)}")

        # Check: what's the relationship between consecutive values?
        print("\nDifferences (c[i]-c[i-1]) mod 3:")
        for c in sorted(scc):
            diffs = [(c[i] - c[(i-1)%5]) % 3 for i in range(5)]
            print(f"  {c}  diffs={diffs}")

    # ============================================================
    # DEEP ANALYSIS 4: How daemon navigates the trap
    # ============================================================
    print("\n" + "="*70)
    print("DEEP ANALYSIS 4: Daemon strategy in trap SCC")
    print("="*70)

    # For GenSol1 (2,2,2,3,3)
    ms, fs = make_generalized_sol1([2, 2, 2, 3, 3])
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)
    attractor, trap = compute_attractor(configs, priv_map, succ_map, good_set)
    sccs = find_trap_sccs(trap, succ_map)

    if sccs:
        scc_set = set(sccs[0])
        print(f"\nFor each trap SCC config, daemon's available moves:")
        for c in sorted(sccs[0]):
            succs = succ_map[c]
            print(f"\n  Config {c} (priv={priv_map[c]}):")
            for (s, p) in succs:
                in_scc = "IN SCC" if s in scc_set else ("IN TRAP" if s in trap else "ESCAPES to attractor")
                print(f"    fire P{p} -> {s}  [{in_scc}]")

        # Count: for each SCC config, how many choices stay in SCC vs escape?
        print(f"\nDaemon choice quality:")
        for c in sorted(sccs[0]):
            succs = succ_map[c]
            in_scc = sum(1 for (s,_) in succs if s in scc_set)
            in_trap = sum(1 for (s,_) in succs if s in trap)
            escape = sum(1 for (s,_) in succs if s not in trap)
            print(f"  {c}: {len(succs)} choices, {in_scc} stay in SCC, {in_trap-in_scc} in trap, {escape} escape")

    # ============================================================
    # DEEP ANALYSIS 5: Minimum privilege in trap — universal?
    # ============================================================
    print("\n" + "="*70)
    print("DEEP ANALYSIS 5: Minimum privilege count in trap")
    print("="*70)

    test_systems = [
        ("GenSol1 (2,2,2,3,3)", make_generalized_sol1([2,2,2,3,3])),
        ("GenSol1 (2,2,2,3,4)", make_generalized_sol1([2,2,2,3,4])),
        ("GenSol1 (2,2,2,2,3)", make_generalized_sol1([2,2,2,2,3])),
        ("Sol1 n=5 K=3", get_sol1(5, 3)),
        ("GenSol1 (3,3,3,3,3)", make_generalized_sol1([3,3,3,3,3])),
    ]

    for name, (ms, fs) in test_systems:
        configs, priv_map, succ_map = build_game_graph(ms, fs)
        good_set, cycle = get_good_cycle(ms, fs)
        if not good_set:
            print(f"  {name}: no good cycle found")
            continue
        attractor, trap = compute_attractor(configs, priv_map, succ_map, good_set)
        if trap:
            min_priv = min(len(priv_map[c]) for c in trap)
            max_priv = max(len(priv_map[c]) for c in trap)
            priv_dist = defaultdict(int)
            for c in trap:
                priv_dist[len(priv_map[c])] += 1
            print(f"  {name}: trap={len(trap)}, min_priv={min_priv}, max_priv={max_priv}, dist={dict(sorted(priv_dist.items()))}")
        else:
            print(f"  {name}: EMPTY trap")

    # ============================================================
    # DEEP ANALYSIS 6: Trap SCC = shadow cycle?
    # ============================================================
    print("\n" + "="*70)
    print("DEEP ANALYSIS 6: Is the trap SCC a known shadow cycle?")
    print("="*70)

    ms_t = [2, 2, 2, 3, 3]
    ms, fs = make_generalized_sol1(ms_t)
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)
    attractor, trap = compute_attractor(configs, priv_map, succ_map, good_set)
    sccs = find_trap_sccs(trap, succ_map)

    if sccs:
        scc = sccs[0]
        scc_set = set(scc)

        # Find an actual cycle through the SCC
        # Start from any config, always choose a successor in the SCC
        start = sorted(scc)[0]
        path = [start]
        visited = {start}
        node = start
        while True:
            next_in_scc = [(s,p) for (s,p) in succ_map[node] if s in scc_set]
            if not next_in_scc:
                break
            # Pick first unvisited, or if all visited, pick one to close cycle
            unvisited = [(s,p) for (s,p) in next_in_scc if s not in visited]
            if unvisited:
                s, p = unvisited[0]
                path.append(s)
                visited.add(s)
                node = s
            else:
                # Try to close cycle
                for s, p in next_in_scc:
                    if s == start:
                        path.append(s)
                        break
                break

        print(f"\nSCC cycle walk (length {len(path)-1 if path[-1]==start else len(path)}):")
        if path[-1] == start:
            for i in range(len(path)-1):
                c = path[i]
                c_next = path[i+1]
                for (s, p) in succ_map[c]:
                    if s == c_next:
                        print(f"  Step {i}: {c} -> fire P{p} -> {c_next}")
                        break

        # How many configs in SCC have ALL successors in SCC?
        all_in_scc = sum(1 for c in scc if all(s in scc_set for (s,_) in succ_map[c]))
        some_escape = sum(1 for c in scc if any(s not in scc_set for (s,_) in succ_map[c]))
        print(f"\nSCC configs where ALL successors stay in SCC: {all_in_scc}")
        print(f"SCC configs where SOME successor escapes SCC: {some_escape}")

        # For those that can escape, where do they go?
        for c in sorted(scc):
            escapes = [(s, p) for (s, p) in succ_map[c] if s not in scc_set]
            if escapes:
                for (s, p) in escapes:
                    dest = "trap" if s in trap else "attractor"
                    print(f"  {c} fire P{p} -> {s} [{dest}]")

    # ============================================================
    # DEEP ANALYSIS 7: Attractor layers (convergence depth)
    # ============================================================
    print("\n" + "="*70)
    print("DEEP ANALYSIS 7: Attractor layers (convergence depth)")
    print("="*70)

    for name, (ms, fs) in [("Sol3 n=5", get_sol3(5)), ("GenSol1 (2,2,2,3,3)", make_generalized_sol1([2,2,2,3,3]))]:
        configs, priv_map, succ_map = build_game_graph(ms, fs)

        result = verify_system(ms, fs)
        if result['valid']:
            good_set = result['good_configs']
        else:
            good_set, _ = get_good_cycle(ms, fs)

        if not good_set:
            continue

        # Compute attractor layers
        attractor = set(good_set)
        all_set = set(configs)
        non_good = all_set - good_set
        layer = {c: 0 for c in good_set}

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

        current_layer = 1
        queue = deque()
        for c in non_good:
            if out_count.get(c, 1) == 0:
                queue.append(c)
                attractor.add(c)
                layer[c] = current_layer

        while queue:
            next_queue = deque()
            while queue:
                node = queue.popleft()
                for pred in rev_edges[node]:
                    if pred in attractor:
                        continue
                    out_count[pred] -= 1
                    if out_count[pred] == 0:
                        attractor.add(pred)
                        layer[pred] = current_layer + 1
                        next_queue.append(pred)
            queue = next_queue
            current_layer += 1

        layer_counts = defaultdict(int)
        for c, lv in layer.items():
            layer_counts[lv] += 1

        print(f"\n{name}:")
        print(f"  Total layers: {max(layer.values()) if layer else 0}")
        for lv in sorted(layer_counts.keys()):
            print(f"  Layer {lv}: {layer_counts[lv]} configs")

        trap = all_set - attractor
        if trap:
            print(f"  Trap (unreachable by attractor): {len(trap)} configs")
