#!/usr/bin/env python3
"""
RA Game Graph Part 4: Connect trap SCC to shadow cycle theory.

The 20-config trap SCC for ms=(2,2,2,3,3) with GenSol1 rules has:
- All configs in {0,1}^5 (ternary procs restricted to {0,1})
- 20 = C(5,3)*2 configs
- Each 3-element privilege set appears exactly twice
- Configs appear in complementary pairs: c and ~c (bitwise complement)

Let's verify: is the complement pairing exact? And does this connect
to the shadow cycle construction?
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


def compute_trap(configs, priv_map, succ_map, good_set):
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
    return all_set - attractor


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
    good = set(single_priv)
    changed = True
    while changed:
        changed = False
        rm = {c for c in good if succ_det[c] not in good}
        if rm:
            good -= rm
            changed = True
    visited = set()
    cycles = []
    for c in good:
        if c in visited:
            continue
        path, node, ps = [], c, set()
        while node not in visited and node not in ps:
            path.append(node)
            ps.add(node)
            node = succ_det[node]
        if node in ps:
            cycles.append(path[path.index(node):])
        visited.update(path)
    if not cycles:
        return set(), []
    cycle = max(cycles, key=len)
    gs = set(cycle)
    rev = defaultdict(list)
    for c in good:
        rev[succ_det[c]].append(c)
    q = deque(cycle)
    while q:
        n0 = q.popleft()
        for p in rev[n0]:
            if p not in gs:
                gs.add(p)
                q.append(p)
    return gs, cycle


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


if __name__ == '__main__':

    # ============================================================
    # 1. Complement structure of SCC
    # ============================================================
    print("="*70)
    print("1. COMPLEMENT STRUCTURE OF TRAP SCC")
    print("="*70)

    ms_t = [2, 2, 2, 3, 3]
    ms, fs = make_generalized_sol1(ms_t)
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)
    trap = compute_trap(configs, priv_map, succ_map, good_set)
    sccs = find_trap_sccs(trap, succ_map)
    scc = set(sccs[0])

    print(f"\nSCC size: {len(scc)}")
    print(f"\nComplement pairs (c, ~c):")
    seen = set()
    complement_pairs = 0
    for c in sorted(scc):
        if c in seen:
            continue
        # Complement: flip each bit (mod mi)
        comp = tuple((ms_t[i] - 1 - c[i]) for i in range(len(ms_t)))
        if comp in scc:
            complement_pairs += 1
            priv_c = tuple(priv_map[c])
            priv_comp = tuple(priv_map[comp])
            print(f"  {c} priv={priv_c}")
            print(f"  {comp} priv={priv_comp}")
            # Check: are privilege sets complementary?
            priv_c_set = set(priv_c)
            priv_comp_set = set(priv_comp)
            print(f"  Same priv set? {priv_c_set == priv_comp_set}")
            print()
            seen.add(c)
            seen.add(comp)
        else:
            print(f"  {c} has NO complement in SCC!")
            seen.add(c)

    print(f"Complement pairs: {complement_pairs}")
    print(f"Unpaired: {len(scc) - 2*complement_pairs}")

    # ============================================================
    # 2. The good cycle IS also in {0,1}^5 — how does it avoid the trap?
    # ============================================================
    print("\n" + "="*70)
    print("2. GOOD CYCLE vs TRAP SCC — both in {0,1}^5")
    print("="*70)

    print(f"\nGood cycle ({len(cycle)} configs):")
    for c in cycle:
        in_scc = "SCC!" if c in scc else "not SCC"
        print(f"  {c}  priv={priv_map[c]}  [{in_scc}]")

    # The 12 {0,1}^5 configs NOT in SCC
    all_01 = list(itertools.product(range(2), repeat=5))
    not_scc = [c for c in all_01 if c not in scc]
    print(f"\n{0,1}^5 configs NOT in SCC ({len(not_scc)}):")
    for c in not_scc:
        in_good = "GOOD" if c in good_set else "bad"
        np = len(priv_map[c])
        print(f"  {c}  priv_count={np}  [{in_good}]")

    # KEY INSIGHT: The 12 non-SCC configs in {0,1}^5 are exactly:
    # - 10 good cycle configs (1 priv each)
    # - 2 configs with 5 priv (all procs privileged)
    print(f"\nOf the 12 non-SCC {0,1}^5 configs:")
    print(f"  In good set: {sum(1 for c in not_scc if c in good_set)}")
    print(f"  5-privileged: {sum(1 for c in not_scc if len(priv_map[c]) == 5)}")
    print(f"  Other: {sum(1 for c in not_scc if c not in good_set and len(priv_map[c]) != 5)}")

    # ============================================================
    # 3. The SCC as a graph: in/out degree within SCC
    # ============================================================
    print("\n" + "="*70)
    print("3. SCC GRAPH STRUCTURE")
    print("="*70)

    in_deg = defaultdict(int)
    out_deg = defaultdict(int)
    scc_edges = []
    for c in scc:
        for (s, p) in succ_map[c]:
            if s in scc:
                out_deg[c] += 1
                in_deg[s] += 1
                scc_edges.append((c, s, p))

    print(f"\nSCC edges: {len(scc_edges)}")
    print(f"Average out-degree: {sum(out_deg[c] for c in scc)/len(scc):.1f}")
    print(f"Average in-degree: {sum(in_deg[c] for c in scc)/len(scc):.1f}")

    print(f"\nOut-degree distribution:")
    for d in sorted(set(out_deg.values())):
        count = sum(1 for c in scc if out_deg[c] == d)
        print(f"  out-deg {d}: {count} configs")

    print(f"\nIn-degree distribution:")
    for d in sorted(set(in_deg.values())):
        count = sum(1 for c in scc if in_deg.get(c,0) == d)
        print(f"  in-deg {d}: {count} configs")

    # ============================================================
    # 4. Scale up: n=6,7 with same structure
    # ============================================================
    print("\n" + "="*70)
    print("4. SCALING: Trap SCC for n=4,5,6,7")
    print("="*70)

    for n_val in [4, 5, 6, 7]:
        # ms = (2,...,2,3,...,3) with 3 binary and rest ternary
        n_bin = min(3, n_val)
        ms_t = [2]*n_bin + [3]*(n_val - n_bin)
        product = 1
        for m in ms_t:
            product *= m

        ms, fs = make_generalized_sol1(ms_t)
        configs, priv_map, succ_map = build_game_graph(ms, fs)
        good_set, cycle = get_good_cycle(ms, fs)
        if not good_set:
            print(f"\nn={n_val}, ms={ms_t}: no good cycle")
            continue
        trap = compute_trap(configs, priv_map, succ_map, good_set)
        sccs = find_trap_sccs(trap, succ_map)

        scc_size = len(sccs[0]) if sccs else 0
        priv_in_scc = defaultdict(int)
        if sccs:
            for c in sccs[0]:
                priv_in_scc[len(priv_map[c])] += 1

        print(f"\nn={n_val}, ms={ms_t}, product={product}:")
        print(f"  Total configs: {product}")
        print(f"  Good set: {len(good_set)}")
        print(f"  Trap: {len(trap)} ({100*len(trap)/product:.1f}%)")
        print(f"  Trap SCCs: {len(sccs)}")
        if sccs:
            print(f"  Largest SCC: {scc_size}")
            print(f"  SCC privilege dist: {dict(sorted(priv_in_scc.items()))}")
            # Check C(n,3)*2 hypothesis
            from math import comb
            expected = comb(n_val, 3) * 2
            print(f"  C(n,3)*2 = {expected}, actual SCC = {scc_size}, match = {scc_size == expected}")

    # ============================================================
    # 5. The two 5-privileged configs — "poles"
    # ============================================================
    print("\n" + "="*70)
    print("5. THE TWO 5-PRIVILEGED CONFIGS (POLES)")
    print("="*70)

    ms_t = [2, 2, 2, 3, 3]
    ms, fs = make_generalized_sol1(ms_t)
    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)
    trap = compute_trap(configs, priv_map, succ_map, good_set)
    sccs = find_trap_sccs(trap, succ_map)
    scc = set(sccs[0])

    five_priv = [c for c in configs if len(priv_map[c]) == 5]
    print(f"\n5-privileged configs: {five_priv}")
    for c in five_priv:
        in_trap = c in trap
        in_scc = c in scc
        print(f"  {c}: in_trap={in_trap}, in_scc={in_scc}")
        print(f"  Successors:")
        for (s, p) in succ_map[c]:
            dest = "SCC" if s in scc else ("trap" if s in trap else ("good" if s in good_set else "attractor"))
            print(f"    fire P{p} -> {s} [{dest}] priv={len(priv_map[s])}")

    # ============================================================
    # 6. Connection to shadow cycle configs
    # ============================================================
    print("\n" + "="*70)
    print("6. SCC CONFIG = SHADOW CYCLE CONFIG?")
    print("="*70)

    # In the shadow cycle theory, the shadow cycle configs are constructed
    # from the good cycle by a specific permutation + complement operation.
    # Good cycle: (0,0,0,0,0) -> (1,0,0,0,0) -> (1,1,0,0,0) -> ... -> (0,0,0,0,0)
    # This is a "wave" pattern.

    # The SCC configs: all 3-privileged configs in {0,1}^5
    # Let's check: does every 3-priv config in {0,1}^5 have the property
    # that it's NOT on the "good wave" and NOT all-same?

    print("\nAll {0,1}^5 configs classified:")
    for c in sorted(itertools.product(range(2), repeat=5)):
        priv = priv_map[c]
        cat = "good" if c in good_set else ("SCC" if c in scc else ("trap" if c in trap else "attr"))
        print(f"  {c}  priv_count={len(priv)}  [{cat}]")

    # The partition: {0,1}^5 = 32 configs = 10 good + 20 SCC + 2 poles (5-priv, in trap but not SCC)
    print(f"\nPartition of {{0,1}}^5:")
    print(f"  Good: {sum(1 for c in itertools.product(range(2), repeat=5) if c in good_set)}")
    print(f"  SCC: {sum(1 for c in itertools.product(range(2), repeat=5) if c in scc)}")
    print(f"  Trap\\SCC: {sum(1 for c in itertools.product(range(2), repeat=5) if c in trap and c not in scc)}")
    print(f"  Attractor\\Good: {sum(1 for c in itertools.product(range(2), repeat=5) if c not in trap and c not in good_set)}")
