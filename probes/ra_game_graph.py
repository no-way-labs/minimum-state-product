#!/usr/bin/env python3
"""
RA: Game Graph Analysis for Self-Stabilizing Token Rings

Investigates the game-theoretic structure:
- System (protagonist) vs Daemon (adversary)
- At multi-privileged configs, daemon chooses which proc fires
- ShadowTrap = daemon winning cycle (closed loop of non-good configs)

Parts 1-6: privilege stats, attractor/trap computation, trap structure,
valid vs invalid comparison.
"""

import itertools
from collections import defaultdict, deque
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from verifier import all_configs, privileged_set, apply_move, verify_system


def build_game_graph(ms, fs):
    """Build full game graph. Returns privilege map and successor map."""
    n = len(ms)
    configs = list(all_configs(ms))

    priv_map = {}
    succ_map = {}

    for c in configs:
        priv = privileged_set(c, fs, ms)
        priv_map[c] = priv
        succs = []
        for p in priv:
            s = apply_move(c, p, fs, ms)
            succs.append((s, p))
        succ_map[c] = succs

    return configs, priv_map, succ_map


def privilege_stats(configs, priv_map):
    """Count configs by number of privileged processors."""
    counts = defaultdict(int)
    for c in configs:
        counts[len(priv_map[c])] += 1
    return dict(sorted(counts.items()))


def compute_attractor(configs, priv_map, succ_map, good_set):
    """
    Compute attractor of good_set under daemon adversary.
    A non-good config c is in the attractor iff ALL its successors are in the attractor.
    """
    attractor = set(good_set)
    all_set = set(configs)
    non_good = all_set - good_set

    # out_count[c] = number of successors of c NOT in attractor
    out_count = {}
    rev_edges = defaultdict(list)

    for c in non_good:
        succs = succ_map[c]
        if not succs:
            # No successors = deadlock. Treat as in attractor (can't escape anyway)
            # Actually a deadlock with 0 priv is stuck forever. NOT in attractor.
            out_count[c] = 1  # can't reach good, so never resolves
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
    """Find SCCs in the trap using iterative Tarjan's."""
    if not trap:
        return []

    trap_succs = {}
    for c in trap:
        trap_succs[c] = [(s, p) for (s, p) in succ_map[c] if s in trap]

    # Iterative Tarjan's
    idx_counter = [0]
    stack = []
    on_stack = set()
    idx = {}
    low = {}
    sccs = []

    for root in trap:
        if root in idx:
            continue
        work = [(root, 0)]  # (node, neighbor_index)
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
                    # Only keep non-trivial SCCs
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


def find_short_daemon_cycles(trap, succ_map, max_len=30, max_cycles=5):
    """Find short cycles in the trap that the daemon can traverse."""
    if not trap:
        return []

    trap_succs = {}
    for c in trap:
        trap_succs[c] = [(s, p) for (s, p) in succ_map[c] if s in trap]

    cycles = []
    visited_keys = set()

    for start in sorted(trap, key=str)[:200]:
        seen = {start: [start]}
        queue = deque([start])
        found = False
        while queue and not found:
            node = queue.popleft()
            path = seen[node]
            if len(path) > max_len:
                continue
            for (s, p) in trap_succs.get(node, []):
                if s == start and len(path) >= 2:
                    key = frozenset(path)
                    if key not in visited_keys:
                        visited_keys.add(key)
                        cycles.append(list(path))
                        found = True
                        break
                if s not in seen and len(path) < max_len:
                    seen[s] = path + [s]
                    queue.append(s)
        if len(cycles) >= max_cycles:
            break

    return cycles


def analyze_system(name, ms, fs, verbose=True):
    """Full game graph analysis."""
    n = len(ms)
    product = 1
    for m in ms:
        product *= m

    print(f"\n{'='*70}")
    print(f"System: {name}")
    print(f"ms = {ms}, product = {product}, n = {n}")
    print(f"{'='*70}")

    # Verify
    result = verify_system(ms, fs)
    is_valid = result['valid']
    print(f"\nValidity: {'VALID' if is_valid else 'INVALID'}")
    for prop, (ok, info) in result.get('properties', {}).items():
        print(f"  {prop}: {'OK' if ok else 'FAIL'} — {info}")

    # Build game graph
    configs, priv_map, succ_map = build_game_graph(ms, fs)

    # Privilege statistics
    stats = privilege_stats(configs, priv_map)
    print(f"\nPrivilege distribution:")
    for k, v in stats.items():
        pct = 100 * v / len(configs)
        print(f"  {k} privileged: {v} configs ({pct:.1f}%)")

    total_edges = sum(len(succ_map[c]) for c in configs)
    multi_priv = sum(v for k, v in stats.items() if k >= 2)
    dead = stats.get(0, 0)
    print(f"\nTotal configs: {len(configs)}")
    print(f"Total game edges: {total_edges}")
    print(f"Deadlocks (0 priv): {dead} ({100*dead/len(configs):.1f}%)")
    print(f"Multi-privileged (2+): {multi_priv} ({100*multi_priv/len(configs):.1f}%)")

    # Find good set
    good_set = set()
    cycle = []
    if is_valid:
        good_set = result['good_configs']
        cycle = result['cycle']
        print(f"\nGood configs: {len(good_set)} (cycle length {result['cycle_length']})")
    else:
        # Find best candidate good cycle
        single_priv = {c for c in configs if len(priv_map[c]) == 1}
        print(f"\nSingle-privilege configs: {len(single_priv)}")

        succ_det = {}
        for c in single_priv:
            p = priv_map[c][0]
            s = apply_move(c, p, fs, ms)
            succ_det[c] = s

        good_candidates = set(single_priv)
        changed = True
        while changed:
            changed = False
            to_remove = {c for c in good_candidates if succ_det[c] not in good_candidates}
            if to_remove:
                good_candidates -= to_remove
                changed = True

        # Find cycles
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

        if cycles_found:
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
            # Check fairness
            procs_in_cycle = set()
            for c in cycle:
                _, p = succ_det[c], priv_map[c][0]
                procs_in_cycle.add(p)
            fair = procs_in_cycle == set(range(n))
            print(f"Best good cycle: length {len(cycle)}, good set: {len(good_set)}, fair: {fair}")
            print(f"  All candidate cycles: {[len(c) for c in cycles_found]}")
        else:
            print("No good cycle found!")

    if not good_set:
        return {
            'name': name, 'ms': ms, 'product': product, 'valid': is_valid,
            'total_configs': len(configs), 'privilege_stats': stats,
            'good_set_size': 0, 'attractor_size': 0, 'trap_size': len(configs),
            'multi_priv': multi_priv, 'dead': dead,
        }

    # Attractor and trap
    attractor, trap = compute_attractor(configs, priv_map, succ_map, good_set)

    print(f"\n--- Attractor / Trap Analysis ---")
    print(f"Good set:   {len(good_set)} configs")
    print(f"Attractor:  {len(attractor)} configs ({100*len(attractor)/len(configs):.1f}%)")
    print(f"Trap:       {len(trap)} configs ({100*len(trap)/len(configs):.1f}%)")

    # Privilege distribution in trap and attractor (non-good)
    attractor_non_good = attractor - good_set
    if attractor_non_good:
        attr_priv = defaultdict(int)
        for c in attractor_non_good:
            attr_priv[len(priv_map[c])] += 1
        print(f"\nAttractor (non-good) privilege distribution:")
        for k, v in sorted(attr_priv.items()):
            print(f"  {k} privileged: {v} configs")

    if trap:
        trap_priv = defaultdict(int)
        for c in trap:
            trap_priv[len(priv_map[c])] += 1
        print(f"\nTrap privilege distribution:")
        for k, v in sorted(trap_priv.items()):
            print(f"  {k} privileged: {v} configs")

        # SCCs in trap
        sccs = find_trap_sccs(trap, succ_map)
        print(f"\nTrap SCCs (non-trivial): {len(sccs)}")
        total_scc = 0
        for i, scc in enumerate(sccs[:10]):
            print(f"  SCC {i}: {len(scc)} configs")
            total_scc += len(scc)
        if len(sccs) > 10:
            total_scc += sum(len(s) for s in sccs[10:])
        print(f"Total configs in trap SCCs: {total_scc}")
        print(f"Trap configs NOT in any SCC: {len(trap) - total_scc}")

        # Short daemon cycles
        short_cycs = find_short_daemon_cycles(trap, succ_map, max_len=25, max_cycles=3)
        if short_cycs:
            print(f"\nSample daemon-winning cycles:")
            for i, cyc in enumerate(short_cycs):
                movers = []
                for j in range(len(cyc)):
                    c_cur = cyc[j]
                    c_next = cyc[(j+1) % len(cyc)]
                    for (s, p) in succ_map[c_cur]:
                        if s == c_next:
                            movers.append(p)
                            break
                print(f"  Cycle {i}: length {len(cyc)}, movers={movers}")
                if len(cyc) <= 12:
                    for j, c in enumerate(cyc):
                        print(f"    {c} priv={priv_map[c]} -> mover={movers[j] if j < len(movers) else '?'}")
    else:
        print("\nTrap is EMPTY — system fully converges under any daemon!")

    return {
        'name': name, 'ms': ms, 'product': product, 'valid': is_valid,
        'total_configs': len(configs), 'privilege_stats': stats,
        'good_set_size': len(good_set), 'attractor_size': len(attractor),
        'trap_size': len(trap), 'multi_priv': multi_priv, 'dead': dead,
    }


# ============================================================
# Known valid system builders
# ============================================================

def get_sol3(n):
    """Dijkstra's Solution 3: ms=(3,...,3), product=3^n."""
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
    """Dijkstra's Solution 1: ms=(K,...,K), product=K^n."""
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


def get_clb_system(n):
    """
    CLB construction: ms=(2,3,...,3,2), product=4*3^(n-2).
    From clb_witness_8748.py / CUP-2 universal rules.
    """
    ms = [2] + [3]*(n-2) + [2]

    # Build using the CUP-2 tables
    T_low = {}
    for L in range(2):
        for S in range(2):
            for R in range(3):
                # P0 (binary bottom): fires when L==S
                if L == S:
                    T_low[(L,S,R)] = (S + 1) % 2
                else:
                    T_low[(L,S,R)] = S

    T_high = {}
    for L in range(3):
        for S in range(2):
            for R in range(2):
                # P_{n-1} (binary top): fires when L!=S
                if L != S:
                    T_high[(L,S,R)] = L % 2
                else:
                    T_high[(L,S,R)] = S

    T_mid = {}
    for L in range(3):
        for S in range(3):
            for R in range(3):
                if L != S:
                    T_mid[(L,S,R)] = L
                else:
                    T_mid[(L,S,R)] = S

    T_low_adj = dict(T_mid)  # same as mid for ternary
    T_high_adj = dict(T_mid)

    # Adjust: P0 sees L from P_{n-1} (binary, range 2) and R from P1 (ternary, range 3)
    # Actually let me just use Sol1-style for the endpoints
    # Sol1: P0 fires if L==S, moves to (S+1)%m. Others fire if L!=S, move to L.
    # This IS valid for (K,...,K) with K>=n+1, but for mixed ms we need something else.

    # Let me use the actual CUP-2 tables from the paper.
    # Actually, the simplest known valid mixed system is just Sol1 with K=n+1
    # For sub-threshold analysis, I'll create invalid systems by modifying valid ones.

    # Fall back to Sol1 with appropriate K
    return get_sol1(n, n+1)


def make_broken_system(ms):
    """
    Create a system that is INTENTIONALLY invalid (sub-threshold product).
    Uses Sol1-like rules but with small state counts.
    P0: if L==S, S' = (S+1) % m0
    Others: if L!=S, S' = L % mi (mod to fit)
    """
    n = len(ms)

    def make_f0(m0, mL):
        def f(L, S, R):
            if L == S:
                return (S + 1) % m0
            return S
        return f

    def make_fi(mi, mL):
        def f(L, S, R):
            if L != S:
                return L % mi
            return S
        return f

    fs = [make_f0(ms[0], ms[-1])]
    for i in range(1, n):
        fs.append(make_fi(ms[i], ms[i-1]))
    return ms, fs


def make_generalized_sol1(ms):
    """
    Generalized Solution 1: P0 increments when L==S, others copy L (mod mi).
    Works when all mi are the same and >= n+1. Breaks for mixed/small.
    """
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


# ============================================================
# Main
# ============================================================

if __name__ == '__main__':
    results = []

    # --- VALID SYSTEMS ---

    # Sol3 n=5: ms=(3,3,3,3,3), product=243
    ms, fs = get_sol3(5)
    r = analyze_system("Sol3 n=5", ms, fs)
    results.append(r)

    # Sol1 n=5 K=6: ms=(6,...,6), product=7776
    ms, fs = get_sol1(5, 6)
    r = analyze_system("Sol1 n=5 K=6", ms, fs)
    results.append(r)

    # Sol3 n=4: ms=(3,3,3,3), product=81
    ms, fs = get_sol3(4)
    r = analyze_system("Sol3 n=4", ms, fs)
    results.append(r)

    # Sol1 n=4 K=5: ms=(5,...,5), product=625
    ms, fs = get_sol1(4, 5)
    r = analyze_system("Sol1 n=4 K=5", ms, fs)
    results.append(r)

    # --- INVALID SYSTEMS (sub-threshold) ---

    # Generalized Sol1 with ms=(2,2,2,3,3), product=72
    ms, fs = make_generalized_sol1([2, 2, 2, 3, 3])
    r = analyze_system("GenSol1 (2,2,2,3,3) p=72", ms, fs)
    results.append(r)

    # Generalized Sol1 with ms=(2,2,2,3,4), product=96 (at M_5 threshold)
    ms, fs = make_generalized_sol1([2, 2, 2, 3, 4])
    r = analyze_system("GenSol1 (2,2,2,3,4) p=96", ms, fs)
    results.append(r)

    # Broken system ms=(2,2,2,2,3), product=48
    ms, fs = make_broken_system([2, 2, 2, 2, 3])
    r = analyze_system("Broken (2,2,2,2,3) p=48", ms, fs)
    results.append(r)

    # Generalized Sol1 with ms=(3,3,3,3,3) (same as Sol3 ms but different rules)
    ms, fs = make_generalized_sol1([3, 3, 3, 3, 3])
    r = analyze_system("GenSol1 (3,3,3,3,3) p=243", ms, fs)
    results.append(r)

    # Sol1 n=5 K=4: ms=(4,4,4,4,4), product=1024
    ms, fs = get_sol1(5, 4)
    r = analyze_system("Sol1 n=5 K=4", ms, fs)
    results.append(r)

    # Sol1 n=5 K=3: ms=(3,3,3,3,3), product=243 (INVALID for Sol1 since K<n+1=6)
    ms, fs = get_sol1(5, 3)
    r = analyze_system("Sol1 n=5 K=3 (sub-threshold)", ms, fs)
    results.append(r)

    # Sol3 n=3: ms=(3,3,3), product=27
    ms, fs = get_sol3(3)
    r = analyze_system("Sol3 n=3", ms, fs)
    results.append(r)

    # Sol1 n=3 K=3: ms=(3,3,3) — borderline (K=n, need K>=n+1?)
    ms, fs = get_sol1(3, 3)
    r = analyze_system("Sol1 n=3 K=3", ms, fs)
    results.append(r)

    # ============================================================
    # Summary
    # ============================================================
    print("\n" + "="*80)
    print("SUMMARY COMPARISON")
    print("="*80)
    header = f"{'System':<35} {'Prod':>5} {'Valid':>6} {'Dead':>5} {'Good':>5} {'Attr':>6} {'Trap':>6} {'Multi%':>7}"
    print(header)
    print("-" * len(header))
    for r in results:
        if r is None:
            continue
        mp = 100 * r['multi_priv'] / r['total_configs'] if r['total_configs'] > 0 else 0
        print(f"{r['name']:<35} {r['product']:>5} {'YES' if r['valid'] else 'NO':>6} "
              f"{r['dead']:>5} {r['good_set_size']:>5} {r['attractor_size']:>6} "
              f"{r['trap_size']:>6} {mp:>6.1f}%")

    print("\n" + "="*80)
    print("KEY OBSERVATIONS")
    print("="*80)

    valid_rs = [r for r in results if r and r['valid']]
    invalid_rs = [r for r in results if r and not r['valid']]

    if valid_rs:
        print("\nValid systems:")
        for r in valid_rs:
            mp = 100 * r['multi_priv'] / r['total_configs']
            print(f"  {r['name']}: dead={r['dead']}, multi-priv={mp:.1f}%, "
                  f"trap={r['trap_size']} ({100*r['trap_size']/r['total_configs']:.1f}%)")

    if invalid_rs:
        print("\nInvalid systems:")
        for r in invalid_rs:
            mp = 100 * r['multi_priv'] / r['total_configs']
            print(f"  {r['name']}: dead={r['dead']}, multi-priv={mp:.1f}%, "
                  f"trap={r['trap_size']} ({100*r['trap_size']/r['total_configs']:.1f}%)")
