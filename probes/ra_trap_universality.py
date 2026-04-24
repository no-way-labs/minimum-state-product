#!/usr/bin/env python3
"""
RA: Trap SCC Universality Tests

Tests whether the privilege-determined trap SCC is universal across:
1. Different transition functions (inc, dec, random)
2. Different state vectors (mixed, non-consecutive binary)
3. Different n values
4. Above vs below threshold

Key hypothesis: every sub-threshold system with >=3 binary procs has a
privilege-determined trap SCC, independent of transition function.
"""

import itertools
import random
from collections import defaultdict, deque
from math import comb
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from verifier import all_configs, privileged_set, apply_move


# ============================================================
# Infrastructure (from ra_game_graph.py / ra_game_graph4.py)
# ============================================================

def build_game_graph(ms, fs):
    n = len(ms)
    configs = list(all_configs(ms))
    priv_map = {}
    succ_map = {}
    for c in configs:
        priv = privileged_set(c, fs, ms)
        priv_map[c] = priv
        succ_map[c] = [(apply_move(c, p, fs, ms), p) for p in priv]
    return configs, priv_map, succ_map


def get_good_cycle(ms, fs):
    """Find the maximal good set and cycle."""
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


# ============================================================
# Transition function builders
# ============================================================

def make_gensol1(ms):
    """GenSol1: P0 increments when L==S, others copy L (mod mi)."""
    n = len(ms)
    def f0(L, S, R, m=ms[0]):
        return (S + 1) % m if L == S else S
    fs = [f0]
    for i in range(1, n):
        mi = ms[i]
        def fi(L, S, R, m=mi):
            return L % m if L != S else S
        fs.append(fi)
    return fs


def make_decsol1(ms):
    """DecSol1: P0 decrements when L==S, others copy L (mod mi)."""
    n = len(ms)
    def f0(L, S, R, m=ms[0]):
        return (S - 1) % m if L == S else S
    fs = [f0]
    for i in range(1, n):
        mi = ms[i]
        def fi(L, S, R, m=mi):
            return L % m if L != S else S
        fs.append(fi)
    return fs


def make_random_transition(ms, seed=None):
    """Random transition: each proc has a random table, but privilege = (fi != S)."""
    rng = random.Random(seed)
    n = len(ms)
    fs = []
    for i in range(n):
        mi = ms[i]
        mL = ms[(i-1) % n]
        mR = ms[(i+1) % n]
        # Build random table
        table = {}
        for L in range(mL):
            for S in range(mi):
                for R in range(mR):
                    # Decide privilege: for P0 use L==S, for others L!=S
                    if i == 0:
                        is_priv = (L == S)
                    else:
                        is_priv = (L != S)
                    if is_priv:
                        # Must change state (privileged)
                        options = [v for v in range(mi) if v != S]
                        if options:
                            table[(L, S, R)] = rng.choice(options)
                        else:
                            table[(L, S, R)] = S  # can't change if mi=1
                    else:
                        table[(L, S, R)] = S  # not privileged
        def make_f(tab):
            def f(L, S, R):
                return tab[(L, S, R)]
            return f
        fs.append(make_f(table))
    return fs


def make_random_privilege_transition(ms, seed=None):
    """Random transition with RANDOM privilege structure too."""
    rng = random.Random(seed)
    n = len(ms)
    fs = []
    for i in range(n):
        mi = ms[i]
        mL = ms[(i-1) % n]
        mR = ms[(i+1) % n]
        table = {}
        for L in range(mL):
            for S in range(mi):
                for R in range(mR):
                    # Random: sometimes privileged, sometimes not
                    if rng.random() < 0.3:  # 30% chance of privilege
                        options = [v for v in range(mi) if v != S]
                        if options:
                            table[(L, S, R)] = rng.choice(options)
                        else:
                            table[(L, S, R)] = S
                    else:
                        table[(L, S, R)] = S
        def make_f(tab):
            def f(L, S, R):
                return tab[(L, S, R)]
            return f
        fs.append(make_f(table))
    return fs


def make_sol1_privilege_random_target(ms, seed=None):
    """Sol1-like privilege structure (P0: L==S, others: L!=S) but RANDOM target values."""
    rng = random.Random(seed)
    n = len(ms)
    fs = []
    for i in range(n):
        mi = ms[i]
        mL = ms[(i-1) % n]
        mR = ms[(i+1) % n]
        table = {}
        for L in range(mL):
            for S in range(mi):
                for R in range(mR):
                    if i == 0:
                        is_priv = (L == S)
                    else:
                        is_priv = (L != S)
                    if is_priv:
                        options = [v for v in range(mi) if v != S]
                        table[(L, S, R)] = rng.choice(options) if options else S
                    else:
                        table[(L, S, R)] = S
        def make_f(tab):
            def f(L, S, R):
                return tab[(L, S, R)]
            return f
        fs.append(make_f(table))
    return fs


# ============================================================
# Analysis helper
# ============================================================

def analyze_trap(ms, fs, label="", verbose=False):
    """Full trap analysis. Returns dict with key metrics."""
    n = len(ms)
    product = 1
    for m in ms:
        product *= m

    configs, priv_map, succ_map = build_game_graph(ms, fs)
    good_set, cycle = get_good_cycle(ms, fs)

    if not good_set:
        return {
            'label': label, 'ms': ms, 'n': n, 'product': product,
            'good_size': 0, 'trap_size': product,
            'scc_sizes': [], 'scc_total': 0, 'scc_count': 0,
            'scc_priv_dist': {}, 'binary_subspace': False,
            'has_good_cycle': False, 'scc_configs': set(),
            'priv_map': {},
        }

    trap = compute_trap(configs, priv_map, succ_map, good_set)
    sccs = find_trap_sccs(trap, succ_map)

    scc_sizes = sorted([len(s) for s in sccs], reverse=True)
    scc_total = sum(scc_sizes)

    # Privilege distribution in largest SCC
    scc_priv_dist = {}
    scc_configs = set()
    if sccs:
        largest = max(sccs, key=len)
        scc_configs = set(largest)
        for c in largest:
            np = len(priv_map[c])
            scc_priv_dist[np] = scc_priv_dist.get(np, 0) + 1

    # Check binary subspace: do all SCC configs have values in {0, 1} at binary procs?
    binary_procs = [i for i in range(n) if ms[i] == 2]
    non_binary = [i for i in range(n) if ms[i] > 2]
    in_binary_subspace = True
    for c in scc_configs:
        for i in non_binary:
            if c[i] > 1:
                in_binary_subspace = False
                break
        if not in_binary_subspace:
            break

    # Binary projection analysis
    binary_projection = None
    if scc_configs and non_binary:
        projections = set()
        for c in scc_configs:
            proj = tuple(c[i] for i in non_binary)
            projections.add(proj)
        if all(all(v <= 1 for v in p) for p in projections):
            binary_projection = "all <=1"
        else:
            binary_projection = f"{len(projections)} distinct projections"

    result = {
        'label': label, 'ms': ms, 'n': n, 'product': product,
        'good_size': len(good_set), 'cycle_len': len(cycle),
        'trap_size': len(trap),
        'scc_count': len(sccs), 'scc_sizes': scc_sizes, 'scc_total': scc_total,
        'scc_priv_dist': scc_priv_dist,
        'in_binary_subspace': in_binary_subspace,
        'binary_projection': binary_projection,
        'has_good_cycle': len(cycle) > 0,
        'scc_configs': scc_configs,
        'priv_map': priv_map,
    }

    return result


def print_result(r, show_formula=True):
    """Print analysis result."""
    n = r['n']
    ms = r['ms']
    B = sum(1 for m in ms if m == 2)
    predicted = 2 * comb(n, 3) if B == n else 2 * comb(B, 3) if B >= 3 else 0

    print(f"  ms={ms}, product={r['product']}, n={n}, B={B}")
    print(f"  Good: {r['good_size']}, cycle={r.get('cycle_len', '?')}")
    print(f"  Trap: {r['trap_size']}, SCCs: {r.get('scc_count', 0)}")
    if r['scc_sizes']:
        print(f"  SCC sizes: {r['scc_sizes']}")
    print(f"  Largest SCC: {r['scc_sizes'][0] if r['scc_sizes'] else 0}")
    if r['scc_priv_dist']:
        print(f"  SCC privilege dist: {dict(sorted(r['scc_priv_dist'].items()))}")
    print(f"  In binary subspace: {r.get('in_binary_subspace', 'N/A')}")
    if r.get('binary_projection'):
        print(f"  Non-binary projection: {r['binary_projection']}")
    if show_formula:
        actual = r['scc_sizes'][0] if r['scc_sizes'] else 0
        print(f"  Formula 2*C(B,3)={predicted} vs actual={actual}: {'MATCH' if predicted == actual else 'MISMATCH'}")
        # Also test 2*C(n,3)
        predicted_n = 2 * comb(n, 3)
        print(f"  Formula 2*C(n,3)={predicted_n} vs actual={actual}: {'MATCH' if predicted_n == actual else 'MISMATCH'}")


# ============================================================
# TESTS
# ============================================================

if __name__ == '__main__':

    # ===========================================================
    # TEST 1: Different transition functions at n=5, ms=(2,2,2,3,3)
    # ===========================================================
    print("=" * 70)
    print("TEST 1: TRANSITION FUNCTION INDEPENDENCE")
    print("  ms=(2,2,2,3,3), product=72, n=5")
    print("=" * 70)

    ms_test = [2, 2, 2, 3, 3]

    # GenSol1 (incrementing)
    fs = make_gensol1(ms_test)
    r1 = analyze_trap(ms_test, fs, "GenSol1-inc")
    print(f"\n[GenSol1 incrementing]")
    print_result(r1)

    # DecSol1 (decrementing)
    fs = make_decsol1(ms_test)
    r2 = analyze_trap(ms_test, fs, "DecSol1-dec")
    print(f"\n[DecSol1 decrementing]")
    print_result(r2)

    # Random targets (same privilege structure)
    scc_sizes_random = []
    print(f"\n[Random target (Sol1-privilege), 20 trials]")
    for seed in range(20):
        fs = make_sol1_privilege_random_target(ms_test, seed=seed)
        r = analyze_trap(ms_test, fs)
        largest = r['scc_sizes'][0] if r['scc_sizes'] else 0
        scc_sizes_random.append(largest)
    print(f"  SCC sizes across 20 random seeds: {sorted(set(scc_sizes_random))}")
    print(f"  All same? {len(set(scc_sizes_random)) == 1}")
    print(f"  Min={min(scc_sizes_random)}, Max={max(scc_sizes_random)}")

    # Check if SCC configs are identical
    print(f"\n[Checking if SCC CONFIG SETS are identical across transitions]")
    ref_scc = r1['scc_configs']
    all_same_configs = True
    for seed in range(10):
        fs = make_sol1_privilege_random_target(ms_test, seed=seed)
        r = analyze_trap(ms_test, fs, verbose=True)
        if r['scc_configs'] != ref_scc:
            all_same_configs = False
            diff = ref_scc.symmetric_difference(r['scc_configs'])
            print(f"  Seed {seed}: DIFFERENT! Symmetric diff = {len(diff)}")
            break
    if all_same_configs:
        print(f"  All 10 seeds: IDENTICAL SCC config sets = {len(ref_scc)} configs")

    # ===========================================================
    # TEST 2: n=9, ms=[2,3,3,2,3,3,2,3,3] (all-odd-gap)
    # ===========================================================
    print("\n" + "=" * 70)
    print("TEST 2: ALL-ODD-GAP FAMILY (n=9)")
    print("  ms=[2,3,3,2,3,3,2,3,3], product=5832")
    print("=" * 70)

    ms_9 = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    product_9 = 1
    for m in ms_9:
        product_9 *= m
    threshold_9 = 4 * (3 ** 7)  # 8748
    print(f"  Product={product_9}, threshold=4*3^7={threshold_9}")
    print(f"  Sub-threshold: {product_9 < threshold_9}")

    fs = make_gensol1(ms_9)
    r9 = analyze_trap(ms_9, fs, "n=9 all-odd-gap", verbose=True)
    print(f"\n[GenSol1]")
    print_result(r9)

    B9 = sum(1 for m in ms_9 if m == 2)
    print(f"\n  B={B9} binary procs, 2*C(B,3)={2*comb(B9,3)}")
    print(f"  2*C(9,3)={2*comb(9,3)}")

    # ===========================================================
    # TEST 3: Mixed state vectors at n=5
    # ===========================================================
    print("\n" + "=" * 70)
    print("TEST 3: MIXED STATE VECTORS (n=5)")
    print("=" * 70)

    test_cases = [
        ([2, 2, 2, 3, 3], "3 binary, 2 ternary, p=72"),
        ([2, 2, 2, 3, 4], "3 binary, 1 ternary, 1 quaternary, p=96 (threshold!)"),
        ([2, 2, 2, 2, 3], "4 binary, 1 ternary, p=48"),
        ([2, 3, 2, 3, 2], "3 non-consecutive binary, p=72"),
        ([2, 2, 3, 2, 3], "3 binary (0,1,3), p=72"),
        ([2, 2, 2, 2, 2], "5 binary, p=32"),
        ([2, 2, 2, 4, 4], "3 binary, 2 quaternary, p=128"),
    ]

    for ms_t, desc in test_cases:
        product = 1
        for m in ms_t:
            product *= m
        threshold = 4 * (3 ** 3)  # 108 for n=5
        print(f"\n--- {desc} ---")
        print(f"  Product={product}, threshold=4*3^3={threshold}, sub={product < threshold}")
        fs = make_gensol1(ms_t)
        r = analyze_trap(ms_t, fs, desc)
        print_result(r)

    # ===========================================================
    # TEST 4: Binary subspace hypothesis
    # ===========================================================
    print("\n" + "=" * 70)
    print("TEST 4: BINARY SUBSPACE HYPOTHESIS")
    print("=" * 70)

    for ms_t, desc in test_cases:
        product = 1
        for m in ms_t:
            product *= m
        fs = make_gensol1(ms_t)
        r = analyze_trap(ms_t, fs, desc, verbose=True)
        if not r['scc_configs']:
            print(f"\n  {desc}: NO SCC (trap empty or no non-trivial SCC)")
            continue

        n = len(ms_t)
        non_binary = [i for i in range(n) if ms_t[i] > 2]
        print(f"\n  {desc}:")
        print(f"    Non-binary procs: {non_binary}")

        # Check: at non-binary positions, what values appear in SCC?
        for i in non_binary:
            vals = set(c[i] for c in r['scc_configs'])
            print(f"    Proc {i} (m={ms_t[i]}): values in SCC = {sorted(vals)}")

        # Binary projection
        binary_procs = [i for i in range(n) if ms_t[i] == 2]
        if non_binary:
            non_binary_projections = set()
            for c in r['scc_configs']:
                proj = tuple(c[i] for i in non_binary)
                non_binary_projections.add(proj)
            print(f"    Non-binary projections: {len(non_binary_projections)} distinct")
            if len(non_binary_projections) <= 20:
                for p in sorted(non_binary_projections):
                    count = sum(1 for c in r['scc_configs'] if tuple(c[i] for i in non_binary) == p)
                    print(f"      {p}: {count} configs")

    # ===========================================================
    # TEST 5: SCC size formula
    # ===========================================================
    print("\n" + "=" * 70)
    print("TEST 5: SCC SIZE FORMULA")
    print("=" * 70)

    print("\nTesting 2*C(B,3) where B = number of binary procs:")
    formula_results = []
    for ms_t, desc in test_cases:
        product = 1
        for m in ms_t:
            product *= m
        n = len(ms_t)
        B = sum(1 for m in ms_t if m == 2)
        threshold = 4 * (3 ** (n-2))

        fs = make_gensol1(ms_t)
        r = analyze_trap(ms_t, fs, desc)
        actual = r['scc_sizes'][0] if r['scc_sizes'] else 0

        predicted_B = 2 * comb(B, 3)
        predicted_n = 2 * comb(n, 3)

        match_B = actual == predicted_B
        match_n = actual == predicted_n

        formula_results.append((ms_t, B, actual, predicted_B, predicted_n, match_B, match_n, product < threshold))

        sub = "SUB" if product < threshold else "AT/ABOVE"
        print(f"  ms={ms_t} B={B} [{sub}]: actual={actual}, 2*C(B,3)={predicted_B} {'OK' if match_B else 'FAIL'}, 2*C(n,3)={predicted_n} {'OK' if match_n else 'FAIL'}")

    # Also test n=6
    print("\n  --- n=6 ---")
    for ms_t in [[2,2,2,3,3,3], [2,2,2,2,3,3], [2,3,2,3,2,3]]:
        n = len(ms_t)
        B = sum(1 for m in ms_t if m == 2)
        product = 1
        for m in ms_t:
            product *= m
        threshold = 4 * (3 ** (n-2))

        fs = make_gensol1(ms_t)
        r = analyze_trap(ms_t, fs)
        actual = r['scc_sizes'][0] if r['scc_sizes'] else 0

        predicted_B = 2 * comb(B, 3)
        predicted_n = 2 * comb(n, 3)

        sub = "SUB" if product < threshold else "AT/ABOVE"
        print(f"  ms={ms_t} B={B} [{sub}]: actual={actual}, 2*C(B,3)={predicted_B} {'OK' if actual == predicted_B else 'FAIL'}, 2*C(n,3)={predicted_n} {'OK' if actual == predicted_n else 'FAIL'}")

    # n=7
    print("\n  --- n=7 ---")
    for ms_t in [[2,2,2,3,3,3,3], [2,2,2,2,3,3,3], [2,2,2,2,2,3,3]]:
        n = len(ms_t)
        B = sum(1 for m in ms_t if m == 2)
        product = 1
        for m in ms_t:
            product *= m
        threshold = 4 * (3 ** (n-2))

        fs = make_gensol1(ms_t)
        r = analyze_trap(ms_t, fs)
        actual = r['scc_sizes'][0] if r['scc_sizes'] else 0

        predicted_B = 2 * comb(B, 3)
        predicted_n = 2 * comb(n, 3)

        sub = "SUB" if product < threshold else "AT/ABOVE"
        print(f"  ms={ms_t} B={B} [{sub}]: actual={actual}, 2*C(B,3)={predicted_B} {'OK' if actual == predicted_B else 'FAIL'}, 2*C(n,3)={predicted_n} {'OK' if actual == predicted_n else 'FAIL'}")

    # ===========================================================
    # TEST 6: Transition function independence (multiple multisets)
    # ===========================================================
    print("\n" + "=" * 70)
    print("TEST 6: TRANSITION FUNCTION INDEPENDENCE (MULTIPLE MULTISETS)")
    print("=" * 70)

    tf_test_cases = [
        [2, 2, 2, 3, 3],
        [2, 2, 2, 2, 3],
        [2, 3, 2, 3, 2],
        [2, 2, 2, 3, 3, 3],
    ]

    for ms_t in tf_test_cases:
        n = len(ms_t)
        product = 1
        for m in ms_t:
            product *= m
        print(f"\n  ms={ms_t}, product={product}")

        results_tf = []
        scc_config_sets = []

        # GenSol1
        fs = make_gensol1(ms_t)
        r = analyze_trap(ms_t, fs, verbose=True)
        results_tf.append(("GenSol1", r['scc_sizes'][0] if r['scc_sizes'] else 0))
        scc_config_sets.append(r['scc_configs'])

        # DecSol1
        fs = make_decsol1(ms_t)
        r = analyze_trap(ms_t, fs, verbose=True)
        results_tf.append(("DecSol1", r['scc_sizes'][0] if r['scc_sizes'] else 0))
        scc_config_sets.append(r['scc_configs'])

        # 5 random
        for seed in range(5):
            fs = make_sol1_privilege_random_target(ms_t, seed=seed+100)
            r = analyze_trap(ms_t, fs, verbose=True)
            results_tf.append((f"Rand-{seed}", r['scc_sizes'][0] if r['scc_sizes'] else 0))
            scc_config_sets.append(r['scc_configs'])

        sizes = [sz for _, sz in results_tf]
        print(f"    SCC sizes: {results_tf}")
        print(f"    All same size? {len(set(sizes)) == 1}")

        # Check config set identity
        ref = scc_config_sets[0]
        all_identical = all(s == ref for s in scc_config_sets)
        print(f"    All same config set? {all_identical}")

        if not all_identical:
            for i, s in enumerate(scc_config_sets):
                if s != ref:
                    diff = ref.symmetric_difference(s)
                    print(f"      {results_tf[i][0]}: symmetric diff = {len(diff)}")

    # ===========================================================
    # TEST 7: Above threshold comparison
    # ===========================================================
    print("\n" + "=" * 70)
    print("TEST 7: ABOVE THRESHOLD (should have EMPTY trap)")
    print("=" * 70)

    # M_5 = 96: ms=(2,2,2,3,4) is at threshold
    # Build the actual M_5 witness system
    ms_96 = [2, 2, 2, 3, 4]
    print(f"\n  ms={ms_96}, product=96 (M_5 threshold)")

    # Try GenSol1 — this is likely INVALID at threshold
    fs = make_gensol1(ms_96)
    r_96 = analyze_trap(ms_96, fs, "GenSol1 at threshold")
    print(f"  [GenSol1] Trap size: {r_96['trap_size']}, SCC: {r_96['scc_sizes']}")

    # Above threshold: ms=(2,2,2,3,5), product=120
    ms_120 = [2, 2, 2, 3, 5]
    fs = make_gensol1(ms_120)
    r_120 = analyze_trap(ms_120, fs, "GenSol1 above threshold")
    print(f"\n  ms={ms_120}, product=120 (above threshold)")
    print(f"  [GenSol1] Trap size: {r_120['trap_size']}, SCC: {r_120['scc_sizes']}")

    # Way above: ms=(3,3,3,3,3), product=243
    ms_243 = [3, 3, 3, 3, 3]
    fs = make_gensol1(ms_243)
    r_243 = analyze_trap(ms_243, fs, "GenSol1 way above threshold")
    print(f"\n  ms={ms_243}, product=243 (way above threshold)")
    print(f"  [GenSol1] Trap size: {r_243['trap_size']}, SCC: {r_243['scc_sizes']}")
    print(f"  Good: {r_243['good_size']}, has_cycle: {r_243['has_good_cycle']}")

    # ===========================================================
    # TEST 8: Privilege structure deep dive
    # ===========================================================
    print("\n" + "=" * 70)
    print("TEST 8: PRIVILEGE STRUCTURE ANALYSIS")
    print("  Is the SCC determined by privilege sets alone?")
    print("=" * 70)

    ms_t = [2, 2, 2, 3, 3]
    fs_inc = make_gensol1(ms_t)
    fs_dec = make_decsol1(ms_t)

    configs_inc, priv_map_inc, _ = build_game_graph(ms_t, fs_inc)
    configs_dec, priv_map_dec, _ = build_game_graph(ms_t, fs_dec)

    # Check: do inc and dec have the SAME privilege sets everywhere?
    same_priv = True
    for c in configs_inc:
        if set(priv_map_inc[c]) != set(priv_map_dec[c]):
            same_priv = False
            print(f"  DIFFERENT privilege at {c}: inc={priv_map_inc[c]} dec={priv_map_dec[c]}")
            break
    print(f"\n  Same privilege structure (inc vs dec)? {same_priv}")

    # Check random transition with same privilege structure
    fs_rand = make_sol1_privilege_random_target(ms_t, seed=42)
    _, priv_map_rand, _ = build_game_graph(ms_t, fs_rand)
    same_priv_rand = all(set(priv_map_inc[c]) == set(priv_map_rand[c]) for c in configs_inc)
    print(f"  Same privilege structure (inc vs random-target)? {same_priv_rand}")

    # Now check: for DIFFERENT privilege structures, does the SCC change?
    print(f"\n  Testing with DIFFERENT privilege structures:")
    fs_diff = make_random_privilege_transition(ms_t, seed=42)
    _, priv_map_diff, _ = build_game_graph(ms_t, fs_diff)
    same_priv_diff = all(set(priv_map_inc[c]) == set(priv_map_diff[c]) for c in configs_inc)
    print(f"  Same privilege structure? {same_priv_diff}")
    r_diff = analyze_trap(ms_t, fs_diff, "random-privilege")
    print(f"  SCC sizes: {r_diff['scc_sizes']}")
    print(f"  Trap: {r_diff['trap_size']}, Good: {r_diff['good_size']}")

    # Try several random-privilege to see what happens
    print(f"\n  Random privilege structures (10 trials):")
    for seed in range(10):
        fs_rp = make_random_privilege_transition(ms_t, seed=seed+200)
        r_rp = analyze_trap(ms_t, fs_rp)
        scc_sz = r_rp['scc_sizes'][0] if r_rp['scc_sizes'] else 0
        print(f"    seed={seed+200}: good={r_rp['good_size']}, trap={r_rp['trap_size']}, scc={scc_sz}")

    # ===========================================================
    # SUMMARY
    # ===========================================================
    print("\n" + "=" * 70)
    print("GRAND SUMMARY")
    print("=" * 70)
    print("""
Key questions answered:
1. Is the trap SCC transition-function-independent (given same privilege structure)?
2. Does 2*C(B,3) or 2*C(n,3) predict SCC size?
3. Does the SCC live in the binary subspace?
4. Does every sub-threshold system with >=3 binary have a trap?
5. Is the trap empty above threshold?
""")
