#!/usr/bin/env python3
"""
RA14: Existential Non-Good Successor Investigation

Parts 1-6: Verify existential claim, find counterexamples, analyze bad cycles,
           focus on stuttered sweep family.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, deque
from verifier import verify_system, privileged_set, apply_move


# ── System builders ──

def build_sol3(n):
    ms = [3] * n
    def f_bottom(L, S, R):
        if (S + 1) % 3 == R: return (S - 1) % 3
        return S
    def f_top(L, S, R):
        if L == R and (L + 1) % 3 != S: return (L + 1) % 3
        return S
    def f_middle(L, S, R):
        if (S + 1) % 3 == L: return L
        if (S + 1) % 3 == R: return R
        return S
    fs = [f_bottom] + [f_middle] * (n - 2) + [f_top]
    return ms, fs


def build_cup2(n):
    ms = [2] + [3] * (n - 2) + [2]
    T_bot = {
        (0,0,0):1, (0,0,1):1, (0,0,2):0,
        (0,1,0):1, (0,1,1):1, (0,1,2):1,
        (1,0,0):0, (1,0,1):1, (1,0,2):0,
        (1,1,0):0, (1,1,1):1, (1,1,2):0,
    }
    T_low = {
        (0,0,0):0, (0,0,1):0, (0,0,2):0,
        (0,1,0):0, (0,1,1):1, (0,1,2):0,
        (0,2,0):0, (0,2,1):2, (0,2,2):0,
        (1,0,0):1, (1,0,1):1, (1,0,2):1,
        (1,1,0):1, (1,1,1):1, (1,1,2):2,
        (1,2,0):0, (1,2,1):1, (1,2,2):2,
    }
    T_mid = {
        (0,0,0):0, (0,0,1):0, (0,0,2):0,
        (0,1,0):0, (0,1,1):1, (0,1,2):0,
        (0,2,0):0, (0,2,1):2, (0,2,2):0,
        (1,0,0):1, (1,0,1):1, (1,0,2):1,
        (1,1,0):1, (1,1,1):1, (1,1,2):2,
        (1,2,0):0, (1,2,1):1, (1,2,2):2,
        (2,0,0):0, (2,0,1):0, (2,0,2):2,
        (2,1,0):1, (2,1,1):0, (2,1,2):2,
        (2,2,0):0, (2,2,1):2, (2,2,2):2,
    }
    T_high = {
        (0,0,0):0, (0,0,1):0,
        (0,1,0):0, (0,1,1):0,
        (0,2,0):0, (0,2,1):0,
        (1,0,0):1, (1,0,1):1,
        (1,1,0):1, (1,1,1):2,
        (1,2,0):0, (1,2,1):2,
        (2,0,0):0, (2,0,1):2,
        (2,1,0):0, (2,1,1):2,
        (2,2,0):2, (2,2,1):2,
    }
    T_top = {
        (0,0,0):0, (0,0,1):0,
        (0,1,0):0, (0,1,1):0,
        (1,0,0):0, (1,0,1):1,
        (1,1,0):1, (1,1,1):1,
        (2,0,0):1, (2,0,1):1,
        (2,1,0):1, (2,1,1):1,
    }
    def get_table(pos):
        if pos == 0: return T_bot
        if pos == 1: return T_low
        if pos == n - 2: return T_high
        if pos == n - 1: return T_top
        return T_mid
    fs = []
    for p in range(n):
        tbl = get_table(p)
        def make_f(t):
            return lambda L, S, R: t[(L, S, R)]
        fs.append(make_f(tbl))
    return ms, fs


def get_good_cycle(ms, fs):
    """Get the good cycle configs and the good set from a valid system."""
    result = verify_system(ms, fs)
    if not result['valid']:
        return None, None
    return result.get('good_configs', None), result


def analyze_system(name, ms, fs):
    """Full analysis of existential non-good successor for a system."""
    n = len(ms)
    result = verify_system(ms, fs)
    if not result['valid']:
        print(f"  {name}: INVALID system")
        return None

    good_set = result['good_configs']
    all_cfgs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_cfgs if c not in good_set]

    # For each non-good config: check existential
    all_to_good = []  # configs where ALL priv procs lead to good
    has_nongood_succ = []  # configs with at least one non-good successor
    stats = {'single_priv': 0, 'multi_priv': 0, 'total_nongood': len(non_good)}

    for c in non_good:
        priv = privileged_set(c, fs, ms)
        if len(priv) == 0:
            # This shouldn't happen in a valid system (liveness)
            print(f"  WARNING: deadlock at {c}")
            continue

        if len(priv) == 1:
            stats['single_priv'] += 1
        else:
            stats['multi_priv'] += 1

        succs_good = []
        succs_nongood = []
        for p in priv:
            s = apply_move(c, p, fs, ms)
            if s in good_set:
                succs_good.append(p)
            else:
                succs_nongood.append(p)

        if len(succs_nongood) == 0:
            all_to_good.append((c, priv, succs_good))
        else:
            has_nongood_succ.append((c, priv, succs_nongood))

    existential_holds = len(all_to_good) == 0

    print(f"  {name}: ms={ms}, |good|={len(good_set)}, |non-good|={len(non_good)}")
    print(f"    single-priv non-good: {stats['single_priv']}, multi-priv: {stats['multi_priv']}")
    print(f"    existential non-good successor: {'HOLDS' if existential_holds else 'FAILS'}")
    print(f"    configs where ALL choices → good: {len(all_to_good)}")

    if all_to_good:
        print(f"    Examples of all-to-good configs:")
        for c, priv, sg in all_to_good[:5]:
            print(f"      {c}, priv={priv}, all → good")

    return {
        'good_set': good_set,
        'all_to_good': all_to_good,
        'has_nongood_succ': has_nongood_succ,
        'stats': stats,
        'existential_holds': existential_holds,
    }


# ══════════════════════════════════════════════════════════════════
# Part 1: Valid systems (Sol3, CUP-2)
# ══════════════════════════════════════════════════════════════════
print("=" * 72)
print("PART 1: Existential Non-Good Successor on Valid Systems")
print("=" * 72)

for n in [5, 7]:
    ms, fs = build_sol3(n)
    analyze_system(f"Sol3 n={n}", ms, fs)

for n in [5, 7]:
    ms, fs = build_cup2(n)
    analyze_system(f"CUP-2 n={n}", ms, fs)


# ══════════════════════════════════════════════════════════════════
# Part 2: Bad cycle analysis in valid systems
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART 2: Bad Cycle Analysis (should be NO bad cycles in valid systems)")
print("=" * 72)

def find_bad_cycles(ms, fs, good_set):
    """Find SCCs in the non-good transition graph."""
    n = len(ms)
    all_cfgs = list(cartesian(*(range(m) for m in ms)))
    non_good = [c for c in all_cfgs if c not in good_set]
    non_good_set = set(non_good)

    # Build adjacency: config → list of non-good successors
    adj = defaultdict(list)
    for c in non_good:
        priv = privileged_set(c, fs, ms)
        for p in priv:
            s = apply_move(c, p, fs, ms)
            if s in non_good_set:
                adj[c].append(s)

    # Tarjan's SCC
    index_counter = [0]
    stack = []
    lowlink = {}
    index = {}
    on_stack = set()
    sccs = []

    def strongconnect(v):
        index[v] = index_counter[0]
        lowlink[v] = index_counter[0]
        index_counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w in adj[v]:
            if w not in index:
                strongconnect(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], index[w])
        if lowlink[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1:
                sccs.append(scc)
            elif len(scc) == 1 and scc[0] in adj[scc[0]]:
                sccs.append(scc)  # self-loop

    # Use iterative Tarjan for large graphs
    for v in non_good:
        if v not in index:
            # Iterative version to avoid recursion limit
            call_stack = [(v, 0)]
            while call_stack:
                node, ni = call_stack[-1]
                if ni == 0:
                    index[node] = index_counter[0]
                    lowlink[node] = index_counter[0]
                    index_counter[0] += 1
                    stack.append(node)
                    on_stack.add(node)
                neighbors = adj[node]
                if ni < len(neighbors):
                    call_stack[-1] = (node, ni + 1)
                    w = neighbors[ni]
                    if w not in index:
                        call_stack.append((w, 0))
                    elif w in on_stack:
                        lowlink[node] = min(lowlink[node], index[w])
                else:
                    if lowlink[node] == index[node]:
                        scc = []
                        while True:
                            w = stack.pop()
                            on_stack.discard(w)
                            scc.append(w)
                            if w == node:
                                break
                        if len(scc) > 1:
                            sccs.append(scc)
                        elif len(scc) == 1 and scc[0] in adj[scc[0]]:
                            sccs.append(scc)
                    call_stack.pop()
                    if call_stack:
                        parent = call_stack[-1][0]
                        lowlink[parent] = min(lowlink[parent], lowlink[node])

    return sccs, adj

for n in [5, 7]:
    ms, fs = build_sol3(n)
    result = verify_system(ms, fs)
    sccs, _ = find_bad_cycles(ms, fs, result['good_configs'])
    print(f"Sol3 n={n}: bad SCCs = {len(sccs)} (expected 0)")

for n in [5, 7]:
    ms, fs = build_cup2(n)
    result = verify_system(ms, fs)
    sccs, _ = find_bad_cycles(ms, fs, result['good_configs'])
    print(f"CUP-2 n={n}: bad SCCs = {len(sccs)} (expected 0)")


# ══════════════════════════════════════════════════════════════════
# Part 3: Stuttered sweep family — bad cycles
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART 3: Stuttered Sweep Family — Bad Cycle Structure")
print("=" * 72)

def enumerate_exact_fc_words(ms, n, target_fc):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    total_len = sum(target_fc[p] for p in range(n))
    results = []
    def dfs(word, fc):
        if len(word) == total_len:
            if abs(word[-1] - word[0]) % n in (1, n-1):
                config = [0]*n
                for p in word:
                    config[p] = (config[p]+1) % ms[p]
                if all(c == 0 for c in config):
                    results.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                remaining = total_len - len(word)
                needed = sum(target_fc[p] - fc[p] for p in range(n))
                if needed <= remaining:
                    dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for p in range(n):
        if target_fc[p] > 0:
            fc = {q: 0 for q in range(n)}
            fc[p] = 1
            dfs([p], fc)
    return results

def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p]+1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]: return None
    if len(set(configs[:ell])) != ell: return None
    return configs[:ell]

def canonicalize_word(word):
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best: best = rot
    return best

def compute_displacement(word, n):
    total = 0
    ell = len(word)
    for i in range(ell):
        diff = (word[(i+1)%ell] - word[i]) % n
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
    return total

def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0: seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0: continue
                seq.append(nv)
                dfs(seq, remaining-1)
                seq.pop()
    dfs([0], k)
    return seqs


def build_sub_threshold_system(ms, n, word, combo):
    """Build a system from a sweep word + state sequence combo.
    Returns (ms, fs, good_set) where fs is a PARTIAL transition function
    (only defined on contexts that appear in the good cycle)."""
    ell = len(word)

    # Compute firing counts
    fc_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        fc_num[s] = pc[word[s]]
        pc[word[s]] += 1

    # Build good cycle configs
    cs = []
    state = [0]*n
    for s in range(ell):
        cs.append(tuple(state))
        p = word[s]
        state[p] = combo[p][fc_num[s]+1]
    good_set = set(cs)

    # Extract mover context → new value mapping
    mcx = defaultdict(dict)
    for s in range(ell):
        p = word[s]
        L = cs[s][(p-1)%n]; S = cs[s][p]; R = cs[s][(p+1)%n]
        mcx[p][(L, S, R)] = combo[p][fc_num[s]+1]

    # Build full transition functions using incrementing as default
    def make_trans(proc, mover_ctx):
        m = ms[proc]
        mL = ms[(proc-1)%n]
        mR = ms[(proc+1)%n]
        tbl = {}
        for L in range(mL):
            for S in range(m):
                for R in range(mR):
                    if (L, S, R) in mover_ctx:
                        tbl[(L, S, R)] = mover_ctx[(L, S, R)]
                    else:
                        tbl[(L, S, R)] = S  # identity = not privileged
        return lambda L, S, R, t=tbl: t[(L, S, R)]

    fs = [make_trans(p, mcx[p]) for p in range(n)]
    return ms, fs, good_set, mcx


# Work at n=5 first (fast), then n=9
print("\n--- n=5 sub-threshold analysis ---")
n = 5
ms_5 = [2, 3, 3, 2, 3]
target_fc = {p: ms_5[p] for p in range(n)}
words = enumerate_exact_fc_words(ms_5, n, target_fc)
seen = set()
unique = []
for w in words:
    canon = canonicalize_word(w)
    if canon not in seen:
        seen.add(canon)
        unique.append(w)
valid_words = []
for w in unique:
    cycle = build_cycle(ms_5, n, w)
    if cycle is not None:
        valid_words.append((w, cycle))
sweeps = [(w, c, compute_displacement(w, n)) for w, c in valid_words if abs(compute_displacement(w, n)) == 2*n]
print(f"n=5: {len(sweeps)} sweep words")

# For each sweep, test first combo
if sweeps:
    w0, cyc0, d0 = sweeps[0]
    combos_per_proc = [enumerate_state_sequences(ms_5[p], ms_5[p]) for p in range(n)]
    total_combos = 1
    for c in combos_per_proc:
        total_combos *= len(c)
    print(f"  Sweep word: {list(w0)}, {total_combos} combos")

    # Test a handful of combos
    tested = 0
    bad_cycle_found = 0
    existential_fails = 0

    import itertools
    combo_iters = list(itertools.product(*combos_per_proc))
    for combo in combo_iters[:min(32, len(combo_iters))]:
        tested += 1
        _, fs, good_set, mcx = build_sub_threshold_system(ms_5, n, w0, combo)

        # Check: does the system have bad cycles?
        all_cfgs = list(cartesian(*(range(m) for m in ms_5)))
        non_good = [c for c in all_cfgs if c not in good_set]
        non_good_set = set(non_good)

        # Build adjacency restricted to non-good
        adj = defaultdict(list)
        for c in non_good:
            priv = privileged_set(c, fs, ms_5)
            for p in priv:
                s = apply_move(c, p, fs, ms_5)
                if s in non_good_set:
                    adj[c].append((s, p))

        # Check for cycle using DFS
        color = {c: 0 for c in non_good}
        has_cycle = False
        for start in non_good:
            if color[start] != 0:
                continue
            stk = [(start, 0)]
            path = []
            while stk:
                node, idx = stk[-1]
                if idx == 0:
                    color[node] = 1  # gray
                    path.append(node)
                nbrs = [s for s, p in adj[node]]
                if idx < len(nbrs):
                    stk[-1] = (node, idx + 1)
                    nxt = nbrs[idx]
                    if color[nxt] == 1:
                        has_cycle = True
                        break
                    if color[nxt] == 0:
                        stk.append((nxt, 0))
                else:
                    color[node] = 2  # black
                    path.pop()
                    stk.pop()
            if has_cycle:
                break

        if has_cycle:
            bad_cycle_found += 1

        # Check existential
        ex_fail = 0
        for c in non_good:
            priv = privileged_set(c, fs, ms_5)
            if len(priv) == 0:
                continue
            all_go_good = True
            for p in priv:
                s = apply_move(c, p, fs, ms_5)
                if s not in good_set:
                    all_go_good = False
                    break
            if all_go_good:
                ex_fail += 1

        if ex_fail > 0:
            existential_fails += 1

    print(f"  Tested {tested} combos: bad cycles in {bad_cycle_found}, existential fails in {existential_fails}")


# ══════════════════════════════════════════════════════════════════
# Part 4 & 5: Deep analysis at n=9 — bad cycle structure
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART 4 & 5: n=9 Stuttered Sweep — Bad Cycle Privilege Structure")
print("=" * 72)

n = 9
ms_9 = [2,3,3,2,3,3,2,3,3]
target_fc = {p: ms_9[p] for p in range(n)}

print("Enumerating sweep words for n=9...")
words9 = enumerate_exact_fc_words(ms_9, n, target_fc)
seen9 = set()
unique9 = []
for w in words9:
    canon = canonicalize_word(w)
    if canon not in seen9:
        seen9.add(canon)
        unique9.append(w)
valid9 = []
for w in unique9:
    cycle = build_cycle(ms_9, n, w)
    if cycle is not None:
        valid9.append((w, cycle))
sweeps9 = [(w, c, compute_displacement(w, n)) for w, c in valid9 if abs(compute_displacement(w, n)) == 2*n]
print(f"n=9: {len(sweeps9)} sweep words")

if sweeps9:
    w0, cyc0, d0 = sweeps9[0]
    combos_per_proc = [enumerate_state_sequences(ms_9[p], ms_9[p]) for p in range(n)]
    combo0 = tuple(c[0] for c in combos_per_proc)
    ell = len(w0)
    print(f"  Sweep word: len={ell}, displacement={d0}")

    _, fs9, good_set9, mcx9 = build_sub_threshold_system(ms_9, n, w0, combo0)

    all_cfgs9 = list(cartesian(*(range(m) for m in ms_9)))
    non_good9 = [c for c in all_cfgs9 if c not in good_set9]
    non_good_set9 = set(non_good9)
    print(f"  |good|={len(good_set9)}, |non-good|={len(non_good9)}, total={len(all_cfgs9)}")

    # Build non-good adjacency with mover info
    adj9 = defaultdict(list)
    for c in non_good9:
        priv = privileged_set(c, fs9, ms_9)
        for p in priv:
            s = apply_move(c, p, fs9, ms_9)
            if s in non_good_set9:
                adj9[c].append((s, p))

    # Find SCCs
    print("  Finding SCCs in non-good graph...")
    index_counter = [0]
    stack = []
    lowlink = {}
    idx_map = {}
    on_stack = set()
    sccs9 = []

    for v in non_good9:
        if v in idx_map:
            continue
        call_stack = [(v, 0)]
        while call_stack:
            node, ni = call_stack[-1]
            if ni == 0:
                idx_map[node] = index_counter[0]
                lowlink[node] = index_counter[0]
                index_counter[0] += 1
                stack.append(node)
                on_stack.add(node)
            neighbors = [s for s, p in adj9[node]]
            if ni < len(neighbors):
                call_stack[-1] = (node, ni + 1)
                w = neighbors[ni]
                if w not in idx_map:
                    call_stack.append((w, 0))
                elif w in on_stack:
                    lowlink[node] = min(lowlink[node], idx_map[w])
            else:
                if lowlink[node] == idx_map[node]:
                    scc = []
                    while True:
                        w = stack.pop()
                        on_stack.discard(w)
                        scc.append(w)
                        if w == node:
                            break
                    if len(scc) > 1 or (len(scc) == 1 and any(s == scc[0] for s, _ in adj9.get(scc[0], []))):
                        sccs9.append(scc)
                call_stack.pop()
                if call_stack:
                    parent = call_stack[-1][0]
                    lowlink[parent] = min(lowlink[parent], lowlink[node])

    print(f"  Bad SCCs: {len(sccs9)}")
    for i, scc in enumerate(sccs9[:5]):
        print(f"    SCC {i}: size={len(scc)}")

    # For the largest SCC: analyze privilege structure
    if sccs9:
        largest_scc = max(sccs9, key=len)
        scc_set = set(largest_scc)
        print(f"\n  Largest SCC: {len(largest_scc)} configs")

        # For each config in SCC: count privileged procs, check which fire to stay in SCC
        single_in_scc = 0
        multi_in_scc = 0
        multi_all_stay = 0  # multi-priv where ALL choices stay in SCC
        priv_counts = defaultdict(int)

        for c in largest_scc:
            priv = privileged_set(c, fs9, ms_9)
            priv_counts[len(priv)] += 1
            if len(priv) == 1:
                single_in_scc += 1
            else:
                multi_in_scc += 1
                # Check: do all priv choices stay in SCC?
                all_stay = True
                for p in priv:
                    s = apply_move(c, p, fs9, ms_9)
                    if s not in scc_set:
                        all_stay = False
                        break
                if all_stay:
                    multi_all_stay += 1

        print(f"  Privilege distribution in SCC:")
        for k in sorted(priv_counts.keys()):
            print(f"    {k}-priv: {priv_counts[k]} configs")
        print(f"  Multi-priv where ALL choices stay in SCC: {multi_all_stay}")

        # Find an actual cycle in the SCC
        print(f"\n  Finding shortest cycle in largest SCC...")
        start = largest_scc[0]
        # BFS from start, looking for path back to start
        visited = {start: ([], [])}
        queue = deque([start])
        shortest_cycle = None
        shortest_movers = None
        while queue:
            cur = queue.popleft()
            for nxt, p in adj9[cur]:
                if nxt == start and visited[cur][0]:
                    path = visited[cur][0] + [cur]
                    movers = visited[cur][1] + [p]
                    if shortest_cycle is None or len(path) < len(shortest_cycle):
                        shortest_cycle = path
                        shortest_movers = movers
                    break  # found
                if nxt in scc_set and nxt not in visited:
                    visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
                    if len(visited[nxt][0]) < 200:
                        queue.append(nxt)
            if shortest_cycle is not None:
                break

        if shortest_cycle:
            print(f"  Shortest cycle length: {len(shortest_cycle)}")
            print(f"  Movers: {shortest_movers}")

            # Analyze privilege at each step
            all_single = True
            for i, c in enumerate(shortest_cycle):
                priv = privileged_set(c, fs9, ms_9)
                if len(priv) > 1:
                    all_single = False
                    nxt = shortest_cycle[(i+1) % len(shortest_cycle)]
                    staying = [p for p in priv if apply_move(c, p, fs9, ms_9) in non_good_set9]
                    leaving = [p for p in priv if apply_move(c, p, fs9, ms_9) in good_set9]
                    if i < 10:
                        print(f"    Step {i}: config={c}, priv={priv}, mover={shortest_movers[i]}")
                        print(f"      staying in non-good: {staying}, escaping to good: {leaving}")

            print(f"\n  ALL configs in cycle are single-priv: {all_single}")

            if all_single:
                print("  >>> KEY INSIGHT: Bad cycle is ENTIRELY single-priv!")
                print("  >>> forcedSucc_nonGood is trivially true ON the cycle")
                print("  >>> (single priv → unique successor → must stay non-good)")
        else:
            print("  Could not find short cycle (SCC may be large)")


# ══════════════════════════════════════════════════════════════════
# Part 5b: Check ALL combos at n=9 for single-priv property
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART 5b: Systematic single-priv check across combos (n=9)")
print("=" * 72)

if sweeps9:
    w0, cyc0, d0 = sweeps9[0]
    combos_per_proc = [enumerate_state_sequences(ms_9[p], ms_9[p]) for p in range(n)]
    total_combos = 1
    for c in combos_per_proc:
        total_combos *= len(c)
    print(f"Total combos: {total_combos}")

    # Sample combos
    import random
    random.seed(42)
    combo_lists = [list(c) for c in combos_per_proc]

    tested = 0
    all_single_count = 0
    has_multi_count = 0
    no_scc_count = 0

    for trial in range(min(64, total_combos)):
        if trial == 0:
            combo = tuple(c[0] for c in combos_per_proc)
        else:
            combo = tuple(random.choice(combo_lists[p]) for p in range(n))

        _, fs_t, good_set_t, _ = build_sub_threshold_system(ms_9, n, w0, combo)
        all_cfgs_t = list(cartesian(*(range(m) for m in ms_9)))
        non_good_t = set(c for c in all_cfgs_t if c not in good_set_t)

        # Build adjacency
        adj_t = defaultdict(list)
        for c in non_good_t:
            priv = privileged_set(c, fs_t, ms_9)
            for p in priv:
                s = apply_move(c, p, fs_t, ms_9)
                if s in non_good_t:
                    adj_t[c].append((s, p))

        # Find configs that can be in a cycle (those with outgoing edge to non-good)
        reachable = set(c for c in non_good_t if adj_t[c])
        if not reachable:
            no_scc_count += 1
            tested += 1
            continue

        # Quick cycle check: iterate from a random start
        # Just check if any config in reachable has multiple priv where >1 stays non-good
        has_multi_in_cycle = False
        # Check: for configs in the forced set (those with all successors in non-good)
        # A simpler check: find any cycle and check privilege
        start = next(iter(reachable))
        # Follow deterministic path (always pick first non-good successor)
        path = [start]
        path_set = {start}
        cur = start
        cycle_found = None
        for _ in range(500):
            nbrs = adj_t[cur]
            if not nbrs:
                break
            nxt = nbrs[0][0]
            if nxt in path_set:
                # Found cycle
                ci = path.index(nxt)
                cycle_found = path[ci:]
                break
            path.append(nxt)
            path_set.add(nxt)
            cur = nxt

        if cycle_found:
            cycle_single = True
            for c in cycle_found:
                priv = privileged_set(c, fs_t, ms_9)
                if len(priv) > 1:
                    cycle_single = False
                    break
            if cycle_single:
                all_single_count += 1
            else:
                has_multi_count += 1
        else:
            no_scc_count += 1

        tested += 1

    print(f"Tested: {tested}")
    print(f"  All-single-priv cycles: {all_single_count}")
    print(f"  Has-multi-priv in cycle: {has_multi_count}")
    print(f"  No cycle found: {no_scc_count}")


# ══════════════════════════════════════════════════════════════════
# Part 6: Proof Sketch
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART 6: Summary and Proof Sketch")
print("=" * 72)
print("""
Key findings (to be filled after computational results above):
1. Existential non-good successor: does it hold for valid systems?
2. All-to-good configs: do they exist? What structure?
3. Bad cycles in sub-threshold systems: always present?
4. Privilege structure of bad cycles: single-priv or multi-priv?
5. Implications for Lean formalization
""")
