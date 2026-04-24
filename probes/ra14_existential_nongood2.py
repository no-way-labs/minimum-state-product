#!/usr/bin/env python3
"""
RA14 Part 2: Deeper investigation.

Key findings from Part 1:
- Existential non-good successor FAILS in valid systems (Sol3, CUP-2)
- Some non-good configs have ALL choices leading to good (1-step convergent)
- Bad cycles exist in sub-threshold systems (n=9 stuttered sweep)
- Bad cycles contain multi-priv configs

New questions:
1. The 5b result (no cycle found in 64 combos) was because identity default
   makes most procs non-privileged. Need to use incrementing default.
2. For the bad cycle found in Part 4: it has multi-priv. Does the daemon
   NEED multi-priv configs to form the cycle, or can it avoid them?
3. What is the MINIMUM cycle in the SCC?
4. For valid systems: the "all-to-good" configs are fine — they're just
   1-step from the good cycle. The daemon can't stall at them.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, deque
from verifier import verify_system, privileged_set, apply_move


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
    T_bot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    T_low = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    T_mid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    T_high = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    T_top = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    def get_table(pos):
        if pos == 0: return T_bot
        if pos == 1: return T_low
        if pos == n - 2: return T_high
        if pos == n - 1: return T_top
        return T_mid
    fs = []
    for p in range(n):
        tbl = get_table(p)
        fs.append(lambda L, S, R, t=tbl: t[(L, S, R)])
    return ms, fs


# ══════════════════════════════════════════════════════════════════
# Part A: Recheck sub-threshold with incrementing default
# ══════════════════════════════════════════════════════════════════
print("=" * 72)
print("PART A: Sub-threshold systems with incrementing default transitions")
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

def build_cycle_configs(ms, n, word, combo):
    ell = len(word)
    fc_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        fc_num[s] = pc[word[s]]
        pc[word[s]] += 1
    cs = []
    state = [0]*n
    for s in range(ell):
        cs.append(tuple(state))
        p = word[s]
        state[p] = combo[p][fc_num[s]+1]
    return cs, fc_num

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


def build_full_system(ms, n, word, combo):
    """Build system with INCREMENTING as default transition for undefined contexts."""
    ell = len(word)
    cs, fc_num = build_cycle_configs(ms, n, word, combo)
    good_set = set(cs)

    # Extract mover contexts
    mcx = defaultdict(dict)
    for s in range(ell):
        p = word[s]
        L = cs[s][(p-1)%n]; S = cs[s][p]; R = cs[s][(p+1)%n]
        mcx[p][(L, S, R)] = combo[p][fc_num[s]+1]

    # Build full transition: use incrementing for undefined contexts
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
                        # Incrementing: (S+1) % m
                        tbl[(L, S, R)] = (S + 1) % m
        return lambda L, S, R, t=tbl: t[(L, S, R)]

    fs = [make_trans(p, mcx[p]) for p in range(n)]
    return ms, fs, good_set, mcx


n = 9
ms_9 = [2,3,3,2,3,3,2,3,3]
target_fc = {p: ms_9[p] for p in range(n)}

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

w0, cyc0, d0 = sweeps9[0]
combos_per_proc = [enumerate_state_sequences(ms_9[p], ms_9[p]) for p in range(n)]
print(f"Combos per proc: {[len(c) for c in combos_per_proc]}")

combo0 = tuple(c[0] for c in combos_per_proc)
_, fs9, good_set9, mcx9 = build_full_system(ms_9, n, w0, combo0)

all_cfgs9 = list(cartesian(*(range(m) for m in ms_9)))
non_good9 = [c for c in all_cfgs9 if c not in good_set9]
non_good_set9 = set(non_good9)
print(f"|good|={len(good_set9)}, |non-good|={len(non_good9)}")

# Build adjacency
adj9 = defaultdict(list)
for c in non_good9:
    priv = privileged_set(c, fs9, ms_9)
    for p in priv:
        s = apply_move(c, p, fs9, ms_9)
        if s in non_good_set9:
            adj9[c].append((s, p))

# Find SCCs using iterative Tarjan
print("Finding SCCs...")
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

print(f"Bad SCCs: {len(sccs9)}, sizes: {sorted([len(s) for s in sccs9], reverse=True)[:10]}")

# ══════════════════════════════════════════════════════════════════
# Part B: For the largest SCC, find SHORTEST cycle & analyze
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART B: Shortest cycle in largest SCC — privilege structure")
print("=" * 72)

if sccs9:
    largest = max(sccs9, key=len)
    scc_set = set(largest)
    print(f"Largest SCC: {len(largest)} configs")

    # Privilege distribution
    priv_dist = defaultdict(int)
    for c in largest:
        priv = privileged_set(c, fs9, ms_9)
        priv_dist[len(priv)] += 1
    print(f"Privilege distribution: {dict(priv_dist)}")

    # BFS for shortest cycle from each starting config (sample)
    import random
    random.seed(42)
    samples = random.sample(largest, min(20, len(largest)))

    min_cycle_len = float('inf')
    min_cycle = None
    min_movers = None

    for start in samples:
        visited = {start: ([], [])}
        queue = deque([start])
        found = False
        while queue and not found:
            cur = queue.popleft()
            for nxt, p in adj9[cur]:
                if nxt == start and visited[cur][0]:
                    path = visited[cur][0] + [cur]
                    movers = visited[cur][1] + [p]
                    if len(path) < min_cycle_len:
                        min_cycle_len = len(path)
                        min_cycle = path
                        min_movers = movers
                    found = True
                    break
                if nxt in scc_set and nxt not in visited:
                    visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
                    if len(visited[nxt][0]) < 100:
                        queue.append(nxt)

    if min_cycle:
        print(f"\nShortest cycle found: length {min_cycle_len}")
        print(f"Movers: {min_movers}")

        # Detailed analysis of each step
        single_count = 0
        multi_count = 0
        for i, c in enumerate(min_cycle):
            priv = privileged_set(c, fs9, ms_9)
            nxt = min_cycle[(i+1) % len(min_cycle)]
            fired = min_movers[i]

            nongood_choices = []
            good_choices = []
            for p in priv:
                s = apply_move(c, p, fs9, ms_9)
                if s in good_set9:
                    good_choices.append(p)
                else:
                    nongood_choices.append(p)

            if len(priv) == 1:
                single_count += 1
            else:
                multi_count += 1

            print(f"  Step {i}: priv={priv}, fired={fired}, "
                  f"nongood_choices={nongood_choices}, good_choices={good_choices}")

        print(f"\nSingle-priv steps: {single_count}, Multi-priv steps: {multi_count}")

    # ══════════════════════════════════════════════════════════════════
    # Part C: Can we find a SINGLE-PRIV-ONLY cycle in the SCC?
    # ══════════════════════════════════════════════════════════════════
    print("\n" + "=" * 72)
    print("PART C: Search for single-priv-only cycle in SCC")
    print("=" * 72)

    single_priv_in_scc = [c for c in largest if len(privileged_set(c, fs9, ms_9)) == 1]
    single_set = set(single_priv_in_scc)
    print(f"Single-priv configs in SCC: {len(single_priv_in_scc)}")

    # Build subgraph restricted to single-priv configs
    adj_single = defaultdict(list)
    for c in single_priv_in_scc:
        priv = privileged_set(c, fs9, ms_9)
        p = priv[0]
        s = apply_move(c, p, fs9, ms_9)
        if s in single_set and s in scc_set:
            adj_single[c].append((s, p))

    # Check for cycle
    visited_s = set()
    single_cycle = None
    for start in single_priv_in_scc:
        if start in visited_s:
            continue
        path = [start]
        path_set = {start}
        cur = start
        for _ in range(500):
            nbrs = adj_single.get(cur, [])
            if not nbrs:
                break
            nxt = nbrs[0][0]
            if nxt in path_set:
                ci = path.index(nxt)
                single_cycle = path[ci:]
                break
            path.append(nxt)
            path_set.add(nxt)
            cur = nxt
        visited_s.update(path)
        if single_cycle:
            break

    if single_cycle:
        print(f"Single-priv cycle found! Length: {len(single_cycle)}")
        for i, c in enumerate(single_cycle[:10]):
            priv = privileged_set(c, fs9, ms_9)
            print(f"  {c}, priv={priv}")
    else:
        print("No single-priv cycle in SCC")
        # But do single-priv configs eventually reach multi-priv?
        print("Checking where single-priv configs go...")
        reaches_multi = 0
        reaches_good = 0
        dead_end = 0
        for c in single_priv_in_scc[:20]:
            priv = privileged_set(c, fs9, ms_9)
            p = priv[0]
            s = apply_move(c, p, fs9, ms_9)
            if s in good_set9:
                reaches_good += 1
            elif s in scc_set:
                sp = privileged_set(s, fs9, ms_9)
                if len(sp) > 1:
                    reaches_multi += 1
                else:
                    dead_end += 1  # single but not in single_set restricted
            else:
                dead_end += 1
        print(f"  Of {min(20, len(single_priv_in_scc))} single-priv: "
              f"→good={reaches_good}, →multi={reaches_multi}, other={dead_end}")


# ══════════════════════════════════════════════════════════════════
# Part D: The RIGHT question — does a bad ATTRACTOR exist?
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART D: Bad attractor analysis")
print("=" * 72)

if sccs9:
    # The SCC IS the bad attractor. The daemon can navigate within it forever.
    # The question for Lean: we need WellFounded(badStep) to fail.
    # badStep c' c = c non-good AND c' non-good AND ∃p, priv p ∧ move(c,p)=c'
    # ¬WellFounded ↔ ∃ infinite descending chain ↔ ∃ cycle in badStep graph
    # The SCC gives us this cycle.

    # But the KEY question: in the Lean formalization, we define badStep as
    # c' c where c transitions to c'. WellFounded means no infinite chain
    # ... c₂ → c₁ → c₀. A cycle gives an infinite chain.

    # For the proof: we need to CONSTRUCT the cycle explicitly.
    # And show each transition is valid (privileged proc exists, fires to next config).

    print("Bad SCC = bad attractor = daemon trap")
    print(f"Largest SCC size: {len(largest)}")

    # Extract a MINIMAL cycle
    # Use BFS from every config, find globally shortest
    global_min_len = float('inf')
    global_min_cycle = None
    global_min_movers = None

    for start in largest:
        visited = {start: ([], [])}
        queue = deque([start])
        found = False
        while queue and not found:
            cur = queue.popleft()
            path_len = len(visited[cur][0])
            if path_len >= global_min_len:
                continue
            for nxt, p in adj9[cur]:
                if nxt == start and visited[cur][0]:
                    path = visited[cur][0] + [cur]
                    movers = visited[cur][1] + [p]
                    if len(path) < global_min_len:
                        global_min_len = len(path)
                        global_min_cycle = path
                        global_min_movers = movers
                    found = True
                    break
                if nxt in scc_set and nxt not in visited:
                    visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
                    if len(visited[nxt][0]) + 1 < global_min_len:
                        queue.append(nxt)

    print(f"\nGlobally shortest cycle in SCC: length {global_min_len}")
    if global_min_cycle:
        print(f"Configs:")
        for i, c in enumerate(global_min_cycle):
            priv = privileged_set(c, fs9, ms_9)
            print(f"  [{i}] {c}  priv={priv}  fire={global_min_movers[i]}")

        # Verify cycle
        print("\nVerification:")
        ok = True
        for i in range(len(global_min_cycle)):
            c = global_min_cycle[i]
            nxt = global_min_cycle[(i+1) % len(global_min_cycle)]
            p = global_min_movers[i]
            actual = apply_move(c, p, fs9, ms_9)
            priv = privileged_set(c, fs9, ms_9)
            if actual != nxt:
                print(f"  FAIL at step {i}: move({c},{p})={actual} != {nxt}")
                ok = False
            if p not in priv:
                print(f"  FAIL at step {i}: proc {p} not privileged at {c}")
                ok = False
            if c in good_set9:
                print(f"  FAIL at step {i}: {c} is GOOD")
                ok = False
        print(f"  All checks passed: {ok}")


# ══════════════════════════════════════════════════════════════════
# Part E: Cross-system comparison — all 8 sweep words × all combos
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART E: All sweep words — bad SCC existence")
print("=" * 72)

total_tested = 0
total_with_scc = 0
total_without_scc = 0
min_cycles_found = []

for wi, (w, cyc, disp) in enumerate(sweeps9):
    combos_per_proc = [enumerate_state_sequences(ms_9[p], ms_9[p]) for p in range(n)]
    import itertools
    all_combos = list(itertools.product(*combos_per_proc))

    word_has_scc = 0
    word_no_scc = 0

    for combo in all_combos:
        _, fs_t, good_set_t, mcx_t = build_full_system(ms_9, n, w, combo)
        all_cfgs_t = list(cartesian(*(range(m) for m in ms_9)))
        non_good_t = set(c for c in all_cfgs_t if c not in good_set_t)

        # Build adjacency restricted to non-good
        adj_t = defaultdict(list)
        for c in non_good_t:
            priv = privileged_set(c, fs_t, ms_9)
            for p in priv:
                s = apply_move(c, p, fs_t, ms_9)
                if s in non_good_t:
                    adj_t[c].append((s, p))

        # Quick cycle check: follow path from a random non-good config
        has_cycle = False
        checked = set()
        for start_c in non_good_t:
            if start_c in checked:
                continue
            if not adj_t[start_c]:
                checked.add(start_c)
                continue
            # Floyd's cycle detection
            slow = start_c
            fast = start_c
            for _ in range(len(non_good_t)):
                if not adj_t.get(slow):
                    break
                slow = adj_t[slow][0][0]
                if not adj_t.get(fast):
                    break
                fast = adj_t[fast][0][0]
                if not adj_t.get(fast):
                    break
                fast = adj_t[fast][0][0]
                if slow == fast:
                    has_cycle = True
                    break
            if has_cycle:
                break
            # Mark all visited as checked
            cur = start_c
            for _ in range(200):
                checked.add(cur)
                if not adj_t.get(cur):
                    break
                cur = adj_t[cur][0][0]
                if cur in checked:
                    break

        if has_cycle:
            word_has_scc += 1
        else:
            word_no_scc += 1
        total_tested += 1

    total_with_scc += word_has_scc
    total_without_scc += word_no_scc
    print(f"  Sweep {wi} (disp={disp}): {word_has_scc}/{word_has_scc+word_no_scc} have bad cycles")

print(f"\nTotal: {total_with_scc}/{total_tested} have bad cycles, {total_without_scc} don't")


# ══════════════════════════════════════════════════════════════════
# Part F: Check with Sol3-like transitions (decrementing) as default
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART F: Alternative default transitions")
print("=" * 72)

def build_full_system_dec(ms, n, word, combo):
    """Build system with DECREMENTING as default."""
    ell = len(word)
    cs, fc_num = build_cycle_configs(ms, n, word, combo)
    good_set = set(cs)
    mcx = defaultdict(dict)
    for s in range(ell):
        p = word[s]
        L = cs[s][(p-1)%n]; S = cs[s][p]; R = cs[s][(p+1)%n]
        mcx[p][(L, S, R)] = combo[p][fc_num[s]+1]

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
                        tbl[(L, S, R)] = (S - 1) % m  # decrementing
        return lambda L, S, R, t=tbl: t[(L, S, R)]
    fs = [make_trans(p, mcx[p]) for p in range(n)]
    return ms, fs, good_set, mcx


# Test sweep 0, combo 0 with decrementing
w0 = sweeps9[0][0]
combo0 = tuple(combos_per_proc[p][0] for p in range(n))
_, fs_dec, good_dec, _ = build_full_system_dec(ms_9, n, w0, combo0)

non_good_dec = set(c for c in all_cfgs9 if c not in good_dec)
adj_dec = defaultdict(list)
for c in non_good_dec:
    priv = privileged_set(c, fs_dec, ms_9)
    for p in priv:
        s = apply_move(c, p, fs_dec, ms_9)
        if s in non_good_dec:
            adj_dec[c].append((s, p))

# Floyd cycle check
has_cycle_dec = False
for start_c in non_good_dec:
    if not adj_dec.get(start_c):
        continue
    slow = start_c
    fast = start_c
    for _ in range(len(non_good_dec)):
        if not adj_dec.get(slow): break
        slow = adj_dec[slow][0][0]
        if not adj_dec.get(fast): break
        fast = adj_dec[fast][0][0]
        if not adj_dec.get(fast): break
        fast = adj_dec[fast][0][0]
        if slow == fast:
            has_cycle_dec = True
            break
    if has_cycle_dec:
        break
print(f"Decrementing default: bad cycle exists = {has_cycle_dec}")

# Also test identity default (only good-cycle contexts are privileged)
def build_full_system_id(ms, n, word, combo):
    """Build system with IDENTITY as default (non-priv outside good cycle)."""
    ell = len(word)
    cs, fc_num = build_cycle_configs(ms, n, word, combo)
    good_set = set(cs)
    mcx = defaultdict(dict)
    for s in range(ell):
        p = word[s]
        L = cs[s][(p-1)%n]; S = cs[s][p]; R = cs[s][(p+1)%n]
        mcx[p][(L, S, R)] = combo[p][fc_num[s]+1]

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
                        tbl[(L, S, R)] = S  # identity
        return lambda L, S, R, t=tbl: t[(L, S, R)]
    fs = [make_trans(p, mcx[p]) for p in range(n)]
    return ms, fs, good_set, mcx

_, fs_id, good_id, _ = build_full_system_id(ms_9, n, w0, combo0)
non_good_id = set(c for c in all_cfgs9 if c not in good_id)
adj_id = defaultdict(list)
for c in non_good_id:
    priv = privileged_set(c, fs_id, ms_9)
    for p in priv:
        s = apply_move(c, p, fs_id, ms_9)
        if s in non_good_id:
            adj_id[c].append((s, p))

has_cycle_id = False
for start_c in non_good_id:
    if not adj_id.get(start_c): continue
    slow = start_c
    fast = start_c
    for _ in range(len(non_good_id)):
        if not adj_id.get(slow): break
        slow = adj_id[slow][0][0]
        if not adj_id.get(fast): break
        fast = adj_id[fast][0][0]
        if not adj_id.get(fast): break
        fast = adj_id[fast][0][0]
        if slow == fast:
            has_cycle_id = True
            break
    if has_cycle_id: break
print(f"Identity default: bad cycle exists = {has_cycle_id}")

# How many privileged configs with identity?
priv_count_id = sum(1 for c in non_good_id if privileged_set(c, fs_id, ms_9))
print(f"Identity: {priv_count_id}/{len(non_good_id)} non-good have ≥1 priv proc")
no_priv_id = [c for c in non_good_id if not privileged_set(c, fs_id, ms_9)]
print(f"Identity: {len(no_priv_id)} non-good configs have NO priv proc (deadlocked)")
