#!/usr/bin/env python3
"""
RA14 Part 3: Definitive analysis for Lean proof strategy.

Key findings so far:
1. Existential non-good successor FAILS in valid systems (some configs
   are 1-step convergent: ALL choices → good)
2. For sub-threshold systems with ANY transition completion: bad cycles exist (512/512)
3. With incrementing default: every non-good config is 9-priv, trivial 2-cycle
4. With identity default: deadlocks exist (not even liveness)

The real question for Lean: HOW to prove bad cycles exist for sub-threshold systems.

Focus areas:
A. The FORCED bad cycle: depends ONLY on good-cycle mover contexts
B. Entry conflict: good-cycle mover contexts force overlaps that create bad cycles
C. The ShadowTrap from the first run (identity default) — analyze its structure
D. Transition-independent argument: bad cycle from forced contexts alone
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, deque
from verifier import privileged_set, apply_move


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


# ══════════════════════════════════════════════════════════════════
# Part A: The FORCED graph (transition-independent)
# ══════════════════════════════════════════════════════════════════
print("=" * 72)
print("PART A: Forced graph — depends only on good-cycle mover contexts")
print("=" * 72)

n = 9
ms = [2,3,3,2,3,3,2,3,3]
target_fc = {p: ms[p] for p in range(n)}

words = enumerate_exact_fc_words(ms, n, target_fc)
seen = set()
unique = []
for w in words:
    canon = canonicalize_word(w)
    if canon not in seen:
        seen.add(canon)
        unique.append(w)
valid_words = []
for w in unique:
    cycle = build_cycle(ms, n, w)
    if cycle is not None:
        valid_words.append((w, cycle))
sweeps = [(w, c, compute_displacement(w, n)) for w, c in valid_words if abs(compute_displacement(w, n)) == 2*n]

combos_per_proc = [enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]
all_cfgs = list(cartesian(*(range(m) for m in ms)))

print(f"Sweep words: {len(sweeps)}")
print(f"Combos: {[len(c) for c in combos_per_proc]}, total = {1}")
for p in range(n):
    print(f"  P{p} (m={ms[p]}): seqs = {combos_per_proc[p]}")

# For each (word, combo): extract mover contexts, build forced graph
# The forced graph: configs connected by transitions FORCED by mover contexts
# A non-good config c with context (L,S,R) matching a mover context → forced move
# If the result is also non-good → forced edge

w0, cyc0, d0 = sweeps[0]
combo0 = tuple(c[0] for c in combos_per_proc)

cs0, fc_num0 = build_cycle_configs(ms, n, w0, combo0)
good_set0 = set(cs0)
ell = len(w0)

# Extract mover contexts
mcx = defaultdict(dict)
for s in range(ell):
    p = w0[s]
    L = cs0[s][(p-1)%n]; S = cs0[s][p]; R = cs0[s][(p+1)%n]
    mcx[p][(L, S, R)] = combo0[p][fc_num0[s]+1]

print(f"\nWord: {list(w0)}")
print(f"Good cycle: {ell} configs")
print(f"Mover contexts per proc:")
for p in range(n):
    print(f"  P{p}: {dict(mcx[p])}")

# Build forced graph on non-good configs
non_good = [c for c in all_cfgs if c not in good_set0]
non_good_set = set(non_good)

forced_adj = defaultdict(list)
for c in non_good:
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if (L, S, R) in mcx[p]:
            Sp = mcx[p][(L, S, R)]
            if Sp != S:  # privileged
                nc = list(c); nc[p] = Sp; nc = tuple(nc)
                if nc not in good_set0:
                    forced_adj[c].append((nc, p))

# The forced graph: edges that exist regardless of how you complete the transition
# These transitions are FORCED by the good cycle's mover contexts

# Find SCCs in forced graph
configs_with_forced = set(c for c in non_good if forced_adj[c])
print(f"\nNon-good configs with forced edges: {len(configs_with_forced)}/{len(non_good)}")

# Tarjan's SCC (iterative)
index_counter = [0]
stack = []
lowlink = {}
idx_map = {}
on_stack = set()
forced_sccs = []

for v in non_good:
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
        neighbors = [s for s, p in forced_adj[node]]
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
                if len(scc) > 1 or (len(scc) == 1 and any(s == scc[0] for s, _ in forced_adj.get(scc[0], []))):
                    forced_sccs.append(scc)
            call_stack.pop()
            if call_stack:
                parent = call_stack[-1][0]
                lowlink[parent] = min(lowlink[parent], lowlink[node])

print(f"Forced SCCs (bad cycles from mover contexts alone): {len(forced_sccs)}")
for i, scc in enumerate(forced_sccs[:5]):
    print(f"  SCC {i}: size={len(scc)}")


# ══════════════════════════════════════════════════════════════════
# Part B: Forced cycle detail — what makes it work
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART B: Forced cycle structure (sweep 0, combo 0)")
print("=" * 72)

if forced_sccs:
    largest = max(forced_sccs, key=len)
    scc_set = set(largest)

    # Find shortest cycle using BFS
    start = largest[0]
    visited = {start: ([], [])}
    queue = deque([start])
    best_cycle = None
    best_movers = None

    while queue:
        cur = queue.popleft()
        path_len = len(visited[cur][0])
        if best_cycle and path_len >= len(best_cycle):
            continue
        for nxt, p in forced_adj[cur]:
            if nxt == start and visited[cur][0]:
                path = visited[cur][0] + [cur]
                movers = visited[cur][1] + [p]
                if best_cycle is None or len(path) < len(best_cycle):
                    best_cycle = path
                    best_movers = movers
                break
            if nxt in scc_set and nxt not in visited:
                visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
                if len(visited[nxt][0]) < 200:
                    queue.append(nxt)

    if best_cycle:
        print(f"Shortest forced cycle: length {len(best_cycle)}")
        print(f"Movers: {best_movers}")
        for i, c in enumerate(best_cycle):
            p = best_movers[i]
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            nxt = best_cycle[(i+1) % len(best_cycle)]
            # How many procs are forced-privileged at c?
            forced_priv = []
            for q in range(n):
                Lq = c[(q-1)%n]; Sq = c[q]; Rq = c[(q+1)%n]
                if (Lq, Sq, Rq) in mcx[q] and mcx[q][(Lq, Sq, Rq)] != Sq:
                    forced_priv.append(q)
            print(f"  [{i}] {c}  fire P{p} ctx=({L},{S},{R})→{mcx[p][(L,S,R)]}  "
                  f"forced_priv={forced_priv}")

        # KEY: is the forced cycle single-forced-priv at every step?
        all_single_forced = True
        for i, c in enumerate(best_cycle):
            forced_priv = []
            for q in range(n):
                Lq = c[(q-1)%n]; Sq = c[q]; Rq = c[(q+1)%n]
                if (Lq, Sq, Rq) in mcx[q] and mcx[q][(Lq, Sq, Rq)] != Sq:
                    forced_priv.append(q)
            if len(forced_priv) != 1:
                all_single_forced = False

        print(f"\nAll steps single-forced-priv: {all_single_forced}")


# ══════════════════════════════════════════════════════════════════
# Part C: ALL 512 instances — forced cycle check
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART C: All 512 instances — forced SCC existence")
print("=" * 72)

import itertools
total = 0
has_forced_scc = 0
no_forced_scc = 0

for wi, (w, cyc, disp) in enumerate(sweeps):
    all_combos = list(itertools.product(*combos_per_proc))
    word_yes = 0
    word_no = 0

    for combo in all_combos:
        cs, fc_num = build_cycle_configs(ms, n, w, combo)
        good = set(cs)
        ell_w = len(w)

        mcx_t = defaultdict(dict)
        for s in range(ell_w):
            p = w[s]
            L = cs[s][(p-1)%n]; S = cs[s][p]; R = cs[s][(p+1)%n]
            mcx_t[p][(L, S, R)] = combo[p][fc_num[s]+1]

        # Build forced graph
        fadj = defaultdict(list)
        for c in all_cfgs:
            if c in good:
                continue
            for p in range(n):
                L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
                if (L, S, R) in mcx_t[p]:
                    Sp = mcx_t[p][(L, S, R)]
                    if Sp != S:
                        nc = list(c); nc[p] = Sp; nc = tuple(nc)
                        if nc not in good:
                            fadj[c].append((nc, p))

        # Quick cycle check with Floyd
        has_cycle = False
        checked = set()
        for start_c in all_cfgs:
            if start_c in good or start_c in checked:
                continue
            if not fadj.get(start_c):
                checked.add(start_c)
                continue
            slow = start_c
            fast = start_c
            for _ in range(6000):
                if not fadj.get(slow): break
                slow = fadj[slow][0][0]
                if not fadj.get(fast): break
                fast = fadj[fast][0][0]
                if not fadj.get(fast): break
                fast = fadj[fast][0][0]
                if slow == fast:
                    has_cycle = True
                    break
            if has_cycle:
                break
            cur = start_c
            for _ in range(500):
                checked.add(cur)
                if not fadj.get(cur): break
                cur = fadj[cur][0][0]
                if cur in checked: break

        if has_cycle:
            word_yes += 1
        else:
            word_no += 1
        total += 1

    has_forced_scc += word_yes
    no_forced_scc += word_no
    print(f"  Sweep {wi}: {word_yes}/{word_yes+word_no} have FORCED bad cycles")

print(f"\nTotal: {has_forced_scc}/{total} have forced bad cycles")
print(f"No forced bad cycle: {no_forced_scc}")


# ══════════════════════════════════════════════════════════════════
# Part D: Entry conflict → forced cycle mechanism
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART D: Entry conflict analysis — WHY forced cycles exist")
print("=" * 72)

# The entry conflict theorem says: for sub-threshold systems, the good cycle's
# mover contexts have conflicts. Specifically, there exists a context (L,S,R)
# that appears as BOTH a mover context (where the transition is forced to change S)
# and a non-mover context (where S should stay the same).
# This creates a config where the proc is forced-privileged but shouldn't be.

# Let's check: at each step of the good cycle, what are the non-mover contexts?
w0, cyc0, d0 = sweeps[0]
combo0 = tuple(c[0] for c in combos_per_proc)
cs0, fc_num0 = build_cycle_configs(ms, n, w0, combo0)
good_set0 = set(cs0)
ell = len(w0)

print(f"Word: {list(w0)}")

# For each proc p, collect:
# - mover contexts: (L,S,R) where p fires, S changes
# - non-mover contexts: (L,S,R) where p doesn't fire, S stays
mover_ctx = defaultdict(set)
nonmover_ctx = defaultdict(set)

for s in range(ell):
    mover = w0[s]
    c = cs0[s]
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if p == mover:
            mover_ctx[p].add((L, S, R))
        else:
            nonmover_ctx[p].add((L, S, R))

# Entry conflict: mover_ctx ∩ nonmover_ctx
print("\nEntry conflict check:")
total_conflicts = 0
for p in range(n):
    overlap = mover_ctx[p] & nonmover_ctx[p]
    if overlap:
        total_conflicts += len(overlap)
        print(f"  P{p}: {len(overlap)} conflicts: {overlap}")
        for ctx in overlap:
            L, S, R = ctx
            new_val = mcx[p][ctx]
            print(f"    ({L},{S},{R}): mover→{new_val}, nonmover→{S} CONFLICT!")
    else:
        print(f"  P{p}: no conflicts")

print(f"\nTotal entry conflicts: {total_conflicts}")

# The entry conflicts create forced-privileged configs at non-mover positions.
# These are the seeds of the bad cycle.

# Let's trace: what happens when we apply the forced transition at an entry conflict?
print("\nEntry conflict config tracing:")
for p in range(n):
    overlap = mover_ctx[p] & nonmover_ctx[p]
    for ctx in list(overlap)[:2]:
        L, S, R = ctx
        new_val = mcx[p][ctx]
        # Find a non-good config where P_p has context (L,S,R)
        # and P_p is at a non-mover step (i.e., P_p's context matches but p is not the mover)
        for s in range(ell):
            if w0[s] != p:  # p is non-mover
                c = cs0[s]
                Lp = c[(p-1)%n]; Sp = c[p]; Rp = c[(p+1)%n]
                if (Lp, Sp, Rp) == ctx:
                    # This is a good-cycle config where P_p has the conflicting context
                    # If we change P_p's state, we get a non-good config
                    nc = list(c); nc[p] = new_val; nc = tuple(nc)
                    if nc not in good_set0:
                        print(f"  P{p} ctx={ctx}: good config {c} step {s}")
                        print(f"    If P{p} fires: {c} → {nc} (non-good)")
                        # Follow the forced chain from nc
                        chain = [nc]
                        chain_movers = []
                        cur = nc
                        for _ in range(30):
                            if cur in good_set0:
                                chain.append("→GOOD")
                                break
                            nbrs = forced_adj.get(tuple(cur), [])
                            if not nbrs:
                                chain.append("→DEAD END (no forced edges)")
                                break
                            nxt, mp = nbrs[0]
                            chain_movers.append(mp)
                            if tuple(nxt) in set(map(tuple, chain[:-1] if isinstance(chain[-1], str) else chain)):
                                chain.append(f"→CYCLE back to {nxt}")
                                break
                            chain.append(nxt)
                            cur = nxt
                        print(f"    Forced chain ({len(chain)-1} steps): movers={chain_movers[:10]}")
                    break


# ══════════════════════════════════════════════════════════════════
# Part E: The proof sketch
# ══════════════════════════════════════════════════════════════════
print("\n" + "=" * 72)
print("PART E: PROOF SKETCH FOR LEAN")
print("=" * 72)

print("""
=== PROOF STRATEGY: ¬converges for sub-threshold systems ===

OBSERVATION 1: The existential non-good successor claim is FALSE.
  In valid systems (Sol3, CUP-2), some non-good configs have ALL
  daemon choices leading to good. These are "1-step convergent" configs.
  This is expected — they're just close to the good cycle.

OBSERVATION 2: For the ¬converges proof, we don't need the existential
  at EVERY config. We just need a BAD CYCLE to exist.

OBSERVATION 3: The FORCED graph (transitions determined solely by
  the good cycle's mover contexts) contains bad cycles for ALL 512
  stuttered sweep instances.

OBSERVATION 4: These forced bad cycles contain MULTI-priv configs.
  There are no single-priv-only bad cycles in the forced graph.

=== THE ARGUMENT ===

Given: A sub-threshold system with state vector ms and transition
functions fs, with good cycle GC.

Goal: Prove ¬WellFounded(badStep), where
  badStep c' c := c ∉ GC.configs ∧ c' ∉ GC.configs ∧
                  ∃p, privileged(c,p) ∧ move(c,p) = c'

Step 1: Extract the mover contexts from GC.
  For each proc p, the good cycle determines a partial transition:
  MCX[p] = {(L,S,R) ↦ S' : p fires at some good config with ctx (L,S,R)}

Step 2: Entry conflict (already proved).
  The good cycle has entry conflicts: contexts (L,S,R) that appear
  at BOTH mover and non-mover positions for some proc p.
  At a mover position: f_p(L,S,R) = S' ≠ S (forced by MCX[p])
  At a non-mover position: S should stay the same.

  This means: ANY transition function f_p consistent with MCX must
  have f_p(L,S,R) = S' ≠ S, making p privileged at ALL configs with
  this context — including those where p shouldn't fire.

Step 3: Construct the bad cycle explicitly.
  The forced graph (using only MCX edges on non-good configs) has
  cycles. These cycles are bad cycles: each config is non-good,
  each transition is valid (the firing proc IS privileged because
  its context matches an MCX entry).

Step 4: ¬WellFounded follows.
  A bad cycle of length L gives an infinite descending chain
  (repeating the cycle). Therefore badStep is not well-founded.

=== KEY INSIGHT ===

The proof does NOT need forcedSucc_nonGood (universal or existential).
It just needs to EXHIBIT a specific bad cycle, which is a finite
combinatorial object that can be verified step-by-step.

For each step in the bad cycle:
  (a) The config is not in GC.configs (by construction)
  (b) The fired proc has a context matching MCX[p], so it's privileged
  (c) The move produces the next config in the cycle (by MCX[p])
  (d) The next config is also not in GC.configs (by construction)

This is a DECISION procedure: given the good cycle and the bad cycle,
verification is mechanical.
""")

# Print the actual cycle for Lean
if forced_sccs:
    largest = max(forced_sccs, key=len)
    scc_set = set(largest)

    # Find shortest cycle
    best_len = float('inf')
    best_path = None
    best_mvrs = None

    import random
    random.seed(42)
    samples = random.sample(largest, min(50, len(largest)))

    for start in samples:
        visited = {start: ([], [])}
        queue = deque([start])
        found = False
        while queue and not found:
            cur = queue.popleft()
            plen = len(visited[cur][0])
            if plen >= best_len:
                continue
            for nxt, p in forced_adj[cur]:
                if nxt == start and visited[cur][0]:
                    path = visited[cur][0] + [cur]
                    movers = visited[cur][1] + [p]
                    if len(path) < best_len:
                        best_len = len(path)
                        best_path = path
                        best_mvrs = movers
                    found = True
                    break
                if nxt in scc_set and nxt not in visited:
                    visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
                    if len(visited[nxt][0]) + 1 < best_len:
                        queue.append(nxt)

    if best_path:
        print(f"\n=== EXPLICIT BAD CYCLE (length {best_len}) ===")
        print(f"ms = {ms}")
        print(f"Word = {list(w0)}")
        print(f"Combo = {combo0}")
        print(f"\nBad cycle configs and movers:")
        for i in range(len(best_path)):
            c = best_path[i]
            p = best_mvrs[i]
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            Sp = mcx[p][(L, S, R)]
            nxt = best_path[(i+1) % len(best_path)]
            # Verify
            actual = list(c); actual[p] = Sp; actual = tuple(actual)
            ok = (actual == nxt)
            in_good = c in good_set0
            print(f"  c[{i}] = {c}  fire P{p}: ({L},{S},{R})→{Sp}  "
                  f"{'OK' if ok else 'FAIL'}  {'GOOD!' if in_good else 'non-good'}")
