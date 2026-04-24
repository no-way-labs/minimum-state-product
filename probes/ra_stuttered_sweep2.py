#!/usr/bin/env python3
"""
RA Part 2: Deep trap analysis - find shadow cycles, understand structure.
Focus on identity fill where trap=540 is combo-independent.
"""

import sys
import itertools
from collections import Counter, defaultdict

def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))

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
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]

def canonicalize_word(word):
    best = word
    for i in range(len(word)):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best

def compute_displacement(word, n):
    total = 0
    ell = len(word)
    for i in range(ell):
        diff = (word[(i+1)%ell] - word[i]) % n
        if diff == 1:
            total += 1
        elif diff == n-1:
            total -= 1
    return total

def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining-1)
                seq.pop()
    dfs([0], k)
    return seqs


# ============================================================
# Setup
# ============================================================
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

valid = []
for w in unique:
    cycle = build_cycle(ms, n, w)
    if cycle is not None:
        valid.append((w, cycle))

# Get sweep #0
sweeps = []
for w, cycle in valid:
    disp = compute_displacement(w, n)
    if abs(disp) == 2*n:
        sweeps.append((w, cycle, disp))

w0, cycle0, disp0 = sweeps[0]
ell = len(w0)

# Use the all-increment state sequence (simplest)
combo = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))

print(f"Word: {list(w0)}")
print(f"Combo: {combo}")

# Build config sequence
fc_counter = Counter(w0)
firing_num = [0]*ell
pc = [0]*n
for s in range(ell):
    firing_num[s] = pc[w0[s]]
    pc[w0[s]] += 1

configs_seq = []
state = [0]*n
for s in range(ell):
    configs_seq.append(tuple(state))
    p = w0[s]
    state[p] = combo[p][firing_num[s]+1]

good_set = set(configs_seq)
print(f"Good cycle: {len(good_set)} configs")

# Build transition tables (identity fill for free entries)
tables = {}
for p in range(n):
    tables[p] = {}

for s in range(ell):
    p = w0[s]
    L = configs_seq[s][(p-1)%n]
    S = configs_seq[s][p]
    R = configs_seq[s][(p+1)%n]
    S_new = combo[p][firing_num[s]+1]
    tables[p][(L, S, R)] = S_new

for s in range(ell):
    for q in range(n):
        if q == w0[s]:
            continue
        L = configs_seq[s][(q-1)%n]
        S = configs_seq[s][q]
        R = configs_seq[s][(q+1)%n]
        if (L, S, R) not in tables[q]:
            tables[q][(L, S, R)] = S

# Identity fill
for p in range(n):
    for L in range(ms[(p-1)%n]):
        for S in range(ms[p]):
            for R in range(ms[(p+1)%n]):
                if (L, S, R) not in tables[p]:
                    tables[p][(L, S, R)] = S

def f(p, L, S, R):
    return tables[p][(L, S, R)]

# ============================================================
# Compute full game graph
# ============================================================
print("\n" + "=" * 72)
print("FULL GAME GRAPH ANALYSIS")
print("=" * 72)

all_cfgs = all_configs(ms)
priv_map = {}
for c in all_cfgs:
    priv = []
    for i in range(n):
        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
        if f(i, L, S, R) != S:
            priv.append(i)
    priv_map[c] = priv

bad_set = set(all_cfgs) - good_set
dead = [c for c in all_cfgs if len(priv_map[c]) == 0]
print(f"Total configs: {len(all_cfgs)}")
print(f"Good: {len(good_set)}, Bad: {len(bad_set)}, Dead: {len(dead)}")

# Build bad successor graph
bad_succs = defaultdict(set)
for c in bad_set:
    for i in priv_map[c]:
        s = list(c)
        s[i] = f(i, c[(i-1)%n], c[i], c[(i+1)%n])
        ns = tuple(s)
        if ns in bad_set:
            bad_succs[c].add(ns)

# Find trap
trap = set(c for c in bad_set if bad_succs[c])
changed = True
while changed:
    changed = False
    to_remove = set()
    for c in trap:
        if not any(s in trap for s in bad_succs[c]):
            to_remove.add(c)
    if to_remove:
        trap -= to_remove
        changed = True

print(f"Trap: {len(trap)} configs")

# ============================================================
# Find ALL cycles in the trap using Tarjan's SCC
# ============================================================
print("\n--- SCCs in trap ---")

# Build adjacency restricted to trap
trap_adj = defaultdict(list)
for c in trap:
    for s in bad_succs[c]:
        if s in trap:
            trap_adj[c].append(s)

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

    for w in trap_adj[v]:
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

# Tarjan's can overflow on 540 nodes, use iterative version
sys.setrecursionlimit(10000)
for v in trap:
    if v not in index:
        strongconnect(v)

print(f"Non-trivial SCCs: {len(sccs)}")
scc_sizes = sorted([len(s) for s in sccs], reverse=True)
print(f"SCC sizes: {scc_sizes[:20]}")

# ============================================================
# Analyze the largest SCC
# ============================================================
if sccs:
    largest = max(sccs, key=len)
    print(f"\nLargest SCC: {len(largest)} configs")

    # Find shortest cycle in largest SCC using BFS
    scc_set = set(largest)
    shortest_cycle = None

    for start in list(scc_set)[:20]:
        # BFS from start, looking for return to start
        visited = {start: [start]}
        queue = [start]
        found = False
        while queue and not found:
            current = queue.pop(0)
            for nxt in trap_adj[current]:
                if nxt == start and len(visited[current]) >= 2:
                    cycle = visited[current]
                    if shortest_cycle is None or len(cycle) < len(shortest_cycle):
                        shortest_cycle = cycle
                    found = True
                    break
                if nxt in scc_set and nxt not in visited:
                    visited[nxt] = visited[current] + [nxt]
                    if len(visited[nxt]) < 50:
                        queue.append(nxt)

    if shortest_cycle:
        print(f"\nShortest cycle found: length {len(shortest_cycle)}")
        for step, cfg in enumerate(shortest_cycle):
            priv = priv_map[cfg]
            nxt = shortest_cycle[(step+1) % len(shortest_cycle)]
            firing_proc = None
            for p in priv:
                s = list(cfg)
                s[p] = f(p, cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
                if tuple(s) == nxt:
                    firing_proc = p
                    break
            print(f"  Step {step:2d}: {cfg} fire P{firing_proc} (priv={priv})")

        # Mover word of shadow cycle
        movers = []
        for step, cfg in enumerate(shortest_cycle):
            nxt = shortest_cycle[(step+1) % len(shortest_cycle)]
            for p in priv_map[cfg]:
                s = list(cfg)
                s[p] = f(p, cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
                if tuple(s) == nxt:
                    movers.append(p)
                    break
        print(f"\n  Shadow mover word: {movers}")
        print(f"  Shadow displacement: {compute_displacement(movers, n)}")
        print(f"  Shadow fire counts: {dict(Counter(movers))}")

# ============================================================
# Key question: is the trap ENTIRELY within dead configs?
# ============================================================
print("\n" + "=" * 72)
print("DEAD CONFIG ANALYSIS")
print("=" * 72)

dead_set = set(dead)
trap_dead = trap & dead_set
trap_live = trap - dead_set
print(f"Trap configs that are dead (no privilege): {len(trap_dead)}")
print(f"Trap configs that are live (have privilege): {len(trap_live)}")

# Wait - dead configs have NO privileged proc, so they can't make any move.
# They shouldn't be in the trap (trap requires the daemon to have a move staying in trap).
# Let's verify.
for c in trap_dead:
    print(f"  Dead in trap: {c}, priv={priv_map[c]}")
    break  # just check one

# Hmm, dead configs have priv=[], so bad_succs[c] is empty, so they can't be in trap.
# Let me re-check.
print(f"\nVerification: trap_dead should be 0: {len(trap_dead)}")

# ============================================================
# What are the privilege patterns in the trap?
# ============================================================
print("\n" + "=" * 72)
print("TRAP PRIVILEGE PATTERNS")
print("=" * 72)

priv_patterns = Counter()
for c in trap:
    priv_patterns[tuple(sorted(priv_map[c]))] += 1

for pat, cnt in priv_patterns.most_common(20):
    print(f"  Priv at procs {pat}: {cnt} configs")

# For each config in trap: check if ALL successors stay in trap,
# or just SOME successors stay in trap
all_stay = 0
some_stay = 0
for c in trap:
    all_in = all(
        any(
            tuple(list(c)[:i] + [f(i, c[(i-1)%n], c[i], c[(i+1)%n])] + list(c)[i+1:]) in trap
            for _ in [None]  # dummy
        )
        for i in priv_map[c]
    )
    # Actually cleaner:
    succs_in = 0
    succs_out = 0
    for i in priv_map[c]:
        s = list(c)
        s[i] = f(i, c[(i-1)%n], c[i], c[(i+1)%n])
        ns = tuple(s)
        if ns in trap:
            succs_in += 1
        else:
            succs_out += 1
    if succs_out == 0:
        all_stay += 1
    else:
        some_stay += 1

print(f"\nAll successors in trap: {all_stay}")
print(f"Some successors leave trap: {some_stay}")

# ============================================================
# The TRUE daemon trap: configs where EVERY move stays bad
# ============================================================
print("\n" + "=" * 72)
print("DAEMON-WINS ANALYSIS (every move stays bad)")
print("=" * 72)

# A config is in the "daemon wins" set if for EVERY privileged proc,
# firing leads to another config in the set.
# This is the STRONGEST trap: the daemon has no escape.

# Start with all bad live configs, iteratively remove those with an escape
daemon_wins = set()
for c in bad_set:
    if priv_map[c]:  # live
        # Check if ALL successors are bad
        all_bad = True
        for i in priv_map[c]:
            s = list(c)
            s[i] = f(i, c[(i-1)%n], c[i], c[(i+1)%n])
            ns = tuple(s)
            if ns in good_set or ns in dead_set:
                all_bad = False
                break
        if all_bad:
            daemon_wins.add(c)

# Now iteratively: remove configs from daemon_wins if any successor leaves daemon_wins
changed = True
while changed:
    changed = False
    to_remove = set()
    for c in daemon_wins:
        # Check: does there exist a successor NOT in daemon_wins?
        for i in priv_map[c]:
            s = list(c)
            s[i] = f(i, c[(i-1)%n], c[i], c[(i+1)%n])
            ns = tuple(s)
            if ns not in daemon_wins:
                to_remove.add(c)
                break
    if to_remove:
        daemon_wins -= to_remove
        changed = True

print(f"Daemon-wins set (all moves stay bad+live): {len(daemon_wins)}")

# Wait, that's not quite right. The daemon WANTS to stay bad.
# A trap for the daemon means: for each config c, there EXISTS a privileged
# proc whose firing leads to another config in the trap.
# That's the original trap definition.

# The STRONGEST version for non-convergence: there exists a cycle
# in the bad graph (daemon can choose moves to cycle forever).
# We already found this in the SCCs.

# But for the PROOF we need something different:
# We need to show that for ANY completion of free table entries,
# convergence fails. The identity fill gives trap=540.
# But the free entries could be filled differently.

# ============================================================
# CRITICAL: Check if trap exists for EXHAUSTIVE fill search
# ============================================================
print("\n" + "=" * 72)
print("EXHAUSTIVE FREE-FILL SEARCH (sampling)")
print("=" * 72)

# How many free entries does each proc have?
free_entries = {}
forced = {}
for p in range(n):
    forced[p] = set()
    free_entries[p] = []

for s in range(ell):
    p = w0[s]
    L = configs_seq[s][(p-1)%n]
    S = configs_seq[s][p]
    R = configs_seq[s][(p+1)%n]
    forced[p].add((L, S, R))

for s in range(ell):
    for q in range(n):
        if q == w0[s]:
            continue
        L = configs_seq[s][(q-1)%n]
        S = configs_seq[s][q]
        R = configs_seq[s][(q+1)%n]
        forced[q].add((L, S, R))

for p in range(n):
    for L in range(ms[(p-1)%n]):
        for S in range(ms[p]):
            for R in range(ms[(p+1)%n]):
                if (L, S, R) not in forced[p]:
                    free_entries[p].append((L, S, R))

total_free = sum(len(free_entries[p]) for p in range(n))
total_choices = 1
for p in range(n):
    for ctx in free_entries[p]:
        total_choices *= ms[p]

print(f"Free entries per proc:")
for p in range(n):
    print(f"  P{p}: {len(free_entries[p])} free entries, m={ms[p]}, choices={ms[p]**len(free_entries[p])}")
print(f"Total free entries: {total_free}")
print(f"Total fill combinations: {total_choices}")

# Can't exhaustively search 2^90 combinations.
# But: let's check if the trap=540 configs are ALWAYS trapped regardless of free entries.

# Key insight: the 540 trap configs - do they ever USE a free table entry?
# If they only use forced entries, then the trap is INDEPENDENT of the fill.

print("\n--- Checking if trap configs use free entries ---")
trap_uses_free = set()
trap_uses_forced = set()

for c in trap:
    for i in priv_map[c]:
        L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
        ctx = (L, S, R)
        if ctx not in forced[i]:
            trap_uses_free.add((c, i, ctx))
        else:
            trap_uses_forced.add((c, i, ctx))

        # Also check the successor config
        s = list(c)
        s[i] = f(i, L, S, R)
        ns = tuple(s)

print(f"Trap privilege evaluations using free entries: {len(trap_uses_free)}")
print(f"Trap privilege evaluations using forced entries: {len(trap_uses_forced)}")

if trap_uses_free:
    print("\nSample free-entry usages in trap:")
    for (c, i, ctx) in list(trap_uses_free)[:10]:
        val = f(i, *ctx)
        print(f"  Config {c}, proc {i}, ctx={ctx}, f={val} (identity -> {ctx[1]})")
        # Under identity fill, f(L,S,R) = S, so proc is NOT privileged.
        # Wait - if f(L,S,R) = S = identity, then proc is NOT privileged there.
        # So free entries with identity fill make the proc non-privileged.
        # But the config IS in the trap, so some OTHER proc must be privileged.
        print(f"    Privileged? {val != ctx[1]} (S={ctx[1]}, f={val})")

# ============================================================
# REAL check: which priv evaluations in the TRAP CYCLE use free entries?
# ============================================================
print("\n" + "=" * 72)
print("TRAP CYCLE ENTRY ANALYSIS")
print("=" * 72)

if sccs:
    # Take shortest cycle
    if shortest_cycle:
        cycle_cfgs = shortest_cycle
        print(f"Analyzing cycle of length {len(cycle_cfgs)}")

        cycle_uses_free = 0
        cycle_uses_forced = 0
        for step, cfg in enumerate(cycle_cfgs):
            nxt = cycle_cfgs[(step+1) % len(cycle_cfgs)]
            # Find which proc fires
            for p in priv_map[cfg]:
                s = list(cfg)
                s[p] = f(p, cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
                if tuple(s) == nxt:
                    ctx = (cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
                    if ctx not in forced[p]:
                        cycle_uses_free += 1
                        print(f"  Step {step}: P{p} ctx={ctx} -> {f(p,*ctx)} [FREE entry]")
                    else:
                        cycle_uses_forced += 1
                        print(f"  Step {step}: P{p} ctx={ctx} -> {f(p,*ctx)} [FORCED]")
                    break

        print(f"\nCycle entries: {cycle_uses_forced} forced, {cycle_uses_free} free")
        if cycle_uses_free == 0:
            print("*** CYCLE USES ONLY FORCED ENTRIES ***")
            print("*** This means the trap cycle is FILL-INDEPENDENT ***")

# ============================================================
# Also check: non-mover constraints in the trap cycle
# ============================================================
print("\n" + "=" * 72)
print("TRAP CYCLE NON-MOVER ANALYSIS")
print("=" * 72)

if sccs and shortest_cycle:
    cycle_cfgs = shortest_cycle
    # For each step in the trap cycle, check that non-movers are stable
    # (they should be, since we're just checking privilege, not ME)
    # But: does the trap cycle have ME=1? That would make it a shadow good cycle.

    for step, cfg in enumerate(cycle_cfgs):
        priv = priv_map[cfg]
        if len(priv) != 1:
            print(f"  Step {step}: {cfg} has {len(priv)} privileged procs: {priv}")

    me_ok = all(len(priv_map[c]) == 1 for c in cycle_cfgs)
    print(f"\nAll configs in trap cycle have ME=1: {me_ok}")

# ============================================================
# Alternative: find cycles with ME=1 in bad set
# ============================================================
print("\n" + "=" * 72)
print("SINGLE-PRIVILEGE BAD CYCLES (daemon-forced)")
print("=" * 72)

# These are the most dangerous: configs with exactly 1 privileged proc
# that cycle among themselves (no daemon choice needed)
sp_bad = {c for c in bad_set if len(priv_map[c]) == 1 and priv_map[c]}
print(f"Single-priv bad configs: {len(sp_bad)}")

# Build deterministic successor
sp_succ = {}
for c in sp_bad:
    p = priv_map[c][0]
    s = list(c)
    s[p] = f(p, c[(p-1)%n], c[p], c[(p+1)%n])
    ns = tuple(s)
    sp_succ[c] = ns

# Find cycles
sp_closed = {c for c in sp_bad if sp_succ[c] in sp_bad}
print(f"SP bad configs with successor in SP bad: {len(sp_closed)}")

# Further: iteratively close
sp_core = set(sp_closed)
changed = True
while changed:
    changed = False
    to_remove = set()
    for c in sp_core:
        if sp_succ[c] not in sp_core:
            to_remove.add(c)
    if to_remove:
        sp_core -= to_remove
        changed = True

print(f"SP bad core (closed under successor): {len(sp_core)}")

if sp_core:
    # Find cycles
    visited = set()
    sp_cycles = []
    for start in sp_core:
        if start in visited:
            continue
        path = [start]
        path_set = {start}
        current = start
        while True:
            nxt = sp_succ[current]
            if nxt in path_set:
                idx = path.index(nxt)
                sp_cycles.append(path[idx:])
                break
            if nxt not in sp_core:
                break
            path.append(nxt)
            path_set.add(nxt)
            current = nxt
        visited.update(path_set)

    print(f"Deterministic cycles in SP bad: {len(sp_cycles)}")
    for ci, cyc in enumerate(sp_cycles[:5]):
        movers = [priv_map[c][0] for c in cyc]
        d = compute_displacement(movers, n)
        fc = Counter(movers)
        print(f"\n  Cycle {ci}: length {len(cyc)}, disp={d}")
        print(f"    Movers: {movers}")
        print(f"    Fire counts: {dict(fc)}")

        # Check if entries are all forced
        uses_free = 0
        for step, cfg in enumerate(cyc):
            p = priv_map[cfg][0]
            ctx = (cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
            if ctx not in forced[p]:
                uses_free += 1
        print(f"    Uses free entries: {uses_free}")

        if len(cyc) <= 30:
            for step, cfg in enumerate(cyc):
                p = priv_map[cfg][0]
                ctx = (cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
                is_free = "FREE" if ctx not in forced[p] else "FORCD"
                print(f"      Step {step:2d}: {cfg} fire P{p} ctx={ctx} [{is_free}]")

print("\n" + "=" * 72)
print("DONE")
print("=" * 72)
