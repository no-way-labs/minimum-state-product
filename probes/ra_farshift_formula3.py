#!/usr/bin/env python3
"""
RA Part 3: Understand the forced-entry bad cycle structure.

Key finding: same-mover bad cycles DON'T EXIST with forced entries.
The actual bad cycle has DIFFERENT movers from the good cycle.

New question: What IS the structure of the forced-entry bad cycle?
- What movers does it use?
- Is there a formula for the bad configs?
- Is the bad cycle related to a DIFFERENT good cycle?

Also: the Lean doesn't require same movers for BadCycleData - let me re-check.
"""

import itertools
from collections import defaultdict

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

def get_good_cycle_with_combo(ms, n, word, combo):
    ell = len(word)
    fc_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        fc_num[s] = pc[word[s]]
        pc[word[s]] += 1
    configs = []
    state = [0]*n
    for s in range(ell):
        configs.append(tuple(state))
        p = word[s]
        state[p] = combo[p][fc_num[s]+1]
    return configs, fc_num

# ============================================================
# Setup: n=7 (smaller, faster)
# ============================================================
n = 7
ms = [2,3,3,2,3,3,2]
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
sweeps = [(w, c, compute_displacement(w, n)) for w, c in valid if abs(compute_displacement(w, n)) == 2*n]

print(f"n={n}, ms={ms}, sweeps={len(sweeps)}")

w0, _, d0 = sweeps[0]
ell = len(w0)
combo0 = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))
gc_configs, fc_num = get_good_cycle_with_combo(ms, n, w0, combo0)
good_set = set(gc_configs)

print(f"Mover word: {list(w0)}")
print(f"Cycle length: {ell}")

# Build forced mover entries
mcx = defaultdict(dict)
for s in range(ell):
    p = w0[s]
    L = gc_configs[s][(p-1)%n]; S = gc_configs[s][p]; R = gc_configs[s][(p+1)%n]
    mcx[p][(L, S, R)] = gc_configs[(s+1)%ell][p]

print(f"Forced entries:")
for p in sorted(mcx.keys()):
    print(f"  P{p} (m={ms[p]}): {dict(mcx[p])}")

# ============================================================
# Build forced-entry graph (ANY mover, not just same movers)
# ============================================================
all_cfgs = list(itertools.product(*(range(m) for m in ms)))
non_good = set(c for c in all_cfgs if c not in good_set)

forced_adj = defaultdict(list)
for c in non_good:
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if (L, S, R) in mcx[p]:
            Sp = mcx[p][(L, S, R)]
            if Sp != S:
                nc = list(c); nc[p] = Sp; nc = tuple(nc)
                if nc in non_good:
                    forced_adj[c].append((nc, p))

# Find trap
trap = set(c for c in forced_adj if forced_adj[c])
changed = True
while changed:
    changed = False
    to_remove = set()
    for c in trap:
        if not any(nc in trap for nc, p in forced_adj[c]):
            to_remove.add(c)
    if to_remove:
        trap -= to_remove
        changed = True

print(f"\nTrap size: {len(trap)}")

# Find ALL cycles of length ell in the trap using DFS
# (too expensive for large trap, but n=7 is small)
# Instead, find shortest cycle from each starting config
print(f"\nSearching for cycles of length {ell}...")

# BFS from each trap config, looking for return to start
cycles_found = []
for start in list(trap)[:100]:  # Sample
    visited = {start: ([], [])}
    queue = [start]
    found = False
    while queue and not found:
        cur = queue.pop(0)
        for nxt, p in forced_adj[cur]:
            if nxt not in trap:
                continue
            if nxt == start and visited[cur][0]:
                path = visited[cur][0] + [cur]
                movers = visited[cur][1] + [p]
                if len(path) == ell:
                    cycles_found.append((path, movers))
                    found = True
                    break
                elif len(path) < ell:
                    # Keep searching for length-ell cycle
                    pass
            if nxt not in visited:
                visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
                if len(visited[nxt][0]) < ell:
                    queue.append(nxt)

    if found:
        break

print(f"Cycles of length {ell} found: {len(cycles_found)}")

# Try BFS for shortest cycle (any length)
start = list(trap)[0]
visited = {start: ([], [])}
queue = [start]
shortest = None
while queue:
    cur = queue.pop(0)
    for nxt, p in forced_adj[cur]:
        if nxt == start and visited[cur][0]:
            path = visited[cur][0] + [cur]
            movers = visited[cur][1] + [p]
            if shortest is None or len(path) < len(shortest):
                shortest = path
                break
        if nxt in trap and nxt not in visited:
            visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
            if len(visited[nxt][0]) < 40:
                queue.append(nxt)

if shortest:
    # Extract the shortest cycle
    movers_sh = visited[shortest[-1]][1] + [None]  # need to reconstruct
    # Actually let me redo BFS properly
    pass

# Simpler: just find ALL short cycles
print(f"\nExhaustive cycle search in trap...")

# Find strongly connected components
import sys
sys.setrecursionlimit(10000)

def tarjan_scc(nodes, adj):
    idx = [0]
    stack = []
    on_stack = set()
    index = {}
    lowlink = {}
    sccs = []

    def strongconnect(v):
        index[v] = lowlink[v] = idx[0]
        idx[0] += 1
        stack.append(v)
        on_stack.add(v)

        for w, _ in adj.get(v, []):
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
            sccs.append(scc)

    for v in nodes:
        if v not in index:
            strongconnect(v)

    return sccs

sccs = tarjan_scc(trap, forced_adj)
nontrivial = [s for s in sccs if len(s) > 1]
print(f"SCCs: {len(sccs)}, nontrivial: {len(nontrivial)}")
for i, scc in enumerate(nontrivial[:5]):
    print(f"  SCC {i}: size {len(scc)}")

# For the largest SCC, find a cycle
if nontrivial:
    scc0 = set(nontrivial[0])
    # Find cycle using DFS
    start = nontrivial[0][0]
    # BFS for shortest cycle
    visited = {start: ([], [])}
    queue = [start]
    best_cycle = None
    best_movers = None
    while queue:
        cur = queue.pop(0)
        for nxt, p in forced_adj[cur]:
            if nxt not in scc0:
                continue
            if nxt == start and visited[cur][0]:
                path = visited[cur][0] + [cur]
                movers = visited[cur][1] + [p]
                if best_cycle is None or len(path) < len(best_cycle):
                    best_cycle = path
                    best_movers = movers
                continue
            if nxt not in visited:
                visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
                if len(visited[nxt][0]) < ell + 5:
                    queue.append(nxt)

    if best_cycle:
        print(f"\nShortest cycle: length {len(best_cycle)}")
        print(f"  Movers: {best_movers}")
        print(f"  Good movers: {list(w0)}")

        # Print full cycle
        for s in range(len(best_cycle)):
            gc_s = gc_configs[s % ell] if s < ell else "N/A"
            d = tuple((best_cycle[s][p] - gc_configs[s % ell][p]) % ms[p] for p in range(n)) if s < ell else "N/A"
            print(f"  b[{s:2d}] = {best_cycle[s]}  fire P{best_movers[s]}  good={gc_s}  offset={d}")

# ============================================================
# KEY QUESTION: Is the bad cycle a ROTATION of the good cycle?
# ============================================================
print(f"\n{'='*72}")
print("PART 2: Is bad cycle a rotation/reflection of good cycle?")
print("="*72)

if best_cycle and len(best_cycle) == ell:
    # Check if bad configs = {good configs rotated}
    bad_set = set(map(tuple, best_cycle))
    good_set_configs = set(gc_configs)
    print(f"Bad ∩ Good: {len(bad_set & good_set_configs)}")
    print(f"|Bad|: {len(bad_set)}, |Good|: {len(good_set_configs)}")

    # Check if bad cycle is a good cycle for a DIFFERENT mover word
    bad_word = tuple(best_movers)
    print(f"\nBad mover word: {bad_word}")
    # Check if this is a valid mover word (ring walk, all procs fire m_p times)
    fc_bad = [0]*n
    for p in bad_word:
        fc_bad[p] += 1
    print(f"Fire counts: {fc_bad} vs ms: {ms}")
    fc_match = all(fc_bad[p] == ms[p] for p in range(n))
    print(f"Fire count match: {fc_match}")

    # Check ring adjacency
    ring_ok = True
    for s in range(len(bad_word)):
        p = bad_word[s]
        q = bad_word[(s+1) % len(bad_word)]
        if abs(p - q) % n not in (1, n-1):
            ring_ok = False
            break
    print(f"Ring adjacency: {ring_ok}")

    if fc_match and ring_ok:
        print(f"Bad mover word IS a valid ring walk with correct fire counts!")
        disp = compute_displacement(list(bad_word), n)
        print(f"Displacement: {disp} (sweep needs {2*n} or {-2*n})")

        # Is it one of our known sweep words?
        bad_canon = canonicalize_word(bad_word)
        for wi, (w, _, d) in enumerate(sweeps):
            if canonicalize_word(w) == bad_canon:
                print(f"  MATCH: bad word = sweep {wi} (rotation)")
                break
        else:
            # Check non-sweeps too
            for wi, (w, c) in enumerate(valid):
                if canonicalize_word(w) == bad_canon:
                    print(f"  MATCH: bad word = valid cycle {wi} (rotation)")
                    break
            else:
                print(f"  No match among known valid cycle words")

# ============================================================
# PART 3: Look at ALL forced-entry bad cycles
# ============================================================
print(f"\n{'='*72}")
print("PART 3: ALL forced-entry cycles in trap")
print("="*72)

# Find all cycles by exploring orbits
all_cycles = []
remaining = set(trap)
while remaining:
    start = next(iter(remaining))
    # Follow one path from start
    visited_order = [start]
    visited_set = {start}
    cur = start
    found_cycle = False
    while True:
        # Pick first available successor in trap
        succ = None
        succ_p = None
        for nxt, p in forced_adj[cur]:
            if nxt in trap:
                succ = nxt
                succ_p = p
                break
        if succ is None:
            break
        if succ in visited_set:
            # Found a cycle
            idx = visited_order.index(succ)
            cycle_configs = visited_order[idx:]
            # Get movers
            cycle_movers = []
            for i in range(len(cycle_configs)):
                c = cycle_configs[i]
                nc = cycle_configs[(i+1) % len(cycle_configs)]
                for nxt, p in forced_adj[c]:
                    if nxt == nc:
                        cycle_movers.append(p)
                        break
            all_cycles.append((cycle_configs, cycle_movers))
            remaining -= set(cycle_configs)
            found_cycle = True
            break
        visited_order.append(succ)
        visited_set.add(succ)
        cur = succ

    if not found_cycle:
        remaining.discard(start)

print(f"Cycles found: {len(all_cycles)}")
for i, (cyc, mov) in enumerate(all_cycles):
    fc = [0]*n
    for p in mov:
        fc[p] += 1
    disp = compute_displacement(list(mov), n) if len(mov) > 0 else 0
    print(f"  Cycle {i}: len={len(cyc)}, movers={mov[:10]}{'...' if len(mov)>10 else ''}, fc={fc}, disp={disp}")

# ============================================================
# PART 4: The correct approach - ANY-mover BadCycleData
# ============================================================
print(f"\n{'='*72}")
print("PART 4: BadCycleData with free movers")
print("="*72)

# Re-read the Lean BadCycleData structure
# It has: cfg, mover, disjoint, priv, step, distinct
# The mover can be ANYTHING, not necessarily same as good cycle.
# So we need:
# 1. cfg: Fin L -> Config
# 2. mover: Fin L -> Fin n
# 3. ∀ k, cfg k ∉ gc.configs
# 4. ∀ k, privileged (cfg k) (mover k)
# 5. ∀ k, move (cfg k) (mover k) = cfg (k+1)
# 6. ∀ a b, cfg a = cfg b → a = b

# The Lean currently has: mover := fun k => gc.moverAt k (SAME movers)
# This is WRONG based on our finding. The mover should be free.

# Let me verify the bad cycle we found satisfies all properties.
if best_cycle:
    print(f"\nVerifying BadCycleData for shortest cycle (len={len(best_cycle)}):")

    # Disjoint
    disjoint = all(tuple(c) not in good_set for c in best_cycle)
    print(f"  disjoint: {disjoint}")

    # Distinct
    distinct = len(set(map(tuple, best_cycle))) == len(best_cycle)
    print(f"  distinct: {distinct}")

    # Priv + Step
    priv_ok = True
    step_ok = True
    for s in range(len(best_cycle)):
        p = best_movers[s]
        c = best_cycle[s]
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]

        # Priv: (L,S,R) is in forced table and S' != S
        if (L, S, R) not in mcx[p]:
            priv_ok = False
            print(f"  PRIV FAIL at step {s}: P{p} ctx=({L},{S},{R}) not forced")
            break
        Sp = mcx[p][(L, S, R)]
        if Sp == S:
            priv_ok = False
            print(f"  PRIV FAIL at step {s}: P{p} ctx=({L},{S},{R}) -> {Sp} = S")
            break

        # Step: firing gives next
        nc = list(c); nc[p] = Sp; nc = tuple(nc)
        expected = tuple(best_cycle[(s+1) % len(best_cycle)])
        if nc != expected:
            step_ok = False
            print(f"  STEP FAIL at step {s}: got {nc}, expected {expected}")
            break

    print(f"  priv: {priv_ok}")
    print(f"  step: {step_ok}")
    print(f"  VALID BadCycleData: {disjoint and distinct and priv_ok and step_ok}")

# ============================================================
# PART 5: Universal check - all sweeps x all combos at n=7
# ============================================================
print(f"\n{'='*72}")
print("PART 5: Universal verification at n=7")
print("="*72)

all_combos = list(itertools.product(*[enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]))
print(f"Sweeps: {len(sweeps)}, Combos: {len(all_combos)}, Total: {len(sweeps) * len(all_combos)}")

pass_count = 0
fail_count = 0
cycle_lengths = defaultdict(int)

for wi, (word, _, disp) in enumerate(sweeps):
    for ci, combo in enumerate(all_combos):
        gc, fc = get_good_cycle_with_combo(ms, n, word, combo)
        gs = set(gc)

        mx = defaultdict(dict)
        for s in range(len(word)):
            p = word[s]
            L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
            mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

        # Build forced-entry graph
        fa = defaultdict(list)
        for c in all_cfgs:
            if c in gs: continue
            for p in range(n):
                L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
                if (L, S, R) in mx[p]:
                    Sp = mx[p][(L, S, R)]
                    if Sp != S:
                        nc = list(c); nc[p] = Sp; nc = tuple(nc)
                        if nc not in gs:
                            fa[c].append((nc, p))

        # Find trap
        tr = set(c for c in fa if fa[c])
        ch = True
        while ch:
            ch = False
            rem = set()
            for c in tr:
                if not any(nc in tr for nc, p_ in fa[c]):
                    rem.add(c)
            if rem:
                tr -= rem
                ch = True

        if tr:
            pass_count += 1
            cycle_lengths[len(tr)] += 1
        else:
            fail_count += 1
            print(f"  FAIL: sweep {wi}, combo {ci}")

print(f"Pass: {pass_count}, Fail: {fail_count}")
print(f"Trap sizes: {dict(cycle_lengths)}")

# ============================================================
# PART 6: The key structural insight
# ============================================================
print(f"\n{'='*72}")
print("PART 6: Structural analysis of bad cycle")
print("="*72)

# The bad cycle has different movers from the good cycle.
# What's the relationship? Is the bad cycle the forced-entry orbit
# of a specific starting config? Or is there a pattern?

# Let me look at what happens if we just pick ONE non-good config
# and follow the forced entries (picking any available forced transition).
w0, _, _ = sweeps[0]
gc_configs, _ = get_good_cycle_with_combo(ms, n, w0, combo0)
good_set = set(gc_configs)

mcx = defaultdict(dict)
for s in range(len(w0)):
    p = w0[s]
    L = gc_configs[s][(p-1)%n]; S = gc_configs[s][p]; R = gc_configs[s][(p+1)%n]
    mcx[p][(L, S, R)] = gc_configs[(s+1)%len(w0)][p]

# For each non-good config, count how many forced transitions are available
trans_count = defaultdict(int)
for c in all_cfgs:
    if c in good_set: continue
    cnt = 0
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if (L, S, R) in mcx[p]:
            Sp = mcx[p][(L, S, R)]
            if Sp != S:
                nc = list(c); nc[p] = Sp; nc = tuple(nc)
                if nc not in good_set:
                    cnt += 1
    trans_count[cnt] += 1

print(f"Non-good configs by # forced transitions available:")
for cnt in sorted(trans_count.keys()):
    print(f"  {cnt} transitions: {trans_count[cnt]} configs")

# What procs are available as movers at each config in the bad cycle?
if best_cycle:
    print(f"\nBad cycle mover analysis:")
    for s in range(len(best_cycle)):
        c = best_cycle[s]
        available = []
        for p in range(n):
            L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
            if (L, S, R) in mcx[p]:
                Sp = mcx[p][(L, S, R)]
                if Sp != S:
                    nc = list(c); nc[p] = Sp; nc = tuple(nc)
                    if nc not in good_set:
                        available.append(p)
        chosen = best_movers[s]
        print(f"  b[{s:2d}] = {c}  available={available}  chosen=P{chosen}")
