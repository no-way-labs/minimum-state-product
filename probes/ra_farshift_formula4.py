#!/usr/bin/env python3
"""
RA Part 4: Focused analysis of forced-entry bad cycles.

Key findings so far:
1. Constant offset does NOT work
2. Same-mover bad cycles do NOT exist with forced entries
3. The Lean's `mover := fun k => gc.moverAt k` is wrong

Strategy: Work at n=7 with a lean, focused approach.
Build forced-entry graph, find cycles via orbit tracing.
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
# n=7
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

w0, _, d0 = sweeps[0]
ell = len(w0)
combo0 = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))
gc_configs, _ = get_good_cycle_with_combo(ms, n, w0, combo0)
good_set = set(gc_configs)

# Forced mover entries
mcx = defaultdict(dict)
for s in range(ell):
    p = w0[s]
    L = gc_configs[s][(p-1)%n]; S = gc_configs[s][p]; R = gc_configs[s][(p+1)%n]
    mcx[p][(L, S, R)] = gc_configs[(s+1)%ell][p]

print(f"n={n}, ms={ms}")
print(f"Mover word: {list(w0)}")
print(f"Cycle length: {ell}")
print(f"Good configs: {ell}")
print(f"Forced entries:")
for p in sorted(mcx.keys()):
    print(f"  P{p}: {dict(mcx[p])}")

# Build forced-entry graph (any mover)
all_cfgs = list(itertools.product(*(range(m) for m in ms)))
non_good = [c for c in all_cfgs if c not in good_set]

# For each non-good config, find all forced transitions
adj = {}  # c -> [(nc, p), ...]
for c in non_good:
    edges = []
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if (L, S, R) in mcx[p]:
            Sp = mcx[p][(L, S, R)]
            if Sp != S:
                nc = list(c); nc[p] = Sp; nc = tuple(nc)
                if nc not in good_set:
                    edges.append((nc, p))
    if edges:
        adj[c] = edges

# Find cycles by orbit tracing (follow first available edge)
visited_global = set()
cycles = []

for start_c in adj:
    if start_c in visited_global:
        continue
    # Follow first-edge orbit
    path = [start_c]
    path_set = {start_c}
    cur = start_c
    movers = []
    while cur in adj:
        nxt, p = adj[cur][0]  # First edge
        movers.append(p)
        if nxt in path_set:
            # Found cycle
            idx = path.index(nxt)
            cyc = path[idx:]
            cyc_movers = movers[idx:]
            cycles.append((cyc, cyc_movers))
            visited_global.update(cyc)
            break
        if nxt in visited_global:
            break
        path.append(nxt)
        path_set.add(nxt)
        cur = nxt

print(f"\nCycles found: {len(cycles)}")
lens = [len(c) for c, m in cycles]
from collections import Counter
print(f"Length distribution: {Counter(lens)}")

# Show all cycles
for i, (cyc, mov) in enumerate(cycles):
    fc = [0]*n
    for p in mov:
        fc[p] += 1
    print(f"  Cycle {i}: len={len(cyc)}, fc={fc}, movers={mov}")

# ============================================================
# DETAILED ANALYSIS of the first cycle
# ============================================================
if cycles:
    cyc, mov = cycles[0]
    print(f"\n{'='*72}")
    print(f"DETAILED CYCLE ANALYSIS (cycle 0, len={len(cyc)})")
    print(f"{'='*72}")

    for s in range(len(cyc)):
        c = cyc[s]
        p = mov[s]
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        Sp = mcx[p][(L, S, R)]
        # Find closest good config
        gc_s = None
        for gs_idx in range(ell):
            if gc_configs[gs_idx] == c:
                gc_s = gs_idx
                break
        print(f"  [{s:2d}] {c}  fire P{p} ({L},{S},{R})->{Sp}  good_match={'Y:'+str(gc_s) if gc_s is not None else 'N'}")

    # Check: is bad cycle configs = good cycle configs with some procs shifted?
    # Look at position-wise values
    print(f"\n  Position-wise comparison with good cycle:")
    print(f"  {'Step':>4} {'Bad':>20} {'Good[0]':>20} {'Diff':>20}")
    for s in range(min(len(cyc), ell)):
        diff = tuple((cyc[s][p] - gc_configs[s][p]) % ms[p] for p in range(n))
        print(f"  {s:4d} {str(cyc[s]):>20} {str(gc_configs[s]):>20} {str(diff):>20}")

# ============================================================
# UNIVERSALITY CHECK at n=7
# ============================================================
print(f"\n{'='*72}")
print(f"UNIVERSALITY CHECK: n=7, all sweeps x combos")
print(f"{'='*72}")

all_combos = list(itertools.product(*[enumerate_state_sequences(ms[p], ms[p]) for p in range(n)]))
print(f"Sweeps: {len(sweeps)}, Combos: {len(all_combos)}")

pass_count = 0
fail_count = 0

for wi, (word, _, disp) in enumerate(sweeps):
    for ci, combo in enumerate(all_combos):
        gc, _ = get_good_cycle_with_combo(ms, n, word, combo)
        gs = set(gc)

        mx = defaultdict(dict)
        for s in range(len(word)):
            p = word[s]
            L = gc[s][(p-1)%n]; S = gc[s][p]; R = gc[s][(p+1)%n]
            mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

        # Build graph
        has_cycle = False
        local_adj = {}
        for c in all_cfgs:
            if c in gs: continue
            edges = []
            for p in range(n):
                L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
                if (L, S, R) in mx[p]:
                    Sp = mx[p][(L, S, R)]
                    if Sp != S:
                        nc = list(c); nc[p] = Sp; nc = tuple(nc)
                        if nc not in gs:
                            edges.append((nc, p))
            if edges:
                local_adj[c] = edges

        # Quick cycle check: follow first edges, look for revisit
        visited = set()
        for start in local_adj:
            if start in visited:
                continue
            path_set = {start}
            cur = start
            found = False
            for _ in range(100):
                if cur not in local_adj:
                    break
                nxt, _ = local_adj[cur][0]
                if nxt in path_set:
                    has_cycle = True
                    found = True
                    break
                if nxt in visited:
                    break
                path_set.add(nxt)
                cur = nxt
            visited.update(path_set)
            if found:
                break

        if has_cycle:
            pass_count += 1
        else:
            fail_count += 1
            print(f"  FAIL: sweep {wi}, combo {ci}")

print(f"Pass: {pass_count}/{pass_count + fail_count}")

# ============================================================
# n=9 CHECK
# ============================================================
print(f"\n{'='*72}")
print(f"UNIVERSALITY CHECK: n=9")
print(f"{'='*72}")

n9 = 9
ms9 = [2,3,3,2,3,3,2,3,3]
target_fc9 = {p: ms9[p] for p in range(n9)}
words9 = enumerate_exact_fc_words(ms9, n9, target_fc9)
seen9 = set()
unique9 = []
for w in words9:
    canon = canonicalize_word(w)
    if canon not in seen9:
        seen9.add(canon)
        unique9.append(w)
valid9 = []
for w in unique9:
    cycle = build_cycle(ms9, n9, w)
    if cycle is not None:
        valid9.append((w, cycle))
sweeps9 = [(w, c, compute_displacement(w, n9)) for w, c in valid9 if abs(compute_displacement(w, n9)) == 2*n9]

all_cfgs9 = list(itertools.product(*(range(m) for m in ms9)))
all_combos9 = list(itertools.product(*[enumerate_state_sequences(ms9[p], ms9[p]) for p in range(n9)]))
print(f"Sweeps: {len(sweeps9)}, Combos: {len(all_combos9)}")

pass9 = 0
fail9 = 0
for wi, (word, _, disp) in enumerate(sweeps9):
    for ci, combo in enumerate(all_combos9):
        gc, _ = get_good_cycle_with_combo(ms9, n9, word, combo)
        gs = set(gc)

        mx = defaultdict(dict)
        for s in range(len(word)):
            p = word[s]
            L = gc[s][(p-1)%n9]; S = gc[s][p]; R = gc[s][(p+1)%n9]
            mx[p][(L, S, R)] = gc[(s+1)%len(word)][p]

        local_adj = {}
        for c in all_cfgs9:
            if c in gs: continue
            edges = []
            for p in range(n9):
                L = c[(p-1)%n9]; S = c[p]; R = c[(p+1)%n9]
                if (L, S, R) in mx[p]:
                    Sp = mx[p][(L, S, R)]
                    if Sp != S:
                        nc = list(c); nc[p] = Sp; nc = tuple(nc)
                        if nc not in gs:
                            edges.append((nc, p))
            if edges:
                local_adj[c] = edges

        visited = set()
        has_cycle = False
        for start in local_adj:
            if start in visited: continue
            path_set = {start}
            cur = start
            for _ in range(200):
                if cur not in local_adj: break
                nxt, _ = local_adj[cur][0]
                if nxt in path_set:
                    has_cycle = True
                    break
                if nxt in visited: break
                path_set.add(nxt)
                cur = nxt
            visited.update(path_set)
            if has_cycle: break

        if has_cycle:
            pass9 += 1
        else:
            fail9 += 1
            print(f"  FAIL: sweep {wi}, combo {ci}")

print(f"Pass: {pass9}/{pass9 + fail9}")
