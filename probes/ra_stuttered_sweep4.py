#!/usr/bin/env python3
"""
RA Part 4: Understand the MECHANISM of the forced bad cycle.

KEY DISCOVERY: The bad cycle reuses ALL good cycle mover entries (24/24).
This means every step of the bad cycle fires a proc at the SAME (L,S,R) context
as some step in the good cycle, but the config is DIFFERENT (other procs differ).

This is the SHADOW CYCLE phenomenon, but at the level of forced entries rather
than at the word level. Let me understand exactly:
1. Why do the mover contexts from the good cycle appear at non-good configs?
2. Is this because the stuttered sweep uses only a small set of mover contexts?
3. Can we characterize WHICH non-good configs inherit the forced privilege?
"""

import sys
import itertools
from collections import Counter, defaultdict

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
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
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
sweeps = [(w, c, compute_displacement(w, n)) for w, c in valid if abs(compute_displacement(w, n)) == 2*n]

w0, cycle0, disp0 = sweeps[0]
ell = len(w0)
combo = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))

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

# Extract forced mover entries
mover_entries = {}  # (proc, L, S, R) -> S'
for s in range(ell):
    p = w0[s]
    L = configs_seq[s][(p-1)%n]
    S = configs_seq[s][p]
    R = configs_seq[s][(p+1)%n]
    S_new = combo[p][firing_num[s]+1]
    mover_entries[(p, L, S, R)] = S_new

print("=" * 72)
print("MOVER CONTEXT ANALYSIS")
print("=" * 72)

print(f"\nGood cycle word: {list(w0)}")
print(f"\nForced mover entries ({len(mover_entries)}):")
for (p, L, S, R), Sp in sorted(mover_entries.items()):
    print(f"  P{p}: ({L},{S},{R}) -> {Sp}")

# Group by processor
mover_by_proc = defaultdict(list)
for (p, L, S, R), Sp in mover_entries.items():
    mover_by_proc[p].append(((L, S, R), Sp))

print("\nGrouped by processor:")
for p in range(n):
    entries = mover_by_proc[p]
    print(f"\n  P{p} (m={ms[p]}): {len(entries)} mover entries")
    for (ctx, sp) in entries:
        print(f"    ({ctx[0]},{ctx[1]},{ctx[2]}) -> {sp}")

# ============================================================
# KEY: How many total contexts does each proc have?
# And how many are used as mover contexts?
# ============================================================
print("\n" + "=" * 72)
print("CONTEXT COVERAGE")
print("=" * 72)

for p in range(n):
    total_ctxs = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
    mover_ctxs = len(mover_by_proc[p])
    print(f"  P{p}: {mover_ctxs}/{total_ctxs} contexts used as mover "
          f"({100*mover_ctxs/total_ctxs:.0f}%)")

# ============================================================
# The bad cycle: show the RELATIONSHIP to the good cycle
# ============================================================
print("\n" + "=" * 72)
print("GOOD vs BAD CYCLE COMPARISON")
print("=" * 72)

# Reconstruct the bad cycle from script 2
# Build tables with identity fill
tables = {}
for p in range(n):
    tables[p] = {}
for s in range(ell):
    p = w0[s]
    L = configs_seq[s][(p-1)%n]; S = configs_seq[s][p]; R = configs_seq[s][(p+1)%n]
    tables[p][(L, S, R)] = combo[p][firing_num[s]+1]
for s in range(ell):
    for q in range(n):
        if q == w0[s]: continue
        L = configs_seq[s][(q-1)%n]; S = configs_seq[s][q]; R = configs_seq[s][(q+1)%n]
        if (L, S, R) not in tables[q]:
            tables[q][(L, S, R)] = S
for p in range(n):
    for L in range(ms[(p-1)%n]):
        for S in range(ms[p]):
            for R in range(ms[(p+1)%n]):
                if (L, S, R) not in tables[p]:
                    tables[p][(L, S, R)] = S

def f(p, L, S, R):
    return tables[p][(L, S, R)]

# Build forced-privilege graph for bad configs
all_cfgs = list(itertools.product(*(range(m) for m in ms)))

# For each non-good config, find forced privileges
mover_ctx_lookup = defaultdict(dict)
for (p, L, S, R), Sp in mover_entries.items():
    mover_ctx_lookup[p][(L, S, R)] = Sp

forced_adj = defaultdict(list)
for c in all_cfgs:
    if c in good_set:
        continue
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        ctx = (L, S, R)
        if ctx in mover_ctx_lookup[p]:
            Sp = mover_ctx_lookup[p][ctx]
            if Sp != S:
                nc = list(c)
                nc[p] = Sp
                nc = tuple(nc)
                if nc not in good_set:
                    forced_adj[c].append((nc, p))

# Find cycle using BFS from a config in the trap
# First find the trap
trap_candidates = set(c for c in forced_adj if forced_adj[c])
changed = True
while changed:
    changed = False
    to_remove = set()
    for c in trap_candidates:
        if not any(nc in trap_candidates for nc, p in forced_adj[c]):
            to_remove.add(c)
    if to_remove:
        trap_candidates -= to_remove
        changed = True

# Find short cycle
start = next(iter(trap_candidates))
visited = {start: ([], [])}
queue = [start]
shortest = None
shortest_movers = None
while queue:
    current = queue.pop(0)
    for nxt, p in forced_adj[current]:
        if nxt == start and visited[current][0]:
            path = visited[current][0] + [current]
            movers = visited[current][1] + [p]
            if shortest is None or len(path) < len(shortest):
                shortest = path
                shortest_movers = movers
            break
        if nxt in trap_candidates and nxt not in visited:
            visited[nxt] = (visited[current][0] + [current], visited[current][1] + [p])
            if len(visited[nxt][0]) < 30:
                queue.append(nxt)

if shortest:
    print(f"\nGood cycle ({ell} steps):")
    for s in range(ell):
        p = w0[s]
        ctx = (configs_seq[s][(p-1)%n], configs_seq[s][p], configs_seq[s][(p+1)%n])
        print(f"  Step {s:2d}: {configs_seq[s]} fire P{p} ctx={ctx}")

    print(f"\nBad cycle ({len(shortest)} steps):")
    for step in range(len(shortest)):
        cfg = shortest[step]
        p = shortest_movers[step]
        ctx = (cfg[(p-1)%n], cfg[p], cfg[(p+1)%n])
        # Find which good step has same (proc, ctx)
        matching_good = None
        for s in range(ell):
            if w0[s] == p:
                gctx = (configs_seq[s][(p-1)%n], configs_seq[s][p], configs_seq[s][(p+1)%n])
                if gctx == ctx:
                    matching_good = s
                    break
        print(f"  Step {step:2d}: {cfg} fire P{p} ctx={ctx} [matches good step {matching_good}]")

    # Show the DIFFERENCE between good and bad configs at matching steps
    print(f"\nConfig differences (bad - good) at matching steps:")
    for step in range(len(shortest)):
        cfg_bad = shortest[step]
        p = shortest_movers[step]
        ctx_bad = (cfg_bad[(p-1)%n], cfg_bad[p], cfg_bad[(p+1)%n])
        for s in range(ell):
            if w0[s] == p:
                gctx = (configs_seq[s][(p-1)%n], configs_seq[s][p], configs_seq[s][(p+1)%n])
                if gctx == ctx_bad:
                    cfg_good = configs_seq[s]
                    diff = tuple((b-g) % ms[i] for i, (b, g) in enumerate(zip(cfg_bad, cfg_good)))
                    differing = [i for i in range(n) if diff[i] != 0]
                    print(f"  Step {step:2d} (good {s:2d}): "
                          f"differ at procs {differing}, "
                          f"diff={diff}")
                    break

# ============================================================
# The shadow offset pattern
# ============================================================
print("\n" + "=" * 72)
print("SHADOW OFFSET PATTERN")
print("=" * 72)

# For each bad cycle config, compute its offset from the matching good config
offsets = []
for step in range(len(shortest)):
    cfg_bad = shortest[step]
    p = shortest_movers[step]
    ctx_bad = (cfg_bad[(p-1)%n], cfg_bad[p], cfg_bad[(p+1)%n])
    for s in range(ell):
        if w0[s] == p:
            gctx = (configs_seq[s][(p-1)%n], configs_seq[s][p], configs_seq[s][(p+1)%n])
            if gctx == ctx_bad:
                cfg_good = configs_seq[s]
                offset = tuple((b-g) % ms[i] for i, (b, g) in enumerate(zip(cfg_bad, cfg_good)))
                offsets.append((step, s, offset, p))
                break

print("Bad step -> Good step mapping and offsets:")
for step, gs, offset, p in offsets:
    print(f"  Bad {step:2d} -> Good {gs:2d} (fire P{p}): offset = {offset}")

# Check if offset is constant
unique_offsets = set(o for _, _, o, _ in offsets)
print(f"\nUnique offsets: {len(unique_offsets)}")
for o in sorted(unique_offsets):
    count = sum(1 for _, _, oo, _ in offsets if oo == o)
    print(f"  {o}: appears {count} times")

# ============================================================
# Check: is this a constant-offset shadow?
# ============================================================
print("\n" + "=" * 72)
print("CONSTANT OFFSET CHECK")
print("=" * 72)

if len(unique_offsets) == 1:
    d = list(unique_offsets)[0]
    print(f"YES! The bad cycle is a constant-offset shadow of the good cycle.")
    print(f"Offset: d = {d}")
    print(f"shadow[t] = good[sigma(t)] + d mod ms")
else:
    print(f"NOT a constant offset. {len(unique_offsets)} different offsets.")

    # Is there a pattern? Maybe it's piecewise constant?
    # Group consecutive steps with same offset
    print("\nOffset sequence:")
    prev = None
    for step, gs, offset, p in offsets:
        if offset != prev:
            print(f"  Steps {step}+: offset = {offset}")
            prev = offset

# ============================================================
# Check at n=7 too
# ============================================================
print("\n" + "=" * 72)
print("SAME ANALYSIS AT n=7")
print("=" * 72)

n7 = 7
ms7 = [2,3,3,2,3,3,2]
target7 = {p: ms7[p] for p in range(n7)}
words7 = enumerate_exact_fc_words(ms7, n7, target7)
seen7 = set()
for w in words7:
    c = canonicalize_word(w)
    if c not in seen7:
        seen7.add(c)
valid7 = []
for w in seen7:
    cyc = build_cycle(ms7, n7, w)
    if cyc is not None:
        valid7.append((w, cyc))
sweeps7 = [(w, c, compute_displacement(w, n7)) for w, c in valid7 if abs(compute_displacement(w, n7)) == 2*n7]

if sweeps7:
    w7, cyc7, d7 = sweeps7[0]
    combo7 = tuple(enumerate_state_sequences(ms7[p], ms7[p])[0] for p in range(n7))
    ell7 = len(w7)

    fc7 = [0]*ell7
    pc7 = [0]*n7
    for s in range(ell7):
        fc7[s] = pc7[w7[s]]
        pc7[w7[s]] += 1

    cs7 = []
    st7 = [0]*n7
    for s in range(ell7):
        cs7.append(tuple(st7))
        p = w7[s]
        st7[p] = combo7[p][fc7[s]+1]
    good7 = set(cs7)

    me7 = {}
    for s in range(ell7):
        p = w7[s]
        L = cs7[s][(p-1)%n7]; S = cs7[s][p]; R = cs7[s][(p+1)%n7]
        me7[(p, L, S, R)] = combo7[p][fc7[s]+1]

    mcl7 = defaultdict(dict)
    for (p, L, S, R), Sp in me7.items():
        mcl7[p][(L, S, R)] = Sp

    print(f"n=7, ms={ms7}, sweep word: {list(w7)}")
    print(f"Good cycle: {ell7} configs")
    print(f"Forced mover entries: {len(me7)}")

    for p in range(n7):
        entries = [(ctx, sp) for ctx, sp in mcl7[p].items()]
        total = ms7[(p-1)%n7] * ms7[p] * ms7[(p+1)%n7]
        print(f"  P{p}: {len(entries)}/{total} mover contexts")

    # Find forced bad cycle
    fa7 = defaultdict(list)
    all7 = list(itertools.product(*(range(m) for m in ms7)))
    for c in all7:
        if c in good7:
            continue
        for p in range(n7):
            L = c[(p-1)%n7]; S = c[p]; R = c[(p+1)%n7]
            if (L, S, R) in mcl7[p]:
                Sp = mcl7[p][(L, S, R)]
                if Sp != S:
                    nc = list(c)
                    nc[p] = Sp
                    nc = tuple(nc)
                    if nc not in good7:
                        fa7[c].append((nc, p))

    trap7 = set(c for c in fa7 if fa7[c])
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in trap7:
            if not any(nc in trap7 for nc, p in fa7[c]):
                to_remove.add(c)
        if to_remove:
            trap7 -= to_remove
            changed = True

    print(f"Forced trap: {len(trap7)} configs")

    if trap7:
        start7 = next(iter(trap7))
        visited7 = {start7: ([], [])}
        queue7 = [start7]
        sh7 = None
        sm7 = None
        while queue7:
            cur = queue7.pop(0)
            for nxt, p in fa7[cur]:
                if nxt == start7 and visited7[cur][0]:
                    path = visited7[cur][0] + [cur]
                    movers = visited7[cur][1] + [p]
                    if sh7 is None or len(path) < len(sh7):
                        sh7 = path
                        sm7 = movers
                    break
                if nxt in trap7 and nxt not in visited7:
                    visited7[nxt] = (visited7[cur][0] + [cur], visited7[cur][1] + [p])
                    if len(visited7[nxt][0]) < 25:
                        queue7.append(nxt)

        if sh7:
            print(f"Shortest bad cycle: {len(sh7)} steps")
            print(f"Bad mover word: {sm7}")
            print(f"Good mover word: {list(w7)}")

            # Offset analysis
            off7 = []
            for step in range(len(sh7)):
                cfg_bad = sh7[step]
                p = sm7[step]
                ctx_bad = (cfg_bad[(p-1)%n7], cfg_bad[p], cfg_bad[(p+1)%n7])
                for s in range(ell7):
                    if w7[s] == p:
                        gctx = (cs7[s][(p-1)%n7], cs7[s][p], cs7[s][(p+1)%n7])
                        if gctx == ctx_bad:
                            offset = tuple((b-g) % ms7[i] for i, (b, g) in enumerate(zip(cfg_bad, cs7[s])))
                            off7.append((step, s, offset, p))
                            break

            unique7 = set(o for _, _, o, _ in off7)
            print(f"Unique offsets: {len(unique7)}")
            for o in sorted(unique7):
                cnt = sum(1 for _, _, oo, _ in off7 if oo == o)
                print(f"  {o}: {cnt} times")

            for step, gs, offset, p in off7:
                print(f"  Bad {step:2d} -> Good {gs:2d} (P{p}): offset = {offset}")

print("\nDONE")
