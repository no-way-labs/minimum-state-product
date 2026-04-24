#!/usr/bin/env python3
"""
RA Part 7: Final summary + n=11 spot check + explicit ShadowTrap example.
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


# ============================================================
# Explicit ShadowTrap for n=9, sweep #0, combo #0
# ============================================================
print("=" * 72)
print("EXPLICIT SHADOW TRAP FOR LEAN")
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
valid = []
for w in unique:
    cycle = build_cycle(ms, n, w)
    if cycle is not None:
        valid.append((w, cycle))
sweeps = [(w, c, compute_displacement(w, n)) for w, c in valid if abs(compute_displacement(w, n)) == 2*n]

w0, cyc0, d0 = sweeps[0]
combo = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))
ell = len(w0)

fc_num = [0]*ell
pc = [0]*n
for s in range(ell):
    fc_num[s] = pc[w0[s]]
    pc[w0[s]] += 1

cs = []
state = [0]*n
for s in range(ell):
    cs.append(tuple(state))
    p = w0[s]
    state[p] = combo[p][fc_num[s]+1]
good_set = set(cs)

mcx = defaultdict(dict)
for s in range(ell):
    p = w0[s]
    L = cs[s][(p-1)%n]; S = cs[s][p]; R = cs[s][(p+1)%n]
    mcx[p][(L, S, R)] = combo[p][fc_num[s]+1]

# Find forced trap and extract the actual cycle
all_cfgs = list(itertools.product(*(range(m) for m in ms)))
forced_adj = defaultdict(list)
for c in all_cfgs:
    if c in good_set: continue
    for p in range(n):
        L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
        if (L, S, R) in mcx[p]:
            Sp = mcx[p][(L, S, R)]
            if Sp != S:
                nc = list(c); nc[p] = Sp; nc = tuple(nc)
                if nc not in good_set:
                    forced_adj[c].append((nc, p))

trap = set(c for c in forced_adj if forced_adj[c])
changed = True
while changed:
    changed = False
    to_remove = set()
    for c in trap:
        if not any(nc in trap for nc, p in forced_adj[c]): to_remove.add(c)
    if to_remove: trap -= to_remove; changed = True

# BFS for shortest cycle
start = next(iter(trap))
visited = {start: ([], [])}
queue = [start]
shortest = None
shortest_movers = None
while queue:
    cur = queue.pop(0)
    for nxt, p in forced_adj[cur]:
        if nxt == start and visited[cur][0]:
            path = visited[cur][0] + [cur]
            movers = visited[cur][1] + [p]
            if shortest is None or len(path) < len(shortest):
                shortest = path
                shortest_movers = movers
            break
        if nxt in trap and nxt not in visited:
            visited[nxt] = (visited[cur][0] + [cur], visited[cur][1] + [p])
            if len(visited[nxt][0]) < 40:
                queue.append(nxt)

print(f"\nGood cycle: {ell} configs")
print(f"Good word: {list(w0)}")
print(f"\nShadow trap: {len(shortest)} configs")
print(f"Shadow word: {shortest_movers}")
print(f"\nGood cycle configs and movers:")
for s in range(ell):
    p = w0[s]
    ctx = (cs[s][(p-1)%n], cs[s][p], cs[s][(p+1)%n])
    print(f"  g[{s:2d}] = {cs[s]}  fire P{p} ctx={ctx}")

print(f"\nShadow trap configs and movers:")
for s in range(len(shortest)):
    c = shortest[s]
    p = shortest_movers[s]
    ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
    print(f"  s[{s:2d}] = {c}  fire P{p} ctx={ctx}")

# Verify all shadow configs are non-good
shadow_not_good = all(c not in good_set for c in shortest)
# Verify closed
shadow_closed = True
for s in range(len(shortest)):
    c = shortest[s]
    p = shortest_movers[s]
    nc = list(c); nc[p] = mcx[p][(c[(p-1)%n], c[p], c[(p+1)%n])]; nc = tuple(nc)
    expected = shortest[(s+1) % len(shortest)]
    if nc != expected:
        shadow_closed = False
        print(f"  CLOSURE FAIL at step {s}: got {nc}, expected {expected}")
# Verify distinct
shadow_distinct = len(set(shortest)) == len(shortest)

print(f"\nShadowTrap verification:")
print(f"  Non-empty: True ({len(shortest)} configs)")
print(f"  Disjoint from good: {shadow_not_good}")
print(f"  Closed: {shadow_closed}")
print(f"  Distinct: {shadow_distinct}")
print(f"  Valid ShadowTrap: {shadow_not_good and shadow_closed and shadow_distinct}")

# ============================================================
# Check: can we also find shadow trap for NON-sweep cycles?
# (This would mean the forced-entry trap is even more general)
# ============================================================
print(f"\n{'='*72}")
print("NON-SWEEP CYCLES CHECK")
print(f"{'='*72}")

non_sweeps = [(w, c) for w, c in valid if abs(compute_displacement(w, n)) != 2*n]
print(f"Non-sweep cycles: {len(non_sweeps)}")

for wi, (w, cyc) in enumerate(non_sweeps[:5]):
    disp = compute_displacement(w, n)
    combo = tuple(enumerate_state_sequences(ms[p], ms[p])[0] for p in range(n))
    ell = len(w)

    fc_num = [0]*ell
    pc = [0]*n
    for s in range(ell):
        fc_num[s] = pc[w[s]]
        pc[w[s]] += 1

    cseq = []
    state = [0]*n
    for s in range(ell):
        cseq.append(tuple(state))
        p = w[s]
        state[p] = combo[p][fc_num[s]+1]
    gs = set(cseq)

    mx = defaultdict(dict)
    for s in range(ell):
        p = w[s]
        L = cseq[s][(p-1)%n]; S = cseq[s][p]; R = cseq[s][(p+1)%n]
        mx[p][(L, S, R)] = combo[p][fc_num[s]+1]

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

    tr = set(c for c in fa if fa[c])
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in tr:
            if not any(nc in tr for nc, p in fa[c]): to_remove.add(c)
        if to_remove: tr -= to_remove; changed = True

    print(f"  Cycle {wi}: disp={disp:+d}, CL={ell}, trap={len(tr)}")

# ============================================================
# FINAL SUMMARY
# ============================================================
print(f"\n{'='*72}")
print("FINAL SUMMARY")
print(f"{'='*72}")

print("""
FINDINGS:

1. STUTTERED SWEEP CHARACTERIZATION (Part 1):
   - 8 sweep cycles at n=9, ms=[2,3,3,2,3,3,2,3,3]
   - All have CL=24, |disp|=18=2n, 21 CW/CCW + 3 stutters
   - Stutters occur at binary proc positions
   - ALL are EC-free for ALL 64 state-sequence combos

2. TABLE ENTRY ANALYSIS (Part 2):
   - 162 total entries, 72 forced (44.4%), 90 free
   - Binary: 2 forced mover + 6 forced nonmover + 10 free
   - Ternary: 3 forced mover + 5 forced nonmover + 10 free

3. FORCED-ENTRY SHADOW TRAP (Parts 3-4):
   - The forced mover entries create privilege at NON-GOOD configs
   - These transitions form a cycle among non-good configs
   - The cycle uses ONLY forced entries (0 free entries)
   - Therefore the trap is FILL-INDEPENDENT
   - Verified: 64/64 tests at n=7, 512/512 tests at n=9
   - Shortest bad cycle = CL (same length as good cycle)
   - ShadowTrap properties verified: nonempty, disjoint, closed, distinct

4. NOT A CONSTANT-OFFSET SHADOW (Part 4):
   - The bad cycle is NOT a constant-offset translate of good cycle
   - It's piecewise constant with 11 different offsets at n=9
   - But it IS a forced-entry shadow: each step reuses a good mover entry

5. BINARY FLIP CONFIRMED DEAD (Part 6):
   - Flipping any single binary proc's state gives OVERLAP with good (not disjoint)
   - Binary flip approach is definitively wrong

6. THE PROOF MECHANISM:
   - hconv IS available at the sorry (line 581)
   - Construct ShadowTrap from forced entries
   - Apply shadowTrap_not_converges -> not(converges)
   - Contradiction with hconv
   - Same pattern as existing waterfall shadow proof

7. WHAT'S NEEDED FOR LEAN:
   a. The hard part: constructing the ShadowTrap for stuttered sweeps
   b. This requires showing the forced mover entries create a bad cycle
   c. The construction is STRUCTURAL (depends only on mover word, not combos)
   d. For each combo, the mover entries differ, but a trap always exists

   SIMPLEST APPROACH: Use the fact that for ANY good cycle, the
   forced mover entries create a "shadow" bad cycle. This is because:
   - Each mover context (L,S,R) only depends on 3 consecutive procs
   - With n >= 7 and non-consecutive binary (gap >= 3), there exist
     "far" procs whose state doesn't affect any mover context
   - Shifting these far procs creates non-good configs with same
     mover contexts -> same forced privilege -> same transitions
   - The shifted configs form a cycle (same structure, shifted values)

   This is provable analytically for general n.
""")
