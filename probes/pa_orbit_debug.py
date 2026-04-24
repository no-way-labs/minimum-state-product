#!/usr/bin/env python3
"""Debug: trace one orbit in detail."""

import itertools, sys

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

def compute_displacement(w, n):
    total = 0; ell = len(w)
    for i in range(ell):
        diff = (w[(i+1)%ell] - w[i]) % n
        if diff == 1: total += 1
        elif diff == n-1: total -= 1
    return total

def enumerate_sweep_words(ms, n):
    CL = sum(ms)
    target_fc = {p: ms[p] for p in range(n)}
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    results = []
    def dfs(word, fc):
        if len(word) == CL:
            if abs(word[-1] - word[0]) % n in (1, n-1):
                config = [0]*n
                for p in word: config[p] = (config[p]+1) % ms[p]
                if all(c == 0 for c in config):
                    if abs(compute_displacement(word, n)) == 2*n:
                        results.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target_fc[nxt]:
                fc[nxt] += 1; word.append(nxt)
                if sum(target_fc[p] - fc[p] for p in range(n)) <= CL - len(word):
                    dfs(word, fc)
                word.pop(); fc[nxt] -= 1
    for p in range(n):
        if target_fc[p] > 0:
            fc = {q: 0 for q in range(n)}; fc[p] = 1
            dfs([p], fc)
    seen = set(); unique = []
    for w in results:
        canon = tuple(min(w[i:]+w[:i] for i in range(len(w))))
        if canon not in seen: seen.add(canon); unique.append(w)
    return unique

def enumerate_value_sequences(m, k):
    seqs = []
    def dfs(seq, rem):
        if rem == 0:
            if seq[-1] == 0: seqs.append(tuple(seq))
            return
        for v in range(m):
            if v != seq[-1]:
                if rem == 1 and v != 0: continue
                seq.append(v); dfs(seq, rem-1); seq.pop()
    dfs([0], k)
    return seqs

def build_cycle(ms, n, word, combo):
    ell = len(word); fc = [0]*n
    state = [combo[p][0] for p in range(n)]
    configs = []
    for s in range(ell):
        configs.append(tuple(state))
        p = word[s]; fc[p] += 1; state[p] = combo[p][fc[p]]
    if tuple(state) != configs[0]: return None
    if len(set(configs)) != ell: return None
    return configs

n = 9
ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = sum(ms)

words = enumerate_sweep_words(ms, n)
print(f"Found {len(words)} sweep words")
w = words[0]
print(f"Word: {w}")

all_combos = {p: enumerate_value_sequences(ms[p], ms[p]) for p in range(n)}
# Take first combo
combo = tuple(all_combos[p][0] for p in range(n))
print(f"Combo: {combo}")

cfgs = build_cycle(ms, n, w, combo)
if cfgs is None:
    print("No valid cycle!")
    sys.exit(1)

print(f"Cycle length: {len(cfgs)}")
print(f"First 3 configs: {cfgs[:3]}")

good_set = set(cfgs)

# Build MCT
mct = {}
for s in range(CL):
    p = w[s]; c = cfgs[s]
    L, S, R = get_context(c, p, n)
    Sp = cfgs[(s+1) % CL][p]
    key = (p, L, S, R)
    mct[key] = Sp

print(f"MCT entries: {len(mct)}")

# Try shifting g_0
g0 = cfgs[0]
w0 = w[0]
print(f"g0 = {g0}, mover w0 = {w0}")

# Find q far from w0
for q in range(n):
    d = min(abs(q - w0), n - abs(q - w0))
    if d > 1:
        print(f"Trying q={q} (distance {d} from w0={w0})")
        c0 = list(g0); c0[q] = (c0[q] + 1) % ms[q]; c0 = tuple(c0)
        print(f"c0 = {c0}")
        print(f"c0 in good_set? {c0 in good_set}")

        # Check forced-privileged
        fps = []
        for p in range(n):
            L, S, R = get_context(c0, p, n)
            key = (p, L, S, R)
            if key in mct and mct[key] != S:
                fps.append((p, key, mct[key]))
        print(f"Forced-priv at c0: {fps}")

        if fps:
            # Follow orbit
            cur = c0
            orbit_len = 0
            for step in range(CL + 5):
                fps2 = []
                for p in range(n):
                    L, S, R = get_context(cur, p, n)
                    key2 = (p, L, S, R)
                    if key2 in mct and mct[key2] != S:
                        fps2.append((p, key2))
                if not fps2:
                    print(f"  Step {step}: HALTED (no forced-priv)")
                    break
                p, key2 = fps2[0]
                nxt = list(cur); nxt[p] = mct[key2]; nxt = tuple(nxt)
                orbit_len = step + 1
                if nxt in good_set:
                    print(f"  Step {step}: reached good config!")
                    break
                if nxt == c0:
                    print(f"  Step {step}: orbit closed at length {orbit_len}")
                    break
                if step < 5:
                    print(f"  Step {step}: fire p={p}, {len(fps2)} fp procs, nxt={nxt[:4]}...")
                cur = nxt
            break
