#!/usr/bin/env python3
"""
Reachability analysis: which non-good configs with forced privilege
are reachable from exists_nonGood_with_privileged starting config?

Are the failure configs (where successor has no privilege) reachable?
"""

import itertools, time, sys
from collections import defaultdict, deque

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


def reachability_analysis(ms, n, word, configs):
    CL = len(configs)
    good_set = set(configs)

    mct = {}
    for s in range(CL):
        p = word[s]; c = configs[s]
        L, S, R = get_context(c, p, n)
        Sp = configs[(s+1) % CL][p]
        key = (p, L, S, R)
        if key in mct: return None
        mct[key] = Sp

    def forced_privileged(c):
        result = []
        for p in range(n):
            L, S, R = get_context(c, p, n)
            key = (p, L, S, R)
            if key in mct and mct[key] != S:
                result.append(p)
        return result

    def fire(c, i):
        L, S, R = get_context(c, i, n)
        key = (i, L, S, R)
        c_prime = list(c)
        c_prime[i] = mct[key]
        return tuple(c_prime)

    # Find ALL starting configs (from exists_nonGood_with_privileged)
    # These are configs obtained by shifting a good config at a far position
    starting_configs = set()
    for gk in configs:
        for q in range(n):
            for d in range(1, ms[q]):
                c0 = list(gk); c0[q] = (c0[q] + d) % ms[q]; c0 = tuple(c0)
                if c0 not in good_set:
                    fps = forced_privileged(c0)
                    if fps:
                        starting_configs.add(c0)

    # BFS: follow ALL forced-privilege transitions from starting configs
    # (fire every forced-privileged proc, not just the first)
    reachable = set(starting_configs)
    queue = deque(starting_configs)

    dead_ends = []  # configs where successor has no forced-priv proc

    while queue:
        c = queue.popleft()
        fps = forced_privileged(c)
        if not fps:
            continue
        for i in fps:
            c_prime = fire(c, i)
            if c_prime in good_set:
                continue
            fps_prime = forced_privileged(c_prime)
            if not fps_prime:
                dead_ends.append((c, i, c_prime))
            if c_prime not in reachable:
                reachable.add(c_prime)
                queue.append(c_prime)

    # Find ALL non-good configs with forced-priv (to compare)
    total_configs = 1
    for m in ms: total_configs *= m
    all_nongood_fp = set()
    for cfg_idx in range(total_configs):
        c = []
        idx = cfg_idx
        for p in range(n):
            c.append(idx % ms[p])
            idx //= ms[p]
        c = tuple(c)
        if c not in good_set and forced_privileged(c):
            all_nongood_fp.add(c)

    # Check: are dead_end SOURCE configs reachable?
    dead_end_sources = set(de[0] for de in dead_ends)
    dead_reachable = dead_end_sources & reachable

    print(f"  Starting configs: {len(starting_configs)}")
    print(f"  Reachable non-good configs: {len(reachable)}")
    print(f"  All non-good with fp: {len(all_nongood_fp)}")
    print(f"  Dead-end transitions: {len(dead_ends)}")
    print(f"  Dead-end source configs: {len(dead_end_sources)}")
    print(f"  Dead-end sources that are reachable: {len(dead_reachable)}")
    if dead_reachable:
        for c in list(dead_reachable)[:3]:
            print(f"    Reachable dead-end source: {c}")
            fps = forced_privileged(c)
            for i in fps:
                cp = fire(c, i)
                if cp not in good_set and not forced_privileged(cp):
                    print(f"      fire {i} -> {cp} (NO FP)")

    # Specifically check: along deterministic orbits (fire first fp proc),
    # starting from starting_configs, does any orbit hit a dead end?
    orbit_dead = 0
    orbit_ok = 0
    for c0 in starting_configs:
        cur = c0
        ok = True
        for step in range(CL * 3):
            fps = forced_privileged(cur)
            if not fps:
                # This orbit halted
                ok = False
                break
            p = fps[0]  # deterministic: first
            c_prime = fire(cur, p)
            if c_prime in good_set:
                ok = False
                break
            if c_prime == c0:
                break  # closed
            cur = c_prime
        if ok:
            orbit_ok += 1
        else:
            orbit_dead += 1

    print(f"  Deterministic orbits from starts: {orbit_ok} ok, {orbit_dead} halt/good")


print("=" * 70)
print("REACHABILITY ANALYSIS")
print("=" * 70)

sys.setrecursionlimit(5000)

n = 7
ms = [2, 2, 2, 3, 3, 3, 3]
CL = sum(ms)
print(f"\n--- n={n}, ms={ms}, CL={CL} ---")

words = enumerate_sweep_words(ms, n)
all_combos = {p: enumerate_value_sequences(ms[p], ms[p]) for p in range(n)}

for widx, w in enumerate(words):
    combo_lists = [all_combos[p] for p in range(n)]
    for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
        combo = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
        cfgs = build_cycle(ms, n, w, combo)
        if cfgs is None: continue
        print(f"\n  Word {widx}, combo {combo_idx}:")
        reachability_analysis(ms, n, w, cfgs)
        break
    break

print("\n" + "=" * 70)
