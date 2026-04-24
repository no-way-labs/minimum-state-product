#!/usr/bin/env python3
"""
Existential privilege propagation: for each non-good config c with
forced-privileged procs, does there EXIST some i in fp(c) such that
fire(c, i) is either good or has a forced-privileged proc?

This is the weaker (existential) version needed for the Acc induction.
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


def test_existential_propagation(ms, n, word, configs):
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

    total_configs = 1
    for m in ms: total_configs *= m

    universal_ok = 0       # ALL choices of i propagate
    existential_ok = 0     # SOME choice of i propagates (or reaches good)
    existential_fail = 0   # NO choice of i works
    nongood_with_fp = 0

    for cfg_idx in range(total_configs):
        c = []
        idx = cfg_idx
        for p in range(n):
            c.append(idx % ms[p])
            idx //= ms[p]
        c = tuple(c)

        if c in good_set: continue
        fps = forced_privileged(c)
        if not fps: continue
        nongood_with_fp += 1

        all_ok = True
        some_ok = False
        for i in fps:
            c_prime = fire(c, i)
            if c_prime in good_set:
                some_ok = True
                continue
            fps_prime = forced_privileged(c_prime)
            if fps_prime:
                some_ok = True
            else:
                all_ok = False

        if all_ok:
            universal_ok += 1
        if some_ok:
            existential_ok += 1
        else:
            existential_fail += 1
            print(f"  EXISTENTIAL FAIL: c={c}, fp={fps}")
            for i in fps:
                cp = fire(c, i)
                print(f"    fire {i} -> {cp} good={cp in good_set} fp={forced_privileged(cp)}")

    return {
        "nongood_with_fp": nongood_with_fp,
        "universal_ok": universal_ok,
        "existential_ok": existential_ok,
        "existential_fail": existential_fail,
    }


print("=" * 70)
print("EXISTENTIAL PRIVILEGE PROPAGATION")
print("=" * 70)

sys.setrecursionlimit(5000)

test_cases = [
    (7, [2, 2, 2, 3, 3, 3, 3], "n=7, 3 consecutive binary"),
]

for n, ms, desc in test_cases:
    CL = sum(ms)
    print(f"\n--- {desc}, CL={CL} ---")

    words = enumerate_sweep_words(ms, n)
    all_combos = {p: enumerate_value_sequences(ms[p], ms[p]) for p in range(n)}

    for widx, w in enumerate(words):
        combo_lists = [all_combos[p] for p in range(n)]
        for cidx, combo_idx in enumerate(itertools.product(*[range(len(c)) for c in combo_lists])):
            combo = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
            cfgs = build_cycle(ms, n, w, combo)
            if cfgs is None: continue
            print(f"\n  Word {widx}, combo {cidx}:")
            r = test_existential_propagation(ms, n, w, cfgs)
            if r:
                for k, v in r.items():
                    print(f"    {k}: {v}")
            if cidx >= 1: break  # just first 2 combos
        break  # just first word

print("\n" + "=" * 70)
