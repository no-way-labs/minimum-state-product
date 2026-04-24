#!/usr/bin/env python3
"""
UNIVERSAL privilege propagation test.

For EVERY non-good config c with a forced-privileged proc i:
  If move(sys, c, i) is non-good, does move(sys, c, i) have a forced-privileged proc?

This is what the Lean theorem forcedSucc_has_privileged requires.
"""

import itertools, time, sys
from collections import defaultdict

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


def test_universal_propagation(ms, n, word, configs):
    """
    Enumerate ALL configs in the state space.
    For each non-good config c with a forced-privileged proc i:
      fire i -> get c' = move(sys, c, i)
      if c' is non-good: check that c' has a forced-privileged proc.
    """
    CL = len(configs)
    good_set = set(configs)

    # Build MCT
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

    # Enumerate all configs
    total_configs = 1
    for m in ms: total_configs *= m

    tested = 0
    propagated = 0
    failed = 0
    nongood_with_fp = 0
    succ_is_good = 0

    for cfg_idx in range(total_configs):
        c = []
        idx = cfg_idx
        for p in range(n):
            c.append(idx % ms[p])
            idx //= ms[p]
        c = tuple(c)

        if c in good_set:
            continue

        fps = forced_privileged(c)
        if not fps:
            continue

        nongood_with_fp += 1

        for i in fps:
            tested += 1
            # Fire proc i
            L, S, R = get_context(c, i, n)
            key = (i, L, S, R)
            new_val = mct[key]
            c_prime = list(c)
            c_prime[i] = new_val
            c_prime = tuple(c_prime)

            if c_prime in good_set:
                succ_is_good += 1
                continue

            # c_prime is non-good. Does it have a forced-privileged proc?
            fps_prime = forced_privileged(c_prime)
            if fps_prime:
                propagated += 1
            else:
                failed += 1
                if failed <= 5:
                    print(f"  FAILURE: c={c}, fire proc {i}, c'={c_prime}")
                    print(f"    c fp: {fps}")
                    print(f"    c' fp: {fps_prime}")

    return {
        "total_configs": total_configs,
        "nongood_with_fp": nongood_with_fp,
        "tested_transitions": tested,
        "succ_is_good": succ_is_good,
        "succ_nongood_propagated": propagated,
        "succ_nongood_failed": failed,
    }


print("=" * 70)
print("UNIVERSAL PRIVILEGE PROPAGATION TEST")
print("=" * 70)

sys.setrecursionlimit(5000)

# Use n=7 for full state space enumeration (product 648 is feasible)
test_cases = [
    (7, [2, 2, 2, 3, 3, 3, 3], "n=7, 3 consecutive binary"),
]

for n, ms, desc in test_cases:
    CL = sum(ms)
    product = 1
    for m in ms: product *= m
    print(f"\n--- {desc}, CL={CL}, product={product} ---")

    t0 = time.time()
    words = enumerate_sweep_words(ms, n)
    all_combos = {p: enumerate_value_sequences(ms[p], ms[p]) for p in range(n)}
    print(f"  Sweep words: {len(words)}")

    for widx, w in enumerate(words):
        combo_lists = [all_combos[p] for p in range(n)]
        for combo_idx in itertools.product(*[range(len(c)) for c in combo_lists]):
            combo = tuple(combo_lists[p][combo_idx[p]] for p in range(n))
            cfgs = build_cycle(ms, n, w, combo)
            if cfgs is None: continue

            r = test_universal_propagation(ms, n, w, cfgs)
            if r is None: continue
            print(f"  Word {widx}, combo {combo_idx}:")
            for k, v in r.items():
                print(f"    {k}: {v}")
            break  # just first combo per word for speed
        break  # just first word

    print(f"  Time: {time.time()-t0:.1f}s")

print("\n" + "=" * 70)
