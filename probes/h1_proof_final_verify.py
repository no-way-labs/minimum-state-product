#!/usr/bin/env python3
"""
FINAL comprehensive verification of the theorem at n=5 and n=7.

Theorem: For {2,3} state sizes, n>=5, >=3 binary, sub-threshold product,
sandwiched ternary t with (1,1) phase => entry conflict exists.

n=5: exhaustive check (all words up to length 20).
n=7: check one representative system from each case.
"""
from collections import Counter
from itertools import product as iproduct
import time

def build_configs(ms, n, word):
    L = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(L):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]: return None
    if len(set(configs[:L])) != L: return None
    return configs[:L]

def enumerate_good_cycles(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length: return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

def check_cycle(word, configs, ms, n, sandwiched):
    """Check if cycle with (1,1) phase has EC."""
    L = len(word)
    # Check for (1,1) phase
    has_11 = False
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        t_steps = [s for s in range(L) if word[s] == t]
        for idx in range(len(t_steps)):
            k1 = t_steps[idx]
            k2 = t_steps[(idx+1)%len(t_steps)]
            phase = []
            s = (k1+1)%L
            while s != k2:
                phase.append(s)
                s = (s+1)%L
            J = sum(1 for s in phase if word[s] == bL)
            K = sum(1 for s in phase if word[s] == bR)
            if J == 1 and K == 1: has_11 = True; break
        if has_11: break
    if not has_11: return None  # no (1,1) phase

    # Check EC at any proc
    for p in range(n):
        pL, pR = (p-1)%n, (p+1)%n
        mover, nonmover = set(), set()
        for s in range(L):
            ctx = (configs[s][pL], configs[s][p], configs[s][pR])
            if word[s] == p: mover.add(ctx)
            else: nonmover.add(ctx)
        if mover & nonmover:
            return True
    return False

# ===== n=5 =====
print("="*70)
print("n=5: EXHAUSTIVE VERIFICATION")
print("="*70)

n = 5
threshold = 4*3**(n-2)
t0 = time.time()

total_11 = 0
total_ec = 0
total_exc = 0

for ms_tuple in iproduct([2,3], repeat=n):
    ms = list(ms_tuple)
    prod = 1
    for m in ms: prod *= m
    if prod >= threshold: continue
    binary = [p for p in range(n) if ms[p] == 2]
    if len(binary) < 3: continue
    sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
    if not sandwiched: continue

    words = enumerate_good_cycles(ms, n, 20)
    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None: continue
        if not is_wrap_adjacent(word, n): continue
        result = check_cycle(word, configs, ms, n, sandwiched)
        if result is None: continue
        total_11 += 1
        if result:
            total_ec += 1
        else:
            total_exc += 1
            print(f"  EXCEPTION: ms={ms}, word={word}")

print(f"n=5: {total_11} cycles with (1,1), EC={total_ec}, exceptions={total_exc}")
print(f"Time: {time.time()-t0:.1f}s")

# ===== n=7: representative systems =====
print("\n" + "="*70)
print("n=7: REPRESENTATIVE SYSTEMS")
print("="*70)

n = 7
threshold = 4*3**(n-2)

# Case A representative
ms_a = [2, 2, 2, 2, 2, 2, 3]
# Case B representative
ms_b = [2, 3, 2, 3, 2, 3, 3]

for ms_label, ms in [("Case A", ms_a), ("Case B", ms_b)]:
    prod = 1
    for m in ms: prod *= m
    binary = [p for p in range(n) if ms[p] == 2]
    sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]

    if prod >= threshold or len(binary) < 3 or not sandwiched:
        print(f"  {ms_label}: ms={ms} SKIPPED (prod={prod}, binary={len(binary)}, sandwiched={sandwiched})")
        continue

    print(f"\n{ms_label}: ms={ms}, prod={prod}, sandwiched={sandwiched}")
    t0 = time.time()
    words = enumerate_good_cycles(ms, n, 22)

    total_11 = 0
    total_ec = 0
    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None: continue
        if not is_wrap_adjacent(word, n): continue
        result = check_cycle(word, configs, ms, n, sandwiched)
        if result is None: continue
        total_11 += 1
        if result: total_ec += 1
        else: print(f"  EXCEPTION: word={word}")

    print(f"  cycles with (1,1): {total_11}, EC={total_ec}, exceptions={total_11 - total_ec}")
    print(f"  Time: {time.time()-t0:.1f}s")
