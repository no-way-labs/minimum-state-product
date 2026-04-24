#!/usr/bin/env python3
"""
Verify: do sweep cycles at consecutive binary REALLY lack EC?
And if so: what ARE they? (shadow cycles? or something else?)
"""
from itertools import product as iproduct
from collections import Counter

n = 7
ms = [2,2,2,3,3,3,3]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

results = []
def dfs(word, fc, config):
    if len(word) > 20: return
    if len(word) >= n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
        return
    remaining = 20 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

def winding(word):
    w = 0
    for i in range(len(word)):
        d = (word[(i+1)%len(word)] - word[i]) % n
        if d == 1: w += 1
        elif d == n-1: w -= 1
    return w

def has_ec(word):
    ell = len(word)
    configs = [list(start)]
    for i in range(ell):
        c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs.append(c)
    for p in range(n):
        m_ctx, n_ctx = set(), set()
        for s in range(ell):
            ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: return True, p
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: return True, p
                n_ctx.add(ctx)
    return False, None

sweep_cycles = [(winding(word), word) for word in results if abs(winding(word)) >= 2*n]
print(f"n={n}, ms={ms}")
print(f"Total sweep cycles: {len(sweep_cycles)}")

ec_count = 0
no_ec_count = 0
no_ec_examples = []

for w, word in sweep_cycles:
    has, p = has_ec(word)
    if has:
        ec_count += 1
    else:
        no_ec_count += 1
        if len(no_ec_examples) < 3:
            fc = Counter(word)
            no_ec_examples.append((word, w, dict(fc)))

print(f"With EC: {ec_count}")
print(f"Without EC: {no_ec_count}")

if no_ec_examples:
    print(f"\nSweep cycles WITHOUT EC:")
    for word, w, fc in no_ec_examples:
        print(f"  winding={w}, len={len(word)}, fc={fc}")
        print(f"  word={word}")

# Key question: are these uniform-direction sweeps?
print(f"\nDirection analysis of no-EC sweep cycles:")
for word, w, fc in no_ec_examples:
    ell = len(word)
    cw = sum(1 for i in range(ell) if (word[(i+1)%ell] - word[i]) % n == 1)
    ccw = sum(1 for i in range(ell) if (word[(i+1)%ell] - word[i]) % n == n-1)
    stay = ell - cw - ccw
    print(f"  CW={cw}, CCW={ccw}, stay={stay}, uniform={'YES' if ccw==0 or cw==0 else 'NO'}")
