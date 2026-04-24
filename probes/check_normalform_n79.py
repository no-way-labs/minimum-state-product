#!/usr/bin/env python3
"""Check if all-normal-form cycles exist at n=7 and n=9."""
from itertools import product as iproduct
from collections import Counter

def check_normal_form(n, ms, max_len):
    start = tuple(0 for _ in range(n))
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]

    results = []
    def dfs(word, fc, config):
        if len(word) > max_len: return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                if len(results) >= 500: return
            return
        if len(results) >= 500: return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            if len(results) >= 500: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= 500: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

    def winding(word):
        w = 0
        for i in range(len(word)):
            d = (word[(i+1)%len(word)] - word[i]) % n
            if d == 1: w += 1
            elif d == n-1: w -= 1
        return w

    zw = [w for w in results if winding(w) == 0]

    nf_count = 0
    for word in zw:
        ell = len(word)
        all_normal = True
        for t in sandwiched:
            fire_steps = sorted(s for s in range(ell) if word[s] == t)
            if not fire_steps: continue
            left_t = (t-1)%n; right_t = (t+1)%n
            for idx in range(len(fire_steps)):
                a = fire_steps[idx]
                s = fire_steps[(idx+1) % len(fire_steps)]
                if s <= a: s += ell
                J = sum(1 for step in range(a+1, s) if word[step%ell] == left_t)
                K = sum(1 for step in range(a+1, s) if word[step%ell] == right_t)
                if (J, K) not in [(1,0), (0,1), (1,1)]:
                    all_normal = False; break
            if not all_normal: break
        if all_normal:
            nf_count += 1

    print(f"n={n}, ms={ms}: {len(zw)} ZW cycles, {nf_count} all-normal-form" +
          (" ← STAGE A COVERS ALL!" if nf_count == 0 else f" ← {nf_count} NEED STAGE B"))

for n, ms, ml in [
    (5, [2,3,2,3,2], 16),
    (7, [2,3,2,3,2,3,2], 20),
    (7, [2,3,3,2,3,3,3], 22),
    (9, [2,3,3,2,3,3,2,3,3], 26),
    (9, [2,3,3,3,2,3,3,3,2], 26),
]:
    check_normal_form(n, ms, ml)
