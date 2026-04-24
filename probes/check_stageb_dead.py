#!/usr/bin/env python3
"""
Is Stage B (PhaseExtraction:778) dead code?

Stage B is reached when: sandwiched ternary exists AND all gaps are normal-form.
Our earlier check showed: alternating rings have 0 all-normal-form cycles.

But: Stage B assumes a sandwiched ternary t is GIVEN. This means it's only
called when a sandwiched ternary EXISTS (alternating or has binary-gap-binary).

Check: for ALL layouts where sandwiched ternary exists, do ALL cycles
have at least one non-normal-form gap at SOME sandwiched ternary?
If yes → Stage B is dead code.
"""
from itertools import product as iproduct
from collections import Counter

def check_stageb(n, ms, max_len):
    start = tuple(0 for _ in range(n))
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]

    if not sandwiched:
        return None  # No sandwiched ternary → Stage B not reachable

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

    # For each ZW cycle: check if SOME sandwiched ternary has a non-normal-form gap
    stageb_needed = 0
    for word in zw:
        ell = len(word)
        some_non_normal = False
        for t in sandwiched:
            fire_steps = sorted(s for s in range(ell) if word[s] == t)
            if len(fire_steps) < 2: continue
            left_t = (t-1)%n; right_t = (t+1)%n
            for idx in range(len(fire_steps)):
                a = fire_steps[idx]
                s = fire_steps[(idx+1) % len(fire_steps)]
                if s <= a: s += ell
                J = sum(1 for step in range(a+1, s) if word[step%ell] == left_t)
                K = sum(1 for step in range(a+1, s) if word[step%ell] == right_t)
                if (J, K) not in [(1,0), (0,1), (1,1)]:
                    some_non_normal = True
                    break
            if some_non_normal: break
        if not some_non_normal:
            stageb_needed += 1

    return len(zw), stageb_needed

layouts = [
    (5, [2,3,2,3,2], 16),
    (7, [2,3,2,3,2,3,2], 20),
    (9, [2,3,2,3,2,3,2,3,2], 26),
    (9, [2,3,2,3,3,3,3,3,2], 26),  # has sandwiched at proc 1
    (7, [2,3,2,3,3,3,3], 22),  # has sandwiched at proc 1
]

for n, ms, ml in layouts:
    sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
    result = check_stageb(n, ms, ml)
    if result is None:
        print(f"n={n}, ms={ms}: no sandwiched ternary, Stage B not reachable")
    else:
        zw, sb = result
        status = "DEAD ✅" if sb == 0 else f"ALIVE ⚠️ {sb} need Stage B"
        print(f"n={n}, ms={ms}: sandwiched={sandwiched}, ZW={zw}, Stage B: {status}")
