#!/usr/bin/env python3
"""Check more n>=9 layouts for mechanism reachability."""
from itertools import product as iproduct
from collections import Counter

def check_dispatch_quick(n, ms, max_len):
    start = tuple(0 for _ in range(n))
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    results = []
    def dfs(word, fc, config):
        if len(word) > max_len: return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                if len(results) >= 200: return
            return
        if len(results) >= 200: return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            if len(results) >= 200: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= 200: break
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

    unreachable = 0
    for word in zw:
        ell = len(word)
        cfgs = [list(start)]
        for i in range(ell):
            c = list(cfgs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
            cfgs.append(c)

        # Check if ANY sandwiched-ternary or binary proc has EC
        found = False
        for p in range(n):
            p_tern = ms[p] == 3
            p_bin = ms[p] == 2
            p_L_bin = ms[(p-1)%n] == 2
            p_R_bin = ms[(p+1)%n] == 2
            if not ((p_tern and p_L_bin and p_R_bin) or p_bin): continue

            m_ctx, n_ctx = set(), set()
            has_ec = False
            for s in range(ell):
                ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
                if word[s] == p:
                    if ctx in n_ctx: has_ec = True; break
                    m_ctx.add(ctx)
                else:
                    if ctx in m_ctx: has_ec = True; break
                    n_ctx.add(ctx)
            if has_ec: found = True; break

        if not found: unreachable += 1

    return len(zw), unreachable

# Test various n>=9 layouts
layouts = [
    (9, [2,3,3,2,3,3,2,3,3]),      # [2,3,3]^3
    (9, [2,3,3,3,2,3,3,3,2]),      # 3 binary, gaps of 3
    (9, [2,3,2,3,3,3,3,3,2]),      # 3 binary, gaps 1,4,2
    (9, [2,2,3,3,3,2,3,3,3]),      # 2 consec + 1 separate
    (10, [2,3,2,3,2,3,3,3,3,3]),   # 3 binary at n=10
    (10, [2,3,3,2,3,3,2,3,3,3]),   # 3 binary at n=10 v2
]

for n, ms_layout in layouts:
    prod = 1
    for m in ms_layout: prod *= m
    threshold = 4 * 3**(n-2)
    if prod >= threshold:
        print(f"n={n}, ms={ms_layout}: product {prod} >= {threshold} SKIP")
        continue
    binary = [i for i in range(n) if ms_layout[i] == 2]
    has_3consec = any(ms_layout[i]==2 and ms_layout[(i+1)%n]==2 and ms_layout[(i+2)%n]==2 for i in range(n))
    sandwiched = [p for p in range(n) if ms_layout[p]==3 and ms_layout[(p-1)%n]==2 and ms_layout[(p+1)%n]==2]

    total, unreach = check_dispatch_quick(n, ms_layout, 26)
    status = "✅" if unreach == 0 else f"⚠️ {unreach} unreachable"
    print(f"n={n}, ms={ms_layout}: binary={binary}, sandwiched={sandwiched}, "
          f"3consec={has_3consec}, ZW={total}, {status}")
