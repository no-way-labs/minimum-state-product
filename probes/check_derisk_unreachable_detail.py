#!/usr/bin/env python3
"""Detail on unreachable EC cases at n=9."""
from itertools import product as iproduct
from collections import Counter

n = 9
ms = [2,3,3,3,2,3,3,3,2]  # the worst case: 16 unreachable
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

results = []
def dfs(word, fc, config):
    if len(word) > 26: return
    if len(word) >= 2*n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
            if len(results) >= 200: return
        return
    if len(results) >= 200: return
    remaining = 26 - len(word)
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
print(f"n={n}, ms={ms}, {len(zw)} zero-winding cycles")
print(f"Binary: {[i for i in range(n) if ms[i]==2]}")
print(f"Sandwiched ternary: {[p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]}")

# For unreachable cycles: where is EC, and what type of proc?
for word in zw:
    ell = len(word)
    cfgs = [list(start)]
    for i in range(ell):
        c = list(cfgs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        cfgs.append(c)

    # Check reachability
    reachable = False
    for p in range(n):
        if not ((ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2) or ms[p]==2): continue
        m_ctx, n_ctx = set(), set()
        for s in range(ell):
            ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: reachable = True; break
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: reachable = True; break
                n_ctx.add(ctx)
        if reachable: break

    if reachable: continue

    # This is unreachable — find where EC actually is
    print(f"\nUnreachable cycle: word={word[:10]}...")
    for p in range(n):
        m_ctx, n_ctx = set(), set()
        conflict = None
        for s in range(ell):
            ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: conflict = ctx; break
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: conflict = ctx; break
                n_ctx.add(ctx)
        if conflict:
            L_m = ms[(p-1)%n]
            R_m = ms[(p+1)%n]
            print(f"  EC at proc {p}: m={ms[p]}, L_m={L_m}, R_m={R_m}, ctx={conflict}")
            # What mechanism WOULD work here?
            if ms[p] == 3 and L_m == 2 and R_m == 2:
                print(f"    → sandwiched ternary (mechanisms apply)")
            elif ms[p] == 3 and (L_m == 2 or R_m == 2):
                which = "left" if L_m == 2 else "right"
                print(f"    → ternary with ONE binary neighbor ({which})")
                print(f"    → NEED: extended mechanism with one binary neighbor")
            elif ms[p] == 2:
                print(f"    → binary (BoundaryShadowEntry applies)")
            else:
                print(f"    → ternary with NO binary neighbor")
            break
