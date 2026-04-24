#!/usr/bin/env python3
"""
GOTCHA 4 deep dive: at n=9, ms=[2,3,3,2,3,3,2,3,3], no sandwiched ternary.
Do the mechanisms still find EC? At which proc?
"""
from itertools import product as iproduct
from collections import Counter
import time

n = 9
ms = [2,3,3,2,3,3,2,3,3]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

print(f"n={n}, ms={ms}")
print(f"Binary: {[p for p in range(n) if ms[p]==2]}")
print(f"Sandwiched ternary (both neighbors binary): ", end="")
sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
print(sandwiched if sandwiched else "NONE")
print(f"Ternary with at least ONE binary neighbor: ", end="")
one_bin = [p for p in range(n) if ms[p]==3 and (ms[(p-1)%n]==2 or ms[(p+1)%n]==2)]
print(one_bin)

# Generate cycles (small sample due to large state space)
# product = 2^3 * 3^6 = 5832. Too many configs for full enumeration.
# Use shorter max_len
t0 = time.time()
results = []
def dfs(word, fc, config):
    if len(word) > 22: return  # tighter bound
    if len(word) >= 2*n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
            if len(results) >= 200: return  # cap
        return
    if len(results) >= 200: return
    remaining = 22 - len(word)
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

elapsed = time.time() - t0
print(f"\nFound {len(results)} cycles in {elapsed:.1f}s")

if not results:
    print("No cycles found! (max_len too tight)")
else:
    # Check EC
    def has_ec_at(word, p):
        ell = len(word)
        configs = [list(start)]
        for i in range(ell):
            c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
            configs.append(c)
        m_ctx, n_ctx = set(), set()
        for s in range(ell):
            ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: return True
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: return True
                n_ctx.add(ctx)
        return False

    ec_procs = Counter()
    no_ec = 0
    for word in results:
        found = False
        for p in range(n):
            if has_ec_at(word, p):
                ec_procs[p] += 1
                found = True
                break
        if not found:
            no_ec += 1

    print(f"\nEC proc distribution:")
    for p in sorted(ec_procs):
        print(f"  Proc {p} (m={ms[p]}, L={ms[(p-1)%n]}, R={ms[(p+1)%n]}): {ec_procs[p]}")
    print(f"No EC: {no_ec}")

    # Key: is EC ever at a non-sandwiched ternary?
    for p in sorted(ec_procs):
        if ms[p] == 3:
            l_bin = ms[(p-1)%n] == 2
            r_bin = ms[(p+1)%n] == 2
            print(f"  Proc {p}: ternary, L_binary={l_bin}, R_binary={r_bin}, sandwiched={l_bin and r_bin}")
