#!/usr/bin/env python3
"""Quick: do all non-incrementing valid cycles have EC?"""
from itertools import product as iproduct

n = 5
ms = [2, 3, 2, 3, 2]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

inc_results = []
def dfs_inc(word, fc, config):
    if len(word) > 16: return
    if len(word) >= 2*n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            inc_results.append(tuple(word))
        return
    remaining = 16 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs_inc(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs_inc([p], [1 if i==p else 0 for i in range(n)], tuple(first))

def check_ec(word, configs):
    ell = len(word)
    for p in range(n):
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

noninc_total = 0
noninc_ec = 0
noninc_no_ec = 0

for word in inc_results[:500]:
    ell = len(word)
    ternary_steps = [s for s in range(ell) if ms[word[s]] == 3]
    for combo in iproduct(*[range(2) for _ in ternary_steps]):
        is_inc = all(combo[i] == 0 for i in range(len(ternary_steps)))
        if is_inc: continue

        configs = [list(start)]
        for s in range(ell):
            p = word[s]
            cur = configs[-1][p]
            if ms[p] == 2:
                new_val = 1 - cur
            else:
                options = [v for v in range(3) if v != cur]
                idx = ternary_steps.index(s)
                new_val = options[combo[idx]]
            nc = list(configs[-1])
            nc[p] = new_val
            configs.append(nc)

        if tuple(configs[-1]) != start: continue
        config_set = set(tuple(c) for c in configs[:ell])
        if len(config_set) != ell: continue

        noninc_total += 1
        if check_ec(word, configs):
            noninc_ec += 1
        else:
            noninc_no_ec += 1
            if noninc_no_ec <= 3:
                print(f"NO EC: word={word}, combo={combo}")

print(f"\nNon-incrementing valid cycles: {noninc_total}")
print(f"With EC: {noninc_ec} ({100*noninc_ec/max(1,noninc_total):.1f}%)")
print(f"Without EC: {noninc_no_ec}")
if noninc_no_ec == 0:
    print("*** ALL non-incrementing cycles have EC! No gap! ***")
