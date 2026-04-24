#!/usr/bin/env python3
"""
In cycles where ALL ternary gaps are normal-form (1,0)/(0,1)/(1,1),
WHERE does EC actually occur?
"""
from itertools import product as iproduct
from collections import Counter

n = 5; ms = [2,3,2,3,2]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
sandwiched = [p for p in range(n) if ms[p]==3 and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]

results = []
def dfs(word, fc, config):
    if len(word) > 16: return
    if len(word) >= 2*n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
            if len(results) >= 2000: return
        return
    if len(results) >= 2000: return
    remaining = 16 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        if len(results) >= 2000: return
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    if len(results) >= 2000: break
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

# Find cycles where ALL ternary gaps are normal-form
normal_form_cycles = []
for word in zw:
    ell = len(word)
    fc = Counter(word)
    all_normal = True

    for t in sandwiched:
        fire_steps = sorted(s for s in range(ell) if word[s] == t)
        left_t = (t-1)%n; right_t = (t+1)%n

        for idx in range(len(fire_steps)):
            a = fire_steps[idx]
            s = fire_steps[(idx+1) % len(fire_steps)]
            if s <= a: s += ell
            J = sum(1 for step in range(a+1, s) if word[step%ell] == left_t)
            K = sum(1 for step in range(a+1, s) if word[step%ell] == right_t)

            # Normal form: (1,0), (0,1), or (1,1)
            if (J, K) not in [(1,0), (0,1), (1,1)]:
                all_normal = False
                break
        if not all_normal: break

    if all_normal:
        normal_form_cycles.append(word)

print(f"All-normal-form cycles: {len(normal_form_cycles)}")

# For these: where is EC?
ec_at = Counter()
for word in normal_form_cycles:
    ell = len(word)
    cfgs = [list(start)]
    for i in range(ell):
        c = list(cfgs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        cfgs.append(c)

    for p in range(n):
        m_ctx, n_ctx = set(), set()
        found = False
        for s in range(ell):
            ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: found = True; break
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: found = True; break
                n_ctx.add(ctx)
        if found:
            ec_at[p] += 1
            break

print(f"\nEC location in normal-form cycles:")
for p in sorted(ec_at):
    print(f"  Proc {p} (m={ms[p]}): {ec_at[p]}")

no_ec = len(normal_form_cycles) - sum(ec_at.values())
print(f"No EC: {no_ec}")
