#!/usr/bin/env python3
"""
Can ANY transition function completion of an EC-free cycle avoid deadlocks?

The identity completion created deadlocks. But what if we use a smarter
completion that makes every config have at least one privileged proc?

For unseen contexts: instead of f(L,S,R) = S, try f(L,S,R) != S.
This makes the proc privileged at that context.
"""
from itertools import product as iproduct
from collections import Counter

n = 9
ms = [2,3,3,2,3,3,2,3,3]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

# Find an EC-free cycle
results = []
def dfs(word, fc, config):
    if len(word) > 26: return
    if len(word) >= 24 and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
            if len(results) >= 10: return
        return
    if len(results) >= 10: return
    remaining = 26 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        if len(results) >= 10: return
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    if len(results) >= 10: break
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

def has_ec(word):
    ell = len(word)
    configs_list = [list(start)]
    for i in range(ell):
        c = list(configs_list[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs_list.append(c)
    for p in range(n):
        m_ctx, n_ctx = set(), set()
        for s in range(ell):
            ctx = (configs_list[s][(p-1)%n], configs_list[s][p], configs_list[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: return True
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: return True
                n_ctx.add(ctx)
    return False

ec_free = [w for w in results if not has_ec(w)]
if not ec_free:
    print("No EC-free cycles"); exit()

word = ec_free[0]
ell = len(word)
print(f"EC-free cycle: len={ell}")

# Build configs and constraints
configs = [list(start)]
for i in range(ell):
    c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
    configs.append(c)

# Collect FIXED constraints from cycle
fixed = {}  # (proc, L, S, R) -> required output
for p in range(n):
    for s in range(ell):
        ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
        if word[s] == p:
            fixed[(p, *ctx)] = configs[s+1][p]  # must be != S, specific value
        else:
            fixed[(p, *ctx)] = configs[s][p]  # must be = S

# Count free (unseen) contexts per proc
free_count = {}
for p in range(n):
    total_ctx = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
    seen = sum(1 for k in fixed if k[0] == p)
    free_count[p] = total_ctx - seen

print(f"\nFree (unseen) contexts per proc:")
for p in range(n):
    total_ctx = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
    print(f"  Proc {p} (m={ms[p]}): {free_count[p]}/{total_ctx} free")

# For "good-targeting" completion: set ALL unseen to privileged (f != S)
# This maximizes the number of privileged procs at non-cycle configs
rules_gt = {}
for p in range(n):
    rules_gt[p] = {}
    for L in range(ms[(p-1)%n]):
        for S in range(ms[p]):
            for R in range(ms[(p+1)%n]):
                key = (p, L, S, R)
                if key in fixed:
                    rules_gt[p][(L,S,R)] = fixed[key]
                else:
                    # Good-targeting: make privileged (f != S)
                    rules_gt[p][(L,S,R)] = (S + 1) % ms[p]

# Check: with good-targeting, are there still deadlocks?
all_configs_list = list(iproduct(*(range(m) for m in ms)))
cidx = {c: i for i, c in enumerate(all_configs_list)}
cycle_set = set(tuple(configs[s]) for s in range(ell))

deadlocks = 0
for c in all_configs_list:
    if tuple(c) in cycle_set: continue
    has_priv = False
    for p in range(n):
        ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
        if rules_gt[p][ctx] != c[p]:
            has_priv = True; break
    if not has_priv:
        deadlocks += 1

print(f"\nGood-targeting completion:")
print(f"  Deadlocks: {deadlocks}")

if deadlocks == 0:
    # Check convergence (no bad cycles)
    non_legit = set(range(len(all_configs_list))) - set(cidx[c] for c in cycle_set)
    nl_succs = {}
    for ci in non_legit:
        c = all_configs_list[ci]
        succs = []
        for p in range(n):
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if rules_gt[p][ctx] != c[p]:
                nc = list(c); nc[p] = rules_gt[p][ctx]
                nci = cidx[tuple(nc)]
                if nci in non_legit:
                    succs.append(nci)
        nl_succs[ci] = succs

    # Check for cycles
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {ci: WHITE for ci in non_legit}
    has_cycle = False
    for start_ci in non_legit:
        if color[start_ci] != WHITE: continue
        stack = [(start_ci, iter(nl_succs.get(start_ci, [])))]
        color[start_ci] = GRAY
        while stack:
            ci, it = stack[-1]
            try:
                nci = next(it)
                if color[nci] == GRAY:
                    has_cycle = True; break
                elif color[nci] == WHITE:
                    color[nci] = GRAY
                    stack.append((nci, iter(nl_succs.get(nci, []))))
            except StopIteration:
                color[ci] = BLACK
                stack.pop()
        if has_cycle: break

    print(f"  Bad cycle exists: {has_cycle}")
    if has_cycle:
        print(f"  *** GOOD-TARGETING DOESN'T CONVERGE (bad cycle) ***")
    else:
        print(f"  *** GOOD-TARGETING CONVERGES! POTENTIAL COUNTEREXAMPLE! ***")
        # Check token ring property
        legit_ok = True
        for c_tuple in cycle_set:
            c = list(c_tuple)
            privs = [p for p in range(n) if rules_gt[p][(c[(p-1)%n], c[p], c[(p+1)%n])] != c[p]]
            if len(privs) != 1:
                legit_ok = False
                print(f"  Legit config {c} has {len(privs)} privileged: {privs}")
        if legit_ok:
            print(f"  Token ring property: OK (exactly 1 privileged per legit config)")
else:
    print(f"  Good-targeting still has deadlocks — system invalid")
    print(f"  *** EC-free cycle CANNOT be completed to valid system ***")
