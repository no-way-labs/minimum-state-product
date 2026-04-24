#!/usr/bin/env python3
"""Quick check: do the 242 uncovered cycles at n=5 still have EC (brute force)?"""
from collections import Counter

n = 5
ms = [2,3,2,3,2]
sandwiched = [1, 3]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

results = []
def dfs(word, fc, config):
    if len(word) > 16: return
    if len(word) >= 2*n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
        return
    remaining = 16 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        nf = list(fc); nf[nxt] += 1
        word.append(nxt)
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

def temporal_order(steps, ell):
    if len(steps) <= 1: return steps
    max_gap = 0; start_after = 0
    for i in range(len(steps)):
        nxt = (i+1) % len(steps)
        gap = (steps[nxt] - steps[i]) % ell
        if gap > max_gap: max_gap = gap; start_after = i
    si = (start_after+1) % len(steps)
    return [steps[(si+i) % len(steps)] for i in range(len(steps))]

def check_4mech(word, configs, t, ell):
    bL, bR = (t-1)%n, (t+1)%n
    for k in range(3):
        raw = sorted(s for s in range(ell) if configs[s][t] == k)
        steps = temporal_order(raw, ell)
        M = sum(1 for s in steps if word[s] == t)
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        if M == 1 and J%2==0 and K%2==0: return True
        if (J>=3 and K==0) or (J==0 and K>=3): return True
        if M==1 and ((J>=2 and K==0) or (J==0 and K>=2)): return True
        if M==1 and (J,K) in [(2,1),(1,2)]:
            single = bR if J==2 else bL
            for s in steps:
                if word[s] in (bL,bR):
                    if word[s] == single: return True
                    break
    return False

def brute_ec(word, configs, ell):
    """Check EC at ANY proc (not just sandwiched)."""
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for s in range(ell):
            ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
            if word[s] == p:
                if ctx in nonmover_ctx: return True, p
                mover_ctx.add(ctx)
            else:
                if ctx in mover_ctx: return True, p
                nonmover_ctx.add(ctx)
    return False, None

uncovered = []
for word in results:
    ell = len(word)
    configs = [list(start)]
    for i in range(ell):
        c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs.append(c)

    covered = any(check_4mech(word, configs, t, ell) for t in sandwiched)
    if not covered:
        uncovered.append((word, configs))

print(f"Total uncovered by 4 mechanisms: {len(uncovered)}")

# Check brute force EC
ec_count = 0
ec_procs = Counter()
no_ec = 0
for word, configs in uncovered:
    ell = len(word)
    has, p = brute_ec(word, configs, ell)
    if has:
        ec_count += 1
        ec_procs[p] += 1
    else:
        no_ec += 1
        if no_ec <= 3:
            print(f"  NO EC: word={word}")

print(f"\nUncovered cycles with brute-force EC: {ec_count}/{len(uncovered)}")
print(f"EC proc distribution: {dict(sorted(ec_procs.items()))}")
print(f"NO EC at all: {no_ec}")
if no_ec == 0:
    print("*** All uncovered cycles still have EC (at non-sandwiched procs!) ***")
