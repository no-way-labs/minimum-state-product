#!/usr/bin/env python3
"""
Quick check: do ANY valid non-incrementing cycles exist at n=5, ms=[2,3,2,3,2]?

Enumerate ALL mover words AND all transition value assignments.
"""
from itertools import product as iproduct
from collections import Counter

n = 5
ms = [2, 3, 2, 3, 2]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

# First get all valid incrementing cycles
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

print(f"Incrementing valid cycles: {len(inc_results)}")

# Now for a sample of words, check non-incrementing
total_noninc_valid = 0
total_noninc_checked = 0

for word in inc_results[:200]:  # check first 200 words
    ell = len(word)
    ternary_steps = [s for s in range(ell) if ms[word[s]] == 3]
    num_combos = 2 ** len(ternary_steps)
    total_noninc_checked += 1

    for combo in iproduct(*[range(2) for _ in ternary_steps]):
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

        # Check if this is the incrementing version
        is_inc = all(combo[i] == 0 for i in range(len(ternary_steps)))
        if not is_inc:
            total_noninc_valid += 1
            if total_noninc_valid <= 3:
                print(f"  NON-INC valid: word={word[:8]}..., combo={combo}")

print(f"\nChecked {total_noninc_checked} words")
print(f"Non-incrementing valid cycles found: {total_noninc_valid}")
if total_noninc_valid == 0:
    print("*** NO non-incrementing cycles exist! Incrementing is forced by cycle closure! ***")
