#!/usr/bin/env python3
"""
What cycles does each sorry need to handle?

The master theorem splits on:
1. Zero winding vs non-zero winding
2. Within zero winding: consecutive binary vs non-consecutive
3. Within non-zero winding: sweep vs odd-winding

For each category: how many cycles exist at n=5? n=7?
Do they ALL have entry conflict (brute force)?
If so: the sorry is "just" routing to the right mechanism.
If not: the sorry has genuine mathematical content.
"""
from itertools import product as iproduct
from collections import Counter
import time

def analyze_landscape(n, ms, max_len):
    binary_procs = [p for p in range(n) if ms[p] == 2]
    ternary_procs = [p for p in range(n) if ms[p] == 3]

    # Check consecutive binary
    has_3consec = False
    for i in range(n):
        if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
            has_3consec = True
            break

    all_configs = list(iproduct(*(range(m) for m in ms)))
    cidx = {c: i for i, c in enumerate(all_configs)}
    total = len(all_configs)
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    start = tuple(0 for _ in range(n))

    # Find all good cycles (mover words)
    results = []
    def dfs(word, fc, config):
        if len(word) > max_len: return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

    print(f"\nn={n}, ms={ms}, 3-consec={has_3consec}")
    print(f"Total good cycles: {len(results)}")

    # Classify by winding
    zero_wind = 0
    nonzero_wind = 0

    def winding(word):
        w = 0
        for i in range(len(word)):
            d = (word[(i+1)%len(word)] - word[i]) % n
            if d == 1: w += 1
            elif d == n-1: w -= 1
        return w

    def has_ec(word):
        ell = len(word)
        configs = [list(start)]
        for i in range(ell):
            c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
            configs.append(c)
        for p in range(n):
            mover_ctx = set()
            nonmover_ctx = set()
            for s in range(ell):
                ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
                if word[s] == p:
                    if ctx in nonmover_ctx: return True
                    mover_ctx.add(ctx)
                else:
                    if ctx in mover_ctx: return True
                    nonmover_ctx.add(ctx)
        return False

    cats = Counter()
    ec_cats = Counter()

    for word in results:
        w = winding(word)
        if w == 0:
            cat = 'zero_wind'
        elif abs(w) >= 2*n:
            cat = 'sweep'
        elif abs(w) == n:
            cat = 'odd_wind'
        else:
            cat = f'other_wind_{w}'

        cats[cat] += 1
        if has_ec(word):
            ec_cats[cat] += 1

    print(f"\nCategory breakdown:")
    for cat in sorted(cats):
        ec = ec_cats.get(cat, 0)
        total_cat = cats[cat]
        pct = 100*ec/total_cat if total_cat > 0 else 0
        print(f"  {cat}: {total_cat} cycles, {ec} have EC ({pct:.0f}%)")
        if ec < total_cat:
            print(f"    *** {total_cat - ec} cycles WITHOUT EC ***")

# Test cases
# Consecutive binary
analyze_landscape(5, [2,2,2,3,3], 16)

# Non-consecutive binary
analyze_landscape(5, [2,3,2,3,2], 16)

# Larger consecutive
analyze_landscape(7, [2,2,2,3,3,3,3], 20)
