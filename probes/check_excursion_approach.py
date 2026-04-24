#!/usr/bin/env python3
"""
DERISK: Does the excursion/scatterer approach work?

For every cycle that our sorry's need to handle:
1. Project the mover walk onto the binary triple {i, ri, rri}
2. Classify each visit: trapped / sweep / reflect
3. Check: does the cycle-walk dichotomy (drift OR 2 reversals) hold?
4. Does the existing shadow infrastructure handle it?

If yes → the approach is sound. If no → we need more.
"""
from itertools import product as iproduct
from collections import Counter

n = 7
ms = [2, 2, 2, 3, 3, 3, 3]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

results = []
def dfs(word, fc, config):
    if len(word) > 20: return
    if len(word) >= 2*n and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
            if len(results) >= 500: return
        return
    if len(results) >= 500: return
    remaining = 20 - len(word)
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

print(f"n={n}, ms={ms}, {len(results)} cycles")

# Binary triple: {0, 1, 2}
triple = {0, 1, 2}

def winding(word):
    w = 0
    for i in range(len(word)):
        d = (word[(i+1)%len(word)] - word[i]) % n
        if d == 1: w += 1
        elif d == n-1: w -= 1
    return w

# For each cycle: classify the mover walk's relationship to the triple
sweep_count = 0
reflect_count = 0
trapped_count = 0
mixed_count = 0
has_ec_count = 0

for word in results:
    ell = len(word)
    w = winding(word)

    # Find maximal "visits" to the triple: contiguous runs where mover ∈ triple
    visits = []
    in_triple = False
    visit_start = -1
    for t in range(ell):
        if word[t] in triple:
            if not in_triple:
                visit_start = t
                in_triple = True
        else:
            if in_triple:
                visits.append((visit_start, t - 1))
                in_triple = False
    if in_triple:
        visits.append((visit_start, ell - 1))

    # If mover is ALWAYS in triple: trapped
    if len(visits) == 1 and visits[0] == (0, ell - 1):
        trapped_count += 1
        continue
    if not visits:
        # Mover never visits triple — shouldn't happen with 3 binary
        continue

    # Classify each visit: does the mover enter from left or right, exit left or right?
    visit_types = []
    for vs, ve in visits:
        if vs == 0:
            entry_side = 'unknown'
        else:
            prev = word[vs - 1]
            if prev < word[vs]:  # came from left (lower index)
                entry_side = 'L'
            else:
                entry_side = 'R'

        if ve == ell - 1:
            exit_side = 'unknown'
        else:
            nxt = word[ve + 1]
            if nxt > word[ve]:  # exits to right
                exit_side = 'R'
            else:
                exit_side = 'L'

        if entry_side == exit_side and entry_side != 'unknown':
            visit_types.append('reflect')
        elif entry_side != exit_side and entry_side != 'unknown' and exit_side != 'unknown':
            visit_types.append('sweep')
        else:
            visit_types.append('unknown')

    # Count reversals in the full mover word
    reversals = 0
    for t in range(ell):
        d1 = (word[(t+1)%ell] - word[t]) % n
        d2 = (word[(t+2)%ell] - word[(t+1)%ell]) % n
        s1 = 1 if d1 == 1 else (-1 if d1 == n-1 else 0)
        s2 = 1 if d2 == 1 else (-1 if d2 == n-1 else 0)
        if s1 != 0 and s2 != 0 and s1 != s2:
            reversals += 1

    # Classify cycle
    if abs(w) >= 2*n:
        cycle_type = 'sweep'
        sweep_count += 1
    elif reversals >= 2:
        cycle_type = 'wiggle'
        reflect_count += 1
    elif reversals == 0:
        cycle_type = 'uniform'
        sweep_count += 1
    else:
        cycle_type = f'rev={reversals}'
        mixed_count += 1

print(f"\nCycle classification:")
print(f"  Sweep/uniform: {sweep_count}")
print(f"  Wiggle (≥2 reversals): {reflect_count}")
print(f"  Trapped: {trapped_count}")
print(f"  Mixed/other: {mixed_count}")

# KEY CHECK: does every cycle fall into sweep, wiggle, or trapped?
total = sweep_count + reflect_count + trapped_count + mixed_count
uncovered = mixed_count  # cycles with exactly 1 reversal
print(f"\nTotal: {total}")
print(f"Covered by sweep+wiggle+trapped: {total - uncovered}")
print(f"Uncovered (1 reversal): {uncovered}")

if uncovered == 0:
    print("*** ALL CYCLES COVERED by excursion approach ***")
else:
    print(f"*** {uncovered} cycles need additional handling ***")
    # What are the 1-reversal cycles?
    for word in results[:500]:
        ell = len(word)
        revs = 0
        for t in range(ell):
            d1 = (word[(t+1)%ell] - word[t]) % n
            d2 = (word[(t+2)%ell] - word[(t+1)%ell]) % n
            s1 = 1 if d1 == 1 else (-1 if d1 == n-1 else 0)
            s2 = 1 if d2 == 1 else (-1 if d2 == n-1 else 0)
            if s1 != 0 and s2 != 0 and s1 != s2:
                revs += 1
        w = winding(word)
        if revs == 1 and abs(w) < 2*n:
            print(f"  1-rev cycle: w={w}, word={word[:10]}...")
            break
