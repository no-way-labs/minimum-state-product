#!/usr/bin/env python3
"""RA12 Phase 4: Distance pattern for EC in single-ternary systems.

At n=7, ms=[3,2,2,2,2,2,2], ternary at pos 0:
  EC at procs: {2,3,4,5} — distances 2,3,3,2 from ternary.
  NOT at procs: {0(ternary), 1(dist=1), 6(dist=1)}

The "distance 1" binary procs (direct neighbors of ternary) never have EC.
This script verifies the distance pattern.
"""

from collections import Counter
from itertools import product as iproduct


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                     if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)


def get_phases(word, cycle, t, n):
    ell = len(word)
    t_steps = [s for s in range(ell) if word[s] == t]
    if not t_steps:
        return []
    bL = (t - 1) % n
    bR = (t + 1) % n
    phases = []
    for idx in range(len(t_steps)):
        start = t_steps[idx]
        end = t_steps[(idx + 1) % len(t_steps)]
        phase_steps = []
        s = (start + 1) % ell
        while s != end:
            phase_steps.append(s)
            s = (s + 1) % ell
        J = sum(1 for s in phase_steps if word[s] == bL)
        K = sum(1 for s in phase_steps if word[s] == bR)
        phases.append({'J': J, 'K': K})
    return phases


def check_ec_all_procs(word, cycle, ms, n):
    ell = len(word)
    result = {}
    for p in range(n):
        bL = (p - 1) % n
        bR = (p + 1) % n
        mover = set()
        nonmover = set()
        for s in range(ell):
            ctx = (cycle[s][bL], cycle[s][p], cycle[s][bR])
            if word[s] == p:
                mover.add(ctx)
            else:
                nonmover.add(ctx)
        result[p] = len(mover & nonmover) > 0
    return result


print("=" * 70)
print("DISTANCE PATTERN: EC vs distance from ternary (single-ternary systems)")
print("=" * 70)

for n in [5, 7]:
    print(f"\n--- n={n} ---")
    t_pos = 0  # Put ternary at position 0

    ms = [2] * n
    ms[t_pos] = 3

    words = enumerate_mover_words(ms, n, max_length=22 if n == 7 else 20)

    ec_by_dist = Counter()
    total_by_dist = Counter()

    total_cycles = 0
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        phases = get_phases(word, cycle, t_pos, n)
        has_11 = any(p['J'] == 1 and p['K'] == 1 for p in phases)
        if not has_11:
            continue
        total_cycles += 1

        ec_result = check_ec_all_procs(word, cycle, ms, n)
        for p in range(n):
            dist = min(abs(p - t_pos), n - abs(p - t_pos))
            total_by_dist[dist] += 1
            if ec_result[p]:
                ec_by_dist[dist] += 1

    print(f"  Total (1,1) cycles: {total_cycles}")
    print(f"  EC rate by distance from ternary:")
    for dist in sorted(total_by_dist.keys()):
        cnt = ec_by_dist.get(dist, 0)
        tot = total_by_dist[dist]
        pct = 100 * cnt / tot if tot > 0 else 0
        print(f"    dist={dist}: {cnt}/{tot} ({pct:.0f}%)")


# =====================================================================
# WHY distance-1 binary procs avoid EC
# =====================================================================

print("\n" + "=" * 70)
print("WHY distance-1 binary avoids EC (n=5)")
print("=" * 70)

n = 5
ms = [2, 2, 2, 2, 3]
t_pos = 4

words = enumerate_mover_words(ms, n, max_length=20)

# Proc 3 is distance 1 from ternary (left neighbor of proc 4)
# Proc 0 is distance 1 from ternary (right neighbor of proc 4)
# Why don't they have EC?

# Proc 3: context = (c[2], c[3], c[4])
# When proc 3 fires (mover): c[4] = ternary state
# When proc 3 is non-mover: c[4] = some ternary state

# Key: ternary has 3 values. Each (c[2], c[3]) pair combined with any of 3 c[4] values
# gives different contexts. The 3 ternary values provide enough "room" to separate.

count = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    phases = get_phases(word, cycle, t_pos, n)
    has_11 = any(p['J'] == 1 and p['K'] == 1 for p in phases)
    if not has_11:
        continue
    if count >= 1:
        break
    count += 1

    ell = len(word)
    print(f"\nWord: {word}")

    # Proc 3 (distance 1, left of ternary)
    p = 3
    bL, bR = 2, 4
    print(f"\nProc {p} (dist=1 from ternary): context = (c[{bL}], c[{p}], c[{bR}])")
    print(f"  Note: c[{bR}] = TERNARY value (0,1,2)")

    mover_ctxs = []
    nonmover_ctxs = []
    for s in range(ell):
        ctx = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p:
            mover_ctxs.append((s, ctx))
        else:
            nonmover_ctxs.append((s, ctx))

    print(f"  Mover contexts: {[ctx for _, ctx in mover_ctxs]}")
    print(f"  Non-mover contexts: {sorted(set(ctx for _, ctx in nonmover_ctxs))}")
    print(f"  Overlap: {set(ctx for _, ctx in mover_ctxs) & set(ctx for _, ctx in nonmover_ctxs)}")

    # Proc 1 (distance 2, EC always present)
    p = 1
    bL, bR = 0, 2
    print(f"\nProc {p} (dist=2 from ternary): context = (c[{bL}], c[{p}], c[{bR}])")
    print(f"  Note: ALL values are binary (0,1)")

    mover_ctxs = []
    nonmover_ctxs = []
    for s in range(ell):
        ctx = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p:
            mover_ctxs.append((s, ctx))
        else:
            nonmover_ctxs.append((s, ctx))

    print(f"  Mover contexts: {[ctx for _, ctx in mover_ctxs]}")
    print(f"  Non-mover contexts: {sorted(set(ctx for _, ctx in nonmover_ctxs))}")
    print(f"  Overlap: {set(ctx for _, ctx in mover_ctxs) & set(ctx for _, ctx in nonmover_ctxs)}")
    print(f"  Total possible (L,S,R) triples with all-binary: 2*2*2 = 8")
    print(f"  Mover uses: {len(set(ctx for _, ctx in mover_ctxs))} distinct")
    print(f"  Non-mover uses: {len(set(ctx for _, ctx in nonmover_ctxs))} distinct")
    print(f"  Combined: {len(set(ctx for _, ctx in mover_ctxs) | set(ctx for _, ctx in nonmover_ctxs))} / 8")

print("""
STRUCTURAL EXPLANATION:

Distance-1 binary (adjacent to ternary):
  Its context includes the ternary state (0,1,2). With 3 possible ternary values
  in the right neighbor, the context space is 2*2*3 = 12. The cycle uses only
  a subset, and the ternary value provides enough separation between mover and
  non-mover contexts.

Distance-2+ binary (all binary neighbors):
  Its context is (binary, binary, binary), giving only 2*2*2 = 8 possible
  triples. With 2 mover firings and many non-mover appearances, pigeonhole
  forces overlap. The binary proc fires twice (m=2), using 2 of 8 slots as
  mover contexts, while non-mover contexts use 5+ of 8 slots. Overlap is
  nearly guaranteed.

This explains the sharp boundary:
  - Distance 0 (ternary itself): 3 mover contexts, 3 distinct t-values → no overlap with non-mover
  - Distance 1 (binary with ternary neighbor): 12-slot context space → enough room
  - Distance 2+ (all-binary context): 8-slot space, 2 mover + 5+ non-mover → pigeonhole forces overlap
""")
