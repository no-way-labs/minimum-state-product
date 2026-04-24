#!/usr/bin/env python3
"""
RA12: Where do entry conflicts occur in gap cases?
Are they at ternary or binary? Interior or boundary?
"""
import sys, os, time
from collections import Counter

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)

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


def find_all_ec_procs(ms, n, word):
    """Find ALL procs with entry conflict."""
    config = tuple(0 for _ in range(n))
    configs = [config]
    for p in word:
        nc = list(config)
        nc[p] = (nc[p] + 1) % ms[p]
        config = tuple(nc)
        configs.append(config)

    cl = len(word)
    ec_procs = []
    for t in range(n):
        mover_ctxs = set()
        nonmover_ctxs = set()
        for step in range(cl):
            p = word[step]
            L = configs[step][(t - 1) % n]
            S = configs[step][t]
            R = configs[step][(t + 1) % n]
            ctx = (L, S, R)
            if p == t:
                mover_ctxs.add(ctx)
            else:
                nonmover_ctxs.add(ctx)
        if mover_ctxs & nonmover_ctxs:
            ec_procs.append(t)
    return ec_procs


ms = [3, 3, 3, 2, 2, 2, 3]
n = 7
binary_pos = [i for i in range(n) if ms[i] == 2]
ternary_pos = [i for i in range(n) if ms[i] == 3]
boundary_ter = [t for t in ternary_pos
                if ms[(t-1) % n] == 2 or ms[(t+1) % n] == 2]
interior_ter = [t for t in ternary_pos
                if ms[(t-1) % n] != 2 and ms[(t+1) % n] != 2]

print(f"ms={ms}")
print(f"binary={binary_pos}, ternary={ternary_pos}")
print(f"boundary_ter={boundary_ter}, interior_ter={interior_ter}")

max_cl = sum(ms) + 4
words = enumerate_mover_words(ms, n, max_cl)

# Find gap cases and check where EC occurs
print(f"\nAnalyzing gap cases...")
ec_location_counter = Counter()  # (proc_type, proc_idx) -> count
ec_at_types = Counter()  # type -> count

for word in words:
    fc = Counter(word)
    if not any(fc[p] >= 3 for p in range(n)):
        continue

    # Check if gap
    satisfies_A = any(
        (fc[t] >= 3 and ms[(t-1)%n] == 2 and fc[(t-1)%n] < fc[t])
        or (fc[t] >= 3 and ms[(t+1)%n] == 2 and fc[(t+1)%n] < fc[t])
        for t in ternary_pos
    )
    if satisfies_A:
        continue

    # Gap case
    ec_procs = find_all_ec_procs(ms, n, word)
    for p in ec_procs:
        if ms[p] == 2:
            typ = "binary"
        elif p in boundary_ter:
            typ = "boundary_ter"
        else:
            typ = "interior_ter"
        ec_location_counter[(typ, p)] += 1
        ec_at_types[typ] += 1

print(f"\nEC location distribution in gap cases:")
for (typ, p), count in sorted(ec_location_counter.items()):
    print(f"  proc {p} ({typ}): {count}")
print(f"\nBy type: {dict(ec_at_types)}")

# Now check: is there always an EC at a boundary ternary or binary?
print(f"\nDetailed check: does every gap word have EC at boundary_ter or binary?")
n_gap = 0
n_gap_ec_boundary_or_bin = 0
n_gap_ec_interior_only = 0

for word in words:
    fc = Counter(word)
    if not any(fc[p] >= 3 for p in range(n)):
        continue
    satisfies_A = any(
        (fc[t] >= 3 and ms[(t-1)%n] == 2 and fc[(t-1)%n] < fc[t])
        or (fc[t] >= 3 and ms[(t+1)%n] == 2 and fc[(t+1)%n] < fc[t])
        for t in ternary_pos
    )
    if satisfies_A:
        continue

    n_gap += 1
    ec_procs = find_all_ec_procs(ms, n, word)

    has_boundary_or_bin = any(
        ms[p] == 2 or p in boundary_ter
        for p in ec_procs
    )
    if has_boundary_or_bin:
        n_gap_ec_boundary_or_bin += 1
    else:
        n_gap_ec_interior_only += 1

print(f"  Gap words: {n_gap}")
print(f"  EC at boundary/binary: {n_gap_ec_boundary_or_bin}")
print(f"  EC at interior only: {n_gap_ec_interior_only}")

# Finally: The KEY question.
# In the gap case, the EC is at interior ternary procs (0 and 1).
# These have NO binary neighbor. The EC comes from ternary-ternary interaction.
# This means the phase_dispatch approach is irrelevant for these cases.
# A completely different mechanism produces the EC.

print("\n" + "=" * 70)
print("ANALYZING THE GAP CASE EC MECHANISM")
print("=" * 70)

# Pick one gap word and trace exactly how EC arises
for word in words:
    fc = Counter(word)
    if not any(fc[p] >= 3 for p in range(n)):
        continue
    satisfies_A = any(
        (fc[t] >= 3 and ms[(t-1)%n] == 2 and fc[(t-1)%n] < fc[t])
        or (fc[t] >= 3 and ms[(t+1)%n] == 2 and fc[(t+1)%n] < fc[t])
        for t in ternary_pos
    )
    if satisfies_A:
        continue

    fc_dict = {p: fc[p] for p in range(n)}
    print(f"\nGap word: {word}")
    print(f"fc = {fc_dict}")

    # Build configs
    config = tuple(0 for _ in range(n))
    configs = [config]
    for p in word:
        nc = list(config)
        nc[p] = (nc[p] + 1) % ms[p]
        config = tuple(nc)
        configs.append(config)

    # Find EC at interior ternary (proc 0 and 1)
    for t in [0, 1]:
        mover_ctxs = {}
        nonmover_ctxs = {}
        for step in range(len(word)):
            p = word[step]
            L = configs[step][(t - 1) % n]
            S = configs[step][t]
            R = configs[step][(t + 1) % n]
            ctx = (L, S, R)
            if p == t:
                mover_ctxs[ctx] = mover_ctxs.get(ctx, []) + [step]
            else:
                nonmover_ctxs[ctx] = nonmover_ctxs.get(ctx, []) + [step]

        overlap = set(mover_ctxs.keys()) & set(nonmover_ctxs.keys())
        if overlap:
            print(f"\n  EC at proc {t} (ms={ms[t]}, neighbors: L=ms{ms[(t-1)%n]}, R=ms{ms[(t+1)%n]}):")
            for ctx in overlap:
                print(f"    Context {ctx}: mover at steps {mover_ctxs[ctx]}, nonmover at steps {nonmover_ctxs[ctx]}")

    break  # just one example
