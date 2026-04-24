#!/usr/bin/env python3
"""
RA15 Part 7: The walk-topology argument for gap case EC.

P0 fires can all be in one P1-phase (21% at n=5, 21% at n=7).
So the "2 per phase" pigeonhole fails.

New approach: the ring walk topology constrains which contexts are
reachable at binary procs. Since binary procs form a CLUSTER,
the walk must bounce back and forth through the cluster.

Key insight: in the gap case, the walk spends a LOT of time in the
binary cluster (62.5% at n=5, 50% at n=7). This creates many
"return" visits where the same (L,S,R) pattern recurs.

Let me check: when P1 has no EC, does P0 ALWAYS have EC?
And what's the invariant?

Also: maybe the cleanest argument is just |M| + |NM| > space
at some proc, using walk reachability to bound |NM|.
"""
import sys, os, time
from collections import Counter, defaultdict

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


def is_gap_case(word, ms, n):
    fc = Counter(word)
    binary_pos = set(i for i in range(n) if ms[i] == 2)
    ternary_pos = set(i for i in range(n) if ms[i] == 3)
    if not any(fc[p] >= 3 for p in range(n)):
        return False
    for t in ternary_pos:
        if fc[t] < 3:
            continue
        for nbr in [(t-1)%n, (t+1)%n]:
            if nbr in binary_pos and fc[nbr] < fc[t]:
                return False
    return True


# ============================================================
# CRITICAL CHECK: When P0 fires 4 in one P1-phase
# ============================================================
print("=" * 70)
print("WHEN P0 FIRES ALL IN ONE P1-PHASE")
print("=" * 70)

ms = [2, 2, 2, 3, 3]
n = 5
words = enumerate_mover_words(ms, n, 20)
gap_words = [w for w in words if is_gap_case(w, ms, n)]

# Find gap words where P0 fires 4 times all in one P1-phase
all_in_one_words = []
for w in gap_words:
    fc = Counter(w)
    if fc[1] != 2:  # P1 fires exactly 2 (minimum gap fc pattern)
        continue

    config = [0] * n
    p0_fires_by_p1val = defaultdict(int)
    for mover in w:
        p1_val = config[1]
        if mover == 0:
            p0_fires_by_p1val[p1_val] += 1
        config[mover] = (config[mover] + 1) % ms[mover]

    vals = list(p0_fires_by_p1val.values())
    if len(vals) == 1 or (len(vals) == 2 and 0 in vals):
        all_in_one_words.append(w)

print(f"Gap words with fc[1]=2: {sum(1 for w in gap_words if Counter(w)[1]==2)}")
print(f"P0 fires all in one P1-phase: {len(all_in_one_words)}")

# Check EC for these
ec_procs_dist = Counter()
for w in all_in_one_words[:100]:
    config = [0] * n
    all_m = [set() for _ in range(n)]
    all_nm = [set() for _ in range(n)]
    for mover in w:
        for p in range(n):
            L = config[(p-1)%n]
            S = config[p]
            R = config[(p+1)%n]
            if p == mover:
                all_m[p].add((L,S,R))
            else:
                all_nm[p].add((L,S,R))
        config[mover] = (config[mover] + 1) % ms[mover]

    ec_at = [p for p in range(n) if all_m[p] & all_nm[p]]
    for p in ec_at:
        ec_procs_dist[p] += 1

checked = min(100, len(all_in_one_words))
print(f"\nEC distribution (first {checked}):")
for p in range(n):
    print(f"  P{p}: {ec_procs_dist.get(p,0)}/{checked}")


# ============================================================
# THE REAL QUESTION: what's minimum |M|+|NM| at best binary proc?
# ============================================================
print("\n" + "=" * 70)
print("MINIMUM |M|+|NM| ACROSS ALL BINARY PROCS")
print("=" * 70)

for ms, n, max_cl in [([2,2,2,3,3], 5, 20), ([2,2,2,3,3,3,3], 7, 24)]:
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if is_gap_case(w, ms, n)]
    binary_pos = [i for i in range(n) if ms[i] == 2]

    max_sum_dist = Counter()  # max(|M|+|NM|) over binary procs -> count

    for w in gap_words:
        config = [0] * n
        all_m = [set() for _ in range(n)]
        all_nm = [set() for _ in range(n)]
        for mover in w:
            for p in binary_pos:
                L = config[(p-1)%n]
                S = config[p]
                R = config[(p+1)%n]
                if p == mover:
                    all_m[p].add((L,S,R))
                else:
                    all_nm[p].add((L,S,R))
            config[mover] = (config[mover] + 1) % ms[mover]

        # For each binary: |M|+|NM| vs space
        max_sum = 0
        for p in binary_pos:
            s = len(all_m[p]) + len(all_nm[p])
            space = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
            if s > space:
                max_sum = max(max_sum, s - space)

        max_sum_dist[max_sum] += 1

    print(f"\nms={ms}: max excess (|M|+|NM| - space) at best binary proc:")
    for excess, cnt in sorted(max_sum_dist.items()):
        print(f"  excess={excess}: {cnt} words ({100*cnt/len(gap_words):.1f}%)")


# ============================================================
# BETTER: check |M|+|NM| > space at SOME binary proc
# ============================================================
print("\n" + "=" * 70)
print("|M|+|NM| > SPACE AT SOME BINARY PROC")
print("=" * 70)

for ms, n, max_cl in [([2,2,2,3,3], 5, 20), ([2,2,2,3,3,3,3], 7, 24)]:
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if is_gap_case(w, ms, n)]
    binary_pos = [i for i in range(n) if ms[i] == 2]

    some_exceeds = 0

    for w in gap_words:
        config = [0] * n
        all_m = [set() for _ in range(n)]
        all_nm = [set() for _ in range(n)]
        for mover in w:
            for p in binary_pos:
                L = config[(p-1)%n]
                S = config[p]
                R = config[(p+1)%n]
                if p == mover:
                    all_m[p].add((L,S,R))
                else:
                    all_nm[p].add((L,S,R))
            config[mover] = (config[mover] + 1) % ms[mover]

        found = False
        for p in binary_pos:
            s = len(all_m[p]) + len(all_nm[p])
            space = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
            if s > space:
                found = True
                break
        if found:
            some_exceeds += 1

    print(f"ms={ms}: |M|+|NM| > space at some binary: {some_exceeds}/{len(gap_words)} ({100*some_exceeds/len(gap_words):.1f}%)")


# ============================================================
# CHECK: does |M|+|NM| > space IMPLY EC?
# ============================================================
print("\n" + "=" * 70)
print("DOES |M|+|NM| > SPACE GUARANTEE EC?")
print("=" * 70)

print("""
If |M_distinct| + |NM_distinct| > context_space at proc p:
then by pigeonhole, some context is in both M and NM.
EC GUARANTEED.

This is a CLEAN analytical condition.
The question: is it always satisfied at some binary proc?
""")

# Already checked above. Let me also check ALL procs (not just binary)
for ms, n, max_cl in [([2,2,2,3,3], 5, 20), ([2,2,2,3,3,3,3], 7, 24)]:
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if is_gap_case(w, ms, n)]

    some_exceeds = 0
    exceeds_at_bin = 0
    exceeds_at_ter = 0
    no_exceeds = []

    for w in gap_words:
        config = [0] * n
        all_m = [set() for _ in range(n)]
        all_nm = [set() for _ in range(n)]
        for mover in w:
            for p in range(n):
                L = config[(p-1)%n]
                S = config[p]
                R = config[(p+1)%n]
                if p == mover:
                    all_m[p].add((L,S,R))
                else:
                    all_nm[p].add((L,S,R))
            config[mover] = (config[mover] + 1) % ms[mover]

        found_bin = False
        found_ter = False
        found_any = False
        for p in range(n):
            s = len(all_m[p]) + len(all_nm[p])
            space = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
            if s > space:
                found_any = True
                if ms[p] == 2:
                    found_bin = True
                else:
                    found_ter = True
        if found_any:
            some_exceeds += 1
        if found_bin:
            exceeds_at_bin += 1
        if found_ter:
            exceeds_at_ter += 1
        if not found_any:
            no_exceeds.append(w)

    print(f"\nms={ms}: {len(gap_words)} gap words")
    print(f"  |M|+|NM| > space at SOME proc: {some_exceeds}")
    print(f"  |M|+|NM| > space at some binary: {exceeds_at_bin}")
    print(f"  |M|+|NM| > space at some ternary: {exceeds_at_ter}")
    print(f"  No excess anywhere: {len(no_exceeds)}")

    if no_exceeds:
        print(f"\n  Words with no |M|+|NM| > space (first 5):")
        for w in no_exceeds[:5]:
            fc = Counter(w)
            config = [0] * n
            all_m = [set() for _ in range(n)]
            all_nm = [set() for _ in range(n)]
            for mover in w:
                for p in range(n):
                    L = config[(p-1)%n]
                    S = config[p]
                    R = config[(p+1)%n]
                    if p == mover:
                        all_m[p].add((L,S,R))
                    else:
                        all_nm[p].add((L,S,R))
                config[mover] = (config[mover] + 1) % ms[mover]

            print(f"    CL={len(w)}, fc={dict(sorted(fc.items()))}")
            for p in range(n):
                space = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
                overlap = all_m[p] & all_nm[p]
                print(f"      P{p}({'B' if ms[p]==2 else 'T'}): |M|={len(all_m[p])}, |NM|={len(all_nm[p])}, space={space}, |M|+|NM|={len(all_m[p])+len(all_nm[p])}, EC={len(overlap)}")


print("\n" + "=" * 70)
print("DONE")
print("=" * 70)
