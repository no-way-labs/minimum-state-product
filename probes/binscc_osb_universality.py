#!/usr/bin/env python3
"""Why does every wrap-adjacent cycle have an SR-OSB phase?

An SR-OSB phase at ternary t means: in some phase k,
  min(bLf, bRf) = 0 and max(bLf, bRf) >= 2
i.e., one binary neighbor fires >=2 times, the other fires 0.

Goal: understand the STRUCTURAL reason this always occurs.

Approach: For each ternary t, compute the firing pattern of its
binary neighbors across t's phases. Look for constraints that
force at least one one-sided bounce phase.
"""
import sys, time
from collections import Counter

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

print("=" * 70)
print("SR-OSB UNIVERSALITY ANALYSIS")
print("=" * 70)

n, ms = 6, [2, 3, 2, 3, 2, 3]
tern = [1, 3, 5]

t0 = time.time()
words = enumerate_mover_words(ms, n, 24)
print(f"Words: {len(words)} ({time.time()-t0:.1f}s)")

# PART 1: For each ternary, what is the (bLf, bRf) profile across phases?
print(f"\nPART 1: PHASE FIRING PROFILES PER TERNARY")

profile_dist = Counter()  # (bLf_vec, bRf_vec) across 3 phases
all_osb_by_ternary = Counter()  # which ternary provides the OSB

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    for t in tern:
        if fc[t] > ms[t]:
            continue  # skip multi-round
        bL = (t - 1) % n
        bR = (t + 1) % n

        bLf_vec = []
        bRf_vec = []
        for k in range(ms[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            bLf = sum(1 for s in ps if word[s] == bL)
            bRf = sum(1 for s in ps if word[s] == bR)
            bLf_vec.append(bLf)
            bRf_vec.append(bRf)

        profile = (tuple(bLf_vec), tuple(bRf_vec))
        profile_dist[profile] += 1

        # Check if this ternary has an OSB phase
        has_osb = any(min(bLf_vec[k], bRf_vec[k]) == 0 and
                      max(bLf_vec[k], bRf_vec[k]) >= 2
                      for k in range(ms[t]))
        if has_osb:
            all_osb_by_ternary[t] += 1

print(f"\n  OSB providers by ternary: {dict(all_osb_by_ternary)}")

print(f"\n  Top 20 phase profiles (bLf_vec, bRf_vec) for single-round ternary:")
for (bLf, bRf), cnt in profile_dist.most_common(20):
    has_osb = any(min(bLf[k], bRf[k]) == 0 and max(bLf[k], bRf[k]) >= 2
                  for k in range(len(bLf)))
    print(f"    bL={bLf}, bR={bRf}: {cnt}  {'OSB' if has_osb else 'no-OSB'}")

# PART 2: Which profiles are NOT OSB? What do they look like?
print(f"\n{'='*60}")
print("PART 2: NON-OSB PROFILES")

non_osb_profiles = Counter()
for (bLf, bRf), cnt in profile_dist.items():
    has_osb = any(min(bLf[k], bRf[k]) == 0 and max(bLf[k], bRf[k]) >= 2
                  for k in range(len(bLf)))
    if not has_osb:
        non_osb_profiles[(bLf, bRf)] += cnt

print(f"  Non-OSB profiles (ternary with NO one-sided bounce phase):")
for (bLf, bRf), cnt in non_osb_profiles.most_common(30):
    # Classify each phase
    phases = []
    for k in range(len(bLf)):
        if bLf[k] == 0 and bRf[k] == 0:
            phases.append("empty")
        elif bLf[k] == 0 and bRf[k] == 1:
            phases.append("R1")
        elif bLf[k] == 1 and bRf[k] == 0:
            phases.append("L1")
        elif bLf[k] == 1 and bRf[k] == 1:
            phases.append("sweep")
        elif min(bLf[k], bRf[k]) >= 1:
            phases.append(f"mixed({bLf[k]},{bRf[k]})")
        else:
            phases.append(f"({bLf[k]},{bRf[k]})")
    print(f"    bL={bLf}, bR={bRf}: {cnt}  [{', '.join(phases)}]")

# PART 3: For cycles where some ternary is non-OSB,
# does ANOTHER ternary always have OSB?
print(f"\n{'='*60}")
print("PART 3: OSB COVERAGE - PER-CYCLE ANALYSIS")

total_cycles = 0
any_osb = 0
no_osb_count = 0
osb_ternary_count = Counter()  # how many ternary have OSB per cycle

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total_cycles += 1
    ell = len(word)
    fc = Counter(word)

    osb_set = set()
    for t in tern:
        if fc[t] > ms[t]:
            continue
        bL = (t - 1) % n
        bR = (t + 1) % n

        for k in range(ms[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            bLf = sum(1 for s in ps if word[s] == bL)
            bRf = sum(1 for s in ps if word[s] == bR)
            if min(bLf, bRf) == 0 and max(bLf, bRf) >= 2:
                osb_set.add(t)
                break

    osb_ternary_count[len(osb_set)] += 1
    if osb_set:
        any_osb += 1
    else:
        no_osb_count += 1

print(f"  Total cycles: {total_cycles}")
print(f"  Any ternary has OSB: {any_osb}/{total_cycles} ({100*any_osb/total_cycles:.1f}%)")
print(f"  No ternary has OSB: {no_osb_count}")
print(f"  OSB ternary count distribution: {dict(osb_ternary_count)}")

# PART 4: Total binary firings per ternary's phases (sum constraint)
# Each binary fires ms[b]*k times total. For alternating n=6, each binary fires 4.
# These 4 firings are distributed across the 3 phases of each adjacent ternary.
# bL fires sum(bLf_vec) = 4 times across 3 phases of t.
# Similarly bR fires 4 times.
# For NO phase to be OSB:
#   For each phase k: bLf[k]>0 and bRf[k]>0 (both fire), OR max=0 or max=1
#   i.e., no phase has (one≥2, other=0)
# Constraint: both bL and bR must fire in every non-trivial phase.
print(f"\n{'='*60}")
print("PART 4: FIRING SUM CONSTRAINTS")

# For non-OSB ternary: compute total bL, bR firings
non_osb_sums = Counter()
for (bLf, bRf), cnt in non_osb_profiles.items():
    non_osb_sums[(sum(bLf), sum(bRf))] += cnt

print(f"  Non-OSB ternary (total bL, bR firings): {dict(non_osb_sums)}")

# PART 5: DETAILED: For each non-OSB ternary, how are firings distributed?
# A ternary is non-OSB if every phase has either:
#   (a) max(bLf,bRf) <= 1 (no big bounce), OR
#   (b) min(bLf,bRf) >= 1 (both sides fire)
# These can be classified into:
#   - "all-sweep" (every phase has bLf=bRf=1 or both small)
#   - "mixed" (some phases have both sides firing > 1)

print(f"\n{'='*60}")
print("PART 5: NON-OSB CLASSIFICATION")

non_osb_types = Counter()
for (bLf, bRf), cnt in non_osb_profiles.items():
    phase_types = []
    for k in range(len(bLf)):
        mn, mx = min(bLf[k], bRf[k]), max(bLf[k], bRf[k])
        if mx == 0:
            phase_types.append("null")
        elif mx == 1 and mn == 0:
            phase_types.append("single")  # exactly 1 firing, can't be OSB
        elif mn == 1 and mx == 1:
            phase_types.append("sweep")
        elif mn >= 1:
            phase_types.append("both")
        else:
            phase_types.append("other")
    non_osb_types[tuple(sorted(phase_types))] += cnt

print(f"  Non-OSB phase type distribution:")
for types, cnt in non_osb_types.most_common(20):
    print(f"    {types}: {cnt}")

# PART 6: KEY INSIGHT - What fraction of ternary are multi-round
# in cycles where ALL ternary are non-OSB?
print(f"\n{'='*60}")
print("PART 6: MULTI-ROUND ANALYSIS IN HYPOTHETICAL NO-OSB CYCLES")
print("(Checking if multi-round ternary can rescue)")

# Since no_osb_count = 0, we can't test this directly.
# Instead, test: for each ternary that is non-OSB, is it multi-round?
non_osb_multi = Counter()
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    for t in tern:
        bL = (t - 1) % n
        bR = (t + 1) % n
        is_multi = fc[t] > ms[t]

        has_osb = False
        if not is_multi:
            for k in range(ms[t]):
                ps = [s for s in range(ell) if cycle[s][t] == k]
                bLf = sum(1 for s in ps if word[s] == bL)
                bRf = sum(1 for s in ps if word[s] == bR)
                if min(bLf, bRf) == 0 and max(bLf, bRf) >= 2:
                    has_osb = True
                    break

        if not has_osb and not is_multi:
            non_osb_multi[is_multi] += 1

print(f"  Non-OSB ternary: multi-round status: {dict(non_osb_multi)}")

# PART 7: CRITICAL - for single-round ternary, total firings = ms[t] = 3.
# Each binary neighbor fires exactly 4 times total (since ms[b]=2, fires 2*2=4).
# These 4 firings distributed across 3 phases.
# For non-OSB: need min(bLf[k],bRf[k])>=1 at every phase where max>=2,
# AND max<=1 at phases where min=0.
# But bL fires 4 times across 3 phases. If every phase where bL>=2 also has bR>=1,
# and bR fires 4 times across 3 phases similarly...
# Integer partition constraint!
print(f"\n{'='*60}")
print("PART 7: INTEGER PARTITION ARGUMENT")
print("bL fires 4 times across 3 phases. bR fires 4 times across 3 phases.")
print("Non-OSB requires: no phase has (one>=2, other=0)")
print("")

# Enumerate all partitions of 4 into 3 non-negative parts
from itertools import product as iproduct
partitions = []
for a in range(5):
    for b in range(5-a):
        c = 4 - a - b
        if c >= 0:
            partitions.append((a, b, c))

print(f"  Partitions of 4 into 3 parts: {len(partitions)}")

# For each pair of partitions (bL, bR), check if non-OSB is possible
non_osb_partitions = []
for bL_part in partitions:
    for bR_part in partitions:
        # Check all permutations of bR_part (phases can be matched differently)
        # Actually, phases are fixed, so we check the given assignment
        is_osb = False
        for k in range(3):
            if min(bL_part[k], bR_part[k]) == 0 and max(bL_part[k], bR_part[k]) >= 2:
                is_osb = True
                break
        if not is_osb:
            non_osb_partitions.append((bL_part, bR_part))

print(f"  Partition pairs that are non-OSB: {len(non_osb_partitions)}")
for bL, bR in non_osb_partitions[:30]:
    phases = []
    for k in range(3):
        phases.append(f"({bL[k]},{bR[k]})")
    print(f"    bL={bL}, bR={bR}  phases: {', '.join(phases)}")

# Check: how many of these have some phase with BOTH >= 1?
print(f"\n  Non-OSB partition pairs with every phase having min>=1 or max<=1:")
for bL, bR in non_osb_partitions:
    can_happen = True
    for k in range(3):
        # Phase must have: (min>=1) or (max<=1)
        if min(bL[k], bR[k]) == 0 and max(bL[k], bR[k]) >= 2:
            can_happen = False
    if can_happen:
        # But also: sum(bL) = 4 and sum(bR) = 4
        assert sum(bL) == 4 and sum(bR) == 4

# Actually, let's check: for non-OSB, every phase must have
# min(bLf,bRf) >= 1 OR max(bLf,bRf) <= 1
# Phases with max<=1: contribute at most 1 to each sum
# Phases with min>=1: both contribute >=1

# If p phases have max<=1 and (3-p) have min>=1:
# sum(bL) = sum_max1(bL) + sum_min1(bL) <= p + sum_min1(bL) = 4
# sum(bR) = sum_max1(bR) + sum_min1(bR) <= p + sum_min1(bR) = 4
# sum_min1(bL) >= (3-p), sum_min1(bR) >= (3-p)
# So sum(bL) <= p + (remaining bL from min1 phases)
# If p=0: all 3 phases have min>=1, so bL[k]>=1, bR[k]>=1 for all k
#   sum(bL) >= 3, sum(bR) >= 3. With sum=4 each: one phase gets 2, others get 1
#   So profile is permutation of (2,1,1) for both bL and bR
# If p=1: 2 phases with min>=1, 1 with max<=1
#   min1 phases: bL>=1,bR>=1, sum >= 2+2=4 for bL and bR
#   max1 phase: contributes 0 or 1 to each. With sum=4: need <=2 remaining
#   from min1 phases. So min1 bL in {1,2} and min1 bR in {1,2}
# etc.

print(f"\n{'='*60}")
print("PART 8: ALGEBRAIC CONSTRAINT ANALYSIS")
print("For non-OSB with bL_total=4, bR_total=4 across 3 phases:")

count_by_type = Counter()
for bL, bR in non_osb_partitions:
    n_sweep = sum(1 for k in range(3) if bL[k] >= 1 and bR[k] >= 1)
    n_null = sum(1 for k in range(3) if bL[k] == 0 and bR[k] == 0)
    n_single = 3 - n_sweep - n_null
    count_by_type[(n_sweep, n_single, n_null)] += 1

print(f"  (sweep/both, single, null) distribution:")
for (s, si, nu), cnt in sorted(count_by_type.items()):
    print(f"    sweep={s}, single={si}, null={nu}: {cnt}")

elapsed = time.time() - t0
print(f"\nTotal: {elapsed:.1f}s")
sys.stdout.flush()
