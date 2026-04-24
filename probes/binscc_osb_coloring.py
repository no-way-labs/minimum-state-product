#!/usr/bin/env python3
"""Triangle 2-coloring impossibility for SR-OSB universality.

KEY INSIGHT from universality analysis:
  Non-OSB ternary always has ASYMMETRIC binary neighbor firings:
  one binary fires >=4 ("heavy"), other fires 2 ("light").

This creates a 2-coloring problem on the binary triangle:
  - Each edge (ternary) requires one heavy + one light endpoint
  - Triangle has no proper 2-coloring (odd cycle!)
  - Therefore: not all ternary can be non-OSB
  - Therefore: at least one single-round ternary has OSB
  - Combined with SR-OSB FR theorem -> entry conflict universal

This script:
  1. Verifies the heavy/light asymmetry for non-OSB ternary
  2. Tests the 2-coloring impossibility argument
  3. Investigates WHY non-OSB requires asymmetry (walk constraint)
  4. Extends to general n
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
print("TRIANGLE 2-COLORING IMPOSSIBILITY FOR SR-OSB UNIVERSALITY")
print("=" * 70)

# PART 1: Verify heavy/light asymmetry at n=6
print("\nPART 1: HEAVY/LIGHT ASYMMETRY VERIFICATION (n=6)")

n, ms = 6, [2, 3, 2, 3, 2, 3]
tern = [1, 3, 5]
binn = [0, 2, 4]

t0 = time.time()
words = enumerate_mover_words(ms, n, 24)
print(f"  Words: {len(words)} ({time.time()-t0:.1f}s)")

# For each cycle, classify each ternary as OSB or non-OSB,
# and track the binary firing counts
non_osb_asymmetry = Counter()  # (bL_total, bR_total) for non-OSB ternary
osb_asymmetry = Counter()      # same for OSB ternary
fc_distribution = Counter()    # fire count vectors

total_cycles = 0
both_nonOSB = 0  # cycles where both single-round ternary are non-OSB
both_nonOSB_examples = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    total_cycles += 1
    ell = len(word)
    fc = Counter(word)
    fc_distribution[tuple(fc[p] for p in range(n))] += 1

    non_osb_ternary = []
    osb_ternary = []

    for t in tern:
        is_sr = (fc[t] == ms[t])
        if not is_sr:
            continue  # skip multi-round

        bL = (t - 1) % n
        bR = (t + 1) % n

        has_osb = False
        for k in range(ms[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            bLf = sum(1 for s in ps if word[s] == bL)
            bRf = sum(1 for s in ps if word[s] == bR)
            if min(bLf, bRf) == 0 and max(bLf, bRf) >= 2:
                has_osb = True
                break

        if has_osb:
            osb_ternary.append(t)
            osb_asymmetry[(fc[bL], fc[bR])] += 1
        else:
            non_osb_ternary.append(t)
            non_osb_asymmetry[(fc[bL], fc[bR])] += 1

    if len(non_osb_ternary) >= 2:
        both_nonOSB += 1
        if len(both_nonOSB_examples) < 3:
            both_nonOSB_examples.append({
                'word': word[:20],
                'fc': dict(fc),
                'non_osb': non_osb_ternary,
                'osb': osb_ternary,
            })

print(f"  Total wrap-adj cycles: {total_cycles}")
print(f"\n  Non-OSB ternary (bL_total, bR_total):")
for (bL, bR), cnt in sorted(non_osb_asymmetry.items(), key=lambda x: -x[1]):
    print(f"    fc[bL]={bL}, fc[bR]={bR}: {cnt}  {'ASYMMETRIC' if bL != bR else 'SYMMETRIC'}")

print(f"\n  OSB ternary (bL_total, bR_total):")
for (bL, bR), cnt in sorted(osb_asymmetry.items(), key=lambda x: -x[1])[:10]:
    print(f"    fc[bL]={bL}, fc[bR]={bR}: {cnt}")

print(f"\n  Cycles with ≥2 single-round non-OSB ternary: {both_nonOSB}")
if both_nonOSB_examples:
    for ex in both_nonOSB_examples:
        print(f"    non-OSB={ex['non_osb']}, OSB={ex['osb']}, fc={ex['fc']}")

# PART 2: Parity constraint
print(f"\n{'='*60}")
print("PART 2: PARITY CONSTRAINT")
print("On bipartite ring (even n), walk length ℓ is even.")
print("Ternary fc sum must be divisible by 6 (each fc[t] mult of 3, sum even).")
print("Minimum ternary sum = 12 = 3+3+6. So at least ONE ternary is multi-round.")

print(f"\n  Fire count distributions:")
for fc_vec, cnt in sorted(fc_distribution.items(), key=lambda x: -x[1])[:15]:
    tern_fcs = [fc_vec[t] for t in tern]
    bin_fcs = [fc_vec[b] for b in binn]
    n_sr_tern = sum(1 for f in tern_fcs if f == 3)
    print(f"    fc={list(fc_vec)}, ternary={tern_fcs}, binary={bin_fcs}, "
          f"SR_tern={n_sr_tern}: {cnt}")

# PART 3: Triangle 2-coloring argument
print(f"\n{'='*60}")
print("PART 3: TRIANGLE 2-COLORING ARGUMENT")
print("")
print("Binary processors form a triangle: P0-P2-P4")
print("Each ternary P_t connects two binary neighbors.")
print("Non-OSB at P_t requires one binary heavy (fc>=4), one light (fc=2).")
print("This is a 2-coloring constraint on the triangle.")
print("")
print("Triangle (odd cycle) has NO proper 2-coloring!")
print("Therefore: not all 3 ternary can be non-OSB.")
print("Combined with parity (at most 2 ternary are single-round):")
print("At least 1 of the 2 single-round ternary must have OSB.")

# Verify: for cycles with 2 non-OSB ternary, what's the coloring?
print(f"\n  Cycles with 2 non-OSB single-round ternary: {both_nonOSB}")
if both_nonOSB > 0:
    coloring_types = Counter()
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        non_osb_set = set()
        for t in tern:
            if fc[t] != ms[t]:
                continue
            bL = (t - 1) % n
            bR = (t + 1) % n
            has_osb = False
            for k in range(ms[t]):
                ps = [s for s in range(ell) if cycle[s][t] == k]
                bLf = sum(1 for s in ps if word[s] == bL)
                bRf = sum(1 for s in ps if word[s] == bR)
                if min(bLf, bRf) == 0 and max(bLf, bRf) >= 2:
                    has_osb = True
                    break
            if not has_osb:
                non_osb_set.add(t)

        if len(non_osb_set) < 2:
            continue

        # Check heavy/light assignment at each non-OSB ternary
        assignment = {}
        for t in non_osb_set:
            bL = (t - 1) % n
            bR = (t + 1) % n
            if fc[bL] > fc[bR]:
                assignment[t] = (bL, 'heavy', bR, 'light')
            elif fc[bR] > fc[bL]:
                assignment[t] = (bL, 'light', bR, 'heavy')
            else:
                assignment[t] = (bL, 'equal', bR, 'equal')
        coloring_types[tuple(sorted(assignment.items()))] += 1

    # Summarize coloring patterns
    print(f"\n  Coloring patterns for 2-nonOSB cycles:")
    heavy_set = Counter()
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        non_osb_set = set()
        for t in tern:
            if fc[t] != ms[t]:
                continue
            bL = (t - 1) % n
            bR = (t + 1) % n
            has_osb = False
            for k in range(ms[t]):
                ps = [s for s in range(ell) if cycle[s][t] == k]
                bLf = sum(1 for s in ps if word[s] == bL)
                bRf = sum(1 for s in ps if word[s] == bR)
                if min(bLf, bRf) == 0 and max(bLf, bRf) >= 2:
                    has_osb = True
                    break
            if not has_osb:
                non_osb_set.add(t)

        if len(non_osb_set) < 2:
            continue

        heavies = set()
        for t in non_osb_set:
            bL = (t - 1) % n
            bR = (t + 1) % n
            if fc[bL] > fc[bR]:
                heavies.add(bL)
            elif fc[bR] > fc[bL]:
                heavies.add(bR)
        heavy_set[frozenset(heavies)] += 1

    for hs, cnt in heavy_set.most_common(10):
        print(f"    Heavy binaries: {set(hs)}: {cnt}")

# PART 4: WHY does non-OSB require asymmetry?
# Hypothesis: with bL_total = bR_total = 2 across 3 phases,
# can't avoid having a phase with one=2, other=0 (OSB).
# Test: purely algebraic, is (2,2) non-OSB possible?
print(f"\n{'='*60}")
print("PART 4: ALGEBRAIC CHECK - CAN (2,2) BE NON-OSB?")

# Enumerate all pairs of partitions of 2 into 3 non-negative parts
from itertools import permutations
parts_of_2 = set()
for a in range(3):
    for b in range(3-a):
        c = 2 - a - b
        if c >= 0:
            parts_of_2.add((a, b, c))
# Include all permutations
all_parts = set()
for p in parts_of_2:
    for perm in permutations(p):
        all_parts.add(perm)

n_non_osb_22 = 0
n_osb_22 = 0
for bL in all_parts:
    for bR in all_parts:
        is_osb = False
        for k in range(3):
            if min(bL[k], bR[k]) == 0 and max(bL[k], bR[k]) >= 2:
                is_osb = True
                break
        if is_osb:
            n_osb_22 += 1
        else:
            n_non_osb_22 += 1

print(f"  Partitions of 2 into 3 parts: {len(all_parts)}")
print(f"  Partition pairs that are OSB: {n_osb_22}")
print(f"  Partition pairs that are non-OSB: {n_non_osb_22}")

# Show non-OSB (2,2) pairs
print(f"\n  Non-OSB (2,2) partition pairs:")
for bL in sorted(all_parts):
    for bR in sorted(all_parts):
        is_osb = False
        for k in range(3):
            if min(bL[k], bR[k]) == 0 and max(bL[k], bR[k]) >= 2:
                is_osb = True
                break
        if not is_osb:
            # Check: does it have bL=2 or bR=2 at any phase with other=0?
            print(f"    bL={bL}, bR={bR}")

# PART 5: KEY - is (2,2) non-OSB REALIZABLE on the walk?
# Check if any cycle has a single-round ternary with fc[bL]=fc[bR]=2
# that is non-OSB
print(f"\n{'='*60}")
print("PART 5: REALIZABILITY CHECK - NON-OSB WITH fc[bL]=fc[bR]")

realized_sym = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    for t in tern:
        if fc[t] != ms[t]:
            continue
        bL = (t - 1) % n
        bR = (t + 1) % n
        if fc[bL] != fc[bR]:
            continue  # skip asymmetric

        has_osb = False
        for k in range(ms[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            bLf = sum(1 for s in ps if word[s] == bL)
            bRf = sum(1 for s in ps if word[s] == bR)
            if min(bLf, bRf) == 0 and max(bLf, bRf) >= 2:
                has_osb = True
                break
        if not has_osb:
            realized_sym += 1

print(f"  Single-round ternary with fc[bL]=fc[bR] that is non-OSB: {realized_sym}")
if realized_sym == 0:
    print("  --> CONFIRMED: symmetric binary neighbors always produce OSB")
    print("  --> Non-OSB REQUIRES asymmetry (proved by exhaustion at n=6)")

# PART 6: Check at n=5
print(f"\n{'='*60}")
print("PART 6: ASYMMETRY CHECK AT n=5")

n5 = 5
ms5 = [2, 2, 2, 3, 3]
t1 = time.time()
words5 = enumerate_mover_words(ms5, n5, 20)
print(f"  n=5 words: {len(words5)} ({time.time()-t1:.1f}s)")

non_osb5 = Counter()
osb5 = Counter()
total5 = 0

for word in words5:
    cycle = build_cycle(ms5, n5, word)
    if cycle is None or not is_wrap_adjacent(word, n5):
        continue
    total5 += 1
    ell = len(word)
    fc = Counter(word)

    for t in range(n5):
        if ms5[t] < 3:
            continue  # skip binary
        if fc[t] != ms5[t]:
            continue  # skip multi-round
        bL = (t - 1) % n5
        bR = (t + 1) % n5
        if ms5[bL] != 2 or ms5[bR] != 2:
            continue  # need binary neighbors

        has_osb = False
        for k in range(ms5[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            bLf = sum(1 for s in ps if word[s] == bL)
            bRf = sum(1 for s in ps if word[s] == bR)
            if min(bLf, bRf) == 0 and max(bLf, bRf) >= 2:
                has_osb = True
                break

        if has_osb:
            osb5[(fc[bL], fc[bR])] += 1
        else:
            non_osb5[(fc[bL], fc[bR])] += 1

print(f"  Wrap-adj cycles: {total5}")
print(f"  Non-OSB ternary (bL_total, bR_total):")
for (bL, bR), cnt in sorted(non_osb5.items(), key=lambda x: -x[1]):
    print(f"    fc[bL]={bL}, fc[bR]={bR}: {cnt}  {'ASYM' if bL != bR else 'SYM'}")

# PART 7: Summary
print(f"\n{'='*60}")
print("SUMMARY: SR-OSB UNIVERSALITY PROOF STRUCTURE")
print("")
print("1. PARITY: On bipartite ring (even n), ternary fc sum must be")
print("   divisible by 6. So at most 2 of 3 ternary are single-round.")
print("")
print("2. ASYMMETRY: Non-OSB single-round ternary requires")
print("   fc[bL] ≠ fc[bR] (one heavy, one light). Symmetric always has OSB.")
print("")
print("3. TRIANGLE COLORING: 3 ternary create a triangle on 3 binaries.")
print("   Non-OSB at all 3 requires 2-coloring of triangle (impossible).")
print("   With parity (at most 2 single-round): need 2-coloring of 2 edges")
print("   (path, not triangle). This IS possible! But the third ternary")
print("   being multi-round means it has OSB directly?")
print("")
print("4. KEY QUESTION: Does multi-round ternary always have OSB-type FR?")

elapsed = time.time() - t0
print(f"\nTotal: {elapsed:.1f}s")
sys.stdout.flush()
