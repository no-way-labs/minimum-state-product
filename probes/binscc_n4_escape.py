#!/usr/bin/env python3
"""n=4: 24 cycles escape EC at all ternary. WHY?
n=5: 0 escapes. What changed?

Analyze the 24 n=4 escapes and understand why n=5 can't have them.
"""
import time
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

def has_entry_conflict_at(ms, n, word, cycle, p):
    ell = len(word)
    bL, bR = (p-1)%n, (p+1)%n
    mover, nonmover = set(), set()
    for s in range(ell):
        lsr = (cycle[s][bL], cycle[s][p], cycle[s][bR])
        if word[s] == p: mover.add(lsr)
        else: nonmover.add(lsr)
    return bool(mover & nonmover)

# n=4: find the 24 EC-free cycles
print("=" * 70)
print("n=4: EC-FREE CYCLE ANALYSIS")
print("=" * 70)

n, ms = 4, [2,3,2,3]
words = enumerate_mover_words(ms, n, 14)
sandwiched = [1, 3]

ec_free = []
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    all_ec = all(has_entry_conflict_at(ms, n, word, cycle, t) for t in sandwiched)
    if not all_ec:
        any_ec = any(has_entry_conflict_at(ms, n, word, cycle, t) for t in sandwiched)
        if not any_ec:
            ec_free.append((word, cycle))

print(f"EC-free cycles: {len(ec_free)}")

for i, (word, cycle) in enumerate(ec_free[:6]):
    ell = len(word)
    fc = Counter(word)
    fc_list = [fc.get(p,0) for p in range(n)]
    print(f"\n  Cycle {i}: word={list(word)}, fc={fc_list}, len={ell}")
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        print(f"    P{t}:")
        mover_set = set()
        nonmover_set = set()
        for s in range(ell):
            lsr = (cycle[s][bL], cycle[s][t], cycle[s][bR])
            if word[s] == t:
                mover_set.add(lsr)
            else:
                nonmover_set.add(lsr)
        print(f"      mover (L,S,R):    {sorted(mover_set)}")
        print(f"      nonmover (L,S,R): {sorted(nonmover_set)}")
        print(f"      |mover|={len(mover_set)} |nonmover|={len(nonmover_set)} "
              f"|union|={len(mover_set|nonmover_set)} overlap={mover_set&nonmover_set}")

        # Phase analysis
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            M = sum(1 for s in steps if word[s] == t)
            m_lr = set()
            nm_lr = set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t: m_lr.add(lr)
                else: nm_lr.add(lr)
            print(f"      Phase {k}: (J,K,M)=({J},{K},{M}) d={len(steps)} "
                  f"m_lr={m_lr} nm_lr={nm_lr}")

# KEY: What's special about these 24 cycles?
print(f"\n{'='*70}")
print("EC-FREE CYCLE STRUCTURE")
print("=" * 70)

fc_patterns = Counter()
jk_patterns = Counter()
for word, cycle in ec_free:
    fc = Counter(word)
    fc_list = tuple(fc.get(p,0) for p in range(n))
    fc_patterns[fc_list] += 1
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        jks = []
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            jks.append((J, K))
        jk_patterns[(t, tuple(jks))] += 1

print(f"Fire count patterns: {dict(fc_patterns)}")
print(f"Phase (J,K) patterns:")
for (t, jk), cnt in sorted(jk_patterns.items(), key=lambda x: -x[1]):
    print(f"  P{t}: {jk}: {cnt}")

# n=5: verify 0 escapes and show WHY the n=4 escape pattern fails
print(f"\n{'='*70}")
print("n=5: WHY n=4 ESCAPE PATTERN FAILS")
print("=" * 70)

n5, ms5 = 5, [2,3,2,3,2]
words5 = enumerate_mover_words(ms5, n5, 16)
sandwiched5 = [1, 3]

# At n=5, fc = [2,3,4,3,2] or [4,3,2,3,4]
# For P1: J=fc[0], K=fc[2]. At n=4, the escape had J=K=2 (fc=[2,3,2,3]).
# At n=5, J+K ≥ 6. Can P1 still escape?

total5 = 0
p1_escapes5 = 0
p3_escapes5 = 0
both_escape5 = 0
escape_jk5 = Counter()

for word in words5:
    cycle = build_cycle(ms5, n5, word)
    if cycle is None or not is_wrap_adjacent(word, n5):
        continue
    total5 += 1
    ell = len(word)

    p1_ec = has_entry_conflict_at(ms5, n5, word, cycle, 1)
    p3_ec = has_entry_conflict_at(ms5, n5, word, cycle, 3)

    if not p1_ec:
        p1_escapes5 += 1
        bL, bR = 0, 2
        jks = []
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][1] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            jks.append((J, K))
        escape_jk5[('P1', tuple(jks))] += 1

    if not p3_ec:
        p3_escapes5 += 1
        bL, bR = 2, 4
        jks = []
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][3] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            jks.append((J, K))
        escape_jk5[('P3', tuple(jks))] += 1

    if not p1_ec and not p3_ec:
        both_escape5 += 1

print(f"Total: {total5}")
print(f"P1 escapes: {p1_escapes5}")
print(f"P3 escapes: {p3_escapes5}")
print(f"BOTH escape: {both_escape5}")
print(f"\nEscape (J,K) patterns at n=5:")
for (t, jk), cnt in sorted(escape_jk5.items(), key=lambda x: -x[1])[:10]:
    J_total = sum(j for j,k in jk)
    K_total = sum(k for j,k in jk)
    print(f"  {t}: {jk} (J={J_total},K={K_total}): {cnt}")

# n=4 vs n=5: the minimum J+K
print(f"\n{'='*70}")
print("n=4 vs n=5: MINIMUM J+K AT TERNARY")
print("=" * 70)

# n=4
n4_jk_total = Counter()
for word, cycle in ec_free:
    ell = len(word)
    for t in [1, 3]:
        bL, bR = (t-1)%4, (t+1)%4
        J = sum(1 for s in range(ell) if word[s] == bL)
        K = sum(1 for s in range(ell) if word[s] == bR)
        n4_jk_total[(t, J, K)] += 1
print(f"n=4 EC-free: total (J,K) per ternary: {dict(n4_jk_total)}")

# n=5: total J+K for escaping ternary
print(f"n=5: total (J,K) for escaping ternary already shown above")

# KEY QUESTION: At n=4, J=K=2 allows escape.
# At n=5, the MINIMUM J+K per ternary is higher.
# Does J+K ≥ 6 prevent escape for ALL orderings?
print(f"\n{'='*70}")
print("CRITICAL: J+K THRESHOLD FOR WALK-LEVEL EC")
print("=" * 70)

# For a ternary with J=2,K=2 (n=4 escape case):
# 3 phases, parities (1,0),(0,1),(1,1). With J=K=2:
# Only option: (1,0),(0,1),(1,1) → (J,K) = (1,0),(0,1),(1,1).
# Phase 0: 1 bL firing, 0 bR → d=2, mover sees 1 (L,R)
# Phase 1: 0 bL, 1 bR → d=2, mover sees 1 (L,R)
# Phase 2: 1 bL, 1 bR → d=3, mover sees 1 (L,R), nonmover sees 2 (L,R)
# With {0,1}²=4 values, mover can avoid nonmover set of 2.

# For J=4, K=2 (n=5 case):
# Options: (1,0),(0,1),(3,1) or (1,0),(2,1),(1,1) or (1,2),(0,1),(3,1)...
# Phase with J=3,K=1: d=5, nonmover has more (L,R) values
# Can mover still escape? Check walk constraints.

print("Phase durations and nonmover (L,R) counts:")
print("  (J,K)=(1,0): d=2, nm can see 1 (L,R) value")
print("  (J,K)=(0,1): d=2, nm can see 1 (L,R) value")
print("  (J,K)=(1,1): d=3, nm can see 2 (L,R) values")
print("  (J,K)=(1,2): d=4, nm can see 2-3 (L,R) values")
print("  (J,K)=(2,1): d=4, nm can see 2-3 (L,R) values")
print("  (J,K)=(1,3): d=5, nm can see 2-3 (L,R) values")
print("  (J,K)=(3,1): d=5, nm can see 2-3 (L,R) values")
print()
print("At n=4 with J=K=2: total phase durations = 2+2+3 = 7 → cycle length = 12 - 3(ternary fc) + ... ")
print("  3 phases with 2,2,3 steps = 7 nonmover + 3 mover = 10. ℓ=12 with 2 other procs.")
print()
print("At n=5 with J=4,K=2: phases could be (1,0),(0,1),(3,1).")
print("  Phase C: d=5, nm sees ≥2 (L,R). With J=3,K=1:")
print("  L toggles 3×, R toggles 1×. Path: L₀R₀→¹L₀R₀→L̄₀R₀→L₀R₀→L̄₀R̄₀→mover(L₀,R̄₀)")
print("  nonmover (L,R): {(L₀,R₀), (L̄₀,R₀), (L₀,R₀), (L̄₀,R̄₀)} = {(L₀,R₀),(L̄₀,R₀),(L̄₀,R̄₀)}")
print("  mover: (L₀,R̄₀). If L₀=0,R₀=0: nm={(0,0),(1,0),(1,1)}, m={(0,1)}. NO overlap!")
print("  So J=3,K=1 does NOT guarantee phase EC!")
