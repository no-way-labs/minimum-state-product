#!/usr/bin/env python3
"""WHY is the minimum cycle length forced above Σm_p?

Key hypothesis: on a ring of n procs, a wrap-adjacent mover word of length ℓ
visiting all procs with fc[p] ≡ 0 mod m_p requires ℓ > Σm_p.

The walk must traverse the ring, and the wrap-adjacency constraint
(first and last movers are ring-adjacent) forces the walk to span the ring.

This script investigates the STRUCTURAL reason for length forcing.
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

# PART 1: Analyze the WALK STRUCTURE of the shortest cycles
print("=" * 70)
print("LENGTH FORCING ANALYSIS")
print("=" * 70)

# n=5 alternating: min cycle length = 14
n, ms = 5, [2, 3, 2, 3, 2]
words = enumerate_mover_words(ms, n, 14)
print(f"\nn=5 alt: shortest cycles (len 14)")
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    fc = Counter(word)
    # Analyze walk structure
    print(f"  word={list(word)}")
    print(f"  fc={[fc.get(p,0) for p in range(n)]}")
    # Show which binary fires extra
    for b in [0, 2, 4]:
        if fc[b] > 2:
            print(f"  Binary P{b} fires {fc[b]} times (extra {fc[b]-2})")
    break  # just show one

# PART 2: Why can't n=5 have length 12?
# ℓ=12, fc=[2,3,2,3,2]. Walk of length 12 on ring of 5, visiting all procs.
# The walk is a sequence of adjacent procs. Minimum traversal of ring = 5 steps.
# With wrap-adjacency: word[0] and word[11] must be adjacent.
# The walk must visit procs 0,1,2,3,4 at least ms[p] times each.
# Total visits = 12. The walk must cover the ring.

# Key insight: on a ring graph, a walk of length ℓ starting at proc p
# can reach at most ⌊ℓ/2⌋ positions away (since it must alternate neighbors).
# Wait, that's for a path graph. On a ring, the walk can go either direction.

# The WALK on the ring can be thought of as a walk on Z_n where each step
# moves ±1. The wrap-adjacent constraint means the walk starts and ends
# at adjacent positions.

# For the walk to visit all n procs: the walk must span the ring.
# This requires the walk to traverse at least n-1 positions in one direction
# or combine both directions.

print(f"\n{'='*60}")
print("WALK SPAN ANALYSIS")
print()

# For n=5, every walk that visits all 5 procs needs to span the ring.
# The walk moves ±1 on Z_5 at each step.
# Net displacement after ℓ steps: must be ±1 (wrap-adjacent).
# The walk visits procs 0,1,2,3,4 at least ms[p] times.

# Key constraint: BINARY PROCS CAN ONLY BE VISITED FROM TERNARY NEIGHBORS.
# On the alternating ring: B-T-B-T-B.
# B0's neighbors: T4 and T1 (on ring P0 is between P4 and P1).
# So B0 fires only when walk comes from T4 or T1.
# Between two B0 firings, the walk must return to B0 via T4 or T1.

# For fc[B0]=2: walk visits B0 twice. Between visits, walk goes to
# some neighbor, traverses some path, returns to B0.

# CRITICAL: between two B0 firings, the walk must RETURN to B0.
# Since B0 is at position 0, the walk goes to position 1 (or 4),
# then must come back to 0. This round trip costs at least 2 steps
# (go to 1, come back to 0) but the walk might go further.

# For the walk to also visit B2 and B4:
# Starting at some proc, the walk must reach positions 0, 2, 4
# (all binary) and 1, 3 (all ternary).

# The walk traverses the ring, and each traversal of an edge (p, p+1)
# requires visiting both p and p+1. The binary procs are even-positioned.

# Let me compute the minimum walk length to visit all procs
# with fc constraints, using BFS.

print("Testing minimum walk lengths WITH config distinctness:")

for test_n, test_ms, label in [
    (5, [2,3,2,3,2], "n=5 alt"),
    (6, [2,3,2,3,2,3], "n=6 alt"),
    (7, [2,3,2,3,2,3,3], "n=7 (3bin)"),
]:
    # Check: minimum ℓ such that wrap-adj cycle exists
    for ml in range(sum(test_ms), sum(test_ms) + 20):
        words_ml = enumerate_mover_words(test_ms, test_n, ml)
        count = sum(1 for w in words_ml
                    if build_cycle(test_ms, test_n, w) is not None
                    and is_wrap_adjacent(w, test_n))
        if count > 0:
            print(f"  {label}: min wrap-adj cycle length = {ml} "
                  f"(fc_min={sum(test_ms)}, gap={ml-sum(test_ms)}) "
                  f"({count} cycles)")
            # Show fc of shortest cycles
            for w in words_ml:
                c = build_cycle(test_ms, test_n, w)
                if c and is_wrap_adjacent(w, test_n):
                    fc = Counter(w)
                    fc_list = [fc.get(p,0) for p in range(test_n)]
                    print(f"    fc={fc_list}")
                    break
            break
    else:
        print(f"  {label}: no cycles found up to {sum(test_ms)+19}")

# PART 3: The KEY analytical question
# For n=5: min ℓ = 14, fc = [2,3,4,3,2]. Binary P2 fires 4 times.
# This forces P2 to toggle 4 times, creating Toggle-FR at P1 or P3.
# Specifically: P2 fires 4 times in the cycle. P1 sees fc[P2]=4 as its K.
# P1 has 3 phases with K_A + K_B + K_C = 4.
# If all anti-diagonal: parities (0,1,1). Minimum K = (0,1,1) sum = 2.
# But K total = 4, so extra 2 must be added: (0,1,3) or (2,1,1) or (0,3,1).
# (0,3,1) has K_C=3 in type C... but (3,0) is what triggers Toggle-FR.
# Wait: the K values are P2 firings, not P0 firings. For Toggle-FR at P1,
# we need (J_k, K_k) = (3,0) or (0,3) at some phase.
# J is P0 firings. K is P2 firings.
# With fc[P0]=2: J parities (1,0,1), J = (1,0,1), total 2 (minimum).
# With fc[P2]=4: K parities (0,1,1), K total = 4.
# K must be (0,1,3) or (2,1,1) or (0,3,1) or (2,3,-1)=impossible.
# K values: K_A even≥0, K_B odd≥1, K_C odd≥1, sum=4.
# Options: (0,1,3), (0,3,1), (2,1,1).
# With K_B=3: phase B has (J_B,K_B) = (0,3). Toggle-FR! ∎
# With K_C=3: phase C has (J_C,K_C) = (1,3). Not (0,3), but J+K=4.
# With K=(2,1,1): all ≤2. Phase A: (1,2)→Both-Even? J=1 odd, K=2 even → NOT Both-Even. Phase B: (0,1)→anti-diag. Phase C: (1,1)→anti-diag.

print(f"\n{'='*60}")
print("ANALYTICAL PROOF ATTEMPT FOR n=5")
print()
print("At n=5 alt, min cycle ℓ=14, fc=[2,3,4,3,2]. fc[P2]=4.")
print("P1 phases: J=fc[P0]=2, K=fc[P2]=4.")
print("If P1 all-anti-diagonal: ABC → J parities (1,0,1), K parities (0,1,1)")
print("  J=(1,0,1) sum=2 ✓, K=(K_A,K_B,K_C) parities (0,1,1) sum=4")
print("  K options: (0,1,3), (0,3,1), (2,1,1)")
print()
print("  (0,1,3): Phase A=(1,0), B=(0,1), C=(1,3). No (3,0) or (0,3).")
print("    But Phase C has K_C=3, J_C=1. J+K=4. Toggle-FR possible?")
print("  (0,3,1): Phase A=(1,0), B=(0,3) ← Toggle-FR! K_B=3, J_B=0.")
print("    (0,3) ALWAYS has FR (proved). P1 has FR at phase B. ✓")
print("  (2,1,1): Phase A=(1,2), B=(0,1), C=(1,1).")
print("    No (3,0) or (0,3). No Both-Even. Minimum anti-diagonal.")
print("    But wait: K_A=2 even AND J_A=1 odd → not Both-Even.")
print()
print("So only K=(2,1,1) avoids Toggle-FR at P1. Check P3:")
print("P3 phases: J=fc[P2]=4, K=fc[P4]=2.")
print("If P3 all-anti-diagonal: J parities (1,0,1) sum=4, K parities (0,1,1) sum=2")
print("  J options: (1,0,3), (1,2,1), (3,0,1), (3,2,-1)=impossible")
print("  (3,0,1): Phase A has J_A=3, K_A=0 → (3,0) → Toggle-FR! ✓")
print("  (1,0,3): Phase C has J_C=3, K_C=1 → (3,1). Not (3,0).")
print("  (1,2,1): No phase has J≥3 or K≥3.")
print()
print("KEY: P1 escapes Toggle-FR with K=(2,1,1), P3 escapes with J=(1,2,1).")
print("But K at P1 = fc[P2] split by P1's phases")
print("And J at P3 = fc[P2] split by P3's phases")
print("These are the SAME fc[P2]=4 firings, partitioned differently!")
print()
print("Can P1's K=(2,1,1) and P3's J=(1,2,1) coexist?")
print("Each P2 firing contributes to one P1-phase K and one P3-phase J.")
print("4 P2 firings with landing patterns...")

# Verify: enumerate P2 firing distributions when P1 AND P3 both avoid Toggle-FR
n5, ms5 = 5, [2,3,2,3,2]
words5 = enumerate_mover_words(ms5, n5, 14)
p1_escapes = 0
p3_escapes = 0
both_escape = 0
both_escape_details = []

for word in words5:
    cycle = build_cycle(ms5, n5, word)
    if cycle is None or not is_wrap_adjacent(word, n5):
        continue
    ell = len(word)

    # P1 phase (J,K)
    p1_jk = []
    for k in range(3):
        steps = [s for s in range(ell) if cycle[s][1] == k]
        J = sum(1 for s in steps if word[s] == 0)
        K = sum(1 for s in steps if word[s] == 2)
        p1_jk.append((J, K))

    # P3 phase (J,K)
    p3_jk = []
    for k in range(3):
        steps = [s for s in range(ell) if cycle[s][3] == k]
        J = sum(1 for s in steps if word[s] == 2)
        K = sum(1 for s in steps if word[s] == 4)
        p3_jk.append((J, K))

    # Check if P1 avoids Toggle-FR: no phase with (3,0) or (0,3)
    p1_no_toggle = not any((j >= 3 and k == 0) or (j == 0 and k >= 3) for j,k in p1_jk)
    p3_no_toggle = not any((j >= 3 and k == 0) or (j == 0 and k >= 3) for j,k in p3_jk)

    if p1_no_toggle:
        p1_escapes += 1
    if p3_no_toggle:
        p3_escapes += 1
    if p1_no_toggle and p3_no_toggle:
        both_escape += 1
        both_escape_details.append((word, p1_jk, p3_jk))

total5 = sum(1 for w in words5 if build_cycle(ms5,n5,w) and is_wrap_adjacent(w,n5))
print(f"\n  n=5 verification ({total5} cycles):")
print(f"    P1 escapes Toggle-FR: {p1_escapes}")
print(f"    P3 escapes Toggle-FR: {p3_escapes}")
print(f"    BOTH escape Toggle-FR: {both_escape}")

if both_escape > 0:
    print(f"\n  Cycles where BOTH escape Toggle-FR:")
    for word, jk1, jk3 in both_escape_details[:5]:
        print(f"    P1 phases: {jk1}")
        print(f"    P3 phases: {jk3}")
        # Check entry conflict
        from collections import Counter as C2
        for t in [1,3]:
            bL, bR = (t-1)%n5, (t+1)%n5
            mover_lsr, nonmover_lsr = set(), set()
            for s in range(len(word)):
                lsr = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                if word[s] == t: mover_lsr.add(lsr)
                else: nonmover_lsr.add(lsr)
            has_ec = bool(mover_lsr & nonmover_lsr)
            print(f"    P{t} entry conflict: {has_ec}")
else:
    print(f"\n  *** BOTH ALWAYS have Toggle-FR! At least one has (0,3) or (3,0). ***")
    print(f"  This means Toggle-FR alone suffices for n=5!")
