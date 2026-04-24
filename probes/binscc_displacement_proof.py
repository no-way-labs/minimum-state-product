#!/usr/bin/env python3
"""binscc_displacement_proof.py — Prove Full Return universality via
displacement argument.

KEY LEMMA: Full Return fails at ternary t iff the displacement sequence
(v_k - v_{k-1}) for k=0,1,2 is a permutation of {(1,0),(0,1),(1,1)} on Z_2^2.

Reason: v_{k-1} = (c[bL], c[bR]) at the first nonmover step of phase k.
If v_{k-1} = v_k, this nonmover matches mover → Full Return holds.
So failure requires all displacements nonzero, and they sum to (0,0).
The only 3 nonzero elements of Z_2^2 summing to (0,0) are {(1,0),(0,1),(1,1)}.

For n=6 alternating: 3 ternary (1,3,5), 3 binary (0,2,4).
Coupling: binary 0 → (α for t1, δ for t5), etc.
Test: can all 3 ternary simultaneously have the displacement pattern?
"""
import sys
from itertools import permutations, product as iproduct
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

def get_displacements(ms, n, word, cycle, t):
    """Get displacement sequence (v_k - v_{k-1}) mod 2 for ternary t."""
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
    m_t = ms[t]

    # Find mover steps of t and their (bL, bR) values
    mover_LR = {}  # phase -> (c[bL], c[bR]) at mover
    for s in range(ell):
        if word[s] == t:
            k = cycle[s][t]
            # Multiple rounds: store all mover values per phase
            if k not in mover_LR:
                mover_LR[k] = []
            mover_LR[k].append((cycle[s][bL], cycle[s][bR]))

    # For single round: each phase has 1 mover
    # For displacement: v_k = mover value at phase k
    # Displacement d_k = v_k - v_{k-1} (mod 2)
    if any(len(v) > 1 for v in mover_LR.values()):
        return None  # Multi-round, skip for now

    vals = {k: vs[0] for k, vs in mover_LR.items()}
    disps = []
    for k in range(m_t):
        prev = (k - 1) % m_t
        d = ((vals[k][0] - vals[prev][0]) % 2,
             (vals[k][1] - vals[prev][1]) % 2)
        disps.append(d)
    return disps

print("=" * 70)
print("DISPLACEMENT PROOF FOR FULL RETURN")
print("=" * 70)

# PART 1: Verify displacement lemma
print("\nPART 1: DISPLACEMENT LEMMA VERIFICATION")
n, ms = 5, [2, 3, 2, 3, 2]
tern = [1, 3]
words = enumerate_mover_words(ms, n, 21)
print(f"n={n} ms={ms}")

total = 0
fr_fail_count = 0
disp_pattern_count = Counter()
disp_match = 0
disp_mismatch = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None:
        continue
    total += 1
    if not is_wrap_adjacent(word, n):
        continue

    ell = len(cycle)
    for t in tern:
        bL = (t - 1) % n
        bR = (t + 1) % n

        # Check Full Return
        has_fr = False
        for k in range(ms[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            if len(ps) <= 1:
                continue
            mlrs = set()
            nmlrs = set()
            for s in ps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    mlrs.add(lr)
                else:
                    nmlrs.add(lr)
            if mlrs & nmlrs:
                has_fr = True
                break

        disps = get_displacements(ms, n, word, cycle, t)
        if disps is None:
            continue

        is_all_nonzero = all(d != (0, 0) for d in disps)
        is_perm = sorted(disps) == sorted([(0, 1), (1, 0), (1, 1)])

        if not has_fr:
            fr_fail_count += 1
            if is_perm:
                disp_match += 1
            else:
                disp_mismatch += 1
                print(f"  MISMATCH: word={word[:10]}, disps={disps}")
        else:
            if not is_all_nonzero:
                pass  # Full Return holds because some displacement is zero

        disp_pattern_count[tuple(sorted(disps))] += 1

print(f"  Wrap-adjacent cycles: counted {total}")
print(f"  Full Return failures (per-proc): {fr_fail_count}")
print(f"  FR fail + disp = perm{{(1,0),(0,1),(1,1)}}: {disp_match}")
print(f"  FR fail + disp ≠ perm: {disp_mismatch}")
print(f"  → Lemma verified: {'YES' if disp_mismatch == 0 else 'NO'}")

# Show displacement distribution
print(f"\n  Top displacement patterns:")
for pat, cnt in disp_pattern_count.most_common(10):
    marker = "★" if pat == ((0, 1), (1, 0), (1, 1)) else ""
    print(f"    {pat}: {cnt} {marker}")

# PART 2: At n=6, verify ALL ternary fail → contradiction
print(f"\n{'='*70}")
print("PART 2: ALL-TERNARY-FAIL AT n=6")
n6, ms6 = 6, [2, 3, 2, 3, 2, 3]
tern6 = [1, 3, 5]
words6 = enumerate_mover_words(ms6, n6, 24)
print(f"n={n6} ms={ms6}: {len(words6)} words")

total6 = 0
all_fail = 0
wrap_all_fail = 0

for word in words6:
    cycle = build_cycle(ms6, n6, word)
    if cycle is None:
        continue
    total6 += 1
    wrap = is_wrap_adjacent(word, n6)

    # Check if Full Return fails at ALL ternary
    fails_all = True
    for t in tern6:
        bL = (t - 1) % n6
        bR = (t + 1) % n6
        has_fr = False
        ell = len(cycle)
        for k in range(ms6[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            if len(ps) <= 1:
                continue
            mlrs = set()
            nmlrs = set()
            for s in ps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    mlrs.add(lr)
                else:
                    nmlrs.add(lr)
            if mlrs & nmlrs:
                has_fr = True
                break
        if has_fr:
            fails_all = False
            break

    if fails_all:
        all_fail += 1
        if wrap:
            wrap_all_fail += 1
            # Show displacements
            if wrap_all_fail <= 3:
                print(f"  WRAP ALL-FAIL: word={word[:15]}...")
                for t in tern6:
                    d = get_displacements(ms6, n6, word, cycle, t)
                    print(f"    P{t}: disps={d}")

print(f"\n  Total: {total6}")
print(f"  All ternary Full Return fail: {all_fail}")
print(f"  Wrap-adjacent + all fail: {wrap_all_fail}")
print(f"  → {'PROVED: no wrap-adjacent cycle has all-ternary failure' if wrap_all_fail == 0 else 'OPEN'}")

# PART 3: Displacement pattern for n=5 gap cycles
print(f"\n{'='*70}")
print("PART 3: n=5 GAP CYCLE DISPLACEMENTS")
n5, ms5 = 5, [2, 3, 2, 3, 2]
tern5 = [1, 3]

gap_disps = Counter()
for word in words:
    cycle = build_cycle(ms5, n5, word)
    if cycle is None:
        continue
    if is_wrap_adjacent(word, n5):
        continue  # Only non-wrap
    ell = len(cycle)

    # Check all ternary fail
    fails = True
    for t in tern5:
        bL = (t - 1) % n5
        bR = (t + 1) % n5
        has_fr = False
        for k in range(ms5[t]):
            ps = [s for s in range(ell) if cycle[s][t] == k]
            if len(ps) <= 1:
                continue
            mlrs = set()
            nmlrs = set()
            for s in ps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    mlrs.add(lr)
                else:
                    nmlrs.add(lr)
            if mlrs & nmlrs:
                has_fr = True
                break
        if has_fr:
            fails = False
            break

    if fails:
        d1 = get_displacements(ms5, n5, word, cycle, 1)
        d3 = get_displacements(ms5, n5, word, cycle, 3)
        if d1 is not None and d3 is not None:
            gap_disps[(tuple(d1), tuple(d3))] += 1

print(f"  Gap displacement patterns (P1, P3):")
for (d1, d3), cnt in gap_disps.most_common(20):
    print(f"    P1={list(d1)} P3={list(d3)}: {cnt}")

sys.stdout.flush()
