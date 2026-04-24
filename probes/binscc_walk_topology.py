#!/usr/bin/env python3
"""Walk topology analysis on the ternary transition graph.

On n=6 alternating, the walk alternates B-T. The ternary transitions form
a walk on the triangle {P1, P3, P5} with edges labeled {P0, P2, P4}.

Each ternary-to-ternary transition fires exactly one binary.
The topology of this walk constrains the displacement patterns.

KEY QUESTION: Is there a simple combinatorial constraint that prevents
simultaneous Full Return failure at two ternary procs?
"""
import sys
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

def has_full_return_at(ms, n, word, cycle, t):
    ell = len(cycle)
    bL = (t - 1) % n
    bR = (t + 1) % n
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
            return True
    return False

print("=" * 70)
print("WALK TOPOLOGY ON TERNARY TRIANGLE")
print("=" * 70)

n, ms = 6, [2, 3, 2, 3, 2, 3]
tern = [1, 3, 5]
binn = [0, 2, 4]

words = enumerate_mover_words(ms, n, 24)

# Extract ternary transition sequences
print("\nPART 1: TERNARY TRANSITION TYPES")

trans_types = Counter()  # (from, to) transitions on triangle
p3_dist = Counter()  # distribution of P3 firings across P1 phases

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    # Extract ternary subsequence
    tern_seq = [word[i] for i in range(ell) if word[i] in set(tern)]
    for i in range(len(tern_seq)):
        t1, t2 = tern_seq[i], tern_seq[(i+1) % len(tern_seq)]
        trans_types[(t1, t2)] += 1

    # Distribution of P3 firings across P1 phases
    p1_pos = [i for i in range(ell) if word[i] == 1]
    p3_pos = [i for i in range(ell) if word[i] == 3]

    if len(p1_pos) == 3 and len(p3_pos) == 3:
        # Count P3 firings in each P1-phase
        counts = [0, 0, 0]
        for j in range(3):
            start = p1_pos[j]
            end = p1_pos[(j+1) % 3]
            for p3p in p3_pos:
                if start < end:
                    if start < p3p < end:
                        counts[j] += 1
                else:  # wraps around
                    if p3p > start or p3p < end:
                        counts[j] += 1
        p3_dist[tuple(sorted(counts))] += 1

print(f"  Ternary-to-ternary transitions:")
for (t1, t2), cnt in sorted(trans_types.items()):
    label = "bounce" if t1 == t2 else "cross"
    print(f"    P{t1}→P{t2} ({label}): {cnt}")

print(f"\n  P3 distribution across P1 phases (when both fire 3x):")
for dist, cnt in sorted(p3_dist.items(), key=lambda x: -x[1]):
    print(f"    {dist}: {cnt}")

# PART 2: Direct parity constraint analysis
print(f"\n{'='*60}")
print("PART 2: PARITY CONSTRAINT ON SHARED BINARY")
print("For P2 shared between P1 and P3:")
print("  P2's firings see joint (P1-phase, P3-phase).")
print("  Test: is there a parity pattern that forces FR at one?")

# For each P3-interleaving type, check if pair-failure is algebraically possible
print("\n  Testing all interleavings abstractly:")

# For P1 to fail FR: need pR(P1) [from P2] and pL(P1) [from P0] with specific parities
# pR(P1)_k = parity of P2 firings during P1-phase k
# For P3 to fail: need pL(P3) [from P2] and pR(P3) [from P4]
# pL(P3)_j = parity of P2 firings during P3-phase j

# The P2 firings have joint (P1-phase, P3-phase) distribution.
# Marginal at P1: pR(P1), Marginal at P3: pL(P3)
# Both must be nonzero (exactly 2 ones).

# Check if there exists a {0,1} matrix M with specified row/col parity sums
# Row parities (P1): exactly 2 odd
# Col parities (P3): exactly 2 odd

# For integer matrix with given marginal parities: always exists?
# Any binary matrix with row parity = (1,1,0) and col parity = (1,1,0):
# Example: M = [[1,0,0],[0,1,0],[0,0,0]] → row = (1,1,0), col = (1,1,0) ✓
# M = [[1,0,0],[0,1,0],[0,0,0]] → P2 fires twice at (P1=0,P3=0) and (P1=1,P3=1)

# So algebraically, any pair of nonzero even-sum vectors can be achieved.
# The constraint must come from the walk structure.

# PART 3: Key test - P2 firing positions relative to P1 and P3 phases
print(f"\n{'='*60}")
print("PART 3: P2 FIRING CONTEXT WHEN P1 FAILS FR")
print("What P3-phase is active when P2 fires in each P1-phase?")

# For cycles where P1 fails FR, extract P2's (P1-phase, P3-phase) at each firing
phase_corr = Counter()
phase_corr_fail = Counter()  # when P1 fails

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)

    # Skip multi-round cases for clarity
    if fc[1] > 3 or fc[3] > 3:
        continue

    fr1 = has_full_return_at(ms, n, word, cycle, 1)

    for s in range(ell):
        if word[s] == 2:  # P2 fires
            p1_phase = cycle[s][1]
            p3_phase = cycle[s][3]
            phase_corr[(p1_phase, p3_phase)] += 1
            if not fr1:
                phase_corr_fail[(p1_phase, p3_phase)] += 1

print(f"  P2's (P1-phase, P3-phase) distribution (all single-round cycles):")
for (p1, p3), cnt in sorted(phase_corr.items()):
    print(f"    P1={p1}, P3={p3}: {cnt}")

print(f"\n  Same, restricted to P1-fails-FR cycles:")
for (p1, p3), cnt in sorted(phase_corr_fail.items()):
    print(f"    P1={p1}, P3={p3}: {cnt}")

# PART 4: Direct test - does the walk force a PHASE IDENTITY?
print(f"\n{'='*60}")
print("PART 4: PHASE IDENTITY TEST")
print("For each single-round-both cycle, does c[P1] = c[P3] ever hold at P2 firings?")

p2_identity = Counter()
# (min steps between P1 and P3 firings) → correlation

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)
    if fc[1] > 3 or fc[3] > 3:
        continue

    fr1 = has_full_return_at(ms, n, word, cycle, 1)
    if fr1:
        continue  # only look at P1-fails

    # At each P2 firing, is c[P1] == c[P3]?
    has_identity = False
    for s in range(ell):
        if word[s] == 2:
            if cycle[s][1] == cycle[s][3]:
                has_identity = True
                break
    p2_identity[has_identity] += 1

print(f"  P1-fails cycles: P2 fires with c[P1]==c[P3] at some step:")
for v, cnt in sorted(p2_identity.items()):
    print(f"    {v}: {cnt}")

# PART 5: What is the UNIQUE constraint?
# For each P1-fail cycle, compute the full parity matrix of P2
# and check what constraint prevents P3 from also failing
print(f"\n{'='*60}")
print("PART 5: P2 PARITY MATRIX ANALYSIS")

parity_matrices = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)
    if fc[1] > 3 or fc[3] > 3:
        continue

    fr1 = has_full_return_at(ms, n, word, cycle, 1)
    if fr1:
        continue

    # Build parity matrix for P2
    M = [[0]*3 for _ in range(3)]  # M[P1-phase][P3-phase]
    for s in range(ell):
        if word[s] == 2:
            M[cycle[s][1]][cycle[s][3]] += 1

    # Convert to parity
    P = tuple(tuple(M[i][j] % 2 for j in range(3)) for i in range(3))
    parity_matrices[P] += 1

print(f"  P2 parity matrices (rows=P1-phase, cols=P3-phase) when P1 fails:")
for mat, cnt in parity_matrices.most_common(20):
    row_sums = [sum(mat[i]) % 2 for i in range(3)]
    col_sums = [sum(mat[i][j] for i in range(3)) % 2 for j in range(3)]
    print(f"    {mat} (rows={row_sums}, cols={col_sums}): {cnt}")

    # Check: does this matrix allow P3 to fail?
    # P3 fails needs col parity exactly 2 ones → already shown by col_sums
    # Also need the zero to be at a DIFFERENT position from P4's zero
    # But here we're just checking P2's contribution to P3
    col_ones = sum(col_sums)
    p3_can_fail = col_ones == 2  # P2 gives 2 nonzero phases to P3
    print(f"           P3 can receive nonzero pL: {p3_can_fail}")

print(f"\n{'='*60}")
print("PART 6: P4 CONSTRAINT ON P3 (when P1 fails)")
# When P1 fails, what does P4 contribute to P3?

p4_parity_at_p3 = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)
    if fc[1] > 3 or fc[3] > 3:
        continue

    fr1 = has_full_return_at(ms, n, word, cycle, 1)
    if fr1:
        continue

    # P4's parity at P3's phases
    p4_at_p3 = [0, 0, 0]
    for s in range(ell):
        if word[s] == 4:
            p4_at_p3[cycle[s][3]] += 1
    parity = tuple(x % 2 for x in p4_at_p3)
    p4_parity_at_p3[parity] += 1

    # P2's parity at P3's phases
    p2_at_p3 = [0, 0, 0]
    for s in range(ell):
        if word[s] == 2:
            p2_at_p3[cycle[s][3]] += 1
    p2_parity = tuple(x % 2 for x in p2_at_p3)

    # For P3 to fail FR: need p2_parity != p4_parity (both nonzero, different)
    # Already established both are in {011, 101, 110}
    # Check if they're the SAME → prevents P3 failure
    if p2_parity == parity and sum(p2_parity) == 2:
        # Same nonzero vector → displacement would be (d,d) for each phase
        # → only (0,0) and (1,1) values → NOT a permutation of {10,01,11}
        pass

print(f"  P4 parity at P3 phases (when P1 fails FR, single-round both):")
for parity, cnt in sorted(p4_parity_at_p3.items(), key=lambda x: -x[1]):
    print(f"    {parity}: {cnt}")

# CRITICAL: Check if pL(P3)=pR(P3) forces FR
print(f"\n  KEY: Check if P2-parity == P4-parity at P3 phases (forces FR at P3):")
same_count = 0
diff_count = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    fc = Counter(word)
    if fc[1] > 3 or fc[3] > 3:
        continue

    fr1 = has_full_return_at(ms, n, word, cycle, 1)
    if fr1:
        continue

    p2_at_p3 = [0]*3
    p4_at_p3 = [0]*3
    for s in range(ell):
        if word[s] == 2:
            p2_at_p3[cycle[s][3]] += 1
        elif word[s] == 4:
            p4_at_p3[cycle[s][3]] += 1
    p2p = tuple(x % 2 for x in p2_at_p3)
    p4p = tuple(x % 2 for x in p4_at_p3)

    if p2p == p4p:
        same_count += 1
    else:
        diff_count += 1

print(f"    Same parity vector: {same_count}")
print(f"    Different parity vector: {diff_count}")
print(f"    → If ALWAYS same: proves P3 can't fail (pL=pR → displacement has (0,0))")

sys.stdout.flush()
