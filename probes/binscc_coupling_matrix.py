#!/usr/bin/env python3
"""The P2 coupling matrix: when P1 escapes EC, what constrains P3?

At n=5 (ms=[2,3,2,3,2]):
- P2 fires fc[P2] times. Each firing occurs at (c[P1], c[P3]) = (a, b).
- The coupling matrix count(a,b) determines K_a for P1 and J_b for P3.
- When P1 escapes, the coupling forces P3 into EC.

Analyze the coupling matrix for:
1. All cycles where P1 escapes but P3 has EC
2. Compare with n=4 (where both escape)
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

# n=5 coupling analysis
print("=" * 70)
print("n=5: P2 COUPLING MATRIX ANALYSIS")
print("=" * 70)

n, ms = 5, [2,3,2,3,2]
words = enumerate_mover_words(ms, n, 16)

p1_escape_coupling = Counter()  # coupling matrix when P1 escapes
p3_escape_coupling = Counter()

p1_escape_count = 0
p3_escape_count = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    p1_ec = has_entry_conflict_at(ms, n, word, cycle, 1)
    p3_ec = has_entry_conflict_at(ms, n, word, cycle, 3)

    # Build P2 coupling matrix: (c[P1], c[P3]) at each P2 firing
    coupling = {}  # (a,b) -> count
    for s in range(ell):
        if word[s] == 2:  # P2 fires
            a, b = cycle[s][1], cycle[s][3]
            coupling[(a,b)] = coupling.get((a,b), 0) + 1

    coupling_tuple = tuple(sorted(coupling.items()))

    if not p1_ec:
        p1_escape_coupling[coupling_tuple] += 1
        p1_escape_count += 1
    if not p3_ec:
        p3_escape_coupling[coupling_tuple] += 1
        p3_escape_count += 1

print(f"P1 escapes: {p1_escape_count}")
print(f"P3 escapes: {p3_escape_count}")

print(f"\nP2 coupling matrix when P1 escapes:")
for ct, cnt in sorted(p1_escape_coupling.items(), key=lambda x: -x[1])[:15]:
    # Decode coupling
    matrix = [[0]*3 for _ in range(3)]
    for (a,b), v in ct:
        matrix[a][b] = v
    row_sums = [sum(row) for row in matrix]
    col_sums = [sum(matrix[a][b] for a in range(3)) for b in range(3)]
    print(f"  K(P1)={row_sums}, J(P3)={col_sums}: {cnt}")
    for a in range(3):
        print(f"    [{matrix[a][0]}, {matrix[a][1]}, {matrix[a][2]}]")

print(f"\nP2 coupling matrix when P3 escapes:")
for ct, cnt in sorted(p3_escape_coupling.items(), key=lambda x: -x[1])[:15]:
    matrix = [[0]*3 for _ in range(3)]
    for (a,b), v in ct:
        matrix[a][b] = v
    row_sums = [sum(row) for row in matrix]
    col_sums = [sum(matrix[a][b] for a in range(3)) for b in range(3)]
    print(f"  K(P1)={row_sums}, J(P3)={col_sums}: {cnt}")
    for a in range(3):
        print(f"    [{matrix[a][0]}, {matrix[a][1]}, {matrix[a][2]}]")

# KEY: check overlap between P1-escape and P3-escape coupling matrices
p1_set = set(p1_escape_coupling.keys())
p3_set = set(p3_escape_coupling.keys())
overlap = p1_set & p3_set
print(f"\n{'='*70}")
print(f"Coupling matrix overlap: {len(overlap)} shared matrices")
if overlap:
    for ct in list(overlap)[:5]:
        matrix = [[0]*3 for _ in range(3)]
        for (a,b), v in ct:
            matrix[a][b] = v
        print(f"  Shared: {dict(ct)}")
else:
    print("  NO SHARED MATRICES → coupling prevents simultaneous escape!")

# PART 2: n=4 coupling for comparison
print(f"\n{'='*70}")
print("n=4: P2 COUPLING MATRIX IN EC-FREE CYCLES")
print("=" * 70)

n4, ms4 = 4, [2,3,2,3]
words4 = enumerate_mover_words(ms4, n4, 14)

for word in words4:
    cycle = build_cycle(ms4, n4, word)
    if cycle is None or not is_wrap_adjacent(word, n4):
        continue
    p1_ec = has_entry_conflict_at(ms4, n4, word, cycle, 1)
    p3_ec = has_entry_conflict_at(ms4, n4, word, cycle, 3)
    if p1_ec or p3_ec:
        continue
    # EC-free: show coupling matrix
    ell = len(word)
    coupling = {}
    for s in range(ell):
        if word[s] == 2:
            a, b = cycle[s][1], cycle[s][3]
            coupling[(a,b)] = coupling.get((a,b), 0) + 1
    matrix = [[0]*3 for _ in range(3)]
    for (a,b), v in coupling.items():
        matrix[a][b] = v
    row_sums = [sum(row) for row in matrix]
    col_sums = [sum(matrix[a][b] for a in range(3)) for b in range(3)]
    fc = Counter(word)
    print(f"  fc={[fc.get(p,0) for p in range(4)]} K(P1)={row_sums} J(P3)={col_sums}")
    for a in range(3):
        print(f"    [{matrix[a][0]}, {matrix[a][1]}, {matrix[a][2]}]")
    break  # just one example

# PART 3: What P3 (J,K) values are FORCED by P1-escape coupling?
print(f"\n{'='*70}")
print("n=5: FORCED P3 STRUCTURE WHEN P1 ESCAPES")
print("=" * 70)

n, ms = 5, [2,3,2,3,2]
p3_jk_when_p1_escape = Counter()
p3_ec_mechanism = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    p1_ec = has_entry_conflict_at(ms, n, word, cycle, 1)
    if p1_ec:
        continue

    # P1 escapes. What's P3's structure?
    bL3, bR3 = 2, 4
    jks = []
    for k in range(3):
        steps = [s for s in range(ell) if cycle[s][3] == k]
        J = sum(1 for s in steps if word[s] == bL3)
        K = sum(1 for s in steps if word[s] == bR3)
        jks.append((J, K))
    p3_jk_when_p1_escape[tuple(jks)] += 1

    # What mechanism gives P3 EC?
    has_30 = any((J >= 3 and K == 0) or (J == 0 and K >= 3) for J, K in jks)
    has_20 = any((J >= 2 and K == 0) or (J == 0 and K >= 2) for J, K in jks)
    has_be = any(J % 2 == 0 and K % 2 == 0 and J + K > 0 for J, K in jks)
    if has_30:
        p3_ec_mechanism['toggle≥3'] += 1
    elif has_20:
        p3_ec_mechanism['toggle=2'] += 1
    elif has_be:
        p3_ec_mechanism['both_even'] += 1
    else:
        p3_ec_mechanism['walk_only'] += 1

print(f"P3 (J,K) when P1 escapes:")
for jk, cnt in sorted(p3_jk_when_p1_escape.items(), key=lambda x: -x[1]):
    has30 = any((J>=3 and K==0) or (J==0 and K>=3) for J,K in jk)
    has20 = any((J>=2 and K==0) or (J==0 and K>=2) for J,K in jk)
    marker = " ←(≥3,0)!" if has30 else (" ←(2,0)" if has20 else "")
    print(f"  {jk}: {cnt}{marker}")

print(f"\nP3 EC mechanism when P1 escapes: {dict(p3_ec_mechanism)}")
