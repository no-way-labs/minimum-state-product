#!/usr/bin/env python3
"""BIPARTITE LENGTH FORCING THEOREM (ANALYTICAL)

For alternating ring n=2k: ms=(2,3,2,3,...,2,3). k binary, k ternary.
Ring is bipartite: binary at even positions, ternary at odd.
Walk MUST alternate B-T (bipartite constraint).

THEOREM: Minimum wrap-adjacent cycle length ℓ_min = 12⌈k/2⌉.

PROOF:
1. Walk alternates B-T → ℓ even.
2. ℓ = 2T where T = total binary firings = total ternary firings.
3. Binary: each fires ≡ 0 mod 2, ≥ 2 → T = sum of k even numbers ≥ 2.
   Achievable values: T ∈ {2k, 2k+2, 2k+4, ...} = even ≥ 2k.
4. Ternary: each fires ≡ 0 mod 3, ≥ 3 → T = sum of k multiples of 3 ≥ 3.
   Achievable values: T ∈ {3k, 3k+3, 3k+6, ...} = multiples of 3 ≥ 3k.
5. Need T in both sets: T even AND T ≡ 0 mod 3, so T ≡ 0 mod 6.
   And T ≥ max(2k, 3k) = 3k.
6. T_min = smallest multiple of 6 ≥ 3k = 6⌈k/2⌉.
7. ℓ_min = 2T_min = 12⌈k/2⌉. QED.

This script verifies the theorem computationally.
"""
import time, math
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
print("BIPARTITE LENGTH FORCING THEOREM")
print("=" * 70)

# Verify formula
print("\nFormula: ℓ_min = 12⌈k/2⌉ for alternating ring n=2k\n")
for k in range(2, 8):
    n = 2 * k
    T_min = 6 * math.ceil(k / 2)
    ell_min_formula = 2 * T_min
    fc_min_naive = 2 * k + 3 * k  # = 5k

    print(f"  k={k} (n={n}): T_min={T_min}, ℓ_min={ell_min_formula}, "
          f"naive_min={fc_min_naive}, gap={ell_min_formula - fc_min_naive}")

    # Binary fc at T_min
    bin_remaining = T_min - 2 * k
    print(f"    Binary: base 2×{k}={2*k}, extra {bin_remaining}")
    # Ternary fc at T_min
    tern_remaining = T_min - 3 * k
    print(f"    Ternary: base 3×{k}={3*k}, extra {tern_remaining}")
    if tern_remaining == 0:
        print(f"    → All ternary fire minimum (3)")
    elif tern_remaining == 3:
        print(f"    → One ternary fires 6 (double), rest fire 3")

# Verify computationally
print(f"\n{'='*60}")
print("COMPUTATIONAL VERIFICATION")
print("=" * 60)

for k in [2, 3, 4]:
    n = 2 * k
    ms = [2, 3] * k
    T_min = 6 * math.ceil(k / 2)
    ell_predicted = 2 * T_min

    # Try to find cycles at predicted length and below
    t0 = time.time()
    for test_len in [ell_predicted - 2, ell_predicted]:
        words = enumerate_mover_words(ms, n, test_len)
        count = sum(1 for w in words
                    if build_cycle(ms, n, w) is not None
                    and is_wrap_adjacent(w, n))
        elapsed = time.time() - t0
        status = "✓" if (test_len == ell_predicted and count > 0) or \
                        (test_len < ell_predicted and count == 0) else "✗"
        print(f"  n={n}: max_len={test_len}: {count:>6} cycles ({elapsed:.1f}s) {status}")
        if count > 0 and test_len == ell_predicted:
            # Show fc distribution
            fc_dist = Counter()
            for w in words:
                c = build_cycle(ms, n, w)
                if c and is_wrap_adjacent(w, n):
                    fc = Counter(w)
                    fc_dist[tuple(fc.get(p,0) for p in range(n))] += 1
            for fk, cnt in sorted(fc_dist.items(), key=lambda x: -x[1])[:3]:
                bin_fcs = [fk[i] for i in range(0, n, 2)]
                tern_fcs = [fk[i] for i in range(1, n, 2)]
                print(f"    fc={list(fk)} bin={bin_fcs} tern={tern_fcs}: {cnt}")

# CONSEQUENCE: forced fire counts
print(f"\n{'='*60}")
print("CONSEQUENCE: FORCED FIRE COUNT STRUCTURE")
print("=" * 60)

print("""
For k even (n=4,8,12,...):
  T_min = 3k. Ternary: ALL fire 3 (minimum).
  Binary: sum = 3k with k even numbers ≥ 2.
  Some binary fires ≥ 4 (since average = 3 and all are even).

For k odd (n=6,10,14,...):
  T_min = 3k+3. Ternary: one fires 6, rest fire 3.
  Binary: sum = 3k+3 with k even numbers ≥ 2.
  Some binary fires ≥ 4.

In BOTH cases: at least one binary fires ≥ 4.
This creates a phase at adjacent ternary with high (J,K) values.
""")

# Verify: does some binary always fire ≥ 4?
print("Binary fire count ranges:")
for k in [2, 3, 4]:
    n = 2 * k
    ms = [2, 3] * k
    T = 6 * math.ceil(k / 2)
    words = enumerate_mover_words(ms, n, 2 * T)
    max_bin_fc = 0
    min_max_bin = float('inf')
    for w in words:
        c = build_cycle(ms, n, w)
        if not c or not is_wrap_adjacent(w, n):
            continue
        fc = Counter(w)
        bin_max = max(fc.get(p, 0) for p in range(0, n, 2))
        if bin_max > max_bin_fc:
            max_bin_fc = bin_max
        if bin_max < min_max_bin:
            min_max_bin = bin_max
    print(f"  n={n}: max(binary fc) range = [{min_max_bin}, {max_bin_fc}]")
