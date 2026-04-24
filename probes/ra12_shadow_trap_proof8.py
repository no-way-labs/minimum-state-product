"""
Shadow Trap Proof — Part 8: The proof crystallizes.

THE MECHANISM:
A binary proc q forms a complementary pair when its two firings
in the good cycle see the same (L, R) context. Then:
  Step k1: (L, 0, R) -> 1   and   Step k2: (L, 1, R) -> 0
This traps any non-good config with proc q's neighbors = (L, ?, R).

WHEN DOES THIS HAPPEN?
In a sweep good cycle, proc q fires at step k1 (during forward sweep)
and step k2 (during backward sweep). Between k1 and k2:
- q's left neighbor fires some times, changing its value
- q's right neighbor fires some times, changing its value

For the (L,R) to be the same at both firings:
The LEFT neighbor must return to the same value after its firings between k1 and k2.
The RIGHT neighbor must return to the same value after its firings between k1 and k2.

KEY INSIGHT: "Isolated firings" at q means the mover jumps away from q
between q's two firings. This means q's NEIGHBORS may or may not have
fired between q's firings. The condition for the shadow trap is that
the neighbors' values match.

But actually, the problem says "isolated firings at SOME binary proc."
We only need ONE binary proc to form a complementary pair. Not all of them.

Let me verify: for general sweep patterns with non-consecutive binary,
does there always exist a binary proc with complementary pair?

Let me check systematically: generate various sweep patterns,
check which binary procs form complementary pairs.
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

def check_complementary_pairs(n, ms, movers):
    """Given a good cycle defined by ms and mover sequence,
    check which binary procs form complementary pairs."""
    CL = len(movers)

    # Build configs
    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in movers:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))

    if configs[-1] != configs[0]:
        return None, "doesn't close"
    configs = configs[:-1]

    # Build mover table
    table = []
    cmap = {}
    for k in range(CL):
        p = movers[k]
        g = configs[k]
        L, S, R = get_context(g, p, n)
        Sp = configs[(k+1) % CL][p]
        table.append((p, L, S, R, Sp))
        key = (p, L, S, R)
        if key in cmap:
            return None, f"duplicate context at step {k}"
        cmap[key] = (Sp, k)

    # Check binary procs
    comp_procs = []
    for q in range(n):
        if ms[q] != 2:
            continue
        fire_steps = [k for k in range(CL) if movers[k] == q]
        if len(fire_steps) != 2:
            continue
        k1, k2 = fire_steps
        _, L1, S1, R1, _ = table[k1]
        _, L2, S2, R2, _ = table[k2]
        if L1 == L2 and R1 == R2:
            comp_procs.append(q)

    return comp_procs, configs

# Test 1: Consecutive binary at 0,1,2, ternary at 3,...,n-1
print("=== Test 1: Consecutive binary at 0,1,2 ===")
for n in [5, 7, 9]:
    ms = [2, 2, 2] + [3] * (n - 3)
    # Sweep: right, left, extra-right for ternary
    movers = list(range(n)) + list(range(n-1, -1, -1)) + list(range(3, n))
    comp, result = check_complementary_pairs(n, ms, movers)
    if comp is not None:
        print(f"  n={n}: complementary binary procs = {comp}")
    else:
        print(f"  n={n}: {result}")

# Test 2: Non-consecutive binary at various positions
print("\n=== Test 2: Non-consecutive binary ===")
for n in [7, 9]:
    # Try binary at 0, 2, 4 (non-consecutive)
    ms = [2, 3, 2, 3, 2] + [3] * (n - 5)
    binary_procs = [p for p in range(n) if ms[p] == 2]
    print(f"\n  n={n}, binary at {binary_procs}, ms={ms}")

    # Build sweep: right, left, extra for ternary
    # Each binary fires 2 times, each ternary fires 3 times
    # CL = 2*3 + 3*(n-3) = 3n-3

    # Right sweep: everyone fires once (0->1)
    right = list(range(n))
    # Left sweep: everyone fires once (binary: 1->0, ternary: 1->2)
    left = list(range(n-1, -1, -1))
    # Extra: ternary fires once more (2->0)
    extra = [p for p in range(n) if ms[p] == 3]

    movers = right + left + extra
    CL = len(movers)
    assert CL == sum(ms), f"CL={CL} != sum(ms)={sum(ms)}"

    comp, result = check_complementary_pairs(n, ms, movers)
    if comp is not None:
        print(f"  Sweep R+L+extra: complementary binary procs = {comp}")
    else:
        print(f"  Sweep R+L+extra: {result}")

    # Try different sweep patterns
    # Pattern: right, partial left to middle, right from middle
    # This creates different neighbor contexts

    # Actually, let me try ALL possible mover orderings for small n
    # to understand when complementary pairs exist

# Test 3: Exhaustive for n=5
print("\n=== Test 3: Exhaustive n=5, ms=[2,3,2,3,2] ===")
n = 5
ms = [2, 3, 2, 3, 2]
CL = sum(ms)  # 12
binary_procs = [0, 2, 4]

# Generate all valid mover sequences:
# Each proc p must appear exactly ms[p] times
# The sequence must form a cycle (return to start config when starting from all-0)

from itertools import permutations
import math

# Generate all permutations of the mover multiset
mover_multiset = []
for p in range(n):
    mover_multiset.extend([p] * ms[p])

# Too many permutations (12! / (2!3!2!3!2!) = 166320)
# Let me just try many random ones and sweeps

import random
random.seed(42)

results = defaultdict(int)
seen_words = set()

# Structured sweeps
def try_word(word, label):
    cfg = [0] * n
    configs = [tuple(cfg)]
    for p in word:
        cfg = list(configs[-1])
        cfg[p] = (cfg[p] + 1) % ms[p]
        configs.append(tuple(cfg))
    if configs[-1] != configs[0]:
        return
    configs = configs[:-1]

    # Check unique contexts
    cmap = {}
    for k in range(len(word)):
        p = word[k]
        g = configs[k]
        L, S, R = get_context(g, p, n)
        key = (p, L, S, R)
        if key in cmap:
            return  # Duplicate context
        Sp = configs[(k+1) % len(word)][p]
        cmap[key] = (Sp, k)

    # Check complementary pairs
    comp = []
    for q in binary_procs:
        fire_steps = [k for k in range(len(word)) if word[k] == q]
        if len(fire_steps) != 2:
            continue
        k1, k2 = fire_steps
        g1 = configs[k1]
        g2 = configs[k2]
        L1, S1, R1 = get_context(g1, q, n)
        L2, S2, R2 = get_context(g2, q, n)
        if L1 == L2 and R1 == R2:
            comp.append(q)

    results[tuple(comp)] += 1
    if not comp:
        print(f"  NO COMP: {label}, word={word}")

# Try sweep patterns
for r_order in permutations(range(5)):
    for l_order in permutations(range(5)):
        word = list(r_order) + list(l_order)
        # Need 2 more firings for ternary procs 1, 3
        for extra in itertools.permutations([1, 3]):
            full_word = word + list(extra)
            if len(full_word) != CL:
                continue
            # Check each proc appears right number of times
            counts = defaultdict(int)
            for p in full_word:
                counts[p] += 1
            if all(counts[p] == ms[p] for p in range(n)):
                key = tuple(full_word)
                if key not in seen_words:
                    seen_words.add(key)
                    try_word(full_word, f"sweep")

print(f"\nResults over {sum(results.values())} valid words:")
for comp, count in sorted(results.items()):
    print(f"  Complementary procs {comp}: {count} words")

# Check if ALL valid words have at least one complementary pair
no_comp = results.get((), 0)
print(f"\nWords with NO complementary pair: {no_comp}")
