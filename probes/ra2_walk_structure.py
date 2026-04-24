"""
Script 2: Walk structure analysis for ring-adjacent walks.

Analyzes:
- Boundary processor fraction
- Spread rate per step
- Structure of walks that satisfy binary constraints
"""

from collections import Counter
from itertools import product as iprod
import random

def ring_neighbors(p, n):
    """Return ring-adjacent positions (including self)."""
    return [(p - 1) % n, p, (p + 1) % n]

def enumerate_all_walks(n, length, start=0):
    """
    Enumerate ALL ring-adjacent walks of given length starting at `start`.
    Walk = list of length `length` positions.
    Each consecutive pair is ring-adjacent.
    Returns generator.
    """
    if length == 1:
        yield [start]
        return
    for sub in enumerate_all_walks(n, length - 1, start):
        for nxt in ring_neighbors(sub[-1], n):
            yield sub + [nxt]

def sample_walks(n, length, start=0, num_samples=10000):
    """Sample random ring-adjacent walks."""
    walks = []
    for _ in range(num_samples):
        walk = [start]
        for _ in range(length - 1):
            walk.append(random.choice(ring_neighbors(walk[-1], n)))
        walks.append(walk)
    return walks

def walk_stats(walk, n):
    """Compute statistics of a walk."""
    fc = Counter(walk)
    visited = set(walk)

    # "Boundary" processors: those visited only from one side
    # More precisely: the leftmost and rightmost of the visited arc
    # On a ring this is tricky; use the contiguous arc notion
    # Instead: count how many processors have fire count 1 vs > 1
    singleton_procs = sum(1 for v in fc.values() if v == 1)
    multi_procs = sum(1 for v in fc.values() if v > 1)

    # Spread: how many distinct positions visited
    coverage = len(visited)

    # Max deviation from start
    positions = list(walk)
    max_dist = max(min(abs(p - walk[0]), n - abs(p - walk[0])) for p in positions)

    return {
        'coverage': coverage,
        'singleton_procs': singleton_procs,
        'multi_procs': multi_procs,
        'max_dist': max_dist,
        'fire_counts': fc,
        'length': len(walk),
    }

print("=" * 70)
print("SCRIPT 2: Walk Structure Analysis")
print("=" * 70)

# Part 1: Spread rate
print("\n--- Part 1: How fast does a ring-adjacent walk spread? ---")
print("""
A ring-adjacent walk from position 0:
- After k steps, the walk can reach at most position k (CW) or -k (CCW).
- Maximum spread after k steps: 2k+1 positions (if no revisiting).
- But on a ring of n processors, spread is capped at n.
- To cover all n: need k >= ceil((n-1)/2) in BOTH directions.
  Minimum: n-1 steps going one direction, or ~n/2 going both.
""")

for n in [5, 7, 9, 11]:
    print(f"\nn={n}:")
    # Sample walks of various lengths, check coverage
    for cl in [n, n+2, 2*n-2, 2*n, 3*n]:
        if cl < 1:
            continue
        walks = sample_walks(n, cl, start=0, num_samples=5000)
        full_cov = sum(1 for w in walks if len(set(w)) == n)
        avg_cov = sum(len(set(w)) for w in walks) / len(walks)
        # Among full coverage: check binary parity
        # Use positions 0, 2, 4 as binary (non-consecutive on ring for n >= 5)
        if n >= 5:
            bp = [0, 2, 4] if n >= 7 else [0, 2, 4]
            fc_even = 0
            for w in walks:
                fc = Counter(w)
                if len(set(w)) == n and all(fc[p] % 2 == 0 and fc[p] >= 2 for p in bp):
                    fc_even += 1
        else:
            fc_even = 0
        print(f"  CL={cl:3d}: avg_coverage={avg_cov:.1f}/{n}, "
              f"full_cov={full_cov}/{len(walks)}, "
              f"full+binary_even={fc_even}/{len(walks)}")

# Part 2: Structure of walks that achieve full coverage + binary parity
print("\n\n--- Part 2: Walk types achieving full coverage + even binary fire counts ---")

for n in [5, 7]:
    print(f"\nn={n}:")
    # Non-consecutive binary positions
    if n == 5:
        bp_list = [[0, 2, 4]]  # Only valid non-consecutive triple on C_5 is... let's check
        # On C_5: 0-1-2-3-4-0. Non-adjacent means no two at distance 1.
        # {0,2,4}: dist(0,2)=2, dist(2,4)=2, dist(4,0)=1. Adjacent! NOT valid.
        # {0,2,3}: dist(2,3)=1. No.
        # Actually on C_5, any 3 vertices have some pair at distance <= 1 if n=5, 3 non-adj is impossible?
        # floor(5/2) = 2 is max independent set on C_5. So 3 non-adjacent is IMPOSSIBLE on C_5!
        from itertools import combinations
        valid = []
        for combo in combinations(range(n), 3):
            if all(min(abs(a-b), n-abs(a-b)) >= 2 for a, b in combinations(combo, 2)):
                valid.append(combo)
        print(f"  Valid non-consecutive binary triples: {valid}")
        if not valid:
            print(f"  NO valid placement of 3 non-consecutive binary procs on C_{n}!")
            print(f"  Max independent set on C_{n} = floor({n}/2) = {n//2}")
            continue
        bp_list = valid

    elif n == 7:
        from itertools import combinations
        valid = []
        for combo in combinations(range(n), 3):
            if all(min(abs(a-b), n-abs(a-b)) >= 2 for a, b in combinations(combo, 2)):
                valid.append(combo)
        print(f"  Valid non-consecutive binary triples: {len(valid)} placements")
        bp_list = valid[:3]  # Use first few

    for bp in bp_list[:2]:
        print(f"\n  Binary positions: {bp}")
        # Find walks achieving the goal
        # For small n, enumerate short walks
        found = []
        for cl in range(n, 4*n+1):
            # Sample heavily
            walks = sample_walks(n, cl, start=0, num_samples=20000)
            for w in walks:
                fc = Counter(w)
                if (len(set(w)) == n and
                    all(fc[p] % 2 == 0 and fc[p] >= 2 for p in bp) and
                    min(abs(w[-1] - w[0]), n - abs(w[-1] - w[0])) <= 1):  # cycle-closing
                    found.append((cl, w, fc))
            if found:
                break

        if found:
            cl, w, fc = found[0]
            print(f"    Found at CL={cl}: walk={w}")
            print(f"    Fire counts: {dict(fc)}")
            print(f"    Binary fire counts: {[(p, fc[p]) for p in bp]}")
        else:
            print(f"    No walk found up to CL={4*n}")

# Part 3: Theoretical arc analysis
print("\n\n--- Part 3: Arc structure of ring-adjacent walks ---")
print("""
Key structural insight:

A ring-adjacent walk on C_n is equivalent to a walk on the integer line
(unwrapped ring), where at each step we move by {-1, 0, +1}.

To visit all n processors on the ring, the walk (mod n) must hit all
residues 0, 1, ..., n-1.

For a CYCLE (returns to start): the walk on the line returns to a position
congruent to start (mod n), i.e., net displacement is 0 mod n.

The walk can either:
(A) Stay in a window of width n (back-and-forth): displacement in [0, n-1],
    visiting all positions. To return: must come back, total ~ 2n.
(B) Go around the ring (net displacement = n): total = n steps minimum.
    BUT fire counts are all 1 (each position visited once). Bad for binary.
(C) Go around twice (net displacement = 2n): total = 2n, all fire counts = 2.
    This WORKS for binary constraint!

Type (C) is the KEY: a double-loop walk of length 2n where every processor
fires exactly twice. This satisfies:
- hfull: yes (all fire counts = 2)
- binary even: yes (fire count = 2)
- CL = 2n

But CL = 2n must be <= product of state sizes.
For ms with 3 binary (m=2) and rest ternary (m=3):
  product = 2^3 * 3^(n-3) = 8 * 3^(n-3)

  CL = 2n <= 8 * 3^(n-3)?

  n=5: 10 <= 8*9 = 72.  YES
  n=7: 14 <= 8*81 = 648. YES
  n=9: 18 <= 8*729 = 5832. YES

So CL is not the bottleneck! The walk length is easily within the product.
The real constraint is DISTINCT CONFIGS + NO ENTRY CONFLICT.
""")

# Part 4: Fire count vs product budget
print("--- Part 4: Fire count budget analysis ---")
print(f"{'n':>4} | {'2n':>6} | {'product':>10} | {'ratio':>8} | {'avg_fc':>8}")
print("-" * 50)
for n in [5, 7, 9, 11, 13, 15]:
    cl_min = 2 * n  # double loop
    prod = 8 * (3 ** (n - 3))
    ratio = prod / cl_min
    avg_fc = cl_min / n  # average fire count
    print(f"{n:4d} | {cl_min:6d} | {prod:10d} | {ratio:8.1f} | {avg_fc:8.1f}")

print("""
The product grows exponentially while CL grows linearly.
Walk length is NEVER the bottleneck.
The real question is: can we assign DISTINCT configurations along the walk
such that no entry conflict occurs?

Entry conflict: two steps with the same (processor, left_val, right_val)
context but different required transitions (one as mover, one as non-mover).
""")
