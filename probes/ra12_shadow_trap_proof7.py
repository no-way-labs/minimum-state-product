"""
Shadow Trap Proof — Part 7: 2-cycle analysis.

KEY DISCOVERY: The forced graph has many 2-cycles!
A 2-cycle means: config c has a forced proc p that fires c -> c'.
And c' has a forced proc (same p!) that fires c' -> c.

This happens when proc p sees context (L, S, R) in c, fires to S',
producing c'. In c', proc p sees context (L, S', R) — same L and R
because only p changed. If (p, L, S', R) is ALSO in the mover table
with transition back to S, we get a 2-cycle.

WHEN DOES THIS HAPPEN?
For binary proc p (ms[p] = 2): S ∈ {0,1}, S' = 1-S.
If both (p, L, 0, R) -> 1 and (p, L, 1, R) -> 0 are in the mover table,
then ANY non-good config where proc p has context (L, ?, R)
is trapped in a 2-cycle!

For ternary proc p: S' = S+1 or S-1 (depending on the transition).
Both (p, L, S, R) and (p, L, S', R) must be in the table with
transitions that form a cycle. For a 3-cycle: all three of
(p, L, 0, R), (p, L, 1, R), (p, L, 2, R) must be in the table
with cyclic transitions.

THIS IS THE PROOF MECHANISM:
A binary proc q fires exactly twice in the good cycle: at step k1 and k2.
At step k1: context (L1, S1, R1), fires to 1-S1.
At step k2: context (L2, S2, R2), fires to 1-S2.

If L1 = L2 and R1 = R2 (same left and right neighbor values), then:
Since S2 = 1-S1 (binary proc fired once between k1 and k2):
  Step k1: (L, S, R) -> 1-S
  Step k2: (L, 1-S, R) -> S
This is a COMPLEMENTARY PAIR! Any non-good config with proc q's
neighbors having values (L, ?, R) is trapped in a 2-cycle.

WHEN DOES L1 = L2 AND R1 = R2?
In a sweep: between q's two firings, q's neighbors have changed.
But if the firings are "isolated" (the mover moves away from q
between firings), the neighbors' values at q's second firing
are NOT the same as at q's first firing.

Wait, that contradicts the 2-cycle mechanism...

Let me check: in our n=7 example, what are the 2-cycles?
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

n = 7
ms = [2, 2, 2, 3, 3, 3, 3]
CL = sum(ms)  # 18

# Build good cycle
movers = list(range(7)) + list(range(6, -1, -1)) + [3, 4, 5, 6]
cfg = [0] * n
configs = [tuple(cfg)]
for p in movers:
    cfg = list(configs[-1])
    cfg[p] = (cfg[p] + 1) % ms[p]
    configs.append(tuple(cfg))
configs = configs[:-1]

# Mover context table
table = []
cmap = {}
for k in range(CL):
    p = movers[k]
    g = configs[k]
    L, S, R = get_context(g, p, n)
    Sp = configs[(k+1) % CL][p]
    table.append((p, L, S, R, Sp))
    cmap[(p, L, S, R)] = (Sp, k)

# Find complementary pairs: (p, L, S, R) -> S' and (p, L, S', R) -> S''
# If S'' = S, we have a 2-cycle potential.
print("=== Complementary pairs in mover table ===")
comp_pairs = []
for k1 in range(CL):
    p1, L1, S1, R1, Sp1 = table[k1]
    # Look for entry with (p1, L1, Sp1, R1) -> ?
    key2 = (p1, L1, Sp1, R1)
    if key2 in cmap:
        Sp2, k2 = cmap[key2]
        if Sp2 == S1:
            comp_pairs.append((k1, k2, p1, L1, S1, R1, Sp1))
            print(f"  Steps {k1:2d}<->{k2:2d}: proc {p1}, ({L1},{S1},{R1})->{Sp1} and ({L1},{Sp1},{R1})->{S1}")

print(f"\nTotal complementary pairs: {len(comp_pairs)}")

# For each complementary pair, how many non-good configs are trapped?
print("\n=== Configs trapped by each complementary pair ===")
all_configs = list(itertools.product(*[range(m) for m in ms]))
good_set = set(configs)
non_good = [c for c in all_configs if c not in good_set]

total_trapped = set()
for k1, k2, p, L, S, R, Sp in comp_pairs:
    trapped = []
    for c in non_good:
        ctx = get_context(c, p, n)
        if ctx[0] == L and ctx[2] == R:  # Left and right match
            trapped.append(c)
    total_trapped.update(trapped)
    if trapped:
        print(f"  Proc {p}, L={L}, R={R}: {len(trapped)} trapped configs")

print(f"\nTotal unique trapped configs: {len(total_trapped)} / {len(non_good)} non-good")
print(f"Untrapped non-good: {len(non_good) - len(total_trapped)}")

# KEY QUESTION: Which procs form complementary pairs?
print("\n=== Which procs have complementary pairs? ===")
paired_procs = set()
for k1, k2, p, L, S, R, Sp in comp_pairs:
    paired_procs.add(p)
print(f"Procs with complementary pairs: {sorted(paired_procs)}")
print(f"Binary procs: {[p for p in range(n) if ms[p] == 2]}")

# Let's check what happens at each binary proc
print("\n=== Binary proc firing analysis ===")
for q in range(n):
    if ms[q] != 2:
        continue
    fire_steps = [k for k in range(CL) if movers[k] == q]
    print(f"\nBinary proc {q}, fires at steps {fire_steps}:")
    for k in fire_steps:
        p, L, S, R, Sp = table[k]
        print(f"  Step {k}: ({L},{S},{R}) -> {Sp}")

    if len(fire_steps) == 2:
        k1, k2 = fire_steps
        p, L1, S1, R1, Sp1 = table[k1]
        _, L2, S2, R2, Sp2 = table[k2]
        print(f"  L matches: {L1 == L2}, R matches: {R1 == R2}")
        print(f"  S complementary: {S2 == Sp1 and Sp2 == S1}")

# DISCOVERY: For our sweep, binary proc 0 fires at steps 0 and 13:
# Step 0: (0,0,0)->1, Step 13: (2,1,0)->0
# L changes from 0 to 2, R stays 0. NOT complementary!
# So the 2-cycles come from ternary procs, not binary procs!

print("\n=== Ternary proc analysis ===")
for q in range(n):
    if ms[q] != 3:
        continue
    fire_steps = [k for k in range(CL) if movers[k] == q]
    print(f"\nTernary proc {q}, fires at steps {fire_steps}:")
    for k in fire_steps:
        p, L, S, R, Sp = table[k]
        print(f"  Step {k}: ({L},{S},{R}) -> {Sp}")

    # Check which pairs are complementary
    for i in range(len(fire_steps)):
        for j in range(i+1, len(fire_steps)):
            k1, k2 = fire_steps[i], fire_steps[j]
            p1, L1, S1, R1, Sp1 = table[k1]
            _, L2, S2, R2, Sp2 = table[k2]
            if L1 == L2 and R1 == R2:
                print(f"  Steps {k1},{k2}: SAME L={L1}, R={R1}")
                print(f"    ({L1},{S1},{R1})->{Sp1} and ({L2},{S2},{R2})->{Sp2}")
                if Sp1 == S2 and Sp2 == S1:
                    print(f"    *** 2-CYCLE! ***")

# Let me now look at the 2-cycles from a different angle:
# Which specific configs form 2-cycles?
print("\n\n=== Anatomy of 2-cycles ===")
two_cycles = []
for c in non_good:
    for p in range(n):
        ctx = get_context(c, p, n)
        key = (p,) + ctx
        if key in cmap:
            Sp, step = cmap[key]
            new_cfg = list(c)
            new_cfg[p] = Sp
            c2 = tuple(new_cfg)
            if c2 in good_set:
                continue
            # Check if c2 -> c via same proc
            ctx2 = get_context(c2, p, n)
            key2 = (p,) + ctx2
            if key2 in cmap:
                Sp2, step2 = cmap[key2]
                if Sp2 == c[p]:
                    two_cycles.append((c, c2, p, step, step2))

# Deduplicate
seen = set()
unique_2cycles = []
for c1, c2, p, s1, s2 in two_cycles:
    key = frozenset([c1, c2])
    if key not in seen:
        seen.add(key)
        unique_2cycles.append((c1, c2, p, s1, s2))

print(f"Unique 2-cycles: {len(unique_2cycles)}")
for c1, c2, p, s1, s2 in unique_2cycles[:10]:
    min_d1 = min(sum(1 for a,b in zip(c1,g) if a!=b) for g in configs)
    min_d2 = min(sum(1 for a,b in zip(c2,g) if a!=b) for g in configs)
    print(f"  {c1} <-> {c2} via proc {p} (steps {s1},{s2}), Hamming to good: {min_d1},{min_d2}")
