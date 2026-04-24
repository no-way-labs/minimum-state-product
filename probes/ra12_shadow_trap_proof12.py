"""
Shadow Trap Proof — Part 12: Analyzing the multi-step cycles.

From Part 11, the forced graph has:
- SCC of size 8 (a long cycle involving procs 0,1,4)
- SCC of size 5 (a cycle involving procs 2,3)
- Two 2-cycles (proc 4 complementary pair)

The SIZE-5 SCC is especially interesting:
(0,1,0,0,0) -> (0,1,0,2,0) -> (0,1,1,2,0) -> (0,1,1,0,0) -> (0,1,1,1,0) -> ...
via procs 2,7,3,6,3,...

Let me trace the actual cycles and understand the mechanism.

KEY INSIGHT TO PROVE:
In a sweep with ternary procs, the ternary procs create a "waterfall" pattern
where the values cycle through 0->1->2->0. The mover table captures THREE
contexts for each ternary proc (one per value). When a non-good config has
a ternary proc in a "wrong" state, the forced transitions cycle through
the ternary proc's three values, creating a 3-step sub-cycle.

But how does this create a CLOSED cycle? The 3-step sub-cycle changes the
ternary proc's value through all three states. After 3 firings of the
ternary proc, its value returns to the start. But the neighbors' values
might change in between if they're also forced.

The multi-step cycle arises from INTERACTION between multiple forced procs.
"""

import itertools
from collections import defaultdict

def get_context(cfg, p, n):
    return (cfg[(p-1) % n], cfg[p], cfg[(p+1) % n])

n = 5
ms = [2, 3, 2, 3, 2]
CL = sum(ms)

movers = [0,1,2,3,4, 4,3,2,1,0, 1,3]
cfg = [0] * n
configs = [tuple(cfg)]
for p in movers:
    cfg = list(configs[-1])
    cfg[p] = (cfg[p] + 1) % ms[p]
    configs.append(tuple(cfg))
configs = configs[:-1]
good_set = set(configs)

cmap = {}
table = []
for k in range(CL):
    p = movers[k]
    g = configs[k]
    L, S, R = get_context(g, p, n)
    Sp = configs[(k+1) % CL][p]
    cmap[(p, L, S, R)] = (Sp, k)
    table.append((p, L, S, R, Sp))

# Trace the size-5 SCC cycle
print("=== Tracing size-5 SCC ===")
scc5 = [(0,1,0,0,0), (0,1,0,2,0), (0,1,1,0,0), (0,1,1,1,0), (0,1,1,2,0)]
scc5_set = set(scc5)

# Follow the cycle step by step
current = (0, 1, 0, 0, 0)
for step in range(10):
    forced = []
    for p in range(n):
        ctx = get_context(current, p, n)
        key = (p,) + ctx
        if key in cmap:
            Sp, k = cmap[key]
            new_cfg = list(current)
            new_cfg[p] = Sp
            nc = tuple(new_cfg)
            in_scc = nc in scc5_set
            forced.append((p, k, nc, in_scc))

    # Pick the transition that stays in SCC
    stay_in_scc = [f for f in forced if f[3]]
    print(f"  Step {step}: {current}")
    for p, k, nc, in_scc in forced:
        marker = " ***" if in_scc else ""
        print(f"    Forced: proc {p} (matches step {k}) -> {nc}{marker}")

    if stay_in_scc:
        current = stay_in_scc[0][2]
    else:
        print("    No transition stays in SCC!")
        break

# Now trace the size-8 SCC
print("\n=== Tracing size-8 SCC ===")
scc8 = [(0,0,0,1,0), (0,2,0,1,0), (1,0,0,1,0), (1,0,0,1,1),
        (1,1,0,1,0), (1,1,0,1,1), (1,2,0,1,0), (1,2,0,1,1)]
scc8_set = set(scc8)

current = (0, 0, 0, 1, 0)
for step in range(20):
    forced = []
    for p in range(n):
        ctx = get_context(current, p, n)
        key = (p,) + ctx
        if key in cmap:
            Sp, k = cmap[key]
            new_cfg = list(current)
            new_cfg[p] = Sp
            nc = tuple(new_cfg)
            in_scc = nc in scc8_set
            forced.append((p, k, nc, in_scc))

    stay_in_scc = [f for f in forced if f[3]]
    if not stay_in_scc:
        other = [f for f in forced]
        print(f"  Step {step}: {current} -> no SCC transition")
        for p, k, nc, _ in other:
            print(f"    Forced: proc {p} (step {k}) -> {nc}")
        break

    p, k, nc, _ = stay_in_scc[0]
    print(f"  Step {step}: {current} -> fire proc {p} (step {k}) -> {nc}")
    if nc == (0, 0, 0, 1, 0) and step > 0:
        print(f"  *** CYCLE CLOSED after {step+1} steps! ***")
        break
    current = nc

# KEY ANALYSIS: What INVARIANT holds in each SCC?
print("\n\n=== INVARIANT ANALYSIS ===")
print("\nSize-5 SCC configs:")
for c in sorted(scc5):
    print(f"  {c}: proc 0={c[0]}, proc 4={c[4]}")
    # What's constant?
print("Invariant: proc 0 = 0, proc 4 = 0, proc 1 = 1")
print("Varying: proc 2 ∈ {0,1}, proc 3 ∈ {0,1,2}")
print("But not all combos: only 5 of 6 possible")

print("\nSize-8 SCC configs:")
for c in sorted(scc8):
    print(f"  {c}: proc 2={c[2]}, proc 3={c[3]}")
print("Invariant: proc 2 = 0, proc 3 = 1")
print("Varying: proc 0 ∈ {0,1}, proc 1 ∈ {0,1,2}, proc 4 ∈ {0,1}")
print("Not all combos: 8 of 12 possible")

# THE KEY OBSERVATION:
# In the size-5 SCC, proc 3 (ternary) has value ∈ {0,1,2} — it cycles through
# all three values. The forced transitions rotate proc 3 through its values.
# But proc 2 also changes (0->1->1->1->0->...).
# The cycle is driven by the interaction between procs 2 and 3.

# Let me check: for which ternary procs is the FULL value cycle present?
print("\n=== Ternary proc value cycling ===")
for q in range(n):
    if ms[q] != 3:
        continue
    entries = [(k, L, S, R, Sp) for k, (p, L, S, R, Sp) in enumerate(table) if p == q]
    print(f"\nTernary proc {q}:")
    for k, L, S, R, Sp in entries:
        print(f"  Step {k}: ({L},{S},{R}) -> {Sp}")

    # Check if all three values appear as S
    values = set(S for _, L, S, R, Sp in entries)
    print(f"  Values seen: {values}")

    # Check if the three entries form a cycle: S0->S1, S1->S2, S2->S0
    transitions = {S: Sp for _, L, S, R, Sp in entries}
    if len(transitions) == 3:
        # Check for cycle
        v = 0
        cycle = [v]
        for _ in range(3):
            v = transitions.get(v)
            if v is None:
                break
            cycle.append(v)
        if len(cycle) == 4 and cycle[0] == cycle[3]:
            print(f"  *** 3-CYCLE: {cycle[:3]} ***")

# CRITICAL: Do the three entries for each ternary proc have the SAME (L,R)?
print("\n=== Do ternary proc entries share (L,R)? ===")
for q in range(n):
    if ms[q] != 3:
        continue
    entries = [(k, L, S, R, Sp) for k, (p, L, S, R, Sp) in enumerate(table) if p == q]
    lr_pairs = set((L, R) for _, L, S, R, _ in entries)
    print(f"  Ternary proc {q}: {len(entries)} entries, (L,R) pairs: {lr_pairs}")
    if len(lr_pairs) == 1:
        print(f"    *** ALL SAME (L,R) — ternary proc {q} creates a 3-cycle trap! ***")
