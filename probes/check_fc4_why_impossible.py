#!/usr/bin/env python3
"""
Deeper analysis: WHY can't fc=4 happen?

Key observation from the data: p's mover contexts at fc=2 are always
  {(L₁, 0, R₁), (L₂, 1, R₂)} — one with S=0, one with S=1.

For fc=4: p fires 4 times. Since binary toggles: fires at S=0, S=1, S=0, S=1.
So we need 2 contexts with S=0 and 2 with S=1 in M_p.

Question 1: At p's firings, what context does p see? For fc=4 we need:
  Fire 1: (L₁, 0, R₁) → p becomes 1
  Fire 2: (L₂, 1, R₂) → p becomes 0
  Fire 3: (L₃, 0, R₃) → p becomes 1, with (L₃,0,R₃) ≠ (L₁,0,R₁)
  Fire 4: (L₄, 1, R₄) → p becomes 0, with (L₄,1,R₄) ≠ (L₂,1,R₂)

So fc=4 requires at least 2 distinct S=0 mover contexts and 2 distinct S=1 mover contexts.
For all-binary: L,R ∈ {0,1}, so S=0 has 4 contexts: (0,0,0),(0,0,1),(1,0,0),(1,0,1).
2 of 4 must be mover, 2 must be non-mover. This is feasible at p alone.

Question 2: What does the NEIGHBOR see at p's firings?

When p fires (p is mover), all others are non-movers.
At p-1: context is (c[p-2], c[p-1], c[p]). Here c[p] is about to change.
At p+1: context is (c[p], c[p+1], c[p+2]). Here c[p] is about to change.

Crucially: p-1's R component = c[p] = S (the value of p BEFORE firing).
So at fire 1 (S=0): p-1 sees (..., c[p-1], 0) as non-mover.
At fire 3 (S=0): p-1 sees (..., c[p-1], 0) as non-mover.
If c[p-2] and c[p-1] are the same at both times → SAME context at p-1 twice as non-mover.
That's fine (non-mover can repeat). The issue is if it matches a MOVER context.

Let's check: when does p-1 fire? It sees (c[p-2], c[p-1], c[p]) as mover.
"""
from itertools import product as iproduct

n = 5
all_configs = list(iproduct(range(2), repeat=n))
config_idx = {c: i for i, c in enumerate(all_configs)}

def signed_step(a, b):
    d = (b - a) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0

# Find all cycles and analyze mover context structure
print("Finding all zero-winding good cycles at n=5...")

all_cycles = []
for start in range(2**n):
    stack = [(start, [start], [0]*n, 0, {}, [])]
    while stack:
        ci, path, fc, wind, cons, movs = stack.pop()
        if len(path) > 14: continue
        c = all_configs[ci]
        for mover in range(n):
            L = c[(mover-1) % n]; S = c[mover]; R = c[(mover+1) % n]
            key = (mover, L, S, R)
            if key in cons and cons[key] == 'nonmover': continue
            valid = True
            new_cons = dict(cons)
            new_cons[key] = 'mover'
            for p in range(n):
                if p == mover: continue
                kp = (p, c[(p-1)%n], c[p], c[(p+1)%n])
                if kp in new_cons and new_cons[kp] == 'mover':
                    valid = False; break
                new_cons[kp] = 'nonmover'
            if not valid: continue
            new_c = list(c); new_c[mover] = 1-S
            new_ci = config_idx[tuple(new_c)]
            new_fc = list(fc); new_fc[mover] += 1
            new_wind = wind
            if movs: new_wind += signed_step(movs[-1], mover)
            if new_ci == start and len(path) >= 3:
                fw = new_wind + signed_step(mover, movs[0])
                if fw == 0:
                    all_cycles.append({
                        'path': list(path), 'movers': movs + [mover],
                        'fc': list(new_fc), 'cons': dict(new_cons)
                    })
                continue
            if new_ci in path: continue
            stack.append((new_ci, path+[new_ci], new_fc, new_wind, new_cons, movs+[mover]))

print(f"Found {len(all_cycles)} cycles")

# For each cycle and each proc p with fc=2:
# What SPECIFIC contexts does p use as mover?
# And what's the structure of neighbor contexts at p's firing times?
print("\n=== P's MOVER CONTEXT PAIRS (fc=2) ===")
from collections import Counter
mover_pair_types = Counter()

for cyc in all_cycles:
    for p in range(n):
        if cyc['fc'][p] != 2: continue
        path = cyc['path']
        movers = cyc['movers']
        fire_steps = [t for t in range(len(path)) if movers[t] == p]

        ctxs = []
        for t in fire_steps:
            c = all_configs[path[t]]
            ctxs.append((c[(p-1)%n], c[p], c[(p+1)%n]))

        # Classify: do the two contexts share L? Share R?
        L_same = ctxs[0][0] == ctxs[1][0]
        R_same = ctxs[0][2] == ctxs[1][2]
        pair_type = f"L_{'same' if L_same else 'diff'}_R_{'same' if R_same else 'diff'}"
        mover_pair_types[pair_type] += 1

print(f"Mover context pair types: {dict(mover_pair_types)}")

# Key question: for fc=4 to work, we'd need the 3rd firing context at S=0
# to differ from the 1st. What CHANGES between fire 1 and fire 3?
# Only the values of OTHER processors. But p's neighbors are binary too.
# Between fire 1 and fire 3: p fires twice (going 0→1→0).
# The excursion between fire 1 and fire 3 involves all movers between them.
# For the 3rd firing's context (L₃, 0, R₃) ≠ (L₁, 0, R₁),
# we need L₃ ≠ L₁ or R₃ ≠ R₁.

# But here's the thing: p-1's value (= L for p) changes only when p-1 fires.
# Similarly p+1's value (= R for p) changes only when p+1 fires.

# So for L to change between fire 1 and fire 3 of p: p-1 must fire an ODD
# number of times between them (since binary toggle).

# Similarly R changes iff p+1 fires odd times.

# Let's check: in actual fc=2 cycles, how many times do neighbors fire
# between the two firings of p?

print("\n=== NEIGHBOR FIRINGS BETWEEN P's FIRINGS ===")
between_left_fc = Counter()
between_right_fc = Counter()

for cyc in all_cycles:
    for p in range(n):
        if cyc['fc'][p] != 2: continue
        path = cyc['path']
        movers = cyc['movers']
        L_cycle = len(path)
        fire_steps = [t for t in range(L_cycle) if movers[t] == p]
        t1, t2 = fire_steps

        left = (p-1) % n
        right = (p+1) % n

        # Between t1 and t2 (exclusive)
        left_between = sum(1 for t in range(t1+1, t2) if movers[t] == left)
        right_between = sum(1 for t in range(t1+1, t2) if movers[t] == right)
        between_left_fc[left_between] += 1
        between_right_fc[right_between] += 1

print(f"Left neighbor fires between p's fires: {dict(sorted(between_left_fc.items()))}")
print(f"Right neighbor fires between p's fires: {dict(sorted(between_right_fc.items()))}")

# CRITICAL: For fc=4, between fire 1 and fire 3 (two excursions),
# each neighbor fires some number of times. For L₃ ≠ L₁:
# left neighbor must fire odd total times across those two excursions.
# Let's see if this creates an entry conflict at p-1 or p+1.

print("\n=== ENTRY CONFLICT ANALYSIS FOR HYPOTHETICAL fc=4 ===")
print("If p fires 4 times: S=0,1,0,1 at fires 1,2,3,4")
print("At fire 1 (S=0): p-1 sees R=0 as nonmover")
print("At fire 3 (S=0): p-1 sees R=0 as nonmover")
print("Between fires 1&3: p toggles 0→1→0, so p-1's R goes 0→1→0")
print("")
print("KEY: at fire 1, p-1 sees (c[p-2], c[p-1], 0)")
print("     at fire 3, p-1 sees (c'[p-2], c'[p-1], 0)")
print("If c[p-2]=c'[p-2] and c[p-1]=c'[p-1]: SAME nonmover context twice.")
print("That's fine. But when does p-1 FIRE (mover context)?")
print("")
print("If p-1 fires between fires 1 and 2 of p (while p=1):")
print("  p-1 sees (c[p-2], c[p-1], 1) as mover")
print("If p-1 fires between fires 2 and 3 of p (while p=0):")
print("  p-1 sees (c''[p-2], c''[p-1], 0) as mover")
print("  This (_, _, 0) mover context could collide with the (_, _, 0) nonmover from fire 1 or 3!")
print("")
print("THAT'S THE MECHANISM: p-1 has nonmover contexts with R=0 at p's S=0 firings,")
print("and if p-1 fires while p=0 (between fires 2→3 or after 4), the mover context")
print("also has R=0. If L,S match → entry conflict at p-1!")

# Let's verify: in ALL cycles, what R does p-1 see in its mover vs nonmover entries?
print("\n=== P-1's R-VALUE IN MOVER vs NONMOVER CONTEXTS ===")
r_analysis = Counter()

for cyc in all_cycles:
    for p in range(n):
        if cyc['fc'][p] != 2: continue
        left = (p-1) % n

        # Collect p-1's mover and nonmover R values
        mover_R = set()
        nonmover_R = set()
        for key, role in cyc['cons'].items():
            if key[0] == left:  # this constraint is about p-1
                _, L, S, R = key
                if role == 'mover':
                    mover_R.add(R)
                else:
                    nonmover_R.add(R)

        overlap_R = mover_R & nonmover_R
        r_analysis[f"mR={sorted(mover_R)}_nR={sorted(nonmover_R)}_overlap={sorted(overlap_R)}"] += 1

for k, v in sorted(r_analysis.items()):
    print(f"  {k}: {v}")
