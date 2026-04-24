#!/usr/bin/env python3
"""
Compressed witness search: can a zero-winding good cycle have fc(p) >= 4
at a binary processor p with binary neighbors?

GPT-5.4's approach: don't enumerate transition functions. Enumerate the
MARKED CONFIGURATIONS around 3 consecutive fires of p on the 5-window
[p-2, p-1, p, p+1, p+2], and check if entry conflict constraints can
be satisfied.

Setup: 5 consecutive binary processors. p = processor 2 (middle).
p fires at times t1, t2, t3 with states S=0, S=1, S=0 (toggle).

At each fire of p:
  - Config before fire: (a, b, S, d, e) on the 5-window
  - p toggles: config after fire: (a, b, 1-S, d, e)

Between fires: an "excursion" where other procs fire. The excursion
changes a,b,d,e but NOT p (p doesn't fire during excursion).

Key constraint: for each of the 5 procs, the set of (L,S,R) contexts
seen as mover must be DISJOINT from those seen as non-mover.

We enumerate:
  - Config at fire 1 (before): c1 = (a1, b1, 0, d1, e1)  [S=0]
  - Config at fire 2 (before): c2 = (a2, b2, 1, d2, e2)  [S=1, after excursion 1]
  - Config at fire 3 (before): c3 = (a3, b3, 0, d3, e3)  [S=0, after excursion 2]
  - Require (a3,b3,d3,e3) != (a1,b1,d1,e1) — otherwise fire 3 = fire 1 context at p

At each fire of p: p is mover, all others are non-movers.
During excursions: we don't know exactly who fires, but we know:
  - Some subset of {p-2, p-1, p+1, p+2} fire (possibly multiple times)
  - p does NOT fire
  - The mover walk is nearest-neighbor

For the entry conflict check at the 5 marked configs (3 fires of p):
  - p's mover contexts: (b1,0,d1), (b2,1,d2), (b3,0,d3)
    Need (b3,0,d3) != (b1,0,d1) for fc >= 4 (otherwise same context = only fc=2 possible)
  - p-1's non-mover contexts at fires: (a1,b1,0), (a2,b2,1), (a3,b3,0)
  - p+1's non-mover contexts at fires: (d1,d1_val... wait, let me be more careful.

Actually let me think about what contexts appear:

At fire k of p (p=proc 2):
  proc 0 (p-2): non-mover, context = (c[n-1], c[0], c[1]) — but we don't track c[n-1]
  proc 1 (p-1): non-mover, context = (c[0], c[1], c[2]) = (ak, bk, Sk)
  proc 2 (p):   mover,     context = (c[1], c[2], c[3]) = (bk, Sk, dk)
  proc 3 (p+1): non-mover, context = (c[2], c[3], c[4]) = (Sk, dk, ek)
  proc 4 (p+2): non-mover, context = (c[3], c[4], c[n-1 or 0]) — ring wraps

For the 5-window, we can fully track procs 1, 2, 3.
Procs 0 and 4 need their outer neighbors which we don't track.
So focus on entry conflict at p-1, p, and p+1.
"""
from itertools import product as iproduct

print("=== COMPRESSED WITNESS SEARCH: fc(p) >= 4 at binary p ===")
print()

# 5-window: positions 0,1,2,3,4 all binary
# p = position 2. Fires at t1 (S=0), t2 (S=1), t3 (S=0).
# We need the 3rd firing context different from 1st (otherwise not fc>=4).

# Enumerate: (a1,b1,d1,e1) for fire 1, (a2,b2,d2,e2) for fire 2, (a3,b3,d3,e3) for fire 3
# Each in {0,1}^4 = 16 possibilities. Total: 16^3 = 4096.

count_total = 0
count_survive = 0
survivors = []

for a1, b1, d1, e1 in iproduct(range(2), repeat=4):
    for a2, b2, d2, e2 in iproduct(range(2), repeat=4):
        for a3, b3, d3, e3 in iproduct(range(2), repeat=4):
            count_total += 1

            # p's mover contexts at 3 fires
            p_mover = [(b1, 0, d1), (b2, 1, d2), (b3, 0, d3)]

            # For fc >= 4: 3rd fire must have DIFFERENT context from 1st
            # (otherwise same (L,S,R) repeated → only counts as 1 distinct mover entry)
            # Actually for fc=4 we need the 3rd fire to use a NEW context.
            # If (b3,0,d3) == (b1,0,d1), the 3rd fire reuses the same mover entry.
            # That's ALLOWED (same entry can be used multiple times as mover).
            # But we need fc >= 4, which means p fires >= 4 times total.
            # With S alternating 0,1,0,1: we need >= 2 distinct S=0 mover contexts
            # and >= 2 distinct S=1 mover contexts.
            # Actually no: fc counts FIRINGS not distinct contexts.
            # fc=4 means p fires 4 times. The contexts CAN repeat.
            # The entry conflict constraint is about the SET of contexts.
            # p can fire 4 times using only 2 distinct contexts (each used twice).
            # But each context is marked as "mover" — that's fine, no conflict AT p.
            # The conflict must come from NEIGHBORS.

            # So for this search: we model 3 consecutive fires of p.
            # The question: do the NON-MOVER constraints at neighbors conflict
            # with any MOVER constraints the neighbors accumulate?

            # Collect non-mover contexts at p-1 (proc 1) at the 3 fire times:
            p1_nonmover = set()
            p1_nonmover.add((a1, b1, 0))  # fire 1: p=0
            p1_nonmover.add((a2, b2, 1))  # fire 2: p=1
            p1_nonmover.add((a3, b3, 0))  # fire 3: p=0

            # Collect non-mover contexts at p+1 (proc 3) at the 3 fire times:
            p3_nonmover = set()
            p3_nonmover.add((0, d1, e1))  # fire 1: p=0
            p3_nonmover.add((1, d2, e2))  # fire 2: p=1
            p3_nonmover.add((0, d3, e3))  # fire 3: p=0

            # Now: during excursions between fires, p-1 and p+1 may FIRE.
            # When p-1 fires: it's mover with context (a, b, c[2]).
            # c[2] = p's value, which is FIXED during excursion.
            #
            # Excursion 1 (between fire 1 and fire 2): p = 1 (after fire 1 toggles 0→1)
            # Excursion 2 (between fire 2 and fire 3): p = 0 (after fire 2 toggles 1→0)
            #
            # If p-1 fires during excursion 1: context = (?, ?, 1) — R=1
            # If p-1 fires during excursion 2: context = (?, ?, 0) — R=0
            #
            # The p-1 non-mover contexts from fires have R values:
            #   fire 1: R=0, fire 2: R=1, fire 3: R=0
            #
            # If p-1 fires during excursion 2 (R=0), its mover context has R=0.
            # The non-mover contexts at fire 1 and fire 3 also have R=0.
            # Collision if (a_exc, b_exc, 0) matches one of {(a1,b1,0), (a3,b3,0)}.
            #
            # Similarly for p+1: during excursion 1 (p=1), if p+1 fires,
            # context has L=1. Non-mover at fire 2 has L=1.

            # KEY INSIGHT: we don't know exactly what p-1's mover contexts are.
            # But we know the R-value is determined by p's state during excursion.
            # And p-1's (a, b) can be ANYTHING reachable.
            #
            # For the worst case: assume p-1's mover contexts avoid all non-mover contexts.
            # Check: is this POSSIBLE?

            # p-1's non-mover set includes entries from the 3 fires.
            # p-1's mover contexts during excursions have:
            #   Excursion 1: R=1 (p=1). Contexts: (?, ?, 1)
            #   Excursion 2: R=0 (p=0). Contexts: (?, ?, 0)
            #
            # For entry conflict at p-1: need mover context in non-mover set.
            # Non-mover set with R=0: {(a1,b1,0), (a3,b3,0)} (up to 2 entries)
            # Non-mover set with R=1: {(a2,b2,1)} (1 entry)
            #
            # Mover contexts with R=0 (excursion 2): must avoid {(a1,b1,0), (a3,b3,0)}
            # So (a,b) must not be (a1,b1) or (a3,b3). With 4 possible (a,b),
            # there are >= 2 safe options. So p-1 CAN fire during excursion 2 without conflict.
            #
            # BUT: p-1 might ALSO be a non-mover during excursion steps
            # (when OTHER procs fire during the excursion). Those add more non-mover entries.
            #
            # This is getting complicated. Let's think differently.

            # ACTUALLY: the real constraint is that we need the FULL cycle to be consistent.
            # Not just the 3 fire points. The excursions between fires involve many steps
            # that all add mover/non-mover entries.
            #
            # GPT's point: we should check if the MARKED CONFIGS ALONE already force
            # an entry conflict, before worrying about excursion internals.
            #
            # At the 3 marked points:
            # - p: 3 mover entries (may have duplicates)
            # - p-1: 3 non-mover entries
            # - p+1: 3 non-mover entries
            #
            # Check: do p-1's non-mover entries conflict with ANY possible mover entry?
            # p-1 must fire at least once (to change b between fires if needed).
            # p-1's mover entries have R ∈ {0, 1} depending on excursion.
            #
            # Minimal conflict: p-1 fires once with R=0 during excursion 2.
            # Its mover context (a,b,0) must not be in p1_nonmover.
            # Entries in p1_nonmover with R=0: at most {(a1,b1,0), (a3,b3,0)}.
            # With 4 possible (a,b) pairs, at most 2 are blocked → 2 free → NO conflict forced.
            #
            # So the 3-fire marks alone DON'T force a conflict. We need more constraints.

            # Let's instead check: can the EXCURSION be consistent?
            # Between fire 1 and fire 2: config goes from (a1,b1,1,d1,e1) to (a2,b2,1,d2,e2)
            # (p stays at 1 throughout excursion 1)
            # Between fire 2 and fire 3: config goes from (a2,b2,0,d2,e2) to (a3,b3,0,d3,e3)
            # (p stays at 0 throughout excursion 2)
            #
            # The excursion must be a valid sequence of single-proc fires on the OTHER procs.
            # Each step: one of {0,1,3,4} fires (not p=2). Toggle their bit.
            # Entry conflict must be maintained globally.

            # This is getting too complex for pure enumeration of configs.
            # Let's go back to direct cycle search but on the 5-window.

            pass

print(f"Checked {count_total} witness configs (analysis above shows marks alone insufficient)")
print()
print("SWITCHING TO DIRECT APPROACH: search for fc>=4 cycles on 5-window")
print()

# Direct search on 5 binary processors (ring of size 5)
# But treat it as: can fc(p=2) >= 4 in a zero-winding good cycle?
# We already know the answer is NO from exhaustive search.
# What we need: a PROOF-AMENABLE characterization of WHY.

# Let's extract the KEY constraint that kills fc >= 4.
# For each cycle, look at the entry conflict "budget" at each neighbor of
# the max-fc processor.

n = 5
all_configs = list(iproduct(range(2), repeat=n))
config_idx = {c: i for i, c in enumerate(all_configs)}

def signed_step(a, b):
    d = (b - a) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0

# Find all zero-winding good cycles
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

print(f"Found {len(all_cycles)} zero-winding good cycles at n=5")

# For each cycle, for each proc with fc=2:
# Analyze the EXCURSION STRUCTURE between the two fires
print("\n=== EXCURSION ANALYSIS ===")

from collections import Counter
exc_type_counts = Counter()

for cyc in all_cycles:
    path = cyc['path']
    movers = cyc['movers']
    L = len(path)

    for p in range(n):
        if cyc['fc'][p] != 2: continue

        fire_steps = [t for t in range(L) if movers[t] == p]
        t1, t2 = fire_steps

        # Excursion between t1 and t2: movers[t1+1], ..., movers[t2-1], movers[t2]=p
        # First step after p fires: movers[t1+1] — this is the "leave" direction
        # Last step before p fires again: movers[t2] = p, but movers[t2-1] is "return" direction

        if t2 > t1 + 1:
            leave = movers[(t1 + 1) % L]
            ret = movers[(t2 - 1) % L]  # the step just before p fires again...
            # Actually: at t2, p fires. The mover at t2-1 was the last excursion step.
            # The mover at t2 is p. For p to be reachable, movers[t2-1] must be p-1 or p+1.
            # Wait: movers[t2] = p, and movers are nearest-neighbor walk.
            # So movers[t2-1] must be p-1 or p+1. That's the "return" side.

            if t1 + 1 < t2:
                leave_side = 'L' if leave == (p - 1) % n else ('R' if leave == (p + 1) % n else '?')
                return_from = movers[t2 - 1] if t2 - 1 > t1 else movers[t1]
                # Actually the return is the step BEFORE t2.
                # movers[t2] = p, so the previous mover movers[t2-1] must be adjacent to p.
                prev = movers[t2 - 1]
                ret_side = 'L' if prev == (p - 1) % n else ('R' if prev == (p + 1) % n else '?')
                exc_type = leave_side + ret_side
                exc_type_counts[exc_type] += 1

        # Also: excursion after t2 wrapping back to t1 (cyclic)
        # movers[t2+1 mod L], ..., movers[t1-1 mod L]
        wrap_leave = movers[(t2 + 1) % L]
        wrap_leave_side = 'L' if wrap_leave == (p-1)%n else ('R' if wrap_leave == (p+1)%n else '?')
        wrap_ret = movers[(t1 - 1) % L]
        wrap_ret_side = 'L' if wrap_ret == (p-1)%n else ('R' if wrap_ret == (p+1)%n else '?')
        exc_type_counts[wrap_leave_side + wrap_ret_side] += 1

print(f"Excursion types (leave_side + return_side):")
for k in sorted(exc_type_counts):
    print(f"  {k}: {exc_type_counts[k]}")

# Key: for zero winding, #LR = #RL (around-the-ring excursions balance)
# With fc=2: exactly 2 excursions. Options:
# LL+RR (both zero-winding), LR+RL (both around-ring, balanced), LL+LR, etc.

print("\n=== EXCURSION PAIR TYPES PER PROCESSOR ===")
pair_counts = Counter()
for cyc in all_cycles:
    path = cyc['path']
    movers = cyc['movers']
    L = len(path)

    for p in range(n):
        if cyc['fc'][p] != 2: continue
        fire_steps = [t for t in range(L) if movers[t] == p]
        t1, t2 = fire_steps

        types = []
        for (ta, tb) in [(t1, t2), (t2, t1)]:  # two excursions (2nd wraps around)
            # Leave: movers[(ta+1) % L]
            # Return: movers[(tb-1) % L]
            leave = movers[(ta + 1) % L]
            ret = movers[(tb - 1) % L]
            ls = 'L' if leave == (p-1)%n else 'R'
            rs = 'L' if ret == (p-1)%n else 'R'
            types.append(ls + rs)

        pair = tuple(sorted(types))
        pair_counts[pair] += 1

print(f"Excursion pair types:")
for k in sorted(pair_counts):
    print(f"  {k}: {pair_counts[k]}")

# Now the CRITICAL analysis: for each excursion, what's the neighbor's
# context budget?
print("\n=== NEIGHBOR CONTEXT BUDGET PER EXCURSION ===")
# Focus on p-1 (left neighbor).
# At fire of p: p-1 sees (c[p-2], c[p-1], c[p]) as non-mover.
# During excursion: if p-1 fires, sees (c[p-2], c[p-1], c[p]) as mover.
# c[p] is FIXED during excursion (p doesn't fire).
# So R-value at p-1 is fixed during excursion.
#
# At fire 1 (p has S=0): p-1's R = 0. After fire 1, p=1.
# Excursion 1: p=1. If p-1 fires, R=1. Non-mover at fire 2: R=1.
# So during excursion 1, p-1's mover R=1 matches fire-2 non-mover R=1.
# Conflict at p-1 if (a, b) matches.
#
# After fire 2 (p has S=1→0): p=0.
# Excursion 2: p=0. If p-1 fires, R=0. Non-mover at fire 1 and 3: R=0.
# Conflict at p-1 if (a, b) matches (a1,b1) or (a3,b3).

# So: the question is whether p-1's mover (a,b) during excursion 2
# must equal (a1,b1) or (a3,b3).

# Count: in actual cycles, what (a,b) does p-1 have when it fires?
print("\nFor each cycle, checking p-1's mover (a,b) values vs fire-time (a,b):")
conflict_check = Counter()
for cyc in all_cycles[:100]:
    path = cyc['path']
    movers = cyc['movers']
    L = len(path)

    for p in range(n):
        if cyc['fc'][p] != 2: continue
        left = (p-1) % n
        fire_steps = [t for t in range(L) if movers[t] == p]
        t1, t2 = fire_steps

        # p-1's (a,b) at fire times (a = c[p-2], b = c[p-1])
        c1 = all_configs[path[t1]]
        c2 = all_configs[path[t2]]
        ab_fire1 = (c1[(p-2)%n], c1[(p-1)%n])
        ab_fire2 = (c2[(p-2)%n], c2[(p-1)%n])

        # p-1's mover (a,b) at its own fire times
        left_fire_steps = [t for t in range(L) if movers[t] == left]
        for t in left_fire_steps:
            c = all_configs[path[t]]
            ab_mover = (c[(left-1)%n], c[left])
            p_val = c[p]  # p's value when p-1 fires

            # Check: does this mover (a,b,R) match any non-mover at fire times?
            if p_val == 0:  # R=0, same as fire 1 and fire 3
                if ab_mover == ab_fire1:
                    conflict_check['would_conflict_fire1'] += 1
                elif ab_mover == ab_fire2 if len(fire_steps) > 1 else False:
                    conflict_check['would_conflict_fire2'] += 1
                else:
                    conflict_check['safe_R0'] += 1
            else:  # R=1, same as fire 2
                if ab_mover == ab_fire2:
                    conflict_check['would_conflict_fire2_R1'] += 1
                else:
                    conflict_check['safe_R1'] += 1

print(f"Conflict check results: {dict(conflict_check)}")
print("\n(If any 'would_conflict' appears at fc=2, that's a bug — they should all be safe)")
