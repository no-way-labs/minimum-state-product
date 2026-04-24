#!/usr/bin/env python3
"""
Investigate WHY fc >= 4 is impossible at the middle binary processor.

For each zero-winding good cycle at n=5 (all binary), look at cycles where
some processor has fc=2. For each such processor p with fc=2:
- At p's 2 firing steps: what contexts do neighbors p-1 and p+1 see (as non-movers)?
- At p's 2 firing steps: what is p's own (L,S,R)?
- How many distinct non-mover contexts does each neighbor accumulate?

Then: simulate what WOULD happen if fc=4. With 4 firings of p:
- p-1 sees 4 non-mover contexts (at p's firing steps)
- p-1 also fires some times (mover contexts)
- If any non-mover context matches a mover context → entry conflict at p-1

Key question: is the 8-context pigeonhole tight enough that fc=4 forces a collision?
"""
from itertools import product as iproduct

n = 5
ms = [2] * n
total = 2 ** n

all_configs = list(iproduct(range(2), repeat=n))
config_idx = {c: i for i, c in enumerate(all_configs)}

def signed_step(a, b):
    d = (b - a) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0

print(f"n={n}, all binary, {total} configs")
print("Finding all zero-winding good cycles...")

all_cycles = []
for start in range(total):
    stack = [(start, [start], [0]*n, 0, {}, [])]
    while stack:
        ci, path, fc, wind, cons, movs = stack.pop()
        if len(path) > 2*n + 4: continue
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
                        'path': list(path),
                        'movers': movs + [mover],
                        'fc': list(new_fc),
                        'max_fc': max(new_fc),
                        'constraints': dict(new_cons)
                    })
                continue
            if new_ci in path: continue
            stack.append((new_ci, path+[new_ci], new_fc, new_wind, new_cons, movs+[mover]))

print(f"Found {len(all_cycles)} zero-winding good cycles")
print(f"Max fc distribution: { {k: sum(1 for c in all_cycles if c['max_fc']==k) for k in sorted(set(c['max_fc'] for c in all_cycles))} }")

# For each cycle, for each processor with fc=2:
# Look at neighbor contexts at firing steps
print("\n" + "="*60)
print("NEIGHBOR CONTEXT ANALYSIS at firing steps")
print("="*60)

for ci, cyc in enumerate(all_cycles[:50]):  # first 50 cycles
    path = cyc['path']
    movers = cyc['movers']
    L_cycle = len(path)

    for p in range(n):
        if cyc['fc'][p] != 2: continue

        # Find steps where p fires
        fire_steps = [t for t in range(L_cycle) if movers[t] == p]
        if len(fire_steps) != 2: continue

        left = (p - 1) % n
        right = (p + 1) % n

        # At each firing step of p: what do left and right see?
        left_nonmover_ctxs = []
        right_nonmover_ctxs = []
        p_mover_ctxs = []

        for t in fire_steps:
            c = all_configs[path[t]]
            # p's mover context
            p_mover_ctxs.append((c[(p-1)%n], c[p], c[(p+1)%n]))
            # left neighbor's non-mover context
            left_nonmover_ctxs.append((c[(left-1)%n], c[left], c[(left+1)%n]))
            # right neighbor's non-mover context
            right_nonmover_ctxs.append((c[(right-1)%n], c[right], c[(right+1)%n]))

        # Also find left's mover contexts (when left fires)
        left_fire_steps = [t for t in range(L_cycle) if movers[t] == left]
        left_mover_ctxs = []
        for t in left_fire_steps:
            c = all_configs[path[t]]
            left_mover_ctxs.append((c[(left-1)%n], c[left], c[(left+1)%n]))

        # Check: do any of left's non-mover contexts (at p's fires) match left's mover contexts?
        left_overlap = set(left_nonmover_ctxs) & set(left_mover_ctxs)

        right_fire_steps = [t for t in range(L_cycle) if movers[t] == right]
        right_mover_ctxs = []
        for t in right_fire_steps:
            c = all_configs[path[t]]
            right_mover_ctxs.append((c[(right-1)%n], c[right], c[(right+1)%n]))

        right_overlap = set(right_nonmover_ctxs) & set(right_mover_ctxs)

        if ci < 10:  # print details for first 10
            print(f"\nCycle {ci}, proc {p} (fc=2):")
            print(f"  p mover ctxs: {p_mover_ctxs}")
            print(f"  left({left}) nonmover@p_fire: {left_nonmover_ctxs}, mover: {left_mover_ctxs}")
            print(f"  right({right}) nonmover@p_fire: {right_nonmover_ctxs}, mover: {right_mover_ctxs}")
            if left_overlap: print(f"  LEFT OVERLAP: {left_overlap}")
            if right_overlap: print(f"  RIGHT OVERLAP: {right_overlap}")

# KEY ANALYSIS: For fc=2, how many unique non-mover contexts do neighbors see?
# If fc=4, they'd see 4. With only 8 possible contexts total and some used as mover...
print("\n" + "="*60)
print("PIGEONHOLE ANALYSIS: neighbor context budget")
print("="*60)

for ci, cyc in enumerate(all_cycles):
    path = cyc['path']
    movers = cyc['movers']
    L_cycle = len(path)

    for p in range(n):
        if cyc['fc'][p] != 2: continue

        left = (p - 1) % n
        right = (p + 1) % n

        # Count: how many distinct mover vs nonmover contexts does each neighbor have?
        left_mover_set = set()
        left_nonmover_set = set()
        right_mover_set = set()
        right_nonmover_set = set()

        for t in range(L_cycle):
            c = all_configs[path[t]]
            m = movers[t]

            lctx = (c[(left-1)%n], c[left], c[(left+1)%n])
            rctx = (c[(right-1)%n], c[right], c[(right+1)%n])

            if m == left:
                left_mover_set.add(lctx)
            else:
                left_nonmover_set.add(lctx)

            if m == right:
                right_mover_set.add(rctx)
            else:
                right_nonmover_set.add(rctx)

        if ci < 5:
            print(f"\nCycle {ci}, proc {p} (fc=2):")
            print(f"  left({left}): |M|={len(left_mover_set)}, |N|={len(left_nonmover_set)}, M={left_mover_set}, N={left_nonmover_set}")
            print(f"  right({right}): |M|={len(right_mover_set)}, |N|={len(right_nonmover_set)}, M={right_mover_set}, N={right_nonmover_set}")

# Summary statistics
print("\n" + "="*60)
print("SUMMARY: neighbor M/N set sizes across all cycles")
print("="*60)
from collections import Counter
left_M_sizes = Counter()
left_N_sizes = Counter()
right_M_sizes = Counter()
right_N_sizes = Counter()
left_free_slots = Counter()  # 8 - |M| - |N| (unused contexts)

for cyc in all_cycles:
    path = cyc['path']
    movers = cyc['movers']
    L_cycle = len(path)

    for p in range(n):
        if cyc['fc'][p] != 2: continue
        left = (p - 1) % n
        right = (p + 1) % n

        left_M = set()
        left_N = set()
        right_M = set()
        right_N = set()

        for t in range(L_cycle):
            c = all_configs[path[t]]
            m = movers[t]
            lctx = (c[(left-1)%n], c[left], c[(left+1)%n])
            rctx = (c[(right-1)%n], c[right], c[(right+1)%n])
            if m == left: left_M.add(lctx)
            else: left_N.add(lctx)
            if m == right: right_M.add(rctx)
            else: right_N.add(rctx)

        left_M_sizes[len(left_M)] += 1
        left_N_sizes[len(left_N)] += 1
        right_M_sizes[len(right_M)] += 1
        right_N_sizes[len(right_N)] += 1
        left_free_slots[8 - len(left_M) - len(left_N)] += 1

print(f"Left neighbor |M|: {dict(sorted(left_M_sizes.items()))}")
print(f"Left neighbor |N|: {dict(sorted(left_N_sizes.items()))}")
print(f"Right neighbor |M|: {dict(sorted(right_M_sizes.items()))}")
print(f"Right neighbor |N|: {dict(sorted(right_N_sizes.items()))}")
print(f"Left free slots (8-|M|-|N|): {dict(sorted(left_free_slots.items()))}")
