#!/usr/bin/env python3
"""
Mine the killed fc>=3 traces for boundary interface structure.

For each cycle killed by entry conflict at the ternary boundary:
- What specific (L,S,R) context conflicts?
- At which steps does the conflicting context appear as mover vs nonmover?
- What is the boundary proc doing at those steps?
- Is the conflicting context always the same pattern?

Goal: find the ABSTRACT mechanism that kills these cycles, independent
of boundary modulus.
"""
from itertools import product as iproduct
import time

n = 5
ms = [3, 2, 2, 2, 3]
middle = 2

all_configs = list(iproduct(*(range(m) for m in ms)))
cidx = {c: i for i, c in enumerate(all_configs)}
total = len(all_configs)

binary_procs = [1, 2, 3]

def signed_step(a, b):
    d = (b - a) % n
    if d == 1: return 1
    elif d == n - 1: return -1
    return 0

def ctx_idx_bin(p, c):
    L = c[(p-1)%n]; S = c[p]; R = c[(p+1)%n]
    return L * 2 * ms[(p+1)%n] + S * ms[(p+1)%n] + R

print(f"n={n}, ms={ms}, {total} configs")
print("Finding fc>=3 cycles and analyzing boundary conflicts...")

t0 = time.time()
found_cycles = []

for start in range(total):
    init_mm = {p: 0 for p in binary_procs}
    init_nm = {p: 0 for p in binary_procs}

    stack = [(start, [start], [0]*n, 0, dict(init_mm), dict(init_nm), [])]

    while stack:
        ci, path, fc, wind, mm, nm, movs = stack.pop()
        if len(path) > 18: continue
        c = all_configs[ci]
        for mover in range(n):
            S = c[mover]
            possible_vals = [v for v in range(ms[mover]) if v != S]
            for new_val in possible_vals:
                valid = True
                new_mm = dict(mm)
                new_nm = dict(nm)
                if mover in binary_procs:
                    ci_m = ctx_idx_bin(mover, c)
                    if nm[mover] & (1 << ci_m): continue
                    new_mm[mover] = mm[mover] | (1 << ci_m)
                for p in binary_procs:
                    if p == mover: continue
                    ci_p = ctx_idx_bin(p, c)
                    if mm[p] & (1 << ci_p):
                        valid = False; break
                    new_nm[p] = nm[p] | (1 << ci_p)
                if not valid: continue
                new_c = list(c); new_c[mover] = new_val
                new_ci = cidx[tuple(new_c)]
                new_fc = list(fc); new_fc[mover] += 1
                new_wind = wind
                if movs: new_wind += signed_step(movs[-1], mover)
                if new_ci == start and len(path) >= 3:
                    fw = new_wind + signed_step(mover, movs[0])
                    if fw == 0 and new_fc[middle] >= 3:
                        found_cycles.append({
                            'path': list(path),
                            'movers': movs + [mover],
                            'fc': list(new_fc)
                        })
                        if len(found_cycles) >= 200: break
                    continue
                if new_ci in path: continue
                remaining = 18 - len(path)
                if new_fc[middle] + remaining < 3: continue
                stack.append((new_ci, path+[new_ci], new_fc, new_wind,
                              new_mm, new_nm, movs+[mover]))
            if len(found_cycles) >= 200: break
        if len(found_cycles) >= 200: break
    if len(found_cycles) >= 200: break

elapsed = time.time() - t0
print(f"Found {len(found_cycles)} cycles in {elapsed:.1f}s\n")

# Analyze each cycle's boundary conflict
from collections import Counter

conflict_procs = Counter()
conflict_contexts = Counter()
conflict_details = []

for idx, cyc in enumerate(found_cycles):
    path = cyc['path']
    movers = cyc['movers']
    L = len(path)

    mover_ctxs = {p: {} for p in range(n)}  # ctx -> list of steps
    nonmover_ctxs = {p: {} for p in range(n)}

    first_conflict = None
    for t in range(L):
        c = all_configs[path[t]]
        m = movers[t]
        for p in range(n):
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if p == m:
                if ctx in nonmover_ctxs[p]:
                    if first_conflict is None:
                        first_conflict = (p, ctx, t, nonmover_ctxs[p][ctx])
                mover_ctxs[p].setdefault(ctx, []).append(t)
            else:
                if ctx in mover_ctxs[p]:
                    if first_conflict is None:
                        first_conflict = (p, ctx, t, mover_ctxs[p][ctx])
                nonmover_ctxs[p].setdefault(ctx, []).append(t)

    if first_conflict:
        cp, cctx, ct, csteps = first_conflict
        conflict_procs[cp] += 1
        conflict_contexts[(cp, cctx)] += 1
        conflict_details.append({
            'proc': cp, 'ctx': cctx, 'step': ct, 'prev_steps': csteps,
            'fc': cyc['fc'], 'movers': cyc['movers'], 'cycle_len': L
        })

print("=== CONFLICT LOCATION ===")
for p in sorted(conflict_procs):
    print(f"  Proc {p} (m={ms[p]}): {conflict_procs[p]} conflicts")

print("\n=== CONFLICTING CONTEXTS ===")
for (p, ctx) in sorted(conflict_contexts):
    print(f"  Proc {p}, ctx={ctx}: {conflict_contexts[(p, ctx)]} times")

print("\n=== CONFLICT DETAIL (first 10) ===")
for i, d in enumerate(conflict_details[:10]):
    print(f"\nCycle {i}:")
    print(f"  Conflict at proc {d['proc']}, ctx={d['ctx']}")
    print(f"  fc={d['fc']}, cycle_len={d['cycle_len']}")
    print(f"  Conflicting step: {d['step']}, previously seen at steps: {d['prev_steps']}")
    # Show what's happening at the conflicting steps
    cyc = found_cycles[i]
    path = cyc['path']
    movers = cyc['movers']
    p = d['proc']
    for t in d['prev_steps'] + [d['step']]:
        c = all_configs[path[t]]
        ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
        role = 'MOVER' if movers[t] == p else 'nonmover'
        print(f"    step {t}: config={c}, proc {p} ctx={ctx}, role={role}, mover=proc {movers[t]}")

# KEY: analyze the ABSTRACT structure of the boundary conflict
print("\n=== ABSTRACT BOUNDARY ANALYSIS ===")
# For proc 0 (ternary, ms=3): context is (c[4], c[0], c[1])
# c[4] is ternary (0,1,2), c[0] is ternary (0,1,2), c[1] is binary (0,1)
# So contexts are (L, S, R) where L ∈ {0,1,2}, S ∈ {0,1,2}, R ∈ {0,1}
# = 18 possible contexts

# When does proc 0 fire (mover) vs not fire (nonmover)?
# proc 0 fires when: some excursion reaches proc 0.
# proc 0 is nonmover when: any other proc fires.

# The conflict is: same (L,S,R) at proc 0 as both mover and nonmover.
# L = c[4] (ternary), S = c[0] (ternary), R = c[1] (binary)

# KEY QUESTION: does the conflict depend on the SPECIFIC ternary value,
# or only on some abstract property (e.g., S=0 vs S≠0)?

print("\nConflicting S values at boundary proc:")
s_values = Counter()
for d in conflict_details:
    if d['proc'] in [0, 4]:
        s_val = d['ctx'][1]  # S component
        s_values[s_val] += 1
print(f"  S values: {dict(s_values)}")

print("\nConflicting L values at boundary proc:")
l_values = Counter()
for d in conflict_details:
    if d['proc'] in [0, 4]:
        l_val = d['ctx'][0]  # L component
        l_values[l_val] += 1
print(f"  L values: {dict(l_values)}")

print("\nConflicting R values at boundary proc:")
r_values = Counter()
for d in conflict_details:
    if d['proc'] in [0, 4]:
        r_val = d['ctx'][2]  # R component
        r_values[r_val] += 1
print(f"  R values: {dict(r_values)}")

# Check: at the conflict step, what is the mover?
print("\n=== WHO IS MOVER AT CONFLICT STEP? ===")
conflict_movers = Counter()
for d in conflict_details:
    p = d['proc']
    cyc = found_cycles[conflict_details.index(d)]
    mover_at_conflict = cyc['movers'][d['step']]
    conflict_movers[(p, mover_at_conflict)] += 1
    # Was the conflict because proc p was mover or nonmover at the conflict step?
    role = 'MOVER' if mover_at_conflict == p else 'NONMOVER'
    if d == conflict_details[0]:
        print(f"  Example: proc {p} was {role} at conflict step {d['step']}")

for (p, m) in sorted(conflict_movers):
    role = 'MOVER' if m == p else f'NONMOVER(mover={m})'
    print(f"  Proc {p} at conflict: {role}: {conflict_movers[(p,m)]}")

# What role was it in the FIRST occurrence?
print("\n=== ROLE PATTERN (first vs conflict occurrence) ===")
role_patterns = Counter()
for d in conflict_details:
    p = d['proc']
    cyc_idx = conflict_details.index(d)
    cyc = found_cycles[cyc_idx]
    # First occurrence
    first_t = d['prev_steps'][0]
    first_role = 'M' if cyc['movers'][first_t] == p else 'N'
    # Conflict occurrence
    conf_role = 'M' if cyc['movers'][d['step']] == p else 'N'
    role_patterns[f"first={first_role},conflict={conf_role}"] += 1

for k in sorted(role_patterns):
    print(f"  {k}: {role_patterns[k]}")
