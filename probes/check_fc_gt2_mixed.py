#!/usr/bin/env python3
"""
Check fc > 2 zero-winding impossibility for mixed binary/ternary rings.

Key insight: don't DFS all paths. Instead, check if the ENTRY CONFLICT CONSTRAINT
alone prevents fc > 2. The constraint is: for each processor p, no (L,S,R) context
appears at both a mover step and a non-mover step.

For the middle binary p with binary neighbors: (L,S,R) ∈ {0,1}³ = 8 contexts.
Split by S: for S=0, M₀ and N₀ partition {0,1}². For S=1, M₁ and N₁ partition.

With fc(p) ≥ 4: p fires ≥ 2 times at S=0. Each uses a distinct (L,R) ∈ M₀.
Between these firings: other processors fire, changing L and R.

The question: can the dynamics create ≥ 2 distinct privileged (L,R) pairs at S=0?

For the entry conflict at p: M₀ and N₀ are disjoint. |M₀| + |N₀| = 4.
So |M₀| ≤ 4 and we need |M₀| ≥ 2 for fc ≥ 4.

This is possible (|M₀| can be 2, 3, or 4). So the constraint at p alone doesn't
prevent fc > 2. But the constraints at ALL processors together might.

Let's check: for each of the 256 possible transition functions at the middle binary,
and for each partition M₀/N₀: can a zero-winding cycle with fc > 2 exist?

Actually: the simplest check is the all-binary one we already did. For mixed: the
key is that the middle binary's LOCAL constraints are the same (binary neighbors).
The ternary processors only affect GLOBAL dynamics.

For a LEAN proof: we might not need to check mixed systems. If the impossibility
holds for the LOCAL binary triple regardless of ternary dynamics: it's sufficient.

Let me verify the all-binary result more carefully and understand WHY fc > 2 fails.
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

# Find ALL valid zero-winding good cycles (not just fc > 2)
print(f"Finding ALL zero-winding good cycles at n={n}, all binary...")

all_cycles = []
for start in range(total):
    stack = [(start, [start], [0]*n, 0, {}, [])]
    while stack:
        ci, path, fc, wind, cons, movs = stack.pop()
        if len(path) > 20: continue
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
                    # Normalize: use lexicographically smallest rotation
                    cycle_key = tuple(sorted(path))
                    all_cycles.append({
                        'len': len(path),
                        'fc': list(new_fc),
                        'max_fc': max(new_fc),
                        'path': path[:5],
                        'movers': (movs + [mover])[:5]
                    })
                continue
            if new_ci in path: continue
            stack.append((new_ci, path+[new_ci], new_fc, new_wind, new_cons, movs+[mover]))

print(f"Found {len(all_cycles)} zero-winding cycles total")

# Analyze fire count distribution
fc_dist = {}
for cyc in all_cycles:
    mfc = cyc['max_fc']
    fc_dist[mfc] = fc_dist.get(mfc, 0) + 1

print(f"\nFire count distribution (max fc at any proc):")
for mfc in sorted(fc_dist):
    print(f"  max_fc={mfc}: {fc_dist[mfc]} cycles")

# Show some examples
print(f"\nSample cycles:")
for cyc in all_cycles[:10]:
    print(f"  len={cyc['len']}, fc={cyc['fc']}, path={cyc['path']}...")

# Check fc > 2 specifically
fc_gt2 = [c for c in all_cycles if c['max_fc'] > 2]
print(f"\nCycles with max_fc > 2: {len(fc_gt2)}")

# Check fc > 2 at BINARY positions 0,1,2 specifically
fc_gt2_binary = [c for c in all_cycles if max(c['fc'][0], c['fc'][1], c['fc'][2]) > 2]
print(f"Cycles with fc > 2 at positions 0,1,2: {len(fc_gt2_binary)}")
