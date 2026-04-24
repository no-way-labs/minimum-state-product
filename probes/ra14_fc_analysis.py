#!/usr/bin/env python3
"""
RA14 v9: Fire count analysis.

Key insight: in a valid system, each proc p fires fc[p] times in the good cycle.
For binary proc: fc[p] must be even (returns to 0 after fc[p] steps mod 2).
For ternary proc: fc[p] must be divisible by 3.

For fc=2 (CL=2n): each proc fires exactly 2. Binary OK (2%2=0), ternary needs 3|2 → impossible!
Wait, ternary proc fires 2 times with inc: 0→1→2. That's not a cycle (doesn't return to 0).
So for ternary, fc must be multiple of 3. For fc=2 cycle, ternary procs fire 2 times → NOT possible.

Actually wait: fc=2 with inc: 0→1→2 (fires 2 times, ends at 2, NOT 0). So ternary can't have
fc=2 with inc. With mixed trans: 0→1→0 (inc then dec: fires 2 times, returns to 0). OK!

So the DFS starts from all-zero and must return to all-zero. Let me check what fire counts
are compatible with returning to start.
"""

import sys
from collections import Counter
from itertools import product as iproduct
from math import prod

def enumerate_dfs(ms, n, max_cycles=5000, max_time=30.0):
    import time
    t0 = time.time()
    start = tuple([0]*n)
    results = []
    seen = set()
    max_len = min(4*n, prod(ms))
    def dfs(config, path, word, det):
        if time.time() - t0 > max_time or len(results) >= max_cycles:
            return
        for p in range(n):
            for nv in range(ms[p]):
                if nv == config[p]:
                    continue
                if word:
                    last = word[-1]
                    diff = min(abs(p - last), n - abs(p - last))
                    if diff > 1:
                        continue
                Lv = config[(p-1)%n]
                Sv = config[p]
                Rv = config[(p+1)%n]
                km = (p, Lv, Sv, Rv)
                nd = dict(det)
                if km in nd:
                    if nd[km] != nv:
                        continue
                else:
                    nd[km] = nv
                ok = True
                for i in range(n):
                    if i == p:
                        continue
                    ki = (i, config[(i-1)%n], config[i], config[(i+1)%n])
                    if ki in nd:
                        if nd[ki] != config[i]:
                            ok = False
                            break
                    else:
                        nd[ki] = config[i]
                if not ok:
                    continue
                nc = list(config)
                nc[p] = nv
                nc = tuple(nc)
                nw = word + [p]
                if nc == start and len(path) >= 2*n:
                    fc = Counter(nw)
                    if len(fc) == n:
                        ck = frozenset(path)
                        if ck not in seen:
                            seen.add(ck)
                            results.append((list(path), nw))
                    continue
                if nc not in set(path) and len(path) < max_len:
                    path.append(nc)
                    dfs(nc, path, nw, nd)
                    path.pop()
    dfs(start, [start], [], {})
    return results

# The DFS starts at all-zero and returns to all-zero.
# Each proc fires fc[p] times. The net displacement for proc p must be 0 mod ms[p].
# With general transitions (not just inc), the displacement depends on the specific
# transitions chosen. But the DFS tracks consistency, so the transitions are determined.

# The key question: what fire counts appear in valid good cycles?
# For a good cycle in a valid system starting from config c0:
# - The cycle visits CL distinct configs and returns to c0
# - Each proc fires fc[p] times
# - The fire pattern determines the cycle length CL = sum(fc[p])
# - For the cycle to close: the net state change at each proc must be 0

# For a "minimum" good cycle, we'd expect fc[p] = ms[p] for each p.
# CL = sum(ms[p]) = the total state count.
# But longer cycles with fc[p] = k * ms[p] also close.

# The DFS finds cycles starting from (0,...,0). Let's see what fc patterns appear.

n = 5
ms = [3, 3, 2, 2, 2]
print(f"n={n}, ms={ms}")

cycles = enumerate_dfs(ms, n, max_cycles=3000, max_time=30.0)
print(f"Found {len(cycles)} cycles")

fc_patterns = Counter()
for cyc, w in cycles:
    fc = tuple(Counter(w).get(p, 0) for p in range(n))
    fc_patterns[fc] += 1

# Sort by frequency
print(f"\nFire count patterns (top 30):")
for fc, cnt in fc_patterns.most_common(30):
    # Check if fc[p] is a multiple of ms[p] for each p
    ms_mult = all(fc[p] % ms[p] == 0 for p in range(n))
    min_fc = tuple(ms[p] for p in range(n))
    is_min = fc == min_fc
    print(f"  fc={fc}, CL={sum(fc)}, count={cnt}, ms_mult={ms_mult}, min_fc={is_min}")

# Check: are all fire counts multiples of ms[p]?
all_multiples = all(
    all(fc[p] % ms[p] == 0 for p in range(n))
    for fc in fc_patterns.keys()
)
print(f"\nAll fire counts are multiples of ms[p]: {all_multiples}")

# If NOT all multiples, then the transitions are NOT just inc/dec
# but context-dependent (which is expected for real systems)
non_mult = []
for fc in fc_patterns.keys():
    for p in range(n):
        if fc[p] % ms[p] != 0:
            non_mult.append((fc, p, fc[p], ms[p]))
            break

if non_mult:
    print(f"\nNon-multiple fire counts: {len(non_mult)}")
    for fc, p, fcp, msp in non_mult[:10]:
        print(f"  fc={fc}, proc {p}: fires {fcp} times, ms={msp}, {fcp}%{msp}={fcp%msp}")


# =============================================================================
# KEY QUESTION: do the fc=2n (minimum) cycles always have EC?
# =============================================================================
print()
print("=" * 70)
print("FC ANALYSIS: do minimum fire count cycles have EC?")
print("=" * 70)

from collections import defaultdict

def check_ec(good, word, n):
    L = len(word)
    mt = defaultdict(set)
    nt = defaultdict(set)
    for t in range(L):
        c = good[t]
        m = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == m:
                mt[j].add(triple)
            else:
                nt[j].add(triple)
    for j in range(n):
        if mt[j] & nt[j]:
            return True
    return False

def is_uniform_sweep(word, n):
    L = len(word)
    if L % n != 0:
        return False
    reps = L // n
    doubled = word + word
    for start in range(n):
        for d in [1, -1]:
            sweep = [(start + d * i) % n for i in range(n)]
            full = sweep * reps
            for off in range(L):
                if doubled[off:off+L] == full:
                    return True
    return False

min_fc_target = tuple(ms[p] for p in range(n))  # (3,3,2,2,2), CL=12
print(f"Minimum fire count: {min_fc_target}, CL={sum(min_fc_target)}")

min_fc_cycles = [(cyc, w) for cyc, w in cycles
                 if tuple(Counter(w).get(p, 0) for p in range(n)) == min_fc_target]
print(f"Cycles with minimum fc: {len(min_fc_cycles)}")

for cyc, w in min_fc_cycles:
    ec = check_ec(cyc, w, n)
    sw = is_uniform_sweep(w, n)
    print(f"  CL={len(w)}, sweep={sw}, EC={ec}")

# Also check CL=2n cycles (fc=2 for all procs)
fc2_target = tuple(2 for _ in range(n))
fc2_cycles = [(cyc, w) for cyc, w in cycles
              if tuple(Counter(w).get(p, 0) for p in range(n)) == fc2_target]
print(f"\nCycles with fc=(2,2,2,2,2), CL=10: {len(fc2_cycles)}")
for cyc, w in fc2_cycles:
    ec = check_ec(cyc, w, n)
    sw = is_uniform_sweep(w, n)
    print(f"  CL={len(w)}, sweep={sw}, EC={ec}")

# Check the transition modes used
print(f"\nAll non-sweep non-EC cycles have fc NOT equal to minimum:")
noec_ns = [(cyc, w) for cyc, w in cycles
           if not is_uniform_sweep(w, n) and not check_ec(cyc, w, n)]
print(f"Total non-sweep non-EC: {len(noec_ns)}")
fc_of_noec = Counter(tuple(Counter(w).get(p, 0) for p in range(n)) for _, w in noec_ns)
print(f"Distinct fc patterns in non-EC non-sweep: {len(fc_of_noec)}")
for fc, cnt in fc_of_noec.most_common(10):
    is_min = fc == min_fc_target
    ms_mult = all(fc[p] % ms[p] == 0 for p in range(n))
    print(f"  fc={fc}, CL={sum(fc)}, count={cnt}, ms_mult={ms_mult}, min_fc={is_min}")
