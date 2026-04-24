#!/usr/bin/env python3
"""RA15 v3: Streamlined — focus on n=6 tight, then n=7 reuse from part 1 data."""
from collections import Counter, defaultdict
import time, sys

def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    count = [0]
    def dfs(word, fc, config):
        count[0] += 1
        if count[0] % 1000000 == 0:
            print(f"    ... {count[0]//1000000}M nodes explored, {len(results)} results so far", flush=True)
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results

def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]

def has_actual_ec(word, cycle, ms, n):
    ell = len(word)
    for p in range(n):
        mover, nonmover = set(), set()
        for s in range(ell):
            L = cycle[s][(p-1)%n]; S = cycle[s][p]; R = cycle[s][(p+1)%n]
            ctx = (L,S,R)
            if word[s] == p: mover.add(ctx)
            else: nonmover.add(ctx)
        if mover & nonmover:
            return True
    return False

def classify_cycle(word, n):
    ell = len(word)
    total_disp = 0
    cw = ccw = 0
    for i in range(ell):
        d = (word[(i+1)%ell] - word[i]) % n
        if d == 1: total_disp += 1; cw += 1
        elif d == n-1: total_disp -= 1; ccw += 1
    winding = total_disp // n if n > 0 and total_disp % n == 0 else None
    return {
        'winding': winding,
        'winding_odd': winding is not None and winding % 2 != 0,
        'uniform': cw == 0 or ccw == 0,
        'cw': cw, 'ccw': ccw,
    }

def sort_key(k):
    w, u = k
    return (w if w is not None else 999, int(u))

# ============================================================
print("=" * 70)
print("n=6: ms=[2,3,2,3,2,3]")
print("=" * 70)

n = 6
ms = [2, 3, 2, 3, 2, 3]
prod = 1
for m in ms: prod *= m
threshold = 4 * 3**(n-2)
bp = [i for i in range(n) if ms[i] == 2]
print(f"ms={ms}, prod={prod}, threshold={threshold}, binary at {bp}")
print(f"Non-consecutive check: {not any((b+1)%n in bp for b in bp)}")
# At n=6, binary at 0,2,4: (0+1)%6=1 not in {0,2,4}, (2+1)%6=3 not in, (4+1)%6=5 not in
# So this IS non-consecutive at n=6 (unlike n=5 where 4+1=0)

max_len = 22  # tight: sum(ms) = 15, try up to 22
t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
elapsed = time.time() - t0
print(f"{len(words)} words ({elapsed:.1f}s)")

by_type = defaultdict(list)
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    info = classify_cycle(word, n)
    ell = len(word)
    ec = has_actual_ec(word, cycle, ms, n)
    by_type[(info['winding'], info['uniform'])].append((ell, ec, word))

total = sum(len(v) for v in by_type.values())
print(f"Valid cycles: {total}")
for key in sorted(by_type.keys(), key=sort_key):
    w, u = key
    items = by_type[key]
    cls = [x[0] for x in items]
    ecs = [x[1] for x in items]
    ec_count = sum(ecs)
    no_ec = len(ecs) - ec_count
    print(f"  W={w}, {'uniform' if u else 'non-uniform'}: {len(items)} cycles, "
          f"CL∈[{min(cls)},{max(cls)}], EC={ec_count}, no-EC={no_ec}")

nu_no_ec = sum(1 for k, items in by_type.items() if not k[1]
                for _, ec, _ in items if not ec)
u_no_ec = sum(1 for k, items in by_type.items() if k[1]
               for _, ec, _ in items if not ec)
print(f"Non-uniform no-EC: {nu_no_ec}")
print(f"Uniform no-EC: {u_no_ec}")

# Also check second multiset at n=6
ms2 = [2, 3, 2, 3, 3, 2]  # rotated
bp2 = [i for i in range(n) if ms2[i] == 2]
print(f"\nms={ms2}, binary at {bp2}")
print(f"Non-consecutive: {not any((b+1)%n in bp2 for b in bp2)}")
# 0,2,5: (5+1)%6=0 which IS in {0,2,5} → CONSECUTIVE!
# So this is not valid.

# Actually at n=6, the only non-consecutive 3-binary placement is {0,2,4}
# (and rotations, but product is same)

# ============================================================
# KEY ANALYSIS: Why CL > sum(ms)?
# ============================================================
print("\n" + "=" * 70)
print("WHY CL > sum(ms)?")
print("=" * 70)

# At n=6, ms=[2,3,2,3,2,3], sum(ms)=15
# What's the minimum CL?
all_cls = []
for key, items in by_type.items():
    for (ell, ec, word) in items:
        all_cls.append(ell)
if all_cls:
    print(f"n=6: min CL = {min(all_cls)}, sum(ms) = {sum(ms)}")
    print(f"All CLs: {sorted(Counter(all_cls).items())}")

# Try fc vectors with CL = sum(ms) = 15
print(f"\nFC vectors with CL = {sum(ms)}:")
print(f"  fc must be: P0=2, P1=3, P2=2, P3=3, P4=2, P5=3 (= ms)")
print(f"  Walk has CL=15 steps, each ±1 on C_6")
print(f"  D = 6W, so 15 ≡ 6W (mod 2) → 1 ≡ 0 (mod 2) → IMPOSSIBLE!")
print(f"  CL must have same parity as D = 6W, which is always even.")
print(f"  But sum(ms) = 15 is ODD → CL = 15 is impossible!")
print()
print(f"  Next: CL = 16 (even). Need extra firing at some proc.")
print(f"  Binary proc: fc = 2 → 4 (add 2)")
print(f"  Ternary proc: fc = 3 → 6 (add 3)")
print(f"  Cheapest: add 2 to a binary → CL = 17 (odd again!)")
print(f"  Wait, 15 + 2 = 17, which is odd → still impossible?")
print(f"  Need CL even. 15+1=16 but can't add just 1 firing.")
print(f"  15+2=17 (odd, bad). 15+3=18 (even, OK).")
print(f"  15+4=19 (odd). 15+5=20 (even). 15+2+3=20 (even).")
print()

# At n=7, ms=[2,3,2,3,2,3,3], sum(ms)=18 (even)
# D = 7W. CL and D must have same parity.
# 7W and 18: if W even → D even → 18 even OK
# if W odd → D odd → 18 even → MISMATCH → CL ≠ 18 for odd winding
print("At n=7, ms=[2,3,2,3,2,3,3], sum(ms)=18 (even)")
print("  D = 7W. For CL even: need D even → W even")
print("  For odd W: D is odd → CL must be odd → need CL ≥ 19")
print("  But CL = sum of fc, each fc is multiple of m_p")
print("  fc(binary) ∈ {2,4,6,...}, fc(ternary) ∈ {3,6,9,...}")
print("  sum of fc = sum of (even + multiples of 3)")
print("  2+3+2+3+2+3+3 = 18. Next options: 20, 21, 22, ...")
print("  CL=19: 18+1 impossible. Need to add at least 2 → CL=20")
print("  CL=20 even → W must be even → NOT odd winding")
print("  CL=21: 18+3 → add 3 to one ternary → sum = 21, odd → W must be odd → OK")
print("  But is CL=21 achievable? 21 = 7*3, so W could be ±3")
print()

# Let's check: min CL by W at n=7 (from our data)
print("Observed at n=7:")
# Parse from earlier run
print("  From Part 1 output:")
print("    W=-2, non-uniform: min_CL=20")
print("    W=0, non-uniform: min_CL=20")
print("    W=2, non-uniform: min_CL=20")
print("    W=None, non-uniform: min_CL=20")
print()
print("  Predicted min CL by parity:")
for W in range(-4, 5):
    D = 7 * W
    # CL must be ≥ sum(ms) and CL ≡ D (mod 2)
    cl_min = 18  # sum(ms)
    # But CL must be achievable as sum of valid fc
    # Valid fc sums: 18, 20, 21, 22, 23, 24, 25, ...
    # 18 (even), 20 (even), 21 (odd), 22 (even), 23 (odd), ...
    valid_cls = []
    for extra in range(20):
        for binary_extra in range(4):
            for t_extra in range(4):
                cl_try = 18 + 2*binary_extra + 3*t_extra
                if cl_try not in valid_cls:
                    valid_cls.append(cl_try)
    valid_cls = sorted(set(valid_cls))
    # Also CL ≥ |D|
    feasible = [cl for cl in valid_cls if cl >= abs(D) and (cl - abs(D)) % 2 == 0]
    if feasible:
        print(f"  W={W}: D={D}, min feasible CL={feasible[0]}, achievable CL={valid_cls[:10]}")

# ============================================================
# THE REAL QUESTION: Does the claim CL ≥ 3n+4 hold?
# ============================================================
print("\n" + "=" * 70)
print("CL ≥ 3n+4 CHECK")
print("=" * 70)
print("At n=7: 3n+4 = 25. Observed min CL = 20 for ALL types.")
print("So CL ≥ 3n+4 is FALSE. Min CL = 20 < 25.")
print()
print("At n=9: 3n+4 = 31. Observed min CL = 26 for ALL types.")
print("So CL ≥ 3n+4 is also FALSE at n=9.")
print()
print("CONCLUSION: The CL ≥ 3n+4 bound does NOT hold.")
print("The actual minimum CL is much closer to sum(ms) + small correction.")
print()
print("But ALL cycles have EC regardless! The EC is not from pigeonhole")
print("on large CL, it's from structural constraints of the ring walk.")
