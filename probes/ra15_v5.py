#!/usr/bin/env python3
"""RA15 v5: Final check — does EC always occur at ternary too?
And: is the 4-mechanism proof (BinSCC Expl 10) sufficient?"""
from collections import Counter, defaultdict
import time

def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
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

def ec_at_proc(word, cycle, ms, n, p):
    """Check EC at specific proc."""
    ell = len(word)
    mover, nonmover = set(), set()
    for s in range(ell):
        L = cycle[s][(p-1)%n]; S = cycle[s][p]; R = cycle[s][(p+1)%n]
        ctx = (L,S,R)
        if word[s] == p: mover.add(ctx)
        else: nonmover.add(ctx)
    return len(mover & nonmover) > 0

def classify_cycle(word, n):
    ell = len(word)
    total_disp = 0; cw = ccw = 0
    for i in range(ell):
        d = (word[(i+1)%ell] - word[i]) % n
        if d == 1: total_disp += 1; cw += 1
        elif d == n-1: total_disp -= 1; ccw += 1
    winding = total_disp // n if n > 0 and total_disp % n == 0 else None
    return {'winding': winding, 'uniform': cw == 0 or ccw == 0}

# ============================================================
print("=" * 70)
print("FINAL CHECK: EC location + mechanism sufficiency")
print("=" * 70)

n = 7
ms = [2, 3, 2, 3, 2, 3, 3]
bp = [i for i in range(n) if ms[i] == 2]
tp = [i for i in range(n) if ms[i] == 3]

max_len = 26
print(f"Enumerating ms={ms}, max_len={max_len}...")
t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
elapsed = time.time() - t0
print(f"{len(words)} words ({elapsed:.1f}s)")

# For each cycle: check EC at binary-only, ternary-only
binary_only_ec = 0  # EC at some binary but NO ternary
ternary_only_ec = 0  # EC at some ternary but NO binary
both_ec = 0
neither_ec = 0
total = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    total += 1

    ec_b = any(ec_at_proc(word, cycle, ms, n, p) for p in bp)
    ec_t = any(ec_at_proc(word, cycle, ms, n, p) for p in tp)

    if ec_b and ec_t: both_ec += 1
    elif ec_b: binary_only_ec += 1
    elif ec_t: ternary_only_ec += 1
    else: neither_ec += 1

print(f"\nTotal cycles: {total}")
print(f"EC at both binary+ternary: {both_ec}")
print(f"EC at binary only: {binary_only_ec}")
print(f"EC at ternary only: {ternary_only_ec}")
print(f"EC at neither: {neither_ec}")

# ============================================================
# CL minimum analysis with exact fc vectors
# ============================================================
print("\n" + "=" * 70)
print("CL MINIMUM: Exact fc vector analysis")
print("=" * 70)

# Minimum fc vectors and their CLs
fc_to_cl = defaultdict(list)
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    fc = Counter(word)
    fc_vec = tuple(fc.get(p, 0) for p in range(n))
    cl = len(word)
    info = classify_cycle(word, n)
    fc_to_cl[fc_vec].append((cl, info['winding']))

print(f"Distinct fc vectors: {len(fc_to_cl)}")
# Sort by CL
for fc_vec in sorted(fc_to_cl.keys(), key=lambda v: sum(v)):
    cl = sum(fc_vec)
    windings = set(w for _, w in fc_to_cl[fc_vec])
    count = len(fc_to_cl[fc_vec])
    if cl <= 22:
        labels = [f"P{i}({ms[i]})={fc_vec[i]}" for i in range(n)]
        print(f"  CL={cl}, fc={fc_vec}: {count} cycles, W∈{windings}")
        print(f"    {', '.join(labels)}")
        # Parity check
        for W in windings:
            if W is not None:
                D = n * W
                parity_ok = (cl % 2) == (D % 2)
                print(f"    W={W}, D={D}, CL%2={cl%2}, D%2={D%2}, match={parity_ok}")

# ============================================================
# MINIMUM CL DERIVATION
# ============================================================
print("\n" + "=" * 70)
print("MINIMUM CL DERIVATION")
print("=" * 70)

B = len(bp)  # number of binary
T = len(tp)  # number of ternary

print(f"n={n}, B={B} binary, T={T} ternary")
print(f"sum(ms) = 2B + 3T = {2*B + 3*T}")
print()
print("Minimum fc = ms_p for each p (one full value cycle)")
print(f"CL_base = sum(ms) = {2*B + 3*T}")
print()
print("CL must be achievable as sum of multiples:")
print(f"  CL = 2a_0 + 3a_1 + 2a_2 + 3a_3 + 2a_4 + 3a_5 + 3a_6")
print(f"  where a_i ≥ 1 for all i")
print(f"  Minimum: a_i = 1 → CL = {sum(ms)}")
print()
print("Also CL must satisfy parity: CL ≡ nW (mod 2)")
print(f"  n={n} is odd, so nW is odd iff W is odd")
print(f"  sum(ms) = {sum(ms)}, parity = {sum(ms) % 2}")
print()

# For n=7, sum(ms)=18 (even)
# To get CL=18: need D=7W with 18≡7W (mod 2), so 0≡W (mod 2) → W even
# CL=18 works for W=0, ±2
# But we observed min CL=20, not 18. Why?
print("WHY min CL = 20 not 18:")
print("  CL=18 would need fc = ms exactly (2,3,2,3,2,3,3)")
print("  But the walk must be a CONNECTED ring walk:")
print("  consecutive movers must be adjacent on the ring.")
print("  With fc(p) = ms[p], each binary fires 2x, each ternary 3x.")
print()
print("  The walk visits 18 positions. On C_7 ring, this means")
print("  the walk goes around ~2.6 times. But adjacency constraint")
print("  means the walk can't 'skip' positions.")
print()
print("  With non-consecutive binary, binary procs are separated.")
print("  To reach all procs, the walk must traverse ternary gaps.")
print("  This forces extra firings at boundary procs.")
print()

# Check if any CL=18 words exist at all (even invalid cycles)
cl18_words = [w for w in words if len(w) == 18]
print(f"  CL=18 words found: {len(cl18_words)}")
if cl18_words:
    for w in cl18_words[:3]:
        cycle = build_cycle(ms, n, w)
        valid = cycle is not None
        fc = Counter(w)
        print(f"    fc={dict(fc)}, valid cycle={valid}")

# What about CL=19?
cl19_words = [w for w in words if len(w) == 19]
print(f"  CL=19 words found: {len(cl19_words)}")
# CL=19 odd → need D=7W odd → W odd → |D|≥7
# C = (19+7)/2=13, K=6 or C=(19-7)/2=6, K=13
# Very asymmetric walks
if cl19_words:
    for w in cl19_words[:3]:
        cycle = build_cycle(ms, n, w)
        valid = cycle is not None
        fc = Counter(w)
        print(f"    fc={dict(fc)}, valid cycle={valid}")

cl20_words = [w for w in words if len(w) == 20]
cl20_valid = sum(1 for w in cl20_words if build_cycle(ms, n, w) is not None)
print(f"  CL=20 words found: {len(cl20_words)}, valid cycles: {cl20_valid}")
