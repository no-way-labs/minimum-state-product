#!/usr/bin/env python3
"""RA15: Sorry 7 investigation — CL bounds, pigeonhole, cycle-type hypothesis.

Sorry 7: odd-winding + non-consecutive binary + non-uniform direction + isolated firings → EC
Non-consecutive binary requires n ≥ 7 (max independent set of C_n = floor(n/2)).
"""
from collections import Counter, defaultdict
import time

# ============================================================
# Core cycle infrastructure
# ============================================================

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
    displacements = []
    for i in range(ell):
        curr = word[i]; nxt = word[(i+1)%ell]
        d = (nxt - curr) % n
        if d == 1: displacements.append(+1)
        elif d == n-1: displacements.append(-1)
        else: displacements.append(0)
    total_disp = sum(displacements)
    winding = total_disp // n if n > 0 and total_disp % n == 0 else None
    cw = sum(1 for d in displacements if d == 1)
    ccw = sum(1 for d in displacements if d == -1)
    return {
        'total_disp': total_disp, 'winding': winding,
        'winding_odd': winding is not None and winding % 2 != 0,
        'uniform': cw == 0 or ccw == 0,
        'cw': cw, 'ccw': ccw,
    }

def gen_nonconsec_binary_multisets(n, min_binary=3):
    threshold = 4 * 3**(n-2)
    results = []
    for mask in range(1 << n):
        bs = [i for i in range(n) if mask & (1 << i)]
        if len(bs) < min_binary: continue
        if any((b+1)%n in bs for b in bs): continue
        ms = [2 if i in bs else 3 for i in range(n)]
        prod = 1
        for m in ms: prod *= m
        if prod < threshold:
            results.append((ms, prod))
    return results

def sort_key(k):
    w, u = k
    return (w if w is not None else 999, int(u))

# ============================================================
# INDEPENDENT SET ANALYSIS
# ============================================================
print("=" * 70)
print("INDEPENDENT SET CONSTRAINT")
print("=" * 70)
for n in range(5, 12):
    max_indep = n // 2
    threshold = 4 * 3**(n-2)
    multisets = gen_nonconsec_binary_multisets(n)
    print(f"  n={n}: max_indep_set(C_{n})={max_indep}, "
          f"≥3 non-consec binary possible: {max_indep >= 3}, "
          f"threshold={threshold}, multisets={len(multisets)}")

# ============================================================
# n=7 COMPREHENSIVE
# ============================================================
print("\n" + "=" * 70)
print("n=7 COMPREHENSIVE ANALYSIS")
print("=" * 70)

n = 7
multisets = gen_nonconsec_binary_multisets(n)
print(f"Multisets: {len(multisets)}")
for ms, prod in multisets:
    bp = [i for i in range(n) if ms[i] == 2]
    print(f"  ms={ms}, prod={prod}, binary at {bp}")

# Full enumeration for first multiset
ms, prod = multisets[0]
max_len = 26  # 3*7+5
print(f"\nEnumerating ms={ms}, max_len={max_len}...")
t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
elapsed = time.time() - t0
print(f"  {len(words)} raw words ({elapsed:.1f}s)")

by_type = defaultdict(list)
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    info = classify_cycle(word, n)
    ell = len(word)
    ec = has_actual_ec(word, cycle, ms, n)
    by_type[(info['winding'], info['uniform'])].append((ell, ec, word))

total_cycles = sum(len(v) for v in by_type.values())
print(f"  Valid cycles: {total_cycles}")

for key in sorted(by_type.keys(), key=sort_key):
    w, u = key
    items = by_type[key]
    cls = [x[0] for x in items]
    ecs = [x[1] for x in items]
    tag = f"W={w}, {'uniform' if u else 'non-uniform'}"
    ec_count = sum(ecs)
    no_ec = len(ecs) - ec_count
    print(f"  {tag}: {len(items)} cycles, CL∈[{min(cls)},{max(cls)}], EC={ec_count}, no-EC={no_ec}")
    cl_dist = Counter(cls)
    for cl_val in sorted(cl_dist):
        sub = [(e, w2) for (c, e, w2) in items if c == cl_val]
        ec_sub = sum(1 for e, _ in sub if e)
        print(f"    CL={cl_val}: {len(sub)} cycles, EC={ec_sub}/{len(sub)}")

# KEY: non-uniform no-EC?
print(f"\n  === KEY: Non-uniform cycles without EC? ===")
non_unif_no_ec = []
non_unif_total = 0
for key, items in by_type.items():
    if key[1]: continue
    non_unif_total += len(items)
    for (ell, ec, w) in items:
        if not ec:
            non_unif_no_ec.append((ell, w))
print(f"  Non-uniform total: {non_unif_total}, no-EC: {len(non_unif_no_ec)}")
for ell, w in non_unif_no_ec[:10]:
    info = classify_cycle(w, n)
    fc = Counter(w)
    print(f"    CL={ell}, W={info['winding']}, fc={dict(fc)}")

# Uniform no-EC (waterfall type)
print(f"\n  === Uniform cycles without EC (waterfall) ===")
unif_no_ec = []
unif_total = 0
for key, items in by_type.items():
    if not key[1]: continue
    unif_total += len(items)
    for (ell, ec, w) in items:
        if not ec:
            unif_no_ec.append((ell, w, key[0]))
print(f"  Uniform total: {unif_total}, no-EC: {len(unif_no_ec)}")
for ell, w, winding in unif_no_ec[:10]:
    fc = Counter(w)
    print(f"    CL={ell}, W={winding}, fc={dict(fc)}")

# ============================================================
# PIGEONHOLE ANALYSIS at binary procs with ternary neighbors
# ============================================================
print(f"\n  === PIGEONHOLE ANALYSIS ===")
bp = [i for i in range(n) if ms[i] == 2]
# Find binary procs with both neighbors ternary
sandwiched = [b for b in bp if ms[(b-1)%n] == 3 and ms[(b+1)%n] == 3]
print(f"  Binary procs: {bp}")
print(f"  Sandwiched (ternary neighbors): {sandwiched}")

# For each cycle, analyze context coverage at sandwiched binary procs
for word in words[:1000]:  # sample
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    info = classify_cycle(word, n)
    ec = has_actual_ec(word, cycle, ms, n)
    ell = len(word)
    fc = Counter(word)

    if not info['uniform'] and not ec:
        # Interesting case: non-uniform, no EC
        print(f"\n  ANALYZING no-EC non-uniform cycle: CL={ell}, W={info['winding']}")
        for b in sandwiched:
            nm_by_s = {0: set(), 1: set()}
            m_by_s = {0: set(), 1: set()}
            nm_count_by_s = {0: 0, 1: 0}
            m_count_by_s = {0: 0, 1: 0}
            for s_idx in range(ell):
                L = cycle[s_idx][(b-1)%n]
                S = cycle[s_idx][b]
                R = cycle[s_idx][(b+1)%n]
                if word[s_idx] == b:
                    m_by_s[S].add((L,R))
                    m_count_by_s[S] += 1
                else:
                    nm_by_s[S].add((L,R))
                    nm_count_by_s[S] += 1
            print(f"    Proc {b}: fc={fc[b]}, nm_steps={ell-fc[b]}")
            for sv in [0,1]:
                overlap = nm_by_s[sv] & m_by_s[sv]
                print(f"      S={sv}: nm_pairs={len(nm_by_s[sv])}/{nm_count_by_s[sv]} steps, "
                      f"m_pairs={len(m_by_s[sv])}/{m_count_by_s[sv]} steps, "
                      f"overlap={len(overlap)}")

# ============================================================
# FC VECTOR ANALYSIS
# ============================================================
print(f"\n  === FC VECTORS by type ===")
for key in sorted(by_type.keys(), key=sort_key):
    w, u = key
    items = by_type[key]
    tag = f"W={w}, {'uniform' if u else 'non-uniform'}"
    fc_counter = Counter()
    for (ell, ec, word) in items:
        fc = Counter(word)
        fc_vec = tuple(fc.get(p, 0) for p in range(n))
        fc_counter[fc_vec] += 1
    print(f"  {tag}: {len(fc_counter)} distinct fc vectors")
    for fc_vec, cnt in fc_counter.most_common(5):
        fc_labeled = [f"P{i}({ms[i]}):{fc_vec[i]}" for i in range(n)]
        print(f"    fc={fc_vec} x{cnt}: {', '.join(fc_labeled)}")

# ============================================================
# PART 4: THEORETICAL CL ANALYSIS
# ============================================================
print("\n" + "=" * 70)
print("PART 4: Theoretical CL Analysis")
print("=" * 70)

print(f"""
For ms={ms} at n={n}:
  - Binary procs: {bp} (m=2), ternary: {[i for i in range(n) if ms[i]==3]} (m=3)
  - Min fc: binary fires 2, ternary fires 3
  - Min CL = {sum(ms)} = 3*{n}-{len(bp)} = {3*n-len(bp)}
  - 3n+4 = {3*n+4}

Displacement constraint:
  CL = C + K (CW + CCW steps)
  D = C - K = n * W
  CL ≥ n|W| (since C,K ≥ 0)

  For W=1 (odd): CL ≥ n = {n}. But CL ≥ {sum(ms)} anyway (fc constraint).
  So displacement does NOT tighten beyond fc constraint.

  Non-uniform means C > 0 AND K > 0.
  C = (CL + nW)/2, K = (CL - nW)/2
  K > 0 requires CL > nW, i.e., CL ≥ nW + 2 (since CL ≡ nW mod 2)

  For W=1: CL ≥ n + 2 = {n+2}. Still below {sum(ms)}.
  For W=3: CL ≥ 3n + 2 = {3*n+2}. Getting close to {3*n+4}!

  So the CL ≥ 3n+4 claim might come from:
    fc constraint (CL ≥ {sum(ms)}) + extra firings forced by winding.
""")

# Check: for odd-winding non-uniform, what's min CL observed?
for key in sorted(by_type.keys(), key=sort_key):
    w, u = key
    if u: continue  # only non-uniform
    items = by_type[key]
    min_cl = min(x[0] for x in items)
    max_cl = max(x[0] for x in items)
    print(f"  W={w}, non-uniform: min_CL={min_cl}, max_CL={max_cl}, "
          f"sum(ms)={sum(ms)}, n+2={n+2}, 3n+4={3*n+4}")

# ============================================================
# n=9 QUICK CHECK (limited)
# ============================================================
print("\n" + "=" * 70)
print("n=9 QUICK CHECK")
print("=" * 70)

n = 9
multisets9 = gen_nonconsec_binary_multisets(n)
print(f"Multisets: {len(multisets9)}")

if multisets9:
    ms, prod = multisets9[0]
    bp = [i for i in range(n) if ms[i] == 2]
    print(f"Testing ms={ms}, prod={prod}, binary at {bp}")
    max_len = sum(ms) + 4  # tight: just above minimum
    print(f"  sum(ms)={sum(ms)}, max_len={max_len}")
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    elapsed = time.time() - t0
    print(f"  {len(words)} raw words ({elapsed:.1f}s)")

    counts = defaultdict(int)
    ec_counts = defaultdict(int)
    min_cl = defaultdict(lambda: float('inf'))
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None: continue
        info = classify_cycle(word, n)
        ell = len(word)
        ec = has_actual_ec(word, cycle, ms, n)
        key = (info['winding'], info['uniform'])
        counts[key] += 1
        if ec: ec_counts[key] += 1
        min_cl[key] = min(min_cl[key], ell)

    for key in sorted(counts.keys(), key=sort_key):
        w, u = key
        tag = f"W={w}, {'uniform' if u else 'non-uniform'}"
        tot = counts[key]
        ec = ec_counts[key]
        print(f"  {tag}: {tot} cycles, min_CL={min_cl[key]}, EC={ec}/{tot}")
