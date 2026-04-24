#!/usr/bin/env python3
"""RA15 Part 2: Deeper analysis — n=6, pigeonhole detail, CL bound mechanism."""
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

def sort_key(k):
    w, u = k
    return (w if w is not None else 999, int(u))

# ============================================================
# n=6 CHECK
# ============================================================
print("=" * 70)
print("n=6 ANALYSIS")
print("=" * 70)

n = 6
threshold = 4 * 3**(n-2)
multisets = []
for mask in range(1 << n):
    bs = [i for i in range(n) if mask & (1 << i)]
    if len(bs) < 3: continue
    if any((b+1)%n in bs for b in bs): continue
    ms = [2 if i in bs else 3 for i in range(n)]
    prod = 1
    for m in ms: prod *= m
    if prod < threshold:
        multisets.append((ms, prod))

print(f"Threshold: {threshold}, multisets: {len(multisets)}")
for ms, prod in multisets:
    bp = [i for i in range(n) if ms[i] == 2]
    print(f"  ms={ms}, prod={prod}, binary at {bp}")

for ms, prod in multisets:
    max_len = 28
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_len)
    elapsed = time.time() - t0
    print(f"\nms={ms}, {len(words)} words ({elapsed:.1f}s)")

    by_type = defaultdict(list)
    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None: continue
        info = classify_cycle(word, n)
        ell = len(word)
        ec = has_actual_ec(word, cycle, ms, n)
        by_type[(info['winding'], info['uniform'])].append((ell, ec, word))

    total = sum(len(v) for v in by_type.values())
    print(f"  Valid cycles: {total}")
    for key in sorted(by_type.keys(), key=sort_key):
        w, u = key
        items = by_type[key]
        cls = [x[0] for x in items]
        ecs = [x[1] for x in items]
        tag = f"W={w}, {'uniform' if u else 'non-uniform'}"
        ec_count = sum(ecs)
        no_ec = len(ecs) - ec_count
        print(f"  {tag}: {len(items)} cycles, CL∈[{min(cls)},{max(cls)}], "
              f"EC={ec_count}, no-EC={no_ec}")

    # Non-uniform without EC?
    nu_no_ec = sum(1 for key, items in by_type.items() if not key[1]
                    for _, ec, _ in items if not ec)
    print(f"  Non-uniform no-EC: {nu_no_ec}")
    # Uniform without EC?
    u_no_ec = sum(1 for key, items in by_type.items() if key[1]
                   for _, ec, _ in items if not ec)
    print(f"  Uniform no-EC: {u_no_ec}")

# ============================================================
# DEEP PIGEONHOLE AT n=7
# ============================================================
print("\n" + "=" * 70)
print("PIGEONHOLE DEEP ANALYSIS at n=7")
print("=" * 70)

n = 7
ms = [2, 3, 2, 3, 2, 3, 3]
bp = [0, 2, 4]
sandwiched = [b for b in bp if ms[(b-1)%n] == 3 and ms[(b+1)%n] == 3]

max_len = 26
t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
elapsed = time.time() - t0
print(f"ms={ms}, {len(words)} words ({elapsed:.1f}s)")

# For every cycle, check context coverage at sandwiched binary procs
# Specifically: what fraction of (L,R) pairs are covered as non-mover for each S?
coverage_data = []

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    ell = len(word)
    fc = Counter(word)

    for b in sandwiched:
        nm_by_s = {0: set(), 1: set()}
        m_by_s = {0: set(), 1: set()}
        nm_steps_by_s = {0: 0, 1: 0}
        m_steps_by_s = {0: 0, 1: 0}
        for s_idx in range(ell):
            L = cycle[s_idx][(b-1)%n]
            S = cycle[s_idx][b]
            R = cycle[s_idx][(b+1)%n]
            if word[s_idx] == b:
                m_by_s[S].add((L,R))
                m_steps_by_s[S] += 1
            else:
                nm_by_s[S].add((L,R))
                nm_steps_by_s[S] += 1

        # Check: does full coverage at some S guarantee EC?
        for sv in [0, 1]:
            coverage_data.append({
                'ell': ell, 'b': b, 'sv': sv,
                'nm_pairs': len(nm_by_s[sv]),
                'nm_steps': nm_steps_by_s[sv],
                'm_pairs': len(m_by_s[sv]),
                'm_steps': m_steps_by_s[sv],
                'overlap': len(nm_by_s[sv] & m_by_s[sv]),
                'fc_b': fc[b],
            })

# Analyze: when nm_pairs = 9 (full coverage), is overlap always > 0?
full_cov = [d for d in coverage_data if d['nm_pairs'] == 9]
full_cov_ec = [d for d in full_cov if d['overlap'] > 0]
print(f"\nFull (L,R) coverage (9/9 nm pairs):")
print(f"  Total: {len(full_cov)}, with EC: {len(full_cov_ec)}")
print(f"  EC rate: {len(full_cov_ec)/len(full_cov)*100:.1f}%" if full_cov else "  (none)")

# When nm_pairs = 9: does the mover necessarily hit some covered pair?
full_cov_no_ec = [d for d in full_cov if d['overlap'] == 0]
if full_cov_no_ec:
    print(f"  SURPRISE: {len(full_cov_no_ec)} cases with full nm coverage but no EC")
    for d in full_cov_no_ec[:5]:
        print(f"    b={d['b']}, S={d['sv']}, m_pairs={d['m_pairs']}, m_steps={d['m_steps']}")
else:
    print(f"  CONFIRMED: full nm (L,R) coverage ALWAYS implies EC")

# What's the distribution of nm_pairs?
nm_pair_dist = Counter(d['nm_pairs'] for d in coverage_data)
print(f"\nNon-mover (L,R) pair count distribution:")
for k in sorted(nm_pair_dist):
    sub = [d for d in coverage_data if d['nm_pairs'] == k]
    ec_sub = sum(1 for d in sub if d['overlap'] > 0)
    print(f"  {k}/9 pairs: {nm_pair_dist[k]} cases, EC={ec_sub}/{nm_pair_dist[k]}")

# What about by mover pair count?
m_pair_dist = Counter(d['m_pairs'] for d in coverage_data)
print(f"\nMover (L,R) pair count distribution:")
for k in sorted(m_pair_dist):
    sub = [d for d in coverage_data if d['m_pairs'] == k]
    ec_sub = sum(1 for d in sub if d['overlap'] > 0)
    print(f"  {k}/9 pairs: {m_pair_dist[k]} cases, EC={ec_sub}/{m_pair_dist[k]}")

# Pigeonhole threshold: what's the minimum nm_steps for guaranteed EC?
# If nm_steps ≥ T and m_steps ≥ 1 for some S, do we always get EC?
print(f"\nPigeonhole threshold analysis:")
for threshold_nm in range(5, 25):
    above = [d for d in coverage_data if d['nm_steps'] >= threshold_nm and d['m_steps'] >= 1]
    if not above: continue
    ec_above = sum(1 for d in above if d['overlap'] > 0)
    print(f"  nm_steps ≥ {threshold_nm} AND m_steps ≥ 1: {len(above)} cases, EC={ec_above}/{len(above)}")

# Combined: for each cycle, what's the max nm_steps across all (b, S)?
print(f"\nPer-cycle max nm_steps analysis:")
cycle_nm_max = defaultdict(int)
cycle_ec = {}
word_idx = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    ell = len(word)
    ec = has_actual_ec(word, cycle, ms, n)
    cycle_ec[word_idx] = ec

    for b in sandwiched:
        for sv in [0, 1]:
            nm_s = sum(1 for s_idx in range(ell)
                       if word[s_idx] != b and cycle[s_idx][b] == sv)
            cycle_nm_max[word_idx] = max(cycle_nm_max[word_idx], nm_s)
    word_idx += 1

# What's the min max_nm_steps for cycles without EC?
no_ec_nm_max = [cycle_nm_max[i] for i, ec in cycle_ec.items() if not ec]
if no_ec_nm_max:
    print(f"  Cycles without EC: min(max_nm_steps)={min(no_ec_nm_max)}, max={max(no_ec_nm_max)}")
else:
    print(f"  ALL cycles have EC (no-EC count: 0)")

# ============================================================
# CL LOWER BOUND: Why is min CL = 20 at n=7?
# ============================================================
print("\n" + "=" * 70)
print("CL LOWER BOUND MECHANISM at n=7")
print("=" * 70)

# At n=7, ms=[2,3,2,3,2,3,3], min fc = 2+3+2+3+2+3+3 = 18
# But observed min CL = 20. Why?
# Answer: the walk must return to start, so displacement D = n*W must be achievable
# with CL steps of ±1. CL = C + K, D = C - K = 7W.
# Also: CL = sum(fc[p]) and fc[p] must be multiple of ms[p].

print(f"ms={ms}, sum(ms)={sum(ms)}")
print(f"Binary fire counts must be even (multiple of 2)")
print(f"Ternary fire counts must be multiple of 3")
print()

# Enumerate possible fc vectors with CL close to 18
print("Possible fc vectors with small CL:")
for extra_b0 in range(4):
    for extra_b2 in range(4):
        for extra_b4 in range(4):
            for extra_t1 in range(3):
                for extra_t3 in range(3):
                    for extra_t5 in range(3):
                        for extra_t6 in range(3):
                            fcs = [
                                2 + 2*extra_b0,  # P0 (binary)
                                3 + 3*extra_t1,  # P1 (ternary)
                                2 + 2*extra_b2,  # P2 (binary)
                                3 + 3*extra_t3,  # P3 (ternary)
                                2 + 2*extra_b4,  # P4 (binary)
                                3 + 3*extra_t5,  # P5 (ternary)
                                3 + 3*extra_t6,  # P6 (ternary)
                            ]
                            cl = sum(fcs)
                            if cl > 22: continue
                            # Check: can this fc vector form a valid ring walk?
                            # Total displacement D must be multiple of n=7
                            # D = C - K where C + K = CL
                            # Also: the walk must be connected (adjacent movers)
                            # Parity: D and CL have same parity (D = C-K, CL = C+K)
                            # So CL ≡ D (mod 2), and D = 7W
                            for W in range(-3, 4):
                                D = 7 * W
                                if abs(D) > cl: continue
                                if (cl + D) % 2 != 0: continue
                                C = (cl + D) // 2
                                K = (cl - D) // 2
                                if C < 0 or K < 0: continue
                                print(f"  fc={fcs}, CL={cl}, W={W}, C={C}, K={K}")

print("\n--- Does CL=18 with W=0 work? ---")
print("  fc=[2,3,2,3,2,3,3], CL=18, W=0, C=9, K=9")
print("  Each binary fires 2 times, each ternary fires 3 times")
print("  The walk has 9 CW and 9 CCW steps")
print("  But can we build a valid cycle? The walk must visit")
print("  all configs distinctly. Product = 648, cycle len = 18.")
print("  Let's check if any CL=18 cycle exists...")

# Try to find CL=18 cycles
small_words = [w for w in words if len(w) == 18]
print(f"  CL=18 words found: {len(small_words)}")
for w in small_words[:5]:
    cycle = build_cycle(ms, n, w)
    if cycle is not None:
        info = classify_cycle(w, n)
        fc = Counter(w)
        print(f"    VALID: fc={dict(fc)}, W={info['winding']}, uniform={info['uniform']}")
    else:
        print(f"    INVALID (config collision)")

# Try CL=19
w19 = [w for w in words if len(w) == 19]
print(f"\n  CL=19 words found: {len(w19)}")

# Try CL=20
w20 = [w for w in words if len(w) == 20]
valid20 = 0
for w in w20:
    if build_cycle(ms, n, w) is not None:
        valid20 += 1
print(f"  CL=20 words found: {len(w20)}, valid cycles: {valid20}")
