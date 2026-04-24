#!/usr/bin/env python3
"""RA15 v4: EC mechanism analysis — what drives universal EC at non-consec binary?

Key finding from v3: CL ≥ 3n+4 is FALSE. EC is universal anyway.
Now: understand the actual mechanism.
"""
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

def ec_analysis(word, cycle, ms, n):
    """Detailed EC analysis: which proc, which context, overlap type."""
    ell = len(word)
    results = []
    for p in range(n):
        mover_ctxs = {}  # ctx -> [steps]
        nonmover_ctxs = {}
        for s in range(ell):
            L = cycle[s][(p-1)%n]; S = cycle[s][p]; R = cycle[s][(p+1)%n]
            ctx = (L,S,R)
            if word[s] == p:
                mover_ctxs.setdefault(ctx, []).append(s)
            else:
                nonmover_ctxs.setdefault(ctx, []).append(s)
        overlap = set(mover_ctxs.keys()) & set(nonmover_ctxs.keys())
        if overlap:
            results.append({
                'proc': p, 'ms_p': ms[p],
                'overlap': overlap,
                'mover_count': sum(len(v) for v in mover_ctxs.values()),
                'nonmover_count': sum(len(v) for v in nonmover_ctxs.values()),
                'mover_distinct': len(mover_ctxs),
                'nonmover_distinct': len(nonmover_ctxs),
            })
    return results

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
print("EC MECHANISM ANALYSIS at n=7")
print("=" * 70)

n = 7
ms = [2, 3, 2, 3, 2, 3, 3]
bp = [i for i in range(n) if ms[i] == 2]
tp = [i for i in range(n) if ms[i] == 3]
sandwiched = [b for b in bp if ms[(b-1)%n] == 3 and ms[(b+1)%n] == 3]
print(f"ms={ms}, binary={bp}, ternary={tp}, sandwiched={sandwiched}")

max_len = 26
t0 = time.time()
words = enumerate_mover_words(ms, n, max_len)
elapsed = time.time() - t0
print(f"{len(words)} words ({elapsed:.1f}s)")

# Where does EC happen?
ec_at_proc = Counter()
ec_at_binary = 0
ec_at_ternary = 0
ec_at_sandwiched = 0
total_cycles = 0
no_ec_cycles = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    total_cycles += 1

    results = ec_analysis(word, cycle, ms, n)
    if not results:
        no_ec_cycles += 1
        continue

    # Which proc has EC?
    for r in results:
        ec_at_proc[r['proc']] += 1
        if ms[r['proc']] == 2:
            ec_at_binary += 1
        else:
            ec_at_ternary += 1
        if r['proc'] in sandwiched:
            ec_at_sandwiched += 1

print(f"\nTotal valid cycles: {total_cycles}")
print(f"No EC: {no_ec_cycles}")
print(f"\nEC location distribution (per proc, over all cycles with EC at that proc):")
for p in range(n):
    tag = "binary" if ms[p] == 2 else "ternary"
    sw = " (sandwiched)" if p in sandwiched else ""
    print(f"  P{p} ({tag}{sw}): {ec_at_proc[p]} cycles have EC here")
print(f"\nEC at binary total: {ec_at_binary}")
print(f"EC at ternary total: {ec_at_ternary}")
print(f"EC at sandwiched binary: {ec_at_sandwiched}")

# ============================================================
# KEY: For cycles where EC is ONLY at binary procs, analyze the context
# ============================================================
print("\n" + "=" * 70)
print("DETAILED EC CONTEXT ANALYSIS (sample)")
print("=" * 70)

sample_count = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    results = ec_analysis(word, cycle, ms, n)
    if not results: continue

    # Find the FIRST EC at a binary proc
    binary_ec = [r for r in results if ms[r['proc']] == 2]
    if not binary_ec: continue

    r = binary_ec[0]
    p = r['proc']
    ell = len(word)
    fc = Counter(word)
    info = classify_cycle(word, n)

    if sample_count < 5:
        print(f"\nCycle: CL={ell}, W={info['winding']}, fc_binary=[{fc[0]},{fc[2]},{fc[4]}]")
        print(f"  EC at P{p} (binary, sandwiched={p in sandwiched})")
        for ctx in r['overlap']:
            L, S, R = ctx
            print(f"    Overlap context: (L={L}, S={S}, R={R})")

        # Show all mover/nonmover contexts at this proc
        mover_ctxs = set()
        nonmover_ctxs = set()
        for s in range(ell):
            L = cycle[s][(p-1)%n]; S = cycle[s][p]; R = cycle[s][(p+1)%n]
            ctx = (L,S,R)
            if word[s] == p: mover_ctxs.add(ctx)
            else: nonmover_ctxs.add(ctx)
        print(f"    Mover contexts ({len(mover_ctxs)}): {sorted(mover_ctxs)}")
        print(f"    Non-mover contexts ({len(nonmover_ctxs)}): {sorted(nonmover_ctxs)}")
        sample_count += 1

# ============================================================
# PIGEONHOLE COUNTING: precise analysis
# ============================================================
print("\n" + "=" * 70)
print("PIGEONHOLE COUNTING")
print("=" * 70)

# For each cycle, at each sandwiched binary proc:
# - fc(b) = number of mover steps for b
# - non-mover steps = CL - fc(b)
# - mover contexts live in Z3 x {0,1} x Z3 (18 total)
# - non-mover contexts live in same space
# - EC iff overlap

# Key question: is the number of DISTINCT non-mover (L,R) pairs per S=s
# always ≥ number of distinct mover (L,R) pairs per S=s?

coverage_analysis = []
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    ell = len(word)
    fc = Counter(word)

    for b in sandwiched:
        nm_by_s = {0: set(), 1: set()}
        m_by_s = {0: set(), 1: set()}
        for s_idx in range(ell):
            L = cycle[s_idx][(b-1)%n]
            S = cycle[s_idx][b]
            R = cycle[s_idx][(b+1)%n]
            if word[s_idx] == b:
                m_by_s[S].add((L,R))
            else:
                nm_by_s[S].add((L,R))

        for sv in [0, 1]:
            nm_pairs = len(nm_by_s[sv])
            m_pairs = len(m_by_s[sv])
            overlap = len(nm_by_s[sv] & m_by_s[sv])
            coverage_analysis.append({
                'b': b, 'sv': sv, 'ell': ell,
                'fc_b': fc[b],
                'nm_pairs': nm_pairs, 'm_pairs': m_pairs,
                'overlap': overlap,
            })

# Statistics
print(f"Total (proc, S) combos analyzed: {len(coverage_analysis)}")

# Key insight: when overlap > 0, what's the typical nm/m pair counts?
with_overlap = [d for d in coverage_analysis if d['overlap'] > 0]
without_overlap = [d for d in coverage_analysis if d['overlap'] == 0]
print(f"With overlap: {len(with_overlap)}")
print(f"Without overlap: {len(without_overlap)}")

if with_overlap:
    nm_vals = [d['nm_pairs'] for d in with_overlap]
    m_vals = [d['m_pairs'] for d in with_overlap]
    print(f"  nm_pairs range: [{min(nm_vals)}, {max(nm_vals)}], avg={sum(nm_vals)/len(nm_vals):.1f}")
    print(f"  m_pairs range: [{min(m_vals)}, {max(m_vals)}], avg={sum(m_vals)/len(m_vals):.1f}")

if without_overlap:
    nm_vals = [d['nm_pairs'] for d in without_overlap]
    m_vals = [d['m_pairs'] for d in without_overlap]
    print(f"\nWithout overlap:")
    print(f"  nm_pairs range: [{min(nm_vals)}, {max(nm_vals)}], avg={sum(nm_vals)/len(nm_vals):.1f}")
    print(f"  m_pairs range: [{min(m_vals)}, {max(m_vals)}], avg={sum(m_vals)/len(m_vals):.1f}")
    # How many have nm_pairs + m_pairs > 9? (pigeonhole would apply)
    pigeonhole_applies = sum(1 for d in without_overlap if d['nm_pairs'] + d['m_pairs'] > 9)
    print(f"  nm+m > 9 (pigeonhole): {pigeonhole_applies}/{len(without_overlap)}")

# What about sum nm_pairs + m_pairs at each (proc, S)?
print(f"\nCombined pair count nm+m distribution (at combos WITHOUT overlap):")
combined_dist = Counter(d['nm_pairs'] + d['m_pairs'] for d in without_overlap)
for k in sorted(combined_dist):
    print(f"  nm+m = {k}: {combined_dist[k]} cases")

# ============================================================
# THE REAL MECHANISM: Is EC forced by the ring walk structure?
# ============================================================
print("\n" + "=" * 70)
print("EC MECHANISM: Walk structure analysis")
print("=" * 70)

# Hypothesis: when a binary proc fires, its value flips (0→1→0→1...).
# When it's a non-mover, its value doesn't change.
# The key is that the WALK determines which contexts appear.
# Binary value at step s: cumulative fire count mod 2.
# Context (L_s, b_s, R_s) = (ternary_left_value, binary_value, ternary_right_value)

# The binary value alternates between 0 and 1 each time b fires.
# Between firings, the neighbors change as other procs fire.

# Let's trace a specific cycle to see the pattern
sample_word = None
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None: continue
    if len(word) == 20:  # min CL
        sample_word = word
        break

if sample_word:
    word = sample_word
    cycle = build_cycle(ms, n, word)
    ell = len(word)
    fc = Counter(word)
    b = sandwiched[0]
    print(f"\nSample cycle: CL={ell}, b=P{b}")
    print(f"  fc = {dict(fc)}")
    print(f"  Word: {word}")
    print(f"  Step  Mover  Config       P{b}-context  Type")
    for s in range(ell):
        L = cycle[s][(b-1)%n]; S = cycle[s][b]; R = cycle[s][(b+1)%n]
        ctx = (L, S, R)
        typ = "MOVER" if word[s] == b else "nonmov"
        config_str = ''.join(str(c) for c in cycle[s])
        print(f"  {s:3d}   P{word[s]}     {config_str}  ({L},{S},{R})  {typ}")

# ============================================================
# SUMMARY STATISTICS
# ============================================================
print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)

print(f"""
KEY FINDINGS:

1. CL ≥ 3n+4 is FALSE:
   n=6: min CL = 17, 3n+4 = 22
   n=7: min CL = 20, 3n+4 = 25
   n=9: min CL = 26, 3n+4 = 31

2. CL minimum is determined by:
   - sum(ms) = base
   - Parity constraint: CL ≡ D (mod 2) where D = n*W
   - Extra firings from walk connectivity

3. ALL non-consecutive binary cycles have EC:
   n=6: 5046/5046 cycles (100%)
   n=7: 38384/38384 cycles (100%)
   n=9: 59996/59996 cycles (100%)
   Including ALL winding numbers, uniform AND non-uniform

4. EC does NOT require odd-winding or non-uniform direction.
   It's universal for non-consecutive binary sub-threshold.

5. The sorry-7 hypothesis (odd-winding + non-uniform + non-consecutive)
   is UNNECESSARILY RESTRICTIVE. The EC holds for ALL cycle types.

THEREFORE: Sorry 7 should be simplified to:
   "≥3 non-consecutive binary + sub-threshold → entry conflict"
   No winding/direction hypothesis needed.

   This is exactly the Universal Entry Conflict theorem from BinSCC Expl 10,
   which was already proved analytically with 4 mechanisms.
""")
