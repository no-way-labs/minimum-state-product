#!/usr/bin/env python3
"""
RA15 Part 2: Deeper gap case analysis.

Findings from Part 1:
- Gap case only exists at n=5 with ms=[2,2,2,3,3] (132 words, 4.8%)
- At n=7, NO gap cases at all (for tested layouts)
- EC is 100% in gap case, always at binary proc (24 binary-only, 108 both)
- Binary pigeonhole at individual proc: 69.7% (not sufficient alone)
- But EC ALWAYS exists at SOME binary proc

Key questions:
1. Why does gap vanish at n>=7?
2. What covers the 30.3% non-pigeonhole binary EC?
3. Is the argument: "in gap case, SOME binary proc has EC"?
4. What's the combined argument across all binary procs?
"""
import sys, os, time
from itertools import product as iproduct
from collections import Counter, defaultdict

sys.stdout = os.fdopen(sys.stdout.fileno(), 'w', buffering=1)


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


def get_contexts(word, ms, n):
    config = [0] * n
    proc_contexts = defaultdict(list)
    for step_idx, mover in enumerate(word):
        for p in range(n):
            L = config[(p-1) % n]
            S = config[p]
            R = config[(p+1) % n]
            proc_contexts[p].append((L, S, R, p == mover))
        config[mover] = (config[mover] + 1) % ms[mover]
    return proc_contexts


def find_entry_conflicts(word, ms, n):
    contexts = get_contexts(word, ms, n)
    ec_procs = []
    for p in range(n):
        mover_ctxs = set()
        nonmover_ctxs = set()
        for (L, S, R, is_mover) in contexts[p]:
            if is_mover:
                mover_ctxs.add((L, S, R))
            else:
                nonmover_ctxs.add((L, S, R))
        overlap = mover_ctxs & nonmover_ctxs
        if overlap:
            ec_procs.append((p, overlap))
    return ec_procs


def is_gap_case(word, ms, n):
    fc = Counter(word)
    binary_pos = set(i for i in range(n) if ms[i] == 2)
    ternary_pos = set(i for i in range(n) if ms[i] == 3)
    if not any(fc[p] >= 3 for p in range(n)):
        return False
    for t in ternary_pos:
        if fc[t] < 3:
            continue
        L = (t - 1) % n
        R = (t + 1) % n
        for nbr in [L, R]:
            if nbr in binary_pos and fc[nbr] < fc[t]:
                return False
    return True


# ============================================================
# 1. WHY DOES GAP VANISH AT n>=7?
# ============================================================
print("=" * 70)
print("1. WHY DOES GAP VANISH AT n>=7?")
print("=" * 70)

print("""
Gap condition: for ALL boundary ternary t, fc_bin >= fc_ter.

At n=5, ms=[2,2,2,3,3]: binary={0,1,2}, ternary={3,4}.
  Boundary ternary: P3 (nbrs P2=B, P4=T) and P4 (nbrs P3=T, P0=B).
  Only P3-P2 and P4-P0 are boundary pairs.
  Gap: fc[2] >= fc[3] AND fc[0] >= fc[4].
  With CL=16, fc sum = 16: fc[0]+fc[1]+fc[2] = 10 (binary), fc[3]+fc[4] = 6 (ternary).
  fc[1]=2 (minimum). fc[0]+fc[2] = 8. fc[3]=fc[4]=3 (minimum ternary).
  Gap: fc[0]>=3 and fc[2]>=3. With fc[0]+fc[2]=8: gap iff fc[0]>=4 and fc[2]>=4.
  That's 4+4=8: yes, exactly.

At n=7, ms=[2,2,2,3,3,3,3]: binary={0,1,2}, ternary={3,4,5,6}.
  Boundary: P3-P2 and P6-P0.
  CL = 2n + excess = 14 + excess.
  Min CL: 2+2+2+3+3+3+3 = 18 fires minimum, so CL >= 18.
  For CL = 18 (min): fc = [2,2,2,3,3,3,3].
  fc[2]=2, fc[3]=3: fc[2] < fc[3] -> NOT gap.
  fc[0]=2, fc[6]=3: fc[0] < fc[6] -> NOT gap.

  So at minimum CL, binary procs have fc=2 and ternary have fc=3.
  Binary fc < ternary fc at boundary -> always has gradient!
  Gap impossible at minimum CL.

  For higher CL: need fc_bin >= fc_ter at boundaries.
  fc[2] >= fc[3] >= 3 means fc[2] >= 4.
  fc[0] >= fc[6] >= 3 means fc[0] >= 4.
  Extra fires: +2 at P0, +2 at P2 = +4 binary excess.
  Total min fc with gap: 4+2+4+3+3+3+3 = 22 -> CL >= 22 = 2*7 + 8.
  But max CL we searched was 2*7+6 = 20. Let me check with higher max!
""")

ms = [2, 2, 2, 3, 3, 3, 3]
n = 7
max_cl = 2 * n + 10  # generous
t0 = time.time()
words = enumerate_mover_words(ms, n, max_cl)
t1 = time.time()
print(f"ms={ms}, max_cl={max_cl}: {len(words)} words ({t1-t0:.1f}s)")

gap_words = [w for w in words if is_gap_case(w, ms, n)]
print(f"Gap cases: {len(gap_words)}")

# Check fc distributions
cl_dist = Counter(len(w) for w in words)
print(f"CL distribution: {dict(sorted(cl_dist.items()))}")

if gap_words:
    for w in gap_words[:5]:
        fc = Counter(w)
        print(f"  CL={len(w)}: fc={dict(sorted(fc.items()))}")
else:
    print("  (still no gap cases)")

# Check at what CL gap becomes possible
print("\nMinimum CL for gap case:")
for test_ms in [[2,2,2,3,3,3,3], [2,2,2,3,3], [2,2,2,3,3,3,3,3,3]]:
    test_n = len(test_ms)
    binary_pos = [i for i in range(test_n) if test_ms[i] == 2]
    ternary_pos = [i for i in range(test_n) if test_ms[i] == 3]

    # Boundary ternary procs
    boundary = []
    for t in ternary_pos:
        L = (t - 1) % test_n
        R = (t + 1) % test_n
        bin_nbrs = [x for x in [L, R] if test_ms[x] == 2]
        if bin_nbrs:
            boundary.append((t, bin_nbrs))

    # For gap: need fc[b] >= fc[t] >= 3 for all (t, b) boundary pairs
    # Min: fc[t] = 3, fc[b] = 4 (next even >= 3)
    min_gap_fc = {p: test_ms[p] for p in range(test_n)}
    for t, bin_nbrs in boundary:
        for b in bin_nbrs:
            if min_gap_fc[b] < min_gap_fc[t]:
                min_gap_fc[b] = min_gap_fc[t]
                if min_gap_fc[b] % 2 == 1:
                    min_gap_fc[b] += 1  # round up to even

    min_cl = sum(min_gap_fc.values())
    thresh = 4 * 3**(test_n - 2)
    print(f"  ms={test_ms}: min gap CL = {min_cl}, 2n = {2*test_n}, sum(ms) = {sum(test_ms)}, 4*3^(n-2)={thresh}")
    print(f"    min gap fc: {dict(min_gap_fc)}")
    print(f"    boundary pairs: {boundary}")


# ============================================================
# 2. DETAILED MECHANISM AT n=5
# ============================================================
print("\n" + "=" * 70)
print("2. DETAILED MECHANISM: WHY DOES BINARY ALWAYS HAVE EC?")
print("=" * 70)

ms = [2, 2, 2, 3, 3]
n = 5
max_cl = 2 * n + 8
words = enumerate_mover_words(ms, n, max_cl)
gap_words = [w for w in words if len(w) > 2*n and is_gap_case(w, ms, n)]

print(f"\nms={ms}: {len(gap_words)} gap words")
print(f"All have CL=16, fc pattern: P0(B)=4, P1(B)=2, P2(B)=4, P3(T)=3, P4(T)=3")

# For each gap word, which binary proc(s) have EC?
ec_at_procs = Counter()
for w in gap_words:
    ec_procs = find_entry_conflicts(w, ms, n)
    for p, _ in ec_procs:
        ec_at_procs[p] += 1

print(f"\nEC frequency by proc:")
for p in range(n):
    pct = 100 * ec_at_procs.get(p, 0) / len(gap_words)
    print(f"  P{p} ({'B' if ms[p]==2 else 'T'}, fc={"4" if ms[p]==2 and p != 1 else "2" if p==1 else "3"}): EC in {ec_at_procs.get(p,0)}/{len(gap_words)} ({pct:.1f}%)")

# Check if UNION of binary procs always has EC
always_some_binary = 0
for w in gap_words:
    ec_procs = find_entry_conflicts(w, ms, n)
    binary_ec = [p for p, _ in ec_procs if ms[p] == 2]
    if binary_ec:
        always_some_binary += 1

print(f"\nSome binary proc has EC: {always_some_binary}/{len(gap_words)} ({100*always_some_binary/len(gap_words):.1f}%)")


# ============================================================
# 3. MECHANISM: WHAT FORCES EC AT BINARY?
# ============================================================
print("\n" + "=" * 70)
print("3. MECHANISM: WHAT FORCES EC AT BINARY WITH fc=4?")
print("=" * 70)

# For binary proc b with fc=4 in cycle of length 16:
# b fires 4 times, non-mover 12 times.
# S toggles: 0,1,0,1 at fire steps.
#
# Between fires: b's value is fixed. But L and R change.
# The (L,R) pairs seen at mover and non-mover steps:
# Can the same (L,R) pair with same S appear in both?

# Let's trace the exact walk for all gap words
print("Tracing mover (L,R) vs non-mover (L,R) at binary procs:")

# Instead of individual, let's look at the STRUCTURE of why some have EC and some don't
# Focus on P0 (binary, fc=4, nbrs P4=T and P1=B)
# Context space for P0: L=P4 (3 vals), S=P0 (2 vals), R=P1 (2 vals) -> 12 total
# Mover: 4 contexts (2 with S=0, 2 with S=1)
# Non-mover: 12 contexts from 12 steps

# Check: for the 30% without EC at P0, what's the structure?
no_ec_at_p0 = []
ec_at_p0 = []
for w in gap_words:
    ec_procs = find_entry_conflicts(w, ms, n)
    ec_set = set(p for p, _ in ec_procs)
    if 0 in ec_set:
        ec_at_p0.append(w)
    else:
        no_ec_at_p0.append(w)

print(f"P0: EC={len(ec_at_p0)}, no EC={len(no_ec_at_p0)}")

# Look at no-EC-at-P0 words: where DO they have EC?
if no_ec_at_p0:
    print(f"\nWords without EC at P0 (first 5):")
    for w in no_ec_at_p0[:5]:
        ec_procs = find_entry_conflicts(w, ms, n)
        ec_set = set(p for p, _ in ec_procs)
        print(f"  word={w}, EC at procs: {ec_set}")

        # Show P0 mover vs nonmover contexts
        contexts = get_contexts(w, ms, n)
        m0 = set()
        nm0 = set()
        for (L, S, R, is_mover) in contexts[0]:
            if is_mover:
                m0.add((L, S, R))
            else:
                nm0.add((L, S, R))
        print(f"    P0 mover ctxs: {sorted(m0)}")
        print(f"    P0 nonmov ctxs: {sorted(nm0)}")
        print(f"    P0 |M|+|NM|={len(m0)+len(nm0)}, space=12")


# ============================================================
# 4. THE KEY: fc_sum AT BINARY PROCS
# ============================================================
print("\n" + "=" * 70)
print("4. COMBINED BINARY FC IN GAP CASE")
print("=" * 70)

print("""
In gap case at n=5, ms=[2,2,2,3,3]:
  fc = [4, 2, 4, 3, 3], CL = 16
  Binary total fc = 10, ternary total = 6.
  Binary procs occupy 10/16 = 62.5% of all steps.

  P0 fires 4 times in 16 steps. P0 appears as non-mover in 12 steps.
  P2 fires 4 times in 16 steps. P2 appears as non-mover in 12 steps.

  P0 and P2 share neighbor P1 (binary, fc=2).
  P1 only changes value 2 times in 16 steps.
  So for most of the cycle, P1's value is fixed.

  Between P1's two fires:
    Phase A (P1=0): some number of steps
    Phase B (P1=1): some number of steps

  In each phase, P0's right neighbor is fixed.
  P0 fires multiple times with R=fixed.
  P0 mover contexts: (L, S, R_fixed) with varying L, alternating S.
  P0 non-mover contexts: (L, S, R_fixed) with varying L.

  If any (L, S) pair appears in both mover and non-mover with same R:
  EC at P0.

  With R fixed: context space for P0 is 3*2 = 6 (just L and S).
  P0 fires ~2 times in each P1-phase, non-mover ~6 times.
  2 mover + 6 non-mover = 8 appearances from 6 slots.
  Pigeonhole: at least one (L,S) pair appears twice.
  But both could be non-mover!
""")

# Let's check: within each P1-phase, does P0 have EC?
print("P1-phase analysis for P0:")
for w in gap_words[:10]:
    contexts = get_contexts(w, ms, n)
    # Trace P1 value over time
    config = [0] * n
    p1_vals = []
    for step, mover in enumerate(w):
        p1_vals.append(config[1])
        config[mover] = (config[mover] + 1) % ms[mover]

    # Split into P1-phases
    phases = defaultdict(list)  # p1_val -> list of (step, is_mover_at_P0)
    for step in range(len(w)):
        p1_val = p1_vals[step]
        is_mover = (w[step] == 0)
        L, S, R, _ = contexts[0][step]
        phases[p1_val].append((step, is_mover, L, S, R))

    # Check EC within each phase at P0
    for p1v in sorted(phases.keys()):
        entries = phases[p1v]
        mover_lr = set()
        nonmover_lr = set()
        for step, is_mover, L, S, R in entries:
            if is_mover:
                mover_lr.add((L, S))
            else:
                nonmover_lr.add((L, S))
        overlap = mover_lr & nonmover_lr
    # Just count
    break  # skip detailed output


# ============================================================
# 5. GENERAL n ANALYSIS: does gap case even exist?
# ============================================================
print("\n" + "=" * 70)
print("5. GENERAL n: DOES GAP CASE EXIST?")
print("=" * 70)

print("""
For consecutive binary at positions {0,...,B-1} with B >= 3:
  Boundary ternary: P_B (right boundary) and P_{n-1} (left boundary).

  P_B has left neighbor P_{B-1} (binary) and right neighbor P_{B+1}.
  P_{n-1} has left neighbor P_{n-2} and right neighbor P_0 (binary).

  For CL = 2n (minimum ZW):
    fc[binary] = 2, fc[ternary] = 3.
    At boundary: fc[binary] = 2 < 3 = fc[ternary].
    ALWAYS has gradient at minimum CL!

  For gap: need fc[boundary_binary] >= fc[boundary_ternary] >= 3.
    Minimum: fc[boundary_binary] = 4.
    Extra fires needed: 2 per boundary binary.
    With 2 boundary binaries: 4 extra fires.
    CL >= sum(ms) + 4.

  For n=5, ms=[2,2,2,3,3]: sum(ms) = 12, min gap CL = 16 = 2n + 6.
  For n=7, ms=[2,2,2,3,3,3,3]: sum(ms) = 18, min gap CL = 22 = 2n + 8.

  But we're interested in CL = 2n + excess for FIXED excess.
  At n=5: 2n=10, gap needs CL=16, excess=6. Possible!
  At n=7: 2n=14, gap needs CL=22, excess=8. Need to search higher.

  The gap case becomes RARER as n grows because the excess needed is fixed
  but 2n grows. At minimum CL, gradient always exists.

  Actually: for CL <= 2n + 2*(excess per boundary), gap is impossible
  when the boundary binary fc is forced to be 2 (minimum).

  The question is: for CL > 2n, how much excess can go to boundary binary?
""")

# Check at n=7 with higher max_cl
for ms, n, max_cl in [
    ([2,2,2,3,3,3,3], 7, 24),
    ([2,2,2,3,3,3,3], 7, 26),
]:
    t0 = time.time()
    words = enumerate_mover_words(ms, n, max_cl)
    t1 = time.time()
    gap_words = [w for w in words if is_gap_case(w, ms, n)]
    zw = [w for w in words if len(w) > 2*n]
    print(f"ms={ms}, max_cl={max_cl}: {len(words)} words ({t1-t0:.1f}s)")
    print(f"  ZW: {len(zw)}, gap: {len(gap_words)}")

    if gap_words:
        for w in gap_words[:3]:
            fc = Counter(w)
            ec_procs = find_entry_conflicts(w, ms, n)
            print(f"  CL={len(w)}, fc={dict(sorted(fc.items()))}, EC at {[p for p,_ in ec_procs]}")


# ============================================================
# 6. THE REAL ARGUMENT: fc_bin >= 4 forces CL >= 2n+4
# ============================================================
print("\n" + "=" * 70)
print("6. FC DISTRIBUTION IN GAP CASE")
print("=" * 70)

ms = [2, 2, 2, 3, 3]
n = 5
max_cl = 20
words = enumerate_mover_words(ms, n, max_cl)
gap_words = [w for w in words if len(w) > 2*n and is_gap_case(w, ms, n)]

fc_patterns = Counter()
for w in gap_words:
    fc = Counter(w)
    fc_tup = tuple(fc[p] for p in range(n))
    fc_patterns[fc_tup] += 1

print(f"ms={ms}: {len(gap_words)} gap words")
print(f"fc patterns (P0,P1,P2,P3,P4):")
for pat, cnt in sorted(fc_patterns.items()):
    ec_count = 0
    for w in gap_words:
        fc = Counter(w)
        if tuple(fc[p] for p in range(n)) == pat:
            ec = find_entry_conflicts(w, ms, n)
            if ec:
                ec_count += 1
    print(f"  fc={pat}: {cnt} words, EC={ec_count}")


# ============================================================
# 7. NON-ADJACENT BINARY: does gap exist?
# ============================================================
print("\n" + "=" * 70)
print("7. NON-ADJACENT BINARY: does gap exist?")
print("=" * 70)

for ms, n in [([2,3,2,3,2], 5), ([3,2,3,2,3,2,3], 7)]:
    max_cl = 2*n + 8
    words = enumerate_mover_words(ms, n, max_cl)
    zw = [w for w in words if len(w) > 2*n]
    gap = [w for w in zw if is_gap_case(w, ms, n)]
    print(f"ms={ms}: ZW={len(zw)}, gap={len(gap)}")

    # Check: every ternary has binary neighbors on BOTH sides
    # So fc_bin >= fc_ter at ALL boundaries
    # With non-adjacent: every ternary IS a boundary ternary
    # Much harder to satisfy gap condition
    if gap:
        for w in gap[:3]:
            fc = Counter(w)
            print(f"  CL={len(w)}, fc={dict(sorted(fc.items()))}")

print("\n" + "=" * 70)
print("DONE")
print("=" * 70)
