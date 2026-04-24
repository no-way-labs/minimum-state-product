#!/usr/bin/env python3
"""
RA15 Part 3: The real mechanism for gap case EC.

Key findings from Parts 1-2:
- Gap case needs fc_bin >= fc_ter >= 3 at ALL boundary (bin,ter) pairs
- This forces fc_bin >= 4 (even) at boundary binary procs
- Min gap CL = sum(ms) + 4 (two boundary binaries each get +2)
- At n=5 ms=[2,2,2,3,3]: gap fc = [4,2,4,3,3], CL=16
- At n=7 ms=[2,2,2,3,3,3,3]: gap fc = [4,2,4,3,3,3,3], CL=22
- EC is 100% in gap case, always at some binary proc
- P1 (interior binary, fc=2) has EC 97.9% of the time!

Hypothesis: The KEY mechanism is at the INTERIOR binary proc (P1, fc=2).
P1 only fires 2 times in 16 steps -> 14 non-mover appearances.
Context space for P1: 2*2*2 = 8 (both neighbors binary).
14 non-mover appearances from 8 slots: heavy repetition.
2 mover appearances: high chance of collision.

Actually: P1 has 2 mover contexts and 14 non-mover appearances.
Non-mover: 14 from 8 slots -> each slot averages 1.75 appearances.
Mover: 2 contexts. If BOTH are in the non-mover set -> EC.
Non-mover distinct: at most 8, but likely fewer (walk constrains it).
If non-mover distinct >= 7 out of 8, then P(mover hits one) is high.

Let's verify: does EVERY gap word have EC at P1 specifically?
And what's the exact mechanism?

Also test: the high-fc binary procs (P0, P2 with fc=4).
fc=4 fires from context space 12 (3*2*2). 4 mover + 12 non-mover.
"""
import sys, os, time
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
# ANALYSIS 1: Interior binary proc EC
# ============================================================
print("=" * 70)
print("ANALYSIS 1: Interior binary proc P1 in gap case")
print("=" * 70)

ms = [2, 2, 2, 3, 3]
n = 5
max_cl = 20
words = enumerate_mover_words(ms, n, max_cl)
gap_words = [w for w in words if is_gap_case(w, ms, n)]

print(f"ms={ms}: {len(gap_words)} gap words")

# P1 analysis
p1_ec = 0
p1_no_ec = 0
p1_no_ec_words = []

for w in gap_words:
    contexts = get_contexts(w, ms, n)
    mover_ctxs = set()
    nonmover_ctxs = set()
    for (L, S, R, is_mover) in contexts[1]:
        if is_mover:
            mover_ctxs.add((L, S, R))
        else:
            nonmover_ctxs.add((L, S, R))
    if mover_ctxs & nonmover_ctxs:
        p1_ec += 1
    else:
        p1_no_ec += 1
        if len(p1_no_ec_words) < 20:
            p1_no_ec_words.append(w)

print(f"P1 EC: {p1_ec}/{len(gap_words)} ({100*p1_ec/len(gap_words):.1f}%)")
print(f"P1 no EC: {p1_no_ec}")

# For P1 no-EC words: where IS the EC?
print(f"\nP1-no-EC words: EC locations")
for w in p1_no_ec_words[:10]:
    contexts = get_contexts(w, ms, n)
    ec_at = []
    for p in range(n):
        m = set()
        nm = set()
        for (L, S, R, is_mover) in contexts[p]:
            if is_mover:
                m.add((L, S, R))
            else:
                nm.add((L, S, R))
        if m & nm:
            ec_at.append(p)

    # P1 details
    m1 = set()
    nm1 = set()
    for (L, S, R, is_mover) in contexts[1]:
        if is_mover:
            m1.add((L, S, R))
        else:
            nm1.add((L, S, R))

    print(f"  EC at {ec_at}, P1 mover={sorted(m1)}, P1 nonmov_distinct={len(nm1)}/8")


# ============================================================
# ANALYSIS 2: High-fc binary mechanism
# ============================================================
print("\n" + "=" * 70)
print("ANALYSIS 2: Binary fc=4 mechanism detail")
print("=" * 70)

# For P0 (fc=4, nbrs P4=T(3), P1=B(2)): ctx space = 3*2*2 = 12
# For P2 (fc=4, nbrs P1=B(2), P3=T(3)): ctx space = 2*2*3 = 12

# With incrementing transitions:
# P0 fires: 0->1->0->1 (values 0,0,1,1 before fire)
# Actually: start at 0, fire 1: 0->1, fire 2: 1->0, fire 3: 0->1, fire 4: 1->0
# Mover S values: 0, 1, 0, 1 (alternating)

# Key constraint: when P0 fires, its neighbor must have just moved there.
# Ring walk: mover goes ..., P0, P1 or P4, ...
# P0's fires alternate with P1 and P4 moves.

# Let's look at the specific (L,R) pairs at mover steps for P0
print("P0 (fc=4) mover context (L,R) analysis:")

# Collect all P0 mover contexts across all gap words, split by S
s0_lr_counts = Counter()
s1_lr_counts = Counter()
for w in gap_words:
    contexts = get_contexts(w, ms, n)
    for (L, S, R, is_mover) in contexts[0]:
        if is_mover:
            if S == 0:
                s0_lr_counts[(L, R)] += 1
            else:
                s1_lr_counts[(L, R)] += 1

print(f"S=0 mover (L,R) distribution: {dict(s0_lr_counts)}")
print(f"S=1 mover (L,R) distribution: {dict(s1_lr_counts)}")

# How many distinct (L,R) per word?
p0_distinct = Counter()
for w in gap_words:
    contexts = get_contexts(w, ms, n)
    lr_set = set()
    for (L, S, R, is_mover) in contexts[0]:
        if is_mover:
            lr_set.add((L, S, R))
    p0_distinct[len(lr_set)] += 1
print(f"P0 mover distinct contexts per word: {dict(sorted(p0_distinct.items()))}")


# ============================================================
# ANALYSIS 3: The real question - is there a SHORT argument?
# ============================================================
print("\n" + "=" * 70)
print("ANALYSIS 3: CL and context space arithmetic")
print("=" * 70)

print("""
Gap case: fc = [4, 2, 4, 3, 3] at n=5 (only fc pattern).
CL = 16.

For each binary proc b, total appearances = CL = 16.
  P0: ctx_space = 3*2*2 = 12. 16 appearances from 12 slots.
      By pigeonhole: at least one triple appears 2+ times.
      4 mover + 12 non-mover. Need same triple in both.
      NOT guaranteed by simple counting (could be 4 unique movers, 12 from remaining 8).

  P1: ctx_space = 2*2*2 = 8. 16 appearances from 8 slots.
      Average: 2 per slot. 2 mover + 14 non-mover.
      Non-mover uses at least ceil(14/8) = 2 per slot on average.
      Mover uses 2 triples. Non-mover distinct <= 8.
      If non-mover occupies all 8 slots, then 2 mover triples must hit occupied slots.
      BUT: mover could use 2 triples not in non-mover set... if non-mover uses only 6 of 8.

Let me check: how many distinct non-mover contexts does P1 use?
""")

p1_nm_distinct = Counter()
p1_m_distinct = Counter()
p1_nm_size = Counter()
for w in gap_words:
    contexts = get_contexts(w, ms, n)
    m_set = set()
    nm_set = set()
    for (L, S, R, is_mover) in contexts[1]:
        if is_mover:
            m_set.add((L, S, R))
        else:
            nm_set.add((L, S, R))
    p1_nm_distinct[len(nm_set)] += 1
    p1_m_distinct[len(m_set)] += 1
    p1_nm_size[len(nm_set)] += 1

print(f"P1 mover distinct: {dict(sorted(p1_m_distinct.items()))}")
print(f"P1 nonmover distinct: {dict(sorted(p1_nm_distinct.items()))}")

# Check: when P1 has 2 mover distinct and nm distinct is 6 or 7:
# 2 + 6 = 8 = space -> might just fit without overlap
# 2 + 7 = 9 > 8 -> MUST overlap
# 2 + 8 = 10 > 8 -> MUST overlap

# So P1 has EC iff nm_distinct >= 7 (since mover always has 2 distinct).
# Actually mover could have 1 distinct if both fires have same context... let's check.

print(f"\nP1: mover distinct = 2 always? {all(v == 2 for v in [1] if False)}")
# Better check:
m1_always_2 = all(True for w in gap_words
    for _ in [None]
    if len(set((L,S,R) for L,S,R,im in get_contexts(w,ms,n)[1] if im)) == 2)
# Too slow, let me just check the counter
print(f"P1 mover distinct counts: {dict(sorted(p1_m_distinct.items()))}")
print(f"  -> always 2: {p1_m_distinct.get(2, 0) == len(gap_words)}")

# So if mover distinct = 2:
#   EC iff nonmover distinct >= 7 (since 2+7 > 8)
#   No EC iff nonmover distinct <= 6 (since 2+6 = 8 = space, could be disjoint)
# Let's verify:
ec_by_nm = defaultdict(lambda: [0, 0])  # nm_distinct -> [ec_count, no_ec_count]
for w in gap_words:
    contexts = get_contexts(w, ms, n)
    m_set = set()
    nm_set = set()
    for (L, S, R, is_mover) in contexts[1]:
        if is_mover:
            m_set.add((L, S, R))
        else:
            nm_set.add((L, S, R))
    has_ec = len(m_set & nm_set) > 0
    ec_by_nm[len(nm_set)][0 if has_ec else 1] += 1

print(f"\nP1 EC by nonmover_distinct:")
for nd in sorted(ec_by_nm.keys()):
    ec, no_ec = ec_by_nm[nd]
    print(f"  nm_distinct={nd}: EC={ec}, no_EC={no_ec}")


# ============================================================
# ANALYSIS 4: Walk constraints on P1 contexts
# ============================================================
print("\n" + "=" * 70)
print("ANALYSIS 4: Walk constraints on P1 non-mover contexts")
print("=" * 70)

print("""
P1 has neighbors P0 (binary) and P2 (binary).
Context (L,S,R) = (P0_val, P1_val, P2_val), all in {0,1}.
Full space: {0,1}^3 = 8 triples.

P1 fires twice (fc=2). Between fires, P1's value is fixed.
In phase A (P1=0): non-mover contexts are (P0, 0, P2).
In phase B (P1=1): non-mover contexts are (P0, 1, P2).

P0 fires 4 times, P2 fires 4 times. These change the L and R values.

Question: which (L, 0, R) triples appear as non-mover in phase A?
L = P0_val, R = P2_val. Each can be 0 or 1. So 4 possible.
Do all 4 appear? In phase A, P0 toggles 0<->1 several times,
P2 toggles 0<->1 several times.

If both P0 and P2 change at least once during phase A:
then L takes both values and R takes both values.
But do all 4 (L,R) combos appear? Not necessarily.
They appear iff the toggles are not perfectly synchronized.
""")

# Empirical: which non-mover contexts does P1 miss?
missed_contexts = Counter()
for w in gap_words:
    contexts = get_contexts(w, ms, n)
    nm_set = set()
    for (L, S, R, is_mover) in contexts[1]:
        if not is_mover:
            nm_set.add((L, S, R))

    all_8 = set((l,s,r) for l in range(2) for s in range(2) for r in range(2))
    missed = all_8 - nm_set
    for m in missed:
        missed_contexts[m] += 1

print(f"P1 missed non-mover contexts (out of 8):")
for ctx, cnt in sorted(missed_contexts.items(), key=lambda x: -x[1]):
    print(f"  {ctx}: missed in {cnt}/{len(gap_words)} words ({100*cnt/len(gap_words):.1f}%)")


# ============================================================
# ANALYSIS 5: Combined binary argument
# ============================================================
print("\n" + "=" * 70)
print("ANALYSIS 5: Combined argument across binary procs")
print("=" * 70)

print("""
Even though individual binary procs don't always have EC,
SOME binary proc always does. Why?

Key: P0, P1, P2 are consecutive binary. Their contexts are linked.
When P0 fires, it changes P1's left neighbor.
When P2 fires, it changes P1's right neighbor.

If P1 doesn't have EC: its 2 mover contexts avoid all non-mover contexts.
This means P1's mover steps see (L,S,R) values not seen as non-mover.
These are "fresh" L and R values at P1's fire moments.

Claim: if P1 avoids EC, then P0 and P2 are forced into specific patterns
that cause them to have EC.

Let's verify: in P1-no-EC cases, does P0 ALWAYS have EC? Or P2?
""")

p0_ec_when_p1_no = 0
p2_ec_when_p1_no = 0
both_when_p1_no = 0
neither_when_p1_no = 0

for w in p1_no_ec_words:
    contexts = get_contexts(w, ms, n)
    p0_m = set()
    p0_nm = set()
    p2_m = set()
    p2_nm = set()
    for (L, S, R, im) in contexts[0]:
        (p0_m if im else p0_nm).add((L, S, R))
    for (L, S, R, im) in contexts[2]:
        (p2_m if im else p2_nm).add((L, S, R))

    p0_ec = bool(p0_m & p0_nm)
    p2_ec = bool(p2_m & p2_nm)

    if p0_ec and p2_ec:
        both_when_p1_no += 1
    elif p0_ec:
        p0_ec_when_p1_no += 1
    elif p2_ec:
        p2_ec_when_p1_no += 1
    else:
        neither_when_p1_no += 1

print(f"When P1 has no EC ({len(p1_no_ec_words)} words):")
print(f"  P0 and P2 both EC: {both_when_p1_no}")
print(f"  P0 only EC: {p0_ec_when_p1_no}")
print(f"  P2 only EC: {p2_ec_when_p1_no}")
print(f"  Neither P0 nor P2: {neither_when_p1_no}")


# ============================================================
# ANALYSIS 6: What about TERNARY EC in P1-no-EC cases?
# ============================================================
print("\n" + "=" * 70)
print("ANALYSIS 6: Full EC picture when P1 has no EC")
print("=" * 70)

for w in p1_no_ec_words[:5]:
    contexts = get_contexts(w, ms, n)
    fc = Counter(w)
    print(f"\n  word len={len(w)}, fc={dict(sorted(fc.items()))}")
    for p in range(n):
        m_set = set()
        nm_set = set()
        for (L, S, R, im) in contexts[p]:
            (m_set if im else nm_set).add((L, S, R))
        overlap = m_set & nm_set
        space = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
        print(f"  P{p}({'B' if ms[p]==2 else 'T'} fc={fc[p]}): |M|={len(m_set)}, |NM|={len(nm_set)}, space={space}, overlap={len(overlap)}")


# ============================================================
# ANALYSIS 7: For general n in gap case, ALL binary have fc>=4
# ============================================================
print("\n" + "=" * 70)
print("ANALYSIS 7: General n gap structure")
print("=" * 70)

print("""
For n procs with B >= 3 consecutive binary at {0,...,B-1}:
  Boundary pairs: (P_B, P_{B-1}) and (P_{n-1}, P_0).
  Gap: fc[B-1] >= fc[B] >= 3 and fc[0] >= fc[n-1] >= 3.
  Since fc[B-1] even and >= 3: fc[B-1] >= 4.
  Since fc[0] even and >= 3: fc[0] >= 4.

  Interior binary procs {1,...,B-2} could have fc = 2 (minimum).
  But ALL boundary binary procs have fc >= 4.

  Context space for boundary binary b:
    If b has one binary nbr + one ternary nbr: space = 2*2*3 = 12
    If b has two binary nbrs: space = 2*2*2 = 8

  CL in gap case:
    min CL = sum(ms) + 4 = 2B + 3(n-B) + 4 = 3n - B + 4

  For B=3, n=5: min CL = 15-3+4 = 16. CL = 16.
    Each binary proc appears 16 times total.
    Boundary binary (fc=4): 4 mover + 12 non-mover from space 12.
    Interior binary (fc=2): 2 mover + 14 non-mover from space 8.

  For B=3, n=7: min CL = 21-3+4 = 22. CL >= 22.
    Each proc appears 22 times total.
    Boundary binary (fc=4): 4 mover + 18 non-mover from space 12.
    Interior binary (fc=2): 2 mover + 20 non-mover from space 8.

  At n=7, interior binary P1 has 20 non-mover from 8 slots.
  Non-mover distinct: at most 8. Mover: 2.
  If non-mover distinct >= 7: EC guaranteed.
  20 non-mover from 8 slots: non-mover uses at least 8 slots (pigeonhole!).
  Wait: 20 > 8, so non-mover uses exactly 8 distinct (all of them).
  But mover uses 2. 2 + 8 > 8 -> EC GUARANTEED at P1!

  Wait, does this work? 20 non-mover appearances from 8 slots means
  all 8 slots are used. Mover has 2 slots. Both must be in the 8.
  OVERLAP GUARANTEED.

  Hmm wait: the 14 non-mover at n=5 from 8 slots.
  14 > 8 -> also all 8 slots used! So mover 2 slots must overlap.
  But empirically P1 has EC only 97.9%, not 100%.

  THE ISSUE: 14 non-mover APPEARANCES from 8 slots does NOT mean all 8 used.
  It means some slots are used multiple times. Could use only 7 of 8.
  14 appearances, 7 distinct: that's 2 per slot average. Feasible.

  But wait: 14 > 8 doesn't guarantee all 8 distinct.
  For example: 14 appearances could use 5 distinct slots, with some appearing 3+ times.

  The pigeonhole says: with 14 appearances, at least ceil(14/8) = 2 per SOME slot.
  Does NOT guarantee all slots used.

  So the walk structure must be what forces high distinct count.
  Let me check the actual distinct counts.
""")

# Already computed above:
print("From earlier: P1 nonmover distinct counts:")
print(f"  {dict(sorted(p1_nm_distinct.items()))}")
print(f"  P1 EC by nm_distinct: {dict(sorted((k, tuple(v)) for k,v in ec_by_nm.items()))}")


# ============================================================
# ANALYSIS 8: At n=7, is P1 guaranteed to cover all 8?
# ============================================================
print("\n" + "=" * 70)
print("ANALYSIS 8: n=7 gap case P1 analysis")
print("=" * 70)

ms7 = [2, 2, 2, 3, 3, 3, 3]
n7 = 7
max_cl7 = 24

t0 = time.time()
words7 = enumerate_mover_words(ms7, n7, max_cl7)
t1 = time.time()
gap_words7 = [w for w in words7 if is_gap_case(w, ms7, n7)]
print(f"ms={ms7}, max_cl={max_cl7}: {len(words7)} words ({t1-t0:.1f}s)")
print(f"Gap words: {len(gap_words7)}")

if gap_words7:
    # P1 analysis
    p1_nm7 = Counter()
    p1_ec7 = 0
    for w in gap_words7[:5000]:  # sample
        contexts = get_contexts(w, ms7, n7)
        m_set = set()
        nm_set = set()
        for (L, S, R, im) in contexts[1]:
            (m_set if im else nm_set).add((L, S, R))
        p1_nm7[len(nm_set)] += 1
        if m_set & nm_set:
            p1_ec7 += 1

    checked = min(5000, len(gap_words7))
    print(f"P1 nonmover distinct (first {checked}): {dict(sorted(p1_nm7.items()))}")
    print(f"P1 EC: {p1_ec7}/{checked}")

    # Also check: any proc with universal EC?
    proc_ec = Counter()
    for w in gap_words7[:5000]:
        contexts = get_contexts(w, ms7, n7)
        for p in range(n7):
            m = set()
            nm = set()
            for (L, S, R, im) in contexts[p]:
                (m if im else nm).add((L, S, R))
            if m & nm:
                proc_ec[p] += 1

    print(f"EC by proc (first {checked}):")
    for p in range(n7):
        print(f"  P{p}({'B' if ms7[p]==2 else 'T'}): EC in {proc_ec.get(p,0)}/{checked}")

    some_binary = 0
    for w in gap_words7[:5000]:
        contexts = get_contexts(w, ms7, n7)
        has_bin_ec = False
        for p in [0, 1, 2]:
            m = set()
            nm = set()
            for (L, S, R, im) in contexts[p]:
                (m if im else nm).add((L, S, R))
            if m & nm:
                has_bin_ec = True
                break
        if has_bin_ec:
            some_binary += 1
    print(f"Some binary has EC: {some_binary}/{checked}")


print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
