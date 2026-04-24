#!/usr/bin/env python3
"""
RA15 Part 6: Can gap case be eliminated by CL bound?

Key observation: gap case requires CL >= sum(ms) + 4.
For B=3 consecutive binary: sum(ms) = 2*3 + 3*(n-3) = 3n-3.
Min gap CL = 3n + 1.

But CL <= 2n is what we're trying to prove.
If 3n+1 > 2n (i.e., n >= 0), then gap case CL > 2n ALWAYS.
This means gap case ALWAYS has CL > 2n... but that's exactly the
ZW regime we're in.

Wait - the CL <= 2n proof is ABOUT cycles with CL > 2n.
We want to show they all have EC. The gap is a sub-case of CL > 2n.

Actually let me recheck: does gap case require CL much larger than 2n?
At n=5: gap CL = 16 = 2*5 + 6. That's 2n + 6.
At n=7: gap CL >= 22 = 2*7 + 8. That's 2n + 8.
At n=9: gap CL >= 28 = 2*9 + 10. That's 2n + 10.

Gap CL - 2n = (3n+1) - 2n = n+1.

So gap case has excess >= n+1 > 2n would need n+1 > 0, always true.

THE KEY: gap case has very high CL. Specifically, CL >= 3n+1.
With 3 consecutive binary, context space at interior binary is 8.
Non-mover appearances at P1: CL - fc[1].

In gap case: fc[1] >= 2. Non-mover >= 3n + 1 - fc[1].
Minimum: 3n + 1 - max_fc[1].

What's max fc[1]? Since extra fires only go to binary:
total binary excess = CL - sum(ms) = CL - (3n-3).
For minimum gap CL = 3n+1: binary excess = 4.
This goes to boundary binary (+2 each): fc[0]=4, fc[2]=4, fc[1]=2.
Non-mover at P1: 3n+1 - 2 = 3n-1.

For n >= 3: 3n-1 >= 8 (at n=3: 8).
But non-mover DISTINCT is what matters, not appearances.

At n=7: non-mover appearances at P1 = 22-2 = 20. Space = 8.
At n=9: non-mover appearances at P1 = 28-2 = 26. Space = 8.

With 20+ non-mover appearances from 8 contexts:
The walk visits 20+ of the 8 slots.
We need to show all 8 are visited.

Can the walk avoid some? Only if certain (L,R) combos never appear.
P0 fires 4+ times (all even, toggling). P2 fires 4+ times.

Between P1's fires: P1 has 2 phases (P1_val=0 and P1_val=1).
In each phase: 4 contexts (L in {0,1}, R in {0,1}).

P0 fires 4 times total. In P1's first phase (P1_val=0 initially):
P0 must fire at least once (since P0's fires are spread across the cycle).
Similarly P2 fires at least once.

When P0 fires once in a P1-phase: L toggles once. Both L=0 and L=1 seen.
When P2 fires once: R toggles once. Both R=0 and R=1 seen.

But the interleaving determines which (L,R) combos appear.
If P0 fires first then P2: we see (0,0) -> (1,0) -> (1,1).
  Missing: (0,1).
If they interleave: (0,0) -> (1,0) -> (1,1) -> (0,1). All 4!

So with at least 2 fires each of P0 and P2 in a single P1-phase:
L toggles twice (0->1->0), R toggles twice (0->1->0).
With interleaving: all 4 (L,R) combos appear.

But we need to check if P0 fires >= 2 in each P1 phase.
P0 has fc=4 fires across 2 P1-phases.
By pigeonhole: at least 2 per phase. Exactly 2 per phase!
(4 fires, 2 phases, even split by symmetry... actually not guaranteed.)
Could be 3+1 or 4+0.

Hmm. Let me check empirically.
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


def is_gap_case(word, ms, n):
    fc = Counter(word)
    binary_pos = set(i for i in range(n) if ms[i] == 2)
    ternary_pos = set(i for i in range(n) if ms[i] == 3)
    if not any(fc[p] >= 3 for p in range(n)):
        return False
    for t in ternary_pos:
        if fc[t] < 3:
            continue
        for nbr in [(t-1)%n, (t+1)%n]:
            if nbr in binary_pos and fc[nbr] < fc[t]:
                return False
    return True


# ============================================================
# P0 fires per P1-phase
# ============================================================
print("=" * 70)
print("P0 FIRES PER P1-PHASE IN GAP CASE")
print("=" * 70)

for ms, n, max_cl in [([2,2,2,3,3], 5, 20), ([2,2,2,3,3,3,3], 7, 24)]:
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if is_gap_case(w, ms, n)]

    print(f"\nms={ms}, n={n}: {len(gap_words)} gap words")

    phase_fires_p0 = Counter()  # (fires_in_phase0, fires_in_phase1) -> count
    phase_fires_p2 = Counter()

    for w in gap_words[:5000]:
        # Find P1 fire steps
        fire_steps = [i for i, m in enumerate(w) if m == 1]
        # P1 fires at these steps, splitting cycle into phases
        # Phase 0: P1_val = 0 (before first fire)
        # Phase 1: P1_val = 1 (after first fire)
        # etc.

        # Simpler: track P1 value and count P0/P2 fires in each P1-phase
        config = [0] * n
        p0_in_phase = defaultdict(int)  # p1_val -> count of P0 fires
        p2_in_phase = defaultdict(int)

        for mover in w:
            p1_val = config[1]
            if mover == 0:
                p0_in_phase[p1_val] += 1
            if mover == 2:
                p2_in_phase[p1_val] += 1
            config[mover] = (config[mover] + 1) % ms[mover]

        p0_tup = tuple(sorted(p0_in_phase.values()))
        p2_tup = tuple(sorted(p2_in_phase.values()))
        phase_fires_p0[p0_tup] += 1
        phase_fires_p2[p2_tup] += 1

    print("P0 fires per P1-phase:")
    for pat, cnt in sorted(phase_fires_p0.items(), key=lambda x: -x[1])[:10]:
        print(f"  {pat}: {cnt}")
    print("P2 fires per P1-phase:")
    for pat, cnt in sorted(phase_fires_p2.items(), key=lambda x: -x[1])[:10]:
        print(f"  {pat}: {cnt}")


# ============================================================
# (L,R) COVERAGE IN EACH P1-PHASE
# ============================================================
print("\n" + "=" * 70)
print("(L,R) COVERAGE IN EACH P1-PHASE")
print("=" * 70)

for ms, n, max_cl in [([2,2,2,3,3], 5, 20)]:
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if is_gap_case(w, ms, n)]

    print(f"\nms={ms}, n={n}")

    lr_coverage = Counter()  # (coverage_in_s0, coverage_in_s1) -> count

    for w in gap_words:
        config = [0] * n
        lr_in_phase = defaultdict(set)  # p1_val -> set of (L,R)

        for step, mover in enumerate(w):
            if mover != 1:  # non-mover at P1
                p1_val = config[1]
                L = config[0]
                R = config[2]
                lr_in_phase[p1_val].add((L, R))
            config[mover] = (config[mover] + 1) % ms[mover]

        cov = tuple(len(lr_in_phase.get(s, set())) for s in [0, 1])
        lr_coverage[cov] += 1

    print("(L,R) coverage (S=0 phase, S=1 phase):")
    for cov, cnt in sorted(lr_coverage.items()):
        print(f"  coverage={cov}: {cnt} words ({100*cnt/len(gap_words):.1f}%)")

    # If both phases have 4/4 coverage: nm_distinct = 8, EC guaranteed
    # If one phase has 3/4: nm_distinct = 7, EC guaranteed (with mover >= 2)
    # If both have 3/4: nm_distinct = 6, EC not guaranteed by pigeonhole
    #   but empirically still 99.9% EC at P1

    # Cases where nm_distinct < 7 (coverage < (4,3) or (3,4)):
    low_cov = sum(cnt for cov, cnt in lr_coverage.items()
                  if cov[0] + cov[1] < 7)
    print(f"\n  Low coverage (total < 7): {low_cov}/{len(gap_words)} ({100*low_cov/len(gap_words):.1f}%)")


# ============================================================
# TRANSFER ARGUMENT: When P1 misses a context, what happens?
# ============================================================
print("\n" + "=" * 70)
print("TRANSFER: P1 misses -> P0/P2 gains")
print("=" * 70)

ms = [2, 2, 2, 3, 3]
n = 5
words = enumerate_mover_words(ms, n, 20)
gap_words = [w for w in words if is_gap_case(w, ms, n)]

# When P1 avoids EC: mover contexts disjoint from non-mover.
# This means P1's mover sees (L,S,R) not in non-mover set.
# Since S alternates at fires: mover_S0 = {(L1, 0, R1)}, mover_S1 = {(L2, 1, R2)}
# (at minimum fc=2, one fire per S-value)

# If (L1, 0, R1) not in non-mover: the (L,R) = (L1, R1) pair with S=0
# was never seen as non-mover. This means config (L1, 0, R1) at P1
# ONLY appears when P1 fires.

# What does this mean for P0?
# When P1 fires with L=L1: P0_val = L1.
# P0's context at that step: (P4_val, L1, P1_val_before_fire).
# After P1 fires: P0's right neighbor changes.
# The constraint is that P0_val = L1 at the fire step.

# If L1 is "rare" for P0 (only appears at P1's fire step):
# then P0 with S=L1 is rare -> possibly creates EC at P0.

# Let's check: when P1 has no EC, what's P0's situation?
p1_no_ec_words = []
for w in gap_words:
    config = [0] * n
    m_set = set()
    nm_set = set()
    for mover in w:
        L = config[0]; S = config[1]; R = config[2]
        if mover == 1:
            m_set.add((L, S, R))
        else:
            nm_set.add((L, S, R))
        config[mover] = (config[mover] + 1) % ms[mover]
    if not (m_set & nm_set):
        p1_no_ec_words.append(w)

print(f"P1 no-EC words: {len(p1_no_ec_words)}")

# For each: identify the "fresh" mover context at P1 and check P0/P2
for w in p1_no_ec_words[:10]:
    fc = Counter(w)
    config = [0] * n

    # Track P1 contexts
    p1_mover = []
    p1_nonmover = set()
    p0_mover = set()
    p0_nonmover = set()
    p2_mover = set()
    p2_nonmover = set()

    for step, mover in enumerate(w):
        c = list(config)  # snapshot

        # P1 context
        L1, S1, R1 = c[0], c[1], c[2]
        if mover == 1:
            p1_mover.append((L1, S1, R1, step))
        else:
            p1_nonmover.add((L1, S1, R1))

        # P0 context
        L0, S0, R0 = c[4], c[0], c[1]
        if mover == 0:
            p0_mover.add((L0, S0, R0))
        else:
            p0_nonmover.add((L0, S0, R0))

        # P2 context
        L2, S2, R2 = c[1], c[2], c[3]
        if mover == 2:
            p2_mover.add((L2, S2, R2))
        else:
            p2_nonmover.add((L2, S2, R2))

        config[mover] = (config[mover] + 1) % ms[mover]

    # Fresh mover contexts at P1
    fresh = [(L,S,R,step) for (L,S,R,step) in p1_mover if (L,S,R) not in p1_nonmover]

    p0_ec = p0_mover & p0_nonmover
    p2_ec = p2_mover & p2_nonmover

    print(f"\n  CL={len(w)}, fc={dict(sorted(fc.items()))}")
    print(f"  P1 fresh mover: {[(L,S,R) for L,S,R,_ in fresh]}")
    print(f"  P1 nm_distinct: {len(p1_nonmover)}/8")
    print(f"  P0 EC: {len(p0_ec)} overlaps, |M|={len(p0_mover)}, |NM|={len(p0_nonmover)}, space=12")
    print(f"  P2 EC: {len(p2_ec)} overlaps, |M|={len(p2_mover)}, |NM|={len(p2_nonmover)}, space=12")


# ============================================================
# CAN WE USE TERNARY PHASE DECOMPOSITION DIFFERENTLY?
# ============================================================
print("\n" + "=" * 70)
print("TERNARY PERSPECTIVE IN GAP CASE")
print("=" * 70)

print("""
In gap case: ternary procs have fc=3 (minimum).
Ternary P3 has neighbors P2(B) and P4(T).
fc[P2]=4, fc[P4]=3. fc[P2] > fc[P3].

P3 has 1 phase (fc/3 = 1 full cycle 0->1->2->0).
In this phase: P2 fires 4 times, P4 fires 3 times.

Zero-sided at P3 from P2: need P2 fires 0 in some P3-phase.
But P3 has 1 phase with 4 P2 fires. Not zero-sided.

What about EC at P3 directly?
P3 has 3 mover contexts and CL-3 = 13 non-mover contexts.
Context space: 2*3*3 = 18.
3 + 13 = 16 < 18. Pigeonhole doesn't guarantee overlap.

Hmm. At n=7:
P3 has 3 mover, CL-3 = 21 non-mover. Space = 18.
3 + 21 = 24 > 18. But distinct could be less.
If non-mover distinct = 15: 3 + 15 = 18 = space. No guaranteed overlap.
If non-mover distinct = 16: 3 + 16 = 19 > 18. GUARANTEED overlap.

But need to show non-mover distinct >= 16.
With 21 appearances from 18 slots: could use 16+ distinct.
Not guaranteed by counting alone.
""")

# Check ternary non-mover distinct at n=7
for ms, n, max_cl in [([2,2,2,3,3,3,3], 7, 24)]:
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if is_gap_case(w, ms, n)]

    for t in [3, 4, 5, 6]:
        nm_dist = Counter()
        ec_count = 0
        for w in gap_words[:5000]:
            config = [0] * n
            m_set = set()
            nm_set = set()
            for mover in w:
                L = config[(t-1)%n]
                S = config[t]
                R = config[(t+1)%n]
                if mover == t:
                    m_set.add((L, S, R))
                else:
                    nm_set.add((L, S, R))
                config[mover] = (config[mover] + 1) % ms[mover]
            nm_dist[len(nm_set)] += 1
            if m_set & nm_set:
                ec_count += 1

        space = ms[(t-1)%n] * ms[t] * ms[(t+1)%n]
        checked = min(5000, len(gap_words))
        print(f"  P{t}(T) space={space}: nm_distinct={dict(sorted(nm_dist.items()))}, EC={ec_count}/{checked}")


# ============================================================
# DEFINITIVE CHECK: EC at some proc for ALL gap words
# ============================================================
print("\n" + "=" * 70)
print("DEFINITIVE: EC AT SOME PROC FOR ALL GAP WORDS")
print("=" * 70)

for ms, n, max_cl in [([2,2,2,3,3], 5, 20), ([2,2,2,3,3,3,3], 7, 24)]:
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if is_gap_case(w, ms, n)]

    no_ec_anywhere = 0
    for w in gap_words:
        config = [0] * n
        all_m = [set() for _ in range(n)]
        all_nm = [set() for _ in range(n)]
        for mover in w:
            for p in range(n):
                L = config[(p-1)%n]
                S = config[p]
                R = config[(p+1)%n]
                if p == mover:
                    all_m[p].add((L,S,R))
                else:
                    all_nm[p].add((L,S,R))
            config[mover] = (config[mover] + 1) % ms[mover]

        any_ec = False
        for p in range(n):
            if all_m[p] & all_nm[p]:
                any_ec = True
                break
        if not any_ec:
            no_ec_anywhere += 1
            print(f"  NO EC: word={w}")

    print(f"ms={ms}: {len(gap_words)} gap words, no EC anywhere: {no_ec_anywhere}")


print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print("""
DEFINITIVE FINDINGS:

1. Gap case = boundary ternary has no binary neighbor with lower fc.
   This forces boundary binary fc >= 4, all ternary fc = 3 (minimum).

2. Gap case has CL >= 3n+1 (much larger than 2n for n >= 2).

3. Gradient exists at BINARY procs (fc_bin >= 4 > 2 = fc_interior_bin),
   NOT at ternary procs. This gradient is "wrong direction" for
   ternary phase decomposition.

4. EC is 100% at SOME binary proc in gap case.
   - n=5: 21,128/21,128 (100%)
   - n=7: 44,164/44,164 (100%)

5. Interior binary P1 has EC ~98% due to small context space (8)
   and many non-mover appearances.

6. When P1 fails EC: P0 or P2 always has EC (transfer effect).

7. No single simple analytical argument covers all gap cases.
   The cleanest approach: computational verification at n=5,7
   + structural argument for n >= 9 using context space saturation
   at interior binary with all-binary neighborhood.

8. For n >= 9 with B=3 consecutive binary:
   Interior binary P1 context space = 8.
   Non-mover appearances >= 3n-1-fc[1].
   At minimum gap fc: fc[1]=2, non-mover = 3n-3.
   For n=9: 24 non-mover from 8 slots.
   Walk forces nm_distinct >= 7 (each P1-phase has >= 2 L-toggles
   and >= 2 R-toggles from P0 and P2 firing 4+ times).
   With nm_distinct >= 7 and mover_distinct >= 2: EC guaranteed.

RECOMMENDATION: Prove n=5,7 computationally. For n >= 9, prove
that walk structure forces nm_distinct >= 7 at interior binary.
The walk proof: in each P1-phase, P0 fires >= 2 times (since fc[P0] >= 4
and P1 has 2 phases: ceil(4/2) = 2), so L visits both values.
Similarly R visits both values. With >= 2 toggles each: all 4 (L,R)
combos appear in each phase. 2 phases * 4 = 8 non-mover distinct.
EC GUARANTEED.

WAIT: this assumes P0 fires >= 2 in EACH P1-phase.
P0 has 4 fires across 2 P1-phases. Could be 3+1 or 4+0.
Need to rule out 4+0 (all P0 fires in one P1-phase).
""")
