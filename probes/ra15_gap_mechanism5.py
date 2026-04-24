#!/usr/bin/env python3
"""
RA15 Part 5: THE KEY DISCOVERY

From Part 4 Check 3-4: EVERY ZW cycle has SOME gradient somewhere.
There is NO cycle where all procs with fc>=3 have all neighbors with fc>=fc.

This means: the gap case (no gradient at boundary ternary with binary neighbor)
ALWAYS has a gradient at some OTHER proc.

The gradient might be:
  (a) At a binary proc with fc>=4, neighbor with fc < fc_bin
  (b) At a ternary proc with a ternary neighbor with lower fc
  (c) At some other configuration

If the gradient is at a BINARY proc: can we do phase decomposition there?
A binary proc with fc=4 has 2 phases. If neighbor has fc=2: pigeonhole
gives ceil(2/2) = 1 per phase. No zero-sided.

BUT WAIT: maybe the argument doesn't need zero-sided phases.
Maybe the gradient + high CL is enough for EC directly.

Let me find WHERE the gradient is in gap cases and what type.
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
# FIND ALL GRADIENTS IN GAP CASE
# ============================================================
print("=" * 70)
print("WHERE IS THE GRADIENT IN GAP CASE?")
print("=" * 70)

for ms, n, max_cl in [([2,2,2,3,3], 5, 20), ([2,2,2,3,3,3,3], 7, 24)]:
    binary_pos = set(i for i in range(n) if ms[i] == 2)
    ternary_pos = set(i for i in range(n) if ms[i] == 3)

    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if is_gap_case(w, ms, n)]

    print(f"\nms={ms}, n={n}: {len(gap_words)} gap words")

    gradient_types = Counter()
    gradient_procs = Counter()

    for w in gap_words:
        fc = Counter(w)
        for p in range(n):
            if fc[p] < 3:
                continue
            for nbr in [(p-1)%n, (p+1)%n]:
                if fc[nbr] < fc[p]:
                    p_type = 'B' if ms[p] == 2 else 'T'
                    n_type = 'B' if ms[nbr] == 2 else 'T'
                    gradient_types[(p_type, n_type, fc[p], fc[nbr])] += 1
                    gradient_procs[p] += 1

    print("  Gradient types (proc_type, nbr_type, fc_proc, fc_nbr):")
    for key, cnt in sorted(gradient_types.items(), key=lambda x: -x[1]):
        print(f"    {key}: {cnt}")
    print("  Gradient at procs:")
    for p, cnt in sorted(gradient_procs.items()):
        print(f"    P{p}({'B' if ms[p]==2 else 'T'}): {cnt}")


# ============================================================
# KEY INSIGHT: The gradient is always at a BINARY proc
# ============================================================
print("\n" + "=" * 70)
print("GRADIENT ALWAYS AT BINARY PROC IN GAP CASE?")
print("=" * 70)

for ms, n, max_cl in [([2,2,2,3,3], 5, 20), ([2,2,2,3,3,3,3], 7, 24)]:
    binary_pos = set(i for i in range(n) if ms[i] == 2)
    words = enumerate_mover_words(ms, n, max_cl)
    gap_words = [w for w in words if is_gap_case(w, ms, n)]

    gradient_at_binary = 0
    gradient_only_ternary = 0
    no_gradient = 0

    for w in gap_words:
        fc = Counter(w)
        has_bin_grad = False
        has_ter_grad = False
        for p in range(n):
            if fc[p] < 3:
                continue
            for nbr in [(p-1)%n, (p+1)%n]:
                if fc[nbr] < fc[p]:
                    if p in binary_pos:
                        has_bin_grad = True
                    else:
                        has_ter_grad = True
        if has_bin_grad:
            gradient_at_binary += 1
        elif has_ter_grad:
            gradient_only_ternary += 1
        else:
            no_gradient += 1

    print(f"ms={ms}: {len(gap_words)} gap, bin_grad={gradient_at_binary}, ter_only_grad={gradient_only_ternary}, no_grad={no_gradient}")


# ============================================================
# THE PROOF STRUCTURE
# ============================================================
print("\n" + "=" * 70)
print("THE PROOF STRUCTURE")
print("=" * 70)

print("""
Gap case (no gradient at ternary-with-binary-neighbor):
  For every boundary ternary t, all adjacent binary b have fc_b >= fc_t.

Since binary fc is even and fc_t >= 3: fc_b >= 4.
Extra fires: fc_b - 2 >= 2 at each boundary binary.
The extra fires go ONLY to binary procs (verified computationally).
Ternary procs stay at fc_t = 3 (minimum).

In gap case, boundary binary P0 has fc=4 and neighbor P1 has fc=2.
So fc[P0] = 4 > 2 = fc[P1]. GRADIENT AT P0.

But P0 is binary. How does this gradient help?

P0 has fc=4 and P1 has fc=2. The fc_P1=2 fires are distributed
across fc_P0/2 = 2 binary-phases of P0.
Pigeonhole: ceil(2/2) = 1 per phase. Every phase has at least 1 P1 fire.
No zero-sided phase at P0 via P1.

What about P1 as the target?
P1 has fc=2 and P0 has fc=4.
P0's fires across P1's 1 binary-phase: 4 fires in 1 phase.
Every phase has fires. Not useful.

But wait: the gradient is at P0 (high) toward P1 (low).
The USEFUL gradient is high-fc proc with low-fc NEIGHBOR.
Phase decomposition: the HIGH-fc proc has many phases.
The LOW-fc neighbor has few fires distributed across many phases.
If fewer fires than phases: zero-sided exists.

P0 has 2 phases. P1 has 2 fires. Not fewer.
NOT helpful for zero-sided.

However: at n=7 gap case with fc=[4,4,4,3,3,3,3]:
  P0(B) fc=4, P6(T) fc=3. Gradient at P0 toward P6? No: fc[6]=3 < 4=fc[0].
  P0 has 2 phases. P6 has 3 fires across 2 phases. ceil(3/2)=2 each.
  No zero-sided.

  P0(B) fc=4, P1(B) fc=4. No gradient.

  ALL three binary procs have fc=4. NO gradient between them.
  Ternary procs have fc=3. Gradient: P0(4) > P6(3), P2(4) > P3(3).
  But these are binary-ternary gradients where binary has MORE fires.
  Phase decomp at P0: 2 phases, P6 fires 3 times: no zero-sided.

So the gradient in gap case is ALWAYS "wrong direction" for
zero-sided phases: binary has more fires than ternary, so
ternary can't have zero-sided phase at binary's position.

THIS MEANS: gap case can't use phase argument at all.
Must use direct EC.

Let me verify: EC is 100% anyway. So the gap case proof must be
different from the main gradient+phase proof.
""")

# ============================================================
# REFINED QUESTION: Why is EC 100% in gap case?
# ============================================================
print("=" * 70)
print("WHY IS EC 100% IN GAP CASE?")
print("=" * 70)

print("""
Observation: in gap case, ALL extra fires go to binary procs.
This makes binary procs fire a LOT relative to their small state space.

At n=5: binary fires = [4, 2, 4] = 10 fires. CL = 16.
Binary procs contribute 10/16 = 62.5% of all steps.

At n=7: binary fires = [4, 4, 4] = 12 fires. CL = 24.
Binary procs contribute 12/24 = 50% of all steps.

Each binary proc p sees CL total contexts (mover + non-mover).
Context space at p: ms[left] * ms[p] * ms[right].
For interior binary P1 at n=5: 2*2*2 = 8.

Total contexts = CL = 16. Context space = 8.
Average occupancy: 16/8 = 2.0.

But these 16 split into 2 mover + 14 non-mover.
For EC: need mover and non-mover to share a context.

The question is whether the walk structure prevents overlap.
Empirically: 98.3% of gap words at n=5 have EC at P1.
The remaining 1.7% have EC at P0 or P2.

The collective argument: across 3 binary procs,
total contexts = 3*CL = 48 (not independent, but...).
Total context space = 8 + 12 + 12 = 32 at n=5 (or similar).

Not immediately useful since contexts at different procs aren't comparable.

BETTER: the walk structure constrains ALL procs simultaneously.
When binary cluster is dense (many fires), neighboring procs'
contexts are coupled. A "fresh" mover context at P1 forces
specific values at P0 and P2, creating opportunities for EC there.
""")

# ============================================================
# QUANTITATIVE: How constrained is the walk?
# ============================================================
print("=" * 70)
print("WALK CONSTRAINTS: adjacent fire steps")
print("=" * 70)

ms = [2, 2, 2, 3, 3]
n = 5
words = enumerate_mover_words(ms, n, 20)
gap_words = [w for w in words if is_gap_case(w, ms, n)]

# For each gap word, look at consecutive fire steps
# In the ring walk, each step fires a neighbor of the previous mover.
# So consecutive movers are adjacent on the ring.

# When two consecutive binary procs fire (e.g., P0 then P1),
# P0's fire changes P1's context (P1's L changes).
# And P1's fire changes P0's context (P0's R changes).

# Count: how often do consecutive fires stay in binary cluster?
binary_cluster_runs = Counter()
for w in gap_words[:2000]:
    run = 0
    for mover in w:
        if ms[mover] == 2:
            run += 1
        else:
            if run > 0:
                binary_cluster_runs[run] += 1
            run = 0
    if run > 0:
        binary_cluster_runs[run] += 1

print(f"Consecutive binary fire runs (first 2000 gap words):")
for r, cnt in sorted(binary_cluster_runs.items()):
    print(f"  run length {r}: {cnt}")


# ============================================================
# THE CLEANEST ARGUMENT
# ============================================================
print("\n" + "=" * 70)
print("CLEANEST ARGUMENT SEARCH")
print("=" * 70)

print("""
After all analysis, the cleanest argument for gap case seems to be:

ARGUMENT 1: CL is large relative to binary context space.
  In gap case, CL >= sum(ms) + 4.
  For B=3 consecutive binary: CL >= 3n - 3 + 4 = 3n + 1.
  Interior binary P1 has context space 2*2*2 = 8.
  P1 sees CL total contexts. Need CL > 2 * ctx_space = 16 for guaranteed EC.
  At n=5: CL=16 >= 16. Borderline.
  At n=7: CL=24 > 16. Guaranteed.

Wait, why CL > 2*ctx_space? Because:
  mover contexts: fc_p values from ctx_space slots
  non-mover contexts: CL - fc_p values from ctx_space slots
  If fc_p + (CL - fc_p - ctx_space) > 0, i.e., CL > ctx_space + fc_p,
  then non-mover uses more than (ctx_space - fc_p) slots,
  so non-mover uses at least ctx_space - fc_p + 1 slots.
  Then mover_distinct + nonmover_distinct >= fc_p + (ctx_space - fc_p + 1) = ctx_space + 1 > ctx_space.
  OVERLAP GUARANTEED.

Actually that's wrong. Let me think more carefully.

Non-mover has (CL - fc_p) appearances. Each is one of ctx_space contexts.
Non-mover distinct: at most min(CL - fc_p, ctx_space).
Mover distinct: at most min(fc_p, ctx_space).

For overlap: need mover_distinct + nonmover_distinct > ctx_space.
  Sufficient: nonmover_distinct > ctx_space - mover_distinct.
  Since nonmover_distinct >= ceil((CL - fc_p) / max_repeat)... not helpful.

Actually, the right condition is:
  nonmover_distinct >= ctx_space - fc_p + 1
  (non-mover fills all but fc_p - 1 slots, so mover can't avoid it)

When does nonmover_distinct = ctx_space - k?
  If non-mover misses k contexts. With (CL - fc_p) appearances from ctx_space slots.
  Non-mover can miss at most ctx_space - 1 contexts (uses at least 1).
  But with many appearances, it's unlikely to miss many.

The walk constrains which contexts are reachable.
Let me just check: at n=7, is CL large enough for pure pigeonhole at P1?

P1 at n=7 gap: fc=4, CL=24, ctx_space=8.
Non-mover appearances: 24-4 = 20 from 8 slots.
Non-mover distinct: between 1 and 8.
Mover distinct: between 1 and 4.

By pigeonhole on non-mover: 20 appearances, 8 slots -> ALL 8 used.
Wait: 20 >= 8 doesn't guarantee all 8 used!
Example: 20 appearances all in 3 slots.

But the WALK constrains this. Binary proc P1's neighbors are P0 and P2.
Both fire 4 times each. P0's value toggles 0-1-0-1-0.
P2's value toggles 0-1-0-1-0.

P1's non-mover context is (P0_val, P1_val, P2_val).
P1_val is fixed between P1's fires.
In each P1-phase: P0 toggles multiple times, P2 toggles multiple times.

If P0 fires k times in a P1-phase: P0's value changes k times.
P0 takes values from {0, 1}. After k toggles: both values seen (if k >= 1).
Similarly P2.

So in each P1-phase: L takes both values, R takes both values.
But do all 4 (L,R) combos appear? Not necessarily.
The (L,R) values depend on the interleaving of P0 and P2 fires.
""")

# Check: in gap case at n=7, how many distinct non-mover contexts at P1?
ms7 = [2,2,2,3,3,3,3]
n7 = 7
words7 = enumerate_mover_words(ms7, n7, 24)
gap7 = [w for w in words7 if is_gap_case(w, ms7, n7)]

p1_nm7 = Counter()
for w in gap7:
    fc = Counter(w)
    config = [0] * n7
    nm_set = set()
    for mover in w:
        if mover != 1:
            L = config[0]
            S = config[1]
            R = config[2]
            nm_set.add((L, S, R))
        config[mover] = (config[mover] + 1) % ms7[mover]
    p1_nm7[len(nm_set)] += 1

print(f"\nn=7 P1 nonmover distinct: {dict(sorted(p1_nm7.items()))}")
total = sum(p1_nm7.values())
ge7 = sum(v for k,v in p1_nm7.items() if k >= 7)
print(f"  nm_distinct >= 7: {ge7}/{total} ({100*ge7/total:.1f}%)")
print(f"  nm_distinct = 8 (all): {p1_nm7.get(8, 0)}/{total}")

# For nm_distinct < 7 at n=7: does P1 still have EC?
p1_ec_by_nm7 = defaultdict(lambda: [0,0])
for w in gap7:
    config = [0] * n7
    m_set = set()
    nm_set = set()
    for mover in w:
        L = config[0]
        S = config[1]
        R = config[2]
        if mover == 1:
            m_set.add((L, S, R))
        else:
            nm_set.add((L, S, R))
        config[mover] = (config[mover] + 1) % ms7[mover]
    has_ec = len(m_set & nm_set) > 0
    p1_ec_by_nm7[len(nm_set)][0 if has_ec else 1] += 1

print(f"\nn=7 P1 EC by nonmover_distinct:")
for nd in sorted(p1_ec_by_nm7.keys()):
    ec, no_ec = p1_ec_by_nm7[nd]
    print(f"  nm_distinct={nd}: EC={ec}, no_EC={no_ec}")


# ============================================================
# THE SIMPLEST UNIVERSAL ARGUMENT
# ============================================================
print("\n" + "=" * 70)
print("SIMPLEST UNIVERSAL ARGUMENT")
print("=" * 70)

print("""
THEOREM (Gap Case EC):
In the gap case with B >= 3 consecutive binary procs at positions 0..B-1:
  - All boundary binary have fc >= 4 (even)
  - Interior binary have fc >= 2 (even)
  - CL >= sum(ms) + 4

EC is guaranteed at SOME binary proc.

PROOF SKETCH (computational basis + structural observation):

1. At n=5: verified 21,128 gap words, 100% EC at some binary proc.
2. At n=7: verified 44,164 gap words, 100% EC at some binary proc.

3. For n >= 7: interior binary P1 has context space 8 (all-binary neighborhood).
   In gap case with fc pattern [4, >=2, 4, 3, ..., 3]:
   P1 sees CL = 3n - B + 4 + extra total contexts.
   For n >= 7 with B=3: CL >= 22.
   Non-mover: CL - fc[1] >= 22 - 4 = 18 appearances from 8 slots.

   Walk constraint: P0 and P2 each fire >= 4 times during P1's non-mover steps.
   This means L and R each toggle >= 4 times.
   In EACH P1-phase (where P1_val is fixed), both L and R toggle >= 1 time.

   Claim: with enough toggles, non-mover covers >= 7 of 8 contexts.
   Then with mover distinct >= 2: EC guaranteed (7 + 2 > 8).

4. The remaining cases (n <= 6, or low nm_distinct) are handled by
   the combined binary cluster argument: if P1 misses EC, the
   specific walk structure forces EC at P0 or P2.

This is NOT a clean analytical argument yet. The gap case remains
the hardest part of the CL <= 2n proof.

ALTERNATIVE APPROACH: maybe prove gap case directly via the
Universal Entry Conflict theorem (already proved for non-adjacent binary).
The gap case has consecutive binary, so UEC doesn't apply directly.
But the mechanism might be similar.
""")

print("\n" + "=" * 70)
print("DONE")
print("=" * 70)
