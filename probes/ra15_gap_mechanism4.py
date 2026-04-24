#!/usr/bin/env python3
"""
RA15 Part 4: Final gap mechanism analysis.

Key findings so far:
1. Gap case at n=5: 100% EC, always at some binary proc
2. Gap case at n=7: 100% EC (5000/5000 sampled), always at some binary
3. P1 alone: ~98% EC. When P1 fails, P0 or P2 picks up.
4. EC happens at nm_distinct >= 7 for P1 (guaranteed).
   Even at nm_distinct=4,5,6 it usually happens (mover hits occupied slot).

The question: is "some binary proc has EC" provable?

Approach: in gap case, every binary proc b has fc_b >= 2.
For ANY proc p, total appearances = CL.
Mover appearances = fc_p. Non-mover = CL - fc_p.

Key insight to test: over ALL binary procs collectively,
the total binary mover contexts + total binary non-mover contexts
must overlap SOMEWHERE.

Alternative: direct proof that CL > ctx_space at some proc.

Let me also check: is the fc pattern always the same at n=7?
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
# CHECK 1: FC patterns in gap case
# ============================================================
print("=" * 70)
print("CHECK 1: FC patterns in gap case at n=5 and n=7")
print("=" * 70)

ms5 = [2, 2, 2, 3, 3]
n5 = 5
words5 = enumerate_mover_words(ms5, n5, 20)
gap5 = [w for w in words5 if is_gap_case(w, ms5, n5)]

fc_pats5 = Counter()
for w in gap5:
    fc = Counter(w)
    pat = tuple(fc[p] for p in range(n5))
    fc_pats5[pat] += 1

print(f"n=5, ms={ms5}: {len(gap5)} gap words")
print("FC patterns:")
for pat, cnt in sorted(fc_pats5.items()):
    cl = sum(pat)
    print(f"  fc={pat}, CL={cl}: {cnt} words")

ms7 = [2, 2, 2, 3, 3, 3, 3]
n7 = 7
words7 = enumerate_mover_words(ms7, n7, 24)
gap7 = [w for w in words7 if is_gap_case(w, ms7, n7)]

fc_pats7 = Counter()
for w in gap7:
    fc = Counter(w)
    pat = tuple(fc[p] for p in range(n7))
    fc_pats7[pat] += 1

print(f"\nn=7, ms={ms7}: {len(gap7)} gap words")
print("FC patterns:")
for pat, cnt in sorted(fc_pats7.items()):
    cl = sum(pat)
    print(f"  fc={pat}, CL={cl}: {cnt} words")


# ============================================================
# CHECK 2: EC at ALL binary vs at SOME binary
# ============================================================
print("\n" + "=" * 70)
print("CHECK 2: EC at SOME binary proc (universal check)")
print("=" * 70)

for label, gap_words, ms, n in [("n=5", gap5, ms5, n5), ("n=7", gap7, ms7, n7)]:
    binary_pos = [i for i in range(n) if ms[i] == 2]
    total = len(gap_words)
    some_bin_ec = 0
    all_ec = 0
    no_ec = 0

    for w in gap_words:
        contexts = get_contexts(w, ms, n)
        has_bin_ec = False
        has_any_ec = False
        for p in range(n):
            m = set()
            nm = set()
            for (L, S, R, im) in contexts[p]:
                (m if im else nm).add((L, S, R))
            if m & nm:
                has_any_ec = True
                if p in binary_pos:
                    has_bin_ec = True
        if has_bin_ec:
            some_bin_ec += 1
        if has_any_ec:
            all_ec += 1
        else:
            no_ec += 1

    print(f"{label}: {total} gap words")
    print(f"  Any EC: {all_ec}/{total}")
    print(f"  Some binary EC: {some_bin_ec}/{total}")
    print(f"  No EC at all: {no_ec}")


# ============================================================
# CHECK 3: The argument for gap case
# ============================================================
print("\n" + "=" * 70)
print("CHECK 3: Why does gap case have EC?")
print("=" * 70)

print("""
In gap case:
  - fc_bin >= fc_ter >= 3 at all boundary pairs
  - CL = sum(fc) >= sum(ms) + 4 (extra 2 per boundary binary)
  - Every binary proc has fc >= 2 (even)
  - Boundary binary procs have fc >= 4

THE KEY OBSERVATION:
  In gap case, the boundary binary procs have HIGH fc.
  This means they fire many times -> many mover contexts.
  Combined with large CL, contexts repeat.

But the truly clean argument might be different.
Let me check: is there a ternary-ternary gradient that works instead?

In gap case: fc_bin >= fc_ter at binary-ternary boundaries.
But what about ternary-ternary boundaries?
If some ternary t has a ternary neighbor t' with fc[t'] < fc[t],
then the gradient argument works AT (t, t').
The gradient doesn't need a BINARY neighbor - it needs ANY neighbor
with lower fc!

Let me check: in gap case, does some ternary have a TERNARY neighbor
with strictly lower fc?
""")

for label, gap_words, ms, n in [("n=5", gap5, ms5, n5), ("n=7", gap7, ms7, n7)]:
    ternary_pos = set(i for i in range(n) if ms[i] == 3)

    has_ter_gradient = 0
    for w in gap_words:
        fc = Counter(w)
        found = False
        for t in ternary_pos:
            if fc[t] < 3:
                continue
            L = (t-1) % n
            R = (t+1) % n
            # Check ternary neighbors
            for nbr in [L, R]:
                if ms[nbr] >= 2 and fc[nbr] < fc[t]:  # ANY neighbor with lower fc
                    found = True
                    break
            if found:
                break
        if found:
            has_ter_gradient += 1

    print(f"\n{label}: {len(gap_words)} gap words")
    print(f"  Has ANY neighbor with lower fc at some fc>=3 proc: {has_ter_gradient}/{len(gap_words)}")

    # More refined: gap is about binary-ternary. What about ANY proc pair?
    has_any_gradient = 0
    for w in gap_words:
        fc = Counter(w)
        found = False
        for p in range(n):
            if fc[p] < 3:
                continue
            L = (p-1) % n
            R = (p+1) % n
            for nbr in [L, R]:
                if fc[nbr] < fc[p]:
                    found = True
                    break
            if found:
                break
        if found:
            has_any_gradient += 1

    print(f"  Has ANY gradient (fc[nbr] < fc[p] for some p with fc>=3): {has_any_gradient}/{len(gap_words)}")


# ============================================================
# CHECK 4: Refined gap - NO gradient anywhere
# ============================================================
print("\n" + "=" * 70)
print("CHECK 4: Cycles with NO gradient at ANY proc pair")
print("=" * 70)

print("""
Refined gap: for ALL procs p with fc[p] >= 3, ALL neighbors nbr have
fc[nbr] >= fc[p]. This means no gradient exists ANYWHERE.

Does this case even exist?
""")

for label, all_words, ms, n in [("n=5", words5, ms5, n5), ("n=7", words7, ms7, n7)]:
    no_gradient = 0
    no_gradient_words = []
    for w in all_words:
        fc = Counter(w)
        if not any(fc[p] >= 3 for p in range(n)):
            continue
        found_gradient = False
        for p in range(n):
            if fc[p] < 3:
                continue
            for nbr in [(p-1)%n, (p+1)%n]:
                if fc[nbr] < fc[p]:
                    found_gradient = True
                    break
            if found_gradient:
                break
        if not found_gradient:
            no_gradient += 1
            if len(no_gradient_words) < 10:
                no_gradient_words.append(w)

    print(f"\n{label}: {len(all_words)} total words (with fc>=3)")
    print(f"  No gradient anywhere: {no_gradient}")

    if no_gradient_words:
        for w in no_gradient_words[:5]:
            fc = Counter(w)
            fc_str = {p: fc[p] for p in range(n)}
            print(f"    CL={len(w)}, fc={fc_str}")
            # Check EC
            contexts = get_contexts(w, ms, n)
            ec_procs = []
            for p in range(n):
                m = set()
                nm = set()
                for (L, S, R, im) in contexts[p]:
                    (m if im else nm).add((L, S, R))
                if m & nm:
                    ec_procs.append(p)
            print(f"    EC at: {ec_procs}")


# ============================================================
# CHECK 5: Even more refined - ALL fc equal
# ============================================================
print("\n" + "=" * 70)
print("CHECK 5: Cycles where ALL procs have fc = ms[p] (minimum)")
print("=" * 70)

print("""
If all procs fire exactly ms[p] times: CL = sum(ms).
For this to be ZW (CL > 2n): need sum(ms) > 2n.
  n=5: sum(ms) = 12 > 10. YES.
  n=7: sum(ms) = 18 > 14. YES.

At minimum fc: every ternary has fc=3, binary has fc=2.
fc[binary] = 2 < 3 = fc[ternary] at boundary.
So gradient ALWAYS exists at minimum fc.

For no gradient: need fc[binary] >= 3 at boundaries.
Since binary fc is even: fc[binary] >= 4 at boundaries.
This means CL >= sum(ms) + 4.

But then CL = sum(ms) + excess where excess >= 4.
These extra fires go to SOME procs.
If they go to binary: fc stays >= for gap.
If they go to ternary: fc_ter increases, breaking gap (fc_bin < new fc_ter).

So gap forces: the EXTRA fires beyond minimum go to binary procs.
""")

# Check: in gap case, where do extra fires go?
for label, gap_words, ms, n in [("n=5", gap5, ms5, n5), ("n=7", gap7, ms7, n7)]:
    binary_pos = set(i for i in range(n) if ms[i] == 2)
    extra_at_binary = Counter()
    extra_at_ternary = Counter()
    for w in gap_words[:1000]:
        fc = Counter(w)
        for p in range(n):
            extra = fc[p] - ms[p]
            if extra > 0:
                if p in binary_pos:
                    extra_at_binary[extra] += 1
                else:
                    extra_at_ternary[extra] += 1

    print(f"\n{label}: extra fires beyond minimum")
    print(f"  At binary procs: {dict(sorted(extra_at_binary.items()))}")
    print(f"  At ternary procs: {dict(sorted(extra_at_ternary.items()))}")


# ============================================================
# CHECK 6: RETURN to original question - precise gap condition
# ============================================================
print("\n" + "=" * 70)
print("CHECK 6: Does gap need ALL boundary or just SOME?")
print("=" * 70)

print("""
The gap case is defined as: for ALL boundary ternary t,
ALL adjacent binary b have fc_b >= fc_t.

The gradient argument says: if SOME boundary ternary t has SOME adjacent
binary b with fc_b < fc_t, then zero-sided phase exists at t.

So the gap is exactly the complement of the gradient condition.

In gap case at n=5:
  fc = [4, 2, 4, 3, 3].
  Boundary: (P3, P2) and (P4, P0).
  fc[2]=4 >= fc[3]=3: gap holds.
  fc[0]=4 >= fc[4]=3: gap holds.

  BUT: P3 also has neighbor P4 (ternary, fc=3 = fc[3]).
  P4 has neighbor P3 (ternary, fc=3 = fc[4]).
  No ternary-ternary gradient either.

  AND P0 has neighbor P1 (binary, fc=2).
  fc[1]=2 < fc[0]=4. GRADIENT EXISTS at P0!
  But P0 is binary, not ternary. The phase argument works at TERNARY procs.

Wait - the gradient argument specifically needs a ternary proc t
with fc[nbr] < fc[t]. P0 is binary. The phase decomposition is
for ternary procs only.

So the gradient at (P0, P1) doesn't help because P0 is binary.

NEW QUESTION: Can we extend the phase argument to binary procs?
A binary proc with fc=4 has 2 "phases" (0->1 and 1->0).
If some neighbor fires 0 times in one of these phases -> zero-sided.
With fc_nbr < fc_bin and fc_bin=4 (2 phases): fc_nbr < 4.
fc_nbr could be 2 or 3.
If fc_nbr = 2: 2 fires across 2 phases. COULD be 1+1. Not zero-sided.
If fc_nbr = 3: 3 fires across 2 phases. Min = 1. Not zero-sided.
If fc_nbr = 1: 1 fire across 2 phases. YES, zero-sided!
But minimum fc is 2 (binary) or 3 (ternary). So fc_nbr >= 2.

Binary phase argument: fc_bin has fc_bin/2 phases. Need fc_nbr < fc_bin/2.
With fc_bin=4: need fc_nbr < 2. But fc_nbr >= 2. FAILS.
With fc_bin=6: need fc_nbr < 3. But fc_nbr >= 2. So need fc_nbr = 2.
  If binary nbr with fc=2: 2 < 3 phases. Zero-sided!
  If ternary nbr with fc=3: 3 >= 3. Not zero-sided.

So for binary phases, the zero-sided argument at binary proc b works
when fc_bin >= 6 and some binary neighbor has fc = 2.
""")


# ============================================================
# CHECK 7: THE REAL MECHANISM - EC directly
# ============================================================
print("\n" + "=" * 70)
print("CHECK 7: Direct EC mechanism at binary proc with fc >= 4")
print("=" * 70)

print("""
Forget phases. Let's think about EC directly.

Binary proc b, fc_b = 4, CL = 16.
b fires at steps t1, t2, t3, t4.
At each fire step: mover context (L, S, R).
S alternates: 0, 1, 0, 1.

Between fires, b is non-mover. Its S is fixed in each gap.
Gap 1 (after t1, before t2): S = 1 (just fired 0->1).
Gap 2 (after t2, before t3): S = 0 (just fired 1->0).
Gap 3 (after t3, before t4): S = 1 (just fired 0->1).
Gap 4 (after t4, wrap to t1): S = 0 (just fired 1->0).

Mover contexts with S=0: at t1, t3.
Mover contexts with S=1: at t2, t4.

Non-mover with S=0: in gaps 2, 4.
Non-mover with S=1: in gaps 1, 3.

For EC with S=0: need (L, 0, R) at t1 or t3 to equal some
non-mover (L, 0, R) in gap 2 or gap 4.

For EC with S=1: need (L, 1, R) at t2 or t4 to equal some
non-mover (L, 1, R) in gap 1 or gap 3.

The non-mover contexts in each gap depend on what neighbors do.
In gap 1: b's value is 1 (fixed). Neighbors fire and change.
The (L, R) values seen in gap 1 depend on how neighbors move.

KEY: the (L, R) value JUST BEFORE b fires is the MOVER context.
The (L, R) value JUST AFTER b fires is the FIRST non-mover context
of the next gap.

After b fires at t1 (0->1), the config is:
  L = L(t1), R = R(t1) (unchanged by b's fire).
So the first non-mover in gap 1 has (L(t1), 1, R(t1)).
And the mover at t2 has (L(t2), 1, R(t2)).

EC at S=1 between gap 1's first non-mover and t2's mover:
  (L(t1), 1, R(t1)) vs (L(t2), 1, R(t2)).
  EC iff L(t1) = L(t2) and R(t1) = R(t2).
  i.e., the L and R values haven't changed between t1 and t2.

This happens iff neither neighbor fires between t1 and t2.
But gap 1 has some steps where neighbors fire.
Actually: L(t1) is the value BEFORE b fires at t1.
After b fires, neighbors may fire and change L and R.
The first non-mover of gap 1 sees the config AFTER b's fire.

Wait, let me reconsider. At step t1:
  Config before: (..., L, 0, R, ...)
  b fires: config becomes (..., L, 1, R, ...)
  Next step (t1+1): some other proc fires.
  Non-mover context of b at step t1+1:
    L' might have changed (if left neighbor fired), R' too.
    b's value is still 1.
    Context: (L', 1, R').

So the first non-mover after t1 sees (L', 1, R') where L' and R'
may differ from L(t1), R(t1).

The LAST non-mover before t2 sees the config just before b fires again.
That config is: (L(t2), 1, R(t2)).
So the mover at t2 and the last non-mover before t2 see THE SAME (L, S, R)!

WAIT. Is that true?
At step t2: b is the mover. Context: (L(t2), 1, R(t2)).
At step t2-1: some other proc fires. b is non-mover.
  Context at t2-1: depends on who fires at t2-1.

If the proc that fires at t2-1 is NOT a neighbor of b:
  then L(t2) = L(t2-1), R(t2) = R(t2-1).
  Non-mover at t2-1: (L(t2), 1, R(t2)).
  Mover at t2: (L(t2), 1, R(t2)).
  SAME! EC!

If the proc that fires at t2-1 IS a neighbor of b (say left):
  L changes: L(t2) = L(t2-1) + 1 mod m_L.
  Non-mover at t2-1: (L(t2-1), 1, R(t2)).
  Mover at t2: (L(t2-1)+1, 1, R(t2)).
  DIFFERENT (L component).

So EC at b is GUARANTEED unless b's neighbor fires at step t2-1
(immediately before b). This means the mover at t2-1 must be
b-1 or b+1.

In a ring walk: the mover word is a walk on the ring.
Step t2-1 has mover p, step t2 has mover b.
For p to be b's neighbor: |p - b| = 1 mod n, which is ALWAYS true
since ring walks must move to adjacent procs!

So the mover at t2-1 is ALWAYS a neighbor of b.
This means the "last non-mover == mover" argument FAILS.

Hmm. But what about EARLIER non-movers in the gap?
""")

# Let me check empirically: does EC at binary come from
# step just after fire (first non-mover) or from some other step?

ms = [2, 2, 2, 3, 3]
n = 5
words = enumerate_mover_words(ms, n, 20)
gap_words = [w for w in words if is_gap_case(w, ms, n)]

# For P0 (binary, fc=4): identify which non-mover step creates EC
ec_gap_position = Counter()  # which gap (1-4) has the matching non-mover
ec_relative_pos = Counter()  # position within gap

for w in gap_words[:2000]:
    contexts = get_contexts(w, ms, n)
    mover_ctxs = {}  # ctx -> step
    nonmover_ctxs = defaultdict(list)  # ctx -> [steps]
    for step, (L, S, R, im) in enumerate(contexts[0]):
        if im:
            mover_ctxs[(L, S, R)] = step
        else:
            nonmover_ctxs[(L, S, R)].append(step)

    # Find fire steps
    fire_steps = [step for step, (L, S, R, im) in enumerate(contexts[0]) if im]
    if len(fire_steps) != 4:
        continue  # shouldn't happen

    # Check overlap
    for ctx in mover_ctxs:
        if ctx in nonmover_ctxs:
            m_step = mover_ctxs[ctx]
            for nm_step in nonmover_ctxs[ctx]:
                # Which gap is nm_step in?
                # Gaps: after fire[0]..before fire[1], after fire[1]..before fire[2], etc.
                for g in range(4):
                    start = fire_steps[g]
                    end = fire_steps[(g+1) % 4]
                    if end <= start:
                        end += len(w)
                    adj_nm = nm_step if nm_step > start else nm_step + len(w)
                    if start < adj_nm < end:
                        ec_gap_position[g] += 1
                        rel = adj_nm - start
                        ec_relative_pos[rel] += 1
                        break

print(f"\nP0 EC: gap position distribution: {dict(sorted(ec_gap_position.items()))}")
print(f"P0 EC: relative position in gap: {dict(sorted(ec_relative_pos.items()))}")


print("\n" + "=" * 70)
print("FINAL SYNTHESIS")
print("=" * 70)

print("""
SUMMARY OF FINDINGS:

1. GAP CASE EXISTS only when consecutive binary boundary procs have
   fc >= 4 (even, >= fc_ter >= 3). This requires CL >= sum(ms) + 4.

2. At minimum CL = sum(ms): gradient ALWAYS exists (fc_bin=2 < fc_ter=3).

3. Gap case at n=5: fc=[4,2,4,3,3], CL=16. 100% EC at some binary proc.
   Gap case at n=7: fc mostly [4,4,4,3,3,3,3], CL=24. 100% EC at some binary proc.

4. The mechanism is NOT simple pigeonhole at a single proc.
   It's a COMBINED effect across the binary cluster.

5. P1 (interior binary) has EC 98% of time. When it fails,
   P0 or P2 (boundary binary) pick up.

6. No-gradient-anywhere cases: extremely rare, but do exist.
   In ALL cases checked: EC exists at some proc.

7. The universal argument for gap case is:
   SOME binary proc always has entry conflict.
   This is empirically verified but needs an analytical proof.

   Possible analytical approach: transfer argument.
   If P1 avoids EC (mover contexts disjoint from non-mover),
   then the L,R values at P1's fire steps are "fresh" -
   not seen as non-mover. This constrains P0 and P2's fire
   patterns, forcing one of them to have EC.
""")
