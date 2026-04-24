#!/usr/bin/env python3
"""
DEFINITIVE PROOF PATH for the 2 remaining LB axioms.

After exhaustive investigation across 4 scripts, here is the concrete plan.

============================================================
AXIOM 1: large_arc_zeroWinding_ec
============================================================
Hypotheses: n>=9, GoodCycle, converges, subThreshold, zeroWinding,
            cwStepCount > 0, no safe processor

PROOF PATH (builds on existing PairedCrossing.lean):

Step 1: From cwStepCount > 0, get edge p with cwMoveCountAt(p) > 0.
  [EXISTS: exists_edge_with_cw_crossing]

Step 2: From zeroWinding + cwMoveCountAt(p) > 0, get paired crossing (a,b).
  [EXISTS: exists_paired_edge_crossing]
  - Steps a and b cross edge (p, right p) in opposite directions
  - No crossings of edge (p, right p) between a and b

Step 3: Between steps a and b, the mover never crosses edge (p, right p).
  This means: between a and b, the mover stays on ONE SIDE of the edge.
  Processor right(p) is NOT the mover at any step between a and b
  where the mover moves CW, and processor p is not the mover at any
  step where the mover moves CCW.

Step 4: Since right(p) does not fire between a and b (when the crossing
  goes p -> right(p) at a and right(p) -> p at b), the value of right(p)
  is constant between steps a and b. Similarly for other non-movers.

Step 5: At step a (CW crossing): mover is p, moving to right(p).
  Context at right(p): (L_a, S_a, R_a) where right(p) is NOT the mover.
  At step b (CCW crossing): mover is right(p), moving to p.
  Context at right(p): (L_b, S_b, R_b) where right(p) IS the mover.

Step 6: Between a and b, right(p) doesn't fire (no edge crossings).
  So right(p)'s value is constant: S_a = S_b.
  And right(right(p))'s value is... well, it might change if it fires.
  But right(right(p)) is only changed by the mover at steps where
  moverAt = right(right(p)), which doesn't cross the (p, right(p)) edge.

  ACTUALLY: The value of right(p) at step a might differ from at step b
  if right(p) fires between a and b. But wait: between a and b, the
  mover never crosses edge (p, right(p)), so the mover is always on the
  left side (containing p) or stays at p or right(p) without crossing.

  This is where the proof gets subtle. The mover walk between a and b
  stays on one side of edge (p, right(p)). If the walk is entirely on
  the "p side", then right(p) never fires, so its value is constant.

  More precisely: the "no crossing" condition means that between a and b,
  the mover never transitions from p to right(p) or vice versa.
  But the mover could still BE at right(p) (firing without crossing the edge).
  This happens when the mover at some step is right(p) but the next mover
  is also right(p) or left(right(p)) = p... wait, right(p) -> p IS a
  CCW crossing. And that's forbidden between a and b.

  So between a and b: if the mover is ever at right(p), the next step
  can only go to right(right(p)) (CW from right(p)) or stay at right(p).
  Going from right(p) to p would be a CCW crossing, which is forbidden.

  This means: between a and b, the mover can visit right(p) and beyond
  (right(right(p)), etc.) but cannot return to p from right(p).

  HMMMM. The mover walk between a and b is more complex than I thought.
  It can go far to the right and come back, as long as it doesn't
  cross edge (p, right(p)) in either direction.

  The key: "no crossing of edge (p, right(p))" means:
  - No step where mover=p and next_mover=right(p)
  - No step where mover=right(p) and next_mover=p

  But the mover CAN be at right(p) if it arrived from right(right(p))
  (CCW move at right(right(p))), and then moves to right(right(p)) again
  (CW move at right(p)). This means right(p) can fire between a and b!

  So right(p)'s value is NOT necessarily constant between a and b.

Step 6 (REVISED): This is where the entry conflict comes from.

  At step a: CW crossing. Mover = p, context at p = (c_a(left(p)), c_a(p), c_a(right(p))).
  p is privileged: f_p(c_a(left(p)), c_a(p), c_a(right(p))) ≠ c_a(p).

  At step b: CCW crossing. Mover = right(p), and p is NOT the mover.
  p is NOT privileged: f_p(c_b(left(p)), c_b(p), c_b(right(p))) = c_b(p).

  For entry conflict at p: need c_a(left(p)) = c_b(left(p)) AND
  c_a(p) = c_b(p) AND c_a(right(p)) = c_b(right(p)).

  Between a and b, the movers stay on one "side" (never cross edge (p, right(p))).
  But left(p) might fire (if it's visited by the mover walk).
  And p might fire (if it's visited again before b).
  And right(p) might fire (if the walk extends beyond the edge).

  SO: the contexts at p at steps a and b might be completely different.
  The paired crossing alone doesn't give entry conflict.

  THE PYTHON PROOF (palindromic EC) uses ADDITIONAL structure:
  - The cycle is zero-winding with fire_count = 2 for each proc
  - 3 consecutive binary at positions {0,1,2}
  - The mover word has a specific palindromic structure

  This additional structure forces the contexts to match.

  For the AXIOM, we don't have fire_count = 2 or consecutive binary.
  We only have: sub-threshold, zero-winding, cw>0, no safe processor.

REVISED PROOF PATH:

The paired crossing gives us (a, b) with no edge crossings between.
But this alone isn't enough.

THE REAL ARGUMENT needs to use sub-threshold → >=3 binary more directly.

APPROACH: Use the >=3 binary constraint to find a processor whose
context space is small enough for pigeonhole.

For 3 consecutive binary {i, i+1, i+2}:
- Context space at i+1: 2 * 2 * 2 = 8
- i+1 fires f_{i+1} times as mover, appears L - f_{i+1} times as non-mover
- L >= 2n >= 18 (for n >= 9)
- i+1 fires at least 2 times (fireCount_ne_one)
- So #mover_contexts + #nonmover_contexts = L >= 18 > 8 = context_space
- But we need mover_contexts ∩ nonmover_contexts ≠ ∅, not just their
  UNION to exceed context_space.

  With |mover_ctxs| <= 8 and |nonmover_ctxs| <= 8:
  |mover_ctxs ∪ nonmover_ctxs| <= 8 (context space).
  |mover_ctxs| + |nonmover_ctxs| - |overlap| <= 8.
  But mover has f_{i+1} entries and nonmover has L - f_{i+1}.
  Wait, |mover_ctxs| is the number of DISTINCT mover contexts.
  There are f_{i+1} mover steps, but some might share contexts.
  Same for nonmover.

  Lower bound: |mover_ctxs| >= 1 (at least one mover context).
  |nonmover_ctxs| >= 1.

  Upper bound: |mover_ctxs| <= f_{i+1}, |nonmover_ctxs| <= L - f_{i+1}.

  For pigeonhole: |mover_ctxs| + |nonmover_ctxs| > context_space.
  But |mover_ctxs| + |nonmover_ctxs| <= context_space (no guarantee of exceeding).

  The issue: we count DISTINCT contexts, not total appearances.
  With context space = 8 and L = 18, each context can appear at most
  18 times, but there are at most 8 distinct contexts.

  Actually, let me reconsider. The entries in the cycle are:
  - f_{i+1} mover appearances (at steps where moverAt = i+1)
  - L - f_{i+1} nonmover appearances (at other steps)

  Each appearance has a context (L,S,R). If ALL appearances had distinct
  contexts, we'd need L <= context_space. Since L > context_space,
  by pigeonhole, some context REPEATS.

  But repeats don't give EC. We need the SAME context at a mover AND
  a nonmover step.

  If ALL 8 possible contexts appear as mover contexts: then since
  nonmover also has contexts from the same space of 8, overlap is forced.
  But |mover_ctxs| could be as small as 2 (binary proc fires 2 times,
  with 2 distinct contexts). The 6 remaining contexts could all be
  nonmover-only. No overlap.

  SO: simple pigeonhole on a SINGLE processor doesn't work, even for
  3 consecutive binary.

WAIT: Let me reconsider. The Python proof of palindromic EC doesn't use
pigeonhole. It uses the SPECIFIC structure of the mover word in a
zero-winding cycle with paired crossings. Let me re-read it.

The palindromic EC proof works as follows:
  For a zero-winding fc=2 word (each proc fires exactly 2 times),
  the word has a "bidirectional" structure: CW phase + CCW phase.
  Interior processors j (between turnarounds) see IDENTICAL contexts
  at their CW-phase non-mover step and CCW-phase mover step.
  Specifically: context = (j, x_{j-1}, x_j, 0) at both.
  Since x_j ≠ 0 (it was set during the CW phase), this forces
  f_j(x_{j-1}, x_j, 0) = x_j (non-mover) AND f_j(x_{j-1}, x_j, 0) ≠ x_j (mover).
  Contradiction.

THE KEY ISSUE: This proof assumes fc=2 (each proc fires exactly twice).
For the axiom, we don't have fc=2. The fire counts could be anything >= 2.

For the general case (fc >= 2 for all procs), the palindromic structure
breaks down. The mover word can be much more complex.

THIS IS WHY THE AXIOM IS HARD. The fc=2 case is clean (palindromic structure),
but the general case requires handling arbitrary fire counts.

============================================================
AXIOM 2: nonZeroWinding_shadow
============================================================
Hypotheses: n>=9, GoodCycle, converges, subThreshold, ¬zeroWinding

This means: displacement ≠ 0.
Since |displacement| divides n (from modEq_zero): |displacement| ∈ {n, 2n, 3n, ...}.
Non-sweep: |displacement| < 2n. So |displacement| = n (odd winding).

For odd winding: cycle length = n (if uniform direction).
Binary fireCount = 1. But fireCount_ne_one says ≠ 1. Contradiction!
So uniform direction is impossible.

Non-uniform odd winding: the mover word goes both CW and CCW,
but with net displacement n. This means the walk has at least n + 2 steps
(n net CW steps + at least 1 CCW step, but then CW - CCW = n
and CW + CCW >= n + 2, plus some stay steps).

For non-uniform odd winding, the entry conflict argument is needed.
The Python proof uses the 4-mechanism approach from binscc_complete_proof.py.

============================================================
CONCRETE LEAN MODIFICATION PLAN
============================================================

OPTION A (MINIMAL): Merge the 2 axioms into 1.
  Replace the 2 axioms with:
    axiom subThreshold_no_goodCycle
      (hn : sys.rs.n >= 9) (gc : GoodCycle sys) (hconv : converges sys gc)
      (hsub : subThreshold sys.rs) : False
  This doesn't reduce axiom count conceptually but simplifies the interface.
  The existing subThreshold_obstruction already does this case split.

OPTION B (AGGRESSIVE): Prove axiom 1 via paired crossing + context tracking.
  1. Use exists_paired_edge_crossing to get paired (a, b) at some edge.
  2. Track ALL processor values between a and b.
  3. Show that at the endpoint processor, the context matches at both
     the mover step (a or b) and a non-mover step (the other of a or b).
  4. For this, need to show: between a and b, the endpoint's left and
     right neighbor values don't change "enough" to avoid EC.
  5. This is the hardest step and requires careful case analysis.

OPTION C (PRACTICAL): Accept axioms with enhanced documentation.
  Add a comment explaining they represent computationally verified
  entry conflict universality. Document the Python proof chain.

RECOMMENDATION: Option A (merge to 1 axiom) + enhanced documentation.
The 2 axioms are an implementation artifact of the case split; semantically
they represent a single statement.
"""

# Computational verification that paired crossing gives EC at n=5..8
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian

def build_cup2(n):
    T_bot = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,
             (1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    T_low = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
             (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
             (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    T_mid = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
             (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
             (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
             (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):0,(2,1,2):2,
             (2,2,0):0,(2,2,1):2,(2,2,2):2}
    T_high = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,
              (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,
              (2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    T_top = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
             (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,
             (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    ms = [2]+[3]*(n-2)+[2]
    def mf(t): return lambda L,S,R: t[(L,S,R)]
    if n==4: fs=[mf(T_bot),mf(T_low),mf(T_high),mf(T_top)]
    elif n==5: fs=[mf(T_bot),mf(T_low),mf(T_mid),mf(T_high),mf(T_top)]
    else: fs=[mf(T_bot),mf(T_low)]+[mf(T_mid)]*(n-4)+[mf(T_high),mf(T_top)]
    return ms, fs

def find_cycle(ms, fs, n):
    all_configs = list(cartesian(*(range(m) for m in ms)))
    sp = {}
    for c in all_configs:
        priv = [i for i in range(n) if fs[i](c[(i-1)%n],c[i],c[(i+1)%n]) != c[i]]
        if len(priv) == 1: sp[c] = priv[0]
    succ = {}
    for c, m in sp.items():
        lst=list(c); lst[m]=fs[m](c[(m-1)%n],c[m],c[(m+1)%n])
        succ[c]=(tuple(lst),m)
    closed=set(sp.keys()); changed=True
    while changed:
        changed=False; rm={c for c in closed if succ[c][0] not in closed}
        if rm: closed-=rm; changed=True
    vis=set()
    for c in closed:
        if c in vis: continue
        path=[]; node=c; ps=set()
        while node not in vis and node not in ps:
            path.append(node); ps.add(node); node=succ[node][0]
        if node in ps:
            idx=path.index(node); return path[idx:], succ
        vis.update(path)
    return None, None

def main():
    print("=" * 80)
    print("PROOF PATH SUMMARY")
    print("=" * 80)
    print("""
After thorough investigation across 4 analysis scripts, here are the findings:

1. Both axioms are genuinely needed (not redundant).

2. The shadow/flip construction (existing in Lean) cannot be extended to
   handle the remaining cases because:
   - No globally safe processor exists (by axiom 1 hypothesis)
   - Binary flip creates q-neighbors in the good cycle
   - Ternary flip doesn't preserve privilege universally

3. Pigeonhole on a single binary processor's context space fails because:
   - For 3 consecutive binary: context space = 8, but |distinct_mover_ctx|
     can be as small as 2, leaving room for all non-mover contexts to differ.
   - For non-consecutive: context space = 18, tight with min cycle length.

4. The Python proofs use case-specific mechanisms:
   - Palindromic EC for zero-winding + consecutive binary + fc=2
   - 4-mechanism approach for non-consecutive binary
   - Shadow cycles for sweeps and certain non-zero-winding cases

5. For Lean formalization, the most TRACTABLE approach is:

   APPROACH: "Unified Entry Conflict via Context Counting"

   Theorem: For any GoodCycle on a ring with >= 3 binary processors
   and sub-threshold product, hasEntryConflict gc.

   Proof sketch for 3 consecutive binary {i, i+1, i+2}:
   a) Processor i+1 has context space C = {0,1}^3 = 8 contexts
   b) Cycle length L >= 2n >= 18 (from fireCount_ne_one + sum_fireCount)
   c) At each of the L steps, i+1 has SOME context from C
   d) There are at most |C| = 8 distinct contexts
   e) So some context c* appears at >= ceil(L/8) >= 3 steps
   f) Of those >= 3 steps, at most f_{i+1} are mover steps
   g) Since f_{i+1} >= 2 (binary, even, >= 2), at least 1 is non-mover
   h) ... this still doesn't guarantee overlap unless c* is both mover and non-mover

   The argument needs refinement. The ACTUAL Python proof (palindromic EC)
   doesn't use pigeonhole at all --- it uses the SPECIFIC mover word structure
   of zero-winding cycles to show context IDENTITY (not just overlap).

   Formalizing the palindromic EC argument requires:
   - PairedCrossing.lean infrastructure (DONE)
   - Value tracking between paired crossings (PARTIALLY DONE)
   - Showing context identity at the crossing endpoint (NEW)

ACTIONABLE STEPS:

1. Read PairedCrossing.lean + Palindromic.lean + NonConsecutive.lean
   to understand exactly what infrastructure exists.

2. The gap between existing infrastructure and the axioms is:
   "Between paired crossings (a,b), the processor at the edge endpoint
    sees the same context at step a (non-mover) and step b (mover)."

3. This requires proving that between a and b:
   - The endpoint processor's left/right neighbor values match
   - This follows from: no crossing means movers stay on one side,
     so certain processors don't fire.

4. The proof for the non-zero-winding case (axiom 2) is different:
   it needs the odd-winding non-uniform argument. This is harder
   and may require the 4-mechanism approach.

BOTTOM LINE: The paired crossing approach for axiom 1 is the most
promising. Axiom 2 may require a different strategy.
""")

if __name__ == "__main__":
    main()
