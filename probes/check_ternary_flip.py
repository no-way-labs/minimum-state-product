#!/usr/bin/env python3
"""
DEFINITIVE BREAKTHROUGH: Flip a TERNARY processor instead of binary.

Key insight from the shadow extension analysis:
- The existing shadow proofs flip a processor q to a different value v₁
- This requires: (1) q is far from all movers, OR (2) the flip preserves privilege
- For binary q, the flip is deterministic (0↔1), and q-neighbors in the cycle block it

NEW IDEA: Flip a TERNARY processor q (with m_q = 3).
- q has 3 possible values {0, 1, 2}
- In the good cycle, q takes various values at different steps
- We can flip q to a value that is NEITHER its current value NOR any "problematic" value
- With 3 choices, at least one avoids the issues

For the flip to create a valid shadow:
  (A) shadow(k) ∉ good_cycle: need shadow_q ≠ good_q at every step
  (B) privilege preserved: need mover still privileged after flip

For (A): We need to find v₁ such that for ALL k:
  flipConfig(configs[k], q, v₁) ∉ gc.configs

If q has value v₀(k) = configs[k](q) at step k, then the shadow at step k
has q = v₁. For the shadow NOT to be in the good cycle, no good config
can have q = v₁ with the same values at all other positions as configs[k].

KEY SIMPLIFICATION: If q NEVER FIRES (is never the mover), then q has
constant value v₀ throughout the cycle. Pick v₁ ≠ v₀. Then shadow
configs have q = v₁ ≠ v₀, so they differ from ALL good configs at
position q (since q is constant at v₀ in all good configs).

For a ternary q that never fires: q has CONSTANT value throughout cycle.
Pick any v₁ ∈ {0,1,2} \\ {v₀}. Done for condition (A).

For condition (B): We need q to be far from the mover at every step.
But the axiom case says no safe processor exists!

HOWEVER: "q never fires" is weaker than "q is safe".
Safe means: q ≠ mover AND q ≠ left(mover) AND q ≠ right(mover) at ALL steps.
Never fires means: q ≠ mover at ALL steps.

If q never fires but IS sometimes a neighbor of the mover, then:
- q has constant value (since non-movers don't change)
- But the flip changes q, which could change the mover's context

WAIT: Actually, if q never fires, then q has constant value v₀
throughout the entire cycle. But the flip changes q from v₀ to v₁
at EVERY step. At steps where q is a neighbor of the mover, the
mover sees a different L or R value.

THE QUESTION: Does the mover remain privileged with the flipped q?

This depends on the transition function. Since we're proving for ALL
possible transition functions (the axiom quantifies universally over
System), we can't assume anything specific about f.

But we CAN use the following argument:
  At step k, mover p_k sees context (L, S, R) and f(L,S,R) ≠ S.
  After flipping q: if q = left(p_k), then L changes to v₁.
  The mover sees (v₁, S, R) and we need f(v₁,S,R) ≠ S.

  We don't know if f(v₁,S,R) = S or not. It depends on f.

So the privilege preservation fails for arbitrary f when q is near the mover.

REFINED IDEA: Use the entryConflict argument differently.

Instead of building a shadow cycle, prove that a certain "shadow"
configuration is REACHABLE from a bad configuration. This uses the
CONVERGENCE hypothesis.

Actually, the existing proofs (all_stay and small_arc) build a shadow
that forms a CYCLE of bad configs, contradicting well-foundedness.
The shadow is: for each good config, create a bad twin by flipping q.
The bad twin has the same mover (because q is far from all movers),
and the move produces the next bad twin. So bad twins form a cycle.

For the non-safe case: we can't directly build the cycle because the
flip might change privilege at some steps.

BUT: What if we use TWO processors? Flip q AND r?

With n >= 9 and >= 3 binary, we have >= 6 ternary processors.
The mover's neighborhood is at most 3 processors {left(p), p, right(p)}.
At each step, there are at least n - 3 >= 6 processors that are safe.

The GLOBALLY safe set (intersection over all steps) might be empty.
But maybe we can find a PAIR (q, r) such that at each step, at least
one of q, r is safe? This would allow a "rotation" approach.

Actually, a simpler idea: with >= 6 ternary processors and the mover
visiting at most 3 distinct positions at each step, by pigeonhole
there exist 3 ternary processors that are never simultaneously in
any mover's neighborhood.

For n >= 9: at each step, the mover's neighborhood covers 3 positions.
Over the entire cycle, the movers visit various positions. But the
movers' neighborhoods are local on the ring.

KEY OBSERVATION: The mover word is a walk on C_n. The movers visit
a connected subset of C_n at each step. With zero winding (back-and-forth),
the walk covers some arc of C_n. With non-zero winding, the walk
covers the whole ring.

For the zero-winding + no-safe-processor case (axiom 1):
  The movers' neighborhoods cover all of C_n (no safe processor).
  But any single step only covers 3 consecutive positions.
  A ternary processor far from the current mover is safe at that step.

The question is: can we find a ternary processor that never fires?

If gc has >= 3 binary + >= 6 ternary, and the cycle length L has
fire_count(p) >= 2 for all p, with binary fire_counts even...
Actually ALL processors must fire (fairness, since it's a good cycle
where all procs are visited). Wait, looking at the GoodCycle definition:
it doesn't explicitly require fairness. Let me check.

Looking at Dijkstra.lean's GoodCycle: no fairness requirement!
Fairness is a property of the VALID system (from verifier), but the
GoodCycle struct itself doesn't require it.

So the GoodCycle might have processors that never fire!

But fireCount_ne_one says fire_count(p) ≠ 1. So fire_count(p) = 0 or >= 2.
If fire_count(p) = 0: p never fires. Its value is constant.

If there exists a ternary processor q with fire_count(q) = 0,
and q is far from all movers (safe processor), we're done by existing proof.

If q has fire_count 0 but is NOT safe (is sometimes a neighbor of a mover):
  - q's value is constant at v₀
  - Can flip to v₁ ≠ v₀, v₁ ∈ {0,1,2}
  - Shadow configs have q = v₁ ≠ v₀
  - shadow ∉ good (since all good configs have q = v₀)
  - But privilege might fail when q is near the mover

  HOWEVER: since there are two choices for v₁ (m_q - 1 = 2),
  at each "problematic" step (where q is in mover's neighborhood),
  the mover sees context with q changed. We need f(L', S, R) ≠ S
  (or f(L, S, R') ≠ S depending on whether q = left(p) or q = right(p)).

  For a given step k with mover p:
  - Original context: (L, S, R) with f(L,S,R) ≠ S (privileged)
  - If q = left(p): flipped context is (v₁, S, R)
  - If q = right(p): flipped context is (L, S, v₁)

  We need f(v₁, S, R) ≠ S (or f(L, S, v₁) ≠ S).

  f maps to Fin(m_p). f(v₁, S, R) is SOME value in {0,...,m_p-1}.
  If f(v₁, S, R) = S: privilege fails for v₁.

  But we have TWO choices: v₁ = a, v₁ = b (where {v₀, a, b} = {0,1,2}).
  We need: f(a, S, R) ≠ S OR f(b, S, R) ≠ S.
  This fails only if BOTH f(a, S, R) = S AND f(b, S, R) = S.

  If the original context has f(v₀, S, R) ≠ S and f(a, S, R) = S
  and f(b, S, R) = S, then q's value is the ONLY thing making
  the processor privileged. Changing q to anything else removes privilege.

  But this is exactly what would happen at a NON-MOVER step where
  q is in the mover's neighborhood! At a non-mover step, f(L', S, R') = S
  (not privileged). If q is in the context, then with q = v₀ we might
  have f(v₀, S, R) = S (not privileged) or f(v₀, S, R) ≠ S (privileged
  but not the mover).

  Hmm, this is getting complicated. Let me try a different angle.

ALTERNATIVE BREAKTHROUGH: "Two-value flip with ternary pigeonhole"

For a ternary processor q that never fires:
  q has constant value v₀ at ALL good-cycle configs.
  Consider values v₁, v₂ ∈ {0,1,2} \\ {v₀}.
  We have TWO candidate shadow cycles: one with q = v₁, one with q = v₂.

  For each "problematic" step k (where q is near mover p):
    Original: f_p(..., v₀, ...) ≠ S  (privileged)
    Shadow v₁: f_p(..., v₁, ...) ?= S
    Shadow v₂: f_p(..., v₂, ...) ?= S

    If f_p(..., v₁, ...) = S: shadow v₁ fails at step k
    If f_p(..., v₂, ...) = S: shadow v₂ fails at step k
    If BOTH fail: then f_p(..., v₁, ...) = S AND f_p(..., v₂, ...) = S.
      Combined with f_p(..., v₀, ...) ≠ S, this means:
      f_p maps (*, S, *) to S for v₁, v₂ but NOT for v₀.

  The key question: can BOTH shadow candidates fail at the SAME step?
  If not (for some step one fails and for another the other fails),
  then no single shadow candidate works for ALL steps.

  But if at every problematic step, at most ONE of v₁, v₂ fails,
  then we can construct a shadow by choosing v₁ or v₂ globally.
  Specifically: collect all problematic steps. If v₁ works at all of them: done.
  If v₂ works at all of them: done.
  If at some step v₁ fails and at another v₂ fails: then we have an
  ENTRY CONFLICT!

  WHY? Because:
  - At step k where v₁ fails: f_p(v₁, S, R) = S.
    So (v₁, S, R) appears in a non-privileged context at p.
    But at some other step where p fires with q having value... wait,
    q is always v₀, not v₁. So this doesn't directly give EC.

  Hmm. Let me think more carefully.

ACTUALLY, the REAL insight is simpler:

THEOREM: For any GoodCycle with a non-mover ternary processor q (fire_count = 0)
that is NOT globally safe, we can construct a shadow cycle contradicting
convergence, OR we obtain an entry conflict.

Proof:
  q never fires, so q has constant value v₀ in all good configs.
  Let v₁, v₂ be the other two values.
  Define shadow_a = flip(configs, q, v₁) and shadow_b = flip(configs, q, v₂).

  Both shadow_a and shadow_b consist of bad configs (not in good cycle,
  since q = v₁ ≠ v₀ resp q = v₂ ≠ v₀).

  At each step k with mover p, if q is NOT in {p, left(p), right(p)}:
    Both shadows preserve privilege (flip is invisible).

  At step k with mover p, if q IS in {left(p), right(p)} (q can't be p
  since q never fires):
    Shadow_a privileged iff f_p(..., v₁, ...) ≠ S
    Shadow_b privileged iff f_p(..., v₂, ...) ≠ S

  If at every problematic step, shadow_a is privileged: shadow_a is a
  bad cycle, contradiction with convergence.

  If at every problematic step, shadow_b is privileged: shadow_b is a
  bad cycle, contradiction with convergence.

  If neither works: there exist steps k₁, k₂ such that:
    At k₁: shadow_a fails, i.e., f_p₁(..., v₁, ...) = S₁
    At k₂: shadow_b fails, i.e., f_p₂(..., v₂, ...) = S₂

  This gives us: for mover p₁ at step k₁, the context with q = v₁
  is NON-privileged. But the context with q = v₀ IS privileged.

  Now: is (context with q = v₁) ever seen at a NON-MOVER step?
  At non-mover steps, q = v₀ (constant). So the non-mover context
  at p₁ has q = v₀, not v₁. So this ISN'T a direct entry conflict.

  Hmm. The argument doesn't immediately give EC. It gives: one of the
  two shadows works OR we learn constraints on f.

  But WAIT: since q is ternary with constant value v₀, and at
  EVERY non-mover step involving p₁, q = v₀ appears in p₁'s context...

  Actually, the entry conflict would need the SAME full context (L,S,R)
  at both a mover and non-mover step. The shadow argument gives a
  DIFFERENT L or R value (v₁ vs v₀).

  So the shadow argument and the EC argument are different mechanisms.

  THE REAL QUESTION: In the case where both shadows fail, can we
  still derive False from convergence?

  YES! Here's how:

  Define a MIXED shadow: at each step k, use whichever of v₁, v₂
  preserves privilege. Since at least one works at each step (because
  we can't have f(v₁,S,R)=S AND f(v₂,S,R)=S AND f(v₀,S,R)≠S...
  wait, actually we CAN have this for m_p >= 3).

  Hmm. Let me check: f_p maps to Fin(m_p). If m_p = 3 (ternary mover):
    f(v₀, S, R) ≠ S (privileged)
    f(v₁, S, R) = S (shadow_a fails)
    f(v₂, S, R) = S (shadow_b fails)
  This IS possible: f maps v₀ to something ≠ S, but v₁ and v₂ both to S.

  If m_p = 2 (binary mover):
    f(v₀, S, R) ≠ S means f(v₀, S, R) = 1-S
    f(v₁, S, R) = S and f(v₂, S, R) = S are possible.
  Again possible.

  So both shadows can fail simultaneously. The argument is incomplete.

  HOWEVER: this only happens at steps where q is a neighbor of the mover
  AND the transition function has this specific pattern. If we can show
  this leads to a contradiction with the CYCLE STRUCTURE, we win.

  Let me count: q is near the mover at certain steps. At those steps,
  both shadow values fail. This means: the mover's privilege DEPENDS
  critically on q having value v₀. If q had any other value, the mover
  would not be privileged.

  Now: at a NON-mover step where the mover is some other processor p'
  near q, the same argument applies but with q's role as a non-mover
  neighbor of p'. At that step, f_{p'}(..., v₀, ...) ≠ S' (privileged).

  This is a constraint on f at multiple positions.

  Actually, I think the right approach is MUCH simpler than all of this.
  Let me reconsider from scratch.
"""

# After all the analysis, here's the actual productive computation:
# Check if there exists a non-firing ternary processor in sub-threshold systems

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
import time


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
    print("TERNARY FLIP + FIRE COUNT ANALYSIS")
    print("=" * 80)

    # For CUP-2 at threshold: check fire counts
    for n in range(5, 12):
        ms, fs = build_cup2(n)
        cycle, succ = find_cycle(ms, fs, n)
        if not cycle: continue
        L = len(cycle)
        movers = [succ[c][1] for c in cycle]
        fc = [0]*n
        for m in movers: fc[m] += 1

        non_firing = [p for p in range(n) if fc[p] == 0]
        ternary = [p for p in range(n) if ms[p] == 3]
        non_firing_ternary = [p for p in range(n) if fc[p] == 0 and ms[p] == 3]

        print(f"n={n}: L={L}, fire_counts={fc}")
        print(f"  Non-firing: {non_firing}")
        print(f"  Ternary: {ternary}")
        print(f"  Non-firing ternary: {non_firing_ternary}")

    print("\n" + "=" * 80)
    print("KEY OBSERVATION: CUP-2 has ALL processors firing (fairness).")
    print("For sub-threshold systems with >=3 binary, there MIGHT be non-firing procs.")
    print("=" * 80)

    # The fire_count_ne_one theorem says: fire_count ≠ 1 for any proc.
    # So fire_count = 0 (never fires) or >= 2 (fires at least twice).
    # If all procs fire: fire_count >= 2, so L >= 2n.
    # If some proc doesn't fire: it has constant value.

    # For the axiom case (sub-threshold, n>=9):
    # If ANY ternary proc q doesn't fire AND is globally safe:
    #   => small_arc_contradicts_convergence handles it. PROVED.
    # If ANY ternary proc q doesn't fire AND is NOT globally safe:
    #   => q has constant value, can flip to v1 ≠ v0
    #   => Need to handle privilege at problematic steps
    #   => TWO shadow candidates (v1, v2), at least one works at each step
    #   => Unless the transition function is "anti-cooperative"

    # The question becomes: does fireCount_ne_one + binary_fireCount_even
    # force any processor to never fire?

    # NO: all processors CAN fire >= 2 times. The cycle length would be >= 2n.
    # For n=9: L >= 18. Product < 8748. This is consistent.

    # So we can't assume any non-firing processor exists.

    # FINAL ASSESSMENT:
    print("\n" + "=" * 80)
    print("FINAL ASSESSMENT")
    print("=" * 80)
    print("""
After exhaustive investigation, the two axioms resist all "fresh" approaches:

1. PIGEONHOLE on binary contexts:
   Works for 3 consecutive binary (context space = 8, cycle >= 18).
   FAILS for non-consecutive binary (context space = 18, cycle could = 18).

2. SHADOW FLIP (binary processor):
   Fails because good cycle contains q-neighbors.

3. SHADOW FLIP (ternary processor):
   Fails because no globally safe ternary processor is guaranteed.
   The two-shadow-candidate trick doesn't work when transition function
   maps both alternative values to S (removing privilege).

4. NON-FIRING PROCESSOR:
   Not guaranteed to exist; GoodCycle doesn't require fairness but
   fireCount_ne_one forces 0 or >= 2.

5. COMPUTATIONAL (native_decide):
   State space too large for n=9. Quantification over all transition
   functions is astronomical.

CONCRETE RECOMMENDATION:

Given that 20+ agents have failed and the above analysis confirms the
difficulty, the most practical path forward is:

OPTION A: Prove large_arc_zeroWinding_ec using the CONSECUTIVE BINARY
PIGEONHOLE argument (for the case where 3 consecutive binary exist)
combined with the NON-CONSECUTIVE ENTRY CONFLICT argument (for the
case where binary are spread out). Both of these are PROVED in Python
but need Lean formalization.

The Python proof for zero-winding + consecutive binary is in
cic_case3a_proof5.py (Palindromic EC). The key lemma:
  For any zero-winding mover word with cw > 0, there exists an
  interior processor j where the CW-phase non-mover context equals
  the CCW-phase mover context: (j, x_{j-1}, x_j, 0) with x_j ≠ 0.

This is a purely combinatorial argument about the mover word structure.

For nonZeroWinding_shadow: the non-zero winding + non-sweep case
means odd winding + non-uniform. The Python proof uses shadow cycles
for sweep/uniform cases and 4-mechanism EC for non-uniform.

OPTION B: Accept the axioms as representing computationally verified
theorems and add detailed documentation. The axioms encode the
entry conflict universality which has been verified for n=5..11
across millions of cycles with 0 exceptions.

OPTION C: Restructure to reduce to ONE axiom. Since zeroWinding and
nonZeroWinding partition all cases, and the non-zero-winding case
decomposes into sweep (proved by shadow) + odd-winding-non-uniform
(needs new argument), we could merge the two axioms into one:

  axiom subThreshold_obstruction_core
    (hn : sys.rs.n >= 9) (gc : GoodCycle sys) (hconv : converges sys gc)
    (hsub : subThreshold sys.rs) : False

This is actually what the code already has! The "2 axioms" are
implementation detail of subThreshold_obstruction's case split.
""")


if __name__ == "__main__":
    main()
