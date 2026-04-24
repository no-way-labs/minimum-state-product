#!/usr/bin/env python3
"""
KEY QUESTION: Do valid sub-threshold systems exist for n >= 5?

If no valid sub-threshold system exists for n >= K, then BOTH axioms
are vacuously true for n >= K. The axioms say:
  "For any system + good cycle + convergence + sub-threshold + n>=9: False"

If no such (system, good cycle, convergence) triple exists, False
follows from the empty antecedent.

This script checks: for n=5,6,7,8,9, do any valid sub-threshold systems exist?

From the memory:
- M_5 = 96, achieved by ms=(2,2,2,3,4)
- M_6 = 288 = 4*3^4? or 32*3^2 = 288? Yes, 4*3^4 = 324, 32*3^2 = 288
- M_n = 32*3^(n-4) for n=5..8, = 4*3^(n-2) for n>=9

Actually: M_5 = 96, threshold = 4*3^3 = 108. So 96 < 108.
This means valid systems with product 96 exist! They ARE sub-threshold.

So the axioms are NOT vacuously true at n=5. There exist sub-threshold
valid systems. But the axioms require n >= 9.

For n=9: M_9 = 8748 = 4*3^7 = threshold. So at n=9, the minimum
valid product EQUALS the threshold. No valid system with product
STRICTLY LESS than threshold exists. So for n >= 9, the axioms ARE
vacuously true in the sense that no valid sub-threshold system exists.

BUT WAIT: the axioms don't require the FULL system to be valid.
They require:
1. A System (transition functions)
2. A GoodCycle for that system (a cycle of single-privileged configs)
3. converges: the bad-step relation is well-founded

A system can have a GoodCycle without being "valid" in the verifier's sense.
Actually, looking at Dijkstra.lean:
- valid sys := ∃ gc : GoodCycle sys, converges sys gc

So the axioms require exactly "valid sys" to hold. And for n >= 9
with sub-threshold product, M_n >= 4*3^(n-2) means no valid system
exists with product < 4*3^(n-2). So the axioms ARE vacuously true.

This means: if we can prove IN LEAN that "sub-threshold + n>=9 => ¬valid sys",
then both axioms become trivially provable.

But that's exactly what the lower bound theorem IS. It's circular!

The lower bound theorem USES the axioms to prove ¬valid.
The axioms are (we hope) vacuously true because ¬valid.

The way to break the circularity: prove ¬valid WITHOUT the axioms,
using a DIRECT argument. The direct argument is entry conflict.

Let me verify computationally: for n=5..8 with sub-threshold systems,
do ALL good cycles have entry conflict?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))

from itertools import product as cartesian, permutations
from verifier import verify_system, privileged_set, apply_move
import time


def check_ec_for_cycle(cycle, succ, ms, n):
    """Check entry conflict for a good cycle."""
    L = len(cycle)
    for proc in range(n):
        mover_contexts = set()
        nonmover_contexts = set()
        for c in cycle:
            mover = succ[c][1]
            ctx = (c[(proc-1) % n], c[proc], c[(proc+1) % n])
            if mover == proc:
                mover_contexts.add(ctx)
            else:
                nonmover_contexts.add(ctx)
        if mover_contexts & nonmover_contexts:
            return True
    return False


def find_good_cycles(ms, fs, n):
    """Find good cycles for a system."""
    all_configs = list(cartesian(*(range(m) for m in ms)))

    single_priv = {}
    for c in all_configs:
        priv = []
        for i in range(n):
            L = c[(i-1)%n]; S = c[i]; R = c[(i+1)%n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        if len(priv) == 1:
            single_priv[c] = priv[0]

    succ = {}
    for c, mover in single_priv.items():
        lst = list(c)
        lst[mover] = fs[mover](c[(mover-1)%n], c[mover], c[(mover+1)%n])
        succ[c] = (tuple(lst), mover)

    closed = set(single_priv.keys())
    changed = True
    while changed:
        changed = False
        to_remove = {c for c in closed if succ[c][0] not in closed}
        if to_remove:
            closed -= to_remove
            changed = True

    visited = set()
    cycles = []
    for c in closed:
        if c in visited: continue
        path = []; node = c; path_set = set()
        while node not in visited and node not in path_set:
            path.append(node); path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            idx = path.index(node)
            cycles.append(path[idx:])
        visited.update(path)

    return cycles, succ


def try_incrementing_system(ms, n):
    """Build a simple incrementing transition system: f(L,S,R) = (S+1) % m."""
    fs = []
    for i in range(n):
        m = ms[i]
        def make_f(m_val):
            return lambda L,S,R: (S+1) % m_val
        fs.append(make_f(m))
    return fs


def try_all_systems_small(ms, n, max_systems=None):
    """For small state spaces, try many transition function combinations."""
    product = 1
    for m in ms: product *= m

    # Build all possible transition function tables for each processor
    # This is generally infeasible, but for very small products we can try
    # specific strategies

    # Strategy 1: Incrementing
    fs_inc = try_incrementing_system(ms, n)
    result = verify_system(ms, fs_inc)
    if result['valid']:
        return fs_inc, result

    # Strategy 2: CUP-2 style (if applicable)
    if ms == [2] + [3]*(n-2) + [2]:
        from cup2_theorem import build_system
        _, fs_cup = build_system(n)
        result = verify_system(ms, fs_cup)
        if result['valid']:
            return fs_cup, result

    return None, None


def main():
    print("=" * 80)
    print("SUB-THRESHOLD VALIDITY CHECK")
    print("=" * 80)

    for n in [5, 6, 7, 8, 9]:
        threshold = 4 * 3**(n-2)
        print(f"\n{'='*60}")
        print(f"n = {n}, threshold = {threshold}")
        print(f"{'='*60}")

        # M_n values from memory
        m_n = {5: 96, 6: 288, 7: 864, 8: 2592, 9: 8748}

        print(f"  Known M_n = {m_n[n]}")
        print(f"  Sub-threshold means product < {threshold}")
        print(f"  M_n {'<' if m_n[n] < threshold else '>=' if m_n[n] >= threshold else '='} threshold")
        if m_n[n] < threshold:
            print(f"  => Valid sub-threshold systems EXIST")
            print(f"  => Axioms are NOT vacuously true at n={n}")
            print(f"  => Must prove entry conflict for these systems")
        elif m_n[n] == threshold:
            print(f"  => M_n = threshold exactly")
            print(f"  => No valid system with product < threshold exists")
            print(f"  => Axioms ARE vacuously true at n={n}")
        else:
            print(f"  => M_n > threshold")
            print(f"  => No valid system with product < threshold")
            print(f"  => Axioms ARE vacuously true at n={n}")

        # For n=5, let's check what the M_5 witness looks like
        if n == 5:
            print(f"\n  Checking M_5 = 96 witness: ms=(2,2,2,3,4)")
            ms = [2, 2, 2, 3, 4]
            # We'd need the actual transition functions for this witness
            # Let's try incrementing first
            fs = try_incrementing_system(ms, n)
            result = verify_system(ms, fs)
            print(f"    Incrementing system valid? {result['valid']}")

            # The actual M_5 witness uses specific tables found by search
            # It has 3 consecutive binary at positions 0,1,2
            binary_count = sum(1 for m in ms if m == 2)
            consec_3 = any(ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2
                          for i in range(n))
            print(f"    Binary count: {binary_count}")
            print(f"    Has 3 consecutive binary: {consec_3}")
            print(f"    Product = 96 < threshold = 108: sub-threshold")

    print(f"\n{'='*80}")
    print("KEY FINDING")
    print("=" * 80)
    print("""
For n >= 9: M_n = 4*3^(n-2) = threshold. No valid sub-threshold system exists.
Therefore: the axioms' hypotheses (valid sys + sub-threshold) are UNSATISFIABLE.
Both axioms are VACUOUSLY TRUE.

But this doesn't help us eliminate the axioms, because the PROOF that
M_n >= threshold IS the lower bound theorem, which USES the axioms.

To eliminate the axioms, we need to break the circularity by proving
¬(valid sys) for sub-threshold + n>=9 using a DIRECT method.

The existing Lean proof structure:
  lower_bound_theorem uses subThreshold_obstruction
  subThreshold_obstruction uses the 2 axioms
  The 2 axioms assert False

To close the gap:
  Option 1: Prove the axioms directly (entry conflict argument)
  Option 2: Restructure the proof to avoid needing the axioms
  Option 3: Use a completely different proof path

OPTION 2 is the most promising. Here's how:

The current proof goes:
  1. Get gc : GoodCycle sys and hconv : converges sys gc
  2. Case split on winding type
  3. For sweeps/uniform-odd: use shadow_cycle_mirror_theorem (proved!)
  4. For zero-winding + no safe proc: AXIOM 1
  5. For non-zero winding: AXIOM 2

But the case split at step 2 is NOT the only possibility.
Alternative case split:

  1. Get gc : GoodCycle sys and hconv : converges sys gc
  2. Sub-threshold => >=3 binary
  3. Case split on: do 3 consecutive binary exist?
     a. YES: use pigeonhole on middle binary proc's context space
        (8 possible contexts, cycle length >= 18, guaranteed EC)
     b. NO: 3 non-consecutive binary. Case split on cycle structure:
        - If cycle is a sweep (WaterfallCycle): shadow_cycle_mirror_theorem (proved!)
        - If not sweep + zero winding: entry conflict via mover word structure
        - If not sweep + odd winding: already proved (not_uniformDirection...)

Wait, this still has the same hard cases. Let me think differently.

ACTUALLY, let me reconsider the structure. The current proof already
handles:
  - Sweeps (via shadow): PROVED
  - Odd winding + uniform direction: impossible (binary parity): PROVED
  - Odd winding + non-uniform: PROVED
  - Zero winding + cw=0 (all stay): PROVED
  - Zero winding + cw>0 + safe processor: PROVED

What remains:
  - Zero winding + cw>0 + no safe processor: AXIOM 1
  - (Non-zero winding: AXIOM 2 — but wait, non-zero winding is either
    sweep (proved) or odd winding (proved). Is there another case?)

Let me check: the cases are sweep (|displacement| >= 2n), zero winding
(displacement = 0), odd winding (|displacement| = n). Are there other
winding numbers?

From GoodCycle.zeroWinding_or_isOddWinding_of_not_sweep: non-sweep implies
zero winding OR odd winding. So the only possibilities are:
  - Sweep
  - Zero winding
  - Odd winding

And odd winding + non-uniform is proved. Odd winding + uniform is impossible
(binary parity). So odd winding is fully handled.

Zero winding: all_stay proved, safe_processor proved. Remaining: cw>0 + no safe.

Non-zero winding: sweep proved, odd winding proved. Wait — non-zero winding
that's non-sweep must be odd winding. So nonZeroWinding_shadow is used for
non-zero-winding that's non-sweep = odd winding. But odd winding is already
handled!

WAIT. Let me re-read the code more carefully.

In subThreshold_obstruction:
  by_cases hzero : gc.zeroWinding
  · -- zero winding branch
    by_cases hcw : gc.cwStepCount = 0
    · all_stay_contradicts_convergence  (proved)
    · by_cases hsafe : ∃ safe proc
      · small_arc_contradicts_convergence  (proved)
      · large_arc_zeroWinding_ec  (AXIOM)
  · -- non-zero winding branch
    nonZeroWinding_shadow  (AXIOM)

But in Theorem.lean, the case split is different:
  cycle_classification gives: WaterfallCycle OR zeroWinding

If WaterfallCycle: shadow_cycle_mirror_theorem (proved)
If zeroWinding: palindromic_entry_conflict_theorem or
  universal_entry_conflict_nonconsec (both route to axiom)

The nonZeroWinding_shadow axiom is used in subThreshold_obstruction,
which is called by zeroWinding_obstruction (ignoring the hzero hypothesis)
and nonZeroWinding_obstruction.

But nonZeroWinding_obstruction is NOT directly called by Theorem.lean!
It's only used through subThreshold_obstruction.

So the real question is: can we replace subThreshold_obstruction with
a proof that doesn't use the two axioms?

The proven ingredients are:
  P1: all_stay_contradicts_convergence (zero-winding, cw=0)
  P2: small_arc_contradicts_convergence (safe processor exists)
  P3: shadow_cycle_mirror_theorem (WaterfallCycle)
  P4: not_uniformDirection_and_isOddWinding_of_hasGe3Binary

From P3 and P4: non-zero-winding is handled
  (non-sweep odd winding + non-uniform = contradiction;
   sweep = WaterfallCycle = shadow contradiction)

From P1: zero-winding + cw=0 is handled

So the ONLY remaining case is:
  ZERO-WINDING + cw > 0 + NO SAFE PROCESSOR

This is a single axiom to prove: large_arc_zeroWinding_ec.

The nonZeroWinding_shadow axiom is actually redundant! Let me verify...
""")

    # Check: is non-zero winding fully handled by existing proved theorems?
    print("=" * 80)
    print("CHECKING: Is nonZeroWinding_shadow redundant?")
    print("=" * 80)
    print("""
From Theorem.lean, cycle_classification gives:
  (∃ wc : WaterfallCycle sys, wc.toGoodCycle = gc) ∨ gc.zeroWinding

Case 1: WaterfallCycle exists
  => shadow_cycle_mirror_theorem => ¬converges => False  ✓ PROVED

Case 2: gc.zeroWinding
  => Need to prove False from zero-winding + sub-threshold + n>=9 + converges

So the master theorem can be proved from:
  1. shadow_cycle_mirror_theorem (for non-zero-winding via WaterfallCycle)
  2. A single new theorem for zero-winding

Wait, but cycle_classification itself uses cycle_classification_residual
which uses sweep_obstruction (which calls subThreshold_obstruction) and
oddWinding_nonUniform_obstruction (which also calls subThreshold_obstruction).

So cycle_classification ITSELF depends on the axioms through
subThreshold_obstruction!

Let me trace more carefully:

cycle_classification (Theorem.lean line 72):
  h3bin from subThreshold_ge3_binary  (no axiom)
  hnoUniformOdd from not_uniformDirection_and_isOddWinding  (no axiom)
  calls cycle_classification_residual

cycle_classification_residual (line 49):
  by_cases hsweep : gc.isSweep
  · sweep_obstruction  => subThreshold_obstruction  => AXIOM!
  · by_cases hzw : gc.zeroWinding
    · Or.inr hzw  (returns zero winding)
    · odd winding, but ¬uniformDirection (from hnoUniformOdd)
      oddWinding_nonUniform_obstruction => subThreshold_obstruction => AXIOM!

So cycle_classification uses sweep_obstruction for sweeps, which routes
through the axioms. But sweeps are ALREADY proved by shadow_cycle_mirror_theorem!

The issue: cycle_classification doesn't know about WaterfallCycle directly.
It classifies sweeps via gc.isSweep (|displacement| >= 2n), but the
shadow proof needs WaterfallCycle (which has more structure).

BREAKTHROUGH REALIZATION: The current Lean code has a LAYERING PROBLEM.

The right structure is:
  1. Prove: non-zero-winding => ∃ WaterfallCycle (or use existing mechanism)
  2. WaterfallCycle => shadow => ¬converges => False  (PROVED)
  3. zero-winding => need new theorem

But currently, step 1 goes through subThreshold_obstruction (which uses axioms)
for the sweep and odd-winding cases, making everything circular.

FIX: Restructure to avoid cycle_classification when possible.

NEW PROOF of subThreshold_obstruction:
  by_cases hzero : gc.zeroWinding
  · -- Zero winding: ONLY remaining axiom case
    by_cases hcw : gc.cwStepCount = 0
    · all_stay_contradicts_convergence  (PROVED)
    · by_cases hsafe : safe processor
      · small_arc_contradicts_convergence  (PROVED)
      · NEED: new theorem for zero-winding + cw>0 + no safe proc
  · -- Non-zero winding:
    -- Must be sweep or odd winding
    by_cases hsweep : gc.isSweep
    · -- Sweep: need to show WaterfallCycle exists, then use shadow
      -- OR: find alternative that doesn't need WaterfallCycle
      sorry  -- HARD: connecting isSweep to WaterfallCycle
    · -- Non-sweep non-zero: must be odd winding
      have hodd := (gc.zeroWinding_or_isOddWinding_of_not_sweep hsweep).resolve_left hzero
      -- Odd winding + sub-threshold => >=3 binary => not (uniform + odd)
      have h3bin := subThreshold_ge3_binary sys.rs hsub
      have := gc.not_uniformDirection_and_isOddWinding_of_hasGe3Binary h3bin
      -- Need: odd winding + ¬uniform + sub-threshold => False
      -- The existing proof handles this! ...but does it?
      -- oddWinding_nonUniform_obstruction calls subThreshold_obstruction => circular
      sorry  -- NEED: direct proof for odd winding non-uniform

So even the non-zero winding case has problems. The current code routes
everything through subThreshold_obstruction, creating circularity.

REAL BREAKTHROUGH: We need to prove the non-zero-winding case DIRECTLY
(without going through subThreshold_obstruction), AND prove the
zero-winding + cw>0 + no-safe-proc case directly.

For non-zero winding + non-sweep: odd winding.
  Odd winding + >=3 binary => ¬uniform direction (PROVED)
  But ¬uniform doesn't directly give False. We need more.

  Actually, oddWinding_nonUniform_obstruction doesn't prove anything new!
  It just calls subThreshold_obstruction. So the odd winding non-uniform
  case is NOT actually handled by existing proofs.

This means there are actually TWO unsolved cases, and the current
code obscures this by routing both through subThreshold_obstruction.

The two axioms correctly capture the two hard cases:
  1. Zero winding + cw>0 + no safe proc
  2. Non-zero winding (which for non-sweep = odd winding non-uniform)

For case 2: the WaterfallCycle approach handles sweeps.
For odd winding non-uniform non-sweep: this IS the nonZeroWinding_shadow case.

So both axioms ARE needed and are NOT redundant.
""")


if __name__ == "__main__":
    main()
