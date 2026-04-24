#!/usr/bin/env python3
"""binscc_general_overlap_conflict.py — Does overlap → conflict for general transitions?

With incrementing: overlap at proc p means f(L,S,R)=S' at mover and f(L,S,R)=S at nonmover.
Since S'=(S+1)%m ≠ S, this is always a conflict. 100%.

With GENERAL transitions: at a mover step, S' could theoretically equal S
(if we assign f(L,S,R)=S). But then p wouldn't fire at that step!
A mover entry MUST have S'≠S (otherwise no token at p).

So: overlap at proc p means context (L,S,R) appears at both:
  - mover step: f(L,S,R) = S' ≠ S (required: processor fires)
  - nonmover step: f(L,S,R) = S (required: processor stays)
Since S'≠S, we need f(L,S,R) to be BOTH S'(≠S) and S → CONTRADICTION.

THIS IS TRANSITION-INDEPENDENT. Overlap → conflict for ALL transitions, not just incrementing!

Let me verify this reasoning and test computationally.
"""

import sys


def main():
    print("=" * 70)
    print("OVERLAP → CONFLICT: TRANSITION-INDEPENDENT PROOF")
    print("=" * 70)
    print()
    print("Claim: For ANY transition function, mover/nonmover context overlap")
    print("at ANY processor creates an entry conflict.")
    print()
    print("Proof:")
    print("  At a mover step for proc p, context = (L, S, R):")
    print("    - p fires → f_p(L,S,R) = S' where S' ≠ S (p has token)")
    print("  At a nonmover step for proc p, same context (L, S, R):")
    print("    - p doesn't fire → f_p(L,S,R) = S (p has no token)")
    print("  Since S' ≠ S, we need f_p(L,S,R) = S' AND f_p(L,S,R) = S.")
    print("  This is impossible → contradiction.")
    print()
    print("NOTE: This requires that the FULL CONTEXT (L,S,R) matches,")
    print("not just a 2D projection. The UBO error was using projections.")
    print("But with full contexts, overlap → conflict is unconditional.")
    print()
    print("=" * 70)
    print("CONSEQUENCE FOR CASE 3a")
    print("=" * 70)
    print()
    print("For sub-threshold product with 3 consecutive binary:")
    print("  1. P1 overlap (transition-independent) kills most mover words")
    print("  2. Full-context overlap at ANY proc → conflict (transition-independent)")
    print("  3. Overlap-free mover words → shadow cycle (tested computationally)")
    print()
    print("Steps 1 and 2 are PROVED (no enumeration needed).")
    print("Step 3 is the only computational gap.")
    print()
    print("But step 2 has a subtlety: 'full-context overlap' means the SAME")
    print("context (L,S,R) appears at both mover and nonmover steps.")
    print("With general transitions, the context values depend on the")
    print("transition function, so the config sequence changes!")
    print()
    print("The correct framework:")
    print("  - A 'mover word' specifies WHICH proc fires at each step")
    print("  - The config sequence depends on the mover word AND transitions")
    print("  - For BINARY procs, transitions are forced (always flip)")
    print("  - For NON-BINARY procs, transitions are free (any S'≠S)")
    print()
    print("So the same mover word can produce DIFFERENT config sequences")
    print("with different transition functions. Overlap might occur with")
    print("one transition assignment but not another.")
    print()
    print("The question becomes: for a given mover word, does EVERY")
    print("valid transition assignment have overlap at some proc?")
    print()
    print("If YES → that mover word can't lead to a valid system")
    print("If NO → need to check shadow for non-overlapping assignments")
    print()
    print("=" * 70)
    print("KEY INSIGHT: OVERLAP IS TRANSITION-FUNCTION-INDEPENDENT")
    print("=" * 70)
    print()
    print("Wait — let me reconsider. The CONTEXT at step i is determined by")
    print("the CONFIG at step i. The config at step i depends on ALL previous")
    print("transitions. So changing one transition changes all subsequent configs.")
    print()
    print("BUT: for BINARY processors, the transition is ALWAYS flip.")
    print("And P1's full context = (c_0, c_1, c_2) where ALL three are binary.")
    print("So P1's context sequence is FULLY DETERMINED by the mover word,")
    print("regardless of non-binary transition choices.")
    print()
    print("For P0: context = (c_{n-1}, c_0, c_1). c_0, c_1 are binary (determined).")
    print("c_{n-1} is non-binary → changes with transition choices.")
    print("So P0 overlap DOES depend on transition choices.")
    print()
    print("Similarly P2: context = (c_1, c_2, c_3). c_1, c_2 binary, c_3 non-binary.")
    print()
    print("And for P3,P4,...: contexts involve non-binary neighbors.")
    print()
    print("CONCLUSION:")
    print("  - P1 overlap is transition-independent (proved)")
    print("  - P0,P2 overlap depends on non-binary neighbor values (transition-dependent)")
    print("  - P3+ overlap is fully transition-dependent")
    print()
    print("So the hierarchy is:")
    print("  A. Mover words with P1 overlap → killed (for ANY transitions)")
    print("  B. P1-free mover words → need separate analysis")
    print("     B1. With incrementing: overlap at P0/P2/P3/P4 → conflict")
    print("     B2. With incrementing: no overlap → shadow")
    print("     B3. With general transitions: might avoid P0/P2 overlap")
    print("         → need to show shadow still forms")
    print()
    print("The general transition test at n=5 showed:")
    print("  - For overlap-free mover words, only 1/64 assignments valid")
    print("  - That 1 assignment (incrementing) has shadow")
    print("  → These mover words are fully blocked")
    print()
    print("For P1-free mover words WITH incrementing overlap:")
    print("  - With general transitions, overlap might disappear")
    print("  - But shadow might still form with different entries")
    print("  → Need to test ALL valid transition assignments")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
