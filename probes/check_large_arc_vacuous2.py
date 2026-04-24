#!/usr/bin/env python3
"""Check ALL valid sub-threshold systems for zero-winding good cycles.

For n=5,6,7: enumerate ALL multisets with product < 4*3^(n-2) that have
>= 3 binary processors. For each, try ALL possible transition function
assignments and check whether any valid system has a zero-winding good cycle.

Actually, that's too many transition functions. Instead:
- For each ms, enumerate ALL possible good cycles (mover word sequences)
- Check which ones are zero-winding
- For zero-winding ones, check if a valid system can support them

Actually, even simpler: we already know from the memory that ALL sub-threshold
multisets at n=9 fail (M_9 = 8748 = 4*3^7). So there are NO valid sub-threshold
systems at n=9! The axiom is vacuously true!

Let me verify this claim more carefully.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian

def check_sub_threshold_existence(n):
    """Check if ANY valid sub-threshold system exists at given n."""
    threshold = 4 * 3**(n-2)
    print(f"\nn={n}: threshold = 4*3^{n-2} = {threshold}")
    print(f"  Sub-threshold means product < {threshold}")

    # From memory: M_n = 4*3^(n-2) for n >= 9
    # This means the MINIMUM product for a valid system is exactly 4*3^(n-2)
    # So there are NO valid systems with product STRICTLY less than 4*3^(n-2)
    # for n >= 9.

    # For n=5: M_5 = 96 = 32*3^(5-4) = 32*3, threshold = 4*3^3 = 108
    # So 96 < 108: valid sub-threshold systems EXIST at n=5
    # For n=6: M_6 = 32*3^2 = 288, threshold = 4*3^4 = 324
    # So 288 < 324: valid sub-threshold systems EXIST at n=6
    # For n=7: M_7 = 32*3^3 = 864, threshold = 4*3^5 = 972
    # So 864 < 972: valid sub-threshold systems EXIST at n=7
    # For n=8: M_8 = 32*3^4 = 2592, threshold = 4*3^6 = 2916
    # So 2592 < 2916: valid sub-threshold systems EXIST at n=8
    # For n=9: M_9 = 8748 = 4*3^7, threshold = 4*3^7 = 8748
    # So M_9 = threshold: NO sub-threshold system exists!

    M_n_values = {
        5: 96,
        6: 288,
        7: 864,
        8: 2592,
        9: 8748,
        10: 4 * 3**8,
        11: 4 * 3**9,
    }

    if n in M_n_values:
        M_n = M_n_values[n]
        print(f"  M_{n} = {M_n} (minimum product for valid system)")
        if M_n >= threshold:
            print(f"  M_{n} >= threshold => NO valid sub-threshold system exists!")
            print(f"  => large_arc_zeroWinding_ec is VACUOUSLY TRUE at n={n}")
            return False
        else:
            print(f"  M_{n} < threshold => valid sub-threshold systems EXIST")
            return True
    else:
        print(f"  M_{n} not computed, but for n >= 9: M_n = 4*3^(n-2) = threshold")
        print(f"  => NO valid sub-threshold system exists for n >= {n}")
        return False


def main():
    print("=" * 80)
    print("KEY QUESTION: Does large_arc_zeroWinding_ec have any content?")
    print("=" * 80)

    print("\nThe axiom requires: n >= 9, sub-threshold, valid system with good cycle.")
    print("Sub-threshold means product < 4*3^(n-2).")
    print("But M_n = min product for valid system.")
    print()

    for n in range(5, 13):
        check_sub_threshold_existence(n)

    print("\n" + "=" * 80)
    print("CONCLUSION")
    print("=" * 80)
    print()
    print("For n >= 9: M_n = 4*3^(n-2) = threshold.")
    print("Therefore subThreshold means product < 4*3^(n-2) = M_n.")
    print("But a valid system must have product >= M_n.")
    print("CONTRADICTION: no valid sub-threshold system exists for n >= 9.")
    print()
    print("This means large_arc_zeroWinding_ec is VACUOUSLY TRUE for all n >= 9!")
    print("Its hypotheses (valid sub-threshold system) are jointly inconsistent.")
    print()
    print("The proof strategy:")
    print("  subThreshold sys.rs => product < 4*3^(n-2)")
    print("  But the good cycle + convergence imply a valid system exists.")
    print("  And M_n = 4*3^(n-2) means no valid system has product < 4*3^(n-2).")
    print()
    print("WAIT: The axiom doesn't say the system is valid. It says:")
    print("  - GoodCycle exists (implying closure, mutual exclusion, fairness)")
    print("  - converges (well-founded bad-step relation)")
    print("  - subThreshold (product < 4*3^(n-2))")
    print("These ARE the conditions for a valid system!")
    print()
    print("So the proof should be:")
    print("  1. From GoodCycle + converges + liveness (derive from good cycle?)")
    print("     conclude: valid system exists with product < 4*3^(n-2)")
    print("  2. But M_n = 4*3^(n-2) for n >= 9")
    print("  3. Contradiction.")
    print()
    print("BUT WAIT: M_n = 4*3^(n-2) is EXACTLY what we're trying to prove!")
    print("The lower bound theorem IS that no valid system has product < 4*3^(n-2).")
    print("And this axiom is PART of that proof.")
    print("So we can't use the conclusion to prove the axiom.")
    print()
    print("The axiom's role: it handles one CASE in the case analysis that proves")
    print("M_n >= 4*3^(n-2). Specifically, the case where a hypothetical valid")
    print("sub-threshold system has a zero-winding good cycle with CW steps and")
    print("no safe processor.")
    print()
    print("We need to derive False from the axiom's hypotheses WITHOUT assuming")
    print("the lower bound. The existing approach uses entry conflict / shadow cycle")
    print("arguments.")

    print("\n" + "=" * 80)
    print("ALTERNATIVE: Check if the case can be reduced to existing proved theorems")
    print("=" * 80)
    print()
    print("Existing proved theorems in CaseObstructions.lean:")
    print("  1. all_stay_contradicts_convergence: cwStepCount = 0 => False")
    print("  2. small_arc_contradicts_convergence: safe processor exists => False")
    print()
    print("What if we can prove: zero winding + cwStepCount > 0 + sub-threshold")
    print("  => safe processor exists?")
    print("Then the axiom follows from small_arc_contradicts_convergence!")
    print()
    print("Claim: if no safe processor, then every proc is within distance 1 of")
    print("some mover. With n >= 9, the mover visits at least ceil(n/3) distinct")
    print("positions. But zero winding + sub-threshold constrains the mover pattern")
    print("severely...")

    # Let's check: for sub-threshold n=5..8, do all zero-winding good cycles
    # have safe processors?
    print("\n" + "=" * 80)
    print("EMPIRICAL: Check zero-winding cycles at n=5..8")
    print("=" * 80)

    from cup2_theorem import build_system
    from verifier import verify_system, privileged_set, apply_move

    for n in [5, 6, 7, 8]:
        # The M_n witnesses for n=5..8 use ms with a quaternary processor
        # Let's check the known M_n witnesses
        if n == 5:
            # M_5 = 96, ms = (2,2,2,3,4) (from memory)
            # We need the transition functions - use verifier search
            pass

    # Actually, let's just check CUP-2 at small n where it IS sub-threshold
    # CUP-2 has product 4*3^(n-2) which equals the threshold, NOT sub-threshold
    # Sub-threshold is STRICTLY less
    print("\nCUP-2 product = 4*3^(n-2) = threshold, NOT sub-threshold (need <, not <=)")
    print("So CUP-2 itself is not sub-threshold!")

    # What about the 32*3^(n-4) systems for n=5..8?
    # These ARE sub-threshold: 32*3^(n-4) < 4*3^(n-2) iff 32 < 4*9 = 36 ✓
    print("\n32*3^(n-4) systems are sub-threshold (32 < 36 = 4*9)")
    print("These exist for n=5..8 but NOT for n>=9")
    print()
    print("CRITICAL REALIZATION: For n >= 9, ALL valid systems have product >= 4*3^(n-2)")
    print("(because M_9 = 8748 = 4*3^7 and M_n = 4*3^(n-2) for all n >= 9)")
    print("BUT this is circular - this IS the theorem we're proving!")
    print()
    print("To break the circularity, we need to prove this case (zero winding +")
    print("CW > 0 + no safe processor) leads to False from first principles,")
    print("NOT from the lower bound M_n = 4*3^(n-2).")


if __name__ == "__main__":
    main()
