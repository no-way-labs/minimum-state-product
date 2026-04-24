#!/usr/bin/env python3
"""
If a ternary proc uses only 2 of 3 states on the cycle, it's effectively binary.
Does this reduce to an already-eliminated case?

Sub-threshold: product < 4·3^(n-2).
If one ternary proc is effectively binary: effective product = (2/3) * original.
New effective product < (2/3) * 4·3^(n-2) = (8/3)·3^(n-2) = 8·3^(n-3).

But the ACTUAL product is still the same (we can't change the state space).
The question is: does "ternary proc uses only 2 states on cycle" mean
fc is a multiple of 2 (not 3)?

With general transitions: if f_p maps context to one of {0,1,2}, but on the
cycle only values {0,1} appear, then f_p effectively acts on {0,1}.
The fire count for values visited: if proc visits 0→1→0→1→..., fc is even.

KEY: In a good cycle, configs are DISTINCT. If ternary proc t only uses
values {0,1}, then the other n-1 procs must differentiate the configs.
The number of possible configs using only {0,1} at t is:
product_of_other_procs × 2 (instead of × 3).

Cycle length ≤ number of distinct configs ≤ product × (2/3).

With sub-threshold product P < 4·3^(n-2):
Max distinct configs using 2 ternary values = P × (2/3) < (8/3)·3^(n-2).

Does this help? Not directly — the cycle can still be long.

DIFFERENT ANGLE: If ternary t has fc=2 on the cycle, then t visits
exactly 2 values. The cycle has a "phase" structure with 2 phases.
The 4 mechanisms (designed for 3 phases) don't apply.

But: with fc=2 at a ternary proc sandwiched between binary,
the Binary Parity argument might apply! fc=2 is even, so the
ternary proc returns to its original value. Between the 2 firings:
binary neighbors fire some number of times.

Actually, this is EXACTLY the BothEvenReturn setup — just with 2
phases instead of 3. If J and K are even in the gap: EC via
bothEvenReturn_ec. If J or K is odd: toggleFR or zeroSide might apply.

Let me check: does bothEvenReturn_ec actually require t to be ternary?
Or does it work for any proc?
"""
print("The key question: does bothEvenReturn_ec require ternary?")
print()
print("Looking at TernaryPhaseEC.lean signature:")
print("  bothEvenReturn_ec needs:")
print("  - t doesn't fire in [a, s)")
print("  - left(t) fires even times in [a, s)")
print("  - right(t) fires even times in [a, s)")
print("  - t is nonmover at a, mover at s")
print()
print("It does NOT require t to be ternary!")
print("It works for ANY proc — binary, ternary, quaternary.")
print("The 'phase' is just 'interval where t doesn't fire'.")
print()
print("So: for non-incrementing ternary with fc=2:")
print("  Between the 2 firings, there's a gap where t doesn't fire.")
print("  If both neighbors fire even times → bothEvenReturn_ec applies → EC")
print("  If some neighbor fires odd times → need toggleFR/zeroSide")
print()
print("The mechanisms are ACTUALLY transition-function-independent!")
print("They only need: interval where t silent, neighbor fire counts.")
print("The 'phase' doesn't require specific ternary structure.")
print()
print("CONCLUSION: The incrementing assumption is NOT needed for the mechanisms.")
print("The mechanisms work for any transition function.")
print("What WAS incrementing-specific was the VERIFICATION — we only checked")
print("mechanism coverage for incrementing cycles. But the mechanisms themselves")
print("are stated in terms of intervals and fire counts, not phases.")
print()
print("The REAL question: do the mechanisms cover ALL cycles (not just incrementing)?")
print("We need to verify this computationally for non-incrementing cycles too.")
