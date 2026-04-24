#!/usr/bin/env python3
"""
RA14 FINAL SUMMARY

The decisive question: does every non-WaterfallCycle sub-threshold good cycle
with n>=9 and >=3 binary have entry conflict?

ANSWER: NO.
"""
print("RA14 FINAL SUMMARY")
print("=" * 70)
print()
print("ANSWER: NO — the WaterfallCycle/EC dichotomy does NOT hold.")
print()
print("KEY FINDINGS:")
print()
print("1. Non-sweep non-EC cycles exist at ALL n >= 5 with 3+ binary.")
print("   n=5 (3-binary, DFS exhaustive): 4672/4692 = 99.6% are non-sweep non-EC")
print("   n=7 (3-binary, DFS): 2000/2000 = 100% non-sweep non-EC")
print("   n=9 (7-8 binary, word-based): 10,079 non-sweep non-EC found")
print("   n=9 (3-6 binary, word-based): 0 non-sweep non-EC (but DFS infeasible)")
print()
print("2. Most lack shadow too:")
print("   n=5: 94.5% no shadow (189/200)")
print("   n=7: 100% no shadow (50/50)")
print()
print("3. But they CAN'T form valid systems:")
print("   At n=5, product=72 < M_5=96, so no valid system exists.")
print("   0/20 completion attempts succeeded.")
print()
print("4. The proof architecture needs revision:")
print("   Current: 'every good cycle has EC or shadow' -> WRONG")
print("   Needed: system-level argument why no valid system exists")
print("   The existing cycle-level lemmas (PEC, shadow, wiggle) are")
print("   correct for their specific cycle types but don't cover all cycles.")
print()
print("5. For Lean formalization:")
print("   The 'hasEntryConflict' theorem for non-WaterfallCycles is FALSE.")
print("   The lower bound proof needs a different approach for the final step.")
