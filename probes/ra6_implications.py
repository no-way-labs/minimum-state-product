#!/usr/bin/env python3
"""
RA6: What does the CF counterexample mean for the existing proof?

The existing proof of M_n = 4*3^(n-2) uses DIFFERENT mechanisms for
different cases. EC is ONE tool, not the only tool. The key question:

1. Does the CF cycle correspond to a multiset that NEEDS EC to be blocked?
2. Or is it already blocked by shadow cycle / other mechanisms?

Check:
- ms=[2,3,3,2,3,3,2,3,3] at n=9: product=5832 < 8748
- The LB proof needs to show NO valid system exists with this ms
- Methods available: shadow cycle, entry conflict, wiggle shadow, etc.

Also: is the CF cycle a VALID good cycle for a potential self-stabilizing system?
Having a CF good cycle is necessary but not sufficient -- we also need:
- ALL other good cycles in the system to also be CF
- The system must have a valid transition function
- The system must converge from any config

The existing proof blocks systems at the MULTISET level, not the individual
cycle level. Even if ONE cycle is CF, if there's no complete valid system,
the multiset is still blocked.

Let's check what the existing proof says about ms=[2,3,3,2,3,3,2,3,3].
"""
from collections import defaultdict

def main():
    print("RA6: Implications of CF Counterexample")
    print("=" * 70)

    n = 9
    ms = [2,3,3,2,3,3,2,3,3]
    prod = 5832
    thresh = 4*3**7  # = 8748

    print(f"n={n}, ms={ms}")
    print(f"Product={prod}, threshold={thresh}")
    print(f"Sub-threshold: {prod < thresh}")
    print(f"Binary positions: {[p for p in range(n) if ms[p]==2]}")

    # Binary count and arrangement
    bin_pos = [p for p in range(n) if ms[p]==2]
    n_binary = len(bin_pos)
    print(f"Binary count: {n_binary}")
    print(f"Binary arrangement: evenly spaced with gap 3")

    # Check which case of the LB proof this falls under
    print(f"\n--- LB Proof Case Analysis ---")
    print(f"The LB proof has cases:")
    print(f"  Case 1: <= 2 binary procs -> product >= 4*3^(n-2) (not sub-threshold)")
    print(f"  Case 2: >= 3 consecutive binary -> Palindromic Entry Conflict")
    print(f"  Case 3a: >= 3 consecutive binary (subset) -> shadow + PEC")
    print(f"  Case 3b: >= 3 non-consecutive binary, gap >= 2 -> various mechanisms")
    print(f"  Case 3c: non-consecutive binary with non-ternary -> shadow")
    print()
    print(f"This multiset: 3 non-consecutive binary, all ternary otherwise")
    print(f"Falls under: Case 3b (BinSCC / CIC)")
    print()

    # The existing proof for non-consecutive binary uses:
    # 1. Shadow cycle for sweep words
    # 2. Entry conflict for non-sweep words
    # The CF counterexample shows EC doesn't always work for non-sweep.
    # But the proof uses SPECIFIC EC mechanisms (Both-Even Return, etc.)
    # that may still apply to the words that MATTER.

    # KEY QUESTION: does the existing proof require EC for ALL ring-adj hfull cycles,
    # or just for specific types?

    print(f"--- Existing Proof Strategy ---")
    print(f"The proof uses the Universal Entry Conflict theorem (BinSCC Expl 10).")
    print(f"It proves: for >= 3 non-adjacent binary at sub-threshold product,")
    print(f"EVERY good cycle has entry conflict.")
    print()
    print(f"But wait -- the 'good cycle' in the theorem means ANY good cycle")
    print(f"that could be part of a valid self-stabilizing system, not just")
    print(f"ring-adjacent ones. The theorem considers ALL possible mover words,")
    print(f"including non-ring-adjacent ones.")
    print()
    print(f"The CF cycle we found is ring-adjacent + hfull + fc=ms.")
    print(f"The question is: does the existing theorem actually handle this case?")
    print()

    # Let's check: the BinSCC proof uses 4 mechanisms.
    # These apply to good cycles with specific STRUCTURAL properties
    # (phases, singleton counts, etc.), not just ring-adjacency.

    # The CF cycle has:
    word = [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0]
    L = len(word)
    fc = [0]*n
    for p in word:
        fc[p] += 1

    print(f"--- CF Cycle Structure Analysis ---")
    print(f"Word: {word}")
    print(f"CL={L}, fc={fc}")

    # Check if this is a "standard" cycle the BinSCC proof considers
    # The BinSCC proof considers cycles on the FULL config space,
    # not just ring-adjacent walks. It uses the transition function
    # to define which configs are good.

    # Actually, the key insight: the BinSCC proof proves EC for ALL
    # good cycles of a valid system. A good cycle is determined by
    # the transition function + the mover word.

    # The CF cycle uses incrementing transition. But the BinSCC proof
    # says EVERY good cycle has EC -- including this one!

    # Wait -- let me re-read the proof claim more carefully.
    # Is the claim about arbitrary mover words, or about mover words
    # that arise from a specific transition function?

    print(f"\n--- Critical Check: Does the CF cycle fit the BinSCC theorem's scope? ---")
    print(f"The BinSCC theorem (Expl 10) states:")
    print(f"  For >= 3 non-adjacent binary, sub-threshold product,")
    print(f"  EVERY good cycle has entry conflict.")
    print()
    print(f"'Good cycle' = a cycle in the config-successor graph of some")
    print(f"  self-stabilizing system. This means:")
    print(f"  - A fixed transition function f for each processor")
    print(f"  - The mover word arises from the system's dynamics")
    print(f"  - The mover at each step is determined by the config")
    print()
    print(f"But our CF cycle uses the INCREMENTING transition f(v)=(v+1)%m")
    print(f"AND a specific mover word. The mover word is NOT determined by")
    print(f"the transition function -- it's a separate input.")
    print()
    print(f"In a self-stabilizing system, the mover at each config is")
    print(f"determined by the SCHEDULER, not the transition function.")
    print(f"The good cycle exists if there's a way to schedule movers")
    print(f"such that the cycle exists.")
    print()
    print(f"So the question becomes: with transition f(v)=(v+1)%m for all procs,")
    print(f"does the system admit this mover schedule? YES, by construction.")
    print()
    print(f"THIS MEANS: the CF cycle IS a valid good cycle for a system using")
    print(f"incrementing transitions. And it has NO entry conflict.")
    print()
    print(f"But the BinSCC theorem claims ALL good cycles have EC.")
    print(f"So either:")
    print(f"  (a) The BinSCC theorem is WRONG, or")
    print(f"  (b) Our CF cycle is not actually a 'good cycle' in the theorem's sense, or")
    print(f"  (c) We're misunderstanding the theorem's scope")
    print()

    # Let me verify: does the incrementing system at ms=[2,3,3,2,3,3,2,3,3]
    # actually produce a valid self-stabilizing system?
    # A self-stabilizing system needs:
    # 1. A transition function for each proc
    # 2. A privileged predicate (when can a proc fire)
    # 3. Convergence: from any config, eventually reach a good cycle

    # In Dijkstra's framework:
    # - f(j) is the transition function for proc j
    # - Proc j is "privileged" iff c[j] != f(c[j-1], c[j], c[j+1]) applied somehow
    # - Actually, in the standard model: proc j fires when its state differs from
    #   what its transition function says it should be, given neighbors

    # The key: entry conflict means the same (L,S,R) triple appears as both
    # mover and non-mover context. If there's no EC, the transition function
    # can distinguish mover from non-mover at every context.

    # Wait -- that's exactly the POINT. No EC means the system CAN be valid
    # (the transition function doesn't have conflicting requirements).

    # So if this CF cycle exists and is part of a valid system,
    # the BinSCC theorem would be WRONG.

    # But maybe the BinSCC theorem has additional constraints we're missing.

    print(f"--- Checking BinSCC Theorem Applicability ---")
    print(f"The BinSCC theorem verified computationally at n=5,6,8.")
    print(f"Our counterexample is at n=9.")
    print(f"The theorem CLAIMS to hold for all n >= 5.")
    print(f"But the analytical proof may have gaps.")
    print()

    # Let's check: at n=6, ms=[2,3,3,2,3,3], same structure!
    print(f"--- Check n=6 with same structure ---")
    n6 = 6
    ms6 = [2,3,3,2,3,3]
    prod6 = 1
    for m in ms6:
        prod6 *= m
    thresh6 = 4*3**(n6-2)
    print(f"n=6, ms={ms6}, product={prod6}, threshold={thresh6}")
    print(f"Sub-threshold: {prod6 < thresh6}")
    print(f"Product = threshold! This is NOT sub-threshold at n=6.")
    print()
    print(f"At n=6: 2^2 * 3^4 = 4 * 81 = 324 = 4 * 3^4 = threshold")
    print(f"The BinSCC theorem requires STRICT sub-threshold.")
    print(f"At n=6 with 2 binary, we're exactly at threshold.")
    print()
    print(f"At n=9: 2^3 * 3^6 = 8 * 729 = 5832 < 4 * 3^7 = 8748")
    print(f"This IS sub-threshold. So the counterexample is real.")
    print()

    # Check: with 3 binary at gap-3, this multiset falls in the BinSCC scope.
    # The BinSCC theorem should handle it.
    # But we found CF cycles!

    # Let me re-examine the BinSCC verification scripts
    print(f"--- BinSCC Verification at n=8 ---")
    print(f"The BinSCC proof was verified at n=5,6,8.")
    print(f"At n=8 with gap-3 binary: ms=[2,3,3,2,3,3,2,3] has only 2 ternary segments")
    print(f"of size 2, but one segment of size 1 -- WAIT:")
    ms8 = [2,3,3,2,3,3,2,3]
    bp8 = [p for p in range(8) if ms8[p]==2]
    print(f"  n=8, ms={ms8}, binary at {bp8}")
    for i in range(len(bp8)):
        p = (bp8[i]+1)%8
        end = bp8[(i+1)%len(bp8)]
        seg = []
        while p != end:
            seg.append(p)
            p = (p+1)%8
        print(f"  Segment {i}: {seg} (size {len(seg)})")
    print(f"  Not all segments have size >= 2 at n=8!")
    print()

    # At n=9 gap-3: each segment has exactly 2 procs.
    # This is the SMALLEST n where gap-3 with 3 binary gives all segments >= 2.
    # And it's exactly where the counterexample appears!

    print(f"--- KEY INSIGHT ---")
    print(f"At n=9 with gap-(3,3,3), each ternary segment has exactly 2 procs.")
    print(f"This is the critical threshold where the wiggle-sweep construction works.")
    print(f"At n=8 with gap-(3,3,2), one segment has only 1 proc -- no wiggle possible.")
    print(f"At n=12 with gap-(4,4,4), segments have 3 procs -- even more room.")
    print()
    print(f"The BinSCC theorem's analytical proof may fail specifically for")
    print(f"arrangements where all ternary segments have >= 2 procs,")
    print(f"because the wiggle-sweep creates enough triple diversity")
    print(f"to avoid mover/nonmover overlap.")
    print()
    print(f"However: this is just about ENTRY CONFLICT.")
    print(f"The overall LB proof also uses SHADOW CYCLES.")
    print(f"Even if EC fails, the shadow mechanism might still block this multiset.")

    # Check: does the word have a shadow cycle?
    print(f"\n--- Shadow Cycle Check ---")
    word = [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0]
    L = len(word)

    # Is this a sweep word?
    dirs = [(word[(i+1)%L] - word[i]) % n for i in range(L)]
    is_sweep = all(d == 1 for d in dirs) or all(d == n-1 for d in dirs)
    print(f"  Is sweep: {is_sweep}")

    # Is this a fc=2 word (each fires exactly twice)?
    # No, fc = ms = [2,3,3,2,3,3,2,3,3]
    print(f"  fc = {fc} (NOT fc=2 for all)")

    # The shadow cycle machinery applies to sweep and fc=2 non-sweep words.
    # This word has fc=ms, which is a DIFFERENT type.
    # The wiggle shadow applies to single-wiggle words.
    # This word has 3 wiggles (direction changes).

    n_wiggles = sum(1 for i in range(L) if dirs[i] != dirs[(i-1)%L])
    print(f"  Direction changes: {n_wiggles}")
    print(f"  Word type: multi-wiggle (not covered by single-wiggle shadow)")
    print()

    # CRITICAL: the existing proof handles different word types differently:
    # - Sweep words: shadow cycle
    # - fc=2 non-sweep: Palindromic Entry Conflict
    # - Single-wiggle: wiggle shadow
    # - Multi-wiggle with >= 3 binary: ???

    # The CF cycle is a multi-wiggle word with fc != 2.
    # It may fall OUTSIDE the scope of the current proof mechanisms!

    print(f"CONCLUSION:")
    print(f"1. The CF cycle at n=9, ms=[2,3,3,2,3,3,2,3,3] is REAL")
    print(f"2. It shows EC is NOT universal for all good cycles on mixed rings")
    print(f"3. The word is a multi-wiggle type with fc=ms (not fc=2)")
    print(f"4. This may or may not invalidate the BinSCC theorem:")
    print(f"   - The theorem verified computationally at n=5,6,8")
    print(f"   - At those n, gap-(3,3,3) with 3 binary doesn't exist (needs n=9)")
    print(f"   - So the theorem may be correct for n<=8 but fail at n=9")
    print(f"5. The overall LB proof must use OTHER mechanisms for this case")
    print(f"   (shadow cycle, counting argument, etc.)")
    print(f"6. The gap-(3,3,3) arrangement is SPECIAL because all ternary")
    print(f"   segments have >= 2 procs, enabling the wiggle-sweep")


if __name__ == "__main__":
    main()
