#!/usr/bin/env python3
"""
Check: does any sub-threshold system for small n have a zero-winding good cycle
with CW steps and no safe processor?

If no such system exists, the axiom large_arc_zeroWinding_ec is vacuously true.
"""
from itertools import product as iproduct

def check_n5():
    """For n=5, sub-threshold means product < 4*3^3 = 108.
    Exhaustively check all multisets with product < 108."""
    n = 5

    # Generate all ms with product < 108, each m[i] >= 2
    results = []
    for m0 in range(2, 108):
        for m1 in range(2, 108 // m0 + 1):
            for m2 in range(2, 108 // (m0*m1) + 1):
                for m3 in range(2, 108 // (m0*m1*m2) + 1):
                    for m4 in range(2, 108 // (m0*m1*m2*m3) + 1):
                        prod = m0*m1*m2*m3*m4
                        if prod >= 108:
                            continue
                        ms = [m0, m1, m2, m3, m4]
                        # Check: has >= 3 binary
                        bin_count = sum(1 for m in ms if m == 2)
                        if bin_count < 3:
                            continue
                        results.append((ms, prod))

    print(f"n=5: {len(results)} sub-threshold multisets with >= 3 binary")

    # For each, enumerate all possible transition functions and find good cycles
    zero_winding_found = 0
    for ms, prod in results[:3]:  # Just check a few
        print(f"  ms={ms}, product={prod}")
        all_configs = list(iproduct(*(range(m) for m in ms)))
        total = len(all_configs)
        print(f"    {total} configs")

        # Count how many systems have zero-winding good cycles
        # This is exponential in the number of table entries, so just report
        total_entries = sum(ms[(i-1)%n] * ms[i] * ms[(i+1)%n] for i in range(n))
        total_systems = 1
        for i in range(n):
            entries = ms[(i-1)%n] * ms[i] * ms[(i+1)%n]
            total_systems *= ms[i] ** entries
        print(f"    Total systems: ~{total_systems:.2e}")

    return results

def check_mover_words(n):
    """Check: what mover words are possible for zero-winding good cycles?
    A mover word is a closed walk on C_n starting from some vertex.
    Zero winding: sum of signed steps = 0.
    CW step count > 0.
    No safe processor: every processor is within dist 1 of the walk."""

    # For small cycle lengths, enumerate all closed walks
    max_len = 3 * n  # reasonable upper bound
    count_zw = 0
    count_zw_nosafe = 0

    for length in range(n, max_len + 1):
        # Generate closed walks of given length
        # This is exponential, so only do small n
        if n > 6 or length > 20:
            break

        # Count closed walks with zero winding, CW > 0, no safe proc
        # Use dynamic programming
        # State: (current position, CW count, CCW count, visited neighborhoods)

        # Actually this is too complex. Let me just check small cases.
        pass

    print(f"n={n}: skipping full enumeration")

def main():
    print("Checking if large_arc_zeroWinding_ec hypotheses are satisfiable\n")

    # Key insight: the axiom's hypotheses include convergence.
    # A zero-winding good cycle with CW steps in a sub-threshold system
    # that converges... does this combination exist?

    # From the CUP-2 analysis: the CUP-2 system has odd-winding (non-zero) cycles.
    # The axiom handles the zero-winding case.

    # Mathematical argument: if we can show that EVERY sub-threshold
    # convergent system with n>=9 has a NON-zero-winding good cycle,
    # then the axiom is vacuously true.

    # But the theorem structure assumes the cycle IS zero-winding
    # (case split in subThreshold_obstruction).

    # Actually, the key is: the axiom together with other proved theorems
    # covers ALL cases. The non-zero winding case is handled by
    # nonZeroWinding_shadow. The zero-winding + no CW is handled by
    # all_stay_contradicts_convergence. The zero-winding + CW + safe proc
    # is handled by small_arc_contradicts_convergence.

    # So the question is: is the zero-winding + CW + no safe proc case
    # genuinely reachable, or is it excluded by the other cases?

    # If it's excluded, we can prove it by showing one of:
    # (a) zero-winding + CW implies safe proc exists, or
    # (b) zero-winding + no safe proc implies CW = 0, or
    # (c) convergence + sub-threshold + n>=9 implies not zero-winding

    # Let's check (a): does zero-winding + CW always give a safe proc?

    # A zero-winding cycle with CW steps has both CW and CCW.
    # The mover visits some subset of processors.
    # If the mover word doesn't visit the full ring, some proc is safe.

    # For a zero-winding closed walk on C_n:
    # The walk must return to start with equal CW and CCW steps.
    # It visits some arc of the ring.
    # Processors far from this arc are safe.

    # WAIT: Can a zero-winding walk visit all neighborhoods?
    # Yes! Consider the walk: 0,1,2,...,k,...,2,1,0 (BAF with turnaround at k).
    # This has k CW + k CCW = 2k steps, displacement 0.
    # It visits procs 0..k and their left/right neighbors.
    # For all neighborhoods to be covered, we need k >= n-2:
    # right(k) = k+1 needs to be covered. left(0) = n-1 needs to be covered.
    # Visit of proc 0 covers neighborhood {n-1, 0, 1}.
    # Visit of proc k covers neighborhood {k-1, k, k+1}.
    # For ALL procs to be within dist 1: need 0's neighborhood to cover left,
    # and k's neighborhood to cover right. So need k+1 >= n-2 and n-1 >= -1.
    # Actually, need every proc q to have q in {0..k} or (q-1)%n in {0..k} or (q+1)%n in {0..k}.
    # = every proc q is in {0..k} union {(0-1)%n} union {k+1} = {n-1, 0, 1, ..., k, k+1}.
    # So need k+1 >= n-1, i.e., k >= n-2.
    # BAF with k=n-2 covers all neighborhoods: {n-1, 0, 1, ..., n-2, n-1} = all.
    # Length = 2(n-2) steps + ... but wait, the BAF word as a mover word is:
    # [0, 1, 2, ..., n-2, n-3, ..., 1, 0] (then closes).
    # This has n-2 CW steps and n-2 CCW steps. Zero winding.
    # CW count = n-2 > 0 for n >= 3.
    # No safe proc if k >= n-2.

    # So the BAF pattern [0,1,...,n-2,...,1,0] IS a valid zero-winding mover word
    # with CW > 0 and no safe processor. The hypotheses ARE satisfiable
    # (at the mover-word level).

    # The question is whether such a mover word can arise as a good cycle
    # in a convergent sub-threshold system.

    print("Zero-winding + CW + no safe proc IS possible as a mover word pattern")
    print("(e.g., BAF word [0,1,...,n-2,...,1,0])")
    print()
    print("The axiom must be proved genuinely, not vacuously.")
    print()

    # So the proof needs to use sub-threshold + convergence to derive False.
    # The key is the entry conflict construction via BAFArcAdj.

    # For a BAF word like [0,1,...,k,...,1,0]:
    # Edge (j, j+1) for j in {0,...,k-1}:
    #   CW crossing at step j (mover=j, next=j+1)
    #   CCW crossing at step 2k-j (mover=j+1, next=j)
    #   Gap = 2k-j - j = 2(k-j)
    # For gap=2: k-j=1, so j=k-1. Edge (k-1, k).
    # CW crossing at step k-1, CCW crossing at step k+1.
    # Between: step k (mover=k, could be stay or CW).

    # Wait, in the BAF [0,1,...,k,k-1,...,0]:
    # Step 0: mover=0, next=1 (CW)
    # Step 1: mover=1, next=2 (CW)
    # ...
    # Step k-1: mover=k-1, next=k (CW)
    # Step k: mover=k, next=k-1 (CCW) -- REVERSAL
    # Step k+1: mover=k-1, next=k-2 (CCW)
    # ...
    # Step 2k-1: mover=1, next=0 (CCW)
    # Step 2k: mover=0, next=? (closes cycle or continues)

    # Edge (k-1, k):
    # CW crossing at step k-1 (mover=k-1, stepDir=cw)
    # At step k: mover=k, stepDir=ccw (mover goes k->k-1)
    # So CCW crossing of edge (k-1, k) at step k: mover=k=right(k-1), stepDir=ccw.
    # Gap = k - (k-1) = 1.

    # So the minimum gap at edge (k-1, k) is 1, not 2!
    # We need gap >= 2 for BAFArcAdj.

    # What about edge (k-2, k-1)?
    # CW crossing at step k-2 (mover=k-2, stepDir=cw)
    # CCW crossing at step k+1 (mover=k-1=right(k-2), stepDir=ccw)
    # Steps between: k-1 (mover=k-1, CW) and k (mover=k, CCW).
    # Check no crossing of edge (k-2, k-1) in (k-2, k+1):
    #   Step k-1: mover=k-1, stepDir=cw -> this IS a CW crossing of edge (k-1, k), NOT (k-2, k-1).
    #     Actually, CW crossing of edge (k-2, k-1) requires moverAt=k-2 and stepDir=cw. moverAt(k-1)=k-1 != k-2.
    #   Step k: mover=k, stepDir=ccw -> CCW crossing of edge (k-2, k-1) requires moverAt=k-1. moverAt(k)=k != k-1.
    # So NO crossing of edge (k-2, k-1) between steps k-2 and k+1. Gap = 3.
    # But gap >= 2 is what we need!

    # Check BAFArcAdj for edge (k-2, k-1) with proc=k-2:
    # cwProcStep = k-2 (mover=k-2)
    # cwNeighborStep = k-1 (mover=k-1=right(k-2))
    # ccwNeighborStep = k+1 (mover=k-1=right(k-2))
    # ccwProcStep = k+2 (mover=k-2)
    # Adjacency: (k+2) = (k+1) + 1 -> need moverAt(k+2) = k-2

    # In BAF [0,1,...,k,...,1,0] with k=n-2:
    # Step k+2: mover = k-2 (going CCW from k-1 -> k-2). YES!
    # moverAt(k+2) = k-2 = proc. CORRECT.

    # No-fire conditions:
    # proc=k-2 doesn't fire in [k-1, k+2): steps k-1(mover=k-1), k(mover=k), k+1(mover=k-1).
    #   k-2 != k-1, k-2 != k, k-2 != k-1. YES for n >= 5.
    # left(proc)=k-3 doesn't fire in [k-1, k+2): movers are k-1, k, k-1.
    #   k-3 != k-1, k-3 != k, k-3 != k-1. YES for n >= 6.
    # right(proc)=k-1 doesn't fire in (k-1, k+1): step k (mover=k). k != k-1. YES for n >= 4.

    # So for the BAF word, edge (k-2, k-1) with proc=k-2 gives a valid BAFArcAdj!
    # And right(proc) = k-1. Is k-1 binary?
    # In a sub-threshold system with >= 3 binary, some processors ARE binary.
    # But k-1 might not be binary.

    # However, we can choose which edge to use. We need right(proc) to be binary.
    # With >= 3 binary, we can find a binary processor and use the edge to its left.

    # Key: for a BAF word [0,1,...,k,...,1,0], every interior edge (j, j+1) for j in {0,...,k-2}
    # gives a valid BAFArcAdj pattern with proc=j and right(proc)=j+1.
    # We need j+1 to be binary.
    # With >= 3 binary among processors {0,...,n-1}, and the BAF visiting {0,...,k} with k=n-2:
    # The processors {1, ..., k-1} = {1, ..., n-3} are interior.
    # With >= 3 binary total, at least one binary is in {1, ..., n-3} (for n >= 9).
    # Actually we need j+1 to be binary, where j in {0,...,k-2} = {0,...,n-4}.
    # So we need a binary processor in {1, ..., n-3}.
    # With >= 3 binary out of n processors, for n >= 9, it's very likely but not certain
    # that one is in {1,...,n-3}.

    # Actually, for n >= 9 with >= 3 binary: the binary procs could theoretically
    # all be at {0, n-2, n-1}. Then none of {1,...,n-3} is binary.
    # But 0 and n-1 are endpoints, and n-2 is the turnaround.

    # We can choose the BAF starting point! The BAF doesn't have to start at 0.
    # We can rotate it to start at any processor. A BAF from a to a+k and back:
    # visits {a, a+1, ..., a+k}. Interior edges (a+j, a+j+1) for j in {0,...,k-2}.
    # We need a+j+1 to be binary for some j.

    # With >= 3 binary processors spread around the ring, for ANY starting position,
    # the arc {a+1, ..., a+k-1} (of length k-1 = n-3) contains at least...
    # well, with n >= 9 and >= 3 binary, by pigeonhole, in any n-3 consecutive procs,
    # there's at least one binary (since the remaining 2 procs can contain at most 2 non-binary).
    # Wait no, 3 binary out of n, and we're looking at n-3 out of n procs.
    # The 3 binary could be in the 3 procs we're NOT looking at.
    # So we can't guarantee a binary in {a+1,...,a+k-1} from pigeonhole alone.

    # But we can choose the starting position! With 3 binary procs b1, b2, b3,
    # if we choose a such that b1 is in {a+1,...,a+n-3}, that works.
    # Since {a+1,...,a+n-3} has n-3 elements out of n, and there are 3 binary procs,
    # by pigeonhole: among the 3 binary procs, at most 3 can be outside {a+1,...,a+n-3}
    # (which has size 3: {a-2, a-1, a} mod n). So we need at least one binary NOT in {a-2,a-1,a}.
    # With 3 binary and only 3 "bad" slots, it's possible all 3 binary are in {a-2,a-1,a}.
    # But we can vary a! For each a, the bad set is {a-2,a-1,a}. For different a values,
    # the bad sets are different. The 3 binary procs can be in at most one bad set
    # (they'd need to be 3 consecutive procs). So if the 3 binary are not all consecutive,
    # we can find a good a.

    # If the 3 binary ARE all consecutive, that's the "3 consecutive binary" case,
    # which is handled by the palindromic entry conflict (case 3a).

    # If the 3 binary are NOT all consecutive, we can find a good starting position
    # for the BAF where at least one binary is in the interior.

    # ACTUALLY: the proof doesn't know the BAF starts at any particular position.
    # The good cycle's mover word might not be a simple BAF pattern.
    # We need to work with whatever mover word the good cycle gives us.

    # The key insight: from the paired crossing lemma, we get paired crossings
    # at SOME edge. We need to CHOOSE which edge based on binary processor placement.

    print("Analysis complete. The proof strategy:")
    print("1. Sub-threshold -> >= 3 binary")
    print("2. Zero-winding + CW > 0 -> exists edge with CW crossing")
    print("3. Paired crossing lemma -> paired CW/CCW at that edge")
    print("4. Choose edge so right(proc) is binary")
    print("5. Show gap >= 2 (or handle gap-1 separately)")
    print("6. Construct BAFArcAdj -> elim_of_binary_right -> False")
    print()
    print("Gap-1 issue: at reversal points, gap = 1.")
    print("Need to go one edge further from the turnaround to get gap >= 2.")
    print("For this, the proof needs:")
    print("  - cwStepCount >= 2 (so there's an interior CW edge)")
    print("  - A binary processor at an interior edge")

main()
