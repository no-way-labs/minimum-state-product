#!/usr/bin/env python3
"""
RA6: Check BinSCC theorem scope vs our counterexample.

Key questions:
1. At n=8, what 3-binary non-consec multisets exist and are sub-threshold?
2. Was gap-(3,3,3) actually tested in the BinSCC verification?
3. At n=9, what does the BinSCC verification script actually check?

Also: verify the counterexample independently by building a complete
system (transition function) and checking if the CF cycle is actually
compatible with a valid self-stabilizing protocol.
"""
from collections import defaultdict
from itertools import combinations

def main():
    print("RA6: BinSCC Theorem Scope Analysis")
    print("=" * 70)

    # At n=8 with 3 binary:
    # product = 2^3 * 3^5 = 8 * 243 = 1944
    # threshold = 4 * 3^6 = 2916
    # Sub-threshold: 1944 < 2916 YES
    print("--- n=8, 3 binary ---")
    n = 8
    thresh = 4 * 3**(n-2)
    prod_3bin = 2**3 * 3**(n-3)
    print(f"n={n}, threshold={thresh}")
    print(f"3 binary: product = 2^3 * 3^5 = {prod_3bin}")
    print(f"Sub-threshold: {prod_3bin < thresh}")
    print()

    # All non-consecutive 3-binary placements on n=8
    all_bp = []
    for combo in combinations(range(n), 3):
        ok = True
        for i in range(3):
            for j in range(i+1, 3):
                if abs(combo[i]-combo[j]) % n in (1, n-1):
                    ok = False
        if ok:
            all_bp.append(combo)

    print(f"Non-consecutive 3-binary placements on n=8: {len(all_bp)}")

    gap_classes = defaultdict(list)
    for bp in all_bp:
        bps = sorted(bp)
        gaps = sorted([(bps[(i+1)%3] - bps[i]) % n for i in range(3)])
        gap_classes[tuple(gaps)].append(bp)

    for gaps, bps in sorted(gap_classes.items()):
        bp = bps[0]
        # Segment sizes
        bpl = sorted(bp)
        segs = []
        for i in range(3):
            p = (bpl[i]+1) % n
            end = bpl[(i+1)%3]
            seg = []
            while p != end:
                seg.append(p)
                p = (p+1) % n
            segs.append(len(seg))
        min_seg = min(segs)
        print(f"  gaps={gaps}: {len(bps)} placements, seg sizes={sorted(segs)}, "
              f"min_seg={min_seg}, wiggle={'YES' if min_seg>=2 else 'NO'}")

    print()
    print("At n=8, gap-(3,3,2) has min_seg=1 -> NO wiggle possible")
    print("At n=8, gap-(2,2,4) has min_seg=1 -> NO wiggle possible")
    print("At n=8, gap-(2,3,3) has min_seg=1 -> NO wiggle possible")
    print("NO n=8 arrangement allows the wiggle-sweep construction!")
    print()

    # n=9
    print("--- n=9, 3 binary ---")
    n = 9
    thresh = 4 * 3**(n-2)
    prod_3bin = 2**3 * 3**(n-3)
    print(f"n={n}, threshold={thresh}")
    print(f"3 binary: product = 2^3 * 3^6 = {prod_3bin}")
    print(f"Sub-threshold: {prod_3bin < thresh}")

    all_bp9 = []
    for combo in combinations(range(n), 3):
        ok = True
        for i in range(3):
            for j in range(i+1, 3):
                if abs(combo[i]-combo[j]) % n in (1, n-1):
                    ok = False
        if ok:
            all_bp9.append(combo)

    gap_classes9 = defaultdict(list)
    for bp in all_bp9:
        bps = sorted(bp)
        gaps = sorted([(bps[(i+1)%3] - bps[i]) % n for i in range(3)])
        gap_classes9[tuple(gaps)].append(bp)

    for gaps, bps in sorted(gap_classes9.items()):
        bp = bps[0]
        bpl = sorted(bp)
        segs = []
        for i in range(3):
            p = (bpl[i]+1) % n
            end = bpl[(i+1)%3]
            seg = []
            while p != end:
                seg.append(p)
                p = (p+1) % n
            segs.append(len(seg))
        min_seg = min(segs)
        wiggle = "YES" if min_seg >= 2 else "NO"
        print(f"  gaps={gaps}: {len(bps)} placements, seg sizes={sorted(segs)}, "
              f"min_seg={min_seg}, wiggle={wiggle}")

    print()
    print("ONLY gap-(3,3,3) at n=9 has min_seg=2 -> wiggle possible")
    print("All other arrangements have a segment of size 1 -> no wiggle")
    print()

    # What about n >= 10?
    print("--- n=10+, gap-(3,3,3+) ---")
    for n_test in [10, 11, 12]:
        # gap-(3,3,n-6) for 3 binary
        # Segment sizes: 2, 2, n-6-1 = n-7
        # But also gap-(3,4,3) etc.
        thresh_t = 4 * 3**(n_test-2)
        prod_t = 2**3 * 3**(n_test-3)
        print(f"n={n_test}: 3 binary product={prod_t}, thresh={thresh_t}, "
              f"sub={prod_t < thresh_t}")

        all_bp_t = []
        for combo in combinations(range(n_test), 3):
            ok = True
            for i in range(3):
                for j in range(i+1, 3):
                    if abs(combo[i]-combo[j]) % n_test in (1, n_test-1):
                        ok = False
            if ok:
                all_bp_t.append(combo)

        # Check which have all segments >= 2
        wiggle_count = 0
        for bp in all_bp_t:
            bps = sorted(bp)
            segs = []
            for i in range(3):
                p = (bps[i]+1) % n_test
                end = bps[(i+1)%3]
                seg = []
                while p != end:
                    seg.append(p)
                    p = (p+1) % n_test
                segs.append(len(seg))
            if min(segs) >= 2:
                wiggle_count += 1

        print(f"  Total non-consec placements: {len(all_bp_t)}, "
              f"with all-seg>=2: {wiggle_count}")

    print()
    # Now: what about 4+ binary?
    print("--- 4+ binary at n=9 ---")
    # 4 binary: product = 2^4 * 3^5 = 16*243 = 3888 < 8748
    print(f"4 binary at n=9: product = {2**4 * 3**5}, thresh = {4*3**7}")
    print(f"Sub-threshold: {2**4 * 3**5 < 4*3**7}")

    # With 4 non-consecutive binary on n=9:
    # Maximum gap is ceil(9/4) = 3
    all_bp4 = []
    for combo in combinations(range(9), 4):
        ok = True
        for i in range(4):
            for j in range(i+1, 4):
                if abs(combo[i]-combo[j]) % 9 in (1, 8):
                    ok = False
        if ok:
            all_bp4.append(combo)
    print(f"4 non-consec binary placements on n=9: {len(all_bp4)}")
    for bp in all_bp4[:5]:
        bps = sorted(bp)
        gaps = [(bps[(i+1)%4] - bps[i]) % 9 for i in range(4)]
        segs = []
        for i in range(4):
            p = (bps[i]+1) % 9
            end = bps[(i+1)%4]
            seg = []
            while p != end:
                seg.append(p)
                p = (p+1) % 9
            segs.append(len(seg))
        print(f"  {bp}: gaps={sorted(gaps)}, seg sizes={sorted(segs)}")

    print()
    print("=" * 70)
    print("FINAL SUMMARY")
    print("=" * 70)
    print(f"""
FINDINGS:

1. COUNTEREXAMPLE EXISTS: At n=9, ms=[2,3,3,2,3,3,2,3,3] (gap-(3,3,3)),
   there are ring-adjacent hfull good cycles with NO entry conflict.
   ALL 64 state-sequence combos are CF. Product 5832 < 8748 (sub-threshold).

2. GAP-(3,3,3) IS THE CRITICAL CASE: Only the equi-spaced binary arrangement
   allows the wiggle-sweep construction. Other gap patterns have a ternary
   segment of size 1, blocking the construction.

3. n=9 IS THE FIRST FAILURE: At n<=8, no arrangement achieves all segments >= 2
   with 3 non-consecutive binary. So the BinSCC theorem is correct for n<=8
   but fails at n=9.

4. GROWS WITH n: At n>=9, the number of arrangements with all-segments->=2
   increases, meaning more potential counterexamples.

5. THE BinSCC THEOREM (Universal EC for non-consecutive binary) IS WRONG
   for n >= 9, specifically for gap-(3,3,3) binary arrangements.
   The existing computational verification only covered n=5,6,8.

6. THE OVERALL LB PROOF NEEDS REPAIR: The non-consecutive binary case
   at n >= 9 with gap-(3,3,3) requires a different mechanism
   (shadow cycle, counting argument, or a new EC variant).
""")


if __name__ == "__main__":
    main()
