"""
Sanity check for Branch B sub-claim B3.

Scenario: under NoExactProvider + monotone gap runs, a walker with
1 reversal at b + 1 reversal at c of gap G has 3 G-traversals.
Each mid is fired 3 times. So all mids of G must be ternary
(m=3) for fc[mid] = 3 to be consistent (fc for binary must be
multiple of 2).

This rules out the 3-G-traversal scenario in any gap with a
binary mid. So the stretched-self-return case only arises when
gap G is all-ternary interior.

Verify: for the all-odd-gap n=9 family ms=(2,3,3,2,3,3,2,3,3),
each gap between consecutive binaries has 2 ternary mids. So
the scenario CAN arise here. Good.

Also: bound the reversalCount from below using ZW.

Inside 3-G-traversals section: net displacement = +M cw
(where M = gap-width = 1 + |mids|).
Outside section must provide -M (net M ccw) for ZW.
Outside has ≥ 1 pair of reversals (cw→ccw→cw) to balance.
Total reversals ≥ 2 (inside) + 2 (outside) = 4.
"""

def check_mid_modulus(ms, binary_set):
    """For each gap between consecutive binaries, report the mid moduli."""
    n = len(ms)
    binaries = sorted(binary_set)
    gaps = []
    for i in range(len(binaries)):
        b = binaries[i]
        c = binaries[(i+1) % len(binaries)]
        # Mids strictly between b and c in cyclic order
        j = (b + 1) % n
        mids = []
        while j != c:
            mids.append((j, ms[j]))
            j = (j + 1) % n
        gaps.append((b, c, mids))
    return gaps


def analyze(ms_name, ms):
    binary_set = {i for i, m in enumerate(ms) if m == 2}
    print(f"\n{ms_name}: ms={ms}")
    print(f"  binaries at positions: {sorted(binary_set)}")
    gaps = check_mid_modulus(ms, binary_set)
    for b, c, mids in gaps:
        all_ternary = all(m == 3 for _, m in mids)
        moduli = [m for _, m in mids]
        print(f"  gap ({b} -> {c}): mids mod = {moduli}, all ternary = {all_ternary}")


if __name__ == "__main__":
    # Representative n=9 sub-threshold families
    analyze("all-odd-gap n=9 (3 binaries)", [2,3,3,2,3,3,2,3,3])
    analyze("pivot n=9", [2,3,3,3,2,3,3,3,2])
    analyze("spaced n=9", [2,2,3,2,3,3,3,3,3])
    analyze("3cb n=9", [2,2,2,3,3,3,3,3,3])
    # n=5 with mixed
    analyze("n=5 mixed", [2,2,2,3,3])
    # Entirely-ternary-mid gaps occur in...
    analyze("n=11 all-odd-4-binary", [2,3,3,2,3,3,2,3,3,2,3])
