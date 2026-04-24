#!/usr/bin/env python3
"""
For ≥3 binary, no 3 consecutive, n ≥ 9, sub-threshold:
what gap patterns (between consecutive binary procs) are possible?

A "gap" = number of ternary procs between consecutive binary procs.
With no 3 consecutive: each gap ≥ 1 (if two binary are adjacent, gap=0
means 3rd would be consecutive with the pair's neighbors).

Wait, "gap" between binary clusters. With no 3 consecutive:
- Binary procs form clusters of 1 or 2 consecutive.
- Between clusters: ≥ 1 ternary.

For sandwiched ternary (gap=1): need a ternary between two binary clusters.

With ≥3 binary and no 3 consecutive on ring of n ≥ 9:
- If some gap = 1: sandwiched ternary exists.
- If all gaps ≥ 2: no sandwiched ternary.

Under sub-threshold: product = ∏ m_j < 4·3^(n-2). With k binary (m=2)
and n-k ternary (m=3): product = 2^k · 3^(n-k). Sub-threshold:
2^k · 3^(n-k) < 4 · 3^(n-2) ↔ 2^k < 4 · 3^(k-2) ↔ (2/3)^k < 4/9.

For k ≥ 3: (2/3)^3 = 8/27 ≈ 0.296 < 4/9 ≈ 0.444. ✓
So ANY number of binary ≥ 3 is sub-threshold (with rest ternary).

But if some procs have m > 3: product is larger. With m=4 at one proc:
2^k · 4 · 3^(n-k-1) < 4·3^(n-2). → 2^k · 4/3 < 4·3^(k-2).
→ 2^k/3 < 3^(k-2). → 2^k < 3^(k-1).
For k=3: 8 < 9 ✓. For k=4: 16 < 27 ✓.

So sub-threshold allows m ≥ 4 procs. But for the gap analysis:
the key is binary vs non-binary placement, not specific moduli.

QUESTION: with ≥3 binary, no 3 consecutive, n ≥ 9: is there ALWAYS
a gap-1 pattern (sandwiched ternary)?
"""

def check_gap_patterns(n, min_binary=3):
    """Check all binary placements with ≥ min_binary, no 3 consecutive."""
    has_gap1 = 0
    no_gap1 = 0
    examples_no_gap1 = []

    for bits in range(1 << n):
        positions = [i for i in range(n) if bits & (1 << i)]
        if len(positions) < min_binary:
            continue
        # Check no 3 consecutive
        has_3c = False
        for p in positions:
            if (p + 1) % n in positions and (p + 2) % n in positions:
                has_3c = True
                break
        if has_3c:
            continue

        # Check for gap-1 (sandwiched ternary)
        has_sandwiched = False
        for p in positions:
            rp = (p + 1) % n
            rrp = (p + 2) % n
            if rp not in positions and rrp in positions:
                has_sandwiched = True
                break
        if has_sandwiched:
            has_gap1 += 1
        else:
            no_gap1 += 1
            if len(examples_no_gap1) < 5:
                examples_no_gap1.append(positions)

    return has_gap1, no_gap1, examples_no_gap1


def main():
    for n in [5, 7, 9, 11, 13]:
        g1, ng1, examples = check_gap_patterns(n)
        print(f"n={n}: {g1} with gap-1, {ng1} without gap-1")
        if ng1 > 0:
            for ex in examples:
                gaps = []
                sorted_ex = sorted(ex)
                for idx in range(len(sorted_ex)):
                    nxt = sorted_ex[(idx + 1) % len(sorted_ex)]
                    gap = (nxt - sorted_ex[idx] - 1) % n
                    gaps.append(gap)
                print(f"  No gap-1 example: binary={sorted_ex}, gaps={gaps}")

if __name__ == "__main__":
    main()
