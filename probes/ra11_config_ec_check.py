"""
ra11_config_ec_check.py — Check entry conflict at the CONFIG level
for odd-winding non-uniform cycles with non-consecutive binary.

Key insight: the parity-based EC only works for 3 consecutive binary.
For non-consecutive binary, we need to check ACTUAL configs.

But we don't need configs at all! The real question is:
what structural property of the mover word + odd-winding + non-uniform
forces the cycle to be impossible?

Approach: check what the LEAN proof actually does in the recursion.
The recursion goes through subThreshold_binary_core_false which requires:
  - hno_safe (no safe processor)

This is derived from oddWinding (non-zero winding → no safe processor).

Then subThreshold_binary_core_false dispatches on:
  - both_binary_neighbors_false (pivot processor with 2 binary neighbors)
  - no_firing_both_binary_neighbors_false (no such pivot)

For non-consecutive binary with ≥3 binary and no 3 consecutive:
  - Any binary p has at most 1 binary neighbor (since no 3 consecutive)
  - So the "pivot with both binary neighbors" case might not apply.
  - But any NON-BINARY processor t between two binary procs has both binary neighbors!

Wait — for ≥3 non-consecutive binary:
  Example: n=9, binary at {0, 3, 6}, ternary elsewhere.
  Proc 0: left=8(ternary), right=1(ternary). NOT both binary neighbors.
  But no proc has both binary neighbors since no two binary are consecutive.

  Actually "both binary neighbors" means m(left(t)) = 2 AND m(right(t)) = 2.
  For non-consecutive binary: if t is at position between two binary procs
  that are distance 2 apart (like binary at 0,2), then proc 1 has both binary neighbors.

  For ≥3 non-adjacent binary (gap ≥ 2 between each pair):
  Two binary at distance exactly 2: the proc between them has both binary neighbors.
  But "non-adjacent" means no two consecutive binary, so distance ≥ 2.
  If distance = 2: proc between has both binary neighbors.
  If all distances ≥ 3: no proc has both binary neighbors.

This matters because subThreshold_binary_core_false dispatches differently.

Let me trace the actual proof path more carefully.
"""

import itertools
import random
random.seed(42)

def left(p, n):
    return (p - 1) % n

def right(p, n):
    return (p + 1) % n

def total_displacement(movers, n):
    W = 0
    L = len(movers)
    for i in range(L):
        diff = (movers[(i+1) % L] - movers[i]) % n
        if diff == 0:
            pass
        elif diff <= n // 2:
            W += diff
        else:
            W -= (n - diff)
    return W

def step_directions(movers, n):
    L = len(movers)
    dirs = []
    for i in range(L):
        diff = (movers[(i+1) % L] - movers[i]) % n
        if diff == 0:
            dirs.append(0)
        elif diff <= n // 2:
            dirs.append(1)
        else:
            dirs.append(-1)
    return dirs

def is_odd_winding(movers, n):
    return abs(total_displacement(movers, n)) == n

def fire_count(movers, n):
    fc = [0] * n
    for m in movers:
        fc[m] += 1
    return fc

def has_isolated_firings(movers, p):
    L = len(movers)
    for i in range(L):
        if movers[i] == p and movers[(i+1) % L] == p:
            return False
    return True

# ============================================================
# REAL ANALYSIS: trace what the Lean proof does
# ============================================================

def analyze_proof_path(n, ms):
    """
    Trace the proof path for the non-consecutive isolated case.

    In oddWinding_nonUniform_sub_threshold_false, line 1113-1119:
    The code calls subThreshold_binary_core_false_residual which needs:
    - gc, hn (n ≥ 9), hsub, h3bin, hconv, hno_safe

    subThreshold_binary_core_false_residual calls binary_ring_impossibility_residual_callbacks
    which produces 4 callbacks, then calls subThreshold_binary_core_false.

    subThreshold_binary_core_false dispatches on:
    - ∃ t with m(left(t))=2, m(right(t))=2, fc(t)>0  (pivot)
    - vs no such t

    For odd-winding + non-consecutive binary:
    - Every proc fires ≥ 1 (from odd winding)
    - For the pivot: need t with both binary neighbors AND fc(t) > 0
    - Since every proc fires > 0, just need ∃ t with both binary neighbors

    When does t with both binary neighbors exist in non-consecutive binary?
    - Binary at positions b1, b2, ..., bk (k ≥ 3), no 3 consecutive
    - t has both binary neighbors iff left(t) and right(t) are both binary
    - This means t is between two binary procs at distance 2
    - Example: binary at 0 and 2 → proc 1 has both binary neighbors

    So the question is: with ≥3 non-adjacent binary, does there always exist
    a pair of binary procs at distance exactly 2?
    """
    binary = [p for p in range(n) if ms[p] == 2]
    print(f"n={n}, ms={ms}")
    print(f"Binary procs: {binary}")

    # Check for distance-2 pairs
    has_dist2_pair = False
    for b in binary:
        if right(b, n) not in binary and right(right(b, n), n) in binary:
            pivot = right(b, n)
            print(f"  Distance-2 pair: {b}, {right(right(b,n),n)} with pivot {pivot}")
            has_dist2_pair = True

    if not has_dist2_pair:
        print("  NO distance-2 pair! All binary procs are at distance ≥ 3.")
        print("  This means no processor has both binary neighbors.")
        print("  The proof would go through no_firing_both_binary_neighbors_false.")

    return has_dist2_pair


def check_all_nonconsec_configs():
    """Check all possible non-consecutive binary configurations for n=9."""
    n = 9

    # ≥3 binary, no 3 consecutive, product < 4*3^7 = 8748
    # Binary contributes factor 2, ternary 3, etc.
    # With k binary: product = 2^k * prod(remaining)
    # Sub-threshold: product < 4*3^(n-2) = 4*3^7 = 8748

    # With ≥3 binary: product = 2^k * prod(others)
    # If all others are ternary: product = 2^k * 3^(9-k)
    # For k=3: 8 * 3^6 = 8 * 729 = 5832 < 8748 ✓
    # For k=4: 16 * 3^5 = 16 * 243 = 3888 < 8748 ✓
    # etc.

    print("\n=== Non-consecutive binary configurations at n=9 ===")
    print(f"Threshold: 4*3^7 = {4*3**7}")

    # Generate all subsets of [0..8] with ≥3 elements, no 3 consecutive (mod 9)
    from itertools import combinations

    for k in range(3, 10):
        for binary_set in combinations(range(n), k):
            # Check no 3 consecutive (circular)
            has_3consec = False
            for i in range(n):
                if i in binary_set and (i+1)%n in binary_set and (i+2)%n in binary_set:
                    has_3consec = True
                    break
            if has_3consec:
                continue

            # Build ms: binary=2, rest=3 (minimum ternary)
            ms = [2 if p in binary_set else 3 for p in range(n)]
            prod = 1
            for m in ms:
                prod *= m
            if prod >= 4 * 3**(n-2):
                continue

            # Check for distance-2 pairs
            has_dist2 = False
            for b in binary_set:
                r2 = (b + 2) % n
                if r2 in binary_set:
                    has_dist2 = True
                    break

            if not has_dist2:
                print(f"  binary={binary_set}, prod={prod}, NO dist-2 pair!")


def check_existence_of_dist2_pair():
    """
    Prove/disprove: with ≥3 binary, no 3 consecutive, on ring of size n ≥ 9,
    there ALWAYS exists a pair of binary at distance exactly 2.

    Counterexample search: find a set of ≥3 positions on Z/nZ
    with no 3 consecutive and no pair at distance exactly 2.

    Distance exactly 2 means: {b, b+2} both in set.
    No pair at distance 2 means: min gap between consecutive binary ≥ 3.

    With k binary on ring of size n, gaps sum to n.
    No 3 consecutive means min gap ≥ 1 (actually ≥ 0, but "no 3 consec" means
    we can't have gap 0 twice in a row).

    Actually "no pair at distance 2" means no gap of exactly 1
    (gap = distance between consecutive binary in the ring).
    Wait: gap between consecutive binary procs.

    If binary at b1 < b2 < ... < bk (on ring):
    gaps are b2-b1, b3-b2, ..., n-bk+b1.
    "Distance 2 pair" = some gap = 2 (since distance from bi to bi+gap means
    gap=2 iff bi+2 is also binary, i.e., the gap is 2).

    Wait no. Gap of 1 means consecutive binary (e.g., 3,4).
    Gap of 2 means distance 2 (e.g., 3,5), with proc 4 between them having both binary neighbors.

    "No 3 consecutive" means: no two gaps of 1 in a row.
    But we can have individual gaps of 1.

    "No pair at distance 2" means: no gap of exactly 2.

    So we want: k ≥ 3 binary on ring of size n, all gaps ≠ 2.
    Also no 3 consecutive: no two adjacent gaps both = 1.

    With all gaps ∈ {1} ∪ {3,4,5,...}:
    And no two adjacent 1-gaps.

    Minimum sum with k gaps, all ≠ 2, no two adjacent 1s:
    If all gaps ≥ 3: sum ≥ 3k. For n=9, k=3: sum=9 ✓ (all gaps = 3).
    So gaps = [3,3,3] works! Binary at {0,3,6}. No 3 consec, no dist-2 pair.
    """
    print("\n=== Distance-2 pair existence ===")
    print()
    print("COUNTEREXAMPLE: n=9, binary at {0,3,6}")
    print("Gaps: [3,3,3]. No 3 consecutive. No pair at distance 2.")
    print()

    n = 9
    binary_set = {0, 3, 6}
    ms = [2 if p in binary_set else 3 for p in range(n)]
    prod = 1
    for m in ms:
        prod *= m
    print(f"ms = {ms}")
    print(f"product = {prod}")
    print(f"sub-threshold? {prod} < {4*3**7} = {prod < 4*3**7}")
    print()

    # So the pivot case (both binary neighbors) doesn't apply.
    # The proof goes through no_firing_both_binary_neighbors_false.
    # Let's check what that theorem does.

    print("With binary at {0,3,6}:")
    for p in range(n):
        lp = (p-1) % n
        rp = (p+1) % n
        bL = ms[lp] == 2
        bR = ms[rp] == 2
        if bL and bR:
            print(f"  Proc {p}: both binary neighbors ✓")
        elif bL:
            print(f"  Proc {p}: only left binary")
        elif bR:
            print(f"  Proc {p}: only right binary")

    print()
    print("NO processor has both binary neighbors!")
    print("So the proof MUST go through no_firing_both_binary_neighbors_false.")


def trace_no_firing_path():
    """
    Trace no_firing_both_binary_neighbors_false to understand what it does.

    From PhaseExtraction.lean, this theorem dispatches through:
    - binary_ring_impossibility again? Or directly?

    The key question: in the recursion path, when the global dispatch
    receives the oddWinding_nonUniform callback, what does it actually DO?

    Answer: the callbacks are provided by binary_ring_impossibility_residual_callbacks
    which calls oddWinding_nonUniform_false (CaseObstructionsCore.lean line 38).
    That's the sorry stub!

    So the recursion is:
    1. CaseObstructions: oddWinding_nonUniform_sub_threshold_false (non-consec isolated)
    2. → PhaseExtraction: subThreshold_binary_core_false_residual
    3. → PhaseExtraction: binary_ring_impossibility_residual_callbacks
    4.   → CaseObstructionsCore: oddWinding_nonUniform_false (SORRY)
    5.   → This should resolve to CaseObstructions: oddWinding_nonUniform_sub_threshold_false

    So the recursion is:
    oddWinding_nonUniform_sub_threshold_false → ... → oddWinding_nonUniform_false → sorry

    And oddWinding_nonUniform_false should be proved BY
    oddWinding_nonUniform_sub_threshold_false (which is in CaseObstructions).

    The sorry in CaseObstructionsCore.lean is the cycle-breaking point.
    The 4 sorry stubs in CaseObstructionsCore are meant to be filled in by
    the corresponding theorems in CaseObstructions, but since CaseObstructions
    imports PhaseExtraction which imports CaseObstructionsCore, you can't do that
    directly (import cycle).

    So the REAL problem is an import cycle, not a missing proof!

    The proof for oddWinding_nonUniform already EXISTS in CaseObstructions
    (oddWinding_nonUniform_sub_threshold_false), but it can't be plugged in
    because of the circular dependency.

    EXCEPT: the non-consecutive isolated branch of
    oddWinding_nonUniform_sub_threshold_false itself calls through the cycle.
    So the proof is genuinely recursive, not just an import issue.

    The question is: can we break the recursion by giving a DIRECT proof
    for the non-consecutive isolated branch that doesn't need the global dispatch?
    """
    print("\n=== Tracing the recursion path ===")
    print()
    print("Recursion chain:")
    print("  CaseObstructions::oddWinding_nonUniform_sub_threshold_false")
    print("    → non-consec isolated case")
    print("    → PhaseExtraction::subThreshold_binary_core_false_residual")
    print("    → PhaseExtraction::binary_ring_impossibility_residual_callbacks")
    print("    → CaseObstructionsCore::oddWinding_nonUniform_false (SORRY)")
    print("    → should be CaseObstructions::oddWinding_nonUniform_sub_threshold_false")
    print("    → RECURSION!")
    print()
    print("The recursion is REAL: the isolated-firings branch for non-consecutive")
    print("binary dispatches through the global proof which eventually needs to")
    print("handle the oddWinding_nonUniform case again.")
    print()
    print("To break it: prove isolated-firings + non-consec + oddWinding + nonUniform → False")
    print("WITHOUT going through the global dispatch.")
    print()
    print("What does the global dispatch actually do with the oddWinding_nonUniform callback?")
    print("In subThreshold_binary_core_false (PhaseExtraction.lean):")
    print("  It tries to find a pivot t with both binary neighbors and fc(t) > 0.")
    print("  For the no-pivot case: no_firing_both_binary_neighbors_false.")
    print()
    print("Let me check what no_firing_both_binary_neighbors_false does...")


def analyze_no_firing_both():
    """
    Analyze no_firing_both_binary_neighbors_false.

    This theorem handles the case where NO processor has both binary neighbors
    (or no such proc fires). Given ≥3 non-consecutive binary and every proc
    fires ≥ 1 (from odd-winding), the "no proc fires" sub-case is impossible.

    So we're left with: no proc has both binary neighbors.

    What does no_firing_both_binary_neighbors_false do?
    Need to read the code.
    """
    print("\n=== Analysis: no_firing_both_binary_neighbors_false ===")
    print()
    print("Need to check the implementation in PhaseExtraction.lean")


def check_oddwinding_permanent_sufficiency():
    """
    NEW APPROACH: For odd-winding non-uniform with ≥3 non-consecutive binary:

    Every binary proc p fires ≥ 2 times (from odd winding + binary even constraint).
    Trichotomy: EC ∨ permanent ∨ isolated.
    Permanent → W=0, contradiction with |W|=n.

    So for EVERY binary proc: EC ∨ isolated.

    If ANY binary proc gives EC: done.
    Otherwise: ALL binary procs have isolated firings.

    Now: with ALL binary procs having isolated firings + odd winding + non-uniform:
    Is this DIRECTLY contradictory?

    Key: the mover word has |W| = n, both directions present.
    Total steps L = sum(fc). Each binary fires ≥ 2, each ternary fires ≥ 3.
    With ≥3 binary and ≥(n-3) ternary at n=9: L ≥ 3*2 + 6*3 = 24.

    All binary isolated means: no two consecutive binary fires.
    This constrains the mover word structure significantly.
    """
    print("\n=== New approach: all binary isolated ===")
    print()
    print("If ALL binary procs have isolated firings (no EC from any):")
    print("  - Every binary p: fc(p) ≥ 2, no consecutive p-fires")
    print("  - Every ternary q: fc(q) ≥ 3 (from odd winding + ternary constraint)")
    print("  - |W| = n, non-uniform direction")
    print()
    print("Can this configuration exist?")
    print()

    # Generate random mover words at n=9 with these constraints
    n = 9
    ms = [2, 3, 2, 3, 2, 3, 2, 3, 3]  # 4 binary, 5 ternary, non-consec at 0,2,4,6
    # Wait, 0,2,4,6 — check 3 consecutive:
    # No: 0,2 have gap 2; 2,4 have gap 2; 4,6 have gap 2.
    # No 3 consecutive. But is this ≥3 non-adjacent binary? Yes: 4 binary, no 3 consec.

    # Actually let me use a cleaner example: binary at {0, 3, 6}
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    binary = [p for p in range(n) if ms[p] == 2]
    ternary = [p for p in range(n) if ms[p] == 3]
    print(f"n={n}, ms={ms}")
    print(f"Binary: {binary}, Ternary: {ternary}")
    print(f"Product: {eval('*'.join(str(m) for m in ms))}")
    print(f"Threshold: {4*3**7}")
    print()

    # Minimum fc: binary ≥ 2, ternary ≥ 3
    min_fc = [2 if ms[p] == 2 else 3 for p in range(n)]
    min_L = sum(min_fc)
    print(f"Min fire counts: {min_fc}, min L = {min_L}")

    # Generate random valid mover words
    found = 0
    all_isolated = 0
    checked = 0

    for trial in range(100000):
        # Create mover word from min_fc
        word_template = []
        for p in range(n):
            word_template.extend([p] * min_fc[p])

        word = list(word_template)
        random.shuffle(word)

        W = total_displacement(word, n)
        if abs(W) != n:
            continue

        dirs = step_directions(word, n)
        non_stay = [d for d in dirs if d != 0]
        if not non_stay or all(d == non_stay[0] for d in non_stay):
            continue

        checked += 1

        # Check if all binary procs have isolated firings
        all_iso = True
        for p in binary:
            if not has_isolated_firings(word, p):
                all_iso = False
                break

        if all_iso:
            all_isolated += 1

        found += 1
        if found >= 1000:
            break

    print(f"Checked {checked} odd-winding non-uniform words")
    print(f"All binary isolated: {all_isolated}/{checked}")
    print()

    if all_isolated > 0:
        print("YES, such words exist at the mover-word level.")
        print("The contradiction must come from the CONFIG level (system constraints).")
    else:
        print("NO such words found! The mover-word level alone may force EC.")


def check_no_firing_both_lean():
    """Check what no_firing_both_binary_neighbors_false actually does in Lean."""
    print("\n=== Checking no_firing_both_binary_neighbors_false in Lean ===")
    print()
    print("This is the key: when no processor has both binary neighbors,")
    print("what mechanism produces the contradiction?")
    print()
    print("From PhaseExtraction.lean, this theorem receives callbacks for:")
    print("  - zeroWinding consecutive → False")
    print("  - zeroWinding nonConsecutive → False")
    print("  - sweep → False")
    print("  - oddWinding nonUniform → False")
    print()
    print("And dispatches through the global structure.")
    print("The oddWinding_nonUniform callback IS the sorry.")
    print()
    print("So the question becomes: does the path through")
    print("no_firing_both_binary_neighbors_false EVER actually")
    print("invoke the oddWinding_nonUniform callback?")
    print()
    print("If it DOESN'T (because the non-consec + no-pivot case")
    print("is resolved before reaching that callback), then the")
    print("sorry doesn't matter and we can use 'sorry' for that callback.")
    print()
    print("If it DOES, then we truly have a recursive dependency.")


def main():
    print("=" * 70)
    print("Part 1: Check distance-2 binary pairs")
    print("=" * 70)

    n = 9
    for binary_set in [[0,2,4], [0,3,6], [0,2,5], [0,2,7], [0,4,8]]:
        ms = [2 if p in binary_set else 3 for p in range(n)]
        analyze_proof_path(n, ms)
        print()

    check_existence_of_dist2_pair()

    print("\n" + "=" * 70)
    print("Part 2: Check all non-consecutive configurations at n=9")
    print("=" * 70)
    check_all_nonconsec_configs()

    print("\n" + "=" * 70)
    print("Part 3: Trace recursion")
    print("=" * 70)
    trace_no_firing_path()
    analyze_no_firing_both()

    print("\n" + "=" * 70)
    print("Part 4: Check odd-winding permanent sufficiency")
    print("=" * 70)
    check_oddwinding_permanent_sufficiency()
    check_no_firing_both_lean()


if __name__ == "__main__":
    main()
