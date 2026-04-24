#!/usr/bin/env python3
"""binscc_walk_proof.py — Walk-on-cube analytical proof of universal overlap.

For 3 consecutive binary processors P0, P1, P2 on a ring of n ≥ 5:
- P1's context (c_0, c_1, c_2) ∈ {0,1}^3 traces a walk on the 3-cube
- Walk starts and ends at (0,0,0)
- Each binary firing flips one coordinate; ternary firings = stays
- P1 mover contexts: vertices where coord 1 flips
- P1 nonmover contexts: vertices at P0/P2 firings + ternary stays

GOAL: Show that no walk allows P1's mover contexts to be disjoint
from its nonmover contexts, considering ring-adjacency and ternary
distribution constraints.

The walk abstraction:
  Binary firing sequence: b_1, b_2, ..., b_k where b_i ∈ {0,1,2}
  Walk: u_0 → u_1 → ... → u_k, where u_0 = u_k = (0,0,0)
  u_i = u_{i-1} XOR e_{b_i}  (flip coordinate b_i)

  Between firings i and i+1, there are s_i ≥ 0 ternary firings.
  sum(s_i) = ℓ - k  (total ternary firings)

  P1 mover contexts: {u_{i-1} : b_i = 1}
  P1 nonmover from binary: {u_{i-1} : b_i ∈ {0,2}}
  P1 nonmover from ternary: {u_i : s_i > 0}  (vertex AFTER firing i)

  Ring-adjacency constraint on s_i = 0:
    If s_i = 0, firings i and i+1 are consecutive in mover word,
    so b_i and b_{i+1} must be ring-adjacent: (b_i, b_{i+1}) ∈
    {(0,1),(1,0),(1,2),(2,1)}.  P0-P2 are NOT ring-adjacent.

  Overlap at P1: ∃ v ∈ M ∩ (B ∪ T) where
    M = mover set, B = binary-nonmover set, T = ternary-nonmover set
"""

import sys
from itertools import product as cartesian
from collections import defaultdict, Counter


def flip(vertex, coord):
    """Flip coordinate `coord` of vertex on {0,1}^3."""
    v = list(vertex)
    v[coord] = 1 - v[coord]
    return tuple(v)


# Ring-adjacent pairs among {0,1,2}: only P0-P1 and P1-P2
RING_ADJ = {(0,1), (1,0), (1,2), (2,1)}


def enumerate_binary_sequences(max_k=12):
    """Enumerate all valid binary firing sequences.

    Each of coords 0,1,2 must appear an even number of times ≥ 2.
    The walk must return to origin (guaranteed by even parity).

    Returns: list of sequences (tuples of 0,1,2).
    """
    # Generate by DFS: build sequence of firings, track parity
    results = []

    def dfs(seq, parity, counts):
        k = len(seq)
        if k > max_k:
            return
        # Check if we can close: all parities 0 and all counts ≥ 2
        if all(p == 0 for p in parity) and all(c >= 2 for c in counts):
            results.append(tuple(seq))
        # Prune: remaining slots must allow all parities to return to 0
        remaining = max_k - k
        # Each odd-parity coord needs at least 1 more flip
        odd_coords = sum(1 for p in parity if p == 1)
        # Each coord with count < 2 needs at least (2 - count) more flips
        deficit = sum(max(0, 2 - c) for c in counts)
        if remaining < max(odd_coords, deficit):
            return
        # Try extending
        for c in range(3):
            new_parity = list(parity)
            new_parity[c] = 1 - new_parity[c]
            new_counts = list(counts)
            new_counts[c] += 1
            dfs(seq + [c], new_parity, new_counts)

    dfs([], [0,0,0], [0,0,0])
    return results


def analyze_walk(seq):
    """Analyze a binary firing sequence for P1 overlap properties.

    Returns dict with:
      'walk': list of vertices u_0, u_1, ..., u_k
      'mover_set': P1 mover vertices {u_{i-1} : seq[i-1]=1} (0-indexed: seq[i])
      'binary_nonmover': P1 nonmover from binary firings
      'gap_vertices': for each gap i, the vertex u_i that becomes nonmover if s_i > 0
      'ring_adj_gaps': which gaps CAN have s_i = 0 (ring-adjacent pair)
      'must_overlap_binary': M ∩ B (overlap from binary structure alone)
    """
    k = len(seq)
    # Build walk
    walk = [(0,0,0)]
    for i in range(k):
        walk.append(flip(walk[-1], seq[i]))

    # P1 mover contexts: vertex BEFORE P1 fires
    # seq[i] is the i-th firing (0-indexed). Vertex before = walk[i].
    mover_set = set()
    mover_indices = []  # which firing indices are P1 firings
    for i in range(k):
        if seq[i] == 1:
            mover_set.add(walk[i])
            mover_indices.append(i)

    # P1 binary-nonmover: vertex before P0/P2 fires
    binary_nonmover = set()
    for i in range(k):
        if seq[i] in (0, 2):
            binary_nonmover.add(walk[i])

    # Gap vertices: u_i (vertex AFTER firing i) for gap i
    # Gap i is between firing i and firing (i+1) mod k
    gap_vertices = {}  # gap_index -> vertex
    for i in range(k):
        gap_vertices[i] = walk[i+1]  # = walk[(i+1) % (k+1)] but walk[k]=walk[0]

    # Ring-adjacency constraint: gap i connects firing i and firing (i+1)%k
    # If s_i = 0, need (seq[i], seq[(i+1)%k]) ∈ RING_ADJ
    ring_adj_gaps = set()
    for i in range(k):
        pair = (seq[i], seq[(i+1) % k])
        if pair in RING_ADJ:
            ring_adj_gaps.add(i)

    must_overlap_binary = mover_set & binary_nonmover

    return {
        'walk': walk,
        'k': k,
        'seq': seq,
        'mover_set': mover_set,
        'mover_indices': mover_indices,
        'binary_nonmover': binary_nonmover,
        'gap_vertices': gap_vertices,
        'ring_adj_gaps': ring_adj_gaps,
        'must_overlap_binary': must_overlap_binary,
    }


def can_avoid_ternary_overlap(analysis, total_ternary):
    """Check if ternary firings can be distributed to avoid P1 overlap.

    Need: M ∩ T = ∅ where T = {gap_vertices[i] : s_i > 0}.
    Also: sum(s_i) = total_ternary, s_i ≥ 0.
    Constraint: if s_i = 0, gap i must be ring-adjacent.

    So: gaps where s_i MUST be > 0 are those NOT in ring_adj_gaps
    (and we need at least total_ternary ternary firings distributed).

    Forbidden gaps for s > 0: those where gap_vertex is in mover_set.
    So s_i = 0 REQUIRED for these gaps (to avoid M ∩ T overlap).
    But s_i = 0 REQUIRES ring-adjacency.

    If a gap has mover vertex AND is not ring-adjacent: FORCED overlap.
    """
    k = analysis['k']
    mover_set = analysis['mover_set']
    gap_vertices = analysis['gap_vertices']
    ring_adj_gaps = analysis['ring_adj_gaps']

    # Gaps that MUST have s_i = 0 (vertex is a mover vertex)
    must_be_zero = set()
    for i in range(k):
        if gap_vertices[i] in mover_set:
            must_be_zero.add(i)

    # Check: can these gaps have s_i = 0?
    for i in must_be_zero:
        if i not in ring_adj_gaps:
            # This gap must be zero (mover vertex) but can't be zero
            # (not ring-adjacent) → FORCED ternary overlap
            return False, "gap %d: mover vertex %s but not ring-adj (%d→%d)" % (
                i, gap_vertices[i], analysis['seq'][i],
                analysis['seq'][(i+1) % k])

    # Remaining gaps that CAN have s_i > 0
    available_gaps = set(range(k)) - must_be_zero

    # Need sum of s_i over available_gaps ≥ total_ternary
    # (since must_be_zero gaps have s_i = 0, all ternary go to available)
    # This is always satisfiable if len(available_gaps) > 0 and total_ternary > 0
    # Actually need: total_ternary can be distributed among available_gaps
    # with s_i ≥ 0. Also: gaps NOT in ring_adj_gaps that are in available_gaps
    # MUST have s_i > 0 (they can't be 0).

    # Gaps not ring-adjacent and not must_be_zero → MUST have s_i ≥ 1
    forced_positive = set()
    for i in available_gaps:
        if i not in ring_adj_gaps:
            forced_positive.add(i)

    # Minimum ternary needed: at least 1 per forced_positive gap
    min_ternary = len(forced_positive)

    if total_ternary < min_ternary:
        return False, "need %d ternary for forced gaps but only %d available" % (
            min_ternary, total_ternary)

    # If we have enough ternary to cover forced_positive gaps, the rest
    # can go anywhere in available_gaps. So overlap can be avoided.
    return True, "feasible: %d must-zero, %d forced-positive, %d available" % (
        len(must_be_zero), len(forced_positive), len(available_gaps))


def full_overlap_check(analysis, total_ternary):
    """Check if P1 overlap is FORCED (both binary and ternary).

    Returns (is_forced, reason).
    """
    # Step 1: Check binary overlap (M ∩ B)
    if analysis['must_overlap_binary']:
        return True, "binary overlap at %s" % analysis['must_overlap_binary']

    # Step 2: Check ternary overlap
    can_avoid, reason = can_avoid_ternary_overlap(analysis, total_ternary)
    if not can_avoid:
        return True, "ternary overlap: " + reason

    return False, "avoidable: " + reason


if __name__ == "__main__":
    print("=" * 78)
    print("WALK-ON-CUBE ANALYSIS: Can P1 avoid overlap?")
    print("=" * 78)

    # ================================================================
    # Part 1: Enumerate all binary firing sequences up to length 12
    # ================================================================
    print("\nEnumerating binary firing sequences (k ≤ 12)...")
    all_seqs = enumerate_binary_sequences(max_k=12)
    print(f"Total sequences: {len(all_seqs)}")

    # Group by length
    by_length = defaultdict(list)
    for seq in all_seqs:
        by_length[len(seq)].append(seq)

    for k in sorted(by_length):
        print(f"  k={k}: {len(by_length[k])} sequences")

    # ================================================================
    # Part 2: For each sequence, check P1 overlap
    # ================================================================
    # Cycle length ℓ = 3n-2. For n=9: ℓ=25. For n=5: ℓ=13.
    # But actually ℓ varies — exotic words can produce different lengths.
    # Let's check for various ℓ.

    print(f"\n{'=' * 78}")
    print("P1 OVERLAP ANALYSIS (3 consecutive binary)")
    print("=" * 78)

    for n_test in [5, 6, 7, 8, 9]:
        ell = 3 * n_test - 2  # typical good cycle length
        print(f"\n--- n={n_test}, ℓ={ell} ---")

        total_seqs = 0
        binary_overlap = 0
        ternary_forced = 0
        avoidable = 0
        avoidable_examples = []

        for seq in all_seqs:
            k = len(seq)
            total_ternary = ell - k
            if total_ternary < 0:
                continue  # sequence too long for this cycle length

            # Check: do we have enough ternary firings for n-3 ternary procs?
            # Each ternary processor fires at least once (fairness).
            # With n-3 ternary processors, need at least n-3 ternary firings.
            if total_ternary < n_test - 3:
                continue  # not enough ternary for fairness

            total_seqs += 1
            analysis = analyze_walk(seq)
            is_forced, reason = full_overlap_check(analysis, total_ternary)

            if is_forced:
                if "binary" in reason:
                    binary_overlap += 1
                else:
                    ternary_forced += 1
            else:
                avoidable += 1
                if len(avoidable_examples) < 3:
                    avoidable_examples.append((seq, reason))

        print(f"  Sequences tested: {total_seqs}")
        print(f"  Binary overlap (M∩B≠∅): {binary_overlap}")
        print(f"  Ternary forced: {ternary_forced}")
        print(f"  Avoidable: {avoidable}")

        if avoidable_examples:
            for seq, reason in avoidable_examples:
                print(f"    Example: {seq}")
                print(f"      {reason}")

    # ================================================================
    # Part 3: Deeper analysis of avoidable cases
    # ================================================================
    print(f"\n{'=' * 78}")
    print("DEEP ANALYSIS OF AVOIDABLE CASES")
    print("=" * 78)

    # For n=9, ℓ=25: which sequences are avoidable?
    n_test = 9
    ell = 25

    avoidable_seqs = []
    for seq in all_seqs:
        k = len(seq)
        total_ternary = ell - k
        if total_ternary < 0 or total_ternary < n_test - 3:
            continue

        analysis = analyze_walk(seq)
        is_forced, reason = full_overlap_check(analysis, total_ternary)

        if not is_forced:
            avoidable_seqs.append((seq, analysis, reason))

    print(f"\n  n=9, ℓ=25: {len(avoidable_seqs)} avoidable sequences")

    # For avoidable sequences: check P0 and P2 overlap
    # P0's context: (c_{n-1}, c_0, c_1). c_{n-1} is ternary → 3 states.
    # On the binary cube, we only track (c_0, c_1, c_2), so P0's full
    # context includes ternary info. P0 overlap can't be checked purely
    # from the cube walk.
    #
    # BUT: P0's mover context vs nonmover in terms of binary coords only:
    # P0 mover: vertex u_{i-1} where seq[i]=0
    # P0 nonmover: all other vertices
    # If P0 also overlaps on binary coords, it definitely overlaps.
    # If P0 is clean on binary coords, ternary variation might still cause overlap.

    print("\n  Checking P0 + P2 binary-subspace overlap for avoidable cases:")

    all_three_avoidable = 0
    for seq, analysis, reason in avoidable_seqs:
        k = len(seq)
        walk = analysis['walk']

        # P0 mover vertices (where coord 0 flips)
        p0_mover = set()
        for i in range(k):
            if seq[i] == 0:
                p0_mover.add(walk[i])

        # P0 nonmover from binary firings (where coord 1 or 2 flips)
        p0_binary_nm = set()
        for i in range(k):
            if seq[i] in (1, 2):
                p0_binary_nm.add(walk[i])

        p0_binary_overlap = p0_mover & p0_binary_nm

        # P2 mover vertices (where coord 2 flips)
        p2_mover = set()
        for i in range(k):
            if seq[i] == 2:
                p2_mover.add(walk[i])

        p2_binary_nm = set()
        for i in range(k):
            if seq[i] in (0, 1):
                p2_binary_nm.add(walk[i])

        p2_binary_overlap = p2_mover & p2_binary_nm

        if not p0_binary_overlap and not p2_binary_overlap:
            all_three_avoidable += 1

    print(f"  All 3 binary procs avoidable (binary-subspace): {all_three_avoidable}")

    # ================================================================
    # Part 4: Consider ALL possible cycle lengths
    # ================================================================
    print(f"\n{'=' * 78}")
    print("CYCLE LENGTH SENSITIVITY")
    print("=" * 78)

    # The exotic words can produce cycles of various lengths.
    # Check avoidability across a range of cycle lengths.

    for ell_test in range(13, 50):
        avoidable_count = 0
        total_count = 0

        for seq in all_seqs:
            k = len(seq)
            total_ternary = ell_test - k
            if total_ternary < 0 or total_ternary < 1:
                continue

            total_count += 1
            analysis = analyze_walk(seq)
            is_forced, reason = full_overlap_check(analysis, total_ternary)

            if not is_forced:
                avoidable_count += 1

        if total_count > 0:
            print(f"  ℓ={ell_test}: {avoidable_count}/{total_count} avoidable "
                  f"({avoidable_count/total_count*100:.1f}%)")

    # ================================================================
    # Part 5: The key constraint we're missing — ternary ring structure
    # ================================================================
    print(f"\n{'=' * 78}")
    print("TERNARY RING CONSTRAINT")
    print("=" * 78)
    print("""
The walk analysis above only considers P1's overlap on {0,1}^3.
But the mover word must be ring-adjacent, which constrains
ternary firings too.

Key constraint: if gap i has s_i = 0 (no ternary between binary
firings i and i+1), then b_i and b_{i+1} must be ring-adjacent
binary processors. Since P0-P2 are NOT ring-adjacent, we need
b_i ∈ {0,1} and b_{i+1} ∈ {0,2} etc.

But ALSO: the first/last ternary firings in each gap must be
ring-adjacent to the surrounding binary firings. The ternary
processors on the ring form a path P3, P4, ..., P_{n-1} (for
consecutive binary P0,P1,P2 at the start).

If binary firing i is P2 (coord 2) and the next is P0 (coord 0),
then the ternary path must go P3 → P4 → ... → P_{n-1} → P0
to reach P0. This requires at least n-4 ternary firings in the gap
(to traverse the ternary path from P3 to P_{n-1}).
""")

    # The ternary firings in a gap between P2 and P0 must form a path
    # on the ring from P3 to P_{n-1} (at minimum n-4 steps).
    # Similarly, gap from P0 to P2 requires going through P_{n-1} to P3.

    # This means: a gap between non-adjacent binary firings needs
    # at least n-4 ternary firings. With n=9: at least 5 ternary.

    # Let's redo the analysis with this constraint.
    print("TERNARY GAP MINIMUM ANALYSIS:")

    def min_ternary_in_gap(b_prev, b_next, n):
        """Minimum ternary firings needed in gap between binary b_prev and b_next.

        Binary processors are P0, P1, P2 (consecutive on ring).
        Ternary processors are P3, P4, ..., P_{n-1}.

        If b_prev and b_next are ring-adjacent: gap can be 0 ternary.
        Otherwise: need to traverse the ternary path.

        From P0: neighbors are P1 (binary) and P_{n-1} (ternary).
        From P2: neighbors are P1 (binary) and P3 (ternary).

        Gap from P0 firing to P2 firing (s_i > 0):
          Must go P0 → P_{n-1} → P_{n-2} → ... → P3 → P2
          That's n-3 ternary firings minimum.

        Gap from P2 to P0 (s_i > 0):
          Must go P2 → P3 → P4 → ... → P_{n-1} → P0
          Also n-3 ternary firings minimum.

        Gap from P0 to P0 (s_i > 0):
          P0 → P_{n-1} → ... → some ternary → ... → P_{n-1} → P0
          OR P0 → P1 (binary, but P1 would be another binary firing, not ternary)
          Minimum: 2 ternary (P0 → P_{n-1} → P0, but P_{n-1} fires)
          Actually: just 1 if P_{n-1} fires then back to P0. But P_{n-1} → P0
          is ring adjacent, so: P0 → P_{n-1} → P0: 1 ternary firing of P_{n-1}.
          Wait no: in the gap, ALL firings are ternary. So P0 just fired,
          next must be ring-adjacent to P0 = P1 or P_{n-1}. P1 is binary,
          so must be ternary → P_{n-1}. Then from P_{n-1}, next can be P0.
          So gap P0→P0 with ternary: minimum 1 (just P_{n-1}).
          But this means P0 fires twice in a row with only P_{n-1} in between.

        Gap from P2 to P2:
          P2 → P3 → P2: 1 ternary (P3).

        Gap from P1 to P1:
          P1 → P0 or P2 (binary!) → can't. Must go through ternary.
          P1's ring neighbors are P0 (binary) and P2 (binary).
          So P1 can ONLY be followed by P0 or P2 in a ring-adjacent word!
          This means there's no gap "P1 to P1" — between two P1 firings,
          there MUST be a P0 or P2 firing (binary), not just ternary.

        Hmm wait, that's important. For P1 to fire, the previous/next mover
        must be P0 or P2. So in the binary firing sequence, P1 always
        alternates with P0 or P2. The binary firing sequence can have
        ...0,1,0,1... or ...0,1,2,1... or ...2,1,0,1... etc.
        """
        if (b_prev, b_next) in RING_ADJ:
            return 0  # can be consecutive

        # Need ternary path
        if {b_prev, b_next} == {0, 2}:
            # P0 to P2 or P2 to P0: need full ternary traversal
            return n - 3

        if b_prev == b_next:
            if b_prev == 0:
                return 1  # P0 → P_{n-1} → P0
            elif b_prev == 2:
                return 1  # P2 → P3 → P2
            else:  # b_prev == 1
                return -1  # impossible! P1 has no ternary neighbors

        return -1  # shouldn't reach here

    for n_test in [5, 7, 9, 11]:
        ell = 3 * n_test - 2
        print(f"\n  n={n_test}, ℓ={ell}:")

        avoidable = 0
        total = 0
        forced_by_gap = 0

        for seq in all_seqs:
            k = len(seq)
            total_ternary = ell - k
            if total_ternary < 0 or total_ternary < n_test - 3:
                continue

            analysis = analyze_walk(seq)

            # Check binary overlap first
            if analysis['must_overlap_binary']:
                total += 1
                continue

            # Check ternary overlap with gap minimum constraints
            mover_set = analysis['mover_set']
            gap_verts = analysis['gap_vertices']

            # For each gap, compute minimum ternary firings
            gap_min = {}
            feasible = True
            for i in range(k):
                b_prev = seq[i]
                b_next = seq[(i+1) % k]
                gmin = min_ternary_in_gap(b_prev, b_next, n_test)
                if gmin < 0:
                    feasible = False
                    break
                gap_min[i] = gmin

            if not feasible:
                total += 1
                continue

            # Check: total minimum ternary ≤ total_ternary
            total_gap_min = sum(gap_min.values())
            if total_gap_min > total_ternary:
                total += 1
                continue

            # Now check: gaps where vertex is a mover vertex MUST have s_i = 0.
            # But s_i = 0 requires gap_min[i] = 0, i.e., ring-adjacent.
            must_zero_gaps = set()
            for i in range(k):
                if gap_verts[i] in mover_set:
                    must_zero_gaps.add(i)

            overlap_forced = False
            for i in must_zero_gaps:
                if gap_min[i] > 0:
                    overlap_forced = True
                    forced_by_gap += 1
                    break

            if overlap_forced:
                total += 1
                continue

            # Check ternary budget: zero gaps absorb 0, forced gaps absorb minimum
            used = sum(gap_min[i] for i in range(k) if i not in must_zero_gaps)
            if used > total_ternary:
                total += 1
                continue

            avoidable += 1
            total += 1
            if avoidable <= 3:
                print(f"    AVOIDABLE: seq={seq}")
                print(f"      k={k}, ternary={total_ternary}")
                print(f"      mover_set={analysis['mover_set']}")
                print(f"      must_zero_gaps={must_zero_gaps}")
                for i in range(k):
                    v = gap_verts[i]
                    marker = " ← MOVER VERTEX" if v in mover_set else ""
                    adj = "ring-adj" if (seq[i], seq[(i+1)%k]) in RING_ADJ else "NOT adj"
                    print(f"      gap {i}: {seq[i]}→{seq[(i+1)%k]} ({adj}), "
                          f"vertex={v}, min_ternary={gap_min[i]}{marker}")

        print(f"    Total: {total}, Avoidable: {avoidable}, "
              f"Gap-forced: {forced_by_gap}")

    # ================================================================
    # Part 6: What about non-consecutive binary?
    # ================================================================
    print(f"\n{'=' * 78}")
    print("NON-CONSECUTIVE BINARY: Spread ≥3 binary")
    print("=" * 78)
    print("""
For spread binary (e.g., P0, P3, P6 on n=9 ring), each binary
processor has ternary neighbors. The context space is 3×2×3 = 18.

The walk on {0,1}^3 no longer captures the full context because
ternary neighbors' states matter. However, the binary state
component (c_p ∈ {0,1}) is still determined by firing parity.

For spread binary, the ring-adjacency constraint means:
- P_binary can only fire after one of its (ternary) neighbors fires
- Between two binary firings at distant positions, many ternary
  firings are needed to traverse the ring

The overlap argument for spread binary likely needs a different
approach: context space is larger (18 vs 8), but the structural
constraints from ring traversal may still force overlap.
""")

    # ================================================================
    # Part 7: Verify against actual cycles
    # ================================================================
    print(f"\n{'=' * 78}")
    print("VERIFICATION: Check walk analysis against actual cycles")
    print("=" * 78)

    # Load exotic words and test a few on 3-consecutive binary
    import os
    EXOTIC_PATH = os.path.join(
        os.path.dirname(__file__), '..', 'gpt', 'scripts',
        'glb_wrap_unknown_rotation_reps_n9.txt'
    )

    if os.path.exists(EXOTIC_PATH):
        n = 9
        ms = (2, 2, 2, 3, 3, 3, 3, 3, 3)  # 3 consecutive binary

        words = []
        with open(EXOTIC_PATH) as f:
            for line in f:
                s = line.strip()
                if s:
                    words.append(tuple(int(x) for x in s.split()))

        # Add bounce
        bounce = tuple(list(range(n)) + list(range(n-2, 0, -1)))
        words.append(bounce)

        fair_cycles = 0
        walk_overlap = 0
        actual_overlap = 0
        walk_avoidable_but_actual_overlap = 0

        for word in words[:2000]:
            # Build cycle
            config = [0] * n
            cycle = [tuple(config)]
            visited = {tuple(config)}
            full = list(word) * 10
            movers = []
            ok = False
            for step, mover in enumerate(full):
                config = list(cycle[-1])
                config[mover] = (config[mover] + 1) % ms[mover]
                nc = tuple(config)
                movers.append(mover)
                if nc == cycle[0]:
                    ok = True
                    break
                if nc in visited:
                    break
                visited.add(nc)
                cycle.append(nc)

            if not ok:
                continue
            if len(set(movers)) != n:
                continue

            fair_cycles += 1

            # Extract binary firing sequence
            binary_seq = [m for m in movers if m < 3]  # P0, P1, P2

            # Check actual overlap
            mover_triples = defaultdict(set)
            nonmover_triples = defaultdict(set)
            for idx in range(len(cycle)):
                c = cycle[idx]
                mv = movers[idx]
                for p in range(n):
                    triple = (c[(p-1)%n], c[p], c[(p+1)%n])
                    if p == mv:
                        mover_triples[p].add(triple)
                    else:
                        nonmover_triples[p].add(triple)

            has_actual = False
            for p in range(n):
                if mover_triples[p] & nonmover_triples[p]:
                    has_actual = True
                    break

            if has_actual:
                actual_overlap += 1

            # Check walk-based P1 overlap prediction
            # Build walk on {0,1}^3
            walk = [(0,0,0)]
            for m in movers:
                if m < 3:
                    walk.append(flip(walk[-1], m))
                else:
                    walk.append(walk[-1])  # stay

            p1_mover = set()
            p1_nonmover = set()
            for idx in range(len(movers)):
                v = walk[idx]
                if movers[idx] == 1:
                    p1_mover.add(v)
                else:
                    p1_nonmover.add(v)

            if p1_mover & p1_nonmover:
                walk_overlap += 1
                if has_actual:
                    pass  # both agree
            else:
                if has_actual:
                    walk_avoidable_but_actual_overlap += 1

        print(f"  Fair cycles tested: {fair_cycles}")
        print(f"  Actual overlap: {actual_overlap}")
        print(f"  Walk P1 overlap: {walk_overlap}")
        print(f"  Walk avoidable but actual overlap: "
              f"{walk_avoidable_but_actual_overlap}")
        print(f"  (actual overlap at OTHER proc, not P1)")

    print(f"\n{'=' * 78}")
    print("DONE")
    print("=" * 78)
