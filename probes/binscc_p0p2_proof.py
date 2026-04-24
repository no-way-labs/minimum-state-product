#!/usr/bin/env python3
"""binscc_p0p2_proof.py — Analyze WHY P0/P2 have overlap on P1-avoidable walks.

For k=6 P1-avoidable walks, P1 avoids overlap. But P0 or P2 can't.

Key observation for P0:
  P0 context is (c_{n-1}, c_0, c_1).
  Binary-visible part: (c_0, c_1) ∈ {0,1}².
  P0 fires ↔ seq[i]=0 (2 times). (c_0, c_1) → mover set.
  Other binary fires: seq[i]=1 or 2 → nonmover set.
  P2 fires: don't change (c_0, c_1) → same as next step.
  Ternary gaps: (c_0, c_1) fixed → additional nonmover.

The 6-step walk on {0,1}³ projects to (c_0,c_1) space:
  P0 fire → flip c_0
  P1 fire → flip c_1
  P2 fire → no change (only c_2 flips)

So (c_0,c_1) walk has 4 transitions (P0+P1 fires) and 2 stays (P2 fires).
"""

from binscc_exact_parity import enumerate_binary_sequences, flip, RING_ADJ


def main():
    all_seqs = enumerate_binary_sequences(max_k=12)

    # Focus on k=6 P1-avoidable walks
    avoidable_k6 = []
    for seq in all_seqs:
        if len(seq) != 6:
            continue
        k = 6
        walk = [(0,0,0)]
        for i in range(k):
            walk.append(flip(walk[-1], seq[i]))
        ms = set(walk[i] for i in range(k) if seq[i] == 1)
        bn = set(walk[i] for i in range(k) if seq[i] != 1)
        if ms & bn:
            continue
        gv = {i: walk[i+1] for i in range(k)}
        avoidable = True
        for i in range(k):
            if gv[i] in ms and (seq[i], seq[(i+1)%k]) not in RING_ADJ:
                avoidable = False
                break
        if not avoidable:
            continue
        avoidable_k6.append(seq)

    print(f"Total k=6 P1-avoidable walks: {len(avoidable_k6)}")

    # Analyze P0 and P2 (c_0,c_1) and (c_1,c_2) projections
    print("\n--- P0 (c_0,c_1) projection analysis ---\n")

    p0_clean = []
    p0_overlap = []

    for seq in avoidable_k6:
        walk = [(0,0,0)]
        for i in range(6):
            walk.append(flip(walk[-1], seq[i]))

        # P0 mover (c_0,c_1) and nonmover (c_0,c_1)
        p0_mover = set()
        p0_nonmover = set()
        for i in range(6):
            c01 = (walk[i][0], walk[i][1])
            if seq[i] == 0:
                p0_mover.add(c01)
            else:
                p0_nonmover.add(c01)

        overlap = p0_mover & p0_nonmover
        if overlap:
            p0_overlap.append((seq, p0_mover, p0_nonmover, overlap))
        else:
            p0_clean.append((seq, p0_mover, p0_nonmover))

    print(f"P0 binary overlap: {len(p0_overlap)} / {len(avoidable_k6)}")
    print(f"P0 clean: {len(p0_clean)} / {len(avoidable_k6)}")

    # For P0-clean walks, check P2
    print("\n--- P2 (c_1,c_2) projection for P0-clean walks ---\n")

    p2_clean = []
    p2_overlap = []

    for seq, p0m, p0n in p0_clean:
        walk = [(0,0,0)]
        for i in range(6):
            walk.append(flip(walk[-1], seq[i]))

        p2_mover = set()
        p2_nonmover = set()
        for i in range(6):
            c12 = (walk[i][1], walk[i][2])
            if seq[i] == 2:
                p2_mover.add(c12)
            else:
                p2_nonmover.add(c12)

        overlap = p2_mover & p2_nonmover
        if overlap:
            p2_overlap.append((seq, p2_mover, p2_nonmover, overlap))
        else:
            p2_clean.append((seq, p2_mover, p2_nonmover))

    print(f"P2 binary overlap (among P0-clean): {len(p2_overlap)} / {len(p0_clean)}")
    print(f"Both P0-clean AND P2-clean: {len(p2_clean)} / {len(p0_clean)}")

    if p2_clean:
        print("\n*** DANGER: walks clean at both P0 and P2! ***")
        for seq, p2m, p2n in p2_clean[:5]:
            walk = [(0,0,0)]
            for i in range(6):
                walk.append(flip(walk[-1], seq[i]))
            print(f"  seq={seq}")
            print(f"    walk: {[walk[i] for i in range(7)]}")
            # P0 context (c0,c1), P1 context (c0,c1,c2), P2 context (c1,c2)
            for i in range(6):
                c0,c1,c2 = walk[i]
                mover = f"P{seq[i]}"
                gap_v = walk[i+1]
                print(f"    step {i}: ({c0},{c1},{c2}) fire P{seq[i]}, "
                      f"gap entry ({gap_v[0]},{gap_v[1]},{gap_v[2]})")

    # Now check ternary gap overlap
    print("\n--- Ternary gap overlap for P0+P2 clean walks ---\n")

    if p2_clean:
        for seq, p2m, p2n in p2_clean:
            walk = [(0,0,0)]
            for i in range(6):
                walk.append(flip(walk[-1], seq[i]))

            # P0 mover (c0,c1)
            p0_mover = set()
            for i in range(6):
                if seq[i] == 0:
                    p0_mover.add((walk[i][0], walk[i][1]))

            # P2 mover (c1,c2)
            p2_mover = set()
            for i in range(6):
                if seq[i] == 2:
                    p2_mover.add((walk[i][1], walk[i][2]))

            # Check each gap entry point
            p0_gap_overlap = False
            p2_gap_overlap = False

            for i in range(6):
                b_prev = seq[i]
                b_next = seq[(i+1) % 6]
                if (b_prev, b_next) not in RING_ADJ:
                    # This is a required gap — ternary fires here
                    c0, c1, c2 = walk[i+1]
                    if (c0, c1) in p0_mover:
                        p0_gap_overlap = True
                    if (c1, c2) in p2_mover:
                        p2_gap_overlap = True

            print(f"  seq={seq}: P0_gap_overlap={p0_gap_overlap}, "
                  f"P2_gap_overlap={p2_gap_overlap}")

            if not p0_gap_overlap and not p2_gap_overlap:
                print(f"    *** TRULY CLEAN — no overlap at P0, P1, or P2 ***")
                print(f"    P0 mover (c0,c1): {p0_mover}")
                print(f"    P2 mover (c1,c2): {p2_mover}")
                print(f"    Gap entries:")
                for i in range(6):
                    b_prev = seq[i]
                    b_next = seq[(i+1) % 6]
                    if (b_prev, b_next) not in RING_ADJ:
                        c0,c1,c2 = walk[i+1]
                        print(f"      gap at step {i}: ({c0},{c1},{c2}), "
                              f"P0 sees (c0,c1)=({c0},{c1}), "
                              f"P2 sees (c1,c2)=({c1},{c2})")

    # ================================================================
    # Structural analysis: WHY P0 or P2 always overlaps
    # ================================================================
    print(f"\n{'=' * 78}")
    print("STRUCTURAL ANALYSIS: Why P0 or P2 always overlaps")
    print("=" * 78)

    # Count all (c_0,c_1) projections at P0 mover/nonmover steps
    print("\nFor ALL k=6 P1-avoidable walks:")
    print("  P0 has 2 mover (c_0,c_1) + 4 nonmover (c_0,c_1) on {0,1}²")
    print("  P2 has 2 mover (c_1,c_2) + 4 nonmover (c_1,c_2) on {0,1}²")
    print()

    # Count distinct mover/nonmover per walk
    for seq in avoidable_k6[:30]:
        walk = [(0,0,0)]
        for i in range(6):
            walk.append(flip(walk[-1], seq[i]))

        p0m = set(); p0n = set()
        p2m = set(); p2n = set()
        for i in range(6):
            c0,c1,c2 = walk[i]
            if seq[i] == 0:
                p0m.add((c0,c1))
            else:
                p0n.add((c0,c1))
            if seq[i] == 2:
                p2m.add((c1,c2))
            else:
                p2n.add((c1,c2))

        p0_ovlp = 'Y' if p0m & p0n else 'N'
        p2_ovlp = 'Y' if p2m & p2n else 'N'

        # Also check: what are the distinct values?
        all_c01 = [walk[i][:2] for i in range(6)]
        all_c12 = [(walk[i][1], walk[i][2]) for i in range(6)]

        # (c0,c1) walk: changes at P0 and P1 fires
        c01_changes = sum(1 for i in range(6) if seq[i] in [0,1])
        c12_changes = sum(1 for i in range(6) if seq[i] in [1,2])

        print(f"  {seq}: |P0m|={len(p0m)}, |P0n|={len(p0n)}, P0={p0_ovlp} | "
              f"|P2m|={len(p2m)}, |P2n|={len(p2n)}, P2={p2_ovlp} | "
              f"c01_changes={c01_changes}, c12_changes={c12_changes}")

    # Key structural observation
    print(f"\n{'=' * 78}")
    print("KEY OBSERVATION")
    print("=" * 78)
    print("""
For k=6, each of P0, P1, P2 fires exactly 2 times.

P0's (c_0,c_1) projection:
  - Transitions: P0 fires flip c_0 (2 times), P1 fires flip c_1 (2 times)
  - Stays: P2 fires don't change (c_0,c_1) (2 times)
  - So 4 transitions + 2 stays = 6 steps

  The walk on {0,1}² has 4 transitions among 4 possible values.
  Starting at (0,0), after 4 transitions (c_0 flips twice, c_1 twice),
  we return to (0,0). This is a closed walk on {0,1}².

  Possible 4-step closed walks on {0,1}²:
  - Visit 2 vertices: e.g., (0,0)→(1,0)→(0,0)→(1,0)→(0,0) [but this
    requires all 4 transitions to be c_0 flips, which means P0 fires 4 times — contradiction]
  - Visit 3 vertices: e.g., (0,0)→(1,0)→(1,1)→(0,1)→(0,0) [full square]
  - Visit 4 vertices: same as full square

  With exactly 2 c_0 flips and 2 c_1 flips interleaved, the walk visits
  exactly 4 vertices (full square traversal with a specific pattern).

  Wait, not necessarily. The order matters. If c_0 flip and c_1 flip alternate,
  you get: (0,0)→(1,0)→(1,1)→(0,1)→(0,0) — visits 4 vertices.
  If c_0 flips are adjacent: (0,0)→(1,0)→(0,0)→(0,1)→(0,0)... no, that
  means c_0 flips twice then c_1 flips twice. Walk: (0,0)→(1,0)→(0,0)→(0,1)→(0,0).
  Visits 3 vertices: (0,0), (1,0), (0,1).

  But these transitions happen at SPECIFIC positions in the 6-step sequence.
  The P2 fires (stays) happen between transitions.
""")

    # Enumerate ALL possible (c_0,c_1) walk patterns
    print("All distinct P0 (c_0,c_1) walks for P1-avoidable k=6 seqs:")
    seen_patterns = set()
    for seq in avoidable_k6:
        walk = [(0,0,0)]
        for i in range(6):
            walk.append(flip(walk[-1], seq[i]))

        c01_walk = tuple(walk[i][:2] for i in range(7))  # 7 points (0..6, 6=0)
        c01_movers = tuple(i for i in range(6) if seq[i] == 0)  # P0 fire positions

        pattern = (c01_walk, c01_movers)
        if pattern not in seen_patterns:
            seen_patterns.add(pattern)
            p0m = set(c01_walk[i] for i in c01_movers)
            p0n = set(c01_walk[i] for i in range(6) if i not in c01_movers)
            ovlp = p0m & p0n

            print(f"  c01_walk={c01_walk}, P0 fires at {c01_movers}: "
                  f"M={p0m}, N={p0n}, ovlp={ovlp}")

    print(f"\nTotal distinct (c01_walk, P0_positions) patterns: {len(seen_patterns)}")


if __name__ == "__main__":
    main()
