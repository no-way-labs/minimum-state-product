#!/usr/bin/env python3
"""binscc_binary_overlap_fast.py — Fast check: does EVERY P1-avoidable walk
have overlap at P0, P1, or P2 from binary walk structure alone?

No mod-3 check needed — just binary walk on {0,1}^3.
If overlap is forced at the binary level, it holds for ALL cycle lengths.
"""

from binscc_exact_parity import enumerate_binary_sequences, flip, RING_ADJ, gap_info


def check_all_processor_overlap(seq, check_gap=True, n_t=2):
    """Check if some binary processor has overlap from the walk alone.

    Returns (has_overlap, details).
    If check_gap: also check ternary gap entry points.
    """
    k = len(seq)
    walk = [(0,0,0)]
    for i in range(k):
        walk.append(flip(walk[-1], seq[i]))

    for proc in [0, 1, 2]:
        # Extract the relevant 2D (or 3D for P1) projection
        mover = set()
        nonmover = set()

        for i in range(k):
            if proc == 0:
                ctx = (walk[i][0], walk[i][1])
            elif proc == 1:
                ctx = walk[i]  # full 3D
            else:
                ctx = (walk[i][1], walk[i][2])

            if seq[i] == proc:
                mover.add(ctx)
            else:
                nonmover.add(ctx)

        if mover & nonmover:
            return True, f"P{proc} binary overlap"

        if check_gap:
            for i in range(k):
                gi = gap_info(seq[i], seq[(i+1)%k], n_t)
                if gi is not None and gi != 'impossible':
                    c0, c1, c2 = walk[i+1]
                    if proc == 0:
                        gap_ctx = (c0, c1)
                    elif proc == 1:
                        gap_ctx = (c0, c1, c2)
                    else:
                        gap_ctx = (c1, c2)
                    if gap_ctx in mover:
                        return True, f"P{proc} gap overlap at step {i}"

    return False, "clean"


def main():
    print("=" * 70)
    print("FAST BINARY OVERLAP CHECK — ALL k values up to 12")
    print("=" * 70)

    all_seqs = enumerate_binary_sequences(max_k=12)
    print(f"Total binary sequences: {len(all_seqs)}")

    # Part 1: Binary overlap only (no gap check) — n-independent
    print("\n--- Part 1: Pure binary overlap (no gap check) ---")

    by_k = {}
    for seq in all_seqs:
        k = len(seq)
        if k not in by_k:
            by_k[k] = []
        by_k[k].append(seq)

    for k in sorted(by_k.keys()):
        total = len(by_k[k])
        p1_avoidable = 0
        any_overlap = 0
        clean = []

        for seq in by_k[k]:
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

            p1_avoidable += 1
            has_ovlp, _ = check_all_processor_overlap(seq, check_gap=False)
            if has_ovlp:
                any_overlap += 1
            else:
                clean.append(seq)

        if p1_avoidable > 0:
            print(f"  k={k:2d}: {p1_avoidable:5d} P1-avoidable, "
                  f"{any_overlap:5d} have P0/P2 overlap, "
                  f"{len(clean):3d} clean (binary only)")

    # Part 2: With gap check — depends on n_t
    print("\n--- Part 2: With ternary gap overlap (n_t dependent) ---")

    for n_t in [2, 4, 6, 8]:
        n = n_t + 3
        print(f"\n  n={n} (n_t={n_t}):")

        total_clean = 0

        for k in sorted(by_k.keys()):
            p1_avoidable = 0
            clean = []

            for seq in by_k[k]:
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

                # Check gap structure validity
                has_impossible = False
                for i in range(k):
                    gi = gap_info(seq[i], seq[(i+1)%k], n_t)
                    if gi == 'impossible':
                        has_impossible = True
                        break
                if has_impossible:
                    continue

                p1_avoidable += 1
                has_ovlp, detail = check_all_processor_overlap(seq, check_gap=True, n_t=n_t)
                if not has_ovlp:
                    clean.append(seq)

            if p1_avoidable > 0 and len(clean) > 0:
                print(f"    k={k:2d}: {p1_avoidable:5d} avoidable, {len(clean):3d} clean")
                total_clean += len(clean)

        if total_clean == 0:
            print(f"    *** ALL OVERLAP — no clean walks at any k ***")
        else:
            print(f"    *** {total_clean} CLEAN WALKS FOUND ***")
            # Show them
            for k in sorted(by_k.keys()):
                for seq in by_k[k]:
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
                    has_impossible = False
                    for i in range(k):
                        gi = gap_info(seq[i], seq[(i+1)%k], n_t)
                        if gi == 'impossible':
                            has_impossible = True
                            break
                    if has_impossible:
                        continue
                    has_ovlp, _ = check_all_processor_overlap(seq, check_gap=True, n_t=n_t)
                    if not has_ovlp:
                        print(f"      CLEAN: seq={seq}")

    # Part 3: The critical insight
    print(f"\n{'=' * 70}")
    print("CRITICAL INSIGHT")
    print("=" * 70)
    print("""
The binary walk overlap check is INDEPENDENT of cycle length ℓ.
It depends only on:
  (a) the binary firing sequence (which processor fires in what order)
  (b) gap structure (which gaps have ternary, depends on n_t)

If overlap is forced at the binary walk level for ALL P1-avoidable
sequences at a given n_t, then it holds for ALL cycle lengths.

This eliminates the need to check individual cycle lengths!
""")


if __name__ == "__main__":
    main()
