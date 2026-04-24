#!/usr/bin/env python3
"""
RA6: Gap analysis — which binary arrangements allow CF cycles?

The CF counterexample exists for gap-3 binary (positions {0,3,6})
but NOT for gap-2 (alternating, positions {0,2,4}).

Systematically check:
1. All possible 3-binary placements on n=9 ring
2. For each, use the wiggle-sweep construction
3. Check EC

Also: can we construct CF cycles for gap-1 (consecutive) binary?
And: what about arrangements with >3 binary?
"""
from itertools import combinations, product as iproduct
from collections import defaultdict
import time


def build_wiggle_sweep_word(n, ms, binary_positions):
    """Construct the wiggle-sweep word that worked for gap-3.
    Pattern: for each pair of consecutive ternary procs, add a bounce.
    Then do a clean backward sweep.

    The word structure:
    - Phase 1: sweep backward with bounces at each ternary pair
    - Phase 2: clean backward sweep

    For gap-3 binary at {0,3,6}:
    Ternary pairs: (8,7), (5,4), (2,1)
    Phase 1: 8,7,8,7, 6, 5,4,5,4, 3, 2,1,2,1, 0
    Phase 2: 8,7,6,5,4,3,2,1,0
    """
    bp = sorted(binary_positions)

    # Build ternary segments between binary procs
    # On the ring, segments go: bp[0]+1..bp[1]-1, bp[1]+1..bp[2]-1, bp[2]+1..bp[0]-1 (mod n)
    segments = []
    for i in range(len(bp)):
        start = (bp[i] + 1) % n
        end = bp[(i+1) % len(bp)]
        seg = []
        p = start
        while p != end:
            seg.append(p)
            p = (p + 1) % n
        segments.append(seg)

    # For the wiggle-sweep to work, we need each segment to have >= 2 ternary procs
    # (so we can bounce within the segment)

    # Phase 1: sweep backward with bounces
    # Start from the proc just before bp[0] (which is bp[-1]+segment[-1])
    # and sweep backward, bouncing in each ternary segment

    # Actually, let me just try the specific construction that worked:
    # For each ternary segment of length k going backward:
    #   if k >= 2: bounce the first two (a,b) -> a,b,a,b then continue
    #   if k == 1: just visit once
    # Then visit the binary proc

    # Let's be more general. Sweep backward from the last ternary before bp[0].
    # Go: ..., bp[0]-1, bp[0]-2, ..., visit ternary segment, then binary, repeat.

    word = []
    # Start position: the ternary proc just before bp[0] going backward
    # i.e., (bp[0] - 1) % n

    # We'll sweep backward through the ring
    pos = (bp[0] - 1) % n  # This should be a ternary proc

    # For each segment (going backward from bp[0]):
    # The backward order visits: segment[-1][-1], ..., segment[-1][0], bp[-1],
    #                           segment[-2][-1], ..., segment[-2][0], bp[-2], ...

    # Let me just hardcode the pattern for gap-3 and test generalization
    for i in range(len(bp)):
        # Ternary segment before bp[i] (going backward)
        seg_idx = (i - 1) % len(bp)  # segment ending at bp[i]
        # Actually segments[seg_idx] goes FORWARD from bp[seg_idx]+1 to bp[i]-1
        seg = segments[i - 1 if i > 0 else len(bp) - 1]

        # Backward through segment: visit in reverse order
        seg_rev = list(reversed(seg))

        if len(seg_rev) >= 2:
            # Bounce the first pair
            a, b = seg_rev[0], seg_rev[1]
            word.extend([a, b, a, b])
            # Then the rest
            for p in seg_rev[2:]:
                word.append(p)
        elif len(seg_rev) == 1:
            word.append(seg_rev[0])
        # Then visit the binary proc
        word.append(bp[(i - 1) % len(bp)] if i > 0 else bp[-1])

    # Wait, this is getting complicated. Let me just construct it directly
    # based on the pattern that worked.

    # The pattern for gap-3 at {0,3,6}:
    # Ternary between 6 and 0: {7,8}  (backward: 8,7)
    # Ternary between 0 and 3: {1,2}  (backward: 2,1)
    # Ternary between 3 and 6: {4,5}  (backward: 5,4)
    # Phase 1: bounce(8,7), cross 6, bounce(5,4), cross 3, bounce(2,1), cross 0
    # Phase 2: sweep 8,7,6,5,4,3,2,1,0

    return None  # Need to think about this differently


def check_ec(word, ms, n):
    """Check EC with incrementing transition."""
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + 1) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None, "NOT CLOSED"
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None, "NOT DISTINCT"

    good = [tuple(c) for c in configs[:L]]
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            Lp = (j-1)%n; Rp = (j+1)%n
            triple = (c[Lp], c[j], c[Rp])
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)
    conflicts = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            conflicts[j] = overlap
    return conflicts, "OK"


def check_ec_all_trans(word, ms, n):
    """Check EC with ALL transitions."""
    L = len(word)
    fc = [0]*n
    for p in word:
        fc[p] += 1

    def enum_ss(m, k):
        if k == 0:
            return [[0]]
        seqs = []
        def dfs(seq, rem):
            if rem == 0:
                if seq[-1] == 0:
                    seqs.append(list(seq))
                return
            for nv in range(m):
                if nv != seq[-1]:
                    if rem == 1 and nv != 0:
                        continue
                    seq.append(nv)
                    dfs(seq, rem-1)
                    seq.pop()
        dfs([0], k)
        return seqs

    proc_seqs = {p: enum_ss(ms[p], fc[p]) for p in range(n)}
    total_v = 0
    total_cf = 0
    for combo in iproduct(*(proc_seqs[p] for p in range(n))):
        ss = {p: combo[p] for p in range(n)}
        fcc = [0]*n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:L])) != L:
            continue
        total_v += 1
        good = configs[:L]

        mt = defaultdict(set)
        nmt = defaultdict(set)
        for t in range(L):
            c = good[t]
            mover = word[t]
            for j in range(n):
                Lp = (j-1)%n; Rp = (j+1)%n
                triple = (c[Lp], c[j], c[Rp])
                if j == mover:
                    mt[j].add(triple)
                else:
                    nmt[j].add(triple)
        has_ec = any(mt[j] & nmt[j] for j in range(n))
        if not has_ec:
            total_cf += 1

    return total_v, total_cf


def construct_wiggle_sweep(n, binary_pos):
    """Construct wiggle-sweep word for given binary positions.
    Returns word or None if construction fails."""
    bp = sorted(binary_pos)
    nb = len(bp)

    # Build ternary segments (going forward on ring from each binary)
    segments = []
    for i in range(nb):
        seg = []
        p = (bp[i] + 1) % n
        end = bp[(i+1) % nb]
        while p != end:
            seg.append(p)
            p = (p + 1) % n
        segments.append(seg)

    # Check each segment has >= 2 ternary procs
    for seg in segments:
        if len(seg) < 2:
            return None  # Can't bounce

    # Phase 1: wiggly backward sweep
    # Go backward from bp[0]-1, bouncing in each ternary segment
    word = []

    # Process segments in reverse order (backward sweep)
    for i in range(nb-1, -1, -1):
        seg = segments[i]
        seg_rev = list(reversed(seg))
        # Bounce first pair
        word.extend([seg_rev[0], seg_rev[1], seg_rev[0], seg_rev[1]])
        # Rest of segment (if any)
        for p in seg_rev[2:]:
            word.append(p)
        # Binary proc
        word.append(bp[i])

    # Phase 2: clean backward sweep
    for p in range(n-1, -1, -1):
        # Adjust: start from bp[0]-1 going backward
        actual = (bp[0] - 1 - (n-1-p)) % n
        word.append(actual)

    # Check fire counts
    ms = [3]*n
    for p in bp:
        ms[p] = 2

    fc = [0]*n
    for p in word:
        fc[p] += 1

    # Check ring-adjacency
    L = len(word)
    for i in range(L):
        cur = word[i]
        nxt = word[(i+1)%L]
        if abs(cur - nxt) % n not in (1, n-1):
            return None

    # Check fc matches ms
    if fc != ms:
        return None

    return word


def main():
    print("RA6: Gap Analysis — Which Binary Arrangements Allow CF?")
    print("=" * 70)

    n = 9

    # All possible placements of 3 non-consecutive binary procs on n=9 ring
    all_placements = []
    for combo in combinations(range(n), 3):
        # Check non-consecutive
        ok = True
        for i in range(3):
            for j in range(i+1, 3):
                if abs(combo[i] - combo[j]) % n in (1, n-1):
                    ok = False
        if ok:
            all_placements.append(combo)

    print(f"Non-consecutive 3-binary placements on n=9: {len(all_placements)}")
    for bp in all_placements[:5]:
        gaps = []
        bps = sorted(bp)
        for i in range(3):
            g = (bps[(i+1)%3] - bps[i]) % n
            gaps.append(g)
        print(f"  {bp}: gaps={gaps}")

    # Classify by gap pattern
    gap_classes = defaultdict(list)
    for bp in all_placements:
        bps = sorted(bp)
        gaps = sorted([(bps[(i+1)%3] - bps[i]) % n for i in range(3)])
        gap_classes[tuple(gaps)].append(bp)

    print(f"\nGap classes:")
    for gaps, bps in sorted(gap_classes.items()):
        print(f"  gaps={gaps}: {len(bps)} placements, e.g. {bps[0]}")

    # The known CF word
    print("\n--- Testing known CF word ---")
    word_known = [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0]
    ms_known = [2,3,3,2,3,3,2,3,3]
    conflicts, status = check_ec(word_known, ms_known, n)
    print(f"  Known word EC (inc): {len(conflicts) if conflicts else 0} conflicts [{status}]")

    # Try constructing wiggle-sweep for each placement
    print("\n--- Constructing wiggle-sweep for all placements ---")
    for gaps, placements in sorted(gap_classes.items()):
        bp = placements[0]
        ms = [3]*n
        for p in bp:
            ms[p] = 2

        # Try the known word pattern adapted to this placement
        # For gap=(3,3,3), we know the word works
        # For other gaps, need different construction

        # Direct approach: try building the wiggle-sweep
        word = construct_wiggle_sweep(n, bp)
        if word is None:
            print(f"  gaps={gaps}, bp={bp}: construction FAILED (segment too short)")
            continue

        conflicts, status = check_ec(word, ms, n)
        if status != "OK":
            print(f"  gaps={gaps}, bp={bp}: {status}")
            continue

        if not conflicts:
            # Verify with all transitions
            tv, tc = check_ec_all_trans(word, ms, n)
            print(f"  gaps={gaps}, bp={bp}: NO EC (inc), all-trans: {tv} valid, {tc} CF")
        else:
            print(f"  gaps={gaps}, bp={bp}: EC at {len(conflicts)} procs (inc)")

    # === Special focus on gap-2 (alternating) ===
    print("\n--- Gap-2 deep investigation ---")
    # [2,3,2,3,2,3,3,3,3] has binary at {0,2,4}, gaps=(2,2,5)
    ms_alt = [2,3,2,3,2,3,3,3,3]
    bp_alt = (0,2,4)
    segments_alt = []
    bps = sorted(bp_alt)
    for i in range(3):
        seg = []
        p = (bps[i]+1)%n
        end = bps[(i+1)%3]
        while p != end:
            seg.append(p)
            p = (p+1)%n
        segments_alt.append(seg)
    print(f"  bp={bp_alt}, segments: {segments_alt}")
    print(f"  Segment sizes: {[len(s) for s in segments_alt]}")
    print(f"  Segments with <2 procs: {sum(1 for s in segments_alt if len(s) < 2)}")

    # For gap-2: segments are [1], [3], [5,6,7,8,0] - wait, that's wrong
    # Actually bp=(0,2,4), so:
    # seg 0: 0+1=1 to 2 -> [1]
    # seg 1: 2+1=3 to 4 -> [3]
    # seg 2: 4+1=5 to 0 -> [5,6,7,8]
    # Two segments have size 1! Can't bounce there.

    # For the all-alternating [3,2,3,2,3,2,3,2,3]:
    # 4 binary at {1,3,5,7}, gaps all (2,2,2,2)... wait that's 4 binary
    # Let me check the actual alternating 3-binary case

    print("\n--- Why gap matters ---")
    print("For 3 binary procs on n=9 ring:")
    print("Possible gap patterns and segment sizes:")
    for gaps, placements in sorted(gap_classes.items()):
        bp = placements[0]
        bps = sorted(bp)
        segs = []
        for i in range(3):
            p = (bps[i]+1)%n
            end = bps[(i+1)%3]
            seg = []
            while p != end:
                seg.append(p)
                p = (p+1)%n
            segs.append(len(seg))
        min_seg = min(segs)
        print(f"  gaps={gaps}: segment sizes={sorted(segs)}, min={min_seg}, "
              f"wiggle possible={'YES' if min_seg >= 2 else 'NO'}")

    # Try random search on gap-2 arrangements
    print("\n--- Random search on gap-(2,2,5) arrangement ---")
    import random
    random.seed(42)

    ms_gap2 = [2,3,2,3,2,3,3,3,3]

    def random_word_v2(n, ms, attempts=100):
        target = list(ms)
        total = sum(target)
        for _ in range(attempts):
            fc = [0]*n
            start = random.randint(0, n-1)
            word = [start]
            fc[start] = 1
            for step in range(total - 1):
                last = word[-1]
                nbrs = [(last+1)%n, (last-1)%n]
                random.shuffle(nbrs)
                scores = [(max(0, target[p]-fc[p]), p) for p in nbrs]
                scores.sort(reverse=True)
                nxt = scores[0][1] if scores[0][0] > 0 else (scores[1][1] if scores[1][0] > 0 else random.choice(nbrs))
                word.append(nxt)
                fc[nxt] += 1
            if all(fc[p] == target[p] for p in range(n)):
                if abs(word[-1]-word[0])%n in (1, n-1):
                    return word
        return None

    cf_found = 0
    total_valid = 0
    for trial in range(50000):
        word = random_word_v2(n, ms_gap2, attempts=5)
        if word is None:
            continue
        good_cycle = [[0]*n]
        for t in range(len(word)):
            c = list(good_cycle[-1])
            p = word[t]
            c[p] = (c[p]+1) % ms_gap2[p]
            good_cycle.append(c)
        if good_cycle[-1] != good_cycle[0]:
            continue
        if len(set(tuple(c) for c in good_cycle[:-1])) != len(word):
            continue
        total_valid += 1
        good = [tuple(c) for c in good_cycle[:-1]]
        mt = defaultdict(set)
        nmt = defaultdict(set)
        for t in range(len(word)):
            c = good[t]
            mover = word[t]
            for j in range(n):
                triple = (c[(j-1)%n], c[j], c[(j+1)%n])
                if j == mover:
                    mt[j].add(triple)
                else:
                    nmt[j].add(triple)
        if not any(mt[j] & nmt[j] for j in range(n)):
            cf_found += 1
            if cf_found <= 3:
                print(f"  CF found! word={word}")

    print(f"  gap-(2,2,5): {total_valid} valid, {cf_found} CF")

    # Also try gap-(2,3,4)
    print("\n--- Random search on gap-(2,3,4) arrangement ---")
    random.seed(42)
    # binary at {0,2,5}: gaps 2,3,4
    ms_gap234 = [2,3,2,3,3,2,3,3,3]  # binary at 0,2,5
    cf_found2 = 0
    total_valid2 = 0
    for trial in range(50000):
        word = random_word_v2(n, ms_gap234, attempts=5)
        if word is None:
            continue
        good_cycle = [[0]*n]
        for t in range(len(word)):
            c = list(good_cycle[-1])
            p = word[t]
            c[p] = (c[p]+1) % ms_gap234[p]
            good_cycle.append(c)
        if good_cycle[-1] != good_cycle[0]:
            continue
        if len(set(tuple(c) for c in good_cycle[:-1])) != len(word):
            continue
        total_valid2 += 1
        good = [tuple(c) for c in good_cycle[:-1]]
        mt = defaultdict(set)
        nmt = defaultdict(set)
        for t in range(len(word)):
            c = good[t]
            mover = word[t]
            for j in range(n):
                triple = (c[(j-1)%n], c[j], c[(j+1)%n])
                if j == mover:
                    mt[j].add(triple)
                else:
                    nmt[j].add(triple)
        if not any(mt[j] & nmt[j] for j in range(n)):
            cf_found2 += 1
            if cf_found2 <= 3:
                print(f"  CF found! word={word}")

    print(f"  gap-(2,3,4): {total_valid2} valid, {cf_found2} CF")

    print("\nDone.")


if __name__ == "__main__":
    main()
