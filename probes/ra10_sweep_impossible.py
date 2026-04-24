#!/usr/bin/env python3
"""
RA10b: Investigate why sweep mover words are structurally impossible
with ≥3 non-consecutive binary at sub-threshold product.

Hypothesis: With ≥3 binary procs (ms[p]=2), each fires exactly 2 times.
CL = sum(ms). For sweep: |disp| ≥ 2n, meaning the walk has net wrap ≥ 2.
Each step is ±1 on ring. Net displacement = (CW steps) - (CCW steps).
Total steps = CL = CW + CCW.
|disp| = |CW - CCW| ≥ 2n.
So CW + CCW = CL and |CW - CCW| ≥ 2n.
This means max(CW,CCW) ≥ n + CL/2 and min(CW,CCW) ≤ CL/2 - n.
For CL/2 - n ≥ 0: need CL ≥ 2n.

With ≥3 binary: CL = sum(ms) ≤ 3*(n-3) + 2*3 = 3n - 3 (if exactly 3 binary, rest ternary).
Actually CL = sum(ms). With k binary: CL = 2k + 3(n-k) = 3n - k.
For k ≥ 3: CL = 3n - k ≤ 3n - 3.
Need CL ≥ 2n for sweep (min CW/CCW ≥ 0): always true for n ≥ 3.

But more specifically: |disp| ≥ 2n requires CL - 2n steps "in the right direction".
With CL = 3n-k: |disp| ≤ CL = 3n-k. Need 3n-k ≥ 2n, i.e., n ≥ k.
For k=3: need n ≥ 3. OK.

So sweep words COULD exist in principle. Why don't they?

Maybe the constraint is tighter. Let me check if ring-adjacent words with
these fire counts exist at all (ignoring sweep), then separately check
if any of them are sweeps.
"""
import time


def total_displacement(word, n):
    """Signed displacement of cyclic mover walk."""
    disp = 0
    L = len(word)
    for i in range(L):
        nxt = word[(i + 1) % L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            disp += 1
        elif diff == n - 1:
            disp -= 1
        else:
            return None
    return disp


def enumerate_words_dfs(n, ms, max_results=5000, timeout=60):
    """Enumerate ALL ring-adjacent cyclic mover words with fc=ms."""
    target_cl = sum(ms)
    results = []
    t0 = time.time()

    def dfs(word, fc):
        if time.time() - t0 > timeout:
            return
        if len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n - 1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0] * n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)

    return results


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def main():
    print("RA10b: Sweep Word Structural Impossibility")
    print("=" * 70)

    # Test: do ANY ring-adjacent words exist? What displacements occur?
    test_cases = [
        (5, [2, 3, 2, 3, 2]),
        (5, [3, 2, 3, 2, 2]),
        (5, [2, 2, 3, 2, 3]),  # binary at {0,1,3} — has consecutive pair
        (6, [2, 3, 2, 3, 2, 3]),
        (6, [2, 3, 2, 3, 3, 2]),
        (7, [2, 3, 2, 3, 2, 3, 3]),
        (7, [2, 3, 2, 3, 3, 2, 3]),
    ]

    for n, ms in test_cases:
        bins = [p for p in range(n) if ms[p] == 2]
        k = len(bins)
        CL = sum(ms)
        product = 1
        for m in ms:
            product *= m
        threshold = 4 * (3 ** (n - 2))

        print(f"\nn={n}, ms={ms}")
        print(f"  Binary at {bins} (k={k}), CL={CL}, product={product}, threshold={threshold}")
        print(f"  Max possible |disp| = CL = {CL}, need ≥ {2*n} for sweep")

        t0 = time.time()
        words = enumerate_words_dfs(n, ms, max_results=5000, timeout=30)
        t1 = time.time()

        # Deduplicate
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        print(f"  Found {len(unique)} unique words in {t1-t0:.1f}s")

        if not unique:
            print(f"  >>> NO RING-ADJACENT WORDS AT ALL <<<")
            continue

        # Displacement distribution
        disp_counts = {}
        for w in unique.values():
            d = total_displacement(list(w), n)
            disp_counts[d] = disp_counts.get(d, 0) + 1

        print(f"  Displacement distribution:")
        for d in sorted(disp_counts.keys()):
            sweep_marker = " [SWEEP]" if abs(d) >= 2 * n else ""
            print(f"    disp={d:+3d}: {disp_counts[d]} words{sweep_marker}")

        n_sweep = sum(v for d, v in disp_counts.items() if abs(d) >= 2 * n)
        print(f"  Sweep words: {n_sweep}/{len(unique)}")

    # Now let's understand WHY displacement is bounded.
    # Key constraint: binary proc fires exactly 2 times.
    # Each firing at proc p corresponds to the walk being at p.
    # Between two visits to p, the walk must go away and come back.
    # If p fires only 2 times, the walk visits p exactly twice.
    # Each visit contributes a "segment" of the walk.
    #
    # Think of the walk as segments between visits to binary procs.
    # With k=3 binary procs, the walk visits them total 2k=6 times.
    # Between visits to binary procs, the walk traverses ternary procs.
    #
    # The displacement of each segment is bounded.
    # Net displacement is sum of segment displacements.
    #
    # Key: between two consecutive visits to binary procs, the walk
    # must stay within the ternary gap between them.

    print(f"\n{'='*70}")
    print("PHASE 2: Displacement bound analysis")
    print("=" * 70)

    # Let's check: with 3 binary at {0, 2, 4} on n=5 ring,
    # gaps between binary: 0→2 (through 1), 2→4 (through 3), 4→0 (through nothing, adjacent)
    # Wait, 4 and 0 are adjacent on ring of 5? 4→0 is +1 mod 5.
    # So gaps: {0,2,4} on ring of 5: ternary at {1,3}.
    # Gap 0→2: position 1 (1 ternary)
    # Gap 2→4: position 3 (1 ternary)
    # Gap 4→0: no ternary (adjacent)
    #
    # Between visits to 0 and 2, walk goes through 1 (fire 3 times).
    # Each visit to 1 is a step from 0→1 or 2→1, then 1→0 or 1→2.
    # The displacement of the segment 0→1→0 is 0.
    # The displacement of 0→1→2 is +2.
    # The displacement of 2→1→0 is -2.
    # The displacement of 2→1→2 is 0.
    #
    # So each "bounce" through a gap of width g contributes displacement in [-2g, +2g]?
    # No, more precisely the walk must respect fire counts.

    # Let me think about it differently.
    # The walk is a sequence of positions on ring of size n.
    # Lift to the universal cover (integers). Walk on Z.
    # Displacement = final position - initial position on Z.
    # Each step ±1 on Z.
    # CL = 3n-k steps total.
    # Binary proc p: fires 2 times → walk visits p exactly twice.
    # On Z, these are positions ≡ p (mod n), say p and p+an for some a.
    # With 3 binary: walk visits each binary lift exactly twice.
    #
    # The displacement is constrained by how far the walk can go on Z
    # while respecting all fire count constraints.

    # Actually, I think there might be a simpler counting argument.
    # Let me check: with non-adjacent binary, can we bound the displacement
    # by the gap structure?

    print("\nPHASE 2a: Lifted walk analysis")
    print("-" * 60)

    for n, ms in [(5, [2, 3, 2, 3, 2]), (7, [2, 3, 2, 3, 2, 3, 3])]:
        bins = [p for p in range(n) if ms[p] == 2]
        CL = sum(ms)
        print(f"\nn={n}, ms={ms}, bins={bins}, CL={CL}")

        words = enumerate_words_dfs(n, ms, max_results=5000, timeout=30)
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        # For each word, compute the lifted walk
        max_disp = 0
        max_range = 0
        for w in unique.values():
            wl = list(w)
            L = len(wl)
            # Lifted walk
            pos = [0]  # start at 0 (position of first proc)
            for i in range(L):
                nxt_ring = wl[(i + 1) % L]
                cur_ring = wl[i]
                diff = (nxt_ring - cur_ring) % n
                if diff == 1:
                    pos.append(pos[-1] + 1)
                else:
                    pos.append(pos[-1] - 1)

            disp = pos[-1]
            walk_range = max(pos) - min(pos)
            max_disp = max(max_disp, abs(disp))
            max_range = max(max_range, walk_range)

        print(f"  Max |disp| = {max_disp} (need {2*n} for sweep)")
        print(f"  Max walk range = {max_range}")
        print(f"  CL = {CL}")

    # PHASE 3: Try larger n and different binary placements
    print(f"\n{'='*70}")
    print("PHASE 3: Larger n — systematic sweep existence check")
    print("=" * 70)

    from itertools import combinations

    for n in [5, 6, 7, 8, 9]:
        threshold = 4 * (3 ** (n - 2))
        # Generate all non-consecutive binary placements with exactly 3 binary
        for bin_combo in combinations(range(n), 3):
            # Check non-consecutive (no three consecutive)
            bins_set = set(bin_combo)
            has_triple = False
            for i in range(n):
                if i in bins_set and (i+1)%n in bins_set and (i+2)%n in bins_set:
                    has_triple = True
                    break
            if has_triple:
                continue

            # Also check no pair is adjacent if we want truly non-consecutive
            # Actually, "non-consecutive" in the problem means no THREE consecutive.
            # But let's check both.

            ms = [2 if p in bins_set else 3 for p in range(n)]
            product = 1
            for m in ms:
                product *= m
            if product >= threshold:
                continue

            CL = sum(ms)

            # Quick check: CL vs 2n
            if CL < 2 * n:
                # Can't have |disp| ≥ 2n with only CL steps of ±1
                print(f"  n={n} bins={bin_combo}: CL={CL} < 2n={2*n}, trivially no sweep")
                continue

            words = enumerate_words_dfs(n, ms, max_results=100, timeout=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            n_sweep = 0
            max_disp = 0
            for w in unique.values():
                d = total_displacement(list(w), n)
                if d is not None:
                    max_disp = max(max_disp, abs(d))
                    if abs(d) >= 2 * n:
                        n_sweep += 1

            status = "SWEEP EXISTS!" if n_sweep > 0 else "no sweep"
            print(f"  n={n} bins={list(bin_combo)} CL={CL}: {len(unique)} words, max|disp|={max_disp}, {status}")

    # PHASE 4: What about 4+ binary?
    print(f"\n{'='*70}")
    print("PHASE 4: 4+ binary (still non-consecutive)")
    print("=" * 70)

    for n in [5, 6, 7, 8]:
        threshold = 4 * (3 ** (n - 2))
        for k in range(4, n + 1):
            for bin_combo in combinations(range(n), k):
                bins_set = set(bin_combo)
                has_triple = False
                for i in range(n):
                    if i in bins_set and (i+1)%n in bins_set and (i+2)%n in bins_set:
                        has_triple = True
                        break
                if has_triple:
                    continue

                ms = [2 if p in bins_set else 3 for p in range(n)]
                product = 1
                for m in ms:
                    product *= m
                if product >= threshold:
                    continue

                CL = sum(ms)
                if CL < 2 * n:
                    print(f"  n={n} k={k} bins={list(bin_combo)}: CL={CL} < 2n={2*n}, trivially no sweep")
                    continue

                words = enumerate_words_dfs(n, ms, max_results=100, timeout=5)
                unique = {}
                for w in words:
                    c = canonicalize(w)
                    if c not in unique:
                        unique[c] = w

                n_sweep = 0
                max_disp = 0
                for w in unique.values():
                    d = total_displacement(list(w), n)
                    if d is not None:
                        max_disp = max(max_disp, abs(d))
                        if abs(d) >= 2 * n:
                            n_sweep += 1

                status = "SWEEP EXISTS!" if n_sweep > 0 else "no sweep"
                print(f"  n={n} k={k} bins={list(bin_combo)} CL={CL}: {len(unique)} words, max|disp|={max_disp}, {status}")

    # PHASE 5: Displacement bound theorem
    print(f"\n{'='*70}")
    print("PHASE 5: Displacement bound — can we prove |disp| < 2n?")
    print("=" * 70)

    # With k binary (each firing 2x) and (n-k) ternary (each firing 3x):
    # CL = 2k + 3(n-k) = 3n - k.
    # Walk has CL steps, each ±1, so |disp| ≤ CL = 3n-k.
    # Sweep needs |disp| ≥ 2n.
    # So need 3n-k ≥ 2n, i.e., k ≤ n. Always true.
    # But |disp| = |CW - CCW| where CW + CCW = CL.
    # |disp| = 2n iff CW = (CL+2n)/2 = (3n-k+2n)/2 = (5n-k)/2.
    # This needs 5n-k even, and CW ≤ CL, i.e., (5n-k)/2 ≤ 3n-k, i.e., n ≤ k.
    # Wait: (5n-k)/2 ≤ 3n-k iff 5n-k ≤ 6n-2k iff k ≤ n. True.
    # So the count constraint alone doesn't rule out sweep.

    # The constraint must come from RING ADJACENCY + FIRE COUNTS.
    # The walk visits binary proc p exactly 2 times.
    # Between consecutive visits to any proc, the walk oscillates.
    #
    # Key insight: for non-adjacent binary procs, the walk must traverse
    # at least one ternary proc to get between them. These ternary procs
    # fire 3 times = odd. So between visits to a binary proc, the walk
    # passes through ternary procs an odd number of times? No, that's
    # about the fire count, not traversals.

    # Let me think about this differently.
    # Consider two non-adjacent binary procs b1, b2 with ternary procs between them.
    # The walk must visit b1 twice and b2 twice.
    # On the lifted walk (on Z), b1 appears at positions ≡ b1 (mod n),
    # and b2 at positions ≡ b2 (mod n).
    #
    # For the walk to be a sweep (disp ≥ 2n), it must advance by ≥ 2n total.
    # But each binary proc is visited only 2 times. On the lift, these are
    # at positions b1+a*n and b1+c*n for some a,c. The walk visits b1+a*n
    # then eventually b1+c*n. Since fc(b1)=2, we must have |c-a| ≤ 1
    # (the walk wraps past b1 at most twice).
    #
    # Actually wait: on the lift, the walk visits b1+a1*n and b1+a2*n.
    # It could be that a2 = a1+2 (walk went past b1 at b1+(a1+1)*n but didn't fire).
    # No! Each visit to the lift position b1+j*n IS a firing at b1 (since the
    # walk visits that ring position = fires that proc). So the walk visits
    # b1 on the lift at exactly 2 heights.

    # Hmm, but the walk visits POSITION b1 on the ring. On the lift, this
    # corresponds to visiting any b1 + j*n. Each such visit is a firing.
    # So with fc(b1) = 2, the walk visits exactly 2 of {b1+j*n : j ∈ Z}.
    # Say heights h1 < h2 where h1 ≡ h2 ≡ b1 (mod n), h2 - h1 = c*n for some c ≥ 1.
    #
    # The displacement must be at least 2n. The walk starts at some position
    # and ends at start + disp. For |disp| ≥ 2n to work, the walk range must
    # be ≥ 2n.
    #
    # Key constraint: binary proc visits are at EXACTLY 2 heights.
    # For the walk to span range ≥ 2n, some proc must be visited at height
    # difference ≥ 2n. But binary procs have fc=2, so their two heights differ
    # by c*n where 1 ≤ c. For c ≥ 2, difference is ≥ 2n.
    # Ternary procs have fc=3, heights could span up to 2n.
    #
    # But for a CYCLIC walk, the start and end are the same height shifted by disp.
    # The walk must return to start + disp.

    # Let me just enumerate what displacement values actually occur.
    print("\nDisplacement values for all configurations:")
    for n in range(5, 10):
        threshold = 4 * (3 ** (n - 2))
        found_sweep = False
        for bin_combo in combinations(range(n), 3):
            bins_set = set(bin_combo)
            has_triple = False
            for i in range(n):
                if i in bins_set and (i+1)%n in bins_set and (i+2)%n in bins_set:
                    has_triple = True
                    break
            if has_triple:
                continue

            # Check non-adjacent (no pair adjacent either — truly non-consecutive)
            has_pair = False
            for i in range(n):
                if i in bins_set and (i+1)%n in bins_set:
                    has_pair = True
                    break

            ms = [2 if p in bins_set else 3 for p in range(n)]
            product = 1
            for m in ms:
                product *= m
            if product >= threshold:
                continue

            CL = sum(ms)

            words = enumerate_words_dfs(n, ms, max_results=2000, timeout=10)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            disps = set()
            for w in unique.values():
                d = total_displacement(list(w), n)
                if d is not None:
                    disps.add(d)

            if disps:
                max_abs = max(abs(d) for d in disps)
                adj = "adj" if has_pair else "nonadj"
                if max_abs >= 2 * n:
                    found_sweep = True
                if max_abs >= n:  # interesting cases
                    print(f"  n={n} bins={list(bin_combo)} [{adj}]: disps={sorted(disps)}, max|d|={max_abs}, need≥{2*n}")

        if not found_sweep:
            print(f"  n={n}: NO SWEEP for any 3-binary non-triple placement")


if __name__ == '__main__':
    main()
