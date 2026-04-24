#!/usr/bin/env python3
"""
RA10e: Detailed structural analysis of sweep cycles with non-consecutive binary.

Key findings so far:
- Sweep cycles exist at n=7,9 with ≥3 binary (no triple)
- They have disp = ±2n exactly, NOT ±CL
- They are NOT uniform (have k CCW wiggles where k = binary count)
- They have NO entry conflict
- They have MNU

The goal: find a direct argument for sweep + non-consec binary → False.

Possible approaches:
A. Show sweep implies a second good cycle exists (shadow argument adapted)
B. Show sweep structure contradicts convergence directly
C. Show the wiggles force a structural impossibility
"""
from collections import defaultdict
from itertools import combinations
import time


def total_displacement(word, n):
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
    target_cl = sum(ms)
    results = []
    t0 = time.time()

    def dfs(word, fc):
        if time.time() - t0 > timeout or len(results) >= max_results:
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


def analyze_word_structure(word, n, ms):
    """Analyze the walk structure: identify wiggles, uniform segments, etc."""
    L = len(word)
    wl = list(word)
    bins_set = {p for p, m in enumerate(ms) if m == 2}

    # Identify direction of each step
    steps = []
    for i in range(L):
        cur = wl[i]
        nxt = wl[(i + 1) % L]
        diff = (nxt - cur) % n
        direction = 1 if diff == 1 else -1
        steps.append((cur, nxt, direction))

    # Find wiggles: CCW step followed by CW step (or vice versa)
    wiggles = []
    for i in range(L):
        if steps[i][2] == -1:  # CCW step
            wiggles.append({
                'pos': i,
                'from': steps[i][0],
                'to': steps[i][1],
                'prev_dir': steps[(i-1)%L][2],
                'next_dir': steps[(i+1)%L][2],
                'is_binary_from': steps[i][0] in bins_set,
                'is_binary_to': steps[i][1] in bins_set,
            })

    # Track which procs are visited between wiggles
    return steps, wiggles


def main():
    print("RA10e: Sweep Cycle Structure Analysis")
    print("=" * 70)

    # Analyze n=9, bins={0,3,6} in detail
    n = 9
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]  # bins at {0,3,6}
    bins_set = {0, 3, 6}

    words = enumerate_words_dfs(n, ms, max_results=100, timeout=10)
    unique = {}
    for w in words:
        c = canonicalize(w)
        if c not in unique:
            unique[c] = w

    sweep_words = [w for w in unique.values()
                   if total_displacement(list(w), n) is not None
                   and abs(total_displacement(list(w), n)) >= 2 * n]

    print(f"n={n}, ms={ms}, bins={sorted(bins_set)}")
    print(f"CL={sum(ms)}, {len(sweep_words)} sweep words")

    for w in sweep_words:
        wl = list(w)
        disp = total_displacement(wl, n)
        steps, wiggles = analyze_word_structure(wl, n, ms)

        print(f"\nword={wl}")
        print(f"  disp={disp}, CW={sum(1 for s in steps if s[2]==1)}, CCW={sum(1 for s in steps if s[2]==-1)}")

        for wig in wiggles:
            print(f"  WIGGLE at step {wig['pos']}: "
                  f"{wig['from']}→{wig['to']} (CCW), "
                  f"from_binary={wig['is_binary_from']}, to_binary={wig['is_binary_to']}")

    # KEY ANALYSIS: Every wiggle is adjacent to a binary proc
    print(f"\n{'='*70}")
    print("WIGGLE-BINARY CORRESPONDENCE")
    print("=" * 70)

    all_wiggle_adjacent_binary = True
    for n_test in [7, 9]:
        threshold = 4 * (3 ** (n_test - 2))
        for bin_combo in combinations(range(n_test), 3):
            bins_set = set(bin_combo)
            has_triple = any(i in bins_set and (i+1)%n_test in bins_set and (i+2)%n_test in bins_set for i in range(n_test))
            if has_triple:
                continue
            ms_t = [2 if p in bins_set else 3 for p in range(n_test)]
            product = 1
            for m in ms_t:
                product *= m
            if product >= threshold:
                continue

            words = enumerate_words_dfs(n_test, ms_t, max_results=100, timeout=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                d = total_displacement(list(w), n_test)
                if d is None or abs(d) < 2 * n_test:
                    continue

                steps, wiggles = analyze_word_structure(list(w), n_test, ms_t)
                for wig in wiggles:
                    # Check if the CCW step involves a binary neighbor
                    from_p = wig['from']
                    to_p = wig['to']
                    # Binary neighbors of from_p or to_p
                    binary_near = (from_p in bins_set or to_p in bins_set or
                                   (from_p + 1) % n_test in bins_set or
                                   (from_p - 1) % n_test in bins_set or
                                   (to_p + 1) % n_test in bins_set or
                                   (to_p - 1) % n_test in bins_set)
                    if not binary_near:
                        all_wiggle_adjacent_binary = False
                        print(f"  EXCEPTION: n={n_test} bins={list(bin_combo)} "
                              f"wiggle {from_p}→{to_p} not near binary")

    if all_wiggle_adjacent_binary:
        print("ALL wiggles are adjacent to a binary proc!")

    # CRITICAL CHECK: for each wiggle, where exactly is the binary proc?
    print(f"\n{'='*70}")
    print("WIGGLE POSITION RELATIVE TO BINARY")
    print("=" * 70)

    for n_test in [7, 9]:
        threshold = 4 * (3 ** (n_test - 2))
        for bin_combo in combinations(range(n_test), 3):
            bins_set = set(bin_combo)
            has_triple = any(i in bins_set and (i+1)%n_test in bins_set and (i+2)%n_test in bins_set for i in range(n_test))
            if has_triple:
                continue
            ms_t = [2 if p in bins_set else 3 for p in range(n_test)]
            product = 1
            for m in ms_t:
                product *= m
            if product >= threshold:
                continue

            words = enumerate_words_dfs(n_test, ms_t, max_results=100, timeout=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                d = total_displacement(list(w), n_test)
                if d is None or abs(d) < 2 * n_test:
                    continue

                wl = list(w)
                L = len(wl)
                # Classify the walk structure
                # Each binary proc fires exactly 2 times.
                # In a CW sweep of displacement 2n with (n-3) CCW steps:
                # CW steps = (CL+2n)/2 = (3n-3+2n)/2 = (5n-3)/2
                # CCW steps = (CL-2n)/2 = (3n-3-2n)/2 = (n-3)/2
                cw = sum(1 for i in range(L) if (wl[(i+1)%L] - wl[i]) % n_test == 1)
                ccw = L - cw
                expected_ccw = (n_test - 3) // 2 if d > 0 else (n_test - 3) // 2
                print(f"  n={n_test} bins={list(bin_combo)} d={d}: CW={cw} CCW={ccw} (expected CCW={(n_test-3)//2 if n_test%2==1 else '?'})")

                # Where are the CCW steps?
                for i in range(L):
                    nxt = wl[(i+1)%L]
                    cur = wl[i]
                    if (nxt - cur) % n_test == n_test - 1:  # CCW
                        # Which binary proc is nearest?
                        nearest_bin = min(bins_set, key=lambda b: min(abs(cur-b), abs(cur-b-n_test), abs(cur-b+n_test)))
                        print(f"    CCW at step {i}: {cur}→{nxt}, nearest binary={nearest_bin}, dist={min(abs(cur-nearest_bin)%n_test, abs(nearest_bin-cur)%n_test)}")
                break  # just first sweep word per config

    # Now let's think about the proof approach.
    # For n odd: (n-3)/2 CCW steps (integer).
    # For n=7: 2 CCW, for n=9: 3 CCW.
    # The CCW steps correspond to the binary procs having fc=2 instead of fc=3.
    # The surplus firing count for ternary (3) vs binary (2) is 1 per binary proc.
    # With 3 binary procs: surplus = 3.
    # In a pure CW sweep: CL = 2n = sum(fc).
    # Here: CL = 3n-3, but 2n displacement. CW = (5n-3)/2, CCW = (n-3)/2.
    #
    # The CCW steps are "detours" that add a step but no net displacement.
    # Each detour: CW, CCW = one step CW + one step CCW = net 0 displacement,
    # but adds 2 to the step count. Wait, that's not right.
    # Let me count: CL = CW + CCW, disp = CW - CCW.
    # CW = (CL + disp)/2 = (3n-3+2n)/2 = (5n-3)/2.
    # CCW = (CL - disp)/2 = (3n-3-2n)/2 = (n-3)/2.
    # Each CCW step reduces displacement by 2 compared to all-CW.
    # Net displacement if all CW: CL = 3n-3.
    # Actual: 3n-3 - 2*(n-3)/2 = 3n-3 - (n-3) = 2n. ✓

    print(f"\n{'='*70}")
    print("PROOF SKETCH: sweep + non-consec binary → False (direct)")
    print("=" * 70)
    print("""
APPROACH: Direct sweep displacement counting argument.

Claim: For ≥3 binary (no triple) at sub-threshold product,
sweep (|disp| ≥ 2n) is impossible because:

1. |disp| ≤ CL = sum(ms). Need CL ≥ 2n.
   CL = 2k + 3(n-k) = 3n - k where k = number of binary procs.
   For k=3: CL = 3n-3. Need 3n-3 ≥ 2n, i.e., n ≥ 3. Always true.

2. |disp| must equal CL mod 2 (parity: CW + CCW = CL, CW - CCW = disp,
   so disp = CL - 2*CCW). So |disp| ≡ CL (mod 2).
   CL = 3n-3 has parity (n-1). disp ≡ n-1 (mod 2).
   For sweep: |disp| ≥ 2n, and |disp| ≤ 3n-3.
   Values: 2n, 2n+2, ..., 3n-3 (if same parity), or empty.
   2n ≡ 0 (mod 2). CL = 3n-3 ≡ n-1 (mod 2).
   If n is odd: 2n is even, CL is even. OK, 2n is achievable.
   If n is even: 2n is even, CL is odd. So disp must be odd.
   Minimum odd |disp| ≥ 2n is 2n+1. But 2n+1 ≤ 3n-3 iff n ≥ 4. True for n ≥ 9.
   Wait, disp ≡ CL (mod 2). If CL is odd, disp is odd.
   So minimum sweep displacement is 2n+1 (if CL odd, which is when n is even).

   WAIT: sweep is |disp| ≥ 2n, not > 2n. With n even:
   |disp| is odd, so minimum is 2n+1 > 2n. This is still a sweep.
   But does |disp| = 2n+1 actually occur?

   For k=3 binary: |disp| = CL - 2*CCW = 3n-3 - 2*CCW.
   For |disp| = 2n+1: CCW = (3n-3 - 2n-1)/2 = (n-4)/2.
   Integer iff n is even. ✓ for n even.

   But with k > 3 binary: CL = 3n-k. |disp| = 3n-k - 2*CCW.
   Need 3n-k - 2*CCW ≥ 2n, i.e., CCW ≤ (n-k)/2.
   For k > n: impossible (CL < 2n, can't sweep).
   But k ≤ n trivially.

This doesn't give impossibility from counting alone.

ALTERNATIVE APPROACH: Use the Lean-already-proved fact:
sweep + ≥3 binary + no triple + uniformDirection → False
(via `not_uniformDirection_and_isSweep_of_hasGe3Binary` or similar)
combined with:
sweep + ≥3 binary + no triple + ¬uniformDirection → False
(this is what we need to prove)

Actually, does `not_uniformDirection_and_isSweep_of_hasGe3Binary` exist?
""")

    # Let me check: is there a parity argument?
    # If gc has uniform direction (all CW), then fc(p) is constant for all p.
    # But binary has fc=2, ternary has fc=3. Contradiction!
    # So sweep + binary → NOT uniformDirection.
    # And the proof already handles uniformDirection sweep + binary.
    # The problem is exactly the non-uniformDirection sweep case.

    print("PARITY OBSERVATION:")
    print("If cycle is uniformCW, then fireCount is constant for all procs.")
    print("But binary fires 2, ternary fires 3. CONTRADICTION.")
    print("So sweep with mixed state sizes → NOT uniformDirection.")
    print("This means all sweep cycles with binary procs are non-uniform.")
    print("The WaterfallBridge handles UNIFORM sweeps only (length 2n, all fc=2).")
    print("Non-uniform sweeps need a DIFFERENT argument.")

    print(f"\n{'='*70}")
    print("DISPLACEMENT PARITY REFINED")
    print("=" * 70)

    # Actually wait. Let me reconsider. isSweep means |disp| ≥ 2n.
    # With ≥3 binary: CL = 3n - k ≤ 3n - 3.
    # |disp| ≤ CL = 3n - k.
    # So 2n ≤ |disp| ≤ 3n - k.
    # If k ≥ n+1: 3n-k < 2n, impossible. But k ≤ n always (n procs total).
    # Actually k ≥ n+1 is impossible: k ≤ n. 3n-k ≥ 2n iff k ≤ n. Always true.
    #
    # BUT: the fire count constraint is stronger.
    # Binary proc p fires an EVEN number of times (ms[p] = 2, fc divisible by 2? NO).
    # Wait: fc(p) must divide CL? No, fc(p) = ms[p] (each proc fires exactly ms[p] times).
    # Actually: in a good cycle of length L, each proc p fires fc(p) times where
    # sum fc(p) = L and c[p] cycles back to its starting value after fc(p) fires.
    # So fc(p) must be a multiple of ms[p] for c[p] to return to start.
    # For binary: fc(p) = 2k for some k ≥ 1. For ternary: fc(p) = 3k.
    # Under sub-threshold: product < 4*3^(n-2). L = sum fc(p) < product.
    # Minimum: fc(p) = ms[p] (each fires once through its cycle).
    # L = CL = sum ms = 2k + 3(n-k) = 3n-k.
    #
    # But wait: good cycles with fc(p) = ms[p] have L = CL.
    # For longer cycles: fc(p) = 2*ms[p] would give L = 2*CL.
    # But 2*CL = 2(3n-k) > product for sub-threshold. So fc(p) = ms[p].
    # Actually: 2*CL = 6n-2k. Product < 4*3^(n-2). For n=9, k=3:
    # 2*CL = 48, product < 8748. So 2*CL << product. Can have fc = 2*ms!
    # But in practice: good cycles have distinct configs, so L ≤ product.
    # L = fc(0) + ... + fc(n-1). Each fc(p) is a multiple of ms[p].
    # Minimum: fc(p) = ms[p].
    #
    # For our sweep cycles: fc(p) = ms[p] (verified computationally).
    # So L = CL = 3n-k.

    # Check if fc = ms for all sweep cycles
    for n_test in [7, 9]:
        threshold = 4 * (3 ** (n_test - 2))
        for bin_combo in [(0,3,6)] if n_test == 9 else [(0,1,4)]:
            bins_set = set(bin_combo)
            ms_t = [2 if p in bins_set else 3 for p in range(n_test)]
            product = 1
            for m in ms_t:
                product *= m
            if product >= threshold:
                continue

            words = enumerate_words_dfs(n_test, ms_t, max_results=100, timeout=5)
            unique = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique:
                    unique[c] = w

            for w in unique.values():
                d = total_displacement(list(w), n_test)
                if d is None or abs(d) < 2 * n_test:
                    continue
                wl = list(w)
                fc = [0] * n_test
                for p in wl:
                    fc[p] += 1
                print(f"  n={n_test} bins={list(bin_combo)}: fc={fc}, ms={ms_t}, fc==ms: {fc == ms_t}")


if __name__ == '__main__':
    main()
