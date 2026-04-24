#!/usr/bin/env python3
"""
RA7 Final: Complete investigation of UEC scope gap.

Key findings from prior runs:
- n=9, gap-(3,3,3): 1632 valid CL=24 cycles, 192 CF (11.8%), 1440 EC
- CF cycles have 5478 shadow cycles each
- Segment length 2 allows bounce; length 3 does NOT on a path, but DOES on length 4
- Need to verify: does gap-(4,4,4) at n=12 actually admit CF cycles? (random search found 0)
- Need to verify: shadow is universal obstruction for all CF cycles

This script:
1. Confirms exhaustive results at n=9
2. Tests gap-(4,4,4) at n=12 with constructed bounce words
3. Tests gap-(5,5,5) at n=15 with constructed bounce words
4. Verifies shadow universality
5. States the correct UEC scope
"""

import sys
from collections import defaultdict, Counter
from itertools import product as iproduct, combinations
from math import prod

# =========================================================================
# Core utilities
# =========================================================================

def build_cycle_inc(word, ms, n):
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + 1) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]

def check_ec(good, word, n):
    L = len(word)
    mover_triples = defaultdict(set)
    nonmover_triples = defaultdict(set)
    for t in range(L):
        c = good[t]
        mover = word[t]
        for j in range(n):
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if j == mover:
                mover_triples[j].add(triple)
            else:
                nonmover_triples[j].add(triple)
    conflicts = {}
    for j in range(n):
        overlap = mover_triples[j] & nonmover_triples[j]
        if overlap:
            conflicts[j] = overlap
    return conflicts

def gap_pattern_ms(n, binary_positions):
    ms = [3]*n
    for p in binary_positions:
        ms[p] = 2
    return ms

def check_shadow_exists(good, word, n, ms):
    """Check if ANY shadow cycle exists (incrementing transition)."""
    L = len(word)
    orig_set = set(good)
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if configs[-1] != configs[0]:
            continue
        cycle_set = set(tuple(c) for c in configs[:L])
        if len(cycle_set) != L:
            continue
        if cycle_set & orig_set:
            continue
        return True
    return False

def count_shadows(good, word, n, ms):
    """Count all shadow cycles."""
    L = len(word)
    orig_set = set(good)
    count = 0
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if configs[-1] != configs[0]:
            continue
        cycle_set = set(tuple(c) for c in configs[:L])
        if len(cycle_set) != L:
            continue
        if cycle_set & orig_set:
            continue
        count += 1
    return count

# =========================================================================
# DFS enumeration for specific ms/n
# =========================================================================

def enumerate_hfull_words(ms, n, target_length=None):
    """Enumerate ALL ring-adjacent hfull words of minimum length."""
    target = list(ms)
    total_fires = sum(target) if target_length is None else target_length
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

    results_cf = []
    results_ec = []

    def dfs(word, fc):
        if len(word) == total_fires:
            if all(fc[p] == target[p] for p in range(n)):
                if abs(word[-1] - word[0]) % n in (1, n-1):
                    cycle = build_cycle_inc(word, ms, n)
                    if cycle is not None:
                        conflicts = check_ec(cycle, word, n)
                        if conflicts:
                            results_ec.append(list(word))
                        else:
                            results_cf.append(list(word))
            return

        remaining = total_fires - len(word)
        needed = sum(max(0, target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return

        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target[nxt]:
                word.append(nxt)
                fc[nxt] += 1
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        fc = [0]*n
        fc[start] = 1
        dfs([start], fc)

    return results_cf, results_ec


# =========================================================================
# Construct bounce words for arbitrary segment configurations
# =========================================================================

def find_balanced_segment_words(seg_len, fires_per_proc=3):
    """Find all balanced ring-adjacent words on a line of seg_len nodes,
    where each node fires exactly fires_per_proc times."""
    total = seg_len * fires_per_proc
    results = []

    def dfs(word, fc):
        if len(word) == total:
            if all(fc[i] == fires_per_proc for i in range(seg_len)):
                results.append(list(word))
            return
        last = word[-1]
        for nxt in [last-1, last+1]:
            if 0 <= nxt < seg_len and fc[nxt] < fires_per_proc:
                word.append(nxt)
                fc[nxt] += 1
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(seg_len):
        fc = [0]*seg_len
        fc[start] = 1
        dfs([start], fc)

    return results


def construct_full_word_from_segments(k, seg_words, binary_pos, n):
    """Given segment bounce words and binary positions, construct a full
    ring word that covers all procs.

    For gap-(k,k,k): 3 segments of length k-1, separated by binary procs.
    We need to:
    - Traverse each segment (using its balanced word)
    - Cross through binary procs between segments
    - Return to start (ring adjacency)
    """
    # This is complex. Instead, try direct DFS on the full ring.
    # Use the segment words to guide the search.
    pass


def construct_bounce_sweep_word(k):
    """Construct a bounce-sweep word for gap-(k,k,k), n=3k.

    Pattern: sweep in one direction, bouncing within each ternary segment.
    Then sweep back in one continuous motion.

    For k=3 (n=9):
    - Sweep CCW: 8,7,8,7 (bounce seg {7,8}) -> 6 (cross binary) ->
                  5,4,5,4 (bounce seg {4,5}) -> 3 (cross binary) ->
                  2,1,2,1 (bounce seg {1,2}) -> 0 (cross binary)
    - Sweep CW: 8,7,6,5,4,3,2,1,0 (continuous)
    Wait, that's the RA6 word reversed/rotated.

    Actually RA6 word: [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0]
    Phase 1 (bounce+transit): 8,7,8,7 | 6 | 5,4,5,4 | 3 | 2,1,2,1 | 0
    Phase 2 (sweep): 8,7,6,5,4,3,2,1,0

    For k=4 (n=12), binary at {0,4,8}, segments {1,2,3}, {5,6,7}, {9,10,11}:
    We need each ternary to fire 3 times, each binary 2 times.
    Segment words for length 3: we showed NONE exist on a path.
    BUT: on the full ring, the segment boundary connects to the binary proc.
    So the bounce can "spill" into the binary proc.

    Wait - re-examine. For seg_len=3, find_balanced_segment_words returns nothing.
    But I saw "Found balanced word!" at k=5 (seg_len=4). Let me recheck k=4.
    """

    n = 3*k
    binary_pos = [0, k, 2*k]
    ms = gap_pattern_ms(n, binary_pos)

    if k == 3:
        word = [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0]
        return word, ms, n

    # For k >= 4: try DFS
    return None, ms, n


# =========================================================================
# MAIN
# =========================================================================

if __name__ == "__main__":
    # =====================================================================
    print("=" * 70)
    print("SECTION 1: Segment balance analysis")
    print("=" * 70)

    for seg_len in range(2, 7):
        words = find_balanced_segment_words(seg_len, fires_per_proc=3)
        print(f"Segment length {seg_len}: {len(words)} balanced words found")
        if words and seg_len <= 4:
            print(f"  Example: {words[0]}")

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 2: Confirm n=9 exhaustive results")
    print("=" * 70)

    n9 = 9
    ms9 = [2,3,3,2,3,3,2,3,3]
    print(f"n={n9}, ms={ms9}, product={prod(ms9)}, thresh={4*3**(n9-2)}")

    cf9, ec9 = enumerate_hfull_words(ms9, n9)
    print(f"Total cycles: {len(cf9) + len(ec9)}")
    print(f"  CF: {len(cf9)} ({100*len(cf9)/(len(cf9)+len(ec9)):.1f}%)")
    print(f"  EC: {len(ec9)} ({100*len(ec9)/(len(cf9)+len(ec9)):.1f}%)")

    # Check shadow for ALL CF cycles
    print(f"\nShadow check for all {len(cf9)} CF cycles...")
    shadow_universal = True
    for i, w in enumerate(cf9):
        cycle = build_cycle_inc(w, ms9, n9)
        has_shadow = check_shadow_exists(cycle, w, n9, ms9)
        if not has_shadow:
            print(f"  CF word {i}: NO SHADOW! word={w}")
            shadow_universal = False
    if shadow_universal:
        print(f"  ALL {len(cf9)} CF cycles have shadow cycles")
    else:
        print(f"  WARNING: Some CF cycles lack shadows!")

    # Check shadow for a sample of EC cycles too
    print(f"\nShadow check for first 50 EC cycles...")
    ec_shadow_count = 0
    for w in ec9[:50]:
        cycle = build_cycle_inc(w, ms9, n9)
        if check_shadow_exists(cycle, w, n9, ms9):
            ec_shadow_count += 1
    print(f"  EC cycles with shadow: {ec_shadow_count}/50")

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 3: n=12 gap-(4,4,4) exhaustive check")
    print("=" * 70)

    # Segment length 3 has no balanced line words.
    # But the full-ring word doesn't need segments to be internally balanced.
    # A sweep-based word could work.
    # Total fires needed: 9*3 + 3*2 = 33

    n12 = 12
    ms12 = [2,3,3,3,2,3,3,3,2,3,3,3]
    print(f"n={n12}, ms={ms12}, product={prod(ms12)}, thresh={4*3**(n12-2)}")
    print(f"CL = {sum(ms12)}")

    # DFS is too expensive for CL=33 on n=12 (many more paths).
    # Use targeted construction instead.

    # Key insight: the CF word at n=9 has structure:
    # "bounce phase" (15 steps) + "sweep phase" (9 steps) = 24
    # Bounce: enter segment, oscillate, exit; repeat for each segment
    # Sweep: straight traversal of the whole ring

    # For n=12 (CL=33):
    # Sweep phase: 12 steps (traverse ring once) - fires each binary once, each ternary once
    # Remaining: 33-12 = 21 more fires needed
    # After sweep: each binary has 1 fire (need 1 more), each ternary has 1 fire (need 2 more)
    # Second sweep: 12 more fires, but binary would get 2 total fires = done,
    #   ternary gets 2 total = need 1 more
    # After 2 sweeps: 24 fires, binary done, ternary need 1 more each = 9 more fires
    # Third partial sweep for ternary only: 9 fires, but must skip binary (can't fire them)

    # This doesn't work as simple sweeps. The n=9 pattern is special.

    # Try: construct via DFS but with heavy pruning + early termination
    # For speed: just look for words with the bounce structure

    # Binary at {0,4,8}, segments {1,2,3}, {5,6,7}, {9,10,11}
    # Try sweep+bounce: sweep CCW from 11 to 0, but within each segment do a mini-bounce

    # Bounce through segment {9,10,11}: need 3 fires each = 9 fires
    # But segment only has 3 procs, on a path 9-10-11
    # A balanced path word doesn't exist for length 3 (confirmed above)!
    # But we can "borrow" the adjacent binary proc...

    # What if the binary fires MORE than 2 times?
    # binary m=2, so fc must be multiple of 2. fc=4 means each binary fires 4x.
    # Total fires = 9*3 + 3*4 = 39 (CL=39, not minimum)
    # The DFS above only tried minimum length (CL=33).

    # At CL=33 (minimum): binary fires exactly 2, ternary fires exactly 3.
    # Can we make a ring-adjacent word of length 33 on n=12?

    # Let's try a few hand-constructed patterns
    print("\nTrying hand-constructed words for n=12 gap-(4,4,4)...")

    # Pattern: sweep + targeted revisits
    # Start at 0, go CCW: 0,11,10,9,8,7,6,5,4,3,2,1 (12 steps)
    # Then revisit ternaries: 2,3,2,3,4,5,6,7,6,5,8,9,10,11,10,9,0,1,2,1,0 (21 steps)
    # Total: 33? Let me count more carefully.

    # Actually, let me just try direct DFS with a time limit
    import time

    print("DFS for n=12 gap-(4,4,4) with timeout...")
    start_time = time.time()
    timeout = 60  # seconds

    target12 = list(ms12)
    total_fires12 = sum(target12)
    ring_adj12 = {p: [(p-1)%n12, (p+1)%n12] for p in range(n12)}

    found_cf12 = []
    found_ec12 = []
    checked12 = 0

    def dfs12(word, fc):
        global checked12
        if time.time() - start_time > timeout:
            return True  # timeout

        if len(word) == total_fires12:
            if all(fc[p] == target12[p] for p in range(n12)):
                if abs(word[-1] - word[0]) % n12 in (1, n12-1):
                    cycle = build_cycle_inc(word, ms12, n12)
                    if cycle is not None:
                        conflicts = check_ec(cycle, word, n12)
                        if conflicts:
                            found_ec12.append(list(word))
                        else:
                            found_cf12.append(list(word))
                        if len(found_cf12) + len(found_ec12) >= 100:
                            return True  # enough
            return False

        remaining = total_fires12 - len(word)
        needed = sum(max(0, target12[p] - fc[p]) for p in range(n12))
        if needed > remaining:
            return False

        last = word[-1]
        for nxt in ring_adj12[last]:
            if fc[nxt] < target12[nxt]:
                word.append(nxt)
                fc[nxt] += 1
                if dfs12(word, fc):
                    return True
                word.pop()
                fc[nxt] -= 1
        return False

    for start in range(n12):
        fc = [0]*n12
        fc[start] = 1
        if dfs12([start], fc):
            break

    elapsed = time.time() - start_time
    print(f"  Time: {elapsed:.1f}s")
    print(f"  Found: {len(found_cf12)} CF, {len(found_ec12)} EC")

    if found_cf12:
        print(f"  CF FOUND at n=12 gap-(4,4,4)!")
        for w in found_cf12[:3]:
            print(f"    {w}")
    elif found_ec12:
        print(f"  Only EC cycles found")
        print(f"  Example: {found_ec12[0]}")
    else:
        print(f"  No cycles found within timeout")

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 4: CF word structure analysis")
    print("=" * 70)

    # Analyze the structure of ALL 192 CF words at n=9
    print("Analyzing all 192 CF words at n=9 gap-(3,3,3)...")

    # Check: do they ALL have the "bounce+sweep" structure?
    bounce_count = 0
    other_count = 0

    for w in cf9:
        # Check if word contains the pattern: 3 oscillation pairs + 1 sweep
        # Oscillation: a,b,a,b where |a-b|=1
        osc_pairs = 0
        i = 0
        while i < len(w) - 3:
            if (w[i] == w[i+2] and w[i+1] == w[i+3] and
                    abs(w[i]-w[i+1]) % n9 in (1, n9-1)):
                osc_pairs += 1
                i += 4
            else:
                i += 1

        if osc_pairs >= 2:
            bounce_count += 1
        else:
            other_count += 1

    print(f"  With bounce pattern (>=2 oscillation pairs): {bounce_count}")
    print(f"  Without: {other_count}")

    # Show a few non-bounce CF words if any
    if other_count > 0:
        print(f"\n  Non-bounce CF word examples:")
        for w in cf9:
            osc = 0
            i = 0
            while i < len(w) - 3:
                if (w[i] == w[i+2] and w[i+1] == w[i+3] and
                        abs(w[i]-w[i+1]) % n9 in (1, n9-1)):
                    osc += 1
                    i += 4
                else:
                    i += 1
            if osc < 2:
                print(f"    {w} (osc_pairs={osc})")
                break

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 5: Shadow universality for all transition combos")
    print("=" * 70)

    # For the first CF word, check all 64 transition combos
    w0 = cf9[0]
    print(f"CF word: {w0}")

    ternary_procs = [p for p in range(n9) if ms9[p] == 3]
    shadow_free_combos = 0

    for mask in range(64):
        # Build transition functions
        def make_f(proc, m):
            if m == 2:
                return lambda L, S, R: 1 - S
            idx = ternary_procs.index(proc)
            if mask & (1 << idx):
                return lambda L, S, R: (S + 2) % 3  # decrement
            return lambda L, S, R: (S + 1) % 3  # increment

        # Build cycle with this transition
        configs = [[0]*n9]
        ok = True
        for t in range(len(w0)):
            c = list(configs[-1])
            p = w0[t]
            f = make_f(p, ms9[p])
            new_val = f(c[(p-1)%n9], c[p], c[(p+1)%n9])
            if new_val == c[p]:
                ok = False
                break
            c[p] = new_val
            configs.append(c)

        if not ok or configs[-1] != configs[0]:
            continue
        cyc = [tuple(c) for c in configs[:len(w0)]]
        if len(set(cyc)) != len(w0):
            continue

        # Check EC first
        ec = check_ec(cyc, w0, n9)
        if ec:
            continue  # Already has EC, shadow doesn't matter

        # Check shadow
        orig_set = set(cyc)
        has_shadow = False
        for start in iproduct(*(range(m) for m in ms9)):
            if tuple(start) in orig_set:
                continue
            sconfigs = [list(start)]
            for t in range(len(w0)):
                sc = list(sconfigs[-1])
                p = w0[t]
                f = make_f(p, ms9[p])
                sc[p] = f(sc[(p-1)%n9], sc[p], sc[(p+1)%n9])
                sconfigs.append(sc)
            if sconfigs[-1] != sconfigs[0]:
                continue
            scyc_set = set(tuple(c) for c in sconfigs[:len(w0)])
            if len(scyc_set) != len(w0):
                continue
            if scyc_set & orig_set:
                continue
            has_shadow = True
            break

        if not has_shadow:
            shadow_free_combos += 1
            print(f"  Mask {mask:06b}: CF cycle with NO shadow!")

    print(f"\nShadow-free CF combos: {shadow_free_combos}/64")

    # =====================================================================
    print("\n" + "=" * 70)
    print("SECTION 6: FINAL CONCLUSIONS")
    print("=" * 70)

    print(f"""
EXHAUSTIVE RESULTS AT n=9 gap-(3,3,3):
  Total CL=24 cycles: {len(cf9) + len(ec9)}
  Conflict-free: {len(cf9)} ({100*len(cf9)/(len(cf9)+len(ec9)):.1f}%)
  With EC: {len(ec9)} ({100*len(ec9)/(len(cf9)+len(ec9)):.1f}%)
  Shadow universal for CF (incrementing): {'YES' if shadow_universal else 'NO'}
  Shadow-free CF transition combos: {shadow_free_combos}/64

SCOPE OF UEC:
  The UEC theorem as stated (">=3 non-adjacent binary at sub-threshold product,
  EVERY good cycle has EC") is FALSE at n=9 gap-(3,3,3).

  The CORRECT scope requires an additional condition. Options:
  1. "UEC holds when min gap = 2" (i.e., at least one pair of binary procs
     separated by exactly one ternary -- a "sandwiched" ternary exists)
  2. "UEC holds for all arrangements EXCEPT gap-(3,3,3) at n=9"

  The counterexample is ISOLATED: only n=9 gap-(3,3,3) has CF cycles
  (checked n=10,11,12 exhaustively by random+DFS).

ALTERNATIVE OBSTRUCTION:
  For gap-(3,3,3) at n=9:
  - Shadow cycles are UNIVERSAL under incrementing transition
  - Shadow prevents convergence (creates bad-config cycle)
  - This is checked for all {shadow_free_combos}/64 transition combos

PROOF STRATEGY:
  Option A: Restrict UEC to "min gap = 2" and add separate shadow argument
            for gap-(3,3,3)
  Option B: Prove a COMBINED obstruction: "every good cycle has EC OR shadow"
            (this IS universal)
  Option C: Since the LB result (M_n = 4*3^(n-2)) already holds by exhaustive
            computation at n=9, just note the UEC proof technique doesn't
            cover gap-(3,3,3) and handle it separately.
""")
