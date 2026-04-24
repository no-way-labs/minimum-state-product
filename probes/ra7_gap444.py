#!/usr/bin/env python3
"""
RA7 Gap-(4,4,4) and Gap-(5,5,5): Can balanced segments enable CF cycles?

Key insight from segment analysis:
- Segment length 2: balanced (bounce a,b,a,b,a,b) -- enables CF at n=9
- Segment length 3: NO balanced words
- Segment length 4: balanced words EXIST (0,1,0,1,0,1,2,3,2,3,2,3)
- Segment length 5: NO balanced words
- Segment length 6: balanced words EXIST

Pattern: even segment lengths have balanced words, odd don't.
Gap-(k,k,k): segment length = k-1. So k=3 (seg 2), k=5 (seg 4), k=7 (seg 6) work.

This means:
- n=9,  gap-(3,3,3): seg 2, balanced -- CF CONFIRMED
- n=12, gap-(4,4,4): seg 3, NOT balanced -- likely no CF
- n=15, gap-(5,5,5): seg 4, balanced -- CF POSSIBLE
- n=18, gap-(6,6,6): seg 5, NOT balanced
- n=21, gap-(7,7,7): seg 6, balanced -- CF POSSIBLE

Must test n=15 gap-(5,5,5) with a constructed bounce word.
"""

import sys
import time
from collections import defaultdict, Counter
from itertools import product as iproduct
from math import prod

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


def find_balanced_segment_words(seg_len, target=3):
    """Find balanced ring-adjacent words on a LINE of seg_len nodes."""
    total = seg_len * target
    results = []
    def dfs(word, fc):
        if len(word) == total:
            if all(fc[i] == target for i in range(seg_len)):
                results.append(list(word))
            return
        last = word[-1]
        for nxt in [last-1, last+1]:
            if 0 <= nxt < seg_len and fc[nxt] < target:
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


def construct_bounce_sweep(k):
    """Construct a bounce-sweep word for gap-(k,k,k), n=3k.

    For k=3 (n=9): known pattern works.
    For k=5 (n=15): seg_len=4, balanced words exist.

    Structure:
    - Phase 1: bounce through segment 1, cross binary, bounce segment 2,
               cross binary, bounce segment 3, cross binary (this fires
               each ternary 3x, each binary 1x)
    - Phase 2: sweep the entire ring (fires each proc 1x more:
               ternary gets 4th fire = bad, binary gets 2nd = done)

    Wait, for the sweep phase at n=9 the word is 9 steps, giving one fire each.
    At n=9: bounce phase = 6+1+6+1+6+1 = 21 fires? No.
    Let me re-analyze the n=9 pattern.

    n=9 word: [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0]
    Fires: 8:3, 7:3, 6:2, 5:3, 4:3, 3:2, 2:3, 1:3, 0:2
    This is already complete! Each ternary fires 3x, each binary fires 2x.

    The structure is:
    - Bounce {8,7}: 8,7,8,7 (4 steps: 8 fires 2x, 7 fires 2x)
    - Cross 6: 6 (1 step: 6 fires 1x)
    - Bounce {5,4}: 5,4,5,4 (4 steps: 5 fires 2x, 4 fires 2x)
    - Cross 3: 3 (1 step: 3 fires 1x)
    - Bounce {2,1}: 2,1,2,1 (4 steps: 2 fires 2x, 1 fires 2x)
    - Cross 0: 0 (1 step: 0 fires 1x)
    - Sweep: 8,7,6,5,4,3,2,1,0 (9 steps: each fires 1x more)

    After bounce+cross: ternary 2x each, binary 1x each
    After sweep: ternary 3x each, binary 2x each. Done!

    For k=5 (n=15):
    Binary at {0,5,10}, segments {1,2,3,4}, {6,7,8,9}, {11,12,13,14}
    Segment length 4, balanced words exist: e.g., [0,1,0,1,0,1,2,3,2,3,2,3]

    But this balanced word fires each of the 4 segment procs 3 times = 12 steps/segment.
    We need each ternary to fire 3 times total. If we use the segment word in the
    bounce phase, each fires 3x, then the sweep adds 1x more = 4x total. Too many!

    So for longer segments, we can't do "full bounce + sweep".
    Instead: "partial bounce" (fire each ternary 2x) + "sweep" (fire each 1x more).

    Partial balanced word for segment length 4, target=2:
    Total = 4*2 = 8 steps on a line of 4 nodes, each fires 2x.
    """
    n = 3*k
    binary_pos = [0, k, 2*k]
    ms = gap_pattern_ms(n, binary_pos)

    if k == 3:
        return [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0], ms, n

    seg_len = k - 1
    # We need partial bounce words: each proc fires 2x in the segment
    partial_words = find_balanced_segment_words(seg_len, target=2)
    if not partial_words:
        print(f"  No partial (target=2) balanced words for seg_len={seg_len}")
        return None, ms, n

    # Take first partial word and map to actual proc positions
    seg_word = partial_words[0]

    # Segments: {2k+1,...,3k-1}, {k+1,...,2k-1}, {1,...,k-1}
    # Going CCW from binary 0: we hit segment {n-1,...,2k+1} first
    # Actually let's go CCW: 0 -> n-1 -> n-2 -> ...
    # Segment between binary 2k and 0: procs {2k+1, 2k+2, ..., 3k-1} = {2k+1,...,n-1}
    # Wait, going CCW from 0: 0 -> n-1 -> n-2 -> ... -> 2k+1 -> 2k (binary)
    # That's segment {n-1, n-2, ..., 2k+1}, which is {2k+1,...,n-1} reversed

    # Segments in CCW order from binary 0:
    # Seg A: {n-1, n-2, ..., 2k+1} (between binary 2k and 0, going CCW)
    # Binary 2k
    # Seg B: {2k-1, 2k-2, ..., k+1} (between binary k and 2k, going CCW)
    # Binary k
    # Seg C: {k-1, k-2, ..., 1} (between binary 0 and k, going CCW)
    # Binary 0

    seg_A = list(range(n-1, 2*k, -1))  # [n-1, n-2, ..., 2k+1]
    seg_B = list(range(2*k-1, k, -1))  # [2k-1, 2k-2, ..., k+1]
    seg_C = list(range(k-1, 0, -1))    # [k-1, k-2, ..., 1]

    print(f"  k={k}, n={n}")
    print(f"  Seg A: {seg_A}")
    print(f"  Seg B: {seg_B}")
    print(f"  Seg C: {seg_C}")

    # Map segment word to actual positions
    # seg_word is on {0,1,...,seg_len-1}
    # Map 0 -> seg[0], 1 -> seg[1], etc.
    def map_seg(seg_word_local, seg):
        return [seg[i] for i in seg_word_local]

    bounce_A = map_seg(seg_word, seg_A)
    bounce_B = map_seg(seg_word, seg_B)
    bounce_C = map_seg(seg_word, seg_C)

    # Build word: bounce A, cross 2k, bounce B, cross k, bounce C, cross 0, sweep
    word = []
    word.extend(bounce_A)   # each in seg_A fires 2x
    word.append(2*k)        # binary 2k fires 1x
    word.extend(bounce_B)   # each in seg_B fires 2x
    word.append(k)          # binary k fires 1x
    word.extend(bounce_C)   # each in seg_C fires 2x
    word.append(0)          # binary 0 fires 1x

    # Now sweep: need each ternary to fire 1 more time, each binary 1 more time
    # Sweep CCW: n-1, n-2, ..., 1, 0
    sweep = list(range(n-1, -1, -1))
    word.extend(sweep)

    # Check: total fires
    fc = Counter(word)
    total = len(word)
    expected = sum(ms)

    print(f"  Word length: {total}, expected CL: {expected}")
    print(f"  Firing counts: {dict(sorted(fc.items()))}")
    print(f"  Expected: ternary=3, binary=2")

    ok = all(fc[p] == ms[p] for p in range(n))
    print(f"  Correct firing counts: {ok}")

    if not ok:
        # Fix: the bounce gives 2 fires per ternary, cross gives 1 per binary,
        # sweep gives 1 per everyone. So ternary = 3, binary = 2. Should work.
        # But wait: the bounce word might start/end at positions that aren't
        # adjacent to the binary proc.
        print(f"  DEBUG: bounce_A starts at {bounce_A[0]}, ends at {bounce_A[-1]}")
        print(f"  Need bounce_A to end adjacent to binary {2*k}")
        print(f"  Binary {2*k} neighbors: {(2*k-1)%n}, {(2*k+1)%n}")

        # The issue: the segment word might not start/end at the segment endpoint
        # adjacent to the next binary. Let me check adjacency.
        if abs(bounce_A[-1] - 2*k) % n not in (1, n-1):
            print(f"  Bounce A end {bounce_A[-1]} NOT adjacent to binary {2*k}!")
            # Need a different segment word or ordering

        return None, ms, n

    # Check ring adjacency
    all_adj = True
    for i in range(len(word)):
        diff = abs(word[i] - word[(i+1)%len(word)])
        if diff != 1 and diff != n-1:
            all_adj = False
            print(f"  NOT ring-adjacent at step {i}: {word[i]} -> {word[(i+1)%len(word)]}")
            break

    if not all_adj:
        return None, ms, n

    print(f"  Ring-adjacent: YES")

    # Try to build cycle
    cycle = build_cycle_inc(word, ms, n)
    if cycle is None:
        print(f"  Cycle build FAILED (doesn't close or not distinct)")
        return None, ms, n

    ec = check_ec(cycle, word, n)
    print(f"  EC: {bool(ec)}")
    if not ec:
        print(f"  *** CONFLICT-FREE CYCLE FOUND at n={n} gap-({k},{k},{k})! ***")

    return word, ms, n


if __name__ == "__main__":
    # First check: segment balance with target=2
    print("=" * 70)
    print("Segment balance with target=2 fires per proc")
    print("=" * 70)
    for seg_len in range(2, 8):
        words = find_balanced_segment_words(seg_len, target=2)
        print(f"  Seg len {seg_len}: {len(words)} balanced words (target=2)")
        if words:
            print(f"    Example: {words[0]}")
            # Show start/end positions
            w = words[0]
            print(f"    Start: {w[0]}, End: {w[-1]}")

    print()

    # Test constructions
    for k in [3, 5, 7]:
        print(f"\n{'='*70}")
        print(f"Testing gap-({k},{k},{k}), n={3*k}")
        print(f"{'='*70}")
        word, ms, n = construct_bounce_sweep(k)
        if word is not None:
            print(f"  WORD: {word}")

    # If construction fails, try DFS for n=15 gap-(5,5,5)
    print(f"\n{'='*70}")
    print(f"DFS search for n=15 gap-(5,5,5)")
    print(f"{'='*70}")

    n = 15
    ms = gap_pattern_ms(n, [0, 5, 10])
    target = list(ms)
    total_fires = sum(target)
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

    print(f"n={n}, ms={ms}, CL={total_fires}")
    print(f"Product: {prod(ms)}, threshold: {4*3**(n-2)}")

    found_cf = []
    found_ec = []
    start_time = time.time()
    timeout = 120

    def dfs15(word, fc):
        if time.time() - start_time > timeout:
            return True
        if len(word) == total_fires:
            if all(fc[p] == target[p] for p in range(n)):
                if abs(word[-1] - word[0]) % n in (1, n-1):
                    cycle = build_cycle_inc(word, ms, n)
                    if cycle is not None:
                        conflicts = check_ec(cycle, word, n)
                        if conflicts:
                            found_ec.append(list(word))
                        else:
                            found_cf.append(list(word))
                        return len(found_cf) + len(found_ec) >= 50
            return False
        remaining = total_fires - len(word)
        needed = sum(max(0, target[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return False
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < target[nxt]:
                word.append(nxt)
                fc[nxt] += 1
                if dfs15(word, fc):
                    return True
                word.pop()
                fc[nxt] -= 1
        return False

    for start in range(n):
        fc = [0]*n
        fc[start] = 1
        if dfs15([start], fc):
            break
        if time.time() - start_time > timeout:
            break

    elapsed = time.time() - start_time
    print(f"Time: {elapsed:.1f}s")
    print(f"Found: {len(found_cf)} CF, {len(found_ec)} EC")
    if found_cf:
        print(f"CF word: {found_cf[0]}")
    elif found_ec:
        print(f"EC word example: {found_ec[0]}")
