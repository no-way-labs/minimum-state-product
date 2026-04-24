#!/usr/bin/env python3
"""
RA13 Q2: For no-EC cycles at n=9, does GlobalObstruction (shadow) hold?

The bounce-sweep word at n=9 (gap-333) produces 64 no-EC cycles under
all transition combos. Check:
1. Does each have a shadow cycle (disjoint companion)?
2. If shadow exists under incrementing: does the shadow cycle MIRROR
   theorem apply?
3. Is the shadow cycle disjoint from the good cycle's configs?
"""

from collections import defaultdict, Counter
from itertools import product as iproduct
from math import prod

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


def build_cycle_trans(word, ms, n, trans_mode):
    L = len(word)
    configs = [[0]*n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans_mode[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return [tuple(c) for c in configs[:L]]


def count_shadows_inc(good, word, n, ms):
    """Count shadow cycles under incrementing transition."""
    L = len(word)
    orig_set = set(good)
    found = []
    visited = set()
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in orig_set or tuple(start) in visited:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if tuple(configs[-1]) != tuple(configs[0]):
            continue
        cycle_set = set(tuple(c) for c in configs[:L])
        if len(cycle_set) != L:
            continue
        if cycle_set & orig_set:
            continue
        found.append(cycle_set)
        visited |= cycle_set
    return found


def count_all_cycles_inc(word, n, ms):
    """Count ALL cycles (including the good one) under incrementing."""
    L = len(word)
    product_val = prod(ms)
    visited = set()
    cycles = []
    for start in iproduct(*(range(m) for m in ms)):
        if tuple(start) in visited:
            continue
        configs = [list(start)]
        for t in range(L):
            c = list(configs[-1])
            p = word[t]
            c[p] = (c[p] + 1) % ms[p]
            configs.append(c)
        if tuple(configs[-1]) != tuple(configs[0]):
            continue
        cycle_set = set(tuple(c) for c in configs[:L])
        if len(cycle_set) == L:
            cycles.append(cycle_set)
            visited |= cycle_set
    return cycles


def find_balanced_segment_words(seg_len, target=2):
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


if __name__ == "__main__":
    n = 9
    k = 3
    bp = [0, 3, 6]
    ms = [2, 3, 3, 2, 3, 3, 2, 3, 3]
    product_val = prod(ms)
    threshold = 4 * 3**(n-2)

    print(f"n={n}, bp={bp}, ms={ms}")
    print(f"Product={product_val}, threshold={threshold}, sub={product_val < threshold}")

    # Build the bounce-sweep word
    seg_words = find_balanced_segment_words(k-1, target=2)
    seg_A = list(range(n-1, 2*k, -1))
    seg_B = list(range(2*k-1, k, -1))
    seg_C = list(range(k-1, 0, -1))

    sw = seg_words[0]
    bounce_A = [seg_A[i] for i in sw]
    bounce_B = [seg_B[i] for i in sw]
    bounce_C = [seg_C[i] for i in sw]

    word = []
    word.extend(bounce_A)
    word.append(2*k)
    word.extend(bounce_B)
    word.append(k)
    word.extend(bounce_C)
    word.append(0)
    word.extend(list(range(n-1, -1, -1)))

    print(f"\nBounce-sweep word: {word}")
    print(f"CL = {len(word)}")

    # Test with all-inc
    trans_inc = [1]*n
    cyc_inc = build_cycle_trans(word, ms, n, trans_inc)
    if cyc_inc:
        ec = check_ec(cyc_inc, word, n)
        print(f"\nAll-inc: EC = {bool(ec)}, CL = {len(cyc_inc)}")

        # Count ALL cycles under this word + incrementing
        print(f"\nCounting all cycles under incrementing...")
        all_cycles = count_all_cycles_inc(word, n, ms)
        print(f"Total distinct CL-{len(word)} cycles: {len(all_cycles)}")
        total_covered = sum(len(c) for c in all_cycles)
        print(f"Total configs in cycles: {total_covered} / {product_val}")
        print(f"Coverage: {100*total_covered/product_val:.1f}%")

        # How many are disjoint from the good cycle?
        good_set = set(cyc_inc)
        shadows = [c for c in all_cycles if not (c & good_set)]
        print(f"Shadow cycles (disjoint from good): {len(shadows)}")
        shadow_configs = sum(len(c) for c in shadows)
        print(f"Shadow configs: {shadow_configs}")
        print(f"Good + shadow: {len(good_set) + shadow_configs}")

        if shadows:
            print(f"\n*** SHADOW EXISTS for all-inc ***")
            print("This cycle has Mode B obstruction (GlobalObstruction)")
        else:
            print(f"\n*** NO SHADOW for all-inc ***")

    # Test all 64 ternary transition combos
    print(f"\n{'='*60}")
    print("Testing all 64 ternary transition combos")
    print(f"{'='*60}")

    ternary_procs = [1, 2, 4, 5, 7, 8]
    n_ec = 0
    n_noec = 0
    n_noec_shadow = 0
    n_noec_noshadow = 0
    noec_noshadow_details = []

    for combo in iproduct([1, -1], repeat=6):
        trans = [1]*n
        for idx, tp in enumerate(ternary_procs):
            trans[tp] = combo[idx]

        cyc = build_cycle_trans(word, ms, n, trans)
        if cyc is None:
            continue

        ec = check_ec(cyc, word, n)
        if ec:
            n_ec += 1
            continue

        n_noec += 1

        # Check shadow under INCREMENTING (standard shadow check)
        shadows = count_shadows_inc(cyc, word, n, ms)
        if shadows:
            n_noec_shadow += 1
        else:
            n_noec_noshadow += 1
            noec_noshadow_details.append((combo, cyc))

    print(f"\nTotal valid cycles: {n_ec + n_noec}")
    print(f"With EC (Mode A): {n_ec}")
    print(f"Without EC: {n_noec}")
    print(f"  With shadow (Mode B): {n_noec_shadow}")
    print(f"  Without shadow: {n_noec_noshadow}")

    if n_noec_noshadow == 0 and n_noec > 0:
        print(f"\n*** EC ∨ SHADOW HOLDS at n=9 for bounce-sweep word ***")
        print("Every no-EC cycle has a shadow companion!")
        print("=> Mode A ∨ Mode B is TRUE for this word family")
    elif n_noec_noshadow > 0:
        print(f"\n*** EC ∨ SHADOW FAILS at n=9 ***")
        print(f"{n_noec_noshadow} cycles have neither EC nor shadow")
        for combo, cyc in noec_noshadow_details[:3]:
            print(f"  trans combo (ternary): {combo}")

    # Also check the second bounce-sweep word
    if len(seg_words) > 1:
        print(f"\n{'='*60}")
        print("Second bounce-sweep word variant")
        print(f"{'='*60}")

        sw2 = seg_words[1]
        bounce_A2 = [seg_A[i] for i in sw2]
        bounce_B2 = [seg_B[i] for i in sw2]
        bounce_C2 = [seg_C[i] for i in sw2]

        word2 = []
        word2.extend(bounce_A2)
        word2.append(2*k)
        word2.extend(bounce_B2)
        word2.append(k)
        word2.extend(bounce_C2)
        word2.append(0)
        word2.extend(list(range(n-1, -1, -1)))

        print(f"Word 2: {word2}")

        n_ec2 = 0
        n_noec2_shadow = 0
        n_noec2_noshadow = 0

        for combo in iproduct([1, -1], repeat=6):
            trans = [1]*n
            for idx, tp in enumerate(ternary_procs):
                trans[tp] = combo[idx]
            cyc = build_cycle_trans(word2, ms, n, trans)
            if cyc is None:
                continue
            ec = check_ec(cyc, word2, n)
            if ec:
                n_ec2 += 1
                continue
            shadows = count_shadows_inc(cyc, word2, n, ms)
            if shadows:
                n_noec2_shadow += 1
            else:
                n_noec2_noshadow += 1

        print(f"EC: {n_ec2}, no-EC+shadow: {n_noec2_shadow}, "
              f"no-EC+no-shadow: {n_noec2_noshadow}")
