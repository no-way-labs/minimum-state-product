#!/usr/bin/env python3
"""binscc_conflict_sharp.py — Find the sharpest conflict mechanism.

Strategy: analyze conflict-free cycles that WOULD exist if no conflict held.
Find what structural property prevents them.

KEY INSIGHT: For binary b with ternary neighbor t:
t fires 3 times → b sees ALL 3 values of t as nonmover.
One of those values = b's mover R-value.
For no conflict: at that step, b's state or other neighbor must differ.

With 3 non-adjacent binary: the constraints from multiple ternary procs interact.
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys
import time


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def main():
    print("=" * 70)
    print("SHARP CONFLICT MECHANISM")
    print("=" * 70)

    n, ms = 5, [2, 3, 2, 3, 2]
    bin_procs = [0, 2, 4]

    # PART 1: For each binary proc, track ternary neighbor firing overlap
    print("\nPART 1: TERNARY FIRING → BINARY NONMOVER CONTEXT MATCH")
    print("=" * 60)
    print()
    print("When ternary t (right neighbor of binary b) fires from state s:")
    print("  b is nonmover, sees R=s at that step.")
    print("  If b's mover also has R=s: conflict iff (L, S) also match.")
    print()

    words = enumerate_mover_words(ms, n, 16)  # shorter for speed
    print(f"  {len(words)} mover words (max_len=16)")

    total = 0
    # For each binary: track when ternary neighbor fires and it matches mover R
    ternary_match_conflict = Counter()

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        total += 1
        ell = len(cycle)

        for b in bin_procs:
            mL = (b - 1) % n
            mR = (b + 1) % n  # ternary right neighbor

            # Find b's mover steps and their contexts
            up_ctx = down_ctx = None
            for step in range(ell):
                if word[step] == b:
                    c = cycle[step]
                    L, S, R = c[mL], c[b], c[mR]
                    if S == 0:
                        up_ctx = (L, 0, R)
                    else:
                        down_ctx = (L, 1, R)

            if up_ctx is None or down_ctx is None:
                continue

            # Find steps where mR (ternary) fires
            for step in range(ell):
                if word[step] == mR:
                    c = cycle[step]
                    R_val = c[mR]  # ternary's state before firing
                    b_state = c[b]
                    L_val = c[mL]
                    nm_ctx = (L_val, b_state, R_val)

                    if nm_ctx == up_ctx or nm_ctx == down_ctx:
                        ternary_match_conflict[(b, 'direct')] += 1

            # Find steps where mL fires (affects L side)
            for step in range(ell):
                if word[step] == mL:
                    c = cycle[step]
                    L_val = c[mL]
                    b_state = c[b]
                    R_val = c[mR]
                    nm_ctx = (L_val, b_state, R_val)

                    if nm_ctx == up_ctx or nm_ctx == down_ctx:
                        ternary_match_conflict[(b, 'L-side')] += 1

    print(f"  Total valid: {total}")
    print(f"  Ternary-firing conflict: {dict(ternary_match_conflict)}")

    # PART 2: Minimal length cycles only
    print(f"\n\n{'='*70}")
    print("PART 2: MINIMAL LENGTH CYCLES (ℓ=12)")
    print("=" * 70)

    words_all = enumerate_mover_words(ms, n, 21)
    min_len = sum(ms)  # = 12

    min_total = 0
    min_conflict = 0
    min_no_conflict = 0

    for word in words_all:
        if len(word) != min_len:
            continue
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        min_total += 1

        has_conflict = False
        for p in range(n):
            mL = (p - 1) % n
            mR = (p + 1) % n
            mover_set = set()
            nonmover_set = set()
            for step in range(len(cycle)):
                c = cycle[step]
                ctx = (c[mL], c[p], c[mR])
                if word[step] == p:
                    mover_set.add(ctx)
                else:
                    nonmover_set.add(ctx)
            if mover_set & nonmover_set:
                has_conflict = True
                break

        if has_conflict:
            min_conflict += 1
        else:
            min_no_conflict += 1

    print(f"  ℓ={min_len}: {min_total} valid, {min_conflict} conflict, {min_no_conflict} no-conflict")

    # Also check ℓ=14, 15, 16
    for target_len in range(min_len + 1, min_len + 10):
        tc = 0
        cc = 0
        for word in words_all:
            if len(word) != target_len:
                continue
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            tc += 1
            for p in range(n):
                mL = (p - 1) % n; mR = (p + 1) % n
                ms_set = set(); nms_set = set()
                for step in range(len(cycle)):
                    c = cycle[step]
                    ctx = (c[mL], c[p], c[mR])
                    if word[step] == p: ms_set.add(ctx)
                    else: nms_set.add(ctx)
                if ms_set & nms_set:
                    cc += 1
                    break
        if tc > 0:
            print(f"  ℓ={target_len}: {tc} valid, {cc} conflict ({100*cc/tc:.1f}%)")

    # PART 3: The exact avoidance condition
    print(f"\n\n{'='*70}")
    print("PART 3: WHAT MAKES CONFLICT UNAVOIDABLE")
    print("=" * 70)
    print()
    print("For each binary b in a conflicting cycle:")
    print("  Find the SPECIFIC mechanism (which proc's firing creates the overlap)")
    print()

    # For first 20 minimal cycles, detail the conflict mechanism
    count = 0
    mechanism_counter = Counter()

    for word in words_all:
        if len(word) != min_len:
            continue
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue

        ell = len(cycle)

        for p in range(n):
            mL = (p - 1) % n; mR = (p + 1) % n
            mover_steps = {}
            nonmover_steps = defaultdict(list)

            for step in range(ell):
                c = cycle[step]
                ctx = (c[mL], c[p], c[mR])
                if word[step] == p:
                    mover_steps[step] = ctx
                else:
                    nonmover_steps[ctx].append(step)

            for m_step, m_ctx in mover_steps.items():
                if m_ctx in nonmover_steps:
                    # Who fired at the nonmover step?
                    for nm_step in nonmover_steps[m_ctx]:
                        firer = word[nm_step]
                        rel = 'L-neighbor' if firer == mL else ('R-neighbor' if firer == mR else f'P{firer}')
                        mechanism_counter[(f'P{p}', rel)] += 1

        count += 1

    print(f"  Analyzed {count} minimal cycles")
    print(f"  Conflict mechanisms (conflicting proc, firer at nonmover step):")
    for k, v in sorted(mechanism_counter.items(), key=lambda x: -x[1]):
        print(f"    {k}: {v}")

    # PART 4: The (bL, bR) pair at each ternary firing — correlation analysis
    print(f"\n\n{'='*70}")
    print("PART 4: STATE CORRELATION AT TERNARY FIRING STEPS")
    print("=" * 70)
    print()

    # For binary b0=P0 with right ternary P1:
    # When P1 fires from state s, what are P0's state and P4's state?
    b, tR = 0, 1
    mL = 4
    state_at_ternary = defaultdict(Counter)

    for word in words_all:
        if len(word) != min_len:
            continue
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        for step in range(ell):
            if word[step] == tR:
                c = cycle[step]
                tR_state = c[tR]
                b_state = c[b]
                mL_state = c[mL]
                state_at_ternary[tR_state][(b_state, mL_state)] += 1

    print(f"  P0 with right-ternary P1:")
    print(f"  When P1 fires from state s, (P0_state, P4_state) distribution:")
    for s in sorted(state_at_ternary):
        print(f"    P1 fires from s={s}: {dict(sorted(state_at_ternary[s].items()))}")

    # PART 5: Check non-consecutive binary at n=6 (exhaustive min-length)
    print(f"\n\n{'='*70}")
    print("PART 5: n=6 ALTERNATING — MINIMAL CYCLES")
    print("=" * 70)

    n6, ms6 = 6, [2, 3, 2, 3, 2, 3]
    min_len6 = sum(ms6)  # 15
    words6 = enumerate_mover_words(ms6, n6, min_len6)
    print(f"  {len(words6)} mover words at ℓ={min_len6}")

    tc6 = 0; cc6 = 0
    for word in words6:
        cycle = build_cycle(ms6, n6, word)
        if cycle is None:
            continue
        tc6 += 1
        for p in range(n6):
            mL = (p-1) % n6; mR = (p+1) % n6
            ms_s = set(); nms_s = set()
            for step in range(len(cycle)):
                c = cycle[step]
                ctx = (c[mL], c[p], c[mR])
                if word[step] == p: ms_s.add(ctx)
                else: nms_s.add(ctx)
            if ms_s & nms_s:
                cc6 += 1
                break
    print(f"  ℓ={min_len6}: {tc6} valid, {cc6} conflict ({100*cc6/tc6:.1f}%)" if tc6 > 0 else "  No valid cycles")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
