#!/usr/bin/env python3
"""
RA12: Analyze the 512 EC-free exceptions for (3,3,3) placement at n=9.
Understand their structure and check if they can form valid systems.

Key question: does the ABSENCE of entry conflict mean a valid system EXISTS?
No -- entry conflict is sufficient but not necessary for blocking.
There might be other obstructions (shadow cycles, overlap, etc.).
But entry conflict universality is what we're testing.
"""

from itertools import product as iproduct
from collections import Counter
import time


def make_ms(n, binary_positions):
    ms = [3] * n
    for b in binary_positions:
        ms[b] = 2
    return ms


def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def enumerate_walks(n, ms):
    """Enumerate all min-length ring walks where fc[p] = ms[p]."""
    total_len = sum(ms)
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == total_len:
            nxt = path[0]
            if abs(pos - nxt) % n in (1, n - 1):
                if all(fc[p] == ms[p] for p in range(n)):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    for p0 in range(n):
        fc = [0] * n
        fc[p0] = 1
        dfs([p0], fc)
    # Deduplicate under rotation
    unique = set()
    result = []
    for w in walks:
        ell = len(w)
        best = w
        for i in range(ell):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(w)
    return result


def check_ec_detailed(word, n, ms, combo):
    """Check EC for a specific (word, state-seq combo).
    Returns list of (proc, overlapping_contexts)."""
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0]:
        return None  # not valid
    if len(set(configs[:L])) != L:
        return None  # not distinct

    good = configs[:L]
    ec_details = []
    for j in range(n):
        Lp = (j - 1) % n
        Rp = (j + 1) % n
        mover_ctxs = {}
        nonmover_ctxs = set()
        for t in range(L):
            ctx = (good[t][Lp], good[t][j], good[t][Rp])
            if word[t] == j:
                next_val = good[(t + 1) % L][j]
                if next_val != ctx[1]:
                    mover_ctxs[ctx] = next_val
            else:
                nonmover_ctxs.add(ctx)
        overlap = set(mover_ctxs.keys()) & nonmover_ctxs
        if overlap:
            ec_details.append((j, overlap, {k: mover_ctxs[k] for k in overlap}))
    return ec_details


def is_sweep(word, n):
    """Is this a pure sweep (all CW or all CCW)?"""
    L = len(word)
    dirs = [(word[(i + 1) % L] - word[i]) % n for i in range(L)]
    return all(d == 1 for d in dirs) or all(d == n - 1 for d in dirs)


def classify_walk(word, n):
    """Classify walk type: sweep, wiggle, etc."""
    L = len(word)
    dirs = []
    for i in range(L):
        d = (word[(i + 1) % L] - word[i]) % n
        if d == 1:
            dirs.append('+')
        elif d == n - 1:
            dirs.append('-')
        else:
            dirs.append('?')
    direction_changes = sum(1 for i in range(L) if dirs[i] != dirs[(i + 1) % L])
    if direction_changes == 0:
        return "sweep"
    elif direction_changes == 2:
        return "single-wiggle"
    else:
        return f"multi-wiggle({direction_changes})"


def main():
    n = 9
    ms = make_ms(n, (0, 3, 6))  # (3,3,3) gaps
    print(f"ms = {ms}")
    print(f"Binary at: 0, 3, 6")
    print(f"Ternary at: 1, 2, 4, 5, 7, 8")

    # Enumerate walks
    walks = enumerate_walks(n, ms)
    print(f"\nTotal walks: {len(walks)}")

    # Classify walks
    walk_types = Counter()
    for w in walks:
        wtype = classify_walk(w, n)
        walk_types[wtype] += 1
    print(f"Walk types: {dict(walk_types)}")

    # For each walk, check all state-sequence combos
    # Binary: ms=2, fc=2 -> seqs: [(0,1,0)]
    # Ternary: ms=3, fc=3 -> seqs: [(0,1,2,0), (0,2,1,0)]
    print("\nState sequence counts per proc:")
    for p in range(n):
        seqs = enumerate_state_sequences(ms[p], ms[p])
        print(f"  P{p} (m={ms[p]}): {len(seqs)} seqs: {seqs}")

    # Total combos per walk: 1^3 * 2^6 = 64
    print(f"\nCombos per walk: 1^3 * 2^6 = 64")

    all_exceptions = []
    walk_stats = []

    for widx, word in enumerate(walks):
        wtype = classify_walk(word, n)
        proc_seqs = {}
        for p in range(n):
            proc_seqs[p] = enumerate_state_sequences(ms[p], ms[p])
        sl = [proc_seqs[p] for p in range(n)]

        valid = 0
        ec_count = 0
        no_ec = []

        for combo in iproduct(*sl):
            details = check_ec_detailed(word, n, ms, combo)
            if details is None:
                continue
            valid += 1
            if details:
                ec_count += 1
            else:
                no_ec.append(combo)
                all_exceptions.append((word, combo))

        walk_stats.append((word, wtype, valid, ec_count, len(no_ec)))

    # Report
    print(f"\n{'='*70}")
    print("WALK-BY-WALK ANALYSIS")
    print(f"{'='*70}")

    total_valid = 0
    total_ec = 0
    total_no_ec = 0

    for word, wtype, valid, ec, no_ec in walk_stats:
        total_valid += valid
        total_ec += ec
        total_no_ec += no_ec
        if no_ec > 0:
            print(f"  word_start={list(word)[:8]}..., type={wtype}, "
                  f"valid={valid}, EC={ec}, no_EC={no_ec}")

    print(f"\nTotals: valid={total_valid}, EC={total_ec}, no_EC={total_no_ec}")

    # Analyze exceptions
    print(f"\n{'='*70}")
    print(f"EXCEPTION ANALYSIS ({len(all_exceptions)} total)")
    print(f"{'='*70}")

    # Group by walk type
    exc_by_type = Counter()
    for word, combo in all_exceptions:
        exc_by_type[classify_walk(word, n)] += 1
    print(f"Exceptions by walk type: {dict(exc_by_type)}")

    # Group by state-sequence pattern
    exc_by_seqpattern = Counter()
    for word, combo in all_exceptions:
        # For ternary procs, is the sequence inc (0,1,2,0) or dec (0,2,1,0)?
        pattern = []
        for p in range(n):
            if ms[p] == 3:
                if combo[p] == (0, 1, 2, 0):
                    pattern.append('I')
                elif combo[p] == (0, 2, 1, 0):
                    pattern.append('D')
                else:
                    pattern.append('?')
            else:
                pattern.append('b')
        exc_by_seqpattern[tuple(pattern)] += 1

    print(f"\nExceptions by ternary inc/dec pattern:")
    for pattern, cnt in sorted(exc_by_seqpattern.items(), key=lambda x: -x[1]):
        print(f"  {pattern}: {cnt}")

    # Show a detailed exception
    if all_exceptions:
        print(f"\nDetailed first exception:")
        word, combo = all_exceptions[0]
        print(f"  Word: {list(word)}")
        print(f"  State seqs: {[list(combo[p]) for p in range(n)]}")
        L = len(word)
        ss = {p: combo[p] for p in range(n)}
        fcc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        good = configs[:L]
        print(f"  Cycle length: {L}")
        print(f"  Configs:")
        for t in range(min(L, 10)):
            mover = word[t]
            print(f"    t={t}: {good[t]} -> fire P{mover}")

        # Show per-processor contexts
        print(f"\n  Per-processor context analysis:")
        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            mover_ctxs = {}
            nonmover_ctxs = {}
            for t in range(L):
                ctx = (good[t][Lp], good[t][j], good[t][Rp])
                if word[t] == j:
                    next_val = good[(t + 1) % L][j]
                    mover_ctxs[ctx] = next_val
                else:
                    if ctx not in nonmover_ctxs:
                        nonmover_ctxs[ctx] = []
                    nonmover_ctxs[ctx].append(t)
            overlap = set(mover_ctxs.keys()) & set(nonmover_ctxs.keys())
            print(f"    P{j} (m={ms[j]}): mover_ctxs={len(mover_ctxs)}, "
                  f"nonmover_ctxs={len(nonmover_ctxs)}, overlap={len(overlap)}")
            if not overlap:
                print(f"      Mover: {mover_ctxs}")
                print(f"      Nonmover keys: {set(nonmover_ctxs.keys())}")

    # Check: are the exceptions all sweeps?
    sweep_exceptions = sum(1 for w, c in all_exceptions if is_sweep(w, n))
    print(f"\nSweep exceptions: {sweep_exceptions}/{len(all_exceptions)}")

    # For sweep cycles, shadow cycle should block them
    # (this is proved in MEMORY.md for consecutive binary,
    #  need to verify for non-consecutive)


if __name__ == "__main__":
    main()
