#!/usr/bin/env python3
"""binscc_prove_overlap.py — Toward analytical proof of universal overlap.

Key question: WHY must every fair cycle on ≥3 binary architectures overlap?

Approach: For binary processor p, track HOW the context (L,S,R) evolves
along the cycle. The mover contexts and nonmover contexts are not random —
they're constrained by the ring dynamics. Understand these constraints to
build a pigeonhole/parity argument.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict, Counter
import random

random.seed(42)

EXOTIC_WORDS_PATH = os.path.join(
    os.path.dirname(__file__), '..', 'gpt', 'scripts',
    'glb_wrap_unknown_rotation_reps_n9.txt'
)


def load_exotic_words(path, max_words=None):
    words = []
    with open(path) as f:
        for line in f:
            s = line.strip()
            if not s:
                continue
            words.append(tuple(int(x) for x in s.split()))
            if max_words and len(words) >= max_words:
                break
    return words


def build_cycle_from_movers(ms, n, movers_word, max_reps=10):
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = list(movers_word) * max_reps
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            return cycle, full[:step+1]
        if nc in visited:
            return None, None
        visited.add(nc)
        cycle.append(nc)
    return None, None


def is_fair(movers, n):
    return len(set(movers)) == n


def parity_compatible(ms, movers):
    n = len(ms)
    counts = Counter(movers)
    for p in range(n):
        if ms[p] == 2 and counts.get(p, 0) % 2 != 0:
            return False
    return True


if __name__ == "__main__":
    n = 9

    # Load words
    exotic_words = load_exotic_words(EXOTIC_WORDS_PATH)
    bounce_word = tuple(list(range(n)) + list(range(n-2, 0, -1)) + list(range(n)))
    insertion_word = tuple([0,1,0] + list(range(1,n)) + list(range(n-2,0,-1)) + list(range(2,n)))
    top_insertion = (0,8,7,8,7,6,5,4,3,2,1,0,1,2,3,4,5,6,7,6,5,4,3,2,1)
    all_words = list(exotic_words) + [bounce_word, insertion_word, top_insertion]

    # ================================================================
    # Part 1: Identify the 4 clean cases on 2B control
    # ================================================================
    print("=" * 78)
    print("THE 4 CLEAN CASES ON 2B CONTROL: (2,3,3,3,3,3,3,3,2)")
    print("=" * 78)

    ms = (2,3,3,3,3,3,3,3,2)
    clean_words = []

    for word in all_words:
        if not parity_compatible(ms, word):
            continue
        cycle, movers = build_cycle_from_movers(ms, n, word)
        if cycle is None:
            continue
        if not is_fair(movers, n):
            continue

        # Check overlap
        mover_triples = defaultdict(set)
        nonmover_triples = defaultdict(set)
        for idx in range(len(cycle)):
            c = cycle[idx]
            mv = movers[idx]
            for p in range(n):
                triple = (c[(p-1)%n], c[p], c[(p+1)%n])
                if p == mv:
                    mover_triples[p].add(triple)
                else:
                    nonmover_triples[p].add(triple)

        has_overlap = False
        for p in range(n):
            if mover_triples[p] & nonmover_triples[p]:
                has_overlap = True
                break

        if not has_overlap:
            clean_words.append((word, cycle, movers))

    print(f"Found {len(clean_words)} clean (overlap-free) cycles")
    for i, (word, cycle, movers) in enumerate(clean_words):
        print(f"\n  Clean cycle {i+1}:")
        print(f"    Movers: {list(word)}")
        print(f"    Cycle length: {len(cycle)}")
        counts = Counter(word)
        print(f"    Mover counts: {dict(sorted(counts.items()))}")

        # Show context usage per processor
        mover_triples = defaultdict(set)
        nonmover_triples = defaultdict(set)
        for idx in range(len(cycle)):
            c = cycle[idx]
            mv = movers[idx]
            for p in range(n):
                triple = (c[(p-1)%n], c[p], c[(p+1)%n])
                if p == mv:
                    mover_triples[p].add(triple)
                else:
                    nonmover_triples[p].add(triple)

        for p in [0, 8]:  # binary processors
            m_L = ms[(p-1)%n]
            m_R = ms[(p+1)%n]
            total = m_L * 2 * m_R
            mt = mover_triples[p]
            nmt = nonmover_triples[p]
            print(f"    P{p} (binary, ctx_space={total}): "
                  f"mover_ctx={sorted(mt)} nonmover_ctx={sorted(nmt)}")
            print(f"      Used {len(mt)+len(nmt)}/{total} contexts, "
                  f"free={total - len(mt) - len(nmt)}")

    # ================================================================
    # Part 2: Detailed overlap anatomy for ≥3 binary
    # ================================================================
    print(f"\n{'=' * 78}")
    print("OVERLAP ANATOMY: Why ≥3 binary always overlaps")
    print("=" * 78)

    ms3b = (2, 3, 3, 2, 3, 3, 2, 3, 3)  # 3B evenly spread

    # Take a sample of fair cycles and analyze overlap mechanism
    sample_cycles = []
    for word in all_words:
        if not parity_compatible(ms3b, word):
            continue
        cycle, movers = build_cycle_from_movers(ms3b, n, word)
        if cycle is None:
            continue
        if not is_fair(movers, n):
            continue
        sample_cycles.append((word, cycle, movers))
        if len(sample_cycles) >= 500:
            break

    print(f"Analyzing {len(sample_cycles)} fair cycles on {ms3b}")

    # For each binary processor, track:
    # - Which contexts are used as mover vs nonmover
    # - What fraction of context space is covered by nonmover
    # - The overlap contexts
    bin_procs = [p for p in range(n) if ms3b[p] == 2]

    for p in bin_procs:
        m_L = ms3b[(p-1)%n]
        m_R = ms3b[(p+1)%n]
        total_ctx = m_L * 2 * m_R

        # All possible contexts for this processor
        all_ctx = set()
        for L in range(m_L):
            for S in range(2):
                for R in range(m_R):
                    all_ctx.add((L, S, R))

        # Statistics across cycles
        nonmover_coverage = []  # fraction of context space covered by nonmover
        mover_sizes = []
        overlap_sizes = []
        never_free = Counter()  # contexts that are ALWAYS in nonmover set

        for word, cycle, movers in sample_cycles:
            mover_ctx = set()
            nonmover_ctx = set()
            for idx in range(len(cycle)):
                c = cycle[idx]
                mv = movers[idx]
                triple = (c[(p-1)%n], c[p], c[(p+1)%n])
                if mv == p:
                    mover_ctx.add(triple)
                else:
                    nonmover_ctx.add(triple)

            nonmover_coverage.append(len(nonmover_ctx) / total_ctx)
            mover_sizes.append(len(mover_ctx))
            overlap_sizes.append(len(mover_ctx & nonmover_ctx))

            for ctx in nonmover_ctx:
                never_free[ctx] += 1

        avg_nm_cov = sum(nonmover_coverage) / len(nonmover_coverage)
        avg_m = sum(mover_sizes) / len(mover_sizes)
        avg_ov = sum(overlap_sizes) / len(overlap_sizes)
        min_free = total_ctx - max(len(nc) for _, _, nc in
            [(w, c, {(c2[(p-1)%n], c2[p], c2[(p+1)%n]) for idx2, c2 in enumerate(c) if m[idx2] != p})
             for w, c, m in sample_cycles[:1]] or [set()])

        print(f"\n  P{p} (binary, neighbors m_L={m_L}, m_R={m_R}, ctx_space={total_ctx}):")
        print(f"    Avg nonmover coverage: {avg_nm_cov:.1%} of context space")
        print(f"    Avg mover contexts: {avg_m:.1f}")
        print(f"    Avg overlaps: {avg_ov:.1f}")

        # Which contexts are always in nonmover?
        always_nonmover = [ctx for ctx, count in never_free.items()
                          if count == len(sample_cycles)]
        print(f"    Contexts in nonmover in ALL cycles: {len(always_nonmover)}/{total_ctx}")
        if always_nonmover:
            print(f"      {sorted(always_nonmover)[:10]}")

        # Which contexts are in mover in at least one cycle?
        mover_ever = Counter()
        for word, cycle, movers in sample_cycles:
            for idx in range(len(cycle)):
                c = cycle[idx]
                if movers[idx] == p:
                    mover_ever[(c[(p-1)%n], c[p], c[(p+1)%n])] += 1

        mover_possible = {ctx for ctx, count in mover_ever.items()}
        print(f"    Contexts used as mover (across all cycles): {len(mover_possible)}/{total_ctx}")

        # The critical question: can mover contexts avoid nonmover contexts?
        free_from_nonmover = all_ctx - set(always_nonmover)
        can_avoid = mover_possible <= free_from_nonmover
        print(f"    Free from always-nonmover: {len(free_from_nonmover)} contexts")
        print(f"    Can mover avoid always-nonmover? {can_avoid}")
        if not can_avoid:
            stuck = mover_possible & set(always_nonmover)
            print(f"    *** FORCED OVERLAP: {len(stuck)} mover contexts "
                  f"are ALWAYS nonmover ***")
            print(f"      Stuck contexts: {sorted(stuck)}")

    # ================================================================
    # Part 3: Analytical proof attempt — context evolution
    # ================================================================
    print(f"\n{'=' * 78}")
    print("CONTEXT EVOLUTION: How binary processor contexts change along the cycle")
    print("=" * 78)

    # For the all-zeros starting config, track how P0's context (L,S,R)
    # evolves step by step. When does P0 fire vs not fire?

    ms3b_test = (2, 3, 3, 2, 3, 3, 2, 3, 3)
    word = sample_cycles[0][0]
    cycle = sample_cycles[0][1]
    movers_list = sample_cycles[0][2]

    p = 0  # binary processor at position 0
    print(f"\n  Cycle for {ms3b_test}, word starts with: {list(word)[:20]}...")
    print(f"  P{p} (binary) context evolution:")
    print(f"  {'Step':>4} {'Mover':>5} {'P0_ctx':>15} {'Role':>8}")
    print(f"  {'-'*35}")
    for idx in range(min(len(cycle), 30)):
        c = cycle[idx]
        mv = movers_list[idx]
        L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
        role = "MOVER" if mv == p else f"P{mv}"
        print(f"  {idx:>4} {mv:>5} ({L},{S},{R}){' ':>6} {role:>8}")

    # ================================================================
    # Part 4: Key insight — nonmover includes the START config
    # ================================================================
    print(f"\n{'=' * 78}")
    print("KEY INSIGHT: Start config forces overlap")
    print("=" * 78)

    # The all-zeros config (0,0,...,0) is visited by every cycle.
    # At this config, binary processor p sees context (0,0,0) if both
    # neighbors are binary, or (0,0,0) if neighbors start at 0 too.
    # The mover at step 0 is movers[0]. If movers[0] ≠ p, then p sees
    # (0,0,0) as nonmover.
    # But at some other step, p fires with context (0,0,0) → this would
    # create overlap.

    # For the cycle to return to all-zeros, p must fire from state 0 and
    # return to state 0 (since m_p = 2, this means firing 2k times:
    # 0→1→0 or 0→1→0→1→0 etc.)
    # At least one firing has S=0 and at least one has S=1.
    # The S=0 firing sees context (L, 0, R) for some L, R.

    # Now: at the all-zeros start, p sees (0, 0, 0) (if both neighbors
    # are binary or start at 0). If p is not the first mover, this is
    # a nonmover context. If p later fires at context (0, 0, R) for any R,
    # and if R=0 was the value at start... overlap.

    print(f"  Every cycle starts at all-zeros: (0,0,...,0)")
    print(f"  At all-zeros, binary processor p sees context (0, 0, neighbor_0)")
    print(f"  Since cycle starts at all-zeros, p is nonmover at step 0")
    print(f"  (unless p is the first mover)")
    print(f"  For the cycle to be fair, p must fire at least once.")
    print(f"  If p fires from state 0, it sees (L, 0, R) for some L, R.")
    print(f"  If L = neighbor's initial state and R = other neighbor's initial state,")
    print(f"  this could coincide with the step-0 nonmover context.")
    print(f"  But the neighbors may have changed by then...")

    # Let's check: for each cycle, when p first fires, what's the context?
    # Is it the same as the initial nonmover context?
    for p in bin_procs:
        same_as_start = 0
        total_checked = 0

        for word, cycle, movers_l in sample_cycles:
            # Context at start
            c0 = cycle[0]
            start_ctx = (c0[(p-1)%n], c0[p], c0[(p+1)%n])
            is_mover_at_start = (movers_l[0] == p)

            # Find first firing of p
            first_fire_ctx = None
            for idx in range(len(cycle)):
                if movers_l[idx] == p:
                    c = cycle[idx]
                    first_fire_ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
                    break

            if first_fire_ctx is None:
                continue

            total_checked += 1
            if first_fire_ctx == start_ctx and not is_mover_at_start:
                same_as_start += 1

        print(f"  P{p}: first fire context = start context (when not starting mover): "
              f"{same_as_start}/{total_checked} ({same_as_start/max(1,total_checked)*100:.1f}%)")

    # ================================================================
    # Part 5: Which processor overlaps?
    # ================================================================
    print(f"\n{'=' * 78}")
    print("WHICH PROCESSORS OVERLAP? (per cycle)")
    print("=" * 78)

    overlap_at = Counter()
    overlap_at_binary = Counter()
    total_fair = 0

    for word, cycle, movers_l in sample_cycles:
        total_fair += 1
        mover_triples = defaultdict(set)
        nonmover_triples = defaultdict(set)
        for idx in range(len(cycle)):
            c = cycle[idx]
            mv = movers_l[idx]
            for p in range(n):
                triple = (c[(p-1)%n], c[p], c[(p+1)%n])
                if mv == p:
                    mover_triples[p].add(triple)
                else:
                    nonmover_triples[p].add(triple)

        for p in range(n):
            if mover_triples[p] & nonmover_triples[p]:
                overlap_at[p] += 1
                if ms3b[p] == 2:
                    overlap_at_binary[p] += 1

    print(f"  Architecture: {ms3b}, {total_fair} fair cycles")
    for p in range(n):
        bstr = "BIN" if ms3b[p] == 2 else "TER"
        pct = overlap_at[p] / total_fair * 100
        print(f"  P{p} ({bstr}): overlaps in {overlap_at[p]}/{total_fair} cycles ({pct:.1f}%)")

    # Is overlap ALWAYS at the same processor?
    always_overlap_at = [p for p in range(n) if overlap_at[p] == total_fair]
    if always_overlap_at:
        print(f"\n  Processors that ALWAYS overlap: {always_overlap_at}")
    else:
        print(f"\n  No single processor overlaps in ALL cycles")
        print(f"  But overlap occurs SOMEWHERE in every cycle")

    # ================================================================
    # Part 6: Try to construct a non-overlapping cycle analytically
    # ================================================================
    print(f"\n{'=' * 78}")
    print("ANALYTICAL LOWER BOUND ON OVERLAP")
    print("=" * 78)

    # For binary p with neighbors m_L, m_R:
    # Context space C = {(L,S,R) : L ∈ [m_L], S ∈ {0,1}, R ∈ [m_R]}
    # |C| = 2 · m_L · m_R
    #
    # In cycle of length ℓ:
    # - p fires k times (k even, k ≥ 2)
    # - p is nonmover ℓ - k times
    # - Mover contexts M ⊆ C, |M| ≤ k
    # - Nonmover contexts N ⊆ C, |N| ≤ ℓ - k
    # - Need M ∩ N = ∅ (no overlap)
    # - So |M| + |N| ≤ |C| = 2 · m_L · m_R
    # - i.e., k + (ℓ - k) ≤ 2 · m_L · m_R
    # - i.e., ℓ ≤ 2 · m_L · m_R
    #
    # For ℓ = 3n - 2 = 25 and binary neighbors (m_L = m_R = 2):
    # Need 25 ≤ 2 · 2 · 2 = 8... FALSE!
    # So if m_L = m_R = 2, the cycle is LONGER than the context space.
    # By PIGEONHOLE: some context must be used as BOTH mover and nonmover.
    #
    # BUT: this only applies when m_L = m_R = 2 (binary neighbors).
    # With ternary neighbors: 25 ≤ 2 · 3 · 3 = 18? NO, 25 > 18.
    # ALSO fails! Even with ternary neighbors!
    # With 3-ternary neighbors: 25 ≤ 2 · 3 · 3 = 18? 25 > 18. FAILS.
    #
    # WAIT: ℓ = 25 and |C| = 18. So we need 25 visits to fit in 18 slots.
    # But visits are split: k mover visits use at most k distinct contexts,
    # and ℓ-k nonmover visits use at most ℓ-k distinct contexts.
    # If k ≤ |C|/2 and ℓ-k ≤ |C|/2, no pigeonhole.
    # But ℓ > |C| means k + (ℓ-k) = ℓ > |C|.
    # Since M and N are subsets of C and M ∩ N = ∅ required:
    # |M ∪ N| = |M| + |N| ≤ |C|
    # But |M| ≤ min(k, |C|) and |N| ≤ min(ℓ-k, |C|)
    # We need |M| + |N| ≤ |C|
    # Not |M| + |N| = ℓ (that would be wrong: distinct contexts, not visits)
    #
    # Hmm, the pigeonhole is on VISITS not CONTEXTS.
    # With ℓ = 25 visits and |C| = 18 context slots:
    # by pigeonhole, ≥ 25 - 18 = 7 visits share a context with another visit.
    # But sharing between two mover visits is OK, between two nonmover is OK.
    # Only mover-nonmover sharing creates overlap.
    #
    # REVISED: Need |M| + |N| ≤ |C| where M = distinct mover contexts,
    # N = distinct nonmover contexts. With k mover visits, |M| ≤ k.
    # With ℓ-k nonmover visits, |N| ≤ ℓ-k. But also |M| ≤ |C| and |N| ≤ |C|.
    # For disjointness: |M| + |N| ≤ |C|.
    # Since |M| ≤ k and |N| ≤ min(ℓ-k, |C|):
    # Need k + min(ℓ-k, |C|) ≤ |C|? NO, that's wrong too.
    # Need |M| + |N| ≤ |C|. We know |M| ≤ k. For |N|: with ℓ-k visits
    # across |C| contexts, |N| ≤ min(ℓ-k, |C|).
    # If ℓ - k ≥ |C|, then |N| CAN be = |C| (all contexts covered as nonmover).
    # Then |M| + |N| ≤ |C| requires |M| = 0, i.e., k = 0. But k ≥ 2 (fairness).
    # So IF ℓ - k ≥ |C| AND |N| = |C|, overlap is FORCED.
    #
    # When is |N| = |C|? When the ℓ-k nonmover visits cover ALL contexts.
    # This is guaranteed if the cycle structure ensures diverse enough configs.
    # It's NOT automatic — the nonmover visits might cluster.
    #
    # KEY: ℓ - k ≥ |C| means the nonmover visits CAN cover all contexts
    # (by pigeonhole they use at least ℓ-k-|C|+1 distinct contexts,
    # which is more than 0 if ℓ-k > |C|).
    # But ℓ-k ALWAYS covers all |C| contexts? NOT necessarily.

    print(f"  Cycle length ℓ = 3n - 2 = {3*n - 2}")
    print()

    for ms_label, ms_val in [("3B consec", (2,2,2,3,3,3,3,3,3)),
                               ("3B spread", (2,3,3,2,3,3,2,3,3)),
                               ("2B control", (2,3,3,3,3,3,3,3,2))]:
        bin_procs_local = [p for p in range(n) if ms_val[p] == 2]
        print(f"  {ms_label} = {ms_val}")
        for p in bin_procs_local:
            m_L = ms_val[(p-1)%n]
            m_R = ms_val[(p+1)%n]
            ctx_size = 2 * m_L * m_R
            # k = mover visits to p. For binary, k is even, k ≥ 2.
            # ℓ = cycle length = 25 (for 3n-2)
            # nonmover visits = ℓ - k ≥ 25 - k
            # For disjointness: |M| + |N| ≤ ctx_size
            # |M| ≤ k, |N| = |N_actual| (could be up to min(ℓ-k, ctx_size))
            # Worst case for prover: |N| as small as possible.
            # But nonmover visits ≥ 23. With 23 visits to 18 contexts,
            # |N| ≥ ? Not clear without structure.

            print(f"    P{p}: m_L={m_L}, m_R={m_R}, ctx_space={ctx_size}")
            print(f"      ℓ={3*n-2}, min k=2 → nonmover visits ≥ {3*n-2 - 2} = {3*n-4}")
            if 3*n - 4 > ctx_size:
                print(f"      nonmover visits ({3*n-4}) > ctx_space ({ctx_size})")
                print(f"      → nonmover MUST repeat contexts (but may not cover all)")
                print(f"      If nonmover covers all {ctx_size} contexts: |M|=0 needed → impossible (k≥2)")
                print(f"      But does nonmover ALWAYS cover all? Depends on cycle structure.")
            else:
                print(f"      nonmover visits ({3*n-4}) ≤ ctx_space ({ctx_size}) — no pigeonhole")
        print()

    # So the pure pigeonhole on |M|+|N| ≤ |C| doesn't directly work
    # for ternary neighbors. We need a structural argument about
    # nonmover coverage.

    # ================================================================
    # Part 7: Empirical nonmover coverage
    # ================================================================
    print(f"{'=' * 78}")
    print("NONMOVER COVERAGE: Do nonmover visits cover all contexts?")
    print("=" * 78)

    for ms_label, ms_val in [("3B spread", (2,3,3,2,3,3,2,3,3)),
                               ("2B control", (2,3,3,3,3,3,3,3,2))]:
        words_to_test = all_words[:5000]
        bin_procs_local = [p for p in range(n) if ms_val[p] == 2]

        coverage_stats = defaultdict(list)

        for word in words_to_test:
            if not parity_compatible(ms_val, word):
                continue
            cycle, movers_l = build_cycle_from_movers(ms_val, n, word)
            if cycle is None:
                continue
            if not is_fair(movers_l, n):
                continue

            for p in bin_procs_local:
                m_L = ms_val[(p-1)%n]
                m_R = ms_val[(p+1)%n]
                ctx_size = 2 * m_L * m_R

                nonmover_ctx = set()
                mover_ctx = set()
                for idx in range(len(cycle)):
                    c = cycle[idx]
                    triple = (c[(p-1)%n], c[p], c[(p+1)%n])
                    if movers_l[idx] == p:
                        mover_ctx.add(triple)
                    else:
                        nonmover_ctx.add(triple)

                coverage = len(nonmover_ctx) / ctx_size
                coverage_stats[(p, ctx_size)].append(
                    (coverage, len(mover_ctx), len(nonmover_ctx), ctx_size))

        print(f"\n  {ms_label} = {ms_val}")
        for (p, ctx_size), stats in sorted(coverage_stats.items()):
            coverages = [s[0] for s in stats]
            mover_sizes = [s[1] for s in stats]
            nonmover_sizes = [s[2] for s in stats]
            min_cov = min(coverages)
            max_cov = max(coverages)
            avg_cov = sum(coverages) / len(coverages)
            min_nm = min(nonmover_sizes)
            full_coverage = sum(1 for c in coverages if c == 1.0)
            # Check: is |M| + |N| > |C| in any case?
            m_plus_n = [m + nm for m, nm in zip(mover_sizes, nonmover_sizes)]
            exceeds = sum(1 for v in m_plus_n if v > ctx_size)

            print(f"    P{p} (ctx={ctx_size}): {len(stats)} cycles, "
                  f"nonmover coverage: min={min_cov:.2f} avg={avg_cov:.2f} max={max_cov:.2f}, "
                  f"full={full_coverage}/{len(stats)}, "
                  f"|M|+|N|>{ctx_size}: {exceeds}/{len(stats)}")

    print(f"\n{'=' * 78}")
    print("DONE")
    print("=" * 78)
