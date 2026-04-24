#!/usr/bin/env python3
"""binscc_sandwich_theorem.py — Prove: non-binary proc between binary always has conflict.

KEY CONJECTURE: If non-binary proc q has BOTH neighbors binary (bL, bR),
then on any fair ring-adjacent cycle, q has mover/nonmover context overlap.

This is the "sandwich theorem" — q is sandwiched between binary procs.

PROOF IDEA:
q fires m_q times. Each firing gives a mover context (bL_val, q_state, bR_val).
Between firings, q stays at a fixed state. During that interval, bL and bR
may fire (changing L and R). Those steps are nonmover contexts for q.

Context space: 2 × m_q × 2 = 4m_q.
q's mover contexts use m_q of these.
q's nonmover contexts use the rest.

If nonmover contexts at q cover ALL of the context space, then every
mover context is also a nonmover context → conflict guaranteed.

The question: do nonmover contexts at q cover the entire 4m_q context space?

Ring-adjacency constraint: after q fires, the next mover is bL or bR.
Before q fires, the previous mover was bL or bR.
So binary neighbors fire AROUND q's firing, cycling through (bL,bR) states.
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
    print("SANDWICH THEOREM: NB PROC BETWEEN BINARY ALWAYS HAS CONFLICT")
    print("=" * 70)
    print()

    # Part 1: For each "sandwiched" NB proc, check if IT always has conflict
    print("PART 1: PER-SANDWICHED-PROC CONFLICT CHECK")
    print("=" * 60)
    print()

    test_configs = [
        (5, [2, 3, 2, 3, 2], 21),    # P1,P3 sandwiched
        (6, [2, 3, 2, 3, 2, 3], 24),  # P1,P3,P5 sandwiched
        (7, [2, 3, 2, 3, 2, 3, 3], 27),  # P1,P3 sandwiched (P5,P6 not)
        (5, [2, 4, 2, 3, 2], 21),     # mixed: P1(m=4), P3(m=3) sandwiched
        (6, [2, 4, 2, 3, 2, 3], 24),  # mixed
    ]

    for n, ms, max_len in test_configs:
        print(f"\n--- n={n} ms={ms} ---")
        bin_procs = [i for i in range(n) if ms[i] == 2]
        sandwiched = [i for i in range(n) if ms[i] > 2
                      and ms[(i-1) % n] == 2 and ms[(i+1) % n] == 2]
        print(f"  Binary: {bin_procs}, Sandwiched NB: {sandwiched}")

        t0 = time.time()
        words = enumerate_mover_words(ms, n, max_len)
        t1 = time.time()

        total = 0
        # Per sandwiched proc: does it ALWAYS have conflict?
        proc_conflict = {q: 0 for q in sandwiched}
        proc_no_conflict = {q: 0 for q in sandwiched}
        any_sandwiched_conflict = 0
        no_sandwiched_conflict = 0

        # Coverage analysis: what fraction of context space is nonmover?
        proc_nm_coverage = {q: Counter() for q in sandwiched}  # q -> {coverage: count}

        # Mover context analysis
        proc_mover_pattern = {q: Counter() for q in sandwiched}  # q -> {(bL,bR): count}

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1
            ell = len(cycle)

            any_sw = False
            for q in sandwiched:
                mL = (q-1) % n
                mR = (q+1) % n
                ctx_space = 2 * ms[q] * 2

                mover_set = set()
                nonmover_set = set()

                for step in range(ell):
                    c = cycle[step]
                    c_next = cycle[(step+1) % ell]
                    diffs = [j for j in range(n) if c[j] != c_next[j]]
                    mover = diffs[0]
                    L = c[mL]
                    S = c[q]
                    R = c[mR]

                    if mover == q:
                        mover_set.add((L, S, R))
                    else:
                        nonmover_set.add((L, S, R))

                overlap = mover_set & nonmover_set
                coverage = len(nonmover_set)

                proc_nm_coverage[q][coverage] += 1

                if overlap:
                    proc_conflict[q] += 1
                    any_sw = True

                    # Track which (bL,bR) pairs cause overlap
                    for ctx in overlap:
                        proc_mover_pattern[q][(ctx[0], ctx[2])] += 1
                else:
                    proc_no_conflict[q] += 1

            if any_sw:
                any_sandwiched_conflict += 1
            else:
                no_sandwiched_conflict += 1

        elapsed = time.time() - t0
        print(f"  {total} valid cycles ({elapsed:.1f}s)")

        for q in sandwiched:
            ctx_space = 2 * ms[q] * 2
            pct = 100 * proc_conflict[q] / total if total > 0 else 0
            print(f"  P{q} (m={ms[q]}, ctx_space={ctx_space}): {proc_conflict[q]}/{total} conflict ({pct:.1f}%)")
            print(f"    NM coverage: {dict(sorted(proc_nm_coverage[q].items()))}")
            if proc_mover_pattern[q]:
                print(f"    Overlap (bL,bR): {dict(sorted(proc_mover_pattern[q].items()))}")

        pct_any = 100 * any_sandwiched_conflict / total if total > 0 else 0
        print(f"  ANY sandwiched conflict: {any_sandwiched_conflict}/{total} ({pct_any:.1f}%)")
        if no_sandwiched_conflict > 0:
            print(f"  !! {no_sandwiched_conflict} cycles with NO sandwiched conflict")
        else:
            print(f"  ★ ALL cycles have sandwiched conflict!")
        sys.stdout.flush()

    # Part 2: Detailed analysis of NM coverage at sandwiched procs
    print(f"\n\n{'='*70}")
    print("PART 2: WHY COVERAGE IS ALWAYS FULL")
    print("=" * 70)
    print()
    print("For sandwiched NB proc q (m_q=3, binary neighbors):")
    print("  Context space = 2×3×2 = 12")
    print("  q fires 3 times → 3 mover contexts")
    print("  ell-3 nonmover visits")
    print("  If NM covers all 12: conflict guaranteed")
    print()

    # Focus on n=5 alternating — simplest case
    n, ms, max_len = 5, [2, 3, 2, 3, 2], 21
    sandwiched = [1, 3]
    words = enumerate_mover_words(ms, n, max_len)

    # For cycles where sandwiched proc has NM coverage < full:
    # Analyze what's missing
    partial_coverage = []
    full_but_conflict = 0
    full_no_conflict = 0  # shouldn't exist
    partial_conflict = 0
    partial_no_conflict = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        for q in sandwiched:
            mL = (q-1) % n
            mR = (q+1) % n

            mover_set = set()
            nonmover_set = set()
            # Track nonmover per q-state
            nm_per_state = defaultdict(set)  # q_state -> set of (bL, bR)
            mover_per_state = {}  # q_state -> (bL, bR)

            for step in range(ell):
                c = cycle[step]
                c_next = cycle[(step+1) % ell]
                diffs = [j for j in range(n) if c[j] != c_next[j]]
                mover = diffs[0]
                L = c[mL]
                S = c[q]
                R = c[mR]

                if mover == q:
                    mover_set.add((L, S, R))
                    mover_per_state[S] = (L, R)
                else:
                    nonmover_set.add((L, S, R))
                    nm_per_state[S].add((L, R))

            ctx_space = 2 * ms[q] * 2
            coverage = len(nonmover_set)

            if coverage < ctx_space:
                # Missing some nonmover contexts
                all_ctxs = set(iproduct(range(2), range(ms[q]), range(2)))
                missing = all_ctxs - nonmover_set
                overlap = mover_set & nonmover_set

                if len(partial_coverage) < 10:
                    partial_coverage.append({
                        'word': word, 'q': q, 'ell': ell,
                        'coverage': coverage, 'missing': missing,
                        'mover_set': mover_set, 'overlap': overlap,
                        'nm_per_state': dict(nm_per_state),
                        'mover_per_state': dict(mover_per_state),
                    })

                if overlap:
                    partial_conflict += 1
                else:
                    partial_no_conflict += 1
            else:
                if mover_set & nonmover_set:
                    full_but_conflict += 1
                else:
                    full_no_conflict += 1

    print(f"  Full NM coverage + conflict: {full_but_conflict}")
    print(f"  Full NM coverage + NO conflict: {full_no_conflict}")
    print(f"  Partial NM coverage + conflict: {partial_conflict}")
    print(f"  Partial NM coverage + NO conflict: {partial_no_conflict}")
    print()

    if partial_coverage:
        print(f"  First {min(5, len(partial_coverage))} partial coverage examples:")
        for ex in partial_coverage[:5]:
            q = ex['q']
            print(f"\n    P{q}: word len={ex['ell']}, NM coverage={ex['coverage']}/12")
            print(f"    Missing NM contexts: {sorted(ex['missing'])}")
            print(f"    Mover contexts: {sorted(ex['mover_set'])}")
            print(f"    Overlap: {sorted(ex['overlap'])}")
            for s in sorted(ex['nm_per_state'].keys()):
                print(f"    State {s}: NM (bL,bR)={sorted(ex['nm_per_state'][s])}, "
                      f"Mover (bL,bR)={ex['mover_per_state'].get(s, 'N/A')}")

    # Part 3: Binary (bL,bR) pair analysis during q's state intervals
    print(f"\n\n{'='*70}")
    print("PART 3: BINARY PAIR COVERAGE PER Q-STATE INTERVAL")
    print("=" * 70)
    print()
    print("For each q-state s, count distinct (bL,bR) pairs at nonmover steps.")
    print("If count = 4 for any state → that state's mover must conflict.")
    print("If count ≥ 3 for all states with min fire → conflict by occupancy.")
    print()

    n, ms, max_len = 5, [2, 3, 2, 3, 2], 21
    words = enumerate_mover_words(ms, n, max_len)

    coverage_per_state = Counter()  # (min_coverage_across_states) -> count

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        for q in [1, 3]:  # sandwiched procs
            mL = (q-1) % n
            mR = (q+1) % n
            nm_per_state = defaultdict(set)
            for step in range(ell):
                c = cycle[step]
                c_next = cycle[(step+1) % ell]
                diffs = [j for j in range(n) if c[j] != c_next[j]]
                if diffs[0] != q:
                    nm_per_state[c[q]].add((c[mL], c[mR]))

            if nm_per_state:
                min_cov = min(len(v) for v in nm_per_state.values())
                coverage_per_state[min_cov] += 1

    print(f"  Min (bL,bR) coverage across q-states:")
    for k in sorted(coverage_per_state.keys()):
        pct = 100 * coverage_per_state[k] / sum(coverage_per_state.values())
        label = "→ conflict guaranteed" if k == 4 else ("→ mover has ≤1 option" if k == 3 else "")
        print(f"    {k}/4 pairs: {coverage_per_state[k]} ({pct:.1f}%) {label}")

    # Part 4: The key counting argument
    print(f"\n\n{'='*70}")
    print("PART 4: COUNTING ARGUMENT")
    print("=" * 70)
    print()
    print("For sandwiched q (m_q=3, binary neighbors):")
    print("  q fires 3 times, cycling through states 0,1,2.")
    print("  At each state s, q_mover sees (bL_s, s, bR_s) — one specific pair.")
    print("  At each state s, q_nonmover sees various (bL, s, bR) pairs.")
    print()
    print("  For NO conflict: (bL_s, bR_s) must NOT appear as nonmover at state s.")
    print()
    print("  q has 3 state-intervals. bL fires 2× total, bR fires 2× total.")
    print("  By pigeonhole: some state-interval has ≤ ⌊2/3⌋ = 0 bL firings.")
    print("  But bR might fire in that interval...")
    print()
    print("  REFINED: 4 binary firings (2 bL + 2 bR) across 3 q-states.")
    print("  By pigeonhole: some state has ≤ ⌊4/3⌋ = 1 binary firing near q.")
    print("  But that's still enough to generate 1-2 (bL,bR) pairs as nonmover.")
    print()
    print("  The ACTUAL argument needs to account for ring-adjacency constraints.")
    print()

    # Part 5: Ring-adjacency constraint analysis
    print(f"{'='*70}")
    print("PART 5: RING-ADJACENCY STRUCTURE AT SANDWICHED PROCS")
    print("=" * 70)
    print()
    print("On ring-adjacent cycle, q fires only after bL or bR fires.")
    print("Analyze: what fires immediately before and after q?")
    print()

    n, ms, max_len = 5, [2, 3, 2, 3, 2], 21
    words = enumerate_mover_words(ms, n, max_len)

    before_after = Counter()  # (prev_mover, next_mover) relative to q

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None:
            continue
        ell = len(cycle)

        for q in [1, 3]:
            mL = (q-1) % n
            mR = (q+1) % n
            for step in range(ell):
                if word[step] == q:
                    prev = word[(step-1) % ell]
                    nxt = word[(step+1) % ell]
                    before_after[(prev - q, nxt - q)] += 1

    print(f"  (prev_mover - q, next_mover - q) pattern:")
    for k, v in sorted(before_after.items()):
        labels = {-1: 'bL', 1: 'bR'}
        prev_label = labels.get(k[0] % n if k[0] < 0 else k[0], '?')
        next_label = labels.get(k[1] % n if k[1] > 0 else k[1], '?')
        # Actually just show the offset
        print(f"    ({k[0]:+d}, {k[1]:+d}): {v}")

    # Part 6: The definitive test — does conflict hold for ALL multisets?
    print(f"\n\n{'='*70}")
    print("PART 6: UNIVERSAL SANDWICH CONFLICT TEST")
    print("=" * 70)
    print()

    configs = [
        # Pure ternary
        (5, [2, 3, 2, 3, 2], 21),
        (6, [2, 3, 2, 3, 2, 3], 24),
        (7, [2, 3, 2, 3, 2, 3, 3], 27),
        # Mixed
        (5, [2, 4, 2, 3, 2], 21),
        (6, [2, 4, 2, 3, 2, 3], 24),
        (6, [2, 3, 2, 4, 2, 3], 24),
        (7, [2, 4, 2, 3, 2, 3, 3], 27),
        # Larger moduli
        (5, [2, 5, 2, 3, 2], 21),
        (5, [2, 6, 2, 3, 2], 21),
    ]

    grand_total = 0
    grand_conflict = 0

    for n, ms, max_len in configs:
        sandwiched = [i for i in range(n) if ms[i] > 2
                      and ms[(i-1) % n] == 2 and ms[(i+1) % n] == 2]
        if not sandwiched:
            continue

        t0 = time.time()
        words = enumerate_mover_words(ms, n, max_len)
        total = 0
        any_sw_conflict = 0

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1
            ell = len(cycle)

            for q in sandwiched:
                mL = (q-1) % n
                mR = (q+1) % n
                mover_set = set()
                nonmover_set = set()
                for step in range(ell):
                    c = cycle[step]
                    c_next = cycle[(step+1) % ell]
                    diffs = [j for j in range(n) if c[j] != c_next[j]]
                    L = c[mL]; S = c[q]; R = c[mR]
                    if diffs[0] == q:
                        mover_set.add((L, S, R))
                    else:
                        nonmover_set.add((L, S, R))
                if mover_set & nonmover_set:
                    any_sw_conflict += 1
                    break  # one conflict suffices

        elapsed = time.time() - t0
        grand_total += total
        grand_conflict += any_sw_conflict
        pct = 100 * any_sw_conflict / total if total > 0 else 0
        status = "★ ALL" if any_sw_conflict == total else f"{any_sw_conflict}/{total}"
        print(f"  n={n} ms={ms}: {total} cycles, {status} have sandwich conflict ({pct:.1f}%) [{elapsed:.1f}s]")
        sys.stdout.flush()

    print(f"\n  GRAND: {grand_conflict}/{grand_total} ({100*grand_conflict/grand_total:.1f}%)")
    if grand_conflict == grand_total:
        print(f"  ★★ SANDWICH THEOREM HOLDS UNIVERSALLY ★★")


if __name__ == "__main__":
    main()
