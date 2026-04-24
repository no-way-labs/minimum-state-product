#!/usr/bin/env python3
"""
LAYER 2 PROOF: Coupling argument across sandwiched ternary procs.

The single-ternary pigeonhole FAILS: a single sandwiched ternary with all
normalForm phases CAN avoid EC (the walk ordering can be chosen to dodge).

The COUPLING argument: multiple sandwiched ternary procs share binary neighbors.
When b is between t1 and t2: the binary proc b's fire count splits across
BOTH t1's and t2's phases. This coupling constrains the walk orderings
simultaneously.

STRUCTURE:
  With >= 3 non-consecutive binary on a ring of n >= 7:
  Binary procs b_1, ..., b_k (k >= 3) separate arcs of ternary procs.
  Each arc has >= 1 ternary proc.
  The boundary ternary at each end of an arc is sandwiched (adjacent to binary on one side).
  Wait -- "sandwiched" = BOTH neighbors binary. So a ternary proc is sandwiched
  iff the arc has length 1 (single ternary between two binaries).

  For non-consecutive binary: between any two adjacent binaries, there's at least
  one ternary proc. If arc length = 1: the unique ternary IS sandwiched.
  If arc length > 1: only the boundary ternary (adjacent to binary) are
  "boundary ternary" but NOT sandwiched (other neighbor is ternary).

  For the allNormalForm_false2 theorem: it specifically requires a sandwiched
  ternary t where BOTH neighbors are binary. So the argument ONLY applies
  when some arc has length exactly 1.

  With >= 3 non-consecutive binary and >= 3 arcs: each arc has >= 1 ternary.
  For n = 2k (alternating): each arc has exactly 1 ternary (all sandwiched).
  For n = 2k+1 (3 binary, rest ternary): arcs have lengths summing to n-3 >= 4.
  With 3 arcs: at least one has length 1 (pigeonhole on 3 arcs with sum >= 4)?
  NO: 3 arcs could be 2,2,... etc. E.g., n=9, ms=[2,3,3,2,3,3,2,3,3]: 3 arcs of 2.
  No sandwiched ternary! But the theorem allNormalForm_false2 receives a
  sandwiched t as input, so it only fires when one exists.

  WAIT: The PhaseExtractionClean code looks for a "pivot" t where
  m(left t) = 2 AND m(right t) = 2. If no such pivot exists, it takes a
  different branch. So the allNormalForm_false2 theorem IS only called when
  a sandwiched ternary exists.

  When does a sandwiched ternary exist?
  With >= 3 non-consecutive binary: some binary b has binary neighbors?
  NO: non-consecutive means no two binary are adjacent.
  So left(b) and right(b) are ternary for all binary b.
  A ternary t is sandwiched iff both left(t) and right(t) are binary.
  This means t is between two binary procs (arc length 1).

  With n >= 7, >= 3 binary, non-consecutive: the binary procs divide the ring
  into >= 3 arcs of ternary procs. The sum of arc lengths = n - k (where k = #binary).
  Each arc has >= 1 ternary (non-consecutive constraint).
  Arc length = 1 iff the ternary is sandwiched.

  WHEN does at least one arc have length 1?
  If k >= ceil(n/2): all arcs have length 1 (alternating).
  If k < ceil(n/2): some arcs have length > 1.
  E.g., n=9, k=3: arcs have lengths summing to 6 across 3 arcs. Each >= 1.
  Could be (1,1,4), (1,2,3), (2,2,2). The (2,2,2) case has NO sandwiched ternary.

  So the PhaseExtractionClean proof would NOT route through allNormalForm_false2
  when no sandwiched ternary exists.

  Let me check: does allNormalForm_false2 even apply in all cases where it's called?
  Actually, in PhaseExtractionClean: the pivot existence check says "exists t with
  m(left t)=2 and m(right t)=2". If no such t exists, the code goes to a different
  branch (no_firing_both_binary_neighbors_false).

  So allNormalForm_false2 ONLY needs to work when a sandwiched ternary exists.
  And it receives the specific sandwiched t as an argument.

  THE ARGUMENT for a single sandwiched ternary t:
  - All phases at t are normalForm.
  - With hfull (all procs fire): there exist other procs firing.
  - The cycle length L >> 2*fc(t).
  - SOME phase at t has length > 2.
  - In a long normalForm phase where the binary fire is tight and no second-neighbor
    fires: EC via triple matching (the step after the binary fire has the same triple
    as the t-fire step).
  - IF second-neighbor fires: the chain of adjacent movers continues.

  The key missing piece in the Lean proof is:
  (a) The adjacent-chain induction when second-neighbors fire.
  (b) The fire-count summation h_le.

  Actually, let me re-read the sorrys. Lines 1012, 1077, 1121 are about chains,
  line 1129 is about h_le (fire count sum), line 1172 is the final EC.

  Let me focus on the TIGHT + LONG PHASE argument, which is the cleanest.

  THEOREM: If all phases at sandwiched t are normalForm, and some phase has
  length > 2 with no second-neighbor firing, then EC exists at t.

  PROOF: In such a phase (a, s):
    - step a: previous t-fire (mover for t)
    - step a+1: binary fire (tight, exactly one of bL/bR)
    - steps a+2..s-1: other procs (not t, bL, bR, and no LL/RR by hypothesis)
    - step s: this t-fire (mover for t)

    Between steps a+1 and s: no fires of bL, bR, t, LL, RR.
    So the boundary triple at t is constant: c[bL], c[t], c[bR] all fixed.
    Step a+2 is a nonmover at t with some triple (L, S, R).
    Step s is a mover at t with the same triple (L, S, R).
    => EC at t.

  So the question reduces to: can ALL phases have length <= 2 OR have
  second-neighbor fires?

  With hfull and n >= 7: let's count. fc(t) = 3 (minimum for ternary).
  3 phases. If all have length 2 and no LL/RR fires: total steps from these
  phases = 3*2 = 6 (3 t-fires + 3 binary fires). But L = sum of ALL fire counts
  >= sum of minimum fire counts = 3*3 + 2*k + other. For n=7, k=3: minimum L
  = 3*3 + 2*3 = 15. The 6 steps in these 3 phases only account for 6 << 15.

  Wait, the 3 phases PLUS the t-fires partition ALL steps. So ALL steps are
  in SOME phase. The 3 phases together contain all L steps. Each phase has
  at least 2 steps (the binary fire + the t-fire). So L = sum of phase lengths.
  If all phases have length 2: L = 6. But L >= 2n = 14 for n=7. Contradiction.

  So WITH HFULL AND N>=7: not all phases can have length 2.
  Some phase has length > 2. Does it have a second-neighbor fire?

  Even if the long phase has LL/RR fires: the CHAIN argument in the Lean proof
  handles this by continuing to look at second-neighbor, third-neighbor, etc.
  Eventually the chain reaches procs far enough away that the last mover in
  the chain has no further neighbor firing before it, giving EC.

  With n >= 7: the chain can extend at most to distance floor(n/2) before
  wrapping around, hitting the other side. The chain produces EC at some
  intermediate proc.

  Actually, the simpler approach: with n >= 9 (the Lean constraint), there are
  enough procs between binary procs that the chain terminates.

LET ME NOW VERIFY COMPUTATIONALLY that the theorem holds for all test cases.
"""

from collections import Counter


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
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


def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)


def is_normal_form(J, K):
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True


def check_ec_anywhere(word, cycle, ms, n):
    """Check if EC exists at ANY processor."""
    ell = len(word)
    for p in range(n):
        pL = (p - 1) % n
        pR = (p + 1) % n
        for sv in range(ms[p]):
            mover = set()
            nonmover = set()
            for i in range(ell):
                if cycle[i][p] == sv:
                    triple = (cycle[i][pL], cycle[i][p], cycle[i][pR])
                    if word[i] == p:
                        mover.add(triple)
                    else:
                        nonmover.add(triple)
            if mover & nonmover:
                return True
    return False


def check_ec_at(word, cycle, ms, n, t):
    """Check EC at proc t."""
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    for sv in range(ms[t]):
        mover = set()
        nonmover = set()
        for i in range(ell):
            if cycle[i][t] == sv:
                triple = (cycle[i][bL], cycle[i][t], cycle[i][bR])
                if word[i] == t:
                    mover.add(triple)
                else:
                    nonmover.add(triple)
        if mover & nonmover:
            return True
    return False


# Test with n=7 alternating and non-alternating configurations
test_cases = [
    (7, [2, 3, 2, 3, 2, 3, 3], "n=7 3bin", 24),
    (7, [3, 2, 3, 2, 3, 2, 3], "n=7 alt", 24),
]

for n, ms, label, max_len in test_cases:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    if not sandwiched:
        print(f"\n{label}: no sandwiched ternary")
        continue

    words = enumerate_mover_words(ms, n, max_len)
    total = 0
    all_nf_count = 0
    all_nf_ec_at_t = 0
    all_nf_ec_anywhere = 0
    all_nf_no_ec_anywhere = 0

    phase_len_gt2_clean = 0  # phase len > 2 and no LL/RR fires
    phase_len_gt2_dirty = 0  # phase len > 2 but LL/RR fires
    all_short = 0  # all phases len <= 2

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        total += 1
        ell = len(word)

        for t in sandwiched:
            bL = (t - 1) % n
            bR = (t + 1) % n
            LL = (t - 2) % n
            RR = (t + 2) % n

            t_fires = [i for i in range(ell) if word[i] == t]
            if not t_fires:
                continue

            phases = []
            for idx in range(len(t_fires)):
                s = t_fires[idx]
                a = t_fires[(idx - 1) % len(t_fires)]
                if s > a:
                    interior = list(range(a + 1, s))
                else:
                    interior = list(range(a + 1, ell)) + list(range(0, s))
                J = sum(1 for st in interior if word[st] == bL)
                K = sum(1 for st in interior if word[st] == bR)
                ll = sum(1 for st in interior if word[st] == LL)
                rr = sum(1 for st in interior if word[st] == RR)
                phases.append({'J': J, 'K': K, 'len': len(interior) + 1,
                              'LL': ll, 'RR': rr, 'a': a, 's': s, 'interior': interior})

            all_nf = all(is_normal_form(ph['J'], ph['K']) for ph in phases)
            if not all_nf:
                continue
            all_nf_count += 1

            # Check EC at t
            ec_t = check_ec_at(word, cycle, ms, n, t)
            if ec_t:
                all_nf_ec_at_t += 1

            # Check EC anywhere
            ec_any = check_ec_anywhere(word, cycle, ms, n)
            if ec_any:
                all_nf_ec_anywhere += 1
            else:
                all_nf_no_ec_anywhere += 1
                print(f"  NO EC ANYWHERE: word={word}, t={t}")
                for ph in phases:
                    print(f"    phase: J={ph['J']}, K={ph['K']}, len={ph['len']}, LL={ph['LL']}, RR={ph['RR']}")

            # Classify phases
            has_clean_long = False
            has_dirty_long = False
            for ph in phases:
                if ph['len'] > 2:
                    if ph['LL'] == 0 and ph['RR'] == 0:
                        has_clean_long = True
                    else:
                        has_dirty_long = True

            if has_clean_long:
                phase_len_gt2_clean += 1
            elif has_dirty_long:
                phase_len_gt2_dirty += 1
            else:
                all_short += 1

    print(f"\n{label}")
    print(f"  Total cycles: {total}")
    print(f"  All-NF at sandwiched t: {all_nf_count}")
    print(f"  EC at t: {all_nf_ec_at_t} ({100*all_nf_ec_at_t/max(1,all_nf_count):.1f}%)")
    print(f"  EC anywhere: {all_nf_ec_anywhere} ({100*all_nf_ec_anywhere/max(1,all_nf_count):.1f}%)")
    print(f"  NO EC anywhere: {all_nf_no_ec_anywhere}")
    print(f"  Has clean long phase: {phase_len_gt2_clean}")
    print(f"  Has dirty long phase (no clean): {phase_len_gt2_dirty}")
    print(f"  All phases short: {all_short}")
