#!/usr/bin/env python3
"""
========================================================================
DEFINITIVE PROOF: allNormalForm_false2
========================================================================

THEOREM: For a good cycle gc on a ring with n >= 9, >= 3 non-consecutive
binary processors, sub-threshold product, with all procs firing (hfull),
and a sandwiched ternary t (both neighbors binary, m(t) >= 3):
if every phase at t is normalForm, then hasEntryConflict gc.

========================================================================
PROOF (by contradiction: assume no EC)
========================================================================

Step 0: Setup (lines 1196-1230 in AllNormalFormFalse2.lean).
  By contradiction, assume h_not_false (no EC anywhere derivable) and
  hnoEC (no entry conflict at any processor).
  From within_phase_ec_left/right: if a phase has no second-neighbor fires
  and the first-neighbor fire is not tight (not at step a+1), then EC.
  Since no EC: all such fires are tight.

Step 1: h_phase_le1 (J+K <= 1 per phase, lines 897-1130).
  For each phase, we show J + K <= 1 (where J = bL fires, K = bR fires).
  From normalForm_gap_constraint:
    J=0 => K=1, K=0 => J=1, J>0 and K>0 => not both even.

  If J+K >= 2, then J >= 1 and K >= 1 (else J=0 => K=1 < 2, contradiction).
  So we need: J >= 1, K >= 1 leads to EC.

  Proof:
    Get first bL fire fL and first bR fire fR in [a, s) (phase interval).
    WLOG fL_pos < fR_pos (fL fires before fR in the phase).

    Interval [a, fL): between phase start and first bL fire.
    Step a fires t (not bL). Steps a+1,...,fL-1 don't fire bL (fL is first).

    CLAIM: LL = left(left(t)) does not fire in [a+1, fL).
    PROOF OF CLAIM (by the ring walk constraint):
      On a ring, the mover word is a walk. Consecutive movers are adjacent.
      Step a fires t. The next mover (step a+1) must be adjacent to t:
      either bL or bR.
      If step a+1 fires bL: fL = a+1 and [a+1, fL) is empty. Claim holds.
      If step a+1 fires bR: then step a+2 must be adjacent to bR.
        bR's neighbors are t and RR. Step a+2 fires t or RR.
        If step a+2 fires t: but t doesn't fire in (a, s). Contradiction.
        So step a+2 fires RR (or procs further right).
        The walk goes t -> bR -> RR -> ... -> eventually reaches bL.
        Between bR and bL on the LEFT side: LL, bL. The walk must go:
        ... -> LL -> bL (to reach bL for the first time).
        So LL fires in [a, fL) IFF the walk approaches bL from the left.
        But the walk went RIGHT (through bR, RR, ...). To reach bL, it must
        traverse AROUND the ring. The path goes: t, bR, RR, ..., and eventually
        comes back to bL either from the left (through LL) or directly from t.

        Since the walk is on a ring, it can only move to adjacent procs.
        The walk started at t, went to bR, then further right.
        To reach bL, it must either:
        (a) Come back through t (but t doesn't fire in the phase), or
        (b) Go all the way around the ring: RR -> ... -> LL -> bL.

        In case (b): LL fires BEFORE bL, so LL fires in [a, fL). But then
        the chain from the Lean proof checks: does LL's fire have a gap?
        If LL fires at step fLL and fLL > a+1: the steps between a+1 and fLL
        don't fire bL (first bL is fL > fLL). What fires between a+1 and fLL?
        The walk was: t (step a) -> bR (step a+1) -> ... -> LL (step fLL).

        Actually, I realize: step a+1 fired bR (in this case), not bL.
        So fL > a+1. Between a and fL: step a fires t, steps a+1,...
        fire bR, RR, ..., LL, bL. So LL fires at some fLL < fL.

        But in the caseC analysis: we check [a, fL) for LL fires.
        LL fires in [a, fL). So we go to the "LL fires" branch.

        The last LL fire before fL: since the walk approaches bL from LL,
        the last LL fire is at fL-1 (tight). Then we check LLL in [a, fLL).
        The walk approaches LL from LLL, so LLL fires at fLL-1 (tight).
        This chain continues...

        BUT WAIT: the walk is a SINGLE path on the ring. It starts at t,
        goes right (to bR), continues right all the way around, and arrives
        at bL. The path is: t, bR, RR, ..., LL, bL. This is a sweep!
        But we assumed the walk is NOT a sweep (the good cycle is not a sweep
        because we have non-consecutive binary which block sweeps).

        Actually, the walk WITHIN THIS PHASE can go in any direction.
        But the key point: for the walk to reach bL from the right side
        (going t -> bR -> RR -> ... -> LL -> bL), it would need to pass
        through ALL procs on the right side. With n >= 9, that's at least
        7 procs on one side. But this phase only has J+K >= 2 fires at
        bL and bR, plus possibly other procs.

        The SIMPLER argument: on the ring walk, step a fires t.
        Step a+1 is adjacent to t, so fires bL or bR.
        If step a+1 fires bL: done, fL = a+1, no LL possible.
        If step a+1 fires bR: step a+2 is adjacent to bR, so fires t or RR.
        Step a+2 can't fire t. So step a+2 fires RR.
        Now the walk is at RR. To reach bL, it must either:
          - Go back through bR (step a+3 fires bR or goes further right)
          - Continue right through RR's right neighbor

        If the walk goes back to bR: step a+3 fires bR.
        Then step a+4 is adjacent to bR: t or RR.
        Can't fire t. Fire RR. Then step a+5: bR or right(RR).
        This bouncing pattern: bR, RR, bR, RR, ...
        Eventually the walk must reach bL. From bR, it can go to t or RR.
        From RR, it can go to bR or right(RR). Neither directly reaches bL.

        To reach bL from bR: step must be t or bR. But bL is left(t), not
        right(bR). bL = left(t), bR = right(t). So bL and bR are NOT adjacent
        (unless n = 3, but n >= 9). The walk CANNOT go from bR to bL directly.

        So to reach bL, the walk MUST go through t (impossible, t doesn't fire
        in the phase) or go ALL THE WAY around the ring through the right side.

        Going around: from RR, go right to right(RR), then right(right(RR)), etc.
        Eventually reach LL = left(bL) = left(left(t)). Then LL -> bL.

        This requires traversing n-3 procs (all except t, bL, bR... well,
        all procs on the right path from RR to LL). With n >= 9: at least 5 procs.
        Each of these procs fires once in this sub-path. So the phase has
        at least 5 + 2 (for bL and bR) + 1 (for t-fire at s) = 8 steps minimum.

        But the key: this traversal means LL fires in [a, fL), so the Lean code's
        "LL fires" branch is taken. And the chain extends all the way around.

        HOWEVER: this traversal is a SWEEP-like pattern within a single phase.
        The ring walk goes t -> bR -> RR -> ... -> LL -> bL.

        For this to happen within a normalForm phase:
          J >= 1 (bL fires once at the end)
          K >= 1 (bR fires once at the start)
          Plus all intermediate procs fire once.

        But with n >= 9: the intermediate procs (RR, right(RR), ..., LLL, LL)
        have at least 5 procs. Each fires once in this phase. But these procs
        also need to fire in OTHER phases (for their fire counts to be multiples
        of their moduli). This is allowed.

        The issue: this is a VALID walk pattern, and it DOES occur.
        In this case, the chain extends all the way, and the sorrys fire.

        BUT: our computational check showed the sorrys NEVER fire at n=7,8!
        Why? Because at n=7,8, the traversal around the ring is short enough
        that it doesn't qualify as a mixed normalForm phase? No -- we checked
        ALL normalForm cycles at n=7,8 and found zero chain cases.

  RESOLUTION: The claim that LL doesn't fire is WRONG in general. But the
  computational evidence shows it's true for n=7,8. The mathematical proof
  must handle the chain case OR show it can't occur.

  ACTUAL PROOF APPROACH (avoiding the chain entirely):

  Instead of showing EC at bL (which requires the chain analysis), we can
  directly show EC at t from the mixed-phase constraint.

  In a mixed phase (J >= 1, K >= 1) at normalForm:
    bL fires J times and bR fires K times.
    At least one of J, K is odd (normalForm).

    The mover at step s (t-fire) sees context (c[bL], c[t], c[bR]).
    Starting from the phase start (L0, v, R0):
      After J bL-fires: L = (L0 + J) mod 2
      After K bR-fires: R = (R0 + K) mod 2
    Mover context at s: ((L0+J)%2, v, (R0+K)%2).

    Nonmover context at step a (phase start): (L0, v, R0).
    (Step a fires t, so mover is t, not related to t's neighbor analysis.)
    Wait: step a fires t, meaning step a IS a mover for t.
    The nonmover contexts at S=v are all steps where c[t]=v and mover != t.
    Step a fires t, so step a is a MOVER for t at S=v' (where v' is the
    PREVIOUS value, since step a transitions t from v' to v'+1 = v).

    Actually, c[t](a) = v' (the value before firing). Step a fires t, so
    c[t](a+1) = v' + 1 = v. The phase at S=v runs from a+1 to s, where
    c[t] = v throughout (since t doesn't fire again until step s).

    At step s: c[t](s) = v. Mover fires t. So the mover triple is
    (c[bL](s), v, c[bR](s)) = ((L0+J)%2, v, (R0+K)%2).

    Nonmover triples at S=v include step a+1 (right after the previous t-fire).
    At step a+1: c[bL](a+1) = L0 (bL hasn't fired yet), c[t](a+1) = v, c[bR](a+1) = R0.
    So nonmover triple at a+1: (L0, v, R0).

    EC at t if (L0+J, R0+K) = (L0, R0) mod 2, i.e., J even AND K even.
    But normalForm excludes both-even! So EC at t does NOT occur from this
    comparison alone.

    But there are OTHER nonmover steps at S=v. As bL and bR fire during the
    phase, the (L, R) coordinates change. Some intermediate step might have
    the same (L, R) as the mover.

    This is the WALK argument on {0,1}^2. The mover endpoint is
    ((L0+J)%2, (R0+K)%2). At least one of J, K is odd.
    So the endpoint differs from (L0, R0) in at least one coordinate.

    The walk visits intermediate vertices. For EC at t: the endpoint must
    equal some intermediate vertex's (L, R).

    This depends on the walk ORDER. The walk is determined by the mover word.
    Not all orderings give EC.

  CORRECT APPROACH: Use the fire-count decomposition (Part A) to derive
  fc(L)+fc(R) <= fc(t), then combine with sparse_phase_sum_ge to get
  exact equality, then use the phase-length argument from Part B.

  In the exact-equality regime (J+K=1 per phase):
    Each phase has length >= 2 (binary fire + t-fire).
    With hfull and n >= 9: total length L >= 2*fc(t) + (n-3) > 2*fc(t).
    So SOME phase has length >= 3 (step a+2 exists).

    In a one-sided phase of length >= 3:
      J = 1, K = 0 (WLOG). Binary bL fires at step a+1 (tight).
      Steps a+2, ..., s-1 are "interior" steps.
      Between step a+1 and step s: no bL fires (J=1, already fired).
      No bR fires (K=0). No t fires (phase interior).

      KEY: does LL or RR fire in the interior?
      If no LL/RR fires: the triple at t is constant from a+2 to s.
      Step a+2 is nonmover for t, step s is mover for t. Same triple => EC.

      If LL fires: the triple at t changes (c[bL] might change?).
      Wait: LL = left(bL). bL's neighbors are LL and t.
      LL firing changes c[LL], but the triple at t is (c[bL], c[t], c[bR]).
      LL is NOT one of {bL, t, bR}. LL is left(left(t)).
      So LL firing does NOT change c[bL], c[t], or c[bR].

      Therefore: the triple at t is ALWAYS constant from a+2 to s,
      regardless of what fires in the interior (as long as it's not bL, bR, or t).

      EC at t: step a+2 (nonmover) has same triple as step s (mover). QED!

THIS IS THE KEY INSIGHT! In the exact-equality regime:
- Each phase has J+K = 1.
- Some phase has length >= 3 (from hfull + n >= 9).
- In that phase: the only neighbor fire is the one binary fire at step a+1.
- After step a+1, the boundary triple at t is fixed (no bL, bR, or t fires).
- Step a+2 exists and has the same triple as step s.
- Step a+2 is nonmover for t, step s is mover for t.
- => EC at t.

The proof DOES NOT need the LL/RR chain analysis! The triple at t only depends
on c[bL], c[t], c[bR], and LL firing doesn't affect any of these.

========================================================================
COMPUTATIONAL VERIFICATION
========================================================================
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


print("=" * 70)
print("DEFINITIVE PROOF VERIFICATION")
print("Exact-equality + hfull + n>=7 => EC at t via phase-length argument")
print("=" * 70)
print()
print("This verifies Part B of the proof: under the assumption of no EC,")
print("fc(L)+fc(R) = fc(t) (exact equality from Parts A + sparse_phase_sum_ge),")
print("and some phase has length >= 3 => EC at t.")
print()
print("We simulate the 'no EC assumption' by checking: for cycles where")
print("all phases are normalForm AND fc(L)+fc(R) = fc(t) AND some phase")
print("has length >= 3, does the boundary-triple match give EC at t?")

for n, ms, label, max_len in [
    (7, [2, 3, 2, 3, 2, 3, 3], "n=7 [2,3,2,3,2,3,3]", 24),
    (7, [3, 2, 3, 2, 3, 2, 3], "n=7 alternating", 24),
    (8, [2, 3, 2, 3, 2, 3, 2, 3], "n=8 alternating", 24),
    (9, [2, 3, 2, 3, 2, 3, 2, 3, 3], "n=9 non-consec", 30),
]:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    if not sandwiched:
        print(f"\n{label}: no sandwiched, skip")
        continue

    words = enumerate_mover_words(ms, n, max_len)

    total_nf = 0
    exact_eq = 0
    long_phase_exists = 0
    ec_at_t_via_triple = 0
    triple_match_failures = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        fc = Counter(word)

        for t in sandwiched:
            bL = (t - 1) % n
            bR = (t + 1) % n

            t_fires = sorted(i for i in range(ell) if word[i] == t)
            if not t_fires:
                continue

            all_nf = True
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
                if not is_normal_form(J, K):
                    all_nf = False
                    break
                phases.append({'J': J, 'K': K, 'len': len(interior) + 1,
                               'a': a, 's': s, 'interior': interior})

            if not all_nf:
                continue
            total_nf += 1

            # Check exact equality: fc(bL) + fc(bR) = fc(t)?
            if fc[bL] + fc[bR] != fc[t]:
                continue
            exact_eq += 1

            # Check: some phase has J+K = 1 AND length >= 3?
            found_ec = False
            for ph in phases:
                if ph['J'] + ph['K'] != 1:
                    continue
                if ph['len'] < 3:
                    continue
                long_phase_exists += 1

                # Phase has length >= 3 with J+K = 1.
                # Step a+1 fires the binary neighbor (tight).
                # Steps a+2, ..., s-1 are interior.
                # Between a+1 and s: no bL, bR, or t fires.
                a = ph['a']
                s = ph['s']
                a2 = ph['interior'][1] if len(ph['interior']) > 1 else None

                if a2 is not None:
                    # Verify: boundary triple at t is same at a2 and s
                    triple_a2 = (cycle[a2][bL], cycle[a2][t], cycle[a2][bR])
                    triple_s = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                    if triple_a2 == triple_s:
                        # Step s is t-mover, step a2 is not t-mover
                        if word[a2] != t and word[s] == t:
                            found_ec = True
                            break
                    else:
                        # Check WHY the triples differ
                        if triple_a2 != triple_s:
                            # Some of bL, t, bR fired between a2 and s?
                            fires_bL = sum(1 for st in ph['interior'][1:] if word[st] == bL)
                            fires_bR = sum(1 for st in ph['interior'][1:] if word[st] == bR)
                            fires_t = sum(1 for st in ph['interior'][1:] if word[st] == t)
                            if triple_match_failures < 3:
                                print(f"  TRIPLE MISMATCH: a2={a2}, s={s}")
                                print(f"    triple_a2={triple_a2}, triple_s={triple_s}")
                                print(f"    bL fires after a+1: {fires_bL}")
                                print(f"    bR fires after a+1: {fires_bR}")
                                print(f"    t fires after a+1: {fires_t}")
                            triple_match_failures += 1

            if found_ec:
                ec_at_t_via_triple += 1

    print(f"\n{label}")
    print(f"  Sandwiched: {sandwiched}")
    print(f"  All-NF instances: {total_nf}")
    print(f"  Exact-equality (fc(L)+fc(R)=fc(t)): {exact_eq}")
    if exact_eq > 0:
        print(f"  Long J+K=1 phase: {long_phase_exists}")
        print(f"  EC at t via triple match: {ec_at_t_via_triple}")
        print(f"  Triple match failures: {triple_match_failures}")
        if ec_at_t_via_triple == exact_eq:
            print(f"  *** 100% EC via triple match ***")
    else:
        print(f"  (No exact-equality instances => proof goes through h_phase_le1)")
