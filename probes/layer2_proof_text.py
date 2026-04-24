#!/usr/bin/env python3
"""
========================================================================
LAYER 2: COMPLETE MATHEMATICAL PROOF
========================================================================

THEOREM (allNormalForm_false2):
  Let gc be a good cycle on a ring with n >= 9, >= 3 non-consecutive binary
  processors, sub-threshold product. Let t be a sandwiched ternary processor
  (m(left t) = m(right t) = 2, m(t) >= 3) with all procs firing (hfull),
  fc(t) >= 2, fc(t) < |cycle|. If every phase at t is normalForm (not
  dispatched by BothEven, ToggleFR, or ZeroSide), then hasEntryConflict gc.

PROOF (by contradiction: assume hnoEC):

  Notation:
  - bL = left(t), bR = right(t) are binary neighbors of t.
  - A "phase" is an interval (a, s] between consecutive t-fires.
  - J = intervalFireCount(bL, a, s), K = intervalFireCount(bR, a, s).
  - NormalForm means: NOT(Even J and Even K), NOT(J>=2 and K=0), NOT(J=0 and K>=2).

  ===== LEMMA 1: h_phase_le1 — J + K <= 1 per phase. =====

  Proof: By normalForm constraints:
    * If J = 0: then K = 1 (since (0,0) is both-even, excluded; and K>=2
      with J=0 is excluded by ZeroSide-R). So J+K = 1.
    * If K = 0: then J = 1 (symmetric). So J+K = 1.
    * If J >= 1 and K >= 1: we derive EC, contradicting hnoEC.

  Proof that J >= 1, K >= 1 gives EC:

    Let fL be the first bL-fire and fR the first bR-fire in [a, s).
    (These exist since J >= 1, K >= 1.)

    WLOG suppose fL fires first (fL_pos < fR_pos in the phase ordering).
    (The symmetric case fR first is identical.)

    Key fact: fL = a + 1.
    Proof: Step a fires t (definition of TernaryPhase). In a good cycle,
    the mover word is a walk on the ring: consecutive movers are ring-adjacent.
    moverAt(a) = t. So moverAt(a+1) in {bL, bR} (the ring neighbors of t).
    Since fL fires first: moverAt(a+1) = bL. Hence fL = a+1.

    Now apply ec_caseC_LR between fL = a+1 and fR:
    The interval (fL, fR) = (a+1, fR). In this interval:
      - No t fires (phase interior).
      - No bL fires (fL was the first, and if J=1 it's the only one; if J>=2,
        the next bL fire is after fR since fL fires first and J>=2 would
        require another bL in the phase, but we only need no bL in (fL, fR)).
        Actually for ec_caseC_LR we need no bL in [fL, fR), but fL fires bL
        and we're looking at (fL, fR). Wait, the Lean mk_ec_left uses:
        v < fL with no LL in [v, fL). But here we need a different formulation.

    Let me use the CORRECT ec_caseC_LR from the Lean code:
    ec_caseC_LR(gc, t, fL, fR, hfLm, hfRm, hfL_lt_fR, hno_t, hno_bR, hno_LL)
    where:
      - hno_t: no t in (fL, fR)
      - hno_bR: no bR in [fL, fR)  -- wait, this might need no bL in (fL, fR)

    Actually, let me look at the Lean ec_caseC_LR signature.

    The point is: between fL and fR, if no LL fires, then the boundary
    triple at bL is constant from fL to fR, and fL (mover for bL) shares
    its triple with fR (nonmover for bL).

    But fL fires bL, changing c[bL]. The triple AFTER fL's fire:
    c[bL](fL+1) = c[bL](fL) + 1 mod 2.
    Between fL+1 and fR: if no bL, no LL, no t fires, then:
    c[LL], c[bL], c[t] are all constant.
    Step fL+1 (nonmover for bL) has some triple T.
    Step fR (nonmover for bL) has the same triple T.

    But we need a MOVER step for bL with triple T. The mover step is fL,
    which has triple (c[LL](fL), c[bL](fL), c[t](fL)). The nonmover steps
    fL+1,...,fR have triple (c[LL](fL+1), c[bL](fL+1), c[t](fL+1)) =
    (c[LL](fL), c[bL](fL)+1, c[t](fL)). Different in the S coordinate.

    Hmm, this is the mover/nonmover at bL. The mover triple is the config
    BEFORE bL fires. The config at step fL (when bL is about to fire)
    has c[bL] = some value v. After firing: c[bL] = v+1 mod 2.

    For EC at bL: need a nonmover step with the same (L,S,R) triple as a
    mover step. The mover at fL has S = c[bL](fL) = v.
    The nonmover at fL+1 has S = c[bL](fL+1) = v+1 mod 2 != v.
    So these don't match.

    But there might be OTHER nonmover steps at S-level v.
    Any step k with c[bL](k) = v and moverAt(k) != bL is a nonmover at S=v.

    Between fL+1 and fR: c[bL] = v+1 (constant). So no nonmover at S=v here.

    Steps BEFORE fL in the phase: a+1 = fL, so only step a. Step a has
    c[bL](a) = some value. If c[bL](a) = v: step a is nonmover for bL at S=v.
    Mover at fL has triple (c[LL](fL), v, c[t](fL)).
    Nonmover at a has triple (c[LL](a), v, c[t](a)).
    But step a fires t, so c[t](a) != c[t](a+1) = c[t](fL). So R coord differs.

    Steps AFTER fR in the phase: between fR and s. These have c[bL] = v+1 (if
    no more bL fires) or v (if another bL fires).

    This is getting very detailed. Let me use a DIFFERENT approach.

    ALTERNATIVE APPROACH for J >= 1, K >= 1: EC at t itself.

    In the mixed phase: both bL and bR fire at least once.
    The mover at step s fires t. The mover triple at t is
    (c[bL](s), c[t](s), c[bR](s)).

    The L coordinate c[bL](s) = c[bL](a) + J mod 2 (J fires of bL toggle it).
    The R coordinate c[bR](s) = c[bR](a) + K mod 2 (K fires of bR toggle it).
    c[t](s) = c[t](a+1) = c[t](a) + 1 mod m(t) (step a fires t, after that
    t doesn't fire until step s).

    Wait: c[t](a) = v' (before t fires). Step a fires t: c[t](a+1) = v' + 1 = v.
    Throughout the phase: c[t] = v. At step s: c[t](s) = v. Mover fires t,
    transitioning to v+1.

    Mover triple at t: (c[bL](s), v, c[bR](s)) = ((L0+J)%2, v, (R0+K)%2)
    where L0 = c[bL](a+1), R0 = c[bR](a+1).

    Nonmover at step a+1: ((L0, v, R0)). Since (J mod 2, K mod 2) != (0,0)
    (normalForm), (L0+J, R0+K) != (L0, R0) mod 2. So mover != nonmover at a+1.

    But there are MANY other nonmover steps at S=v. As bL and bR fire, the
    (L, R) values at t evolve. The walk visits intermediate (L, R) values.

    For EC at t: the mover endpoint ((L0+J)%2, (R0+K)%2) must equal
    some intermediate value.

    The intermediate values form a walk on {0,1}^2 starting at (L0, R0).
    Each bL fire toggles L. Each bR fire toggles R. J+K total toggles.

    Claim: with J >= 1 and K >= 1, the walk visits at least 3 distinct
    (L,R) values (including start and end). Since the endpoint differs
    from the start: at least 2 values. The walk passes through an
    intermediate value that might match the endpoint.

    Actually, with J=1, K=1: walk starts at (L0, R0), toggles L and R
    in some order. Two orderings:
    (a) toggle L first: (L0, R0) -> (1-L0, R0) -> (1-L0, 1-R0) = endpoint.
    (b) toggle R first: (L0, R0) -> (L0, 1-R0) -> (1-L0, 1-R0) = endpoint.

    In case (a): intermediate is (1-L0, R0). Endpoint is (1-L0, 1-R0).
    These differ in R. Intermediate != endpoint. No EC from this walk.

    In case (b): intermediate is (L0, 1-R0). Endpoint is (1-L0, 1-R0).
    These differ in L. Intermediate != endpoint. No EC from this walk.

    So with J=1, K=1: the walk visits exactly 3 distinct values, and
    the endpoint doesn't match any intermediate. No EC at t.

    But EC exists SOMEWHERE (verified 100%). Where?

    It must be at a DIFFERENT processor. The Lean code's ec_caseC approach
    finds EC at bL or bR or LL or RR, not at t.

    Let me reconsider the ec_caseC_LR approach properly.

  CORRECT caseC argument:
    fL = a+1 (first binary fire, fires bL). fR > fL (first bR fire).

    ec_caseC_LR checks: between fL and fR, no LL fires in this interval?
    If no LL in [fL, fR): the boundary triple at bL is:
      (c[LL], c[bL], c[t])
    Between fL and fR: no LL fires (c[LL] constant), no bL fires (fL done,
    next bL fire if any is after fR), no t fires (phase). So c[LL], c[bL], c[t]
    are ALL constant from step fL to step fR.

    Wait: bL fires at fL, changing c[bL]. So c[bL] CHANGES at step fL.
    After fL: c[bL] is constant until the next bL fire.

    Triple at bL at step fL (BEFORE bL fires): (c[LL](fL), c[bL](fL), c[t](fL)).
    Step fL fires bL: c[bL](fL+1) = c[bL](fL) + 1 mod 2.
    Triple at bL at step fL+1 (AFTER bL fires): (c[LL](fL), c[bL](fL)+1, c[t](fL)).

    Between fL+1 and fR: no LL, bL, t fire. Triple constant.
    Step fR: triple = (c[LL](fL), c[bL](fL)+1, c[t](fL)). Step fR fires bR,
    which is nonmover for bL.

    Step fL: triple = (c[LL](fL), c[bL](fL), c[t](fL)). Step fL fires bL (mover).

    The S coordinates differ: c[bL](fL) vs c[bL](fL)+1. NOT EC.

    But: there might be a step BEFORE fL in the phase (i.e., step a) where
    the triple at bL matches fR's triple.

    Step a: moverAt(a) = t. Triple at bL = (c[LL](a), c[bL](a), c[t](a)).
    Step fR: triple at bL = (c[LL](fL), c[bL](fL)+1, c[t](fL)).
    c[LL](a) = c[LL](fL) (no LL fires between a and fL = a+1).
    c[bL](a) = c[bL](fL) = c[bL](a+1-1) = c[bL](a) (bL doesn't fire between a and fL=a+1).
    Wait: fL = a+1. Between a and fL: only step a fires t. No bL fires.
    So c[bL](a) = c[bL](fL). And c[bL](fL)+1 = c[bL](a)+1.
    c[t](a) != c[t](fL) (step a fires t, incrementing c[t]).
    c[t](fL) = c[t](a+1) = c[t](a) + 1 mod m(t).

    Triple at bL at step a: (c[LL](a), c[bL](a), c[t](a)).
    Triple at bL at step fR: (c[LL](a), c[bL](a)+1, c[t](a)+1).
    Both S and R differ. NOT EC.

    So: caseC_LR doesn't directly give EC. The existing Lean code must use
    a DIFFERENT formulation. Let me look at ec_caseC_LR more carefully.

  OK, I think I've been misunderstanding the approach. Let me re-read
  the ec_caseC_LR in the Lean code.
"""

# Let me look at the actual EC that arises in mixed phases
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


def find_ec_details(word, cycle, ms, n):
    """Find first EC: proc, step pair."""
    ell = len(word)
    for p in range(n):
        pL = (p - 1) % n
        pR = (p + 1) % n
        for sv in range(ms[p]):
            mover_steps = []
            nonmover_steps = []
            for i in range(ell):
                if cycle[i][p] == sv:
                    if word[i] == p:
                        mover_steps.append(i)
                    else:
                        nonmover_steps.append(i)
            for ms_ in mover_steps:
                mt = (cycle[ms_][pL], cycle[ms_][p], cycle[ms_][pR])
                for nms in nonmover_steps:
                    nt = (cycle[nms][pL], cycle[nms][p], cycle[nms][pR])
                    if mt == nt:
                        return p, ms_, nms, mt
    return None

# Trace mixed phase EC in detail
n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24
sandwiched = [p for p in range(n) if ms[p] >= 3
              and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]

words = enumerate_mover_words(ms, n, max_len)

ec_at_proc = Counter()
count = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in sandwiched:
        bL = (t - 1) % n
        bR = (t + 1) % n
        t_fires = sorted(i for i in range(ell) if word[i] == t)
        if not t_fires:
            continue

        has_mixed = False
        for idx in range(len(t_fires)):
            s = t_fires[idx]
            a = t_fires[(idx - 1) % len(t_fires)]
            if s > a:
                inter = list(range(a + 1, s))
            else:
                inter = list(range(a + 1, ell)) + list(range(0, s))
            J = sum(1 for st in inter if word[st] == bL)
            K = sum(1 for st in inter if word[st] == bR)
            if is_normal_form(J, K) and J >= 1 and K >= 1:
                has_mixed = True
                break

        if not has_mixed:
            continue

        result = find_ec_details(word, cycle, ms, n)
        if result:
            p, ms_, nms, mt = result
            rel = 'self' if p == t else ('bL' if p == bL else ('bR' if p == bR else
                   ('LL' if p == (t-2)%n else ('RR' if p == (t+2)%n else f'dist{min(abs(p-t),n-abs(p-t))}'))))
            ec_at_proc[rel] += 1
            count += 1

            if count <= 3:
                print(f"Mixed phase at t={t}, EC at p={p} ({rel})")
                print(f"  mover step {ms_}: mover={word[ms_]}, triple={mt}")
                print(f"  nonmover step {nms}: mover={word[nms]}, triple=same")
                print(f"  word = {word[:24]}...")

print(f"\nEC location for mixed phases:")
for rel, cnt in sorted(ec_at_proc.items(), key=lambda x: -x[1]):
    print(f"  {rel}: {cnt}")
