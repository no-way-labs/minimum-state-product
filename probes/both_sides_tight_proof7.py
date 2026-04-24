#!/usr/bin/env python3
"""
PART 7: Finding a CONSTRUCTIVE EC for the sorry cases.

The sorry at line 1077 has these hypotheses:
  - fR = phase.a (step phase.a fires bR)
  - fL > phase.a (first bL fire is later)
  - wmax3 = fL - 1 (last LL fire before fL is tight: at step fL-1)
  - fLL = first LL fire in [fR, fL)
  - left^3(t) fires in [fR, fLL)

We need hasEntryConflict gc.

Key insight: we have SPECIFIC steps with known movers:
  phase.a fires bR (= right(t))
  fLL fires LL (= left(left(t)))
  fL fires bL (= left(t))
  step before fL fires LL (wmax3 = fL-1)

And between phase.a and fLL: left^3(t) fires somewhere.
Between fLL and wmax3=fL-1: possibly more LL fires.
At wmax3=fL-1: LL fires (tight).
At fL: bL fires.

Let me look for EC at a specific proc using the boundary-triple preservation.

For sorry 1077:
  - Step fR (= phase.a) fires bR. At this step, boundary triple at LL = (LLL, LL, bL).
  - Step fLL fires LL. Between fR and fLL: possibly LLL fires (we know it does).
  - So the triple at LL DOES change between fR and fLL (because LLL fires).

What about EC at LLL itself?
  - LLL fires at some step k in [fR, fLL).
  - First LLL fire = k. Boundary triple at LLL = (left^4 t, LLL, LL).
  - Does left^4 t fire in [fR, k)? If not: EC at LLL between fR and k.
  - That's exactly the Lean code's next case split.

But wait — for EC at LLL between fR and k:
  fR fires bR (not LLL, not left^4 t, not LL, since bR is right(t) and n >= 8).
  Need: left^4 t and LL don't fire in [fR, k).
  LL doesn't fire (fLL > k, and fLL is first LL fire, so no LL in [fR, fLL), and k < fLL).
  left^4 t: if it doesn't fire in [fR, k), then triple is preserved. EC at LLL.
  If it does: the chain extends.

The chain extension: left^4 t fires before first LLL fire.
Then left^5 t fires before first left^4 t fire. Etc.

Eventually, the chain reaches a proc that doesn't fire, or reaches the other side (bR).

Let me re-examine: does the chain ACTUALLY give EC at the termination point?
The issue was that at depth 0 (when first_idx = 0), step a fires t which IS a neighbor
of bL (right(bL) = t). So the triple changes.

But what about deeper chain procs?
At depth d, current_proc = left^(d+1)(t). For d >= 2:
  current_proc is at distance d+1 from t.
  left(current_proc) = left^(d+2)(t), right(current_proc) = left^d(t).
  t is NOT a neighbor of current_proc (since d+1 >= 3 and d >= 2, distance >= 3).

  Step a fires t. Between step a and current_proc's first fire at interior[first_idx]:
  Does any neighbor of current_proc fire?
  left(current_proc) = left^(d+2)(t): in the chain, this would be the NEXT outward proc.
    If this is the termination proc (next outward doesn't fire), then left(current_proc)
    doesn't fire in [a, first_idx). But first_idx could be > 0.

  right(current_proc) = left^d(t): this is the PREVIOUS chain proc, which fires at
    some step. If the chain is tight: right(current_proc) fires at first_idx + 1
    (one step after current_proc, going inward).

  So right(current_proc) DOES fire. Triple is not preserved from step a.

  But what about from step right(current_proc)'s fire? After right(current_proc) fires:
  config at right(current_proc) changes. The triple at current_proc changes.
  Between the last fire of right(current_proc) BEFORE first_idx and first_idx:
  if right(current_proc) doesn't fire again, the triple is preserved.

  The last fire of right(current_proc) before first_idx: in the chain, right(current_proc)
  = left^d(t) fires at some step after current_proc (tight chain).
  Wait, the tight chain means: left^(d+1)(t) fires at step first_idx,
  left^d(t) fires at step first_idx + 1 (tight: immediately after).
  So right(current_proc) fires AFTER current_proc, not before!

  Hmm, I'm getting the chain direction confused. Let me be very precise.

For sorry 1077 (chain goes LEFT):
  interior movers: step a+1 = phase.a fires bR = right(t).
  Then at some point: ..., LLL fires, ..., LL fires, ..., LL fires, bL fires.
  The first fires (going outward from t in the LEFT direction):
    bL fires at fL_int_idx
    LL fires at first LL (fLL_int_idx)
    LLL fires at first LLL (some idx < fLL_int_idx)
    ...

  The TIGHT chain means:
    step fL fires bL. step fL-1 fires LL (tight to bL).
    step first_LL-1 fires LLL? No — tight means LAST fire is at first-1.

  Actually, I need to be more careful. The "tight" condition is about LAST fires:
    Last LL fire before fL is at fL-1. This is about the step just before fL.
    But there could be EARLIER LL fires too.

  The chain in the Lean code works with FIRST fires and LAST fires:
    1. Find first bL fire (fL).
    2. Find last LL fire before fL. If NOT at fL-1: gap -> EC.
    3. If at fL-1 (tight): find first LL fire (fLL).
    4. Check if LLL fires before fLL. If not: EC at LL.
    5. If yes (LLL fires before fLL): sorry.

  For the sorry: LLL fires before first LL fire. The sequence in the interior:
    phase.a = bR, ..., LLL(first), ..., LL(first=fLL), ..., LL(last=fL-1), fL=bL, ..., s=t.

Actually, let me just construct the EC for each sorry case and check that
the construction ONLY uses locally available information.
"""

from collections import Counter


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
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


# At n=5, the sorry case has interior movers = [bR, LL, RR, bL] = [2, 4, 3, 0]
# (or reversed, depending on the specific phase).
# Wait, from the data: interior movers = [0, 4, 3, 2] for t=1.
# That's bL=0, LL=4, RR=3, bR=2.
# The sweep goes: 0(bL) -> 4(LL) -> 3(RR) -> 2(bR).
# This is a sweep going LEFT from t (through bL, then continuing left).

# For sorry 1121 at t=1: fL at start (interior[0] = bL), chain goes RIGHT.
# The chain from bR goes through 3(RR), 4(RRR=LL), 0(right^3=bL).
# At proc 0=bL: first fire at interior[0]. Chain says next outward is t=1.
# t doesn't fire -> "no fire at first_idx=0."

# The EC needs to come from the fact that the ENTIRE interior is a sweep.
# All non-t procs fire exactly once in this phase.

# CRUCIAL OBSERVATION: Look at EC at LL between two DIFFERENT phases.
# If every phase starts with the same proc (bL or bR), then across phases,
# the boundary triples at LL repeat.

# Actually, let me try a completely different approach.
# Instead of the chain argument, use EC at bR (= right(t)).
# bR fires at phase.a (first interior step).
# In the PREVIOUS phase: bR also fires (since fc(bR) >= 2 and phases cover all fires).
# The boundary triple at bR in the previous phase's bR-fire vs this phase's bR-fire:
# if they match, EC. If not, some neighbor changed.

# Hmm, that's the cross-phase domino argument. Complex.

# Let me instead look for a DIRECT construction.
# From the sorry hypotheses:
# fR = phase.a fires bR.
# Some step k < fLL fires LLL.
# fLL fires LL.
# fL fires bL.

# EC at LL between step fR (= phase.a, nonmover for LL) and step fLL (mover for LL):
# Need: (LLL, LL, bL) unchanged between fR and fLL.
# LLL fires at step k (between fR and fLL). So LLL value CHANGES. No good.

# EC at LLL between step fR and step k:
# Need: (left^4 t, LLL, LL) unchanged between fR and k.
# left^4 t: might fire. LL: doesn't fire (fLL > k, first LL = fLL).
# If left^4 t doesn't fire: EC at LLL.
# If left^4 t fires: chain extends.

# This is exactly the Lean case split. So the sorry asks: what when the chain extends?

# NEW IDEA: Instead of the chain, use EC at bR directly.
# Step phase.a fires bR.
# Boundary triple at bR: (t, bR, RR) = (left(bR), bR, right(bR)).
# left(bR) = t. right(bR) = RR = right^2(t).
# At step phase.a: mover is bR.
# Need a nonmover step with same (t, bR, RR) triple.
# Step s fires t (mover for t, nonmover for bR).
# Triple at step s: (t_val_at_s, bR_val_at_s, RR_val_at_s).
# Between phase.a and s: what changes?
# t fires at step s. bR fires at phase.a (already accounted).
# RR: fires at some point in the interior (since K >= 1... wait, K = number of bR fires.
# Actually in the sorry case: fR = phase.a fires bR, and K counts bR fires in [a, s).
# K >= 1 was assumed. So bR fires at least once. fR = phase.a counts as one bR fire.
# If K = 1: bR fires only at phase.a.
# If K > 1: bR fires again later.

# For the sorry case: the phase has J >= 1, K >= 1.
# In the full sweep case: J = 1, K = 1.

# Let me try: EC at bR between step s (nonmover for bR) and step phase.a (mover for bR).
# Step s fires t. Step phase.a fires bR.
# Between s and phase.a (going cyclically): only step a (= previous t-fire).
# wait, s is the t-fire at the END of this phase. Between s and next phase.a:
# it depends on the cycle structure.

# Actually, TernaryPhase has phase.a < phase.s. Step a is a nonmover for t,
# step s is a mover for t (fires t). phase.a = a+1 where a is previous t-fire.
# So step phase.a-1 = a fires t.

# For EC at t between step a (mover for t) and step phase.a (nonmover for t):
# Triple at t = (bL, t, bR).
# Step a fires t (mover). Step phase.a fires bR (nonmover for t).
# Between step a and phase.a = a+1: no steps in between.
# Config at phase.a = config at a + (t fired).
# t value changes. Triple differs. No EC.

# OK let me just find what WORKS computationally.

print("="*70)
print("CONSTRUCTIVE EC SEARCH FOR SORRY CASES")
print("="*70)

n, ms = 5, [2, 3, 2, 3, 2]
words = enumerate_mover_words(ms, n, 18)

ec_constructions = Counter()
sorry_count = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in [1, 3]:
        bL = (t-1) % n
        bR = (t+1) % n
        LL = (t-2) % n
        RR = (t+2) % n
        LLL = (t-3) % n

        t_fires = sorted(i for i in range(ell) if word[i] == t)
        if len(t_fires) < 2:
            continue

        for idx in range(len(t_fires)):
            s_step = t_fires[idx]
            a_step = t_fires[(idx-1) % len(t_fires)]
            if s_step > a_step:
                interior = list(range(a_step+1, s_step))
            else:
                interior = list(range(a_step+1, ell)) + list(range(0, s_step))
            if not interior:
                continue

            J = sum(1 for st in interior if word[st] == bL)
            K = sum(1 for st in interior if word[st] == bR)
            if J < 1 or K < 1:
                continue

            fL_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)
            fR_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)

            # Check sorry 1077: fR at start, fL later, LL tight, LLL fires
            if fR_int_idx == 0 and fL_int_idx > 0:
                ll_pos = [i for i in range(fL_int_idx) if word[interior[i]] == LL]
                if ll_pos and ll_pos[-1] == fL_int_idx - 1:
                    first_ll = ll_pos[0]
                    if any(word[interior[i]] == LLL for i in range(first_ll)):
                        sorry_count += 1

                        # Find the EC. Look at all (proc, mover_step, nonmover_step).
                        for p in range(n):
                            pL = (p-1) % n
                            pR = (p+1) % n
                            for m_st in range(ell):
                                if word[m_st] != p:
                                    continue
                                m_triple = (cycle[m_st][pL], cycle[m_st][p], cycle[m_st][pR])
                                for nm_st in range(ell):
                                    if word[nm_st] == p:
                                        continue
                                    nm_triple = (cycle[nm_st][pL], cycle[nm_st][p], cycle[nm_st][pR])
                                    if m_triple == nm_triple:
                                        # Found EC. Classify relationship to sorry-case phase.
                                        # Is m_st or nm_st in this phase?
                                        phase_set = set(interior) | {a_step, s_step}
                                        m_in = m_st in phase_set
                                        nm_in = nm_st in phase_set
                                        rel_p = (p - t) % n
                                        if rel_p > n//2: rel_p -= n
                                        ec_constructions[f'p_rel={rel_p}_m_in={m_in}_nm_in={nm_in}'] += 1
                                        break
                                else:
                                    continue
                                break
                            else:
                                continue
                            break

            # Check sorry 1121: fL at start, fR later, RR tight, RRR fires
            if fL_int_idx == 0 and fR_int_idx > 0:
                rr_pos = [i for i in range(fR_int_idx) if word[interior[i]] == RR]
                if rr_pos and rr_pos[-1] == fR_int_idx - 1:
                    first_rr = rr_pos[0]
                    RRR = (t+3) % n
                    if any(word[interior[i]] == RRR for i in range(first_rr)):
                        sorry_count += 1

                        for p in range(n):
                            pL = (p-1) % n
                            pR = (p+1) % n
                            for m_st in range(ell):
                                if word[m_st] != p:
                                    continue
                                m_triple = (cycle[m_st][pL], cycle[m_st][p], cycle[m_st][pR])
                                for nm_st in range(ell):
                                    if word[nm_st] == p:
                                        continue
                                    nm_triple = (cycle[nm_st][pL], cycle[nm_st][p], cycle[nm_st][pR])
                                    if m_triple == nm_triple:
                                        phase_set = set(interior) | {a_step, s_step}
                                        m_in = m_st in phase_set
                                        nm_in = nm_st in phase_set
                                        rel_p = (p - t) % n
                                        if rel_p > n//2: rel_p -= n
                                        ec_constructions[f'p_rel={rel_p}_m_in={m_in}_nm_in={nm_in}'] += 1
                                        break
                                else:
                                    continue
                                break
                            else:
                                continue
                            break

print(f"\nSorry cases: {sorry_count}")
print(f"\nEC constructions:")
for key in sorted(ec_constructions.keys()):
    print(f"  {key}: {ec_constructions[key]}")

# Now: the critical insight. The EC is always cross-phase.
# What if we don't need to find EC from the phase at all?
# What if the sorry case implies the phase has J+K = 2,
# and we can show J+K <= 1 by a DIFFERENT argument?

# Actually: the sorry is inside the proof of J+K <= 1.
# If J >= 1 AND K >= 1 AND the chain extends, we need EC.
# But the EC is cross-phase.

# ALTERNATIVE: Don't try to find EC within the sorry case.
# Instead, restructure the proof so that the chain extension STOPS EARLIER.

# At sorry 1077: LLL fires in [fR, fLL).
# Instead of continuing the chain, construct EC at LL differently.
# Between fR and fLL: LLL fires, but maybe there's a step where
# LL's triple is preserved DESPITE LLL firing.

# The triple at LL = (LLL_val, LL_val, bL_val).
# LLL fires at step k. So LLL_val changes at step k.
# But the EC could use the INTERVAL [k, fLL):
# After step k fires LLL: LLL_val changed.
# Between step k+1 and step fLL: does anything change at LL's triple?
# Need: no LLL, LL, bL fires in (k, fLL).
# LL doesn't fire (fLL is first LL fire).
# bL doesn't fire (fL > fLL, and fL is first bL fire).
# LLL: might fire again (k was first LLL, but there could be more).

# If LLL fires only once in [fR, fLL): then [k+1, fLL) has no triple changes.
# Step k+1 is a nonmover for LL. Step fLL is mover for LL.
# If k+1 < fLL (gap > 0): EC at LL.

# If k+1 = fLL (tight): LLL fires right before first LL fire. No gap.

# If LLL fires multiple times: find the LAST LLL fire before fLL.
# If that last fire is NOT at fLL-1: gap after it -> EC at LL.
# If tight (last LLL = fLL-1): same sorry condition but one level deeper.

# This is EXACTLY what the Lean code already does! The sorry IS the tight case.

# So the real question: in the sorry case (everything is tight all the way),
# how do we derive EC?

# THE ANSWER: We DON'T derive EC from within the phase.
# Instead, we show that the sorry conditions (full sweep phase) are
# IMPOSSIBLE when combined with the other hypotheses (all normal form,
# no EC, etc.)

# Specifically: if every phase at t has the sweep structure,
# then the cycle itself must have a very specific form.
# This form is inconsistent with "no EC."

# Let me check: in sorry cases, do ALL phases at t have J+K = 2?
print("\n" + "="*70)
print("PHASE PROFILE FOR SORRY-CASE CYCLES")
print("="*70)

for word in words[:200]:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in [1, 3]:
        bL = (t-1) % n
        bR = (t+1) % n
        LL = (t-2) % n
        LLL = (t-3) % n

        t_fires = sorted(i for i in range(ell) if word[i] == t)
        if len(t_fires) < 2:
            continue

        has_sorry = False
        phase_jks = []
        for idx in range(len(t_fires)):
            s_step = t_fires[idx]
            a_step = t_fires[(idx-1) % len(t_fires)]
            if s_step > a_step:
                interior = list(range(a_step+1, s_step))
            else:
                interior = list(range(a_step+1, ell)) + list(range(0, s_step))
            if not interior:
                phase_jks.append((0, 0))
                continue

            J = sum(1 for st in interior if word[st] == bL)
            K = sum(1 for st in interior if word[st] == bR)
            phase_jks.append((J, K))

            if J >= 1 and K >= 1:
                fL_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)
                fR_int_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)
                if fR_int_idx == 0 and fL_int_idx > 0:
                    ll_pos = [i for i in range(fL_int_idx) if word[interior[i]] == LL]
                    if ll_pos and ll_pos[-1] == fL_int_idx - 1:
                        first_ll = ll_pos[0]
                        if any(word[interior[i]] == LLL for i in range(first_ll)):
                            has_sorry = True

        if has_sorry:
            print(f"  word={word[:20]}..., t={t}, phases={phase_jks}")
            # Check if ALL phases have J+K <= 2
            if any(j+k > 2 for j, k in phase_jks):
                print(f"    *** Phase with J+K > 2!")
            break
