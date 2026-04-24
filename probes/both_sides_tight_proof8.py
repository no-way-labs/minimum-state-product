#!/usr/bin/env python3
"""
PART 8: Find the EC mechanism for sorry 1077.

In the sorry case, the chain is fully tight. The interior is a sweep.
The EC must come from the interaction between THIS phase and OTHER phases.

Key idea: in a fully tight chain phase, the boundary triple at some proc
is the same at two steps in DIFFERENT phases. This gives a cross-phase EC.

Specifically: if the phase interior is a sweep [bR, ..., bL] going left,
then at the END of the phase (step s fires t), the config has a specific
state. At the START of the NEXT phase, the config is this state + t-fire.
If two consecutive phases have the same sweep structure, then some
boundary triple repeats.

Let me trace the exact EC mechanism.
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


# Focus on a SPECIFIC sorry case
n, ms = 5, [2, 3, 2, 3, 2]
# word=(0, 4, 3, 2, 1, 0, 4, 3, 2, 1, 0, 4, 3, 4, 0, 1)
# t=1, phase [15, 4): interior [0,1,2,3] movers [0,4,3,2]
word = (0, 4, 3, 2, 1, 0, 4, 3, 2, 1, 0, 4, 3, 4, 0, 1)
cycle = build_cycle(ms, n, word)
ell = len(word)

print("Full cycle trace:")
for st in range(ell):
    c = cycle[st]
    m = word[st]
    # Boundary triples for ALL procs
    triples = {}
    for p in range(n):
        pL = (p-1) % n
        pR = (p+1) % n
        triples[p] = (c[pL], c[p], c[pR])
    print(f"  step {st:2d}: fires {m}, config={c}, "
          f"triples: {' | '.join(f'{p}:{triples[p]}' for p in range(n))}")

print()
print("Entry conflicts:")
for p in range(n):
    pL = (p-1) % n
    pR = (p+1) % n
    mover_triples = {}
    nonmover_triples = {}
    for st in range(ell):
        tr = (cycle[st][pL], cycle[st][p], cycle[st][pR])
        if word[st] == p:
            mover_triples[tr] = mover_triples.get(tr, []) + [st]
        else:
            nonmover_triples[tr] = nonmover_triples.get(tr, []) + [st]
    for tr in mover_triples:
        if tr in nonmover_triples:
            print(f"  proc {p}: triple={tr}, mover_steps={mover_triples[tr]}, "
                  f"nonmover_steps={nonmover_triples[tr]}")

# Let me understand the sorry structure.
# t=1, bL=0, bR=2, LL=4, RR=3, LLL=3, RRR=4.
# Phase [15, 4): step 15 fires 1 (t). Step 4 fires 1 (t).
# Interior: steps 0,1,2,3. Movers: 0(bL), 4(LL), 3(RR), 2(bR).
# J = 1 (bL fires once), K = 1 (bR fires once).

# Sorry 1121: fL at start (step 0 fires bL=0), fR later (step 3 fires bR=2).
# RR=3 fires at step 2 (before bR at step 3). Tight: RR at step 2 = 3-1.
# RRR=4 fires at step 1 (before first RR at step 2). So sorry 1121 applies.

# The sorry needs hasEntryConflict gc.
# Looking at the EC list:
# proc 0: (0,0,2) at steps 10 (mover) and 15 (nonmover)
# proc 0: (0,1,2) at steps 14 (mover) and 11 (nonmover)
# proc 1: (0,2,0) at steps 15 (mover) and 10 (nonmover)
# proc 3: (0,0,1) at steps 2 (mover) and 13 (nonmover)
# proc 4: (0,0,1) at steps 1 (mover) and 14 (nonmover)
# proc 4: (0,1,1) at steps 13 (mover) and 2 (nonmover)

# EC at proc 3 between steps 2 and 13: step 2 fires proc 3, step 13 fires proc 3.
# Wait, step 13 fires proc 4 (from word[13]=4). So step 13 is nonmover for 3.
# Step 2 fires proc 3. Mover for 3.
# Triple (0,0,1) matches.

# Step 2 is in the sorry phase [15, 4). Step 13 is NOT in this phase.
# Phase structure: t fires at 4, 9, 15.
# Phases: [15, 4), [4, 9), [9, 15).
# Step 13 is in phase [9, 15). Interior of [9, 15): steps 10,11,12,13,14.

print()
print("Phase structure at t=1:")
t = 1
t_fires = sorted(i for i in range(ell) if word[i] == t)
print(f"t-fires: {t_fires}")
for idx in range(len(t_fires)):
    s = t_fires[idx]
    a = t_fires[(idx-1) % len(t_fires)]
    if s > a:
        interior = list(range(a+1, s))
    else:
        interior = list(range(a+1, ell)) + list(range(0, s))
    movers = [word[st] for st in interior]
    bL, bR = 0, 2
    J = sum(1 for m in movers if m == bL)
    K = sum(1 for m in movers if m == bR)
    print(f"  phase [{a}, {s}): interior={interior}, movers={movers}, J={J}, K={K}")

# Phase [9, 15): interior [10,11,12,13,14], movers [0,4,3,4,0].
# This is NOT a full sweep. It has J=2 (proc 0 fires twice), K=0.
# So THIS phase has J+K = 2 with J >= 2, K = 0.
# This is the ec_caseA case, which should produce EC directly.

# EC at proc 3 between step 2 (in full-sweep phase) and step 13 (in J=2 phase):
# The EC comes from the interaction between a full-sweep phase and a J=2 phase.

# But from the Lean perspective: h_phase_le1 is proved by showing that
# for EACH phase, if J+K >= 2, derive EC.
# The J=2,K=0 phase would be handled by the J>=2 branch (ec_caseA).
# The J=1,K=1 full-sweep phase would be handled by the sorry branch.
# Since the proof is universal (for all phases), it doesn't matter which
# phase produces the EC — as long as SOME phase does.

# But the sorry is inside the universal quantifier! The proof structure is:
#   h_phase_le1 : forall phase, J+K <= 1 := by
#     intro phase
#     by_contra h_gt  -- assume J+K >= 2
#     -- ... produce EC
#
# For the sorry phase (J=1, K=1, but h_gt says J+K >= 2... wait, J+K = 2,
# which IS >= 2. So h_gt holds. We need to derive False.)
#
# The proof can use `hnoEC` to derive the EC from ANY phase.
# In particular: we don't need to construct EC from THIS specific phase.
# We can construct EC from a DIFFERENT phase.
#
# But that's circular: to use a different phase's EC, we'd need h_phase_le1
# for that phase (to know it has J+K <= 1 and therefore triggers EC).
# That's what we're trying to prove.
#
# Actually: no. The sorry is in the proof of h_phase_le1 for THIS phase.
# We can't use h_phase_le1 for other phases (it's not proved yet).
# But we CAN use the hypotheses that are available: hnoEC, hbL, hbR, etc.
#
# The Lean proof derives EC using mk_ec_left/mk_ec_right, which construct
# EC at specific procs using configVal_eq_of_noFire_between.
# These don't depend on h_phase_le1. They directly produce hasEntryConflict.
#
# So for the sorry: we need to construct hasEntryConflict gc using:
# - The phase structure (fR, fL, fLL, wmax3, and the LLL fire)
# - configVal_eq_of_noFire_between
# - The fact that moverAt is a walk on the ring graph

# KEY IDEA: Don't extend the chain. Instead, construct EC at LLL.
#
# We have:
# - fR fires bR at phase.a
# - Some step k fires LLL in [phase.a, fLL)
# - fLL fires LL in [phase.a, fL)
#
# For EC at LLL: we need a mover step (fires LLL) and a nonmover step with
# same boundary triple at LLL.
#
# Boundary triple at LLL = (left(LLL), LLL, right(LLL)) = (left^4 t, LLL, LL).
#
# At step k (mover for LLL): triple = (config[k][left^4 t], config[k][LLL], config[k][LL]).
#
# Need a nonmover step with same triple.
#
# Between phase.a and k: what fires?
# - phase.a fires bR (which is right(t), far from LLL for n >= 5)
# - Steps phase.a+1 through k-1: could fire various procs
#
# For n=5: LLL = (t-3)%5. If t=1: LLL = 3. left^4(t) = (1-4)%5 = 2 = bR!
# LL = 4. So triple at LLL=3 is (left^4(t)=2, LLL=3, LL=4) = (bR, RR, LL).
# Hmm, at n=5 everything wraps around.
#
# For n >= 8 (the Lean hypothesis): LLL = left^3(t), which is distance 3 from t.
# left^4(t) is distance 4 from t. LL = left^2(t) is distance 2.
# bR = right(t) is distance 2 from LL (going the other way).
# So left^4(t) and right(t) are distance n-5 apart. For n >= 8: distance >= 3.
# They are NOT neighbors.
#
# So: between phase.a (fires bR) and step k (fires LLL):
# bR is NOT a neighbor of LLL (for n >= 8, distance from bR to LLL is n-4 >= 4).
# So bR firing at phase.a does NOT change the boundary triple at LLL.
#
# Between phase.a and k: the only things that change the triple at LLL are
# fires of left^4(t), LLL, or LL.
# - LLL: first fire is k. No LLL fires before k.
# - LL: first fire is fLL > k. No LL fires before fLL.
# - left^4(t): might fire. If not: triple preserved from phase.a to k.
#
# If left^4(t) doesn't fire in [phase.a, k): EC at LLL between phase.a and k.
# At phase.a: fires bR != LLL (nonmover for LLL). At k: fires LLL (mover).
# Same triple. EC at LLL.
#
# If left^4(t) fires: the sorry extends deeper.
#
# But for n >= 8: left^4(t) is a DIFFERENT proc from bR.
# And we need to check: does bR firing at phase.a affect left^4(t)?
# bR is right(t). left^4(t) is at distance 4 from t (going left).
# Distance from bR to left^4(t) on ring = 4+1 = 5 (going around).
# For n >= 8: 5 < n, and distance = min(5, n-5) = 5 for n >= 10, 3 for n=8.
# At n=8: distance = min(5, 3) = 3. So bR is NOT a neighbor of left^4(t). Good.

# So for n >= 8: between phase.a and k:
# - No LLL fires (k is first)
# - No LL fires (fLL is first)
# - left^4(t) might fire -> that's the next chain level
#
# The chain case split: does left^4(t) fire in [phase.a, k)?
# If no: EC at LLL.
# If yes: does left^5(t) fire before first left^4(t)? Etc.
#
# The chain goes: LLL -> left^4(t) -> left^5(t) -> ... -> bR.
# When it reaches bR: bR fires at phase.a. Phase.a is the START of the interval.
# So bR's fire is at the boundary, not in the interior of the chain interval.
# Actually, the chain interval shrinks: [phase.a, k), [phase.a, k2), ...
# where k, k2, ... are first fires of successively outward procs.
# Since bR fires at phase.a: bR's fire is NOT in [phase.a+1, anything).
# Hmm, but the interval includes phase.a: [phase.a, k).
# bR fires at phase.a. Is phase.a in [phase.a, k)? Yes!
# So bR DOES fire in the interval. The chain reaches bR and "terminates"
# because bR has already fired (at phase.a).

# When the chain reaches bR (going left from LLL, wrapping around):
# The chain says: bR fires at phase.a. Its first fire is at phase.a.
# The next proc in the chain is right(bR) = right^2(t) = RR.
# Does RR fire in [phase.a, first_bR_fire = phase.a)? Empty interval!
# So "no fire" at bR, with first_idx = phase.a.

# For EC: we need a nonmover step for bR before phase.a.
# But [phase.a - 1] fires t (step a, the t-fire before the phase).
# t = right(bR)? No, left(bR) = t. right(bR) = RR = right^2(t).
# Wait: bR = right(t). left(bR) = t. right(bR) = right^2(t).
# So step a fires t = left(bR). Firing left(bR) changes the triple at bR!
# So step a does NOT have the same triple as phase.a at bR.

# Hmm. The chain termination at bR doesn't give a clean EC because the
# step before phase.a fires a neighbor of bR.

# BUT: does the chain even REACH bR for n >= 8?
# Chain from LLL: LLL, left^4(t), left^5(t), ..., wraps around to bR.
# Number of procs in chain from LLL to bR (going left): n - 4.
# For n = 8: 4 procs. For n = 9: 5 procs.

# The chain can extend at most until first_idx = 0 (no more room).
# Each extension decreases first_idx by at least 1.
# Starting from first_idx of LLL's first fire (which is somewhere in the interior).

# Interior length for a J=1, K=1 phase: at minimum,
# phase.a, ..., s-1 has at least 3 steps (bR fire + something + bL fire).
# But for n >= 8: much longer.

# I think the fundamental issue is: for n >= 8 with the sorry conditions,
# the chain from LLL doesn't extend all the way to bR.
# It terminates earlier because some intermediate proc doesn't fire in
# the shrinking interval.

# Let me check at n=7 (closest to n=8 that we can enumerate).

print("\n" + "="*70)
print("DETAILED CHAIN TRACE AT n=7")
print("="*70)

n7, ms7 = 7, [2, 3, 2, 3, 2, 3, 3]
words7 = enumerate_mover_words(ms7, n7, 24)

# Find first sorry case at n=7
for word in words7:
    cycle = build_cycle(ms7, n7, word)
    if cycle is None or not is_wrap_adjacent(word, n7):
        continue
    ell = len(word)

    sandwiched = [p for p in range(n7) if ms7[p] >= 3
                  and ms7[(p-1)%n7] == 2 and ms7[(p+1)%n7] == 2]

    for t in sandwiched:
        bL = (t-1) % n7
        bR = (t+1) % n7
        LL = (t-2) % n7
        RR = (t+2) % n7
        LLL = (t-3) % n7

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

            movers = [word[st] for st in interior]
            fR_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)
            fL_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)

            # Check sorry 1077: fR at start
            if fR_idx == 0 and fL_idx > 0:
                ll_pos = [i for i in range(fL_idx) if word[interior[i]] == LL]
                if ll_pos and ll_pos[-1] == fL_idx - 1:
                    first_ll = ll_pos[0]
                    if any(word[interior[i]] == LLL for i in range(first_ll)):
                        # SORRY 1077 HIT
                        print(f"\nSorry 1077: word={word[:20]}...")
                        print(f"  t={t}, bL={bL}, bR={bR}, LL={LL}, RR={RR}, LLL={LLL}")
                        print(f"  Phase [{a_step}, {s_step})")
                        print(f"  Interior movers: {movers}")

                        # Detailed chain trace from LLL
                        print(f"\n  Chain from LLL={LLL} going LEFT:")
                        current = LLL
                        current_first = None
                        for i in range(len(interior)):
                            if word[interior[i]] == current:
                                current_first = i
                                break

                        chain_detail = []
                        while current_first is not None:
                            next_proc = (current - 1) % n7
                            # Find first fire of next_proc in interior[0:current_first)
                            next_first = None
                            for i in range(current_first):
                                if word[interior[i]] == next_proc:
                                    next_first = i
                                    break

                            # Find last fire of next_proc before current_first
                            last_next = None
                            for i in range(current_first-1, -1, -1):
                                if word[interior[i]] == next_proc:
                                    last_next = i
                                    break

                            tight = last_next is not None and last_next == current_first - 1
                            chain_detail.append({
                                'proc': current,
                                'first_fire_idx': current_first,
                                'next_proc': next_proc,
                                'next_fires': next_first is not None,
                                'tight': tight,
                            })

                            print(f"    proc {current}: first fire at int[{current_first}]"
                                  f" = step {interior[current_first]}, "
                                  f"next_proc={next_proc}, "
                                  f"next_fires={next_first is not None}, "
                                  f"tight={tight}")

                            if not tight or next_first is None:
                                if next_first is None:
                                    print(f"    -> {next_proc} doesn't fire before int[{current_first}]")
                                else:
                                    print(f"    -> Gap: last {next_proc} at int[{last_next}], "
                                          f"current at int[{current_first}]")
                                break

                            current = next_proc
                            current_first = next_first

                        # Show EC for this cycle
                        print(f"\n  Entry conflicts in cycle:")
                        for p in range(n7):
                            pL = (p-1) % n7
                            pR = (p+1) % n7
                            mt = {}
                            for st in range(ell):
                                tr = (cycle[st][pL], cycle[st][p], cycle[st][pR])
                                if word[st] == p:
                                    mt[tr] = st
                                elif tr in mt:
                                    ph = 'this_phase' if st in interior else 'other'
                                    print(f"    EC at {p}: m_step={mt[tr]}, nm_step={st} ({ph})")
                                    break

                        # Only show first example
                        raise StopIteration

try:
    pass
except StopIteration:
    pass
