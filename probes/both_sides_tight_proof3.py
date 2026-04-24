#!/usr/bin/env python3
"""
PART 3: Prove WHY both-sides-tight (sorry 1012) is impossible,
and find the proof pattern for sorrys 1077/1121.

=== SORRY 1012: Both-sides-tight impossibility ===

Setup:
- Phase [a+1, s) at sandwiched ternary t (neighbors bL, bR binary)
- J >= 1 (bL fires in phase), K >= 1 (bR fires in phase)
- fL = first bL fire, fL > a+1
- fR = first bR fire, fR > a+1
- Last LL fire before fL is at step fL-1 (LL tight to fL)
- Last RR fire before fR is at step fR-1 (RR tight to fR)

Claim: This configuration is impossible.

Proof sketch:
- WLOG fL < fR (symmetric otherwise).
- Between a+1 and fL: no bL fires (fL is first), no t fires (phase).
  The step at fL-1 fires LL (tight).
- Between a+1 and fR: no bR fires (fR is first), no t fires (phase).
  The step at fR-1 fires RR (tight).
- Since fL < fR: the LL fire at fL-1 is BEFORE the RR fire at fR-1.
  Also: fL-1 < fL < fR, so fL-1 < fR-1 (since fL < fR => fL-1 < fR-1).

- Now: between a+1 and fR: we have LL at fL-1, bL at fL, then ... RR at fR-1, bR at fR.
  What fires in [fL+1, fR-2]? Steps fL+1, ..., fR-2 fire procs other than t, bL, bR
  (fL was first bL, fR was first bR, t doesn't fire in phase).

  But also: LL fires at fL-1 and RR fires at fR-1. What about the steps between fL and fR-1?
  Steps fL+1, ..., fR-2 fire procs that are not t, bL, bR. They could be LL, RR, or others.

Actually, the key constraint is simpler. Let me think about what step a+1 fires.

Wait — if fL > a+1 AND fR > a+1, then step a+1 fires some proc that is NOT t, bL, or bR.
But step a fires t (previous t-fire). Step a+1 must fire a neighbor of step a's mover = t.
So step a+1 fires a neighbor of t on the ring... but this is a WALK on the ring graph.
The mover word is a walk: word[i+1] must be adjacent to word[i] on the ring.

So word[a] = t, word[a+1] must be adjacent to t = bL or bR.
But fL > a+1 means word[a+1] != bL, and fR > a+1 means word[a+1] != bR.
But word[a+1] must be bL or bR (ring-adjacent to t).

CONTRADICTION! If word[a] = t, then word[a+1] in {bL, bR}. But if fL > a+1 and fR > a+1,
then word[a+1] != bL and word[a+1] != bR. Impossible.

This is the proof! The walk constraint forces the step after t to fire bL or bR.
"""

# Verify this argument computationally
print("="*70)
print("SORRY 1012: PROOF VIA WALK CONSTRAINT")
print("="*70)
print()
print("Claim: If word[a] = t (sandwiched ternary), then word[a+1] in {bL, bR}.")
print("This is because the mover word is a walk on the ring graph,")
print("so consecutive movers must be adjacent on the ring.")
print("The neighbors of t on the ring are exactly bL and bR.")
print()
print("Therefore: fL > a+1 AND fR > a+1 is IMPOSSIBLE.")
print("(Since word[a+1] must be bL or bR, either fL = a+1 or fR = a+1.)")
print()
print("This means sorry 1012 is vacuously true: the condition never holds.")
print()

# Verify on all examples
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

# Check: for every good cycle word, for every sandwiched t,
# the step after each t-fire is always bL or bR.
print("Verifying walk constraint on all good cycles...")
print()

for n, ms, max_len in [(5, [2,3,2,3,2], 18), (7, [2,3,2,3,2,3,3], 24)]:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    words = enumerate_mover_words(ms, n, max_len)
    violations = 0
    total_t_fires = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        for t in sandwiched:
            bL = (t-1) % n
            bR = (t+1) % n
            t_fires = [i for i in range(ell) if word[i] == t]
            for tf in t_fires:
                total_t_fires += 1
                next_step = (tf + 1) % ell
                if word[next_step] not in (bL, bR):
                    violations += 1
                    print(f"  VIOLATION: n={n}, word={word}, t={t}, tf={tf}, "
                          f"next={word[next_step]}")

    print(f"n={n}, ms={ms}: {total_t_fires} t-fires checked, {violations} violations")

print()
print("="*70)
print("SORRY 1012 PROOF COMPLETE")
print("="*70)
print()
print("The walk constraint on the ring graph forces word[a+1] in {bL, bR}.")
print("Since TernaryPhase.a = a+1 (step after previous t-fire),")
print("and fL/fR are first bL/bR fires with phase.a <= fL.val < s.val:")
print("  phase.a itself fires bL or bR, so min(fL, fR) = phase.a.val.")
print("  Therefore fL > phase.a AND fR > phase.a is impossible.")
print("  QED.")

print()
print("="*70)
print("NOW: SORRY 1077/1121 — THE CHAIN EXTENSION")
print("="*70)
print()
print("Sorry 1077: fR = phase.a (first step fires bR), fL > phase.a.")
print("  Chain: LL tight to fL, LLL fires before first LL.")
print()
print("Sorry 1121: fL = phase.a (first step fires bL), fR > phase.a.")
print("  Chain: RR tight to fR, RRR fires before first RR.")
print()
print("The chain argument needs to continue: at the chain end,")
print("either the next-outward proc doesn't fire (EC at chain end),")
print("or the chain extends further.")
print()
print("Key: the chain must terminate because:")
print("  1. The ring has n processors.")
print("  2. Each chain step fires a different processor.")
print("  3. The chain extends through consecutive processors on the ring.")
print("  4. After at most n-3 steps, the chain wraps around to bR (or bL).")
print("  5. At that point, we have bR firing TWICE (once in chain, once as first fire)")
print("     which gives a double-fire contradiction or EC.")
print()

# Now let's understand the actual chain structure more precisely.
# For sorry 1121 at t, the phase interior starts with bL, and the chain
# goes RIGHT: bR -> RR -> RRR -> ...
#
# The chain is: step phase.a fires bL.
# Then at some point, the right chain fires: ..., RRR, ..., RR, ..., bR.
# The chain of tight fires going backwards from bR:
#   step fR fires bR
#   step fR-1 fires RR (tight to fR)
#   Before RR: first RR fire is fRR, and RRR fires before fRR
#   So the interior looks like: bL, ..., RRR_fire, ..., fRR(=RR), ..., fR-1(=RR), fR(=bR)
#
# The sorry: LLL fires before first LL. The existing code already handled:
# - No LLL: EC at LL (triple preserved)
# - LLL fires: sorry (chain continues)
#
# To discharge sorry: continue the chain. After LLL fires, check left^4(t).
# If left^4(t) doesn't fire: EC at LLL.
# If left^4(t) fires: continue. Eventually, the chain from the left hits
# the chain from the right, or wraps around.
#
# In the Lean proof: we need a GENERAL chain termination argument.
# The simplest approach: INDUCTION on the distance to the next binary proc.
#
# Actually, the simplest fix for the sorry is a ONE-LEVEL deeper case split.
# The sorry at 1077: LLL fires in [a, fLL).
# Just do the SAME argument at LLL:
#   find first LLL fire, check if left^4(t) fires before it.
#   If not: EC at LLL (configVal_eq_of_noFire_between).
#   If yes: the chain extends to left^4(t).
#
# At n >= 8 with 3 non-consecutive binary:
# The distance between consecutive binary procs is at least 2 on each side.
# From t: bL (binary, dist 1), LL (ternary, dist 2), LLL (?, dist 3).
# With 3 non-consecutive binary on a ring of 8: arcs of length >= 2.
# The binary procs are at positions with gaps of at least 2.
# From sandwiched t: bL (binary), LL (could be ternary or binary).
# If LL is ternary: chain continues through LL to LLL.
# If LL is binary: impossible since bL is binary and non-consecutive means
# no two adjacent binary. Wait — bL is binary, LL = left(bL). If LL is binary,
# then bL and LL are adjacent binary — violating non-consecutive.
#
# So LL must be ternary (or higher). Similarly for RR.
# What about LLL = left(LL)? LL is ternary. LLL could be binary.
# If LLL is binary: the chain from left reaches a binary proc.
# Binary procs fire exactly 2 times. The chain used one fire (LLL fires once).
# This constrains the phase severely.
#
# At n=8 with 3 non-consecutive binary at positions {0, 3, 6}:
# t=1 (sandwiched by 0 and 2), bL=0(B), bR=2(T)... wait, bR must be binary too.
# "Sandwiched" means BOTH neighbors are binary.
# With 3 non-consecutive binary on ring of 8: {0,3,6} gives arcs 0-3-6-0
# of lengths 3, 3, 2. Procs: 0(B),1(T),2(T),3(B),4(T),5(T),6(B),7(T).
# Sandwiched ternary: proc p with ms[p-1]=2, ms[p+1]=2.
# p=1: left=0(B), right=2(T). NOT sandwiched (right is ternary).
# p=7: left=6(B), right=0(B). Sandwiched!
# p=2: left=1(T), right=3(B). Not sandwiched.
# Only p=7 is sandwiched with arcs of length 3,3,2.
#
# For n=8 with binary at {0,2,5}: arcs 0-2-5-0, lengths 2,3,3.
# Procs: 0(B),1(T),2(B),3(T),4(T),5(B),6(T),7(T).
# Sandwiched: p=1 (left=0(B), right=2(B)). Yes!
# Also: no others.
# At t=1: bL=0(B), bR=2(B), LL=7(T), RR=3(T), LLL=6(T), RRR=4(T).
# left^4 t = 5(B), right^4 t = 5(B). They MEET at 5!

print("For n=8, binary at {0,2,5}, t=1:")
print("  Chain left:  bL=0(B), LL=7(T), LLL=6(T), left^4=5(B)")
print("  Chain right: bR=2(B), RR=3(T), RRR=4(T), right^4=5(B)")
print("  Both chains meet at proc 5 (binary)!")
print()
print("The chains grow from opposite sides and MUST meet.")
print("When they meet at a proc p:")
print("  - p fires in BOTH chains. But p fires only a few times total.")
print("  - If p is binary: fires 2 times total. Being in both chains")
print("    means p fires at least once for each chain = at least 2 times")
print("    in the phase. But a binary proc fires exactly 2 times in the")
print("    entire cycle, so both fires are in this one phase.")
print("    This is extremely constraining.")
print()

# The INDUCTIVE argument: extend the chain until it terminates.
# At each step, either:
# (a) The next-outward proc doesn't fire -> EC at current proc
# (b) The next-outward proc fires -> chain extends
#
# Since the ring has n procs and the chain extends one proc per step,
# after at most floor(n/2) steps from each side, the chains meet.
#
# The KEY insight for the Lean proof: we don't need to handle arbitrary
# chain depth. We just need ONE more level of case-split beyond what the
# current code does.
#
# Current code handles: LL tight to fL, checks LLL.
#   - No LLL: EC at LL. DONE.
#   - LLL fires: sorry.
#
# Fix: when LLL fires, apply the same pattern to LLL:
#   find first LLL fire (fLLL), find last left^4(t) fire before fLLL.
#   - No left^4(t): EC at LLL.
#   - left^4(t) tight to fLLL: continue chain... but at this depth,
#     for n >= 8, the chain is already 3 procs deep from one side.
#     The other side (fR = phase.a fires bR, then RR, RRR, ...)
#     has used at most 1 step (bR at start).
#     With n >= 8: left chain depth 3 + right chain depth 1 = 4 procs used.
#     That's half the ring. The next step on either chain would overlap.
#
# ACTUALLY: For the Lean sorry, we just need to show hasEntryConflict gc.
# We don't need the chain to terminate at a specific proc.
# We just need to find SOME EC in the cycle.
#
# The deepest approach: prove the chain ALWAYS terminates by finding EC.
# For the Lean formalization: a recursive/inductive proof that scans
# outward from t, at each step producing either EC or extending the chain.
# The chain is bounded by n, so the recursion terminates.

print("="*70)
print("SUMMARY: PROOF STRUCTURE")
print("="*70)
print()
print("1. SORRY 1012: Both fL > phase.a AND fR > phase.a is IMPOSSIBLE.")
print("   Proof: walk constraint. word[a] = t, so word[a+1] in {bL, bR}.")
print("   phase.a = a+1, so word[phase.a] in {bL, bR}.")
print("   This means fL = phase.a or fR = phase.a.")
print("   SORRY 1012 IS VACUOUSLY TRUE.")
print()
print("2. SORRY 1077/1121: Chain extends one more level.")
print("   The fix: apply mk_ec_left/mk_ec_right one level deeper.")
print("   At the deeper level (LLL for 1077, RRR for 1121):")
print("   - Find first fire of the deeper proc in the interval")
print("   - Check if its outer neighbor fires before it")
print("   - If no: EC at the deeper proc (configVal_eq_of_noFire_between)")
print("   - If yes: chain extends AGAIN. For finite ring, eventually terminates.")
print()
print("   For the Lean code: the simplest fix is a FINITE case split.")
print("   With n >= 8: the chain can extend at most 3 steps from each side")
print("   (3 + 3 = 6 < 8 = n). After 3 steps, both chains have used 7 procs")
print("   total (t + 3 left + 3 right), and the meeting point gives EC.")
print()
print("   HOWEVER: the Lean proof should work for general n >= 8.")
print("   The clean approach: a recursive lemma that takes the chain depth")
print("   as a decreasing argument (Nat.rec or well-founded recursion on")
print("   the remaining ring distance).")
print()
print("   SIMPLEST FIX: Just repeat the case split ONE more time.")
print("   At depth 3 (left^3(t) = LLL fires before first LL):")
print("   - Find first LLL fire, check left^4(t).")
print("   - If left^4(t) doesn't fire: EC at LLL. Done.")
print("   - If left^4(t) fires (tight): at this point we've consumed")
print("     4 consecutive procs from the left (bL, LL, LLL, left^4(t))")
print("     and 1 from the right (bR at start). Total: 5 procs + t = 6.")
print("     For n >= 8: at least 2 more procs. But the right chain")
print("     hasn't extended beyond bR. The important point is that")
print("     left^4(t) = right^(n-4)(t). For n=8: right^4(t).")
print("     The two chains meet at n/2 from each side.")
print()
print("   THE REAL INSIGHT: We don't need arbitrary depth.")
print("   For the sorry at line 1077/1121: we just need ONE more")
print("   mk_ec_left/mk_ec_right call. The existing pattern is:")
print("     find last fire of next_proc -> gap or tight.")
print("     gap: EC. tight: sorry.")
print("   Extending by one level: at the tight case, find first fire,")
print("   look at its outer neighbor's fires in [a, first_fire).")
print("   This is EXACTLY what the code already does at lines 1044-1077,")
print("   but for one level shallower. Copy the pattern one more time.")
