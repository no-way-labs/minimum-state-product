#!/usr/bin/env python3
"""
RA12: Prove CL ≤ 2n for zero-winding good cycles.

Key insight from the Lean codebase:
- next_mover_is_local: consecutive movers differ by at most 1 (left/self/right)
- So steps are exactly CW (+1), stay (0), or CCW (-1). No jumps.
- CL = cwSteps + staySteps + ccwSteps
- zeroWinding: totalDisplacement = 0, i.e., cwSteps - ccwSteps = 0
- So cwSteps = ccwSteps, and CL = 2*cwSteps + staySteps

The proof needs: CL ≤ 2n.

Approach: Think about edges and fire counts.

Fire count of proc p = number of times p appears in the mover word.
fc(p) ≥ 2 for all p.
sum fc(p) = CL.

cwMoveCountAt(p) = number of CW steps at edge (p, p+1)
  = number of steps where mover = p and next mover = right(p) = p+1.
ccwMoveCountAt(p) = number of CCW steps AT proc right(p)
  where mover = right(p) and next mover = p.

Wait, let me think about this more carefully via the Lean definitions:
- cwMoveCountAt(p): steps where mover = p and direction = CW
  That means: mover[k] = p and mover[k+1] = right(p)
- ccwMoveCountAt(p): steps where mover = p and direction = CCW
  That means: mover[k] = p and mover[k+1] = left(p)

Then:
  fc(p) = cwMoveCountAt(p) + ccwMoveCountAt(p) + stayMoveCountAt(p)

where stayMoveCountAt(p) = steps where mover = p and next mover = p.

And:
  cwStepCount = sum_p cwMoveCountAt(p)
  ccwStepCount = sum_p ccwMoveCountAt(p)
  stayStepCount = sum_p stayMoveCountAt(p)

Zero winding edge balance (from FCBound.lean):
  cwMoveCountAt(p) = ccwMoveCountAt(right(p)) for all p

This means: the number of CW crossings of edge (p, right p) equals
the number of CCW crossings of edge (p, right p).

So the NET flow through each edge is 0.

Now, key argument:

Claim: cwStepCount ≥ n under zero winding + fc ≥ 2 + cwStepCount > 0.

Proof attempt:
- cwStepCount = sum_p cwMoveCountAt(p)
- By edge balance: cwMoveCountAt(p) = ccwMoveCountAt(right(p))
- So cwStepCount = sum_p ccwMoveCountAt(right(p)) = sum_p ccwMoveCountAt(p) = ccwStepCount. ✓

Now, can we prove cwStepCount ≥ n?

For each proc p, fc(p) ≥ 2. So p fires at least twice.
When p fires, the next mover is left(p), p, or right(p).
So fc(p) = cwMoveCountAt(p) + ccwMoveCountAt(p) + stayMoveCountAt(p).

By edge balance: cwMoveCountAt(p) = ccwMoveCountAt(right(p)).

Hmm, the argument in the Lean sketch says "cwMoveCountAt(e) ≥ 1 for all edges".
If that were true, cwStepCount = sum cwMoveCountAt ≥ n, and then
CL = 2*cwStepCount + staySteps ≥ 2n + staySteps ≥ 2n.

But is cwMoveCountAt(p) ≥ 1 for all p? Why?

Think: for each proc p, fc(p) ≥ 2. Consider the first time p fires and the second
time p fires. Between these two firings, the mover must leave p's neighborhood and
come back. Since the mover moves by ±1 or 0 at each step, to leave p it must go
either left or right.

Actually, let's think about it differently. The mover word is a closed walk on the
cycle graph C_n (with self-loops). fc(p) ≥ 2 means vertex p is visited ≥ 2 times.

For vertex p: stayMoveCountAt(p) = number of stays at p = number of consecutive
(mover[k], mover[k+1]) = (p, p) pairs.

Each "run" at p is a maximal consecutive sequence of p's in the mover word.
Number of runs = number of times the mover enters p from outside + (1 if word starts at p).
Actually for a cyclic mover word, number of runs at p = number of transitions
(left(p)→p) + (right(p)→p) from outside.

WAIT. Let me think about the fire count vs. edge crossings differently.

Consider the walk on the path graph (ignoring the cyclic structure for a moment).
The mover word is a closed walk on C_n. At each step the walker goes left, stays, or right.

For a closed walk visiting every vertex at least twice:
  - Each edge must be crossed in both directions (to ensure the walk is closed)
  - Total displacement = 0

Actually, the fact that each vertex has fc ≥ 2 doesn't directly imply each edge is
crossed at least once. Consider n=5 and the walk 0,1,2,3,4,3,2,1,0,0 (length 10):
Edge (0,1) crossed CW once, CCW once. fc(0)=2, fc(1)=2, fc(2)=2, fc(3)=2, fc(4)=1.
But fc(4)=1, violating fc≥2.

Let me try: 0,1,2,3,4,3,2,1,0,1,0 (length 11). No, CL=11 not 2n=10.

With fc=2 for all procs: CL=2n=10. Each proc fires exactly twice. The mover word
is a closed walk of length 10 on C_5 visiting each vertex exactly twice.

Can this walk avoid crossing some edge?
Walk: 0,1,2,3,4,4,3,2,1,0 (length 10). Check fc: 0→2, 1→2, 2→2, 3→2, 4→2. ✓
CW crossings: (0,1)→1, (1,2)→1, (2,3)→1, (3,4)→1.
CCW crossings: (3,4)→1, (2,3)→1, (1,2)→1, (0,1)→1.
Edge (4,0): CW=0, CCW=0. NOT crossed!

But wait, is totalDisplacement = 0? Steps:
0→1: +1
1→2: +1
2→3: +1
3→4: +1
4→4: 0 (stay)
4→3: -1
3→2: -1
2→1: -1
1→0: -1
0→0 (wrap back to start): what's the step from config 9 (mover=0) to config 0 (mover=0)?
That's a STAY step.

Total displacement: 4(+1) + 1(0) + 4(-1) + 1(0) = 0. ✓ Zero winding!
cwSteps = 4, ccwSteps = 4, staySteps = 2.
CL = 10 = 2*5 = 2n. ✓

So CL = 2n BUT cwSteps < n (cwSteps = 4 < 5 = n).
Edge (4,0) is never crossed!

BUT: cwMoveCountAt(0) = 1, cwMoveCountAt(1) = 1, cwMoveCountAt(2) = 1, cwMoveCountAt(3) = 1, cwMoveCountAt(4) = 0.
So cwStepCount = 4, not 5.

This shows cwStepCount can be < n even with ZW + fc=2.
The stay steps compensate.

So the argument "cwMoveCountAt ≥ 1 for all p" is WRONG in general.

But CL = 2n is still true in this example because CL = 2*4 + 2 = 10 = 2*5.

The real question: is CL = 2n forced by fc=2 for all procs?
Answer: YES trivially! If fc(p) = 2 for all p, then CL = sum fc(p) = 2n.

So the proof strategy should be:
1. fc(p) ≥ 2 for all p (already proved in Step B)
2. CL = sum fc(p) ≥ 2n (already proved)
3. If any fc(p) ≥ 3, then CL ≥ 3 + 2(n-1) = 2n+1

Wait, but the claim is fc(p) = 2 for all p, and that's what we're TRYING to prove.
The proof goes: CL ≤ 2n (needed) + CL ≥ 2n + fc≥2 → fc=2.

So we need CL ≤ 2n independently of fc=2.

Let me reconsider. What if we don't know fc=2 yet, only fc≥2?
Then CL = sum fc ≥ 2n. We need CL ≤ 2n.

OK so the REAL question: given zero winding + cwStepCount > 0 + no safe + sub-threshold + ≥3 binary + n≥9,
prove CL ≤ 2n.

CL = 2*cwSteps + staySteps (from ZW).

So CL ≤ 2n ⟺ 2*cwSteps + staySteps ≤ 2n.

Approach: use the sub-threshold product bound.

Sub-threshold: product(ms) < 4*3^(n-2).
The number of distinct configs is CL (good cycle).
CL ≤ product(ms) (pigeonhole: each config is distinct and lives in the state space).
So CL ≤ product(ms) - 1 < 4*3^(n-2).

But 4*3^(n-2) is much larger than 2n for n≥9, so this doesn't give CL ≤ 2n directly.

Hmm, we need a tighter argument. Let me re-read the Lean sketch more carefully.
"""

# Let me think about this differently. The claim at line 25-32 says:
# "Product = Π m_i ≤ CL (good cycle length bound)."
# This is WRONG for general good cycles. CL can be much less than the product.
# Maybe the key insight is about BINARY processors.

# For binary procs (m=2): fc is even (cycle closure: binary toggles).
# fc ≥ 2 (from Step B). So fc ∈ {2, 4, 6, ...}.
# If a binary proc has fc = 4, it fires 4 times, cycling through 2 values:
#   v → v' → v → v' → v
# Each firing changes the value. After fc=4 firings, value returns to original. ✓
#
# Now: with ≥3 binary procs and fc ≥ 2, CL ≥ 2n.
# With fc(p) = 2 for binary p (m=2), the proc only uses 2 distinct configs.
# But the TOTAL number of distinct configs is CL = sum fc.
#
# Actually wait - the number of distinct configs is CL (good cycle: all configs distinct).
# Each config is a function from processors to states.
# CL distinct configs, each in the state space of size product(ms).
# So CL ≤ product(ms). But this doesn't help.

# The real approach must use the STRUCTURE of the walk more carefully.

# Let me think about what happens combinatorially.
# The mover word is a closed walk on C_n with steps ∈ {-1, 0, +1}.
# Zero winding: net displacement = 0.
# No safe: every vertex visited (fc > 0 for all p).
# fc ≥ 2 for all p: every vertex visited at least twice.
# CL = length of mover word = sum of fc.

# Key constraint I haven't used: the CONFIGS must be distinct.
# This means: the sequence of state tuples (c_0, c_1, ..., c_{CL-1}) are all different.

# For a binary proc p with fc(p) = k (even, ≥ 2):
#   p's value alternates: v, v', v, v', ...
#   At the k firings, the value changes k times.
#   Between consecutive firings of p, p's value is constant.
#   So p takes value v for some number of steps, then v' for some, etc.
#
# Now, if p has fc = 2: p fires at step a and step b.
#   Before step a: p has value v.
#   After step a: p has value v'.
#   After step b: p has value v.
#   So there are exactly 2 "phases" for p: one where p=v, one where p=v'.
#
# If p has fc = 4: p fires at steps a, b, c, d.
#   4 phases: v, v', v, v'.
#   Two phases have value v, two have value v'.
#   Within each phase, p's value is constant. For configs to be distinct,
#   the OTHER processors must distinguish configs within each phase.

# The sub-threshold constraint limits the total state space.
# With ≥3 binary procs, the state space is at most 2^3 * 3^(n-3) = 8*3^(n-3)
# when all non-binary are ternary. And 8*3^(n-3) < 4*3^(n-2) = 12*3^(n-3). ✓
# Actually product < 4*3^(n-2) means:
#   If we have exactly 3 binary and (n-3) ternary: product = 8*3^(n-3) < 12*3^(n-3). ✓
#   If we have 4 binary: product ≤ 16*3^(n-4) < 12*3^(n-3) = 36*3^(n-4). ✓ (since 16<36)

# So the state space has at most 4*3^(n-2) - 1 configs.
# CL ≤ state space size.
# But 4*3^(n-2) >> 2n for n ≥ 9, so this is not tight enough.

# I think the RIGHT approach is not about the state space size at all.
# It's about the structure of the walk.

# Let me think about it purely combinatorially on the walk graph.

print("="*70)
print("APPROACH: Walk structure + edge flow balance")
print("="*70)
print()
print("Given:")
print("  - Mover word is a closed walk on C_n")
print("  - Steps are +1, 0, -1 (CW, stay, CCW)")
print("  - Zero winding: cwSteps = ccwSteps")
print("  - fc(p) >= 2 for all p")
print("  - CL = sum fc(p)")
print()
print("Key: CL = 2*cwSteps + staySteps")
print("     CL = sum fc(p) >= 2n")
print()
print("Want: CL <= 2n")
print("  i.e., 2*cwSteps + staySteps <= 2n")
print()

# CRITICAL OBSERVATION:
# The edge flow balance (zeroWinding_cw_eq_ccw_right) says:
#   cwMoveCountAt(p) = ccwMoveCountAt(right(p))
# This means: at each edge, CW crossings = CCW crossings.
#
# Now consider the "local balance" at each vertex.
# For vertex p:
#   inflow = cwMoveCountAt(left(p)) + ccwMoveCountAt(p) + stayMoveCountAt(p)
#            [coming from left]        [coming from right]  [staying]
#   outflow = cwMoveCountAt(p) + ccwMoveCountAt(left(p)??) + stayMoveCountAt(p)
#
# Actually, this is the standard flow conservation for a closed walk.
# Inflow at p = outflow at p = fc(p).
#
# In the cyclic walk:
#   fc(p) = cwMoveCountAt(p) + ccwMoveCountAt(p) + stayMoveCountAt(p)
# where:
#   cwMoveCountAt(p) = # of (p → right(p)) transitions = CW exits from p
#   ccwMoveCountAt(p) = # of (p → left(p)) transitions = CCW exits from p
#   stayMoveCountAt(p) = # of (p → p) transitions = self-loops at p
#
# These count EXITS from p.
# And ENTRIES to p are:
#   CW entries: cwMoveCountAt(left(p))  [left(p) → p]
#   CCW entries: ccwMoveCountAt(right(p))  [right(p) → p]
#   Stay entries: stayMoveCountAt(p)  [p → p]
#
# In a closed walk, exits = entries for each vertex (conservation):
#   fc(p) = cwMoveCountAt(left(p)) + ccwMoveCountAt(right(p)) + stayMoveCountAt(p)
# (This should equal the exit count too.)
#
# By edge balance: cwMoveCountAt(q) = ccwMoveCountAt(right(q)) for all q.
# Set q = left(p): cwMoveCountAt(left(p)) = ccwMoveCountAt(p).
# Set q = p: cwMoveCountAt(p) = ccwMoveCountAt(right(p)).
#
# So entry count at p:
#   = cwMoveCountAt(left(p)) + ccwMoveCountAt(right(p)) + stayMoveCountAt(p)
#   = ccwMoveCountAt(p) + cwMoveCountAt(p) + stayMoveCountAt(p)
#   = fc(p). ✓ (consistent)

# This doesn't directly help. The key insight must come from a DIFFERENT constraint.

# Let me try the PIGEONHOLE approach on the binary processors' states.

# With ≥3 binary procs, consider the tuple of binary states.
# Each binary proc has 2 values. The binary state tuple has 2^k ≤ 2^n values
# (where k = number of binary procs).
#
# In the good cycle, consecutive configs differ at exactly one processor (the mover).
# When the mover is a non-binary proc, the binary state tuple is unchanged.
# When the mover is a binary proc p, one binary bit flips.
#
# The sequence of binary state tuples over the cycle is a closed walk on {0,1}^k
# where at each step, at most one bit changes (and it changes when mover is binary).
#
# The number of bit-flips = sum of fc(p) over binary p ≥ 2*k (since fc(p) ≥ 2 for each).
# Each bit flips an even number of times (cycle closure for binary).
#
# The binary state tuple REPEATS whenever the mover is non-binary AND the binary
# tuple was the same before. So the DISTINCT binary tuples ≤ 2^k.
#
# But distinct CONFIGS ≤ product(ms), and CL = number of distinct configs.
# This still doesn't help.

# BREAKTHROUGH ATTEMPT: The sub-threshold constraint on the PRODUCT
# combined with a counting argument on binary fire counts.

# Let me try a direct arithmetic argument.

# Sub-threshold: product(ms) < 4*3^(n-2).
# With ≥3 binary procs: at most n-3 non-binary procs, each with m_p ≥ 3.
# Binary procs have m_p = 2.
# product = 2^b * ∏_{non-binary} m_p where b ≥ 3.
# Sub-threshold: 2^b * ∏ m_p < 4*3^(n-2).
# If b = 3: 8 * ∏ m_p < 4*3^(n-2) = 12*3^(n-3).
# So ∏_{non-binary} m_p < (12/8)*3^(n-3) = 1.5*3^(n-3).
# Since each non-binary m_p ≥ 3 and there are n-3 of them:
# ∏ m_p ≥ 3^(n-3). And 3^(n-3) < 1.5*3^(n-3). ✓
# So each non-binary m_p = 3 exactly (since if any > 3, product ≥ 4*3^(n-4) and
# 8*4*3^(n-4) = 32*3^(n-4) vs threshold 12*3^(n-3) = 36*3^(n-4). Need 32 < 36. ✓
# But actually 8*3^(n-4)*4 = 32*3^(n-4) < 36*3^(n-4). So ONE quaternary is allowed!
#
# If b ≥ 4: product ≤ 2^4 * 3^(n-4) = 16*3^(n-4) vs 4*3^(n-2) = 36*3^(n-4). ✓
# Even more room.

# This doesn't directly constrain CL.

# Let me revisit. The ACTUAL constraint on CL comes from config distinctness.
# CL ≤ product(ms). But product(ms) can be up to 4*3^(n-2)-1, which is exponential.
# So the pigeonhole argument on the total state space doesn't give CL ≤ 2n.

# The argument MUST be about the mover walk structure + binary parity + something else.

# CLEAN APPROACH: Direct from fc ≥ 2 + ZW decomposition.

# Zero winding: CL = cwSteps + ccwSteps + staySteps, cwSteps = ccwSteps.
# So CL = 2*cwSteps + staySteps.
# fc(p) ≥ 2 → CL ≥ 2n.
# Need CL ≤ 2n.

# The upper bound CL ≤ 2n is equivalent to:
#   sum fc(p) ≤ 2n
#   ⟺ average fc ≤ 2
#   ⟺ since fc ≥ 2 for all p, fc = 2 for all p.

# So we need: no processor has fc ≥ 3.

# For BINARY procs: fc is even and ≥ 2. So fc ∈ {2, 4, 6, ...}.
# If fc ≥ 4 for some binary proc, then CL ≥ 4 + 2(n-1) = 2n+2.

# For TERNARY procs: fc ≥ 2. If fc ≥ 3, CL ≥ 3 + 2(n-1) = 2n+1.

# So: if ANY proc has fc ≥ 3, CL ≥ 2n+1.
# And if a BINARY proc has fc ≥ 4, CL ≥ 2n+2.

# To prove CL ≤ 2n, we need fc = 2 for all procs.
# But that's CIRCULAR — we're trying to prove CL ≤ 2n to DEDUCE fc = 2.

# So the proof can't be purely about the walk structure.
# It MUST use the state-space constraint (sub-threshold product) to bound CL.

# Wait — maybe I'm overcomplicating this. Let me re-read the Lean code.
# Line 32: "CL = 2n; Π m_i ≥ CL = 2n for good cycles, and 2n ≤ 4·3^(n−2) for n ≥ 9."
# This is saying: we already know CL ≥ 2n, and we need CL ≤ 2n.
# The sketch says this follows from "binary parity + config distinctness → collision"
# if there's an extra step.

# I think the REAL argument is:
# Suppose CL > 2n. Then some proc has fc ≥ 3.
# If a binary proc has fc ≥ 4, then... what? Config collision?
# If a ternary proc has fc ≥ 3 (and all binary have fc = 2), then CL = sum ≥ 2b + 3 + 2(n-b-1)
#   = 2n + 1 where b is binary count. But this doesn't give a contradiction.
# Actually we need something specific to FORCE a config collision.

# The issue is: CL > 2n does NOT automatically give a contradiction.
# We need a specific argument that uses the hypotheses.

# Maybe the argument is: with n ≥ 9 and sub-threshold product,
# the product bound constrains the state space in a way that limits CL.

# Actually, I think the answer might be simpler: maybe CL ≤ 2n follows from
# the specific structure of GOOD CONFIGURATIONS (unique privileged processor).

# In a good cycle, every config has exactly one privileged processor.
# Being "good" means: the token is well-defined and unique.
# The structure of the token ring means the number of good configs is bounded.

# Let me check: for sub-threshold product with ≥3 binary, how many good configs are there?

# Actually let me just verify computationally: for actual GOOD CYCLES (not arbitrary
# cycles in the config graph), does CL = 2n hold for zero-winding ones?

print("="*70)
print("COMPUTATIONAL VERIFICATION")
print("="*70)
print()

# I need to properly model the token ring.
# A configuration is "good" if it has exactly one privileged processor.
# A privileged processor p at config c means: c[p] ≠ f_p(c[p-1], c[p], c[p+1])
# i.e., p is not stable.

# In Dijkstra's model, a processor p is privileged if its state differs from
# what its transition function would compute.

# Actually in the general model: privileged(c, p) means the system would change
# c[p] to some other value. The transition function is part of the system.

# For our purposes, we don't have a specific transition function — we're proving
# that NO system can form a valid good cycle at sub-threshold product.
# So we're considering ABSTRACT good cycles.

# In an abstract good cycle:
# - Configs are distinct
# - Each config has exactly one privileged proc (the mover)
# - When the mover fires, its value changes, all others stay

# The "unique privileged" constraint is THE key constraint.
# In the general good cycle: at each config, there's exactly ONE proc that
# would fire. This means at each config, exactly one proc p satisfies
# c[p] ≠ f_p(c[left p], c[p], c[right p]).

# But we don't know f_p! We're proving for ALL possible f_p.
# So the good cycle is "compatible with SOME system".

# For the LOWER BOUND proof, we assume a valid system + good cycle exist
# and derive a contradiction.

# Key property: in a good cycle, consecutive configs differ at exactly one position.
# The mover's value changes, all others stay.
# Configs are distinct (no repetition in the cycle).

# So a "good cycle" IS a simple cycle in the single-flip graph where additionally
# each config has a unique privileged proc.

# But the unique-privileged constraint means: at config c, if p is the mover,
# then for ALL other procs q ≠ p: c[q] = f_q(c[left q], c[q], c[right q]).
# i.e., all non-movers are "stable" / "quiescent".

# This is a STRONG constraint. It means: changing the non-mover procs' values
# would violate the unique-privilege property.

# Hmm, but we still don't have a specific f. We're assuming one exists.

# Let me try a different approach: just enumerate actual valid systems and their
# good cycles at small n.

def verify_system(n, ms, tables):
    """
    Verify a token ring system.
    tables[p] is a dict: (left_val, self_val, right_val) -> new_self_val
    A config c is "good" if exactly one proc p has c[p] ≠ tables[p](c[p-1], c[p], c[p+1]).
    """
    from itertools import product as cprod

    total = 1
    for m in ms:
        total *= m

    ranges = [range(m) for m in ms]
    all_configs = list(cprod(*ranges))

    good_configs = []
    for c in all_configs:
        priv_count = 0
        priv_proc = -1
        for p in range(n):
            left = c[(p - 1) % n]
            self_val = c[p]
            right = c[(p + 1) % n]
            new_val = tables[p].get((left, self_val, right), self_val)
            if new_val != self_val:
                priv_count += 1
                priv_proc = p
        if priv_count == 1:
            good_configs.append((c, priv_proc))

    return good_configs

def find_good_cycles_from_system(n, ms, good_configs):
    """
    Given good configs (each with a unique mover), find all good cycles.
    A good cycle: start from a good config, fire the mover, get next config.
    Continue until we return to start. All configs in the cycle must be good.
    """
    config_to_mover = {}
    for c, p in good_configs:
        config_to_mover[c] = p

    cycles = []
    visited_starts = set()

    for start_config, _ in good_configs:
        if start_config in visited_starts:
            continue

        path = []
        movers = []
        c = start_config
        seen = set()

        while True:
            if c not in config_to_mover:
                break  # not a good config
            if c in seen and c != start_config:
                break  # revisited non-start
            if c == start_config and len(path) > 0:
                # Completed cycle
                if len(path) >= 4:  # minimum meaningful length
                    cycles.append((list(path), list(movers)))
                    for cfg in path:
                        visited_starts.add(cfg)
                break

            seen.add(c)
            path.append(c)
            p = config_to_mover[c]
            movers.append(p)

            # Fire mover
            c_next = list(c)
            # The new value: tables[p](left, self, right)
            # We need the table... let me restructure
            break

    return cycles

# Actually, let me use the verifier.py approach.
# For a concrete system, I can find good cycles directly.

# Let me use a known small system: Dijkstra's Solution 1 or Solution 3
# for n=5, ms=(2,2,2,3,3).

# But actually, what I really need is to find ZERO-WINDING good cycles.
# Let me build a simpler enumerator.

from itertools import product as cprod

def find_zw_cycles_for_system(n, ms, tables, max_cycles=1000):
    """
    For a given system (transition tables), find zero-winding good cycles.
    """
    total = 1
    for m in ms:
        total *= m

    ranges = [range(m) for m in ms]
    all_configs = list(cprod(*ranges))

    # Find good configs and their movers
    good_map = {}  # config -> mover
    for c in all_configs:
        priv_procs = []
        for p in range(n):
            left = c[(p - 1) % n]
            self_val = c[p]
            right_val = c[(p + 1) % n]
            new_val = tables[p][(left, self_val, right_val)]
            if new_val != self_val:
                priv_procs.append(p)
        if len(priv_procs) == 1:
            good_map[c] = priv_procs[0]

    print(f"  Good configs: {len(good_map)} / {total}")

    # Follow the deterministic trajectory from each good config
    cycles = []
    visited = set()

    for start in good_map:
        if start in visited:
            continue

        path = []
        movers_list = []
        c = start

        while True:
            if c not in good_map:
                # Hit a non-good config; this trajectory doesn't form a good cycle
                break
            if c in visited:
                break
            if c == start and len(path) > 0:
                # Completed cycle
                cycles.append((list(path), list(movers_list)))
                break

            visited.add(c)
            path.append(c)
            p = good_map[c]
            movers_list.append(p)

            # Fire mover p
            c_next = list(c)
            left = c[(p - 1) % n]
            self_val = c[p]
            right_val = c[(p + 1) % n]
            c_next[p] = tables[p][(left, self_val, right_val)]
            c = tuple(c_next)

        if len(cycles) >= max_cycles:
            break

    return cycles

def build_full_table(n, ms, f):
    """
    Build transition tables from a function f(p, left, self, right) -> new_self.
    """
    tables = []
    for p in range(n):
        t = {}
        for l in range(ms[(p-1) % n]):
            for s in range(ms[p]):
                for r in range(ms[(p+1) % n]):
                    t[(l, s, r)] = f(p, l, s, r) % ms[p]
        tables.append(t)
    return tables

# Dijkstra Solution 3: ms = (3,3,...,3), f_p(l,s,r) = s if s == l else (l+1)%3
# But we need ≥3 binary procs. Let me use the M_5=96 witness instead.
# ms = (2,2,2,3,4)

# Actually, let me try an abstract approach. Since we're considering ANY valid system,
# the question is purely about the mover word and the state constraints.

# KEY INSIGHT (attempting):
# In a zero-winding good cycle, the mover word traces a closed walk on C_n.
# With zero winding, it returns to start with net displacement 0.
# cwSteps = ccwSteps, staySteps = CL - 2*cwSteps.
#
# For each proc p, consider the "runs" of consecutive mover positions at p.
# Each run of length r contributes r to fc(p) and r-1 to stayMoveCountAt(p).
# So stayMoveCountAt(p) = fc(p) - (number of runs at p).
#
# Total staySteps = sum_p stayMoveCountAt(p) = CL - sum_p (runs at p).
# Total runs = sum_p (runs at p). Each transition between different positions
# contributes to exactly one run ending and one run starting.
# Total transitions = CL - staySteps = 2*cwSteps (CW + CCW steps).
# Each transition ends one run and starts one run at the new position.
# So total run starts = total transitions = 2*cwSteps.
# And total runs = total run starts = 2*cwSteps. (In a cyclic sequence.)
#
# Actually, in a cyclic sequence of length CL:
# Number of position-changes = CL - staySteps = cwSteps + ccwSteps = 2*cwSteps.
# Number of maximal runs = number of position-changes. (Each change starts a new run.)
# But this is only true if consecutive changes alternate... No.
# In a cyclic sequence: number of maximal runs = number of positions where
# value differs from predecessor. This equals the number of position-changes.
# So runs = 2*cwSteps.
#
# Then: staySteps = CL - 2*cwSteps. (Already known.)
# And: staySteps = sum_p (fc(p) - runs(p)) = CL - sum_p runs(p).
# So sum_p runs(p) = 2*cwSteps.
#
# For each p: runs(p) ≥ 1 (since fc(p) ≥ 2 > 0, p is visited).
# Actually runs(p) could be more than 1.
#
# In a zero-winding walk: the mover goes back and forth.
# For each proc p, how many times does the walk visit p?
# It enters from left or right, and leaves from left or right.
# Each CW entry from left(p) + each CCW entry from right(p) starts a new run at p.
# Plus stays continue the same run.
#
# Number of runs at p = cwMoveCountAt(left(p)) + ccwMoveCountAt(right(p))
#   (entries from outside; each starts a new run).
# But wait, in a cyclic walk, if the walk starts at p, there's an extra run start.
# Total runs at p = number of non-stay entries to p.
# For a cyclic walk: runs(p) = cwMoveCountAt(left(p)) + ccwMoveCountAt(right(p))
#   if p has at least one non-stay entry, which it does since fc(p) ≥ 2.
#
# Actually, runs(p) = number of "entry transitions" from outside p.
# In a cyclic walk: runs(p) = number of k where mover[k] = p and mover[k-1] ≠ p.

# By edge balance: cwMoveCountAt(q) = ccwMoveCountAt(right(q)).
# Set q = left(p): cwMoveCountAt(left(p)) = ccwMoveCountAt(p).
# So entries from left = ccwMoveCountAt(p).
# Similarly: ccwMoveCountAt(right(p)) = cwMoveCountAt(p).
# (using edge balance with q = p: cwMoveCountAt(p) = ccwMoveCountAt(right(p)))
#
# So runs(p) = ccwMoveCountAt(p) + cwMoveCountAt(p)
#            = cwMoveCountAt(p) + ccwMoveCountAt(p).
# And fc(p) = cwMoveCountAt(p) + ccwMoveCountAt(p) + stayMoveCountAt(p).
# So stayMoveCountAt(p) = fc(p) - runs(p) = fc(p) - cwMoveCountAt(p) - ccwMoveCountAt(p). ✓
#
# And: sum_p runs(p) = sum_p [cwMoveCountAt(p) + ccwMoveCountAt(p)]
#     = cwStepCount + ccwStepCount = 2*cwSteps. ✓

# Now, the argument for CL ≤ 2n.
# We need to use a PROPERTY OF THE CONFIGS (not just the walk).
# The key must be: distinct configs + state space structure.

# Let me think about what constrains CL beyond the walk structure.
# Each config is distinct. The total number of configs CL is bounded by the
# number of "reachable" configs from the walk.

# Actually I wonder: is CL ≤ 2n a THEOREM about abstract walks on C_n,
# or does it require the config distinctness + sub-threshold constraint?

# Let's check: for an abstract closed walk on C_5 with zero winding,
# fc(p) ≥ 2 for all p, what are the possible lengths?

# Minimum: CL = 2n = 10.
# Can CL = 12?
# Walk: 0,1,2,3,4,3,2,1,0,1,2,1 → length 12.
# fc: 0→2, 1→4, 2→3, 3→2, 4→1. No, fc(4)=1.
# Try: 0,1,2,3,4,4,3,2,1,0,0,1,0 → length 13.
# This doesn't have zero winding either.

# Let me be more careful. With ZW: cwSteps = ccwSteps.
# CL = 12 → cwSteps + ccwSteps + staySteps = 12, cwSteps = ccwSteps.
# So 2*cwSteps + staySteps = 12. cwSteps can be 5 (staySteps=2) or 6 (staySteps=0).

# cwSteps = 5, staySteps = 2:
# Walk: 0,1,2,3,4,4,3,2,1,0,0,1 →
# Steps: +1,+1,+1,+1,0,-1,-1,-1,-1,0,+1 and wrapping: 1→0 is -1.
# Wait: positions are 0,1,2,3,4,4,3,2,1,0,0,1. Last step: 1→0 (wrap, -1).
# CW: 0→1, 1→2, 2→3, 3→4, 0→1 = 5 CW. ✓
# CCW: 4→3, 3→2, 2→1, 1→0, 1→0...
# Let me recount.
# Position sequence: 0,1,2,3,4,4,3,2,1,0,0,1
# Steps (consecutive pairs with wrap):
# (0,1)=+1, (1,2)=+1, (2,3)=+1, (3,4)=+1, (4,4)=0, (4,3)=-1, (3,2)=-1,
# (2,1)=-1, (1,0)=-1, (0,0)=0, (0,1)=+1, (1,0)=-1 [wrap: from pos 11 to pos 0]
# CW: 5, CCW: 5, Stay: 2. Total = 12. ZW: ✓.
# fc: 0→3(pos 0,9,10), 1→3(pos 1,8,11), 2→2(pos 2,7), 3→2(pos 3,6), 4→2(pos 4,5).
# fc(0) = 3, fc(1) = 3 — both ≥ 2. ✓
# CL = 12 > 2*5 = 10.

# So for ABSTRACT walks, CL > 2n IS possible with zero winding + fc ≥ 2.
# The constraint CL ≤ 2n MUST come from the config structure (distinct configs +
# sub-threshold product or some other system property).

print("FINDING: CL > 2n is possible for abstract zero-winding walks with fc ≥ 2.")
print("The bound CL ≤ 2n MUST use config distinctness + system-specific constraints.")
print()

# Now, what system-specific constraint forces CL ≤ 2n?
#
# Possibility 1: Binary parity forces fc even at binary procs.
# With ≥3 binary procs (fc even ≥ 2) and CL ≥ 2n:
# If CL = 2n + k (k > 0), then sum fc = 2n + k.
# Each proc has fc ≥ 2, so "excess" = k distributed among procs.
# For binary procs: excess must be even (fc even). So if a binary proc gets excess,
# it gets ≥ 2. Minimum excess from one binary proc = 2.
# So CL ≥ 2n + 2 if any binary has fc > 2.
# For a ternary proc getting excess 1: fc = 3. CL ≥ 2n + 1.
#
# So CL ∈ {2n, 2n+1, 2n+2, ...}.
# If only ternary procs have excess: CL can be 2n+1.
# If any binary has excess: CL ≥ 2n+2.
#
# Possibility 2: Config collision from binary repetition.
# If a binary proc p has fc = 4: p fires 4 times, value toggles
# v→v'→v→v' → back to v. Between consecutive firings of p, p's value is constant.
# So there are 4 "phases" for p: [v, v', v, v'].
# Two phases have value v, two have value v'.
# For configs to be distinct during the v-phases, other procs must distinguish them.
# With 3 binary procs all having fc ≤ 4: the binary state tuple can take at most
# 2^3 = 8 values. But each phase can last multiple steps.
#
# Hmm, this doesn't immediately give a contradiction.

# Let me look at this from a completely different angle.
# Maybe the proof uses the "no safe processor" condition more directly.

# "No safe processor" means: every proc is within distance 1 of some mover.
# But in a good cycle, movers cover all procs (fc > 0 for all).
# So "no safe" adds: every proc is within distance 1 of SOME mover at EVERY step?
# No — the definition is about the existence of a safe proc across all steps.

# Actually, looking at the Lean definition more carefully:
# _hno_safe : ¬∃ q, ∀ k, moverAt k ≠ q ∧ moverAt k ≠ left q ∧ moverAt k ≠ right q
# This says: there is NO processor q such that for ALL steps k, q and its neighbors
# are never the mover.
# In other words: for every proc q, there exists some step k where the mover is
# q, left q, or right q.

# This is weaker than what I thought. It just means every proc is affected by
# SOME mover at some step.

# Actually, with fc ≥ 2 for all procs (which we have from Step B), the "no safe"
# is automatically satisfied: every proc fires, so moverAt k = q for some k.

# So "no safe" doesn't add information beyond fc > 0.

# OK, I think the CORRECT argument is different from what I've been exploring.
# Let me look at what the Lean proof sketch actually says more carefully.

# The sketch at lines 79-86 says:
# "Zero winding: CL = 2·cwStepCount + stayStepCount.
#  Every edge crossed an even number of times (edgeTraversalCount_even_of_zeroWinding).
#  cwStepCount = ∑ cwMoveCountAt(p) and under ZW each cwMoveCountAt(p) ≥ 1
#  would give cwStepCount ≥ n. Then stayStepCount = 0 and cwStepCount = n
#  force CL = 2n."

# This sketch ASSUMES cwMoveCountAt(p) ≥ 1 for all p, which I showed can fail.
# But maybe in the CONTEXT where configs are distinct, it DOES hold?

# Think: if cwMoveCountAt(p) = 0 for some edge (p, right(p)), then by edge balance
# ccwMoveCountAt(right(p)) = 0 too. So the edge (p, right(p)) is never crossed.
# The walk stays on one side of this edge.
# But the walk visits BOTH p and right(p) (fc ≥ 2 for both).
# If the walk visits p and right(p) without crossing edge (p, right(p)),
# then it must enter p from left(p) and enter right(p) from right(right(p)).
# And the walk visits all vertices... this means the walk visits all vertices
# by going around the ring the "other way" through the uncrossed edge.
# But wait, with zero winding, the walk can't go around the ring net.
#
# If the walk avoids edge (p, right(p)), it must visit p via left(p) and
# right(p) via right(right(p)). To visit BOTH sides of the ring, the walk
# must go from p to right(p) somehow — but the only path on C_n avoiding
# this edge goes the long way around (n-1 edges). With zero winding,
# going CW by n-1 steps must be balanced by CCW n-1 steps, giving CL ≥ 2(n-1).
# But the walk also has stays and visits to p (fc ≥ 2).
#
# Actually, I realize: if edge (p, right(p)) is never crossed,
# the walk is on C_n \ {edge (p, right(p))} = path graph P_n.
# A closed walk on P_n (the path) with zero winding (net displacement 0)
# that visits every vertex at least twice.
# On a path, a closed walk must end where it started.
# Every step goes left, right, or stays.
# Zero winding on a PATH means... the walk is already a closed walk on a path.
# The walk visits all n vertices. On the path 0-1-...-n-1, starting at some v,
# it must reach both endpoints. The total walk length is at least 2*(n-1) + stays.
# But with ZW on C_n: sum of displacements = 0 mod n... wait, we have ZW on C_n
# (totalDisplacement on the ring = 0), not on the path.
#
# If the walk never crosses edge (p, right(p)):
# All steps are between {left, same, right} neighbors on C_n, but never
# cross that one edge. The walk is effectively on the (n-1)-length path
# left(p) - ... - p - ... - right(p) where we identify the ring minus one edge.
# No wait: C_n minus edge (p, right(p)) is the path p+1 - p+2 - ... - p-1 - p
# (going the other direction).
#
# Actually C_n minus edge (p, right(p)) = path: right(p), right(right(p)), ..., left(p), p.
# A path of n vertices.
#
# On this path, a closed walk starting at some vertex v, visiting every vertex ≥ 2 times,
# with zero winding ON THE RING (not the path).
#
# On the path, the signed displacement from v back to v is always 0 (closed walk).
# The ZW condition on the ring is that cwSteps = ccwSteps.
# On the path (missing one edge), CW and CCW steps are well-defined:
# CW means moving from vertex i to right(i) on the ring (where right(i) ≠ p+1 when i=p).
#
# For a closed walk on a path of length n, the walk goes right and left.
# The walk visits every vertex ≥ 2 times. The minimum length of such a walk:
# The walk must reach both endpoints of the path. Going from one end to the other
# is n-1 steps. Going back is n-1 steps. Total ≥ 2(n-1) for visiting all vertices twice.
# Plus any extra visits. With fc ≥ 2 for all procs: CL ≥ 2n (from sum of fc).
# And CL = 2*cwSteps + staySteps.
#
# On the path, cwSteps and ccwSteps equal the number of right-moves and left-moves.
# For a closed walk on the path: right-moves = left-moves.
# So cwSteps = ccwSteps ✓ (zero winding automatically holds on a path).
#
# So the walk on the path has CL = 2*cwSteps + staySteps, cwSteps ≥ n-1
# (must traverse the path at least once in each direction to visit all vertices).
#
# Wait, cwSteps ≥ n-1 for a path traversal? If the walk starts at one end,
# goes to the other end (n-1 CW steps), comes back (n-1 CCW steps), that's
# CL = 2(n-1) with fc(endpoints) = 1, fc(interior) = 2.
# But fc ≥ 2 for all. So endpoints need extra visits. ≥ 2 more steps.
# CL ≥ 2n. And CW steps = n-1 + (at most 1 more CW). But stays contribute.
#
# Hmm, this is getting complex. Let me just verify computationally.

print("="*70)
print("TESTING: Abstract walk with edge avoidance")
print("="*70)

def test_abstract_walks(n):
    """
    Generate abstract zero-winding walks on C_n.
    Check: is cwMoveCountAt(p) ≥ 1 for all p achievable
    when fc(p) ≥ 2 for all p?
    """
    # Walk on C_n: sequence of positions p_0, p_1, ..., p_{L-1}
    # Steps: p_{i+1} - p_i ∈ {-1, 0, +1} mod n
    # Closed: p_0 = p_L (cyclic)
    # ZW: sum(steps) = 0 (equivalently, #CW = #CCW)
    # fc(p) ≥ 2 for all p

    # For n=5, enumerate walks of length 10, 11, 12 with fc ≥ 2 and ZW.
    # Check which ones have an uncrossed edge.

    from itertools import product as cprod

    results = {l: {'total': 0, 'has_uncrossed': 0} for l in range(2*n, 3*n+1)}

    # Generate walks by choosing step directions
    # This is exponential; use n=5 with small lengths

    for L in range(2*n, min(2*n+5, 3*n+1)):
        count = 0
        uncrossed_count = 0

        # Try all walks of length L starting at position 0
        # Each step is -1, 0, or +1
        for steps in cprod([-1, 0, 1], repeat=L):
            # Check zero winding
            if sum(steps) != 0:
                continue

            # Build position sequence
            pos = [0]
            for s in steps:
                pos.append((pos[-1] + s) % n)

            # Check closure
            if pos[-1] != pos[0]:
                continue

            pos = pos[:-1]  # Remove duplicate last position

            # Check fc ≥ 2
            fc = [0] * n
            for p in pos:
                fc[p] += 1
            if any(f < 2 for f in fc):
                continue

            count += 1

            # Check edge crossings
            cw_cross = [0] * n
            ccw_cross = [0] * n
            for i in range(L):
                p_curr = pos[i]
                p_next = pos[(i + 1) % L]
                diff = (p_next - p_curr) % n
                if diff == 1:
                    cw_cross[p_curr] += 1
                elif diff == n - 1:
                    ccw_cross[p_next] += 1

            has_uncrossed = any(cw_cross[e] == 0 for e in range(n))
            if has_uncrossed:
                uncrossed_count += 1

        results[L]['total'] = count
        results[L]['has_uncrossed'] = uncrossed_count
        if count > 0:
            print(f"  n={n}, L={L}: {count} walks, {uncrossed_count} have uncrossed edge ({100*uncrossed_count/count:.1f}%)")

test_abstract_walks(5)
print()

# Now let me also check: for walks with fc ≥ 2 and ZW and L > 2n,
# what are the fire count distributions?

print("="*70)
print("FIRE COUNT DISTRIBUTIONS for ZW walks with fc ≥ 2")
print("="*70)

def analyze_walk_fc(n, max_extra=4):
    from itertools import product as cprod
    from collections import Counter

    for L in range(2*n, 2*n + max_extra + 1):
        fc_dist = Counter()
        count = 0

        for steps in cprod([-1, 0, 1], repeat=L):
            if sum(steps) != 0:
                continue

            pos = [0]
            for s in steps:
                pos.append((pos[-1] + s) % n)
            if pos[-1] != pos[0]:
                continue
            pos = pos[:-1]

            fc = [0] * n
            for p in pos:
                fc[p] += 1
            if any(f < 2 for f in fc):
                continue

            count += 1
            fc_sorted = tuple(sorted(fc))
            fc_dist[fc_sorted] += 1

        if count > 0:
            print(f"\n  n={n}, L={L}: {count} walks")
            for fc_pattern, cnt in sorted(fc_dist.items()):
                print(f"    fc={fc_pattern}: {cnt}")

# n=5 only — exponential in L
analyze_walk_fc(5, max_extra=3)

# KEY QUESTION: Can a walk with L = 2n+1 have fc ≥ 2 for all procs AND
# all binary fc's be even? (Required for binary procs.)
# If L = 2n+1 = 11 (odd), sum fc = 11. With ≥3 procs having even fc ≥ 2,
# the sum of 3 even numbers is even, plus (n-3) remaining fc's sum to 11 - even.
# So remaining sum is odd, meaning at least one remaining proc has odd fc.
# A ternary proc can have odd fc (e.g., fc=3). So this is possible.
# But if that ternary proc has fc = 3, it fires 3 times. Ternary cycle:
# after 3 firings of a ternary proc (m=3), value returns to original iff fc is
# a multiple of 3. fc=3 ✓.
# Actually, for ternary: fc must be a multiple of m=3? NO!
# Cycle closure: after fc firings, value returns to original.
# For a proc with m states that cycles through all states: fc must be 0 mod m.
# But the transition function doesn't have to cycle through all states!
# f(L,S,R) can map S to any value. It doesn't have to be S+1 mod m.
# So fc=2 is fine for ternary: fire twice, each time changing value,
# but not necessarily in a cycle: v1 → v2 → v1.

# So the closure constraint for proc p is: after fc(p) firings, its value
# returns to the original. This DOESN'T constrain fc(p) mod m_p.
# Even for binary (m=2): value toggles each time, so fc must be even.
# For ternary (m=3): value changes each time, and after fc firings returns.
# The value sequence is v_0, v_1, ..., v_{fc-1}, v_0.
# With m=3: the sequence is a cycle of length fc in {0,1,2}.
# Each step changes value: v_i ≠ v_{i+1}. And v_{fc-1} ≠ v_0.
# Such a cycle exists for any fc ≥ 2 (not just multiples of 3).
# For fc=2: v,v',v where v'≠v. ✓
# For fc=3: v,v',v'',v where all consecutive differ. ✓ (e.g., 0,1,2,0)

# So the only parity constraint from cycle closure is:
# Binary procs: fc is even.
# Non-binary procs: no constraint (fc ≥ 2 suffices).

# Now: with ≥3 binary (fc even ≥ 2), what's the minimum CL?
# sum of 3 even numbers ≥ 6, plus sum of (n-3) numbers ≥ 2 = 2(n-3).
# Total ≥ 6 + 2(n-3) = 2n.
# If CL = 2n: all fc = 2. ✓
# If CL = 2n+1: need one extra. Binary can't get +1 (must be even).
# So some non-binary gets fc = 3. Sum = 3 + 2(n-1) = 2n+1. ✓
# This is POSSIBLE from the counting perspective.

# If CL = 2n+2: a binary gets fc = 4, or two non-binary get fc = 3.
# Both possible from counting.

# So CL > 2n is NOT ruled out by counting alone.
# We need the CONFIG DISTINCTNESS argument.

# BREAKTHROUGH: I think the argument is:
# With ≥3 binary procs and fc even:
# If CL > 2n, some proc has fc ≥ 3.
# Case A: a binary proc has fc = 4 (first binary with fc > 2 gets fc ≥ 4).
#   The binary proc fires 4 times: toggles 4 times.
#   Its value visits: v, v', v, v', v.
#   There are 4 "phases" where p has value v, v', v, v'.
#   Between phases, only the mover (p) changes.
#   Two phases with value v: the configs at the START of these phases have
#   the SAME value at p (=v) and the same values at all non-mover procs.
#   So the configs are IDENTICAL. But configs must be distinct → contradiction!
#
#   WAIT: between p's firings, OTHER procs fire. So the values at other procs
#   change. The two phases where p=v don't necessarily have the same full config.
#   So this argument doesn't work directly.

# Let me think about this more carefully...
# Actually, the argument about binary fire count bound comes from the Lean file
# "FCBound.lean" — let me check what's there.

print()
print("="*70)
print("CONCLUSION FROM INITIAL ANALYSIS")
print("="*70)
print()
print("CL ≤ 2n does NOT follow from walk structure alone.")
print("It requires config distinctness + binary parity constraints.")
print("The proof must use system-level properties.")
print()
print("Next: investigate whether sub-threshold product + binary parity")
print("directly gives CL ≤ 2n via a state-space argument.")
