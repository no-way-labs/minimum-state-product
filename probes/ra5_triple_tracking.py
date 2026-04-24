"""
ra5_triple_tracking.py — Track boundary triples at the middle processor.

Setup: 3-arc = {p, p+1, p+2} = {0, 1, 2} for notational convenience.
Ring-adjacent mover constraint: consecutive movers differ by ≤ 1 on the ring.

We focus on processor 1 (the middle). Its boundary triple is:
    T = (config[0], config[1], config[2])

Goal: Find a mover step k for proc 1 and a non-mover step k' for proc 1
where the boundary triples match.

KEY INSIGHT from walk_patterns: The S-component (config[1]) matches between
proc 1's first mover step and all prior non-mover steps.

So we need: config[0] and config[2] to also match between these steps.
"""

import random
from collections import defaultdict


def symbolic_triple_evolution():
    """
    Track the boundary triple at proc 1 symbolically.

    Let the initial config be (..., a, b, c, ...) at positions (0, 1, 2).
    Initially: triple = (a, b, c).

    As the walk progresses, procs 0, 1, 2 fire at various times.
    Each fire of proc i changes config[i] to a new value.

    We trace the triple at each step.
    """
    print("=== Symbolic Triple Evolution ===")
    print()

    # Consider the simplest case: walk enters arc and visits all 3.
    # The walk within the arc must be a path on 0—1—2.
    # Minimal patterns: [0,1,2] or [2,1,0] (or with entry from outside)

    # Pattern: the walk visits the 3-arc. Within the arc, the mover
    # subsequence follows ring-adjacency. Let's trace a generic pattern.

    # Let's name the config values at each step.
    # Initially: config = (..., a0, b0, c0, ...) at positions 0, 1, 2.
    # a0, b0, c0 are the initial values.

    # After proc 0 fires: config[0] = a1 ≠ a0 (since proc 0 was privileged → changes state)
    # After proc 0 fires again: config[0] = a2 ≠ a1
    # After proc 1 fires: config[1] = b1 ≠ b0
    # After proc 2 fires: config[2] = c1 ≠ c0

    # At any step: config[0] = a_{i}, config[1] = b_{j}, config[2] = c_{k}
    # where i = # times proc 0 has fired, j = # times proc 1 has fired,
    # k = # times proc 2 has fired.

    # Triple at proc 1 = (a_i, b_j, c_k).

    # At proc 1's MOVER steps: the triple is (a_i, b_j, c_k) where b_j is
    # BEFORE the fire (so b_j is the current value, and after firing it becomes b_{j+1}).
    # Wait — at the mover step, config[1] = b_j (the current value). After the step,
    # config[1] = b_{j+1}. The boundary triple AT this step is (a_i, b_j, c_k).

    # At proc 1's NON-MOVER steps (proc 0 or 2 fires):
    # config[1] stays at b_j. The triple is (a_i, b_j, c_k) with updated a or c.

    print("Let config[0] take values a_0, a_1, a_2, ... (after 0, 1, 2, ... fires)")
    print("Let config[1] take values b_0, b_1, b_2, ... (after 0, 1, 2, ... fires)")
    print("Let config[2] take values c_0, c_1, c_2, ... (after 0, 1, 2, ... fires)")
    print()
    print("At any step: triple at proc 1 = (a_i, b_j, c_k)")
    print("where i, j, k = cumulative fire counts of procs 0, 1, 2.")
    print()

    # Now let's enumerate the steps within the 3-arc.
    # Consider the mover sequence. Steps OUTSIDE the arc don't change
    # config[0], config[1], or config[2] (since only adjacent procs can fire,
    # and we only care about the triple at proc 1).

    # Wait — that's WRONG. Steps outside the arc CAN change config[0] or config[2]
    # if the mover is proc -1 (changes config[0]'s left neighbor, NOT config[0] itself)
    # or proc 3 (changes config[2]'s right neighbor, NOT config[2] itself).
    # Actually, a step at proc -1 changes config[-1], not config[0]. So the triple
    # at proc 1 = (config[0], config[1], config[2]) only changes when proc 0, 1, or 2 fires.

    # CORRECT: The triple at proc 1 ONLY changes when a proc in {0, 1, 2} fires.

    print("IMPORTANT: Triple at proc 1 only changes when proc 0, 1, or 2 fires.")
    print("Steps with movers outside {0,1,2} do NOT change the triple.")
    print()

    # So we can focus on the SUB-SEQUENCE of steps where the mover is in {0,1,2}.
    # Call these the "relevant steps".

    # At relevant step t: let mover(t) ∈ {0,1,2}.
    # Triple at step t: (a_{i(t)}, b_{j(t)}, c_{k(t)})
    # where i(t) = #{s ≤ t : mover(s) = 0}, etc.

    # At proc 1's mover steps: mover = 1, so j increases by 1.
    # At proc 1's non-mover steps: mover ∈ {0, 2}, and i or k increases.

    print("=== S-Component Match ===")
    print()
    print("Before proc 1's first fire: j = 0, so config[1] = b_0.")
    print("At proc 1's first fire (step t*): j = 0 → 1.")
    print("Triple at t* = (a_{i(t*)}, b_0, c_{k(t*)}).")
    print()
    print("At any non-mover step t' < t* for proc 1: config[1] = b_0.")
    print("Triple at t' = (a_{i(t')}, b_0, c_{k(t')}).")
    print()
    print("S-component matches! So EC at proc 1 between t* and t' iff:")
    print("  a_{i(t*)} = a_{i(t')}  AND  c_{k(t*)} = c_{k(t')}")
    print()


def analyze_flanking_changes():
    """
    Between t' (non-mover for proc 1, before first fire of proc 1)
    and t* (first fire of proc 1):

    How many times have procs 0 and 2 fired?

    Under ring-adjacency within the arc, the walk pattern constrains this.
    """
    print("=== Flanking Processor Changes ===")
    print()

    # The walk within the arc follows patterns like:
    # [0, 1, 2, ...] or [2, 1, 0, ...] etc.

    # Before proc 1's first fire, the relevant mover subsequence is
    # some sequence of 0's and 2's (since mover ≠ 1).
    # But wait: under ring-adjacency, from 0 you can go to 0 or 1 (not 2),
    # and from 2 you can go to 1 or 2 (not 0). So:
    # - If a relevant step has mover = 0, the next relevant mover is 0 or 1.
    # - If a relevant step has mover = 2, the next relevant mover is 1 or 2.
    # - Mover can't jump from 0 to 2 or vice versa without passing through 1!

    # Before proc 1's first fire: all relevant movers are in {0, 2}.
    # But 0 and 2 are NOT ring-adjacent (distance 2 on the ring for n ≥ 5,
    # distance 2 on the local graph 0—1—2).
    # So consecutive relevant movers before proc 1's first fire must be:
    # - 0, 0, 0, ... (only proc 0 fires, since from 0 you must go to 0 or 1)
    # - 2, 2, 2, ... (only proc 2 fires)
    # You CANNOT have a relevant step at 0 followed by a relevant step at 2!

    print("CRITICAL OBSERVATION:")
    print("Before proc 1's first fire, consecutive relevant movers are in {0, 2}.")
    print("But 0 and 2 are distance 2 apart. Ring-adjacency forbids 0 → 2 or 2 → 0.")
    print()
    print("So before proc 1's first fire:")
    print("  Option A: Only proc 0 fires (no proc 2 fires)")
    print("  Option B: Only proc 2 fires (no proc 0 fires)")
    print("  Option C: Neither proc 0 nor proc 2 fires (no relevant steps before t*)")
    print()

    # Wait, this needs more care. The walk can go OUTSIDE the 3-arc between
    # relevant steps. E.g., the walk could be at 0, go to -1, -2, ..., back to -1, 0, ...
    # Then the relevant mover subsequence has two 0-steps that are not ring-adjacent
    # to each other. But the RING-ADJACENCY constraint is on CONSECUTIVE movers in the
    # FULL walk, not just the relevant subsequence.

    # Let me reconsider. The full walk is ring-adjacent. If the walk is at proc 0,
    # the next mover is -1, 0, or 1. If it goes to -1: out of arc. It can wander
    # anywhere outside, eventually return to -1, then to 0. The relevant mover
    # subsequence sees: ..., 0, (gap of non-arc movers), 0, ...

    # Between two visits to the arc, the walk leaves and returns. The entry point
    # must be 0 or 2 (since -1 and 3 are outside, and ring-adjacency means you
    # enter at 0 from -1 or at 2 from 3).

    # So the relevant mover subsequence can be:
    # ..., 0, (exit left, wander, reenter at 0), 0, ...
    # ..., 0, (exit left, wander, reenter at 2), 2, ...  <- but this is a long journey!

    # Actually, if the walk exits left from 0 (goes to -1) and later reenters the arc,
    # it must reenter at 0 (from -1) since you can't teleport to 2.
    # Unless the walk goes all the way around the ring! On a ring of n ≥ 7,
    # going from -1 to 3 takes at least 4 steps (through -2, -3, ..., 3).

    # But this IS possible: the walk can exit left, go around the ring, and
    # reenter from the right (at proc 2 from proc 3).

    # However, going around the ring means the walk touches many other processors.
    # For the argument: we just need to know what happens to the TRIPLE at proc 1.
    # Movers outside {0,1,2} don't change the triple.

    print("REFINED: Between relevant steps in the 3-arc, the walk may leave")
    print("and wander outside. But the triple at proc 1 is frozen during this time.")
    print("So for triple-tracking, we only care about the RELEVANT SUBSEQUENCE.")
    print()

    # OK but what about the ring-adjacency constraint on the relevant subsequence?
    # The relevant subsequence is obtained by extracting movers in {0,1,2}.
    # Between two consecutive relevant steps: the walk left the arc and returned.
    # The exit and reentry determine the constraint:
    # - Exit from 0, reenter at 0: relevant subsequence has ..., 0, ..., 0, ...
    # - Exit from 0, reenter at 2 (went around ring): ..., 0, ..., 2, ...
    # - Exit from 2, reenter at 2: ..., 2, ..., 2, ...
    # - Exit from 2, reenter at 0 (went around ring): ..., 2, ..., 0, ...

    # In the relevant subsequence: ANYTHING can follow anything!
    # The ring-adjacency constraint is satisfied by the full walk, but
    # the relevant subsequence has no adjacency constraint.

    # Wait, what if the walk doesn't leave the arc? Then consecutive relevant
    # movers ARE consecutive movers in the full walk, so ring-adjacency applies.

    # But the walk CAN leave the arc between any two in-arc firings.
    # So the relevant subsequence has no guaranteed adjacency constraint.

    print("IMPORTANT CORRECTION: The relevant mover subsequence has NO inherent")
    print("adjacency constraint. The walk can leave and reenter the arc freely.")
    print()
    print("So before proc 1's first fire, procs 0 and 2 CAN both fire.")
    print("The walk might be: ..., fire 0, leave arc, wander, reenter, fire 2, ...")
    print("Then reenter again and fire proc 1 for the first time.")
    print()

    # This changes the analysis significantly. Let me reconsider.
    # Before proc 1's first fire:
    # - Proc 0 may have fired i0 times
    # - Proc 2 may have fired k0 times
    # At proc 1's first fire: triple = (a_{i0}, b_0, c_{k0})
    # At non-mover step t' before first fire: triple = (a_{i(t')}, b_0, c_{k(t')})
    # For EC: need a_{i0} = a_{i(t')} and c_{k0} = c_{k(t')}

    # If we pick t' to be RIGHT before proc 1's first fire:
    # - If the step just before is proc 0 firing: i(t') = i0 - 1, k(t') = k0
    #   So a_{i0-1} vs a_{i0}: these are different (proc 0 changes state when firing)
    #   But c matches.
    # - If the step just before is proc 2 firing: i(t') = i0, k(t') = k0 - 1
    #   So a matches, but c_{k0-1} vs c_{k0}: different.

    # What if we go FURTHER back?
    # If proc 0 has fired i0 times before t*, and we find t' where proc 0 has
    # also fired i0 times: then a_{i0} = a_{i(t')}. But that means no proc 0
    # fires between t' and t*. Similarly for proc 2.

    # More interestingly: we need (i(t'), k(t')) = (i0, k0).
    # But at t*: (i, k) = (i0, k0).
    # At the step just before t* (which is in the full walk, and may not be relevant):
    # If it's not a relevant step, (i, k) = (i0, k0). So the step before t* in the full walk
    # has the SAME triple as t*! But that step's mover is NOT in {0,1,2}, so it's not
    # a non-mover step for proc 1 in the same way...

    # Actually, EVERY step is either a mover or non-mover step for proc 1.
    # If proc X (outside {0,1,2}) fires at step t', then proc 1 is a non-mover at t'.
    # The triple at proc 1 at step t' is (a_{i(t')}, b_{j(t')}, c_{k(t')}).
    # If j(t') = 0 (before first fire of proc 1) and (i(t'), k(t')) = (i0, k0):
    # then the triple matches the triple at t*.

    # When does (i(t'), k(t')) = (i0, k0) for some t' before t*?
    # Answer: at any step between the LAST relevant step before t* and t* itself!

    print("=== THE KEY ARGUMENT ===")
    print()
    print("Let t* = first mover step for proc 1.")
    print("Let t_prev = the last relevant step (mover in {0,1,2}) before t*,")
    print("  or the start of the cycle if no such step exists.")
    print()
    print("Case 1: No relevant step before t* (proc 1's first fire is the first")
    print("  time ANY proc in {0,1,2} fires).")
    print("  Then: i = k = 0 throughout. But we need a non-mover step.")
    print("  If the cycle has steps before t*: those are all outside the arc.")
    print("  At those steps: triple = (a_0, b_0, c_0) = triple at t*.")
    print("  EC between t* and any prior step, unless there are NO prior steps.")
    print("  But cycle length ≥ product ≥ 2^3 = 8 for 3 binary procs on n ≥ 7.")
    print("  And all 3 must fire. So there are at least 3 relevant steps total.")
    print("  If t* is the very first step, then look at the LAST step of the cycle")
    print("  (since it wraps around). Actually, let's handle this carefully.")
    print()
    print("Case 2: The last relevant step before t* is proc 0 or proc 2 firing.")
    print("  Say proc 0 fires at step s. Then at steps s+1, s+2, ..., t*-1:")
    print("  no proc in {0,1,2} fires. So (i, k) = (i0, k0) at all these steps.")
    print("  At step s: (i, k) = (i0 - 1, k0) if mover was 0, or (i0, k0 - 1) if mover was 2.")
    print()
    print("  Between s+1 and t*-1: these are non-arc steps. At each such step,")
    print("  the triple at proc 1 = (a_{i0}, b_0, c_{k0}).")
    print("  At t*: triple = (a_{i0}, b_0, c_{k0}).")
    print("  MATCH! EC between t* and any step in (s, t*).")
    print()
    print("  But wait: is there at least one step between s and t*?")
    print("  I.e., is s < t* - 1? Not necessarily!")
    print("  If s = t* - 1: the step right before t* is the last relevant step.")
    print("  Then there's no non-arc step between s and t* to use.")
    print()

    print("=== REFINED: Check if there's a gap between last relevant step and t* ===")
    print()
    print("If there IS a gap (at least one non-arc step between last relevant step")
    print("and t*): EC is immediate (triple matches).")
    print()
    print("If there is NO gap (last relevant step is at t*-1 in the full walk):")
    print("  Then the step before t* has mover in {0,1,2} \\ {1} = {0, 2}.")
    print("  And the step at t* has mover = 1.")
    print("  Ring-adjacency: mover(t*-1) and mover(t*) = 1 must be ring-adjacent.")
    print("  dist(mover(t*-1), 1) ≤ 1 → mover(t*-1) ∈ {0, 1, 2}. ✓ (already known)")
    print()
    print("  In this case, we need to look FURTHER back for a matching non-mover step.")


def deep_analysis():
    """
    Let me think about this more carefully with the CYCLE structure.

    A good cycle visits every configuration exactly once and returns to start.
    Each step changes exactly one processor (the mover).

    The cycle has length CL = total number of configs in the good cycle.
    Steps are 0, 1, ..., CL-1 (mod CL for wraparound).

    All 3 procs {0,1,2} fire at least once in the cycle.
    Let f0, f1, f2 = fire counts of procs 0, 1, 2.
    f0 ≥ 1, f1 ≥ 1, f2 ≥ 1.
    f0 + f1 + f2 + (fires of other procs) = CL.

    Boundary triple at proc 1 at step k: T(k) = (config[k][0], config[k][1], config[k][2]).

    We need T(k) = T(k') where mover(k) = 1 and mover(k') ≠ 1.
    """
    print("\n=== Deep Analysis: Cycle-Level Argument ===")
    print()

    # Let's think about it differently.
    # Consider ALL steps where the triple at proc 1 has a particular value (a, b, c).
    # At how many steps does the triple equal (a, b, c)?

    # The triple changes when proc 0, 1, or 2 fires.
    # So the triple is CONSTANT during "runs" between consecutive relevant steps.

    # The number of DISTINCT triple values is at most:
    # (f0+1) * (f1+1) * (f2+1) (each component takes at most fi+1 values)
    # But actually, each component changes monotonically (new value each fire),
    # so config[0] takes exactly f0+1 values: a_0, a_1, ..., a_{f0}.
    # Wait, that's wrong. After f0 fires of proc 0: config[0] has taken values
    # a_0, a_1, ..., a_{f0}. These might not all be distinct (if m_0 < f0+1, cycling).

    # Let me focus on the key argument.

    # CLAIM: There are exactly f0 + f1 + f2 "transitions" of the triple
    # (steps where a proc in {0,1,2} fires), dividing the cycle into
    # f0 + f1 + f2 "intervals" where the triple is constant.

    # Wait, the cycle wraps around. So there are exactly f0 + f1 + f2 transitions,
    # creating exactly f0 + f1 + f2 intervals.

    # In each interval: the triple is constant, and all steps in the interval
    # are non-mover for all of {0,1,2}.

    # Now, consider the f1 intervals that START with a proc 1 firing.
    # At each such interval: the triple just changed (config[1] changed).
    # And consider the f0 + f2 intervals that start with a proc 0 or proc 2 firing.
    # At each such interval: config[1] didn't change, but config[0] or config[2] did.

    # For EC: we need an interval starting with proc 1 firing and another interval
    # (starting with proc 0 or 2 firing) where the triples are the same.

    # Hmm, but the triple in an interval starting with proc 1 firing = the triple
    # AFTER proc 1 fires (so config[1] = new value). The triple at the proc 1 firing
    # step itself has config[1] = OLD value.

    # Let me be precise. At step k where proc 1 fires:
    # T(k) = (a_i, b_j, c_ℓ) where b_j is the value BEFORE firing.
    # After step k: config[1] = b_{j+1} ≠ b_j.
    # So the interval after step k has triple (a_i, b_{j+1}, c_ℓ).

    # We want T(k) = T(k') where mover(k) = 1 and mover(k') ≠ 1.
    # T(k) = (a_i, b_j, c_ℓ): here b_j = config[1] at step k (before firing).

    # At non-mover step k': T(k') = (a_{i'}, b_{j'}, c_{ℓ'}).
    # For match: need a_i = a_{i'}, b_j = b_{j'}, c_ℓ = c_{ℓ'}.

    # b_j = b_{j'}: Since b_j is the value BEFORE the j-th fire,
    # b_j is the value of config[1] during the interval before the j-th fire.
    # If j = 0: b_0 = initial value. This persists from cycle start until first fire.
    # b_{j'} is the value of config[1] at step k'. If k' is before the j-th fire of
    # proc 1, then j' is the number of proc 1 fires before k'.
    # b_j = b_{j'} iff j = j' (assuming all b values are distinct, which they might not be).

    # If all b values are distinct: we need j = j'. If j = 0: k' must be before first fire.
    # That's our earlier argument.

    # If b values are NOT all distinct: b_j = b_{j'} for some j ≠ j'. Then we might
    # get EC at proc 1 between the j-th fire and a non-mover step in the j'-th interval.
    # But we'd still need L and R to match.

    # Let me focus on the j = 0 case (most promising).

    print("Focus: j = 0 (proc 1's first fire).")
    print()
    print("At proc 1's first fire (step t*): T(t*) = (a_{i0}, b_0, c_{k0})")
    print("where i0 = fires of proc 0 before t*, k0 = fires of proc 2 before t*.")
    print()
    print("For EC: need step t' with mover(t') ≠ 1, before proc 1's first fire,")
    print("where proc 0 has fired i0 times and proc 2 has fired k0 times.")
    print()
    print("i0 + k0 = total fires of {0,2} before t*.")
    print("These fires partition the pre-t* period into i0 + k0 + 1 intervals")
    print("(counting from cycle start modulo wrapping).")
    print()
    print("The LAST such interval (just before t*) has fire counts (i0, k0).")
    print("Any step in this interval has triple (a_{i0}, b_0, c_{k0}) = T(t*).")
    print()
    print("EC exists IFF this last interval contains at least one step.")
    print("I.e., there is a step between the last fire of {0,2} before t* and t* itself")
    print("where no proc in {0,1,2} fires.")
    print()
    print("This fails only if the step just before t* is also a fire of proc 0 or 2.")
    print("I.e., mover(t*-1) ∈ {0, 2}.")
    print()

    print("=== What if mover(t*-1) ∈ {0, 2}? ===")
    print()
    print("Then the last interval before t* is EMPTY (zero non-arc steps).")
    print("But we can look at the interval before THAT.")
    print()
    print("If mover(t*-1) = 0: the previous interval has fire counts (i0-1, k0).")
    print("  Any step in this interval has triple (a_{i0-1}, b_0, c_{k0}).")
    print("  Since a_{i0-1} ≠ a_{i0}: L-component doesn't match. No EC here.")
    print()
    print("If mover(t*-1) = 2: previous interval has (i0, k0-1).")
    print("  Triple = (a_{i0}, b_0, c_{k0-1}). R-component doesn't match.")
    print()
    print("What about TWO intervals back?")
    print("If mover(t*-1) = 0 and mover(t*-2) = 2: interval has (i0-1, k0-1).")
    print("  Neither L nor R matches. No EC.")
    print("If mover(t*-1) = 0 and mover(t*-2) = 0: interval has (i0-2, k0).")
    print("  L = a_{i0-2}. Could equal a_{i0} if proc 0 is binary and i0 ≥ 2.")
    print("  Then a_{i0-2} = a_{i0} (mod 2 cycling). So if m_0 = 2 and i0 ≥ 2:")
    print("  a_0 = a_2 = a_4 = ... So a_{i0} = a_{i0-2} iff i0 ≡ i0-2 (mod 2). Always!")
    print()
    print("So for BINARY proc 0: going back 2 fires gives the same L value.")
    print("But this only helps if there IS an interval there.")
    print()

    print("=== The General Problem ===")
    print()
    print("We need an interval before t* where (i, k) = (i0, k0).")
    print("This is impossible IF there are fires of {0,2} immediately before t*.")
    print("In that case, we need to use the CYCLE WRAPAROUND.")
    print()
    print("Consider the FULL CYCLE. Proc 1 fires f1 times.")
    print("Between proc 1's last fire and first fire (going around the cycle),")
    print("config[1] = b_0 (the initial value, same as at first fire).")
    print("This is a segment of the cycle of length CL - (last fire of 1) + (first fire of 1).")
    print("In this segment: procs 0 and 2 fire some number of times.")
    print()
    print("The triple at proc 1 at the first fire = (a_{i0}, b_0, c_{k0}).")
    print("We need (a_{i'}, b_0, c_{k'}) = (a_{i0}, b_0, c_{k0}) at a non-mover step.")
    print("I.e., a_{i'} = a_{i0} and c_{k'} = c_{k0}.")
    print()
    print("Proc 0 fires f0 times total. In the segment where config[1] = b_0,")
    print("proc 0 fires some number F0 of times (where 0 ≤ F0 ≤ f0).")
    print("Config[0] passes through: a_{i0-F0+1}, ..., a_{i0} (before first fire of 1)")
    print("and a_0, a_1, ..., a_{i_after_last} (after last fire of 1).")
    print("Wait, this wraps around the cycle. Let me think differently.")


def pigeonhole_argument():
    """
    THE PROOF (attempt via pigeonhole on the middle processor's triple).

    Key setup:
    - Cycle of length CL.
    - Proc 1 fires f1 ≥ 1 times.
    - Triple T(k) = (config[k][0], config[k][1], config[k][2]).
    - T only changes at relevant steps (movers in {0,1,2}).
    - Number of relevant steps = f0 + f1 + f2.
    - Number of intervals (runs of constant T) = f0 + f1 + f2.
    - Each interval has a unique T value (since configs are distinct? NO — T is a
      projection, not the full config. Different configs can have the same T.)

    Actually, the number of DISTINCT T values might be less than the number of intervals.
    If two intervals have the same T: and one starts with a proc-1 fire and the other
    doesn't: EC!

    How many distinct T values can there be?
    Each component: config[0] takes at most m_0 values, config[1] takes at most m_1 values,
    config[2] takes at most m_2 values.
    So at most m_0 * m_1 * m_2 distinct T values.

    Number of intervals = f0 + f1 + f2.
    If f0 + f1 + f2 > m_0 * m_1 * m_2: pigeonhole gives two intervals with same T.
    But f0 + f1 + f2 could be much smaller than CL.

    For the good cycle: CL ≥ product of all m_i (if cycle visits all good configs),
    so CL can be much larger. But f0, f1, f2 could be small (each ≥ 1).

    Pigeonhole on intervals doesn't directly work for general state sizes.
    """
    print("\n=== Pigeonhole Attempt ===")
    print()
    print("Number of triple intervals: f0 + f1 + f2")
    print("Max distinct triples: m0 * m1 * m2")
    print("Pigeonhole works if f0 + f1 + f2 > m0 * m1 * m2.")
    print("But this might not hold (e.g., m0=m1=m2=3, f0=f1=f2=1 gives 3 vs 27).")
    print()
    print("Need a different approach.")


def the_real_proof():
    """
    THE ACTUAL PROOF.

    Let me reconsider the walk structure MORE carefully.

    We have a GOOD CYCLE: every config appears exactly once.
    All consecutive movers are ring-adjacent.
    Procs {0, 1, 2} all fire.

    At proc 1's mover steps: the boundary triple (L, S, R) = (config[0], config[1], config[2])
    has S = config[1] BEFORE firing. After firing, config[1] changes.

    At proc 1's NON-mover steps: the same triple, with S = current config[1].

    EC exists if any mover-step triple equals any non-mover-step triple.

    APPROACH: Count (S, mover_status) pairs.

    Config[1] takes values v_0, v_1, ..., v_{f1} where:
    - v_0 = initial value (before any fire of proc 1)
    - v_j = value after j-th fire of proc 1
    - v_j ≠ v_{j-1} (each fire changes the value)
    - v_{f1} might or might not equal v_0 (depends on cycle structure)

    Wait — this is a CYCLE. After all CL steps, we return to the start config.
    So config[1] returns to its initial value v_0.
    The sequence of values is v_0, v_1, ..., v_{f1-1}, and then back to v_0.
    So v_{f1} (the value after the last fire) must eventually become v_0 when
    the cycle completes. Actually, v_{f1} is the value of config[1] after the
    last fire of proc 1, and this persists until... well, until proc 1 fires
    again (which is at the start of the cycle in the cyclic sense).
    At the first fire, config[1] = v_0 → v_1. So just before the first fire,
    config[1] = v_0. Just after the last fire: config[1] = v_{f1}.
    Since the cycle returns to start: v_{f1} = v_0.

    Hmm wait: In the cyclic view, the values of config[1] over the cycle are:
    v_0 (initial), then after 1st fire: v_1, ..., after f1-th fire: v_{f1}.
    And v_{f1} must be the initial value of the NEXT traversal = v_0.
    Wait no, this is a single cycle. The good cycle visits a sequence of configs.
    After all CL steps, we're back at config[0] (the starting config).
    So yes, config[1] returns to v_0 after f1 fires: v_{f1} = v_0.
    """
    print("\n=== THE REAL PROOF ===")
    print()
    print("FACT: In the good cycle, config[1] takes values v_0, v_1, ..., v_{f1-1}")
    print("where v_j is the value of config[1] after j fires of proc 1.")
    print("v_{f1} = v_0 (cycle returns to start).")
    print("Each fire changes the value: v_j ≠ v_{j-1} for j = 1, ..., f1.")
    print("So v_{f1} = v_0 ≠ v_{f1-1}.")
    print()

    # The S-component of the triple at proc 1 is:
    # - At mover step j (proc 1's j-th fire, 0-indexed): S = v_j (BEFORE fire → v_{j+1})
    # - At non-mover steps between j-th and (j+1)-th fires: S = v_{j+1}
    # Wait, let me re-index. Using 1-indexed fires:
    # Before 1st fire: S = v_0
    # At 1st fire: S = v_0, then becomes v_1
    # Between 1st and 2nd fires: S = v_1
    # At 2nd fire: S = v_1, then becomes v_2
    # ...
    # After f1-th fire: S = v_{f1} = v_0
    # This wraps back to "before 1st fire": S = v_0. Consistent!

    # So the S values that appear at MOVER steps: v_0, v_1, ..., v_{f1-1}
    # And the S values at NON-MOVER steps: v_1, v_2, ..., v_{f1} = v_0
    # Rewriting: non-mover S values = v_0, v_1, ..., v_{f1-1} (just shifted)

    # BOTH mover and non-mover steps see the SAME set of S values!
    # (v_0 appears at mover step 1 and at non-mover steps after last fire)
    # (v_1 appears at mover step 2 and at non-mover steps after 1st fire)

    print("S-values at MOVER steps: {v_0, v_1, ..., v_{f1-1}}")
    print("S-values at NON-MOVER steps: {v_1, v_2, ..., v_{f1}} = {v_0, v_1, ..., v_{f1-1}}")
    print("(since v_{f1} = v_0)")
    print()
    print("Both sets are identical! Every S-value appears at both mover and non-mover steps.")
    print()

    # For each S-value v_j: it appears at
    # - Mover step: the (j+1)-th fire of proc 1 (where config[1] = v_j before firing)
    # - Non-mover steps: all steps between j-th fire and (j+1)-th fire (where config[1] = v_j after j-th fire)
    # Wait, after j-th fire: config[1] = v_j (I'm using 0-indexed: v_0 is initial, v_1 after 1st fire, etc.)
    # Let me re-do with cleaner notation.

    # Let fire_1, fire_2, ..., fire_{f1} be the steps where proc 1 fires (in cycle order).
    # At step fire_j: config[1] = u_j (value BEFORE firing). After: config[1] = u_j' ≠ u_j.
    # Between fire_j and fire_{j+1}: config[1] = u_j' (constant).
    # u_{j+1} = u_j' (the value before the next fire = the value after the previous fire).
    # So u_1' = u_2, u_2' = u_3, ..., u_{f1}' = u_1 (cycle wraps).

    # S-value at mover step fire_j: u_j
    # S-value at non-mover steps between fire_j and fire_{j+1}: u_j' = u_{j+1 mod f1}

    # Wait, u_j' = u_{j+1 mod f1}. Hmm, u_j' ≠ u_j. And u_{j+1} = u_j'. So:
    # S at mover step j: u_j
    # S at non-mover steps after fire j: u_{j+1 mod f1}

    # S at mover step j = u_j
    # S at non-mover steps after fire j = u_{(j mod f1) + 1}... let me use modular:
    # u_{j+1} where indices are mod f1.

    # So mover S-values: {u_1, u_2, ..., u_{f1}}
    # Non-mover S-values (between fire_j and fire_{j+1}): u_{j+1 mod f1} for j = 1, ..., f1
    #   = {u_2, u_3, ..., u_{f1}, u_1} = {u_1, ..., u_{f1}}

    # Same set! Good.

    # Now, for S-value u_j:
    # It appears as mover S at step fire_j.
    # It appears as non-mover S at all steps between fire_{j-1} and fire_j
    # (i.e., after fire_{j-1}, config[1] = u_{j-1}' = u_j, until fire_j changes it).

    # So for each j: mover step fire_j and non-mover steps (fire_{j-1}, fire_j) share S = u_j.
    # For EC: need (L, R) to also match between fire_j and some step in (fire_{j-1}, fire_j).

    print("For each j = 1, ..., f1:")
    print("  Mover step fire_j: triple = (L_j, u_j, R_j)")
    print("  Non-mover steps in (fire_{j-1}, fire_j): triple = (L, u_j, R)")
    print("    where L and R depend on the fire history of procs 0 and 2.")
    print()
    print("EC at proc 1 between fire_j and some step t ∈ (fire_{j-1}, fire_j)")
    print("iff L(t) = L_j and R(t) = R_j.")
    print()

    # Now, at step fire_j: L_j = config[0] at that moment, R_j = config[2] at that moment.
    # In the interval (fire_{j-1}, fire_j): L and R change when procs 0 and 2 fire.
    # At step fire_j: L_j and R_j are the values just BEFORE fire_j.

    # In the interval (fire_{j-1}, fire_j): the last step before fire_j.
    # If this last step is NOT a fire of proc 0 or 2: then L and R at that step
    # equal L_j and R_j. EC!

    # If the last step before fire_j IS a fire of proc 0 or 2: L or R just changed.
    # So L ≠ L_j (if proc 0 fired) or R ≠ R_j (if proc 2 fired).

    print("EC exists immediately if the step before fire_j (for any j) is NOT a fire of {0,2}.")
    print()
    print("If EVERY fire_j has a fire of {0,2} as its immediate predecessor:")
    print("  This requires f1 distinct predecessor steps, each a fire of {0,2}.")
    print("  So f0 + f2 ≥ f1.")
    print("  Moreover, the predecessor of fire_j is at step fire_j - 1.")
    print("  And mover(fire_j - 1) ∈ {0, 2}.")
    print("  Ring-adjacency: dist(mover(fire_j - 1), 1) ≤ 1 iff mover ∈ {0, 1, 2}.")
    print("  mover(fire_j - 1) ∈ {0, 2}: dist to 1 = 1. ✓ (ring-adjacent)")
    print()

    # So the hard case is: every fire of proc 1 is immediately preceded by a fire of {0, 2}.
    # In this case: for each j, mover(fire_j - 1) ∈ {0, 2}.
    # Let's call this the "tight" case.

    # In the tight case: the mover sequence around each fire_j looks like:
    # ..., 0 or 2, 1, ...
    # And ring-adjacency also constrains the step AFTER fire_j:
    # mover(fire_j + 1) must be ring-adjacent to 1, so mover(fire_j + 1) ∈ {0, 1, 2}.

    print("In the TIGHT case (every fire of proc 1 preceded by fire of {0,2}):")
    print()
    print("Consider the 2-step before fire_j: step fire_j - 2.")
    print("mover(fire_j - 2) must be ring-adjacent to mover(fire_j - 1) ∈ {0, 2}.")
    print("If mover(fire_j - 1) = 0: mover(fire_j - 2) ∈ {n-1, 0, 1}.")
    print("If mover(fire_j - 1) = 2: mover(fire_j - 2) ∈ {1, 2, 3}.")
    print()
    print("If mover(fire_j - 2) ∉ {0, 1, 2}: it's outside the arc, doesn't change triple.")
    print("Then at step fire_j - 2: triple = same as at fire_j - 1 (before the fire).")
    print()
    print("Actually, at step fire_j - 1 (fire of 0 or 2), the triple CHANGES.")
    print("At step fire_j - 2 (non-arc mover): triple = pre-fire-of-{0,2} value.")
    print()
    print("Let's be precise. At step fire_j:")
    print("  L = a_i, S = u_j, R = c_k (for some i, k)")
    print("At step fire_j - 1 (say mover = 0):")
    print("  This step FIRES proc 0: L goes from a_{i-1} to a_i.")
    print("  Triple AT step fire_j - 1 = (a_{i-1}, u_j, c_k)")
    print("  (because at this step, config[0] = a_{i-1} before firing)")
    print("  Wait: the triple at a step is the CURRENT config, before the move.")
    print("  At step fire_j - 1: config = (..., a_{i-1}, u_j, c_k, ...)")
    print("  After the move: config[0] = a_i.")
    print("  At step fire_j: config = (..., a_i, u_j, c_k, ...)")
    print("  Triple = (a_i, u_j, c_k).")
    print()
    print("  At step fire_j - 2 (non-arc mover):")
    print("  config = (..., a_{i-1}, u_j, c_k, ...) [same as fire_j - 1's config]")
    print("  Triple = (a_{i-1}, u_j, c_k)")
    print("  S matches (u_j). But L = a_{i-1} ≠ a_i. No EC.")
    print()
    print("  What about step fire_j - 1 AS A NON-MOVER step for proc 1?")
    print("  Triple = (a_{i-1}, u_j, c_k). Mover is 0 (not 1). S = u_j matches.")
    print("  But L = a_{i-1} ≠ a_i. No EC with fire_j.")
    print()

    # So we need to look at OTHER mover steps of proc 1.
    # What about fire_{j+1}?
    # At fire_{j+1}: triple = (a_{i'}, u_{j+1}, c_{k'}).
    # Non-mover steps in (fire_j, fire_{j+1}) have S = u_{j+1}.
    # For EC between fire_{j+1} and a non-mover step in (fire_j, fire_{j+1}):
    # same argument applies.

    # The key insight might be: in the tight case, the PATTERN of (0/2, 1, 0/2, 1, ...)
    # creates a very constrained walk.

    print("=== Consider the walk pattern in the tight case ===")
    print()
    print("If every fire of proc 1 is preceded by fire of {0, 2}:")
    print("  The relevant mover subsequence has pattern: ..., 0/2, 1, 0/2, 1, ...")
    print("  Proc 1 fires f1 times. Each preceded by a fire of {0, 2}.")
    print("  Between consecutive proc-1 fires: at least one fire of {0, 2}.")
    print("  Possibly more fires of {0, 2} between proc-1 fires too.")
    print()
    print("In the MINIMAL tight case: each proc-1 fire is preceded by exactly one fire of {0,2}.")
    print("Pattern: 0, 1, 0, 1, 0, 1, ... or 2, 1, 2, 1, ... or mixed.")
    print()

    # Let's trace the triple through a specific pattern.
    # Pattern: 0, 1, 2, 1, 0, 1, 2, 1, ...
    # This is a ping-pong between 0 and 2 through 1.

    # Step 1: mover = 0. config[0]: a_0 → a_1. Triple at this step: (a_0, b_0, c_0)
    # Step 2: mover = 1. config[1]: b_0 → b_1. Triple at this step: (a_1, b_0, c_0)
    # Step 3: mover = 2. config[2]: c_0 → c_1. Triple at this step: (a_1, b_1, c_0)
    # Step 4: mover = 1. config[1]: b_1 → b_2. Triple at this step: (a_1, b_1, c_1)
    # Step 5: mover = 0. config[0]: a_1 → a_2. Triple at this step: (a_1, b_2, c_1)
    # Step 6: mover = 1. config[1]: b_2 → b_3. Triple at this step: (a_2, b_2, c_1)
    # Step 7: mover = 2. config[2]: c_1 → c_2. Triple at this step: (a_2, b_3, c_1)
    # Wait, step 7 has mover = 2. After step 6: config = (a_2, b_3, c_1).
    # Step 7: mover = 2, triple = (a_2, b_3, c_1). After: config[2] = c_2.
    # Step 8: mover = 1. Triple = (a_2, b_3, c_2). After: config[1] = b_4.

    print("Trace pattern [0, 1, 2, 1, 0, 1, 2, 1, ...]:")
    print("  Step 1 (mover 0): triple = (a_0, b_0, c_0)")
    print("  Step 2 (mover 1): triple = (a_1, b_0, c_0)  [MOVER for proc 1]")
    print("  Step 3 (mover 2): triple = (a_1, b_1, c_0)")
    print("  Step 4 (mover 1): triple = (a_1, b_1, c_1)  [MOVER for proc 1]")
    print("  Step 5 (mover 0): triple = (a_1, b_2, c_1)")
    print("  Step 6 (mover 1): triple = (a_2, b_2, c_1)  [MOVER for proc 1]")
    print("  Step 7 (mover 2): triple = (a_2, b_3, c_1)")
    print("  Step 8 (mover 1): triple = (a_2, b_3, c_2)  [MOVER for proc 1]")
    print()
    print("Mover triples at proc 1: (a_1,b_0,c_0), (a_1,b_1,c_1), (a_2,b_2,c_1), (a_2,b_3,c_2)")
    print("Non-mover triples at proc 1: (a_0,b_0,c_0), (a_1,b_1,c_0), (a_1,b_2,c_1), (a_2,b_3,c_1)")
    print()
    print("Check for matches:")
    print("  Step 2 mover (a_1,b_0,c_0) vs Step 1 non-mover (a_0,b_0,c_0):")
    print("    S matches (b_0). L: a_1 vs a_0 — different. NO EC.")
    print("  Step 4 mover (a_1,b_1,c_1) vs Step 3 non-mover (a_1,b_1,c_0):")
    print("    S matches (b_1), L matches (a_1). R: c_1 vs c_0 — different. NO EC.")
    print("  Step 4 mover (a_1,b_1,c_1) vs Step 5 non-mover (a_1,b_2,c_1):")
    print("    L matches (a_1), R matches (c_1). S: b_1 vs b_2 — different. NO EC.")
    print()
    print("Hmm, this pattern doesn't immediately give EC within the arc firings.")
    print("But we haven't used the FULL CYCLE yet — there are steps outside the arc too.")


if __name__ == "__main__":
    symbolic_triple_evolution()
    analyze_flanking_changes()
    deep_analysis()
    pigeonhole_argument()
    the_real_proof()
