"""
Check the approach for proving the LB axioms.

Key insight: Both axioms together = "no good cycle exists in sub-threshold system with n>=9".
The proof goes through cycle_classification, which is dead code (all paths eliminated by axioms).

This script analyzes the mathematical structure to find the simplest proof path.
"""

# The approach question:
# Can we prove that for ANY good cycle (regardless of winding type),
# the combination of sub-threshold + n>=9 + >=3 binary leads to False?
#
# The entry conflict at a binary processor p:
# - p fires at some steps (mover = p): f(L, S, R) != S
# - p doesn't fire at other steps: f(L, S, R) = S
# - Same (L, S, R) at both types: contradiction
#
# For 3 consecutive binary at 0, 1, 2:
# Processor 1 context: (c(0), c(1), c(2)), all in {0,1}
# 8 possible contexts.
# Fire contexts (f(L,S,R) != S) and non-fire contexts (f(L,S,R) = S) are disjoint.
# So up to 4 contexts can be "fire" and 4 can be "non-fire".
#
# For an entry conflict, we need the SAME context to appear at both.
# This is impossible by construction (they're disjoint).
# So the entry conflict must come from a DIFFERENT type of argument.

# Actually, the entry conflict IS about the same context appearing at both types.
# The point is that the good cycle STRUCTURE forces this.
# The transition function f is fixed, so each context is exclusively fire or non-fire.
# But the cycle might force a context that's assigned to "fire" to appear at a non-fire step.
# Wait, that can't happen: at a non-fire step, f(L,S,R) = S, so the context IS non-fire.
# And at a fire step, f(L,S,R) != S, so the context IS fire.
#
# The KEY: the good cycle determines which contexts appear at which steps.
# The transition function determines which contexts are fire vs non-fire.
# An entry conflict means: the good cycle places a context at a fire step AND at a non-fire step.
# For this to happen: the transition function says f(L,S,R) = S (non-fire),
# but the good cycle also has a step where p fires with this context (f(L,S,R) != S).
# This is a contradiction in the transition function!

# So: an entry conflict is NOT about the same context appearing at both types.
# It IS about the good cycle itself being inconsistent with any transition function.
# Specifically: the good cycle assigns mover = p at step k with context (L,S,R),
# and assigns mover != p at step k' with the same context (L,S,R).
# For ANY f: f(L,S,R) must simultaneously equal S (from step k') and not equal S (from step k).

# So the entry conflict is a STRUCTURAL property of the good cycle.
# It's about the MOVER WORD and the CONFIGS together being inconsistent.

# The question: under what conditions does a good cycle have an entry conflict?

# For a trivial example: if processor p fires at step 0 with context (0,0,0),
# and at step 5 the context at p is also (0,0,0) but p doesn't fire,
# that's an entry conflict.

# The palindromic argument: in a BAF cycle, the CW pass and CCW pass
# create the SAME context at interior processors.
# The CW pass has the interior processor as non-mover.
# The CCW pass has the interior processor as mover.
# Same context at both → entry conflict.

# But proving the contexts match requires state tracking through the cycle.

# Alternative: can we show that the number of distinct configs forces a context repeat?

# In a good cycle with L configs:
# Processor p is mover at fireCount(p) steps and non-mover at L - fireCount(p) steps.
#
# At mover steps: the context (L,S,R) has f(L,S,R) != S.
# At non-mover steps: the context (L,S,R) has f(L,S,R) = S.
#
# The number of distinct mover contexts + distinct non-mover contexts
# <= total distinct contexts = m_left * m_p * m_right.
#
# For 3 consecutive binary: m_left * m_p * m_right = 2*2*2 = 8.
# So: distinct mover contexts + distinct non-mover contexts <= 8.
# (They're disjoint, as argued above.)
#
# But we need: distinct mover contexts + distinct non-mover contexts > 8.
# For this: we need MORE THAN 8 distinct contexts, which is impossible with 8 total.
# So pigeonhole doesn't work here.

# The actual argument must be more structural. It uses the SPECIFIC pattern
# of the mover word, not just counting.

# For the zero-winding case:
# cwMoveCountAt(p) = ccwMoveCountAt(right(p)) for all p.
# This pairs CW and CCW crossings of each edge.
# The pairing creates context matches.

# For 3 consecutive binary at 0, 1, 2:
# Consider edge {0, 1}: CW crossings (mover = 0) and CCW crossings (mover = 1).
# At a CW crossing step k: proc 1 is non-mover, context = (c_k(0), c_k(1), c_k(2)).
# At a CCW crossing step k': proc 1 is mover (going from 1 to 0),
#   but wait: if mover = 1 at step k', then left(1) = 0 is the mover at next step.
#   Actually no: the CCW crossing of edge {0,1} means mover goes from 1 to 0.
#   So at step k': moverAt = 1, stepDir = .ccw (next mover is left(1) = 0).

# For entry conflict at proc 0:
# At CW crossing of edge {n-1, 0}: mover = n-1, going to 0.
#   Proc 0 is non-mover. Context for 0: (c(n-1), c(0), c(1)).
# At CCW crossing of edge {0, 1}: mover = 1, going to 0.
#   Wait, the mover going from 1 to 0 means moverAt = 1, not 0.
#   At step k': moverAt = 1, so proc 0 is non-mover here too!

# Hmm, let me reconsider. For entry conflict at proc p, we need:
# - A step where p IS the mover
# - A step where p is NOT the mover
# with the same (L, S, R) context.

# So for proc 1:
# - Mover step: moverAt = 1 (proc 1 fires).
# - Non-mover step: moverAt != 1 (some other proc fires, but proc 1 sees same context).

# In the BAF: during the CW pass, mover = 0 fires while proc 1 is non-mover.
# Then mover = 1 fires (proc 1 IS mover).
# If the context at proc 1 is the same at both steps, entry conflict.

# But the CW step where mover = 0 fires changes c(0), which is left(1).
# So the context at proc 1 AFTER mover = 0 fires is different from before.
# The context at proc 1 when mover = 1 fires is: (c'(0), c(1), c(2)).
# The context at proc 1 when mover = 0 fired was: (c(0), c(1), c(2)).
# Since c'(0) != c(0) (mover = 0 fired and changed), these are DIFFERENT!

# So the CW pass where mover = 0 fires doesn't give an entry conflict at proc 1
# with the immediately following step where mover = 1 fires.

# The palindromic argument uses the CCW RETURN, not the adjacent CW step.
# During the CCW return, when the mover comes back to position 2 and fires,
# proc 1 sees the RESTORED context (because binary 2 has fired twice, returning
# to initial value). Then when mover reaches position 1 and fires (CCW),
# proc 1's context is the same as during the CW pass BEFORE mover reached 1.

# This requires: c_ccw(0) = c_cw(0) and c_ccw(2) = c_cw(2).
# For c_ccw(0): proc 0 fires during CW pass (at some point) and during CCW return.
# If proc 0 is binary, two firings bring it back to initial value.
# For c_ccw(2): similarly, proc 2 fires CW and CCW, returning to initial.

# So the argument SPECIFICALLY requires that both neighbors of proc 1 are binary!
# With 3 consecutive binary at 0, 1, 2: left(1) = 0 and right(1) = 2, both binary.
# Binary means two firings return to initial state.

# But there's a subtlety: between the CW and CCW passes, other processors might
# change the neighbor values. If processor 0 fires due to a DIFFERENT edge
# (not the {0,1} edge), that would change c(0).

# In the BAF structure: the mover goes CW from 0 to d, then CCW from d back to 0.
# Between the CW pass through 0,1 and the CCW return through 1,0:
# Processor 0 fires only during the CW pass (at position 0) and during the
# CCW return (when the mover returns to position 1 and then 0).
# If the mover doesn't visit position 0 during the turnaround or other parts,
# processor 0's state doesn't change between the CW-pass fire and the CCW-return fire.

# In a general zero-winding cycle (not BAF), processor 0 might fire more times.
# But since 0 is binary, it fires an EVEN number of times. After an even number
# of binary flips, the value returns to initial.

# THE KEY INSIGHT: Between any two consecutive appearances of the same processor
# as a non-mover neighbor in matching CW/CCW pairs, the binary processor's state
# has been flipped an even number of times (because binary_fireCount_even),
# so it returns to the same value!

# Wait, but binary_fireCount_even is about the TOTAL fire count over the whole cycle,
# not between specific pairs of steps.

# The PREFIX fire count matters. Between step k and step k', the number of times
# proc 0 fires is the difference in prefix fire counts. For the contexts to match,
# we need this difference to be even (for binary proc 0).

# For zero-winding with the palindromic structure, the CW and CCW passes are
# symmetric, so each binary processor fires the same number of times in each half,
# giving an even total between paired steps.

# This is the core of the argument. In Lean, we'd need to:
# 1. Identify paired CW/CCW crossings of an edge adjacent to a binary triple
# 2. Show that between the paired crossings, the binary neighbors fire evenly
# 3. Conclude context matching → entry conflict

# The HARDEST PART: step 2. This requires reasoning about the mover word structure
# and how it interacts with the binary parity.

# For a general zero-winding cycle, the mover word might be very complex.
# The zero-winding constraint (net displacement 0) gives CW steps = CCW steps.
# But the interleaving of CW and CCW steps can be arbitrary.

print("Analysis complete. The entry conflict proof requires:")
print("1. Identifying paired CW/CCW edge crossings at a binary triple")
print("2. Showing binary neighbor prefix fire counts have matching parity")
print("3. Concluding context matching → entry conflict")
print()
print("The hardest part is step 2, which requires mover word structure analysis.")
print("This is equivalent to the palindromic entry conflict argument.")
print()
print("For the non-zero-winding case:")
print("1. Sweep: need WaterfallCycle construction (major gap)")
print("2. Odd winding: need non-uniform entry conflict (major gap)")
print()
print("Recommendation: Focus on zero-winding case with 3 consecutive binary.")
print("The key lemma needed: for zero-winding + 3 consec binary,")
print("the prefix fire count at binary neighbors is even between paired crossings.")
