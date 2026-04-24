#!/usr/bin/env python3
"""
Palindromic Entry Conflict — the core argument for ALL 3 remaining sorrys.

The argument: for a good cycle with specific structural constraints,
the mover word forces a repeated (L,S,R) context across mover/non-mover
steps at some processor.

KEY INSIGHT (from CIC Expl 14):
For 3 consecutive binary {i, ri, rri} in a zero-winding or sweep cycle:
- Consider ri (middle binary). It fires fc ≥ 2 times.
- Between fires, other procs fire, changing the context.
- The CW and CCW passes create PALINDROMIC context patterns.
- At some interior processor j (between the binary triple and its neighbors):
  the CW non-mover context = CCW mover context.
  This gives f(j, L, S, R) = S (non-mover) AND f(j, L, S, R) ≠ S (mover).
  Contradiction!

The argument for NON-CONSECUTIVE binary:
- Find a sandwiched ternary t with binary neighbors.
- t fires fc ≥ 2 times. Between fires: binary neighbors fire.
- The binary fire counts in each phase create specific patterns.
- When ALL phases are "normal form" (neither BothEven nor ToggleFR):
  the Ring Alternation lemma forces a Traversal Return mechanism.

Let me formalize the SIMPLEST version of this argument that closes
the most sorrys.

SIMPLEST TARGET: prove that with cycle length > 8 and 3 consecutive
binary, hasEntryConflict holds.

With cycle length > 8: pigeonhole on the 8 binary triples gives
a repeated triple. Since fire/non-fire contexts are disjoint,
the repeat must be within one category. But with > 8 configs:
SOME non-fire config must reuse a fire triple (since fire triples
have at most 2 configs using them, and 8 - 2 = 6 non-fire triples
can accommodate at most 6 non-fire configs).

Wait, I showed earlier this doesn't work (fire/non-fire contexts at
a single proc are disjoint). Let me reconsider.

ACTUALLY: the entry conflict is at SOME proc, not necessarily ri.
What if the entry conflict is at a TERNARY proc?

For a ternary proc t adjacent to the binary triple:
- t's context includes val(ri) (binary, 2 values).
- With many configs: the context at t might repeat across mover/non-mover.

t's possible contexts: up to m(left(t)) × m(t) × m(right(t)).
If left(t) = rri (binary): 2 × 3 × m(right(t)) = 6 × m(right(t)).
For m(right(t)) = 3 (ternary): 18 possible contexts.

With cycle length ≥ 18: at least 2 configs share a context at t.
Both fire t or both don't fire t (determinism).
No entry conflict from this alone.

With cycle length ≥ 19: 19 configs in 18 contexts → pigeonhole
gives a repeat. Same issue.

Hmm. Pigeonhole on individual procs doesn't give EC (determinism).

The EC must come from the GLOBAL structure of the mover word.
Not pigeonhole. The palindromic argument is genuinely different.

Let me focus on the EXACT palindromic argument.

THE PALINDROMIC ARGUMENT (CIC Expl 14):

Setup: 3 consecutive binary at {0, 1, 2} (WLOG). The mover word
is a closed walk on the ring with zero winding (or sweep).

For zero-winding: the walk goes CW and CCW in equal measure.
The walk MUST cross edge (1, 2) — i.e., proc 1 fires CW or proc 2
fires CCW. From zero winding: cw(1) = ccw(2) at this edge.

If cw(1) > 0: there's a CW crossing at edge (1,2). Let step a be
a CW crossing: moverAt(a) = 1, stepDir(a) = CW (next mover = 2).
From zero winding: ∃ CCW crossing at edge (1,2): step b with
moverAt(b) = 2, stepDir(b) = CCW (next mover = 1).

At step a (CW): proc 1 fires. Config at proc 2 (non-mover):
  context_2(a) = (val(1,a), val(2,a), val(3,a))

At step b (CCW): proc 2 fires. Config at proc 2 (MOVER):
  context_2(b) = (val(1,b), val(2,b), val(3,b))

For EC at proc 2: need context_2(a) = context_2(b).

Between steps a and b: various procs fire, changing values.
The palindromic argument shows: under specific structural conditions,
the values at {1, 2, 3} return to create a matching context.

THIS is the core argument. The "structural conditions" are:
- The walk between a and b has a specific palindromic structure.
- Binary procs alternate, ternary procs cycle through values.

For the ALL-NORMAL case: the walk between CW and CCW crossings
has both binary neighbors firing odd times. This FLIPS their values.
So context_2(b) = (1-val(1,a), f(2,...), 1-val(3,a)).
With val(2,b) = val(2,a) or 1-val(2,a) depending on 2's fires.

If val(2) doesn't change between a and b (2 doesn't fire in (a,b)):
context_2(b) = (1-val(1,a), val(2,a), 1-val(3,a)).
This is the COMPLEMENT of context_2(a) at L and R.
NOT a match (different L and R).

If val(2) fires between a and b: 2's value changes.
context_2(b) = (1-val(1,a), 1-val(2,a), 1-val(3,a)) (if 2 fires once).
Full complement. Still not a match.

Hmm, the palindromic argument doesn't work by comparing JUST two
steps. It needs to look at the FULL cycle and find a proc+step pair
where the context matches across mover/non-mover.

I think the actual argument is more subtle. Let me re-read CIC Expl 14
from the memory more carefully:

"CW non-mover context = CCW mover context = (j, x_{j-1}, x_j, 0),
requiring f=x_j AND f=0. Since x_j≠0: contradiction."

The context format (j, x_{j-1}, x_j, 0) suggests:
- Processor j (interior)
- L = x_{j-1} (left neighbor value)
- S = x_j (self value)
- R = 0 (right neighbor value = 0)

The "0" comes from the binary right neighbor being in a specific state
at that step. The palindromic structure forces this specific state.

For the CW pass: j is a non-mover (the CW mover has passed j and is
now at j+1 or further). j's right neighbor (binary) has value 0.
For the CCW pass: j is the mover (the CCW mover reaches j). j's
right neighbor still has value 0 (it hasn't fired in between).

This creates: same (L, S, R) context at j at both a mover step
(CCW pass) and a non-mover step (CW pass). Entry conflict!

The key requirement: the right neighbor of j has the SAME value (0)
at both steps. This holds because the right neighbor is binary and
hasn't fired between the two steps (or has fired an even number of
times, returning to the same value).

For the "all normal" case with both binary neighbors firing odd times:
the right neighbor's value FLIPS (odd fires). So the context DIFFERS.
No direct palindromic EC from this comparison.

But the palindromic argument uses a DIFFERENT pair of steps, not
just the CW/CCW crossings at the same edge. It uses the GLOBAL
structure of the walk to find a matching pair.

I think the actual argument is:
1. The walk has a CW pass and a CCW pass (from zero winding).
2. During the CW pass: the mover goes ..., j-1, j, j+1, ...
   At step where mover = j: j fires. At step where mover = j+1:
   j is a non-mover with specific context.
3. During the CCW pass: the mover goes ..., j+1, j, j-1, ...
   At step where mover = j: j fires again. At step where mover = j-1:
   j is a non-mover.
4. The palindromic structure makes the CW non-mover context at j
   (when j+1 fires) equal to the CCW mover context at j (when j fires
   during the CCW pass). The equality comes from the binary neighbors
   being in the same state due to even total fire count.

For the "all normal" case: the binary neighbors fire odd times in each
half. So they DON'T return to the same state in each half. The
palindromic argument needs even-fire-count halves.

This is getting very specific. Let me just try to IMPLEMENT the argument
in Lean rather than continuing to analyze in Python. The Python analysis
has established that entry conflicts ALWAYS exist (computationally verified).
The Lean proof is the formalization challenge.
"""

print("The palindromic EC argument is a ~300 line formalization.")
print("Key structure:")
print("1. Find CW/CCW crossings at a binary-binary edge")
print("2. Between crossings: track binary neighbor values (parity)")
print("3. Show the context at some processor matches at mover+non-mover steps")
print("4. entryConflict_impossible → False")
print()
print("For the 'all normal' case: need a different pair of steps")
print("(not just the CW/CCW pair at the same edge)")
print("The Ring Alternation finds the right pair across ternary phases")
