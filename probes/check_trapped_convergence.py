#!/usr/bin/env python3
"""
With convergence + double trapped: can we derive False?

Key idea: processor i is binary, fc(i) = 0, value constant v.
For convergence: from config where i = 1-v, system reaches good cycle.
This requires i to eventually fire.

For i to fire: f(i, L, 1-v, R) != 1-v for some reachable (L, R).
Since m_i = 2: f(i, L, 1-v, R) = v (the only other value).

In the good cycle: f(i, L, v, R) = v for all (L,R) in cycle.
(i is never privileged, so transition function returns the current value.)

Now consider: what (L, R) contexts appear for i?
L = val(left(i)), R = val(right(i)) = val(ri).

ri also has fc=0, constant value w. So R = w always.
L = val(left(i)) which changes as left(i) fires.

In the good cycle: L ranges over the values that left(i) takes.
If left(i) is ternary (m=3): L ∈ {0, 1, 2} potentially.
If left(i) fires all 3 values: L takes values 0, 1, 2 at different cycle steps.

So the good cycle has contexts:
  (0, v, w), (1, v, w), (2, v, w)  [if left(i) visits all 3 values]
At each: f(i, L, v, w) = v.

For convergence with i = 1-v:
  Need f(i, L', 1-v, R') != 1-v = f(i, L', 1-v, R') = v for some (L', R').
  R' = w (ri is also trapped, constant w in the bad config??)

WAIT: in a bad config (not in good cycle), ri might NOT have value w!
During convergence, ri can have any value until the system reaches the cycle.

Hmm, but ri has fc=0 in the good cycle, meaning ri never fires in the cycle.
During convergence from a bad config, ri CAN fire (it's not constrained to
never fire outside the cycle). So ri's value can change during convergence.

This makes the argument more complex. The transition function at i depends
on the CURRENT values of left(i) and ri, which can be anything during
convergence.

SIMPLER APPROACH: Use the fact that the good cycle has fc(i) = 0.

If fc(i) = 0: i never fires in the good cycle. The good cycle has
configs.length configs. In each, i has value v. So EVERY good-cycle
config has i = v.

But the total number of configs in the system is prod(m_j). The number
with i = v is prod(m_j) / m_i = prod / 2.

The good cycle uses configs.length <= prod / 2 configs (all with i = v).
The "bad" configs include ALL configs with i = 1-v (there are prod/2 of them)
plus configs with i = v but not in the cycle.

For convergence: every bad config reaches the cycle. In particular, every
config with i = 1-v reaches the cycle (where i = v). So every starting
config with i = 1-v eventually has i change to v.

For i to change from 1-v to v: i must fire. So i IS privileged at some
config reachable from (i = 1-v). This means:
  ∃ config c (reachable, i = 1-v): f(i, c(left i), 1-v, c(ri)) != 1-v.

This is just a fact about the transition function. It doesn't directly
contradict fc(i) = 0 in the cycle.

DIFFERENT APPROACH: Think about right(i) = ri, also trapped.

ri is binary, fc = 0, constant value w. Same analysis:
  In cycle: f(ri, val(i), w, val(rri)) = w for all contexts.
  val(i) = v (constant). val(rri) varies.

For convergence from (ri = 1-w): need ri to fire eventually.

Now, BOTH i and ri are binary with constant values (v, w).
The good cycle configs all have (i = v, ri = w).
The number of such configs is prod(m_j) / (m_i * m_ri) = prod / 4.

Under sub-threshold: prod < 4 * 3^(n-2).
So configs with (i=v, ri=w): < 4 * 3^(n-2) / 4 = 3^(n-2).
The cycle length = configs.length <= 3^(n-2).

But the cycle length = sum of fire counts of the n-2 arc processors.
Each fires >= 2 times (from fireCount_ne_one + fires >= 1).
Wait, do all arc processors fire >= 1? We know left(i) and rri fire.
But interior arc procs?

From hno_safe: every proc has a nearby mover. For interior arc procs:
at least one of their neighbors fires. But does the proc ITSELF fire?

With fireCount_ne_one: if a proc fires >= 1 time, it fires >= 2 times.
But a proc CAN have fireCount = 0 (never fires).

Could an arc processor have fc = 0? Then it would be like i and ri
(constant value, never fires). If THREE consecutive procs have fc = 0...

Actually, if three consecutive procs have fc = 0, the middle one is safe
(none of its 3-neighborhood fires). hno_safe says no safe proc exists.
So we can't have 3 consecutive fc = 0 procs.

We already have 2 consecutive fc = 0 (i and ri). Can a third be adjacent?
left(i) has fc > 0 (fires CCW). rri has fc > 0 (fires CW). So no third
adjacent to i or ri has fc = 0. ✓

But a proc on the arc, not adjacent to i or ri, could have fc = 0.
E.g., proc 5 (middle of arc for n=9) could have fc = 0 IF its neighbors
3 and 4, or 6, fire to cover it for hno_safe.

Hmm, this still doesn't give a direct contradiction.

Let me try YET ANOTHER approach:
Show that the THREE consecutive binary {i, ri, rri} with i and ri having
fc=0 implies that right(i) (= ri) is safe.

ri's 3-neighborhood: {ri, left(ri), right(ri)} = {ri, i, rri}.
For ri to be safe: mover never visits ri, i, or rri.
We know fc(ri) = 0 and fc(i) = 0. So mover never visits i or ri.
But rri fires (cw > 0). So mover DOES visit rri. ri is NOT safe.

Hmm. What about finding a safe processor elsewhere?

For n >= 9: the arc has n-2 >= 7 procs. If only the two boundary procs
(left(i) and rri) fire, the middle procs would be safe.

Do only boundary procs fire? NO — the zero winding propagation forces
interior procs to fire too. From cw(rri) > 0: ccw(right(rri)) > 0.
So right(rri) fires. And from ccw(left(i)) > 0: cw(left(left(i))) > 0.
So left(left(i)) fires.

The propagation continues: every arc proc has both cw and ccw crossings
at its edges, so every arc proc fires. Wait, does it?

At edge (p, right(p)) on the arc: cw(p) = ccw(right(p)).
This relates cw of p to ccw of right(p). But p's total firing =
cw(p) + ccw(p) + stay(p). We know cw(p) or ccw(p) for some procs
but not all.

Actually, the key chain:
From rri end: cw(rri) > 0 → ccw(right(rri)) = cw(rri) > 0.
From left(i) end: ccw(left(i)) > 0 → cw(left(left(i))) = ccw(left(i)) > 0.

At edge (right(rri), right^2(rri)): cw(right(rri)) = ccw(right^2(rri)).
We know ccw(right(rri)) > 0 but not cw(right(rri)).

If cw(right(rri)) > 0: then ccw(right^2(rri)) > 0, and we propagate.
If cw(right(rri)) = 0: then ccw(right^2(rri)) = 0. right^2(rri) has
ccw = 0. Does it have cw?

From the other end: cw(left(left(i))) > 0. If left(left(i)) = right^2(rri)
(depends on n), then cw(right^2(rri)) > 0 too.

For n = 9, i = 0: arc = [2,3,4,5,6,7,8]. left(i) = 8. rri = 2.
left(left(i)) = 7. right(rri) = 3. right^2(rri) = 4.

Chain from rri=2: cw(2)>0 → ccw(3)>0. cw(3) = ccw(4). ccw(3)>0 but cw(3)?
Chain from left(i)=8: ccw(8)>0 → cw(7)>0. ccw(7) = cw(6). cw(7)>0 but ccw(7)?

These chains propagate from both ends toward the middle. Do they meet?
At proc 5: cw(5) = ccw(6). ccw(5) = cw(4).

We know from the right chain: ccw(3) > 0, ccw(4) = cw(3). But cw(3) is unknown.
We know from the left chain: cw(7) > 0, cw(6) = ccw(7). But ccw(7) is unknown.

Without more info, the interior procs MIGHT have cw=0 or ccw=0.

For example: cw(3) = 0 → ccw(4) = 0. Then proc 4 has ccw = 0.
From edge (4,5): cw(4) = ccw(5). If cw(4) = 0: ccw(5) = 0.
From edge (5,6): cw(5) = ccw(6). If cw(5) = 0: ccw(6) = 0.
But from left chain: cw(6) = ccw(7). And ccw(7) is unknown.

If ccw(7) = 0: cw(6) = 0. Then ccw(6) = 0 and cw(6) = 0.
Proc 6 has fc = cw + ccw + stay. If cw = ccw = 0: fc = stay ≥ 0.

Is there a "stay" step? stay means the mover stays at the same position
(direction = 0). For zero winding: stays contribute 0 to displacement.

Hmm, does the mover word allow "stay" steps? A stay step has mover p
and next mover also p (or at least the signed step is 0).

Actually, the mover at step k and the mover at step k+1 can be the same
processor. That's allowed. It means the same processor fires twice in a row.

With stay steps: a proc can fire with fc > 0 while having cw = ccw = 0.
It fires but stays (direction = 0 each time).

For proc 5: if it fires via stay steps only: fc(5) > 0 but cw(5) = ccw(5) = 0.
Then edge (4,5): cw(4) = ccw(5) = 0. Edge (5,6): cw(5) = ccw(6) = 0.

With cw(4) = 0 and ccw(4) = 0 (from cw(3) = 0 chain): proc 4 has
cw = ccw = 0. If proc 4 also fires only via stay: fc(4) > 0 but cw = ccw = 0.

Continuing: every proc in the middle of the arc could fire via stay only,
with cw = ccw = 0 at every arc edge.

But then: total CW = cw(2) + cw(8) (boundary). Wait, cw(8) = 0 (left(i) = 8,
cw = 0). So total CW = cw(2) = cw(rri) > 0. And total CCW = ccw(8) > 0.
CW = CCW (zero winding). So cw(2) = ccw(8).

Hmm, this scenario IS consistent. The mover fires at boundary procs (CW at 2,
CCW at 8) and fires via stay at interior procs (or doesn't fire at interior
procs at all). Interior procs might have fc = 0.

But if proc 5 has fc = 0: then {4, 5, 6} all need nearby movers (hno_safe).
If 4 fires (via stay): mover visits 4. Then 5's neighborhood {4,5,6} includes 4. ✓
If 4 doesn't fire: 5's neighborhood needs 5 or 6 to fire.

So with careful arrangement, interior procs CAN have fc = 0 without violating
hno_safe. But we can't have 3 consecutive fc = 0 (middle one safe).

KEY INSIGHT: i and ri already have fc = 0 (2 consecutive). If any arc proc
adjacent to i or ri ALSO has fc = 0, we get 3 consecutive fc = 0.
But left(i) and rri have fc > 0. So no 3 consecutive.

For procs far from i,ri: could 2 consecutive have fc = 0?
E.g., procs 4 and 5 both fc = 0. Then proc 4's 3-neighborhood = {3,4,5}.
Need mover in {3,4,5}. If 3 fires, ✓. If 3 doesn't fire: 4 or 5 must fire.
But fc(4) = fc(5) = 0. Contradiction!
So if both 4 and 5 have fc = 0, and 3 doesn't fire, proc 4 is safe. ✗ hno_safe.
But 3 MIGHT fire. If 3 fires: 4 is covered. 5's neighborhood {4,5,6}: need 6
to fire (since 4,5 don't fire). If 6 fires: ✓. If 6 doesn't fire AND 4,5 don't
fire: 5 is safe. So we need 6 to fire.

Bottom line: 2 consecutive non-firing procs is OK as long as BOTH sides fire.
3 consecutive non-firing means the middle is safe.

THIS MEANS: on the arc of n-2 ≥ 7 procs, with no safe processor, the maximum
number of consecutive non-firing procs is 2. And we need a "covering" pattern.

The question remains: does this lead to a CONTRADICTION with the other
hypotheses (zero winding, CW > 0, convergence, sub-threshold)?

I think the answer is: NOT from the hypotheses of double_trapped_baf_false alone
(even with _hconv and _hsub). The scenario IS consistent for generic systems.

But maybe with _hconv + _hsub + binary constraints, there IS a contradiction.
Let me think more...

ACTUALLY: with _hconv, maybe I can construct a ShadowTrap from the trapped pair.

Config c in the good cycle has (i = v, ri = w). Define c' = c with i = 1-v.
c' is NOT in the good cycle (since all cycle configs have i = v).

At c': who is privileged? Proc i might or might not be privileged.
If i is NOT privileged at c': f(i, c'(left i), 1-v, c'(ri)) = 1-v. Then
i doesn't fire. The mover is whoever fires in the good cycle at c (or
some other proc). Let p = the privileged proc at c'. Fire p to get c''.

Is c'' in the good cycle? c'' agrees with c' everywhere except at p.
c'' has i = 1-v (assuming p ≠ i, which is likely since i is non-privileged).
So c'' is NOT in the good cycle. It's another bad config.

This creates a chain: c' → c'' → c''' → ... of bad configs. For convergence,
this chain eventually reaches the good cycle. But for the first few steps
(where i = 1-v), the configs are all bad.

Can I find a CYCLE among these bad configs? That would be a ShadowTrap.

The configs with i = 1-v form a "shadow" of the good cycle. If the dynamics
restricted to i = 1-v create a closed orbit, that's a ShadowTrap.

For each good-cycle config c (with i = v), define shadow(c) = c but with i = 1-v.
At shadow(c): i has value 1-v. If i is not privileged at shadow(c):
  f(i, L, 1-v, R) = 1-v. Then the transition at shadow(c) fires the SAME proc
  as at c (if no other proc's privileged status changes).

Wait, changing i from v to 1-v changes the context at i's neighbors:
- left(i) sees right(left(i)) = i change from v to 1-v.
- ri sees left(ri) = i change from v to 1-v.

But i and ri don't fire in the cycle (fc = 0). So at any cycle step, the mover
is on the arc (not i or ri). For a mover p on the arc, far from i:
- p's context (left(p), p, right(p)) is unchanged between c and shadow(c)
  (since p, left(p), right(p) are all on the arc, and only i changed).
- So p is privileged at shadow(c) iff p is privileged at c.
- And the new value of p is the same: f(p, ...) depends on (left(p), p, right(p)).

For a mover p = left(i) (adjacent to i):
- p's context is (left(left(i)), left(i), i). In c: i = v. In shadow(c): i = 1-v.
- So p's R value changes. p might or might not be privileged at shadow(c).

For a mover p = rri (adjacent to ri):
- p's context is (ri, rri, right(rri)). In c: ri = w. In shadow(c): ri = w (unchanged!).
  Wait, shadow(c) only changes i, not ri! So ri's value is still w.
  Then rri's context is unchanged! rri is privileged at shadow(c) iff at c.

Hmm, so only left(i)'s context changes (because i is its right neighbor).
rri's context is unchanged (its left neighbor is ri, which is still w).

For movers NOT adjacent to i: context unchanged.
For left(i): R = val(i) changes from v to 1-v.

So the shadow dynamics differ from the good cycle ONLY at steps where
left(i) fires. At other steps, the mover and transition are identical.

If left(i) never fires (fc = 0): the shadow perfectly mirrors the good
cycle. But we KNOW left(i) fires (ccw > 0). So there are steps where
the shadow dynamics diverge.

At a step where left(i) fires in the good cycle:
- Good cycle context: (left(left(i)), left(i), v)
- Shadow context: (left(left(i)), left(i), 1-v)
These differ in R. So f(left(i), ...) might give a different result.
If f gives the same result: shadow matches good cycle at this step.
If f gives different: shadow diverges, and the resulting config is different.

CASE 1: f(left(i), L, S, 1-v) = f(left(i), L, S, v) for all relevant (L,S).
Then shadow perfectly mirrors the good cycle. shadow IS a closed cycle among
bad configs. ShadowTrap! Contradiction with convergence!

CASE 2: f gives different. Shadow diverges at left(i)'s fire step.

For CASE 1: we get a shadow trap directly. The shadow cycle = {shadow(c) : c in gc.configs}
is a closed orbit of bad configs. This contradicts convergence. False!

For CASE 2: the shadow diverges. We need a different argument.

But CASE 1 might not always hold. The transition function COULD map (L,S,1-v) ≠ (L,S,v).

Hmm, but we can construct a shadow by flipping BOTH i and ri:
Define shadow(c) = c with i = 1-v AND ri = 1-w.

At shadow(c): i = 1-v, ri = 1-w. The context changes at:
- i's neighbors: left(i) and ri.
- ri's neighbors: i and rri.

left(i)'s context: (left(left(i)), left(i), 1-v). R changed from v to 1-v.
rri's context: (1-w, rri, right(rri)). L changed from w to 1-w.

So both boundary procs (left(i) and rri) have changed contexts.

If BOTH boundary transitions are unchanged despite the flip:
  f(left(i), L, S, 1-v) = f(left(i), L, S, v) AND
  f(rri, 1-w, S, R) = f(rri, w, S, R)
Then the shadow is a perfect mirror. ShadowTrap → False.

If either changes: shadow diverges.

WHAT IF WE TRY ALL 4 FLIPS? i flip, ri flip, both flip, neither (= good cycle).
For each: check if the shadow mirrors the cycle. If any does: ShadowTrap.

With 4 options for (i_val, ri_val): (v,w), (v,1-w), (1-v,w), (1-v,1-w).
The good cycle has (v,w). The other 3 are potential shadows.
For each: the boundary transition functions determine if it's a closed orbit.

EVEN IF NONE of the 3 shadows perfectly mirrors: we can still get False
from convergence. Because from ANY starting config, the system reaches
the good cycle. This constrains the transition function.

OK I think the most promising approach is:
- Try the shadow with just i flipped. Check if it gives a ShadowTrap.
- If not: use convergence more directly.

Let me verify this for n=9 with a concrete system.
"""

print("The simplest proof for double_trapped_baf_false:")
print()
print("WITH convergence: construct a shadow by flipping the trapped binary proc.")
print("If f(left(i), L, S, 1-v) = f(left(i), L, S, v) for all (L,S):")
print("  → Shadow = closed orbit of bad configs → ShadowTrap → ¬converges → False")
print("If not:")
print("  → Need a different argument (convergence forces transition constraints)")
print()
print("KEY OBSERVATION: The shadow might not perfectly mirror.")
print("But with SUB-THRESHOLD + CONVERGENCE: we can enumerate ALL")
print("reachable configs from the shadow start and show they form a trap.")
print("This requires more infrastructure.")
print()
print("SIMPLER IDEA: with n >= 9 and the mover confined to n-2 procs,")
print("show that the REDUCED SYSTEM on the arc has too many configs for")
print("sub-threshold. The arc system has n-2 procs with product m(arc).")
print("But that doesn't obviously give a contradiction.")
print()
print("SIMPLEST VIABLE PROOF:")
print("Use small_arc_contradicts_convergence by finding a safe processor.")
print("Claim: with i and ri trapped (fc=0) and left(i) firing CCW only")
print("and rri firing CW only, the processor left(left(left(i))) is safe")
print("for n >= 9.")
print()
print("left(left(left(i))) = i - 3 on the ring.")
print("Its 3-neighborhood: {i-3, i-4, i-2}.")
print("For i-3 to be safe: mover never visits {i-3, i-4, i-2}.")
print("i-2 = left(left(i)). left(left(i)) fires CW (from zero winding propagation).")
print("So i-2 fires → i-3 is NOT safe.")
print()
print("Hmm, every proc adjacent to a firing proc is not safe.")
print("Since the arc has firing procs throughout (from zero winding)...")
print()
print("ACTUALLY, I think this sorry needs a fundamentally DIFFERENT approach.")
print("The trapped setup + convergence + sub-threshold together force a")
print("contradiction, but the proof requires constructing specific configs")
print("or using properties of the transition function that go beyond what")
print("the simple hno_safe / safe-processor arguments provide.")
