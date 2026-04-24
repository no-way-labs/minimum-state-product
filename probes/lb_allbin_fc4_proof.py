"""
Prove: all-binary-fc≥4 → False
Hypotheses: sub-threshold product, n ≥ 9, ≥ 3 binary, zero-winding with cw > 0,
all fc ≥ 2, some fc ≥ 3.

APPROACH: CL counting via edge traversal and binary parity.

Key facts:
1. sum_fireCount: CL = Σ fc(p)
2. binary_fireCount_even: binary proc b has even fc
3. edgeTraversalCount_even_of_zeroWinding: every edge crossed even times
4. edgeTraversalCount_left_add_edgeTraversalCount = 2 * (fc(p) - stay(p))
5. Sub-threshold + ≥3 binary: prod < 4·3^(n-2), at least 3 procs have m=2

The argument: all binary fc ≥ 4 forces CL ≥ 4B + 2(n-B) = 2n + 2B ≥ 2n + 6.
But we also know some fc ≥ 3. Combined with CL = Σ fc:

CL = Σ fc ≥ 4B + 2(n-B) + 1 = 2n + 2B + 1 ≥ 2n + 7

Wait, that extra +1 comes from some fc ≥ 3 but that proc might be binary (fc ≥ 4, already counted).

Actually: we have ∀ binary: fc ≥ 4, and ∀ non-binary: fc ≥ 2.
Plus ∃ q: fc(q) ≥ 3.
If q is binary: fc(q) ≥ 4 (already counted).
If q is non-binary: fc(q) ≥ 3, giving extra +1.

Case 1: q is non-binary.
CL ≥ 4B + 3 + 2(n-B-1) = 4B + 3 + 2n - 2B - 2 = 2n + 2B + 1 ≥ 2n + 7.

Case 2: q is binary.
CL ≥ 4B + 2(n-B) = 2n + 2B ≥ 2n + 6.
But fc(q) ≥ 4 is already in the 4B sum. The "some fc ≥ 3" doesn't help.

Either way: CL ≥ 2n + 6.

Now: can we get CL ≤ 2n from the zero-winding structure? NO — that's circular
(CL = 2n is proved USING this sorry).

The argument needs to use sub-threshold product DIRECTLY.

NEW APPROACH: sub-threshold product bounds the number of configs.
CL ≤ product (since all configs in good cycle are distinct).
product < 4 · 3^(n-2).

With all binary fc ≥ 4:
CL ≥ 4B + 2(n-B) = 2n + 2B.

For this to be ≤ product: 2n + 2B ≤ 4 · 3^(n-2).
For n=9, B=3: 24 ≤ 8748. No contradiction.

So pure counting won't work.

DEEPER APPROACH: Use the ZERO-WINDING and EDGE TRAVERSAL constraints.

Zero winding means: for each edge, edgeTraversalCount is even.
edgeTraversalCount(left p, p) + edgeTraversalCount(p, right p) = 2 * (fc(p) - stay(p)).

For binary p with fc ≥ 4:
2 * (fc(p) - stay(p)) = ET(left) + ET(right), both even.
fc(p) - stay(p) ≥ 4 - stay(p).
stay(p) ≤ fc(p) (at most all firings are stay moves).

For a BINARY proc, what are "stay" moves? A stay move means the mover doesn't
change sides (fires at the same position again without moving). For binary proc b:
a stay move at b means b fires and the NEXT mover is also b. But we proved that
binary procs can't fire at consecutive steps (in my earlier analysis). So stay(b) = 0!

Wait: "stayMoveCount" might mean something different. Let me check.

Actually: stayMoveCountAt is the number of times the mover fires at p and stays at p
(the next mover is also p). But we showed no consecutive firings at binary procs.
So stayMoveCountAt(b) = 0 for binary b.

Therefore: ET(left b) + ET(right b) = 2 * fc(b) for binary b with fc ≥ 4.

Each ET is even (zero winding). So ET(left b) + ET(right b) = 2 * fc(b) ≥ 8.
Both terms even and ≥ 0. So each term ≥ 0 and sum ≥ 8.

The minimum per edge: ET ≥ 0 (could be 0). But if both neighbors of b have
ET ≥ 2 from other procs...

Hmm, let me think about the TOTAL edge traversal count.

Sum over all edges: Σ ET(e) = 2 * CL (each step crosses one edge, counted twice
for left and right... wait, actually each step where the mover is p contributes
to ET(left p) or ET(right p) or neither (stay move)).

Actually: Σ_p ET(left p) = Σ_p (cwMoveCountAt(p) + ccwMoveCountAt(p))
= cwStepCount + ccwStepCount = CL - stayStepCount.

Wait: cwStepCount + ccwStepCount + stayStepCount = CL.
And Σ_e ET(e) = Σ_p (cwMoveCountAt(p) + ccwMoveCountAt(p)) + ... hmm, edges and
procs are different objects.

Edge e = (p, right p) for each p. ET(e) counts transitions across this edge.
ET(e) = cwMoveCountAt(p) + ccwMoveCountAt(right p).

Under zero winding: cwMoveCountAt(p) = ccwMoveCountAt(right p) for each p.
So ET(e) = 2 * cwMoveCountAt(p) for each edge.

Total: Σ_e ET(e) = 2 * Σ_p cwMoveCountAt(p) = 2 * cwStepCount.
Under zero winding: cwStepCount = ccwStepCount.
CL = cwStepCount + ccwStepCount + stayStepCount = 2 * cwStepCount + stayStepCount.

Σ_e ET(e) = 2 * cwStepCount = CL - stayStepCount.

Now: from binary procs, Σ_b (ET(left b) + ET(right b)) = 2 * Σ_b fc(b)
(using stay(b) = 0).

But ET(left b) = ET(b-1, b) and ET(right b) = ET(b, b+1).
Each edge appears in at most two such sums (from the two endpoints).

So: 2 * Σ_b fc(b) = Σ_b (ET(left b) + ET(right b)) ≤ 2 * Σ_e ET(e)
(each edge counted at most twice).

This gives: Σ_b fc(b) ≤ Σ_e ET(e) = CL - stayStepCount ≤ CL.

But Σ_b fc(b) ≤ CL is trivially true. No new info.

Let me try the PRODUCT constraint more carefully.

Sub-threshold: Π m_i < 4 · 3^(n-2).
B binary procs: Π_{binary} m_i = 2^B.
Non-binary procs: Π_{non-binary} m_i ≥ 3^(n-B).
Product = 2^B * Π_{non-binary} m_i < 4 · 3^(n-2).

So: 2^B * 3^(n-B) ≤ Π m_i < 4 · 3^(n-2).
→ 2^B < 4 · 3^(B-2) = 4 · 3^(B-2).
→ (2/3)^B < 4/9.
→ B ≥ 3 is needed (and B can be up to about n/2 for large n).

For B = 3: Π ≥ 8 · 3^(n-3) and Π < 4 · 3^(n-2) = 12 · 3^(n-3).
So 8 · 3^(n-3) ≤ Π < 12 · 3^(n-3).

Hmm. CL ≤ Π < 12 · 3^(n-3). But CL ≥ 2n + 6 (from binary fc ≥ 4 bound).
12 · 3^(n-3) >> 2n + 6 for n ≥ 9. No contradiction.

OK let me try a COMPLETELY DIFFERENT approach. The key insight I discovered earlier:

**Trigger Lemma**: immediately before a binary proc b fires, its neighbor must
have just fired.

With fc(b) ≥ 4 firings of b, each preceded by a neighbor firing:
The fc(b) firings of b are at steps t_1, t_2, ..., t_{fc(b)}.
At each t_i - 1, a neighbor of b fires.

Between consecutive firings t_i and t_{i+1}: at least one step (the one
immediately before t_{i+1}, which fires a neighbor of b).

The step immediately AFTER t_i also fires a neighbor of b (similar argument).

So the mover sequence near b has pattern:
..., neighbor, b, neighbor, [stuff], neighbor, b, neighbor, [stuff], ...

Now: with ≥ 3 binary procs, each with fc ≥ 4:
Total neighbor-trigger firings needed = Σ_b fc(b) ≥ 4B (one trigger per firing).
But triggers can overlap (the post-trigger of one b-firing may serve as pre-trigger
of another binary's firing).

The tight constraint: each binary proc's 4+ firings are INTERSPERSED with
neighbor firings. For isolated binary procs (both neighbors non-binary),
each trigger is a non-binary neighbor.

For non-binary proc u adjacent to binary b: u provides some triggers for b.
u fires fc(u) ≥ 2 times. It can provide at most fc(u) triggers.

Total triggers available from non-binary procs ≥ triggers needed.
But the key: the triggers are ORDERED in time. The trigger for b's k-th firing
must happen at the right position. This creates sequencing constraints.

Hmm, I keep getting qualitative constraints but not a clean contradiction.

Let me think about this from the WINDING perspective.

Zero winding means the mover walk has zero net displacement. CW steps = CCW steps.
Each binary proc b fires fc(b) times. Each firing is either CW or CCW.
CW firings at b: the walk goes ... → b → right(b) → ...
CCW firings at b: the walk goes ... → b → left(b) → ...
(or stay firings, but we showed stay = 0 for binary).

For b with fc ≥ 4: 4+ firings, 0 stay. So fc = cwMoveCountAt(b) + ccwMoveCountAt(b).
Both ≥ 0. With fc ≥ 4: at least 2 CW and 2 CCW (since both are at least 1? Actually no.)

Zero winding at the EDGE level: cwMoveCountAt(p) = ccwMoveCountAt(right p) for all p.
But at the PROC level: cwMoveCountAt(b) and ccwMoveCountAt(b) aren't necessarily equal.

Hmm. The key geometric constraint: the walk is a CLOSED path on the ring with
zero winding. It goes back and forth.

With all binary fc ≥ 4: each binary proc is visited 4+ times by the walk.
The walk crosses each binary proc at least 4 times. Each crossing either goes
CW or CCW (since stay = 0).

For a single binary proc b: cwFirings + ccwFirings = fc(b) ≥ 4.
If cwFirings ≥ 2 and ccwFirings ≥ 2: b is a "passthrough" (the walk passes
through b in both directions multiple times).

If cwFirings = fc and ccwFirings = 0 (or vice versa): all firings in same direction.
But this would mean the walk always crosses b in the CW direction.
Under zero winding: the net displacement across each edge is 0.
ET(left b, b) = 2 * cwMoveCountAt(left b) (under ZW).
Wait, let me think about this more carefully.

The edge (b-1, b) has ET = cwMoveCountAt(b-1) + ccwMoveCountAt(b).
Under ZW: cwMoveCountAt(b-1) = ccwMoveCountAt(b).
So ET(b-1, b) = 2 * ccwMoveCountAt(b).

If ccwMoveCountAt(b) = 0: ET(b-1, b) = 0. The edge is never traversed.
But fairness requires every proc to fire, and the walk must reach every proc.
If edge (b-1, b) is never traversed: the walk never crosses from b-1 to b or
from b to b-1. But b fires (fc ≥ 4), so the walk visits b. And b-1 fires (fc ≥ 2).
How can both be visited without crossing the edge between them?

They CAN'T. The walk is a connected path on the ring. If the edge (b-1, b) is
never traversed, then b and b-1 are on opposite sides of a "gap." But the ring
is a cycle — there's another path from b-1 to b going the other way around.
So both are reachable as long as the entire ring is connected (which it is).

Wait: the walk IS a sequence of mover positions on the ring. At each step, the
mover is at some position and moves to an adjacent position (CW or CCW) or stays.
If the walk visits both b and b-1 but never crosses the edge between them: the
walk reaches b from the right side and b-1 from the left side, going around the
ring the long way. This IS possible.

So ccwMoveCountAt(b) = 0 is possible if the walk always approaches b from the right.

But then: cwMoveCountAt(b) = fc(b) ≥ 4. All firings of b are CW.
Edge (b, b+1) has ET = cwMoveCountAt(b) + ccwMoveCountAt(b+1) = fc(b) + ccwMoveCountAt(b+1).
This must be even (ZW). fc(b) is even (binary), so ccwMoveCountAt(b+1) must be even.

Now: what does this mean for the neighbors?

I think the clean argument uses the relationship between binary fire counts
and edge traversal counts to derive a constraint that's violated when ALL
binary have fc ≥ 4.

Let me look at it from the PARITY of edge traversal counts.

Under ZW, every ET is even. So for each binary proc b:
ET(left b) + ET(right b) = 2 * fc(b) ≥ 8 (even, ≥ 8).

Each ET is even: ET(left b) = 2a, ET(right b) = 2c. So a + c = fc(b) ≥ 4.

These are just the CW counts: a = cwMoveCountAt(left b), c = ccwMoveCountAt(right b) = cwMoveCountAt(b)
(under ZW). Wait: ET(left b) = ET(left b, b) = cwMoveCountAt(left b) + ccwMoveCountAt(b).
Under ZW: cwMoveCountAt(left b) = ccwMoveCountAt(b). So ET(left b) = 2 * cwMoveCountAt(left b) = 2 * ccwMoveCountAt(b).

Hmm, so the constraints are just on the CW move counts.

Actually, I think I should try a SIMPLER approach.

** THE CL UPPER BOUND FROM DISTINCT CONFIGS **

In a good cycle, all CL configs are distinct. Each config is a tuple of proc values.
The number of distinct configs ≤ product. So CL ≤ product < 4 · 3^(n-2).

But also: with B ≥ 3 binary procs, the value sequence at each binary proc
alternates between 0 and 1. With fc(b) = 4: the value at b goes through
pattern 0, 1, 0, 1, 0 (or 1, 0, 1, 0, 1) over the cycle. This means b is
in state 0 for roughly CL/2 steps and state 1 for roughly CL/2 steps.

The configs with b = 0 and b' = 0 (two binary procs): their count is
≤ (CL/2)² ≈ CL²/4. But the total number of configs with specific binary
values is bounded by the product of non-binary state sizes.

Wait — I'm overcomplicating this.

Let me think about it super simply.

CLAIM: with B ≥ 3 binary procs each having fc ≥ 4, the number of distinct
configs requires product ≥ ... ?

Each binary proc b has 4 "transition points" where its value changes.
Between transitions, b's value is fixed. The 4 transitions split the
CL steps into 4 intervals. In each interval, b's value is constant.

For TWO binary procs b1, b2 with fc ≥ 4 each: their 8 transitions
create at most 8 intervals (actually up to 8 since transitions may coincide).

Hmm. The product constraint doesn't directly help either.

OK LET ME JUST COMPUTE. What happens for concrete small examples?
"""

import itertools
from collections import Counter

def check_zero_winding_cycles(n, ms, max_cl=50, verbose=True):
    """Check if zero-winding good cycles with all binary fc ≥ 4 exist."""
    binary_procs = [i for i in range(n) if ms[i] == 2]
    B = len(binary_procs)
    if B < 3:
        return

    product = 1
    for m in ms:
        product *= m
    threshold = 4 * (3 ** (n - 2))

    if verbose:
        print(f"\nn={n}, ms={ms}, B={B}, product={product}, threshold={threshold}")

    if product >= threshold:
        if verbose:
            print("  Not sub-threshold, skip")
        return

    # For small n, enumerate good cycles as mover sequences with value tracking.
    # A good cycle is a sequence of (config, mover) where:
    # 1. Each config has exactly one privileged proc (the mover)
    # 2. All configs are distinct
    # 3. Mover changes mover's value
    # 4. Cycle returns to start

    # Too expensive for general n. Let me check specific small cases.

    # For the proof: we need to show it's IMPOSSIBLE to have all binary fc ≥ 4.
    # So if the computation finds 0 such cycles, that's evidence.

    # Instead of full enumeration, count the constraint:
    # CL = sum(fc) ≥ 4B + 2(n-B) = 2n + 2B
    min_CL = 4 * B + 2 * (n - B)
    if verbose:
        print(f"  Min CL from fc bounds: {min_CL}")
        print(f"  CL ≤ product = {product}")

    return min_CL

# Test for various configurations
configs_to_test = []

# n=5, B=3: ms = permutations of (2,2,2,3,3)
for perm in set(itertools.permutations([2,2,2,3,3])):
    ms = list(perm)
    n = len(ms)
    binary_procs = [i for i in range(n) if ms[i] == 2]
    B = len(binary_procs)
    if B >= 3:
        product = 1
        for m in ms:
            product *= m
        threshold = 4 * (3 ** (n - 2))
        if product < threshold:
            configs_to_test.append((n, ms))

print("=== n=5 sub-threshold configs with B≥3 ===")
seen = set()
for n, ms in configs_to_test:
    key = tuple(ms)
    if key in seen:
        continue
    seen.add(key)
    check_zero_winding_cycles(n, ms, verbose=True)

# n=9 examples
print("\n=== n=9 examples ===")
# B=3: (2,3,2,3,2,3,3,3,3) and rotations
ms9_B3 = [2,3,2,3,2,3,3,3,3]
check_zero_winding_cycles(9, ms9_B3)

# B=4
ms9_B4 = [2,3,2,3,2,3,2,3,3]
check_zero_winding_cycles(9, ms9_B4)

# B=5
ms9_B5 = [2,3,2,3,2,3,2,3,2]
check_zero_winding_cycles(9, ms9_B5)

print("\n\n=== KEY ANALYSIS ===")
print("""
The pure CL counting approach fails because CL can be much less than the product.
With n=9, B=3: min CL = 24 vs product up to 5832.
Need a structural argument, not just counting.

But wait — re-reading the Lean code, the sorry appears in a context that already
has _hq : gc.fireCount _q ≥ 3 and h_all_ge4. The proc _q with fc ≥ 3 might not
be binary. If _q is non-binary with fc ≥ 3: all binary fc ≥ 4, non-binary fc ≥ 2,
at least one non-binary fc ≥ 3.

The real question: is there a direct pigeonhole argument at a binary proc?

TRIGGER LEMMA (proved above): immediately before binary b fires, a neighbor fires.
This means: b's context changes at the firing step (the trigger changes L or R).

KEY OBSERVATION: Consider binary proc b with fc = 4. Its 4 firings alternate
S = 0, 1, 0, 1 (or 1, 0, 1, 0). At S=0: fires twice. At S=1: fires twice.

At each S=0 firing: context (L, 0, R). The trigger changed either L or R to make
b become privileged. Let's say the trigger is the left neighbor u = b-1.

Then just before b fires: u's value changed from L_old to L_new, and b became
privileged. So:
  f_b(L_old, 0, R) = 0 (b not privileged before trigger)
  f_b(L_new, 0, R) = 1 (b privileged after trigger)
So (L_old, R) ∈ N_0 and (L_new, R) ∈ M_0 with L_old ≠ L_new.

Right after b fires (0→1): context becomes (L_new, 1, R). Next mover is a neighbor
of b. b is NOT privileged: f_b(L_new, 1, R) = 1, so (L_new, R) ∈ N_1.

So (L_new, R) ∈ M_0 ∩ N_1. Since M_0 ∩ M_1 = ∅ and N_1 = complement(M_1):
M_0 ⊂ N_1 (already shown).

Now: consider the TWO S=0 firings of b, with contexts (L₁, 0, R₁) and (L₂, 0, R₂).
Both (L₁, R₁) and (L₂, R₂) ∈ M_0.

And the two S=1 firings: (L₃, 1, R₃) and (L₄, 1, R₄).
Both (L₃, R₃) and (L₄, R₄) ∈ M_1.

M_0 ∩ M_1 = ∅.

Now: the global configs are all distinct. The contexts at b may or may not repeat.
If they DO repeat: same (L,S,R) at b at two different steps. The rest of the
config differs.

For entry conflict: same (L,S,R) at mover step and non-mover step. We showed this
is impossible for a SINGLE proc (f_b is well-defined). So there's no entry conflict
at b from b's own mover/non-mover appearances.

But entry conflict can be at ANY proc. The all-binary-fc≥4 condition might force
entry conflict at a NON-BINARY proc.

Actually, re-reading the Lean code: the sorry just needs to derive False. It doesn't
need to show entry conflict at a specific proc. Maybe it uses the convergence property
or some other infrastructure.

Let me look at what's available in the proof context more carefully.
""")

# Actually, let me look at this from the EDGE TRAVERSAL perspective with concrete numbers.
print("\n=== EDGE TRAVERSAL ANALYSIS ===")
print("""
Under zero winding, for each proc p:
  ET(left p) + ET(right p) = 2 * (fc(p) - stay(p))

For binary p: stay(p) = 0 (proved: no consecutive firings).
So ET(left p) + ET(right p) = 2 * fc(p).

With all binary fc ≥ 4:
  For each binary b: ET(left b) + ET(right b) ≥ 8.

Each ET is even (zero winding). Let ET(left b) = 2a_b, ET(right b) = 2c_b.
Then a_b + c_b = fc(b) ≥ 4.

Sum over all procs:
  Σ_p ET(left p) = Σ_p ET(right p) = Σ_p ET(p) (just re-indexing)
  Σ_p (ET(left p) + ET(right p)) = 2 * Σ_p ET(p) = 2 * Σ_e ET(e) = 2 * (CL - stayStepCount)

Wait: Σ_e ET(e) = CL - stayStepCount (total non-stay moves = edge traversals).
And Σ_p (ET(left p) + ET(right p)) counts each edge TWICE (once from each endpoint).
So Σ_p (ET(left p) + ET(right p)) = 2 * Σ_e ET(e) = 2 * (CL - stayStepCount).

Also: Σ_p (ET(left p) + ET(right p)) = Σ_p 2 * (fc(p) - stay(p))
  = 2 * (CL - stayStepCount)    [since Σ fc = CL, Σ stay = stayStepCount]

So this is just a tautology. No new info.

Hmm. Let me think about what "converges sys gc" gives us that might help.

Actually: "converges sys gc" is about the system's convergence property (no bad
cycles). This is a GLOBAL property of the system, not just the good cycle.

Wait — in the lower bound proof, we're assuming for contradiction that a valid
system exists with sub-threshold product. So converges is part of the system being
valid. The sorry needs to show that under these assumptions, we can derive False.

But can we USE converges directly? It means: in the bad-config transition graph,
there are no cycles. Every path from a bad config eventually reaches a good config.

Hmm. This is a property of the SYSTEM (with transition functions), not just the
good cycle. It might not directly help with the fire count argument.

Let me re-think from scratch.

=== BREAKTHROUGH IDEA ===

Consider the sub-threshold constraint from a DIFFERENT angle:
CL ≤ product < 4 · 3^(n-2).

The number of distinct non-binary-proc value tuples ≤ Π_{non-binary} m_i.
For each tuple of non-binary values, the binary values are determined by the
cycle position (they alternate).

With B binary procs each having fc ≥ 4: each binary proc takes value 0 for
some steps and value 1 for others. The combination of binary values forms a
B-bit vector. There are 2^B possible combinations.

At each step of the cycle, the full config is (binary values, non-binary values).
The binary values form one of 2^B vectors.

With fc(b) ≥ 4 for all binary b: b's value changes 4+ times. Between changes,
b's value is fixed. So the binary value vector changes at every step where a
binary proc fires.

But the binary value vector has only 2^B ≤ 2^{n/2} possible values.
The non-binary value tuple has ≤ Π_{non-binary} m_i possibilities.

Total distinct configs ≤ 2^B × Π_{non-binary} m_i = product.
This is just CL ≤ product, nothing new.

=== ALTERNATIVE: use the neighbor-trigger constraint ===

At each binary firing, a neighbor triggers it. The triggers are specific
neighbor firings at specific values. With fc ≥ 4 at binary b, we need 4 triggers.

The trigger at the left neighbor u changes u's value from L_old to L_new.
This uses one of u's firings. Since u fires fc(u) times, it can provide at most
fc(u) triggers for b.

With both neighbors of b being non-binary (non-consecutive case):
u = left(b) has fc(u) ≥ 2 firings, v = right(b) has fc(v) ≥ 2 firings.
Total triggers available: fc(u) + fc(v).
Triggers needed for b: fc(b) ≥ 4.
So fc(u) + fc(v) ≥ fc(b) ≥ 4. ✓ (already shown above)

But the triggers must be appropriately PLACED. Trigger for b's k-th firing
must happen just before b fires. And NOT overlap with triggers for other
binary procs.

If u is adjacent to TWO binary procs b and b' (non-consecutive case allows this):
u provides triggers for both b and b'. u fires fc(u) times. Some firings trigger
b, some trigger b', some trigger neither (if u fires but neither b nor b' fires next).

Actually, a single u firing can only trigger ONE binary neighbor (the one that
fires in the very next step). So fc(u) triggers are split among up to 2 binary
neighbors.

For binary b with both neighbors non-binary, each non-binary neighbor u:
Triggers from u for b ≤ fc(u).
Triggers from u for other binary neighbors of u ≤ fc(u).
Total: triggers from u ≤ fc(u) (each firing is one trigger).

So: triggers for b = (triggers from left(b)) + (triggers from right(b)) ≥ fc(b) ≥ 4.

Let me count GLOBALLY:
For each binary proc b: at least fc(b) triggers needed from its two neighbors.
Total triggers needed: Σ_b fc(b) ≥ 4B.

Each non-binary proc u provides at most fc(u) triggers (one per firing) to its
binary neighbors (at most 2).

Each binary proc b also provides triggers to adjacent binary procs (if any).
But with B ≥ 3 binary and no 3 consecutive: each binary has at most 1 binary
neighbor.

Total triggers available: Σ_p fc(p) = CL (each firing might be a trigger).
But not all firings are triggers (only those immediately before a binary firing).

Triggers needed = Σ_b fc(b). Each trigger is a specific step where p fires and
the next step fires a binary neighbor of p.

Total trigger-provider steps = Σ_b (fc(b)) = Σ_b fc(b) ≤ CL.

This is always satisfiable. No contradiction from counting alone.

=== WHAT IF THE ARGUMENT IS ABOUT CYCLE STRUCTURE, NOT COUNTING? ===

The zero-winding condition imposes a topological constraint on the mover walk.
With CL > 2n: the walk must have "extra" steps beyond the simple back-and-forth.
These extra steps create repeated local contexts (by the pigeon principle on the
BINARY proc's state and its neighborhood).

Wait — HERE's the key insight I've been missing:

At a binary proc b with fc = 4: b fires at steps t_1, t_2, t_3, t_4.
The mover walk at these steps crosses b in some direction (CW or CCW).
The zero-winding constraint means the GLOBAL CW/CCW counts balance.

But at b: cwFirings(b) + ccwFirings(b) = fc(b) = 4.
Under ZW: the edge (left b, b) has ET = 2 * ccwFirings(b) (even).
The edge (b, right b) has ET = 2 * cwFirings(b) (even).

So cwFirings(b) and ccwFirings(b) are both non-negative integers summing to 4.
Possible: (0,4), (1,3), (2,2), (3,1), (4,0).
But ET must be even: 2*cwFirings and 2*ccwFirings are both even (always true).
So all 5 cases are possible.

If cwFirings(b) = 0: the walk always enters b from the right and exits to the right
(CCW at b). It never crosses the left edge. Then ET(left b, b) = 0.
This means the walk segment from left(b) to b is disconnected at this edge.
But both left(b) and b fire (fc ≥ 2). How do they both get visited?

Via the OTHER path around the ring! The walk goes from left(b) around the entire
ring the long way to reach b, and vice versa.

This is possible but creates a LONG walk. With 3 binary procs, if each has a
"dead edge", the walk might not be able to reach all procs.

CLAIM: With B ≥ 3 binary procs each having fc ≥ 4, at least one binary must have
cwFirings ≥ 2 AND ccwFirings ≥ 2 (i.e., both edges are traversed).

Proof: Suppose all binary procs have one dead edge. Then B dead edges on the ring.
The walk must navigate a ring with B missing edges. If B ≥ 3 and the missing edges
are "well-spaced": the ring breaks into B arcs, but the walk can't visit all arcs
(it must stay connected). CONTRADICTION with fc ≥ 2 for all procs.

Wait: the walk IS a single connected path (it's a cycle on the ring). It CAN
visit all arcs even with missing edges — it just needs to "loop around" through
arcs that are connected. But with B ≥ 3 missing edges on a ring of n ≥ 9 procs:
the ring is partitioned into B arcs. The walk can only traverse edges that exist.
With B missing edges, the "available" edges form B arcs. The walk is a closed path
on these arcs.

Actually the walk is a closed path on the POSITIONS (ring vertices), and it
traverses edges. If edge (left b, b) has ET = 0: the walk never goes from left(b)
to b or from b to left(b). So left(b) and b are in different connected components
of the "traversed edges" graph.

For ALL procs to be visited (fc > 0): the "traversed edges" must form a connected
graph on all n vertices. With B dead edges on an n-cycle: the remaining edges form
B arcs. These B arcs are connected iff B = 0 (all edges present) or if the "dead
edges" leave the graph connected. But removing even one edge from a cycle
DISCONNECTS it into two arcs... wait, no. The ring has n edges. Removing one edge
from a cycle gives a PATH (still connected). Removing two edges gives 3 components
if the removed edges are distinct, or... no.

Wait: n edges on n vertices in a cycle. Remove 1 edge: n-1 edges, still connected
(it's a path). Remove 2 edges: n-2 edges. If the 2 removed edges are distinct, the
graph has 2 components (two paths). Remove 3: 3 components (if edges are distinct
and non-adjacent in the cycle... actually depends on positions).

ACTUALLY: removing k edges from an n-cycle partitions it into at most k connected
components (arcs).

For our case: B dead edges (one per binary proc) partition the ring into at most
B arcs. Each arc is a connected path.

The walk must visit ALL n procs → ALL arcs must be visited.
But the walk is a CLOSED path on the "traversed edges" subgraph.
If the traversed edges form a disconnected graph: the walk can only visit one
connected component. CONTRADICTION.

So: the "traversed edges" subgraph must be CONNECTED.

If every binary proc has one dead edge (either left or right dead):
B dead edges are removed. The remaining graph has B arcs.
For B ≥ 2: the graph is disconnected. CONTRADICTION!

WAIT: that can't be right for B = 2. Removing 2 edges from an n-cycle gives
at most 2 connected components. If both dead edges are at the same place: nah,
they're at different positions (different binary procs).

Actually: each binary proc b contributes AT MOST one dead edge. With B binary procs,
we remove at most B edges. The remaining graph is connected iff we removed fewer
than... well, an n-cycle minus k edges (k < n) is connected iff k = 0 or the
removed edges don't disconnect the cycle. Removing 1 edge: still connected (a path).
Removing 2 edges: disconnected into 2 pieces. Removing k edges: at most k pieces.

Wait no: removing 1 edge from a cycle gives a PATH (connected). But wait, if the
walk traverses edges, and one edge has ET = 0, that means the walk doesn't use that
edge. But the walk is a CYCLE on the ring. It's a sequence of positions. At each step
it moves to an adjacent position (CW or CCW or stays).

If an edge is never traversed: the walk never goes across it. But the walk starts
at some position, makes CL moves, and returns. If the walk visits positions on both
sides of the dead edge: it must cross the dead edge at some point. CONTRADICTION
with ET = 0.

UNLESS: the walk visits all positions on one side, then goes all the way around the
ring to visit positions on the other side of the dead edge, crossing it zero times
but still visiting everything by going the "long way."

Wait: the dead edge between b and left(b) means the walk never goes from left(b) to
b or from b to left(b). But the walk CAN reach both b and left(b) by going around
the rest of the ring.

Example: ring with 5 nodes 0-1-2-3-4-0. Dead edge: (4, 0). Walk: 0→1→2→3→4→3→2→1→0.
This visits all procs and traverses edge (4,0) zero times. It goes 0→1→2→3→4 (CW)
then 4→3→2→1→0 (CCW). Both 4 and 0 are visited.

So ONE dead edge is fine. What about TWO dead edges?

Dead edges: (4, 0) and (1, 2). Walk must visit 0, 1, 2, 3, 4 without crossing (4,0)
or (1,2). Starting from 0: can go to 1 (cross edge 0-1), but can't go to 2 (dead
edge 1-2). So from 1, must go back to 0, then around: 0→4... wait, (4,0) is dead.
Can't cross from 0 to 4 or 4 to 0.

So from 0: can only go to 1 and back. Can't reach 2, 3, or 4. DISCONNECTED!

But wait: the "traversable" edges are {0-1, 2-3, 3-4}. Components: {0,1} and {2,3,4}.
Walk starting at 0 can only visit {0,1}. Can't reach {2,3,4}. But ALL procs must
fire (fc ≥ 2). CONTRADICTION!

So: ≥ 2 dead edges → disconnection → contradiction with fc ≥ 2 for all procs.

Now: IF all binary procs have one dead edge (cwFirings = 0 or ccwFirings = 0),
we get B dead edges. For B ≥ 3: at least 2 dead edges → disconnection → False.

ACTUALLY we need B ≥ 2. And B ≥ 3 (hypothesis).

But wait: it's possible that SOME binary procs have NO dead edge (both cwFirings ≥ 1).
The claim is: all binary fc ≥ 4 → False.

Let me check: can all binary have cwFirings ≥ 1 AND ccwFirings ≥ 1?
If so: no dead edges from binary. But then from non-binary procs: they might have
dead edges. Actually non-binary procs can have stay moves (stay > 0), so
ET(left p) + ET(right p) = 2 * (fc(p) - stay(p)). If stay > 0: ET can be smaller.

Hmm, this approach doesn't directly give "all binary fc ≥ 4 → False."

Let me reconsider. The claim in the Lean code is that with the given hypotheses,
all binary fc ≥ 4 → False. Let me check: is there another route to False?

Looking at the proof context: we have `_hconv : converges sys gc`. Can this be used?

Also: `_hno_safe` is not directly in the sorry's scope but IS in the outer theorem.
Let me check.
""")
