"""
PROOF: All binary fc >= 4 -> False

THEOREM: In a zero-winding good cycle gc with:
  - sys.rs.n >= 9
  - converges sys gc
  - subThreshold sys.rs (product < 4 * 3^(n-2))
  - hasGe3Binary sys.rs (>= 3 binary procs)
  - gc.zeroWinding
  - 0 < gc.cwStepCount
  - all fc >= 2
  - exists q with fc(q) >= 3
  - all binary procs b have fc(b) >= 4

then False.

===========================================================================
PROOF
===========================================================================

The proof proceeds by showing that all binary fc >= 4 forces the good cycle
to have >= 2 dead edges in the ring, disconnecting the mover walk and
contradicting the fact that every processor fires (fc >= 2).

STEP 1: Binary stay = 0.

Lemma (binary_stayMoveCountAt_eq_zero): For binary proc b in a good cycle
with configs.length >= 3, stayMoveCountAt(b) = 0.

Proof: Suppose stayMoveCountAt(b) > 0. Then there exists step k with
moverAt(k) = b and moverAt(nextIndex k) = b. Since b is binary (m_b = 2),
b's value toggles at each firing.

At step k: b fires, toggling value v -> 1-v.
At step k+1: b fires again, toggling value 1-v -> v.

Only b's value changes at steps k and k+1 (one proc fires per step).
So config(k+2) agrees with config(k) at all procs other than b, and
at b: value v -> 1-v -> v (returns to v).

Hence config(k+2) = config(k). Since configs.length >= 3, step k+2
is a different index from step k. This contradicts gc.distinct.

Therefore stayMoveCountAt(b) = 0. QED.

Note: This is a STRICT GENERALIZATION of the existing
  stayMoveCountAt_eq_zero_of_binary_fireCount_two (which requires fc=2).
  The proof is identical and does not depend on the fire count value.

STEP 2: Mover walk structure at binary procs.

For binary proc b with stayMoveCountAt(b) = 0:
  fc(b) = cwMoveCountAt(b) + ccwMoveCountAt(b)

Under zero winding (edgeNetFlow = 0 at every edge):
  cwMoveCountAt(b) = ccwMoveCountAt(right(b))    -- edge (b, right b)
  cwMoveCountAt(left(b)) = ccwMoveCountAt(b)      -- edge (left b, b)

Define:
  ET(e) = edgeTraversalCount(e)

For edge e_L = (left(b), b):
  ET(e_L) = cwMoveCountAt(left(b)) + ccwMoveCountAt(b)
           = 2 * ccwMoveCountAt(b)                     (under ZW)

For edge e_R = (b, right(b)):
  ET(e_R) = cwMoveCountAt(b) + ccwMoveCountAt(right(b))
           = 2 * cwMoveCountAt(b)                       (under ZW)

So:
  ET(e_L) + ET(e_R) = 2 * (ccwMoveCountAt(b) + cwMoveCountAt(b)) = 2 * fc(b) >= 8.

Both ET(e_L) and ET(e_R) are even and non-negative.

STEP 3: Dead edge impossibility.

Lemma (walk_connectivity): The mover walk visits all n positions (from fc(p) >= 2
for all p). The walk is a closed path where consecutive movers are adjacent
(next_mover_is_local). Therefore, the set of edges with ET > 0 forms a connected
subgraph spanning all n vertices.

Corollary: At most 1 edge can have ET = 0. (Removing 1 edge from a connected
spanning subgraph of an n-cycle keeps it connected iff it has >= n-1 edges.
A spanning connected subgraph of a cycle has exactly n or n-1 edges, so
removing 1 keeps >= n-2 >= 7 edges which still span n vertices as a path.)

Actually: more precisely, the edges with ET > 0 form a connected graph on all
n vertices. If 2 edges have ET = 0: removing them from the n-cycle leaves
at most n-2 edges. An n-cycle minus 2 edges has at most 2 connected components
(possibly just 1 if the removed edges are adjacent). For the walk to visit all
procs: ALL components must be visited. But the walk is a single continuous
closed path — it can only visit vertices in ONE connected component.

Wait — the walk CAN visit vertices in multiple components if the components
share vertices. But removing 2 edges from an n-cycle (n >= 4) with the edges
non-adjacent gives 2 connected components with no shared vertices. If the edges
ARE adjacent (sharing a vertex): removing them gives 1 component (a path minus
an endpoint = still connected).

Let me be more precise:

CLAIM: If 2 non-adjacent edges have ET = 0, the walk cannot visit all procs.

Proof: Remove 2 non-adjacent edges from the n-cycle. This creates 2 paths
(arcs) as connected components. The walk, being a single continuous path on
edges with ET > 0, stays within one connected component. Procs in the other
component have fc = 0, contradicting fc >= 2. QED.

CLAIM: If 2 adjacent edges (sharing vertex v) have ET = 0, the walk still
cannot visit v.

Proof: Both edges incident to v have ET = 0. No edge connects v to the rest
of the walk. The walk visits v only if the mover is at v at some step, but
arriving at v requires traversing an incident edge. Since both incident edges
have ET = 0: no step has the mover arriving at v from a neighbor. The only way
v is the mover is if v was the mover at the PREVIOUS step (stay). But for
binary v: stay = 0 (Step 1). So v is never the mover. fc(v) = 0. Contradiction
with fc >= 2. QED.

Wait: this argument assumes v is binary. What if the two dead edges are at a
non-binary proc?

Actually: we're looking at dead edges caused by binary procs. For binary b:
ET(e_L) = 0 iff ccwMoveCountAt(b) = 0.
ET(e_R) = 0 iff cwMoveCountAt(b) = 0.

If both: ccwMoveCountAt(b) = 0 AND cwMoveCountAt(b) = 0. Then fc(b) = 0.
Contradicts fc >= 2. So at most one of b's edges is dead.

If ccwMoveCountAt(b) = 0 (left edge dead): the walk never approaches b from
the left or leaves b to the left. All of b's firings are CW: the walk comes
from the right and goes to the right. So cwMoveCountAt(b) = fc(b) >= 4.

Wait: if ccwMoveCountAt(b) = 0, then the walk at b is always CW (arrive from
left(b), depart to right(b)) plus possibly bounces. Actually no:

cwMoveCountAt(b) = departures from b to right(b).
ccwMoveCountAt(b) = departures from b to left(b).

If ccwMoveCountAt(b) = 0: b NEVER departs to the left. All departures are CW.
Arrivals: arrivals from left = cwMoveCountAt(left(b)) = ccwMoveCountAt(b) = 0 (ZW).
So NO arrivals from the left either. All arrivals are from the right.

So: all firings of b have the walk arriving from right(b) and departing to right(b)
(since departure is always CW = to right, and arrival is always from right).
These are all "bounce right" moves.

STEP 4: Counting dead edges across multiple binary procs.

For each binary b with fc >= 4:
  Case A: ccwMoveCountAt(b) >= 1 AND cwMoveCountAt(b) >= 1. No dead edges at b.
  Case B: ccwMoveCountAt(b) = 0 (left edge dead). cwMoveCountAt(b) = fc(b) >= 4.
  Case C: cwMoveCountAt(b) = 0 (right edge dead). ccwMoveCountAt(b) = fc(b) >= 4.

If at least 2 binary procs are in Case B or Case C: at least 2 dead edges.

SUB-CLAIM: If 2 binary procs b1, b2 each have a dead edge, those dead edges
are at distinct positions (since b1 != b2 and their dead edges are incident
to different vertices).

Are the 2 dead edges non-adjacent? Not necessarily (if b1 and b2 are adjacent,
their dead edges might share a vertex).

CASE ANALYSIS:

If b1 has dead left edge (left(b1), b1) and b2 has dead left edge (left(b2), b2):
  If b1 != b2 and left(b1) != left(b2): edges are at different positions. They're
  non-adjacent unless they share a vertex. The edges are (left(b1), b1) and
  (left(b2), b2). They share a vertex iff left(b1) = b2 or b1 = left(b2)
  (i.e., b1 and b2 are adjacent).

If b1 and b2 are NOT adjacent: the 2 dead edges are non-adjacent.
  => From the claim above: walk can't visit all procs. Contradiction.

If b1 and b2 ARE adjacent (say b2 = right(b1)):
  Dead edges: (left(b1), b1) and (left(b2), b2) = (left(b1), b1) and (b1, b2).
  Wait: left(b2) = left(right(b1)) = b1. So dead edges are (left(b1), b1) and (b1, b2).
  These share vertex b1.
  The walk: b1 never departs left (ccwMoveCountAt(b1) = 0) and the walk never
  traverses edge (b1, b2) from left to right (since b2's left edge is dead:
  arrivals at b2 from left = cwMoveCountAt(b1) = ... hmm let me recalculate.

  b2 has dead left edge: ccwMoveCountAt(b2) = 0.
  Under ZW: cwMoveCountAt(left(b2)) = ccwMoveCountAt(b2) = 0.
  left(b2) = b1. So cwMoveCountAt(b1) = 0.

  But b1 has dead left edge: ccwMoveCountAt(b1) = 0.
  With cwMoveCountAt(b1) = 0 AND ccwMoveCountAt(b1) = 0: fc(b1) = 0.
  Contradiction with fc >= 2!

  So if b1 and b2 are adjacent and both have dead LEFT edges: contradiction.

Similarly: if both have dead RIGHT edges and are adjacent: contradiction.
If b1 has dead LEFT and b2 has dead RIGHT and they're adjacent: need to check.

b1 has dead left: ccwMoveCountAt(b1) = 0. => cwMoveCountAt(left(b1)) = 0.
b2 has dead right: cwMoveCountAt(b2) = 0. => ccwMoveCountAt(right(b2)) = 0.

b2 = right(b1). So right(b2) = right(right(b1)). Dead right edge of b2 at
(b2, right(b2)). cwMoveCountAt(b2) = 0.

fc(b2) = cwMoveCountAt(b2) + ccwMoveCountAt(b2) = 0 + ccwMoveCountAt(b2).
fc(b2) >= 4 => ccwMoveCountAt(b2) >= 4.

Under ZW: cwMoveCountAt(left(b2)) = ccwMoveCountAt(b2) >= 4.
left(b2) = b1. So cwMoveCountAt(b1) >= 4.

fc(b1) = cwMoveCountAt(b1) + ccwMoveCountAt(b1) = cwMoveCountAt(b1) + 0 >= 4.
ET(right edge of b1) = 2 * cwMoveCountAt(b1) >= 8. This edge is (b1, b2).
ET(left edge of b2) = 2 * ccwMoveCountAt(b2) >= 8. This is also (b1, b2)!

Wait: the right edge of b1 IS the left edge of b2 (since b2 = right(b1)).
Both computations give the same edge, consistently: ET >= 8.

The dead edges are: left edge of b1 = (left(b1), b1) and right edge of b2 =
(b2, right(b2)). These are DIFFERENT edges (unless left(b1) = b2 and b1 = right(b2),
which would mean left(b1) = right(b1) => n = 2, contradiction with n >= 9).

So the 2 dead edges are (left(b1), b1) and (b2, right(b2)) = (right(b1), right(right(b1))).
These share no vertex (since n >= 9 and they're 2 edges apart on the ring).

Non-adjacent dead edges => walk disconnected => contradiction!

SO: for any 2 binary procs with dead edges, adjacent or not, we get a contradiction
(either through fc = 0 at a shared vertex or through disconnected walk).

STEP 5: At least 2 binary procs have dead edges.

We have B >= 3 binary procs, each with fc >= 4. We need to show at least 2 are in
Case B or Case C (have a dead edge).

Suppose at most 1 binary has a dead edge. Then >= B-1 >= 2 binary procs are in
Case A (both edges alive): cwMoveCountAt(b) >= 1 and ccwMoveCountAt(b) >= 1.

For Case A binary b: cwMoveCountAt(b) >= 1 and ccwMoveCountAt(b) >= 1.
So cwMoveCountAt(b) + ccwMoveCountAt(b) = fc(b) >= 4 with both >= 1.
This means: cwMoveCountAt(b) in {1, 2, ..., fc(b)-1} and similarly for ccw.

Now: cwStepCount = sum_p cwMoveCountAt(p).

For Case A binary procs (at least 2): each contributes >= 1 to cwStepCount.
For the one possible Case B/C binary: contributes fc(b) >= 4 to cw or ccw
(but 0 to the other). Say Case B (dead left): cwMoveCountAt = fc >= 4, ccw = 0.
Contribution to cwStepCount: fc >= 4.

For non-binary procs: each contributes cwMoveCountAt >= 0 to cwStepCount.

Total cwStepCount >= 1 + 1 + 4 + (contributions from non-binary) >= 6.
ccwStepCount = cwStepCount >= 6 (ZW).

CL = 2*cwStepCount + stayStepCount >= 12.

This doesn't give a contradiction. We need to go further.

ACTUALLY: I realize the argument in Step 5 is wrong. I cannot show >= 2 dead edges
just from fc >= 4. A binary proc with fc = 4 and cwMoveCountAt = 2, ccwMoveCountAt = 2
has no dead edges.

So the dead edge argument only works IF we can show that the TOTAL cwStepCount
is too small (forcing some binary to have all its firings in one direction).

Hmm. Let me reconsider.

===========================================================================
REVISED PROOF APPROACH
===========================================================================

After extensive analysis, the correct proof uses a DIFFERENT mechanism:

THEOREM (Binary FC >= 4 with ZW + adjacent binary => entry conflict at shared neighbor)

This leverages the fact that with >= 3 binary on a ring of n >= 9 with
sub-threshold product:
  - There exist at least 2 binary procs that are "close" (within distance 2)
    on the ring.
  - OR all binary are isolated (no two adjacent).

For the case where two binary procs b1, b2 are adjacent:
  The shared ternary neighbor t between them has tight context constraints.
  With fc(b1) >= 4 and fc(b2) >= 4: t's left and right contexts are both
  binary and both toggle multiple times. The pigeonhole on t's local context
  space (m_{left t} * m_t * m_{right t} = 2 * m_t * 2) with many mover/non-mover
  events forces entry conflict.

For the isolated binary case:
  Every binary b has both neighbors non-binary. The sub-threshold product
  constrains the non-binary state sizes. With fc(b) >= 4 and the trigger lemma
  (each b-firing is preceded and followed by a neighbor firing): the neighbor
  fire counts are at least fc(b)/2 (by pigeonhole distributing fc(b) triggers
  between 2 neighbors). This creates a "fire count propagation" that,
  combined with the sub-threshold product, forces CL > product, contradicting
  CL <= product.

Wait: CL > product isn't achievable since configs are distinct and bounded by product.

Actually: let me try the SIMPLEST possible argument.

===========================================================================
SIMPLEST PROOF: CL BOUND VIA EDGE TRAVERSAL UNDER ZW
===========================================================================

Under ZW: every edge has even ET. The walk visits all n procs.
All edges incident to the ring must collectively have ET summing to CL - stayStepCount.

For binary procs: stayStepCount contribution = 0.
For non-binary procs: stayStepCount contribution >= 0.

cwStepCount = ccwStepCount (ZW). CL = 2*cwStepCount + stayStepCount.

Now: cwStepCount = sum_p cwMoveCountAt(p).

For each proc p: cwMoveCountAt(p) is the number of CW departures.
Under ZW: cwMoveCountAt(p) = ccwMoveCountAt(right p).

The walk visits every proc's RIGHT edge at least cwMoveCountAt(p) times in each
direction. If cwMoveCountAt(p) = 0 for some p: the edge (p, right p) is never
crossed in CW direction. Under ZW: ccwMoveCountAt(right p) = 0 too. So the edge
is dead (ET = 0).

For the walk to be connected: at most 1 dead edge.

If the walk has 0 dead edges: all n edges have cwMoveCountAt >= 1.
cwStepCount = sum cwMoveCountAt >= n.
CL = 2*cwStepCount + stayStepCount >= 2n.

If the walk has 1 dead edge at (p0, right p0):
cwMoveCountAt(p0) = 0. All other n-1 procs have cwMoveCountAt >= 0,
but the walk must still be connected.

With 1 dead edge: n-1 edges alive. cwStepCount = sum cwMoveCountAt >= n-1
(from the alive edges each having cwMoveCountAt >= 1).
CL >= 2*(n-1) = 2n-2.

But: fc(p0) = cwMoveCountAt(p0) + ccwMoveCountAt(p0) + stayMoveCountAt(p0).
With cwMoveCountAt(p0) = 0: fc(p0) = ccwMoveCountAt(p0) + stay(p0).
Under ZW: cwMoveCountAt(left(p0)) = ccwMoveCountAt(p0).
So fc(p0) = cwMoveCountAt(left(p0)) + stay(p0).

If p0 is binary: stay = 0. fc(p0) = cwMoveCountAt(left(p0)).
Also: ccwMoveCountAt(right(p0)) = cwMoveCountAt(p0) = 0.
So the edge (left(p0), p0) has ET = 2*cwMoveCountAt(left(p0)) = 2*fc(p0) >= 8.
And right(p0) has ccwMoveCountAt(right(p0)) = 0.

For right(p0): fc(right(p0)) = cwMoveCountAt(right(p0)) + ccwMoveCountAt(right(p0))
+ stay(right(p0)).
ccwMoveCountAt(right(p0)) = 0. So fc(right(p0)) = cwMoveCountAt(right(p0)) + stay.

If right(p0) is also binary: stay = 0. fc(right(p0)) = cwMoveCountAt(right(p0)).
Under ZW: the edge (right(p0), right(right(p0))) has ET = 2*cwMoveCountAt(right(p0)).
If fc(right(p0)) >= 4: cwMoveCountAt(right(p0)) >= 4. OK, alive.

And the edge (p0, right(p0)) is the dead edge. ET = 0. ✓

So: one dead edge is possible. Two dead edges is NOT.

But I can't show >= 2 dead edges just from all binary fc >= 4.

===========================================================================
I believe the proof requires a result that is not purely local but uses the
sub-threshold product constraint. Let me state the CORRECT proof:

PROOF (using CL <= product):

From gc.distinct: CL = configs.length <= stateProduct(rs) < 4 * 3^(n-2).

From all binary fc >= 4:
  CL = sum fc >= 4B + 2(n-B) = 2n + 2B.

From some fc >= 3:
  At least one proc has fc >= 3. If this proc is non-binary: CL >= 2n + 2B + 1.

From sub-threshold: CL < 4 * 3^(n-2).

These are consistent for any n >= 9. No contradiction from CL bounds alone.

THEREFORE: the proof CANNOT be purely about CL bounds or edge traversal counts.

The proof MUST construct an entry conflict or use convergence.

Since I've exhausted the local analysis without finding a clean mechanism,
I believe the correct approach is:

FOR THE LEAN SORRY: route through the existing `zeroWinding_no_fireCount_ge3`
theorem by providing a one-sided binary provider DIRECTLY, without going through
the passthrough binary intermediate step. This bypasses the need for the
"exists binary with fc=2" step entirely.

Alternatively: the sorry can be filled by showing that the combination of
hypotheses is VACUOUSLY TRUE — i.e., the hypotheses are never simultaneously
satisfied. This would require showing that in any ZW cycle with cw > 0 and
sub-threshold product and >= 3 binary and n >= 9, it's impossible to have
both all fc >= 2 AND some fc >= 3. But that's what CL = 2n proves!

CIRCULAR DEPENDENCY RESOLUTION:
The actual proof structure should be:
1. Show CL >= 2n (from fc >= 2). DONE (in codebase).
2. Show CL <= 2n (from ZW structure). NEEDS NON-CIRCULAR PROOF.
3. From CL = 2n and all fc >= 2: all fc = 2.

The CL <= 2n proof currently routes through zeroWinding_no_fireCount_ge3 which
routes through our sorry. The NON-CIRCULAR fix is:

DIRECT PROOF OF CL <= 2n:

Under ZW: cwStepCount = ccwStepCount. CL = 2*cwStepCount + stayStepCount.

Every proc fires (fc >= 2). By next_mover_is_local: consecutive movers are
adjacent. The mover walk is a lattice walk on Z_n.

CLAIM: Under ZW with cwStepCount > 0 and all fc >= 2:
  cwStepCount = n and stayStepCount = 0. Hence CL = 2n.

Proof of cwStepCount <= n:
  Under ZW: cwMoveCountAt(p) = ccwMoveCountAt(right p) for all p.
  ET(p) = 2 * cwMoveCountAt(p) for edge (p, right p).
  Σ cwMoveCountAt(p) = cwStepCount.

  For the walk to be connected with all procs visited:
    At most 1 edge has ET = 0.
    n-1 or n edges have ET >= 2.
    If n edges: cwStepCount >= n.
    If n-1 edges: cwStepCount >= n-1.

  We need cwStepCount <= n. Suppose cwStepCount >= n+1.
  Then CL >= 2(n+1) = 2n+2. With all fc >= 2: sum fc >= 2n. CL >= 2n.
  If CL > 2n: some proc has fc >= 3. (This is where the previous proof goes.)

  Actually, cwStepCount can be > n. Consider: some proc has cwMoveCountAt = 2.
  Then cwStepCount >= n + 1 (if all others have cwMoveCountAt >= 1).

  The bound cwStepCount = n requires: ALL cwMoveCountAt(p) = 1 for all p.
  This is EXACTLY the uniform sweep structure.

  Hmm, I don't see how to prove cwStepCount <= n without the fc >= 3 contradiction.

FINAL CONCLUSION:
The sorry at line 108 of CaseObstructionsCore.lean requires a NON-TRIVIAL
structural argument. The most promising approach is:

1. Generalize stayMoveCountAt_eq_zero to all binary procs (not just fc=2).
2. Use the generalized stay=0 to show that the walk at each binary proc is a
   lattice walk with cwMoveCountAt + ccwMoveCountAt = fc >= 4.
3. Under ZW: P_CW = P_CCW at each proc (equal passthroughs in each direction).
4. Show that B >= 3 binary procs each with >= 4 lattice moves and P_CW >= 1
   forces cwStepCount >= n + B, hence CL >= 2n + 2B + stayStepCount.
5. Show CL <= product < 4*3^(n-2) is violated for specific multisets.

But step 5 fails because 2n + 2B << 4*3^(n-2) for n >= 9.

The proof likely needs to use entry conflict at a ternary proc, leveraging
the TernaryPhaseEC infrastructure already in the codebase. This would require
showing that all binary fc >= 4 creates a "sparse phase" at some ternary proc
(where the ternary proc fires with frozen binary neighbor), and the sparse
phase infrastructure (PhaseExtractionBase, phase_dispatch_ec) produces EC.
"""
print("Proof analysis complete. See comments above.")
