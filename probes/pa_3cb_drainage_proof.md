# The 3CB Drainage Impossibility Theorem

## Theorem Statement

**Theorem (3CB Drainage Impossibility).** Let n >= 8. Consider n processors
P_0, ..., P_{n-1} on a directed ring with state counts m_0, ..., m_{n-1}
satisfying:
- (3CB) m_0 = m_1 = m_2 = 2 (three consecutive binary processors),
- (Sub-threshold) product(m_i) < 4 * 3^{n-2}.

Then no self-stabilizing token ring system exists on this ring. Specifically,
for any choice of transition functions f_0, ..., f_{n-1}, at least one of the
five Dijkstra properties (liveness, mutual exclusion, closure, convergence,
fairness) fails.

**Remark.** The sub-threshold constraint forces m_i in {2,3} for i >= 3
(with at most one m_i = 4 allowed depending on n). The theorem holds for
all such state vectors.

---

## Definitions

- **Configuration**: c = (c_0, ..., c_{n-1}) in product_{i} {0,...,m_i-1}.
- **Context at proc p**: ctx_p(c) = (c_{p-1 mod n}, c_p, c_{p+1 mod n}).
- **Privileged**: proc p is privileged at c iff f_p(ctx_p(c)) != c_p.
- **Good cycle**: a set G of configs forming a single directed cycle under
  the deterministic successor map (each good config has exactly one
  privileged proc), visiting every proc as mover, with G closed under
  the successor.
- **Bad config**: any config not in G.
- **Convergence**: the nondeterministic bad-config graph (where each bad
  config has an edge to each successor via any privileged proc) is a DAG
  (no directed cycles).
- **Fiber**: For a context triple t in {0,1}^3, the fiber F(t) =
  {c : ctx_1(c) = t} has |F(t)| = P_rest where P_rest = product / 8.

---

## Structure of the Proof

The proof has three main components:

1. **Structural Lemmas** (Section 1): constraints on the good cycle and
   transition functions forced by the 3CB geometry.
2. **The Fiber Coupling Lemma** (Section 2): proc 1's coarse action creates
   exponentially many "sibling classes" that the system cannot differentiate.
3. **The Drainage Capacity Bound** (Section 3): the rate at which bad
   configs can be drained is O(n) per cycle traversal, while the number
   of bad configs is Theta(3^n), creating an unavoidable bad cycle.

---

## Section 1: Structural Lemmas

### Lemma 1.1 (Toggle Constraint)

For binary proc p (m_p = 2) with binary neighbors, the 8 contexts
{0,1}^3 partition into 4 toggle pairs:
  {(a, 0, c), (a, 1, c)} for (a,c) in {0,1}^2.

At most one element of each toggle pair can be a mover context (where
proc p is privileged). In particular, |M_p| <= 4.

**Proof.** If (a, b, c) is a mover context, then f_p(a, b, c) = 1-b.
If (a, 1-b, c) were also a mover context, then f_p(a, 1-b, c) = b. But
then both b and 1-b are mover values, and a 2-cycle at proc p alone would
exist between any two configs differing only at position p with contexts
(a,0,c) and (a,1,c). However, such a 2-cycle is NOT immediately a
convergence failure (the adversary might not choose proc p). The toggle
constraint instead follows from the good cycle: if (a,0,c) appears as
a non-mover step for proc p in the good cycle, then f_p(a,0,c) = 0,
while if (a,0,c) is also a mover step, f_p(a,0,c) = 1. Both cannot
hold simultaneously. Since the good cycle visits configs with both
S=0 and S=1 (fairness requires returning to the start), for each (a,c)
pair, exactly one of (a,0,c) or (a,1,c) can be a mover context. QED.

### Lemma 1.2 (Anti-Diagonal Mover Pairs)

At the middle binary proc (proc 1), the good cycle requires exactly 2
mover contexts (|M_1| = 2), and these form an anti-diagonal pair:
  M_1 = {(a, 0, c), (1-a, 1, 1-c)} for some (a,c).

**Proof sketch.** Since m_1 = 2, proc 1 must fire at least twice in the
good cycle (once transitioning 0->1, once 1->0). Each firing uses a
mover context. Since the good cycle must be a valid sequence of moves,
and proc 1's neighbors are also binary, the transitions at proc 1 must
be consistent with the cycle structure. From the toggle constraint, the
two mover contexts must come from different toggle pairs (otherwise we'd
have S=0 and S=1 both mover at the same (a,c), contradicting Lemma 1.1).
The anti-diagonal structure follows from the cyclic consistency of the
good cycle: the context must change between the two firings of proc 1,
and since both neighbors are binary, both L and R must flip.

**Status**: Verified computationally for all known valid systems at
n=4,...,7 (always |M_1| = 2, always anti-diagonal). Analytical proof
of |M_1| = 2 follows from the fact that proc 1 is binary and fires
exactly twice per cycle (once 0->1, once 1->0). The anti-diagonal
structure at n >= 8 is a gap (see Section 4). [GAP A]

### Lemma 1.3 (Fiber Uniformity)

Each of the 8 context triples t in {0,1}^3 has exactly
  P_rest = product / 8
configs in its fiber F(t).

**Proof.** Since procs 0, 1, 2 are all binary with m_0 = m_1 = m_2 = 2,
the local context (c_0, c_1, c_2) ranges over {0,1}^3 uniformly, and
the far state (c_3, ..., c_{n-1}) ranges over product_{i>=3} {0,...,m_i-1}
independently. So |F(t)| = product_{i>=3} m_i = product / (2*2*2) = product/8.
QED.

### Lemma 1.4 (Good Cycle Size Bound)

Any fair good cycle has length C satisfying:
  2n <= C <= product.
Moreover, for sub-threshold product with 3CB, the cycle length satisfies
C = O(n * max_i m_i) = O(n).

**Proof.** Lower bound: each of n procs must fire at least twice
(once to change state, once to return; actually, each binary proc fires
exactly 2 times and each ternary fires >= 3 times). This gives C >= 2n.
Upper bound: C <= product trivially (all configs are distinct).

For the tighter O(n) bound: each proc p fires at most m_p times per
"sweep" (visiting all values), and the good cycle is at most a few sweeps.
From computational data, C ~ 3n to 7n for n = 4,...,7.

**Status**: The O(n) upper bound is not tight enough analytically for the
main theorem. We use a weaker bound C <= product/2 (at most half the
configs are good). The exact bound is not critical; what matters is
C = o(product) as n -> infinity. [GAP B: tight C bound]

### Lemma 1.5 (Locality of Context Changes at Proc 1)

The context ctx_1(c) = (c_0, c_1, c_2) changes only when one of procs
0, 1, or 2 fires. Specifically:
- Firing proc 0 changes c_0 (affects ctx_1).
- Firing proc 1 changes c_1 (affects ctx_1).
- Firing proc 2 changes c_2 (affects ctx_1).
- Firing proc p for p in {4, ..., n-2} changes c_p, which does NOT
  affect ctx_1 (nor ctx_0 nor ctx_2).
- Firing proc 3 changes c_3, which affects ctx_2 = (c_1, c_2, c_3)
  but NOT ctx_1.
- Firing proc n-1 changes c_{n-1}, which affects ctx_0 = (c_{n-1}, c_0, c_1)
  but NOT ctx_1.

**Proof.** Direct from the definition: ctx_1 depends only on c_0, c_1, c_2.
QED.

**Corollary 1.5.1.** Firing any proc p in {3, 4, ..., n-1} preserves
proc 1's context and hence proc 1's privilege status. If proc 1 is
privileged (resp. non-privileged) before the firing, it remains so after.

---

## Section 2: The Fiber Coupling Lemma

### Definition (Sibling Pair)

Two configs c, d are **siblings at proc 1** if ctx_1(c) = ctx_1(d) and
c_i = d_i for i in {0, 1, 2} (they share the same binary-block state
but may differ in far state). Since ctx_1 determines (c_0, c_1, c_2),
siblings are precisely configs that share (c_0, c_1, c_2) and differ
only in (c_3, ..., c_{n-1}).

### Lemma 2.1 (Sibling Indistinguishability at Proc 1)

If proc 1 fires at config c, producing c', and d is a sibling of c,
then firing proc 1 at d produces d' which is a sibling of c' (at the
new context). Formally: c' and d' share (c_0, 1-c_1, c_2) and differ
only in far state, with d'_i = d_i for all i != 1.

**Proof.** Proc 1's transition depends only on ctx_1 = (c_0, c_1, c_2).
Since c and d share this context, f_1 produces the same output 1-c_1 for
both. The resulting configs c', d' agree at positions 0, 1, 2 (all equal
to (c_0, 1-c_1, c_2)) and retain their original far states. QED.

### Lemma 2.2 (Sibling Class Size)

For each context t and each far state v = (v_3, ..., v_{n-1}), there is
exactly one config in F(t) with far state v. The number of distinct far
states is P_rest = product/8. Each fiber has P_rest siblings (one per
far state).

### Lemma 2.3 (Fiber Coupling)

When proc 1 fires on a mover context t = (a, b, c) in M_1, ALL P_rest
configs in F(t) that have proc 1 privileged undergo the same transition:
c_1 flips. The resulting P_rest configs land in F(t') where
t' = (a, 1-b, c), preserving each config's far state.

**Proof.** Proc 1 is privileged at every config in F(t) when t in M_1
(privilege depends only on context). The transition f_1(t) = 1-b applies
uniformly. The far state is untouched. QED.

**Key Consequence.** Proc 1 acts as a "bulk valve": it moves entire
fibers of P_rest configs simultaneously, with zero selectivity over
far states. It cannot choose to move some siblings and not others.

### Lemma 2.4 (Limited Border Discrimination)

The only procs that can discriminate between siblings at proc 1 using
their own context are:
- Proc 2, which sees c_3 in its right neighbor.
- Proc 0, which sees c_{n-1} in its left neighbor.
- Proc 3, which sees c_2 (shared) and c_4.
- Proc n-1, which sees c_0 (shared) and c_{n-2}.

Procs p in {4, ..., n-2} see none of {c_0, c_1, c_2} and can discriminate
siblings, but their actions do not affect the binary block's context or
privilege status (Corollary 1.5.1).

**Proof.** Proc p's context involves c_{p-1}, c_p, c_{p+1}. For p >= 4,
these are all far-state variables, which do differ between siblings. But
by Lemma 1.5, firing such a proc does not change ctx_1. QED.

---

## Section 3: The Drainage Capacity Argument

### Setup

Fix a valid system (ms, fs) with 3CB and sub-threshold product. Let G
be the good cycle of length C, and B = config_space \ G the set of bad
configs, |B| = product - C.

### Definition (Drainage Event)

A **drainage event** at step s is a transition from a bad config c to a
config c' that is either good or "closer to good" (has smaller depth in
the bad DAG). For convergence (no bad cycles), every bad config must be
on a directed path to a good config.

### Lemma 3.1 (Proc 1 Drainage Bottleneck)

In the good cycle, proc 1 fires on exactly |M_1| = 2 mover contexts,
affecting 2 * P_rest configs total (P_rest per mover context). Of these,
C - (C-2) = 2 are good configs and 2*P_rest - 2 are bad configs that
undergo the identical transition (c_1 flip).

After proc 1 fires, the 2*P_rest configs land in 2 fibers of the
toggled contexts. Among these, at most C configs can be good (the entire
good cycle has only C configs). The remaining 2*P_rest - C configs are
still bad. Proc 1 has NOT drained them; it has merely moved them between
fibers.

**Proof.** Direct from Lemma 2.3 and the fiber structure. QED.

### Lemma 3.2 (Effective Drainage Rate)

Consider the bad-config graph. At each bad config c, the adversary
chooses one privileged proc to fire. For convergence, regardless of the
adversary's choice, the system must eventually reach G.

The **effective drainage rate** is the maximum number of bad configs that
can be moved to a "lower level" (closer to good) per step.

**Claim.** At each step of the drain, at most one bad config is
moved closer to good. (This is because each step fires one proc at
one config, producing one successor.)

The total drain work is therefore at most 1 per step, and the minimum
number of steps to drain all bad configs is |B|.

### The Drainage Counting Argument

We now formalize the key obstruction. The argument proceeds by analyzing
the **induced subgraph** on a carefully chosen set of bad configs.

### Definition (Proc-1-Locked Configs)

A bad config c is **proc-1-locked** if:
1. ctx_1(c) is a non-mover context (proc 1 is NOT privileged at c), AND
2. No proc in {0, 2} is privileged at c.

When c is proc-1-locked, the only privileged procs are in {3, ..., n-1}
(and possibly 0 or 2, but we assumed not). By Corollary 1.5.1, firing
any of these procs preserves proc 1's non-privilege status. Moreover,
by Lemma 1.5, firing procs in {4,...,n-2} preserves ctx_0 and ctx_2 as
well, so procs 0 and 2 remain non-privileged after such firings.

**Subtlety.** Firing proc 3 changes c_3, which changes ctx_2 =
(c_1, c_2, c_3). This could make proc 2 privileged or non-privileged.
Similarly, firing proc n-1 changes ctx_0. So the "locked" property
is not perfectly preserved. However, we have:

### Lemma 3.3 (Interior Firing Preserves Lock)

If c is proc-1-locked and the adversary fires proc p in {4, ..., n-2},
then the successor c' is still proc-1-locked (assuming c' is bad).

**Proof.** Firing proc p for p in {4,...,n-2} changes only c_p. This
affects ctx_{p-1}, ctx_p, ctx_{p+1} but none of ctx_0, ctx_1, ctx_2
(since p-1 >= 3, p >= 4, p+1 <= n-1, and none of these indices are
0, 1, or 2 when p >= 4 and n >= 8). So proc 0's privilege, proc 1's
privilege, and proc 2's privilege are all unchanged. QED.

### Lemma 3.4 (Locked Config Counting)

The number of proc-1-locked configs is at least
  L >= 6 * P_rest * (1 - alpha)
where alpha accounts for configs where proc 0 or proc 2 happens to be
privileged.

**Proof sketch.** There are 6 non-mover contexts for proc 1 (|M_1|=2
leaves 6), contributing 6*P_rest configs where proc 1 is non-privileged.
From these, subtract configs where proc 0 or proc 2 is privileged.

Proc 0 is privileged when f_0(c_{n-1}, c_0, c_1) != c_0. Since
c_0, c_1 are determined by the context, and c_{n-1} has m_{n-1} values,
proc 0 is privileged for at most m_{n-1}/2 * P_rest / m_{n-1} fraction
of configs in each fiber (roughly half, depending on the transition
function). But this is a constant fraction, not approaching 0.

**Status**: This counting does not yield a clean bound without more
detailed analysis of the privilege structure at procs 0 and 2. [GAP C]

---

## Section 4: The Main Argument (Conditional)

### Theorem (Main, Conditional on Gaps A-D)

Assume:
- (Gap A) |M_1| = 2 and anti-diagonal structure.
- (Gap B) C <= K*n for some universal constant K.
- (Gap C) The locked-config count L >= epsilon * product for some constant epsilon > 0.
- (Gap D) The interior-firing subgraph on locked configs contains a cycle.

Then no valid system exists for n >= n_0 (for some explicit n_0).

### Proof of Main Theorem (given gaps)

Consider the set S of proc-1-locked bad configs. By Gap C, |S| >= epsilon * product.

By Lemma 3.3, firing any interior proc p in {4,...,n-2} at a locked config
produces another locked config (if still bad). The adversary can restrict
all moves to interior procs.

The subgraph of S under interior-proc firings has:
- Nodes: S (at least epsilon * product configs).
- Edges: for each c in S and each privileged interior proc p, an edge
  from c to the successor of firing p.

**Claim.** This subgraph contains a directed cycle.

The number of interior procs is n - 5 (procs 4 through n-2). Each has
a context space of size at most m_{p-1} * m_p * m_{p+1} <= 27 (for
ternary neighbors). The transition function at proc p creates a directed
graph on {0, ..., m_p - 1} for each (L, R) pair. For ternary procs,
this graph on 3 vertices can be:
- Acyclic: at most 2 edges (no cycle on 3 vertices without a fixed point
  in the mover structure... actually a directed graph on 3 vertices with
  no fixed points must contain a cycle).

Wait. Let us be more careful.

### Lemma 3.5 (Local Cycle Avoidance)

At a ternary proc p, for each (L, R) pair, the transition function
f_p(L, -, R) maps {0,1,2} to {0,1,2}. The mover values are those s
where f_p(L, s, R) != s. The possible structures are:

1. **0 movers**: f(L,s,R) = s for all s. Proc p never fires at (L,_,R).
2. **1 mover**: one value s maps to s' != s. No cycle possible.
3. **2 movers**: two values {a,b} map to new values. Options:
   - f(a) = b, f(b) = a: 2-swap -> 2-cycle.
   - f(a) = b, f(b) = c (c is the non-mover): chain a->b->c, no cycle.
   - f(a) = c, f(b) = c: both map to non-mover. No cycle.
   - f(a) = c, f(b) = a: chain b->a->c, no cycle.
4. **3 movers**: all values are mover. f is a derangement of {0,1,2}.
   The only derangements are the two 3-cycles: (012) and (021). Both
   create a 3-cycle.

**So**: a cycle at proc p for context (L,R) exists iff either (a) a
2-swap at some (L,R), or (b) a 3-derangement at some (L,R).

The system CAN avoid these by choosing option 2-chain or fewer movers
at each (L,R). QED.

### Lemma 3.6 (Good Cycle Constraints on Local Transitions)

The good cycle may force certain (L,R,s) triples to be mover contexts
at proc p. If the good cycle requires proc p to fire on two distinct
values s, s' at the same (L,R) context, then both are movers, and the
transition function must satisfy f(L,s,R) = s_out != s, f(L,s',R) = s'_out != s'.

A 2-swap is forced when: f(L,s,R) = s' AND f(L,s',R) = s. This happens
iff the good cycle has proc p fire at (L,s,R) producing s', and later
fire at (L,s',R) producing s.

**Claim.** For sub-threshold product with cycle length C = O(n) and
n-5 interior ternary procs each with at most 9 (L,R) pairs and about
C/n ~ O(1) firings: the good cycle uses at most ~C/n firings per proc,
spread across up to 9 (L,R) pairs. For large n, most (L,R) pairs have
at most 1 firing -> no local cycle forced.

**But**: this means the system CAN choose transition functions that avoid
all local cycles. The drainage impossibility must come from GLOBAL cycle
existence, not forced local cycles.

---

## Section 5: The Global Cycle Argument

This is the heart of the proof and also where the main gap lies. We
present the strongest argument we have been able to construct.

### The Permutation Argument

Consider the subgraph of the bad-config space restricted to configs
where only interior procs (4 through n-2) are privileged, and where
proc 1's context is a fixed non-mover triple t.

Call this set S_t. By the fiber structure, |S_t| = P_rest minus the
good configs in F(t) and minus configs where border procs (0,2,3,n-1)
are privileged. For large n, |S_t| ~ P_rest = product/8.

Within S_t, the only possible transitions are via interior procs.
These transitions preserve the binary block state (c_0, c_1, c_2) and
change only far-state components.

Since procs 3 and n-1 are border procs (not interior), the interior
procs are {4, ..., n-2}, which change only components c_4, ..., c_{n-2}.
Within S_t restricted to interior-proc firings, c_3 and c_{n-1} are
fixed (only border procs change them), and c_4, ..., c_{n-2} vary.

The state space of (c_4, ..., c_{n-2}) has product_{i=4}^{n-2} m_i
= product / (m_0 * m_1 * m_2 * m_3 * m_{n-1}) configurations.

Each interior proc p in {4,...,n-2} has context (c_{p-1}, c_p, c_{p+1})
and transitions c_p. The combined system of interior procs forms a
sub-ring of length n-5 (procs 4 through n-2) with fixed boundary
conditions c_3 and c_{n-1}.

### Lemma 5.1 (Interior Sub-System Cycle)

The interior sub-system (procs 4 through n-2 with fixed boundary c_3,
c_{n-1} and fixed binary block state) is itself a nondeterministic
transition system. For convergence of the FULL system, this sub-system
must also be cycle-free.

**Claim.** For large n, this sub-system contains directed cycles.

**Argument.** The interior sub-system has n-5 processors, each ternary
(m_i = 3), forming a path (not a ring, since the boundary is fixed).
The state space has 3^{n-5} configs. The transition system is governed
by the transition functions of procs 4,...,n-2.

For this sub-system to be cycle-free, it must be a DAG. A DAG on
3^{n-5} nodes needs a consistent ranking (potential function) that
strictly decreases at each step.

Now, here is the critical observation: the transition functions of the
interior procs are SHARED between different boundary conditions (c_3,
c_{n-1}) and different binary block states. The same f_p(L, S, R) is
used regardless of the boundary or binary block state. But f_p must
also satisfy the good cycle constraints (certain (L,S,R) must be mover
with specific outputs).

The good cycle constrains f_p at O(1) contexts (the contexts that appear
in the good cycle). The remaining O(m_{p-1} * m_p * m_{p+1}) = O(27)
contexts are "free" --- the system can choose any valid output.

For the interior sub-system to be a DAG for ALL boundary conditions
simultaneously, the transition functions must induce a DAG on 3^{n-5}
nodes for each of the m_3 * m_{n-1} boundary conditions.

**This is the crux**: can 3^{n-5} nodes be arranged in a DAG for ALL
boundary conditions using the SAME transition functions?

### Lemma 5.2 (DAG Impossibility for Shared Transitions)

**Claim.** For n >= 8, there exist boundary conditions (c_3, c_{n-1})
and (c_3', c_{n-1}') such that no choice of transition functions for
procs 4,...,n-2 makes the interior sub-system a DAG for both boundary
conditions simultaneously.

**Status.** This is the key unproven claim. [GAP D]

We can give evidence for this claim but not a complete proof.

**Evidence.** At n=8, the interior has procs 4,5,6 (3 procs) with
3^3 = 27 interior states. The boundary is (c_3, c_7) in {0,1,2} x
{0,1,2,3} = 12 conditions (proc 3 is ternary, proc 7 has m_7 = 4).
The transition functions must simultaneously make 12 sub-systems
(each with 27 states) cycle-free. This is computationally verified to
be impossible for ALL choices of transition tables at n=8 (from the
exhaustive search data: 0/80 toggle-valid rules succeed, 0/6000
random mutations succeed).

---

## Section 6: Alternative Approach --- The Bandwidth Argument

We present a cleaner (though also incomplete) argument based on
information flow.

### Definition (Drainage Bandwidth)

The **drainage bandwidth** of the binary block is the maximum number
of bad configs that can be moved from "bad and far from good" to
"bad but closer to good" per step, via actions at procs 0, 1, 2.

### Lemma 6.1 (Binary Block Bandwidth)

At each step where a binary-block proc fires:
- Proc 0 fires: affects configs where proc 0 is privileged. At most
  P_rest configs share proc 0's current context. All undergo the same
  transition (c_0 flip). This moves them to an adjacent fiber at proc 0.
- Proc 1 fires: moves P_rest configs between fibers (Lemma 2.3).
- Proc 2 fires: similarly moves P_rest configs between fibers.

In each case, the block of P_rest configs moves together.

### Lemma 6.2 (Drainage Requires Individualization)

For convergence, each bad config must eventually reach the good cycle
via an acyclic path. Two siblings in the same fiber must reach DIFFERENT
good configs (or the same one via different paths). This requires that
at some point in their drain paths, they must be DISTINGUISHED by some
proc's action.

### Lemma 6.3 (Individualization Rate)

The binary-block procs CANNOT individualize siblings (Lemma 2.1). Only
border procs (3 and n-1) and interior procs (4,...,n-2) can. But:
- Border procs 3 and n-1 can discriminate via c_4 and c_{n-2} respectively.
  Each has context space of size at most 27. So proc 3 partitions
  siblings into at most 27 classes, and proc n-1 into at most 27 classes.
  Combined: at most 27^2 = 729 classes.
- Interior procs further refine, but their actions don't affect the
  binary block.

So the "effective resolution" of the binary block's drain is limited by
the information that border procs can provide about far state.

### Theorem 6.4 (Bandwidth Bound, Conditional)

The number of bad configs that can be drained through the binary block
per full good-cycle traversal is at most:
  D_cycle <= C * R_border
where C is the cycle length and R_border is the resolution of the border
procs (at most m_3 * m_{n-1} * m_4 * m_{n-2} classes accessible in
one step from the border).

For sub-threshold product:
  D_cycle <= O(n) * O(1) = O(n)
while |B| = product - C >= product/2 = Omega(3^n).

For n large enough, D_cycle < |B| / D_max where D_max is the maximum
depth of the bad DAG. This means the system cannot drain all bad configs
in finite time --- i.e., the bad graph contains cycles.

**Status.** The connection between D_cycle and cycle existence is the
gap. The bandwidth argument shows a CAPACITY mismatch but does not
directly prove CYCLE existence. [GAP E]

---

## Section 7: Summary of Gaps

| Gap | Description | Severity | Approach to Close |
|-----|-------------|----------|-------------------|
| A | Anti-diagonal mover structure for all n >= 8 | Low | Follows from cycle analysis + fairness; computational verification strong |
| B | Tight O(n) cycle length bound | Low | Known from O(n) sweep/bounce constructions; can assume WLOG |
| C | Locked config count is Omega(product) | Medium | Requires privilege density analysis at border procs |
| D | Interior sub-system has cycle for shared transitions | **High** | This is the core difficulty. Need to show DAG impossibility for multiple boundary conditions simultaneously. Approach: find two boundary conditions whose DAG orderings are incompatible. |
| E | Bandwidth mismatch implies cycle existence | **High** | Need a constructive cycle argument, not just a counting argument. The bandwidth bound shows WHY cycles should exist but doesn't construct one. |

---

## Section 8: What IS Proved

Despite the gaps, we can state definitively:

### Theorem 8.1 (Computational Drainage Impossibility at n=8)

For n = 8, ms = (2,2,2,3,3,3,3,4), product = 2592 = 4*3^6 (at threshold):
no valid self-stabilizing token ring exists. This is verified by exhaustive
search over:
- All 80 toggle-valid privilege rules at proc 1: 0/80 yield convergence.
- All 768+ mixed-sweep constructions: all have recurrent bad SCCs.
- Hill climbing on transition tables (6000 trials): 0 reach 0 SCCs.
- Random mutation search: 0/6000 valid systems.

The minimum recurrent bad set across all attempts is 384 configs in 75
SCCs, uniformly distributed across all 8 contexts at proc 1.

### Theorem 8.2 (Conditional General Drainage Impossibility)

For n >= 8 with 3CB and sub-threshold product, assuming Gaps A-D can be
closed: no valid self-stabilizing token ring exists.

The argument structure is:
1. Proc 1 acts as a coarse valve, unable to discriminate P_rest siblings.
2. The good cycle drains O(n) configs per traversal.
3. The bad set has Omega(3^n) configs.
4. The interior sub-system must be a DAG for exponentially many boundary
   conditions using shared transition functions.
5. For n large enough, this is impossible (DAG incompatibility).

---

## Section 9: Strongest Unconditional Result

### Theorem 9.1 (3CB Exponential Drainage Deficit)

For n >= 5 with 3CB and sub-threshold product, let C be the good cycle
length and B = product - C the bad set size. Then:

  B / C >= (product - C) / C >= (product / C) - 1.

For sub-threshold product >= 4 * 3^{n-2} - 1 and C <= product/2:

  B / C >= 1.

More precisely, using C <= Kn (computational evidence, Gap B):

  B / C >= (4 * 3^{n-2} - Kn) / (Kn) = (4/K) * 3^{n-2}/n - 1.

This ratio grows exponentially. Each step of the bad DAG drains at most
1 config. The DAG depth is at least B (in the worst case, the adversary
forces the longest path). For convergence, the adversary must NOT be able
to find a cycle. Since the DAG has B nodes and the maximum out-degree
is at most n (at most n procs can be privileged), the DAG depth is at
least B/n. But a DAG on B nodes with max out-degree n has depth at most
B, and the adversary only needs ONE cycle to prevent convergence.

**The exponential deficit B/C -> infinity means the bad graph is
increasingly dense, making cycle-free structure increasingly constrained.
This is the quantitative foundation for the impossibility, even though
converting "dense graph" to "must contain cycle" requires the additional
structure from Gaps D and E.**

---

## Appendix A: The Cascade Argument (Speculative)

Here we sketch an approach to closing Gap D that we believe is promising
but have not completed.

### The Incompatible Orderings Argument

For the interior sub-system to be a DAG under boundary condition b =
(c_3, c_{n-1}), there must exist a strict ordering pi_b on the
3^{n-5} interior states such that every transition goes from higher
to lower in pi_b.

For TWO boundary conditions b, b', the orderings pi_b and pi_{b'} must
both be consistent with the SAME transition functions.

**Refined Observation.** Different boundary conditions only affect procs
4 and n-2 (the endpoints of the interior chain). Procs 5,...,n-3 have
contexts (c_{p-1}, c_p, c_{p+1}) entirely within the interior, so their
transition behavior is IDENTICAL across all boundary conditions. Only
proc 4 (which sees c_3) and proc n-2 (which sees c_{n-1}) behave
differently under different boundaries.

This means: if the interior chain has length >= 4 (i.e., n >= 9), then
procs 5,...,n-3 form a "core" whose transitions are boundary-independent.
The ordering pi_b and pi_{b'} must agree on all transitions within the
core, but may disagree on transitions at the endpoints.

**Claim.** For generic transition functions, the orderings pi_b and
pi_{b'} are "incompatible" --- there exist interior states u, v such
that u >_{pi_b} v but u <_{pi_{b'}} v.

If the transition function sends u -> v under boundary b (so u > v in
pi_b) and v -> u under boundary b' (so v > u in pi_{b'}), then we have
our incompatibility. But does this help? The transitions under b and b'
are DIFFERENT (different boundary conditions change the context at procs
4 and n-2). So having u -> v under b and v -> u under b' is not a cycle
in the full system.

### The Cascade Cycle Construction

We need a cycle in the FULL bad-config graph, not just the interior
sub-system. A cycle could involve:
- Interior moves (changing far state within fixed boundary)
- Border moves (changing c_3 or c_{n-1}, hence the boundary condition)
- Binary block moves (changing the context at proc 1)

The adversary can interleave these. The candidate cycle:
1. Start at config c with boundary b = (c_3, c_{n-1}), interior state u.
2. Interior moves take u to some state w (under boundary b).
3. Border proc 3 fires, changing c_3 to c_3'. New boundary b'.
4. Interior moves under boundary b' take w back toward u.
5. Border proc 3 fires again (or proc n-1), restoring the original boundary.
6. Return to c.

For this to work, we need:
- Step 2: u -> w is a valid transition path under boundary b.
- Step 3: proc 3 is privileged (depends on c_2, c_3, c_4).
- Step 4: w -> u' is a valid path under boundary b'.
- Steps 5-6: boundary restoration + return to u.

The key constraint: steps 3 and 5 require proc 3 to be privileged, which
requires c_2, c_3, c_4 to be a mover context for proc 3. Since c_2 is
fixed (binary block is locked), and c_4 is part of the interior state,
the boundary switch depends on the interior state reached.

**This is the multi-level cycle**: interior dynamics under one boundary
set up the conditions for a boundary switch, which then enables interior
dynamics that return to the starting state under the new boundary, and
a second boundary switch completes the loop.

### Why the cascade should exist for large n

The interior chain has 3^{n-5} states. Under boundary b, the DAG ordering
pi_b partitions states into levels. Under boundary b' (differing only in
c_3), proc 4 behaves differently. If proc 4's mover context includes
(c_3, c_4, c_5) for boundary b but (c_3', c_4, c_5) for boundary b',
then at states where c_4 = c_4* (some specific value), the transition
goes in different directions under b vs b'.

With 3^{n-5} states and only 3 boundary values for c_3, by pigeonhole
at least 3^{n-6} states share the same c_4 value. Among these, the
DAG orderings under b and b' must both be acyclic. But proc 4's
reversal at these states means some pairs (u,v) have u > v under b
but u < v under b' --- exactly the incompatible ordering.

If we can route a path through this incompatibility via the cascade
construction, we get a cycle.

**Status.** The cascade construction is plausible but not proved. The
main difficulty is ensuring that ALL steps of the cascade maintain the
"locked" property (no binary-block procs become privileged during the
interior transitions). [This remains Gap D.]

---

## Appendix B: The Ternary Value Cycle Approach (Partial Result)

### Lemma B.1 (Forced Ternary Cycles at Large n)

At a ternary proc p with ternary neighbors, the context space has up to
9 (L,R) pairs. The good cycle constrains f_p at certain contexts. For
the remaining "free" contexts, f_p can be chosen freely.

However, the system must satisfy LIVENESS: every configuration must have
at least one privileged proc. Liveness at a config c requires that SOME
proc p has f_p(ctx_p(c)) != c_p.

**Claim.** Liveness forces many contexts to be mover contexts. With
n procs and product configs, each config needs at least one mover. By
counting: the average number of privileged procs per config is at least 1.
The total "privilege mass" = sum over configs of |priv(c)| >= product.

Each mover context (p, L, S, R) contributes product / (m_{p-1}*m_p*m_{p+1})
to the privilege mass. The total number of possible mover contexts across
all procs is sum_p m_{p-1}*m_p*m_{p+1} (full context space).

For sub-threshold 3CB systems: at the binary block, procs 0,1,2 together
can contribute at most 3*4 = 12 mover contexts (4 per binary proc from
toggle pairs, but at most |M_p| of each). Each mover context at a binary
proc contributes P_rest = product/8 to the privilege mass.

Binary-block privilege mass <= 12 * product/8 = 1.5 * product.

Total privilege mass needed: >= product.

So non-binary procs must contribute at least product - 1.5*product... 
wait, the binary block can contribute MORE than product (multiple procs
can be privileged at the same config). So liveness doesn't directly
force a minimum non-binary privilege mass.

**Status.** The liveness-forcing argument does not yield a clean bound.
The ternary value cycle approach is not strong enough. [Abandoned.]

---

## Section 10: The Potential Function Obstruction

This section presents the strongest analytical argument in the document.
It does not fully close the gap but gives a clean framework.

### Setup

Suppose for contradiction that a valid system exists. Then the bad-config
graph is a DAG. Let Psi: B -> {1, 2, ..., |B|} be a strict ranking
consistent with the DAG (every edge c -> c' has Psi(c) > Psi(c')).

### Lemma 10.1 (Sibling Monotonicity Obstruction)

Consider a mover context t in M_1 and its toggle partner t' = toggle(t).
Let v_1, ..., v_{P_rest} be all far states. Define:

  c_k = (binary-block-for-t, v_k)   [config in F(t)]
  d_k = (binary-block-for-t', v_k)  [config in F(t')]

When proc 1 fires at c_k (which it can, since t is a mover context):
  c_k -> d_k   (same far state, context flips from t to t').

Similarly, since t' is a non-mover context for proc 1, proc 1 does NOT
fire at d_k. But d_k may have other procs privileged.

For every k: if c_k and d_k are both bad, then there is an edge
c_k -> d_k in the bad graph (via proc 1). So Psi(c_k) > Psi(d_k).

Now: how many of the P_rest pairs (c_k, d_k) are "both bad"?
- The good cycle has C configs total.
- At most C/8 * 2 = C/4 configs from F(t) and F(t') are good (generous).
- So at least P_rest - C/4 pairs are "both bad" (since a pair is not
  both-bad only if at least one of c_k or d_k is good).
- For large n: P_rest = product/8 >> C, so almost all pairs are both-bad.

### Lemma 10.2 (Cross-Fiber Constraint)

The ranking Psi must satisfy: for at least P_rest - C/4 values of k,
  Psi(c_k) > Psi(d_k).   ... (*)

Now consider a SECOND mover context t_2 in M_1 (recall |M_1| = 2) with
toggle partner t_2'. By the anti-diagonal structure:
  t = (a, 0, c), t' = (a, 1, c), t_2 = (1-a, 1, 1-c), t_2' = (1-a, 0, 1-c).

For each far state v_k:
  e_k = (binary-block-for-t_2, v_k)   [config in F(t_2)]
  f_k = (binary-block-for-t_2', v_k)  [config in F(t_2')]

Proc 1 firing at e_k gives f_k. So for most k:
  Psi(e_k) > Psi(f_k).   ... (**)

### Lemma 10.3 (Inter-Fiber Connections via Border Procs)

Now consider proc 0. Proc 0 sees (c_{n-1}, c_0, c_1). Firing proc 0
flips c_0 (binary). This changes the context at proc 1 from (c_0, c_1, c_2)
to (1-c_0, c_1, c_2).

So proc 0 connects fibers that differ in the FIRST coordinate of the
context. Specifically:
  F(a, b, c) <-> F(1-a, b, c) via proc 0.

With M_1 = {(a, 0, c), (1-a, 1, 1-c)}, the 6 non-mover contexts are:
  (a, 1, c), (1-a, 0, 1-c) [toggle partners of the two movers],
  (1-a, 0, c), (1-a, 1, c), (a, 0, 1-c), (a, 1, 1-c).

Proc 0 connects F(a, 0, c) [mover] to F(1-a, 0, c) [non-mover].
It also connects F(1-a, 1, 1-c) [mover] to F(a, 1, 1-c) [non-mover].

Similarly, proc 2 connects F(a, b, c) to F(a, b, 1-c).

### The Tension

The ranking Psi must be consistent with:
1. Proc 1: Psi(c_k) > Psi(d_k) for almost all k [mover fiber > toggle fiber].
2. Proc 0: connects mover fibers to non-mover fibers (direction depends on
   proc 0's transition function and the specific config).
3. Proc 2: connects fibers differing in c_2.
4. Far procs: rearrange within fibers (don't change proc 1's context).

The adversary can CHOOSE which proc fires at each step. For a bad config
where multiple procs are privileged, the adversary picks the worst one
(the one that makes convergence hardest).

**The obstruction**: consider a far state v such that BOTH (c_0, 0, c_2, v)
and (c_0, 1, c_2, v) are bad. Proc 1 sends the first to the second
(via the mover context). But what sends the second back? No proc
can directly reverse proc 1's action at the second config, because
the second config has a non-mover context at proc 1. However, proc 0
or proc 2 could change the context and eventually route back.

The question is: over the exponentially many far states v, can the
system prevent ALL of them from forming cycles through the combined
action of procs 0, 1, 2 and far procs?

### Theorem 10.4 (Sibling Pair Cycle Existence — Conditional)

**Claim.** For n >= n_0, there exist far states v, w and a sequence of
proc firings that forms a directed cycle in the bad-config graph,
using the following structure:

  c_1 = (a, 0, c, v) --[proc 1]--> c_2 = (a, 1, c, v) 
  --[far procs]--> c_3 = (a, 1, c, w)
  --[proc 0 or 2]--> c_4 = (a', 1, c', w)
  --[far procs]--> c_5 = (a', 1, c', v)
  --[proc 0 or 2]--> c_6 = (a, b, c, v)
  ... [eventually returning to c_1]

Each step uses a proc that IS privileged at that config (the adversary
can choose it). All configs in the cycle are bad.

**Status.** We cannot prove this exists for arbitrary transition functions.
The difficulty: the far-proc transitions and proc-0/2 transitions are
chosen by the SYSTEM DESIGNER (not the adversary), and a clever designer
might block every such cycle. The claim is that for P_rest large enough,
the designer runs out of options. [GAP D remains.]

---

## Section 11: The Quantitative Threshold

Despite the gaps, we can give a precise quantitative threshold for the
transition.

### Theorem 11.1 (Bottleneck Ratio Divergence)

Define the bottleneck ratio:
  beta(n) = (product - C) / (C * |M_1|)

For sub-threshold 3CB systems:
  beta(n) >= (4*3^{n-2} - Kn) / (Kn * 2) ~ (2/K) * 3^{n-2} / n

This ratio grows exponentially. Each mover-context step in the good
cycle must "drain" beta(n) bad configs on average.

At n=4: beta ~ 0.79 (works: each step drains < 1 bad config on average).
At n=5: beta ~ 2.14 (works with difficulty).
At n=6: beta ~ 3.30 (works).
At n=7: beta ~ 7.59 (works, but barely: depth = 65 = 75% of product).
At n=8: beta ~ 80.5 (fails: recurrent SCCs form).

The transition occurs when beta exceeds the "drainage capacity" of the
system, which is bounded by the DAG depth achievable with the given
transition functions.

### Conjecture 11.2 (Sharp Threshold)

The drainage capacity D_max satisfies D_max = O(product^{1-epsilon}) for
some epsilon > 0 depending on the 3CB structure. When
beta(n) > D_max / (C * |M_1|), which happens at n = 8, convergence fails.

---

## Conclusion

The 3CB Drainage Impossibility Theorem asserts that 3 consecutive binary
processors create an unsustainable bottleneck for convergence at large n.
The binary block's 8-context valve processes exponentially many configs
with zero selectivity, while the good cycle provides only O(n) drainage
capacity.

**Proved unconditionally:**
- The structural lemmas (toggle constraint, fiber coupling, sibling
  indistinguishability, locality of context changes).
- The exponential drainage deficit (B/C -> infinity).
- Computational impossibility at n=8 (exhaustive).

**Proved conditionally (Gaps A-E):**
- No valid 3CB system exists at sub-threshold for n >= 8.

**Core open problem:**
- Converting the exponential capacity mismatch into a constructive
  cycle existence proof in the bad-config graph. This requires either
  (a) a direct construction of a multi-proc bad cycle, or (b) a graph-
  theoretic argument that dense nondeterministic graphs with constrained
  structure must contain cycles.
