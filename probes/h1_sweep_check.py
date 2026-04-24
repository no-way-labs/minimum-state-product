"""
Check H-1 Uniqueness for SWEEP cycles specifically.

A sweep cycle visits procs in a specific order (each fires once per sweep).
The mover word for a sweep has each proc appearing exactly once per sweep period.

For the LB proof context: we need H-1 for good cycles of systems with
binary (m=2) and ternary (m=3) procs, where the good cycle has
fc(p) = m_p (each proc visits all states).

Key property: in such systems, CL = sum(m_p) and the mover word
visits each proc exactly m_p times.

The question is whether the MOVER WORD structure (sweep vs non-sweep)
matters for H-1 uniqueness.

Let me check: for the specific mover patterns that arise in sweep cycles
(where each proc fires m_p times in a specific pattern), does H-1 hold?

Actually, let me approach this differently.

THEOREM (H-1 Uniqueness, corrected):
In a good cycle of a self-stabilizing token ring with n >= 3 processors,
where fc(p) = m_p for all p, and gcd(m_0, ..., m_{n-1}) = 1:
H-1 Uniqueness holds.

The proof uses the periodicity argument:
1. Suppose H-1 pair at distance d with 2 <= d <= CL-2.
2. The pair defines a fiber-match. The fiber may or may not propagate.
3. Even without propagation: we can derive a contradiction from the
   fiber return condition and the fire-count constraint.

NEW PROOF APPROACH: Use the fiber-return counting argument.

If fib_p(j) = fib_p(k) with d = k-j, then:
For each q != p: the value at q returns to its starting value after
the d intervening steps. In these d steps, q fires a_q times.

After a_q firings, q returns to its start. But the transitions at q
depend on context (neighbors' values), so the "return" is context-dependent.

KEY: q's value at each step is determined by the HISTORY of transitions.
The history depends on the mover sequence and the transition functions.

For q to return after a_q firings: this is NOT equivalent to a_q being
a multiple of the value-cycle length (since there's no fixed value-cycle
when transitions are context-dependent).

So the counting argument (a_q multiple of m_q) doesn't apply.

BUT: if we additionally know that q visits ALL m_q values exactly once
in the full cycle (which follows from fc(q) = m_q and the value sequence
being a permutation of all m_q values -- which we need to verify):

Then: in the arc of length d, q fires a_q times and visits a_q + 1 values
(including start). For q to return: q visits a_q + 1 values total,
with the last = first. The values form a "path" in q's value space.

If this path visits all m_q values: a_q >= m_q (need at least m_q transitions).
But also a_q <= m_q (total fires). So a_q = m_q and the complementary arc
has b_q = 0. This means all of q's firings happen in one arc.

If the path doesn't visit all values: a_q < m_q.

For the case fc(q) = m_q: does q visit all values?
This is equivalent to: the transition sequence at q forms a permutation
(visits all m_q values exactly once before returning).

This is NOT guaranteed in general (as seen in the Sol3v1 example where
ternary procs visit only 2 of 3 values). BUT: we ASSUMED fc(q) = m_q,
which means q fires exactly m_q times. If q visits fewer than m_q values,
then some value is visited multiple times, which means q fires the same
value with different contexts...

Actually: q fires m_q times. Each firing changes q's value. After m_q firings,
q returns to start. The sequence of values is v_0, v_1, ..., v_{m_q} with
v_0 = v_{m_q}. Each v_{i+1} != v_i. The values CAN repeat (q could go
0->1->0->2->0 for m_q=4).

WAIT: with m_q values and m_q transitions, each changing the value:
v_0 -> v_1 -> ... -> v_{m_q} with v_0 = v_{m_q} and v_{i+1} != v_i.
This is a walk of length m_q on {0, ..., m_q-1} that returns to start.
The walk visits m_q+1 vertices (with possible repeats), but
the number of DISTINCT vertices is at most m_q.

If the walk visits all m_q vertices: it's a Hamiltonian cycle on some graph.
Since the graph is just {0,...,m_q-1} with edges from the transitions,
and we need a closed walk of length m_q visiting all vertices: this is
exactly a Hamiltonian cycle (each vertex visited exactly once).

If the walk DOESN'T visit all vertices: some vertex is never visited,
and at least one vertex is visited more than once.

For the LB proof context: we ASSUME fc(p) = m_p AND m_p = number of states
of proc p. The question is: does fc(p) = m_p guarantee all values are visited?

ANSWER: YES! Here's why:
The good cycle has CL = sum(m_p) configs. For each value v of proc p,
let c_v = number of configs where p holds value v. Then sum_v c_v = CL.
Between consecutive firings of p, p holds a constant value. There are m_p
such intervals (since fc(p) = m_p). Each interval has some length.
The lengths sum to CL.

If value v is never held: c_v = 0. Then sum_{v'!=v} c_{v'} = CL.
But the number of good configs with p = v' is c_{v'} for each v'.

However: there's no reason why c_v must be > 0 in general.
The issue is that the transition function might skip value v entirely.

Example: proc p is ternary (m_p=3), fc(p)=3. Transitions:
0 -> 1 -> 2 -> 0 (visits all 3). OR:
0 -> 1 -> 0 -> 2 -> ... wait, with fc=3 and returning to start:
v_0 = 0, v_1 = 1, v_2 = 0, v_3 = 2. But fc=3 means 3 transitions,
so v_0, v_1, v_2, v_3 with v_0=v_3. This visits 0,1,0,2 — 3 distinct values.
The walk 0->1->0->2 has length 3 and visits {0,1,2}. ✓

Another: v_0=0, v_1=1, v_2=2, v_3=0. Length 3, visits {0,1,2}. ✓

Can we have v_0=0, v_1=1, v_2=0, v_3=0? No, v_2=0 -> v_3 must be != 0.
v_0=0, v_1=1, v_2=0, v_3=2. v_3 must = v_0=0. So 2 != 0. ✗

Wait: fc(p) = m_p = 3 means 3 firings. v_3 must = v_0 (returns).
v_0=0, v_1=1, v_2=0: v_3 must = 0 and v_3 != v_2=0. Contradiction!
So: 0->1->0 can't return to 0 in one step.

With m_p=3: walk of length 3 starting and ending at v_0.
v_0, v_1, v_2, v_3=v_0. Each v_{i+1} != v_i.
So: v_1 != v_0, v_2 != v_1, v_0 != v_2.
3 values, all different! v_0, v_1, v_2 are all distinct.

PROOF: With m_p values and a closed walk of length m_p where each step
changes value: all values are visited.

Proof by pigeonhole: the walk visits m_p + 1 positions (including return),
which is m_p distinct positions (since first = last). Each position is in
{0, ..., m_p-1}. If any value is unvisited: at most m_p - 1 distinct values
are available, but we have m_p positions. By pigeonhole, some value is
visited at two non-consecutive positions (say v_i = v_j with j > i+1).
The sub-walk v_i, v_{i+1}, ..., v_j has length j-i, starts and ends at v_i,
and each step changes. The remaining walk v_0, ..., v_i, v_j, ..., v_{m_p}
has length m_p - (j-i), starts and ends at v_0.

Now: the sub-walk v_i...v_j visits at most j-i values.
The remaining walk visits at most m_p - (j-i) values.
Total distinct values <= (j-i) + (m_p - (j-i)) - 1 = m_p - 1 (subtracting
v_i which appears in both). But we have m_p values total, so at least 1 is
unvisited. Hmm, this doesn't quite work as a proof yet.

Actually, for m_p = 3:
Walk 0, v1, v2, 0 with v1 != 0, v2 != v1, 0 != v2.
So v1 in {1,2}, v2 in {0,...,2}\{v1}, 0 != v2.
If v1=1: v2 in {0,2}, v2 != 0 -> v2=2. Walk: 0,1,2,0. ✓ All 3 visited.
If v1=2: v2 in {0,1}, v2 != 0 -> v2=1. Walk: 0,2,1,0. ✓ All 3 visited.
So for m_p=3: ALL values always visited. ✓

For m_p=2: Walk 0, v1, 0 with v1 != 0, 0 != v1. v1=1. Walk: 0,1,0. ✓

For general m_p: proof that closed walk of length m_p with no consecutive
repeats visits all m_p values.

CLAIM: any closed walk of length m_p on {0,...,m_p-1} with no consecutive
repeats must be a DERANGEMENT cycle.

Hmm, not exactly. But the key insight: with m_p steps and m_p values,
if the walk returns to start and no two consecutive values are equal,
then it forms a cyclic permutation of all values.

PROOF: Consider the walk as a map sigma: {0,...,m_p-1} -> {0,...,m_p-1}
where sigma is NOT a function (the transition depends on context).
But: the walk v_0, v_1, ..., v_{m_p-1}, v_{m_p}=v_0 has m_p edges.
If we model this as a multigraph on {0,...,m_p-1}: each edge goes from
v_i to v_{i+1} with v_{i+1} != v_i. There are m_p edges forming a closed walk.

If the walk visits all m_p vertices: ✓
If not: some vertex has in-degree + out-degree = 0 (never visited).
Each visited vertex has out-degree >= 1 (it transitions to something).
And in-degree >= 1 (something transitions to it — since the walk must
pass through it to leave it, but also must enter it at some point,
unless it's v_0 which has the start edge).

Actually: each vertex in the walk has at least 1 incoming and 1 outgoing edge
(since the walk visits it, transitions out, and must arrive at it too — except
possibly v_0 which is entered at the start and left at step 0, and re-entered
at step m_p).

If vertex v is not in the walk: 0 edges at v. Total edges = m_p.
Distributed among at most m_p - 1 vertices. Each visited vertex uses at least
2 edges (1 in, 1 out) — but edges are shared between vertices.
Total edges going into visited vertices: m_p (each of the m_p edges ends somewhere).
Total edges going out of visited vertices: m_p (each edge starts somewhere).

If k vertices visited (k <= m_p - 1): each visited vertex has at least 1
outgoing edge. But wait, some vertex must have 2+ outgoing edges (since
total out-degree = m_p > k, at least one vertex has out-degree > 1).

Hmm, this doesn't directly prove the claim. Let me try differently.

For m_p >= 2: A closed walk of length m_p with no consecutive repeats on
{0,...,m_p-1}. Does it visit all vertices?

For m_p = 4: walk 0,1,0,1,0. Length 4, returns to 0, no consecutive repeats.
Only visits {0,1}. m_p=4, only 2 vertices visited.

Wait: is this possible? 0->1->0->1->0. Length 4. Visits only {0,1}.
But m_p = 4, so {0,1,2,3} available. 0 and 1 are the only ones visited.

So the claim is FALSE for m_p >= 4! A closed walk of length m_p can miss
vertices.

But: does this happen when fc(p) = m_p in a VALID self-stabilizing system?
The transitions are context-dependent. p could fire 4 times and alternate
between 0 and 1 if the contexts allow it. The other values (2, 3) would
be "dead states" for p in the good cycle.

However: for the LB proof, we want minimal-product systems. If p has m_p=4
states but only visits 2 in the good cycle: we could replace p with a
2-state proc, reducing the product. So the relevant systems for the LB proof
MUST visit all states.

This means: the correct condition for H-1 Uniqueness is:
"p visits all m_p values in the good cycle" (i.e., the value walk is a
Hamiltonian cycle on the complete graph minus self-loops).

For m_p in {2, 3}: this is AUTOMATIC (as shown above).
For m_p >= 4: NOT automatic (the walk can miss vertices).

For the LB proof: binary (m=2) and ternary (m=3) procs always visit all values.
So the condition is automatically satisfied.

FINAL: the correct sufficient condition for the LB proof is:
n >= 3, all procs binary or ternary, fc(p) = m_p.
Under these conditions: each proc visits all values (AUTOMATIC for m in {2,3}),
and the periodicity argument applies.

Let me verify this once more with the original violation. ms=[2,2,3], fc=[2,2,2].
Proc 2 is ternary with fc(2)=2 != m_2=3. So this violates our condition.

All known n >= 3 violations have fc != m for at least one proc. ✓
"""

# Verify: for m_p in {2,3} with fc=m_p, all values are visited.
# This is automatic from the walk argument above.
# But let me verify computationally with known systems.

from itertools import product as iprod

def check_all_values(ms, tables):
    n = len(ms)
    def fire(config, p):
        L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
        new = list(config); new[p] = tables[p][(L,S,R)]
        return tuple(new)
    good = {}
    for config in iprod(*[range(m) for m in ms]):
        privs = []
        for pp in range(n):
            L = config[(pp-1)%n]; S = config[pp]; R = config[(pp+1)%n]
            if tables[pp][(L,S,R)] != S:
                privs.append(pp)
        if len(privs) == 1:
            good[config] = privs[0]
    if not good: return None
    start = next(iter(good))
    cycle = [start]; movers = [good[start]]; cur = start
    for _ in range(100000):
        nxt = fire(cur, good[cur])
        if nxt == start: break
        if nxt not in good: return None
        cycle.append(nxt); movers.append(good[nxt]); cur = nxt
    else: return None
    CL = len(cycle)
    fc = [movers.count(p) for p in range(n)]
    if not all(fc[p] == ms[p] for p in range(n)): return None

    for p in range(n):
        vals = set(cycle[i][p] for i in range(CL))
        if len(vals) < ms[p]:
            return False  # doesn't visit all values
    return True

# Sol3v1: fc != m_p for ternary procs
for n in [5, 7, 9]:
    ms = [2]+[3]*(n-1)
    tables = []
    for p in range(n):
        t = {}
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    if p == 0: t[(L,S,R)] = (S+1)%ms[p] if S==L else S
                    else: t[(L,S,R)] = L if S!=L else S
        tables.append(t)
    result = check_all_values(ms, tables)
    cycle_info = ""
    if result is None:
        # Get the actual cycle info
        def fire_c(config, p):
            L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
            new = list(config); new[p] = tables[p][(L,S,R)]
            return tuple(new)
        good = {}
        for config in iprod(*[range(m) for m in ms]):
            privs = []
            for pp in range(n):
                L = config[(pp-1)%n]; S = config[pp]; R = config[(pp+1)%n]
                if tables[pp][(L,S,R)] != S: privs.append(pp)
            if len(privs) == 1: good[config] = privs[0]
        start = next(iter(good))
        cycle = [start]; movers = [good[start]]; cur = start
        for _ in range(100000):
            nxt = fire_c(cur, good[cur])
            if nxt == start: break
            if nxt not in good: break
            cycle.append(nxt); movers.append(good[nxt]); cur = nxt
        CL = len(cycle)
        fc = [movers.count(p) for p in range(n)]
        cycle_info = f"CL={CL}, fc={fc}"
        # Check all values manually
        for p in range(n):
            vals = set(cycle[i][p] for i in range(CL))
            if len(vals) < ms[p]:
                cycle_info += f" proc {p} visits {len(vals)}/{ms[p]}"
    print(f"Sol3v1 n={n}: fc=m_p={result}, {cycle_info}")

# Sol1: fc = m_p = K
for K in [3, 5]:
    ms = [K]*5
    tables = []
    for p in range(5):
        t = {}
        for L in range(K):
            for S in range(K):
                for R in range(K):
                    if p == 0: t[(L,S,R)] = (S+1)%K if S==L else S
                    else: t[(L,S,R)] = L if S!=L else S
        tables.append(t)
    result = check_all_values(ms, tables)
    print(f"Sol1 K={K} n=5: fc=m_p={result}")

print("\nFor binary/ternary (m in {2,3}): closed walk of length m on m values")
print("with no consecutive repeats ALWAYS visits all values:")
print("  m=2: 0->1->0 (length 2, visits {0,1})")
print("  m=3: 0->a->b->0 with a!=0, b!=a, 0!=b")
print("    a=1: b in {0,2}\\{0} = {2}. Walk: 0,1,2,0")
print("    a=2: b in {0,1}\\{0} = {1}. Walk: 0,2,1,0")
print("  Both visit all 3 values. QED for m<=3.")
