"""
Thinking about the proof for n >= 3.

KEY INSIGHT: At n >= 3, position p has two distinct neighbors p-1 and p+1.
Each non-p proc q has at most ONE neighbor equal to p (since q-1, q, q+1 are
three distinct positions mod n for n >= 3, and only one can equal p).

So for q != p not adjacent to p: q sees identical (L,S,R) in g_j and g_k.
For q adjacent to p (say q = p+1): q sees (g_j[p], g_j[q], g_j[q+1]) vs
  (g_k[p], g_k[q], g_k[q+1]). Only L differs.
For q = p-1: only R differs.

Now consider the PROPAGATION more carefully.

g_j and g_k are Hamming-1 at p. Who is the mover?

Priv(g_j) = some proc m_j.
Priv(g_k) = some proc m_k.

For any proc q not in {p-1, p, p+1}: q sees same context in both configs.
So: q is privileged in g_j iff q is privileged in g_k.

By unique privilege: at most one proc is privileged.

Case 1: m_j = m_k = q for some q not in {p-1, p, p+1}.
  Then firing q gives the same result in both. g_{j+1} and g_{k+1} differ
  only at p (q's value changes identically in both). Propagation works.

Case 2: m_j is in {p-1, p, p+1}.
  Sub-case 2a: m_j = p.
    Then p is privileged in g_j. Is p privileged in g_k?
    p's context: (g[p-1], g[p], g[p+1]). S differs.
    Could go either way.

    If p is also privileged in g_k: m_k = p.
    Firing p in both: g_{j+1}[p] = f(g_j[p-1], g_j[p], g_j[p+1]),
    g_{k+1}[p] = f(g_k[p-1], g_k[p], g_k[p+1]).
    Same L, different S, same R. Different inputs => possibly different outputs.
    If outputs differ: still Hamming-1 at p.
    If outputs same: g_{j+1} = g_{k+1}, impossible (distinct configs in cycle). ✓
    So propagation works.

    If p is NOT privileged in g_k: some other proc m_k is.
    m_k must be in {p-1, p+1} (since procs outside this set match privilege).
    Wait: if m_j = p, then p is privileged in g_j. No other proc is privileged in g_j.
    For procs outside {p-1, p, p+1}: same context => not privileged in g_j => not in g_k.
    So m_k ∈ {p-1, p+1}.

    Say m_k = p+1. So: in g_j, p fires. In g_k, p+1 fires.
    g_{j+1}: changes at p. g_{k+1}: changes at p+1.
    g_{j+1} vs g_{k+1}: differ at p (changed differently) AND at p+1 (changed in g_k only).
    Hamming distance 2! Propagation breaks.

    But can this actually happen? Let's check.

  Sub-case 2b: m_j = p+1 (or p-1, symmetric).
    p+1 sees (g[p], g[p+1], g[p+2]). L = g[p] differs between g_j and g_k.
    Is p+1 privileged in g_k? Different L, might change privilege.

    If p+1 is also privileged in g_k: m_k = p+1. Propagation works
    (same argument as Case 1, but with a wrinkle: p+1's transition depends on
    g[p], which differs. So g_{j+1}[p+1] and g_{k+1}[p+1] might differ.
    Then Hamming-1 at p AND possibly at p+1... Hamming-2! Bad.)

    Actually: g_{j+1}[p] = g_j[p] (p doesn't fire). g_{k+1}[p] = g_k[p] (p doesn't fire).
    g_j[p] != g_k[p]. So still differ at p.
    g_{j+1}[p+1] = f(g_j[p], g_j[p+1], g_j[p+2]).
    g_{k+1}[p+1] = f(g_k[p], g_k[p+1], g_k[p+2]).
    = f(g_k[p], g_j[p+1], g_j[p+2])  (since p+1, p+2 agree).
    Different first arg. Output might differ.
    If output differs: Hamming distance 2 (at p and p+1). NOT Hamming-1.
    If output same: still Hamming-1 at p. OK.

    So: when m_j = m_k = p+1 (neighbor of p), after firing:
    - If f(g_j[p], S, R) = f(g_k[p], S, R): Hamming-1 preserved.
    - If f(g_j[p], S, R) != f(g_k[p], S, R): becomes Hamming-2.

    This is NOT guaranteed to preserve Hamming-1!

So: the propagation argument does NOT work cleanly for n >= 3 when the mover
is a neighbor of p. The Hamming-1 property can "break" by becoming Hamming-2.

But: the REVERSE also applies. Hamming-2 can become Hamming-1 when a neighbor
of p fires and the outputs happen to match.

This means: we can't simply propagate Hamming-1. The dynamics can create and
destroy Hamming-1 relationships at neighbors of p.

REVISED APPROACH: Think about it as a counting/parity argument.

Let me reconsider. The fact that H-1 Uniqueness holds at n >= 3 (empirically)
but fails at n=2 suggests there's a proof, but it's subtler than simple propagation.

NEW IDEA: Use the fact that in a good cycle, the mover sequence visits
each proc multiple times. The Hamming-1 constraint is GLOBAL — everything
except p must match. This is extremely restrictive.

Between g_j and g_k: d steps fire. For each proc q != p:
  - q fires some number of times a_q.
  - q's value must return to start.
  - q's transitions depend on its neighbors' values, which are evolving.

The "return" constraint means: the composition of a_q transition maps at q
(with varying contexts) equals the identity on q's value.

At n >= 3, proc q's transition depends on L = g[(q-1)%n] and R = g[(q+1)%n].
These values change as other procs fire. The constraint that q returns to its
start value, combined with ALL other non-p procs also returning, is extremely tight.

At n=2: each proc's transition depends on the OTHER proc's value (L=R=other).
The other proc IS p (if q != p, there's only one other). So q's entire context
is determined by p's changing value. This gives q enough "freedom" to return.

At n >= 3: q's context depends on its two neighbors, which (for most q) are
independent of p. Their values are FIXED during non-fire intervals.

Hmm. Let me just try a cleaner counting argument.

COUNTING ARGUMENT:
In a good cycle of length CL = sum(m_p):
- Number of good configs = CL.
- Number of Hamming-1 pairs = CL (exactly the adjacent pairs, if theorem holds).
- Each adjacent pair (g_i, g_{i+1}) is Hamming-1 at moverAt(i).

Can there be ADDITIONAL Hamming-1 pairs?

Total possible Hamming-1 pairs: for each position p and each pair of values
(v, v') with v != v', the configs that match everywhere except p and take
values v, v' at p form a potential Hamming-1 pair. But they must both be in
the good cycle.

For each p: p takes m_p values in the cycle. Between consecutive firings of p,
p's value is constant while other procs evolve. A "phase" of p is a maximal
interval where p's value is constant.

There are m_p phases of p. In phase i (where p has value v_i):
the other procs go through a specific sequence of configs.
For two phases i, j with v_i != v_j: a Hamming-1 pair exists iff some
config in phase i matches some config in phase j at all positions except p.

This is like asking: do the two "fibers" (projections ignoring p) intersect?

The fiber of phase i: the sequence of (non-p) configs during phase i.
The fiber of phase j: the sequence of (non-p) configs during phase j.

If any config in fiber i equals any config in fiber j: Hamming-1 pair!

The adjacent Hamming-1 pairs come from the BOUNDARIES between phases:
the last config of phase i and the first config of phase i+1 share
the same (non-p) values (since only p changes at the boundary).

So: the boundary configs between phases i and i+1 give a Hamming-1 pair.
These are adjacent in the cycle. There are m_p such boundaries.

Can an INTERIOR config of phase i match an interior config of phase j?
That would give a non-adjacent Hamming-1 pair.

Interior config of phase i: a config where p = v_i and the other procs
are at some specific values determined by the dynamics.
Interior config of phase j: p = v_j, other procs at some values.

For these to match (at non-p positions): the dynamics must bring all
other procs to the exact same state at two different points in the cycle
(while p has different values).

At n >= 3: this seems extremely unlikely because the dynamics are driven
by ALL procs' interactions. The fiber sequences are determined by the
complex interplay of n >= 3 processors.

But "extremely unlikely" is not a proof. I need to find the actual argument.

Let me revisit the propagation idea, but track what happens more carefully.
"""

# Let me verify: in ALL n=2 counterexamples, is the mover always a neighbor of p?
# And: does the "becomes Hamming-2 then returns to Hamming-1" pattern occur?

from itertools import product as iprod
import random

def get_good_cycle(ms, tables):
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
    if not good: return None, None
    start = next(iter(good))
    cycle = [start]; movers = [good[start]]; cur = start
    for _ in range(100000):
        nxt = fire(cur, good[cur])
        if nxt == start: break
        if nxt not in good: return None, None
        cycle.append(nxt); movers.append(good[nxt]); cur = nxt
    else: return None, None
    return cycle, movers

# At n=2, p-1 = p+1 = the other proc. So EVERY proc is a neighbor of p.
# That's why propagation fails: the mover is always a neighbor.

# At n >= 3, the key question: can the mover sequence for a Hamming-1 pair
# always avoid neighbors of p? Or can it go through neighbors and still
# maintain Hamming-1?

# Let me look at this from the FIBER perspective.
# For a specific violating system at n=2, trace the fiber sequences.

random.seed(42)
ms = [2, 3]; n = 2
for trial in range(50000):
    tables = []
    for p in range(n):
        t = {}
        mL = ms[(p-1)%n]; mS = ms[p]; mR = ms[(p+1)%n]
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    t[(L,S,R)] = random.randrange(mS)
        tables.append(t)
    cycle, movers = get_good_cycle(ms, tables)
    if not cycle or len(cycle) <= 2: continue
    CL = len(cycle)
    fc = [0]*n
    for m in movers: fc[m] += 1
    if not all(fc[p] == ms[p] for p in range(n)): continue

    has_viol = False
    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1 and min(k-j, CL-(k-j)) != 1:
                has_viol = True
                viol_p = diff[0]
                viol_j, viol_k = j, k
                break
        if has_viol: break

    if has_viol:
        print(f"CL={CL}, movers={movers}")
        print(f"Violation at p={viol_p}, j={viol_j}, k={viol_k}")

        # Trace fibers: for each phase of p, show non-p values
        for pp in range(n):
            phases = []
            current_phase = []
            current_val = cycle[0][pp]
            for i in range(CL):
                if movers[i] == pp:
                    phases.append((current_val, current_phase))
                    current_phase = []
                    current_val = cycle[(i+1)%CL][pp]
                else:
                    current_phase.append(i)
            phases.append((current_val, current_phase))
            # Show non-pp values during each phase
            other = 1 - pp  # n=2
            print(f"  Proc {pp} phases (value at other={other}):")
            for val, steps in phases:
                if steps:
                    fiber = [cycle[s][other] for s in steps]
                    print(f"    val={val}, steps={steps}, fiber={fiber}")

        # Hamming distances between all pairs
        print("  Hamming distances:")
        for i in range(CL):
            dists = []
            for j2 in range(CL):
                d = sum(1 for q in range(n) if cycle[i][q] != cycle[j2][q])
                dists.append(d)
            print(f"    [{i}] {cycle[i]}: {dists}")

        break

print("\nDone")
