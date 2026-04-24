"""
H-1 UNIQUENESS THEOREM — PROOF AND VERIFICATION

Theorem: For n >= 3, in any good cycle of a self-stabilizing token ring where
fc(p) = m_p for all processors p (each processor fires exactly m_p times),
if good configs g_j and g_k differ at exactly one position p (Hamming distance 1),
then j and k are adjacent in the cycle (|j - k| = 1 mod CL).

PROOF:

Lemma (Propagation): If g_j and g_k are Hamming-1 at position p, then
g_{j+1} and g_{k+1} are also Hamming-1 at position p.

Proof of Lemma:
  Let n >= 3. g_j and g_k agree at all positions except p.

  Step 1: moverAt(j) = moverAt(k).

    Case A: moverAt(j) = q where q != p.
      Proc q's context (L_q, S_q, R_q) in g_j:
        L_q = g_j[q-1], S_q = g_j[q], R_q = g_j[q+1].
      Since n >= 3, at most one of {q-1, q, q+1} equals p (they're distinct mod n).
      But q != p. If q-1 = p or q+1 = p, then one of L_q, R_q differs between g_j and g_k.

      WAIT: this breaks the argument. If q is a neighbor of p, q sees different context.

      Let me reconsider. If q-1 = p: L_q differs. If q+1 = p: R_q differs.
      Then q might be privileged in g_j but not g_k, or vice versa.

      Actually: unique privilege means exactly ONE proc is privileged.
      If q != p is privileged in g_j, we need q to also be privileged in g_k.

      For q NOT adjacent to p (neither q-1=p nor q+1=p):
        q sees same (L,S,R) in g_j and g_k. So privileged(g_j,q) = privileged(g_k,q).

      For q adjacent to p: q sees different context. May or may not match.

      Hmm, the simple propagation argument has a gap for neighbors of p.
      Let me think more carefully...

  Actually wait. Let me reconsider the unique privilege argument.

  Let priv(g) = the unique privileged proc in good config g.

  If priv(g_j) = q where q is NOT adjacent to p (and q != p):
    q sees same context in g_j and g_k, so q is privileged in g_k.
    By uniqueness: priv(g_k) = q.

  If priv(g_j) = q where q IS adjacent to p (but q != p):
    q sees different context. Two sub-cases:
    (a) q is privileged in g_k too: priv(g_k) = q. OK.
    (b) q is NOT privileged in g_k: then some other proc r is.
        r != q, and r is privileged in g_k.
        If r != p and r not adjacent to p: r sees same context in both,
        so r is privileged in g_j too. But priv(g_j) = q != r. Contradiction.
        If r = p: p's context differs (S differs), so could be privileged in one but not other.
        If r adjacent to p (r != q): r sees different context, could be privileged in g_k but not g_j.

    So the only way priv(g_k) != q is if priv(g_k) = p or priv(g_k) = another neighbor of p.

    At n >= 3, p has exactly 2 neighbors: p-1 and p+1.
    If priv(g_j) = p-1: the "other neighbor" is p+1.
    For p+1 to be privileged in g_k but not g_j:
      p+1's context: (g[p], g[p+1], g[p+2]).
      g[p] differs between g_j and g_k (that's the Hamming-1 position).
      g[p+1] and g[p+2] are same.
      So p+1 sees (g_j[p], S, R) vs (g_k[p], S, R) — different L.
      It's possible p+1 is privileged in one but not the other.

    This is getting complicated. Let me try a different approach.

  BETTER APPROACH: Don't argue about movers. Use distinctness + counting.

  Suppose g_j and g_k are Hamming-1 at p with cyclic distance d > 1.
  WLOG d = k - j with 2 <= d <= CL - 2.

  Between steps j and k, the movers fire at positions moverAt(j), ..., moverAt(k-1).
  This is d firings. Some at position p, some elsewhere.

  For position q != p: g_j[q] = g_k[q]. So the NET effect of all firings at q
  between j and k must be zero: q returns to its original value.

  For position p: g_j[p] != g_k[p]. The firings at p between j and k change
  p's value from g_j[p] to g_k[p].

  Now: between steps k and j+CL (going around the cycle), there are CL-d firings.
  Again: for q != p, net effect is zero (g_k[q] -> g_j[q], same values).
  For p: goes from g_k[p] back to g_j[p] (since it's a cycle).

  So: the CL firings split into two arcs. In each arc, every q != p returns to
  its starting value, and p changes.

  Let a_q = number of times q fires in the first arc (steps j..k-1).
  Let b_q = number of times q fires in the second arc (steps k..j+CL-1).
  a_q + b_q = m_q (total fires in cycle).

  For q != p to return: q must fire a complete number of "cycles" through its
  values in each arc. Since q visits all m_q values exactly once in the full cycle,
  and q returns to its start in the first arc of a_q firings:
  q must make a_q/m_q complete loops. But q visits each value once per loop,
  so a_q must be a multiple of m_q.

  Similarly b_q is a multiple of m_q. Since a_q + b_q = m_q:
  a_q ∈ {0, m_q} (the only multiples of m_q that sum to m_q with a non-negative complement).

  Wait: multiples of m_q that are <= m_q: {0, m_q}. And b_q = m_q - a_q must also be
  a multiple of m_q. So (a_q, b_q) ∈ {(0, m_q), (m_q, 0)}.

  HOLD ON. This argument assumes q visits all m_q values exactly once. But that's
  ONLY true if q's value sequence is a permutation cycle of length m_q.

  Actually: fc(q) = m_q means q fires m_q times. Each firing changes q's value
  (since the proc is privileged, hence fires to a different value). After m_q firings,
  q returns to start. So q visits m_q+1 values counting the start, but the last = first.
  So q visits exactly m_q distinct values.

  But does q visit each value exactly once? Yes! q has m_q states, visits m_q distinct
  values, fires m_q times, and returns to start. So the value sequence at q is a
  permutation of {0, ..., m_q-1}, forming a single cycle of length m_q.

  Now: if q fires a_q times in the first arc and returns to its start, that means
  q traverses a_q steps in its value cycle and returns. Since the value cycle has
  length m_q (a single cycle): a_q must be a multiple of m_q. ✓

  So: a_q ∈ {0, m_q} for all q != p.

  If a_q = 0: q doesn't fire at all in the first arc.
  If a_q = m_q: q fires all m_q times in the first arc, and not at all in the second.

  Let S = {q != p : a_q = m_q} (procs that fire entirely in the first arc).
  The remaining procs (other than p) fire entirely in the second arc.

  First arc length: d = a_p + sum_{q in S} m_q
  where a_p is the number of times p fires in the first arc.

  Second arc length: CL - d = (m_p - a_p) + sum_{q not in S, q != p} m_q

  For p: p fires a_p times in first arc, m_p - a_p in second.
  p does NOT return in the first arc (g_j[p] != g_k[p]), so a_p is NOT a multiple
  of m_p. Combined with 0 <= a_p <= m_p: a_p ∈ {1, 2, ..., m_p - 1}.

  Now: consider what happens at the boundary between the two arcs.
  At step k-1 (last step of first arc): moverAt(k-1) fires.
  At step k (first step of second arc): moverAt(k) fires.

  The procs that fire in the first arc are: p (a_p times) and procs in S (all their fires).
  The procs that fire in the second arc are: p (m_p - a_p times) and procs NOT in S.

  KEY OBSERVATION: consider a proc q in S (fires only in first arc, not in second).
  q fires m_q times, visiting all m_q values. In particular, some firing of q at step t
  (j <= t < k) has a specific context. In the second arc (k <= t' < j+CL), q never fires.
  That means: at every step in the second arc, q is NOT privileged.

  Similarly, a proc r not in S fires only in the second arc. In the first arc, r is
  never privileged.

  Now: the mover sequence is a permutation sequence. At each step, exactly one
  proc is privileged (and fires). The proc that fires is determined by the config.

  Let's count: in the first arc (d steps), only p and procs in S fire.
  In the second arc (CL-d steps), only p and procs NOT in S fire.

  This creates a very rigid structure. Between the two arcs, the set of
  "active" procs changes completely (except for p).

  DOES THIS LEAD TO A CONTRADICTION?

  Not directly. But consider the PROPAGATION argument more carefully for n >= 3.
  Even though neighbors of p see different contexts, the split into two arcs
  forces a very constrained structure. Let me check if such arcs can exist.
"""

# Verify the arc split computationally
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
        for p in range(n):
            L = config[(p-1)%n]; S = config[p]; R = config[(p+1)%n]
            if tables[p][(L,S,R)] != S:
                privs.append(p)
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

# For the ms=[2,3] n=2 counterexamples, verify the arc structure
random.seed(42)
ms = [2, 3]
n = 2
count = 0
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

    for j in range(CL):
        for k in range(j+1, CL):
            diff = [i for i in range(n) if cycle[j][i] != cycle[k][i]]
            if len(diff) == 1:
                cdist = min(k-j, CL-(k-j))
                if cdist > 1:
                    p = diff[0]
                    d = k - j
                    # Count firings per proc in first arc
                    arc1_movers = [movers[i] for i in range(j, k)]
                    arc1_fc = [arc1_movers.count(q) for q in range(n)]
                    arc2_movers = [movers[i % CL] for i in range(k, j+CL)]
                    arc2_fc = [arc2_movers.count(q) for q in range(n)]

                    if count < 5:
                        print(f"n=2, ms={ms}, CL={CL}, j={j}, k={k}, p={p}, d={d}")
                        print(f"  arc1 fc: {arc1_fc}, arc2 fc: {arc2_fc}")
                        print(f"  Total fc: {fc}")
                        # Check: for q != p, is a_q in {0, m_q}?
                        for q in range(n):
                            if q != p:
                                a = arc1_fc[q]
                                print(f"  q={q}: a_q={a}, m_q={ms[q]}, 0-or-full: {a in [0, ms[q]]}")
                    count += 1
                    break
        if count > 4: break
    if count > 4: break

print(f"\nChecked {count} violations")

# Now verify: at n=2, a_q CAN be in {0, m_q} for q != p.
# The issue is that at n=2, when p changes value, q's context changes
# (since q's L = q's R = p's value). So q seeing different context
# can still be "returning" — it just follows a different path that
# happens to end at the same value.
# This is possible because the transition function is context-dependent!
# At n >= 3: the argument should still hold because...
# Actually, let me re-examine. The return argument says q fires a_q times
# and its value returns. For q's VALUE to return, q must traverse a complete
# cycle in its value space. The value transitions at q depend on the context
# (L, R), which CHANGES during the arc. So q's value path is not a simple
# cycle — it depends on the sequence of contexts.
#
# Hmm, this means my "a_q must be multiple of m_q" argument is WRONG!
# The value at q follows a path determined by the sequence of contexts
# (which depend on the mover sequence and other proc values).
# Just because q fires a_q times and returns to its start doesn't mean
# a_q is a multiple of the value-cycle length, because the "cycle" depends
# on context.
#
# Let me re-examine...

# Actually the argument IS that q visits all m_q values in the full cycle.
# But within an arc, q might visit only some values and return.
# E.g., if m_q = 3 and q's path is 0 -> 1 -> 0 in the first arc (a_q = 2),
# that's not a complete cycle but q does return.
# This breaks the "a_q must be multiple of m_q" argument!

# So: the return CAN happen with fewer firings if different contexts
# create a non-cyclic path. The key question is whether this happens at n >= 3.

print("\n=== Checking if violations exist at n=3 with larger search ===")
for ms_test in [[2,3,3], [2,2,3], [3,3,5]]:
    random.seed(42)
    found = 0; viols = 0
    for trial in range(50000):
        tables = []
        n = len(ms_test)
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        cycle, movers = get_good_cycle(ms_test, tables)
        if not cycle or len(cycle) <= 2: continue
        CL = len(cycle)
        fc = [0]*n
        for m in movers: fc[m] += 1
        if not all(fc[p] == ms_test[p] for p in range(n)): continue
        found += 1
        for j in range(CL):
            for k in range(j+1, CL):
                diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
                if diff == 1 and min(k-j, CL-(k-j)) != 1:
                    viols += 1
                    break
            if viols: break
    print(f"ms={ms_test}: {found} minimal, {viols} violations")
