r"""
==========================================================================
H-1 UNIQUENESS — STATUS REPORT AND CORRECTED THEOREM
==========================================================================

ORIGINAL CLAIM: In a good cycle, if g_j and g_k differ at exactly one
position p, then j and k are adjacent (|j-k| = 1 mod CL).

STATUS: The claim is NOT universally true. Counterexamples exist at n=2
(all cases) and n=3 (when some proc doesn't visit all its states).

CORRECTED THEOREM: H-1 Uniqueness holds when:
  (A) n >= 3, AND
  (B) fc(p) = m_p for all p, AND
  (C) m_p in {2, 3} for all p (binary/ternary only), AND
  (D) gcd(m_0, ..., m_{n-1}) = 1 (automatic from B/C if both types present).

This is the EXACT setting of the LB proof (sub-threshold product with >= 3
binary and rest ternary).

PROOF:

Setup: good cycle g_0, ..., g_{CL-1} with n >= 3 procs, m_p in {2,3},
fc(p) = m_p, CL = sum(m_p).

STEP 1 (Value Coverage): Each proc p visits all m_p values exactly once.
  For m_p = 2: walk 0->1->0 visits both values.
  For m_p = 3: walk of length 3 returning to start with no consecutive
  repeats must visit all 3 values (proved by exhaustion above).

STEP 2 (Arc Segregation): Suppose g_j and g_k are Hamming-1 at position p,
  with d = (k-j) mod CL in {2, ..., CL-2}.

  For each q != p: g_j[q] = g_k[q], and q's value must return to this value
  after a_q firings in the arc j..k-1.

  Since q visits all m_q values in a single cycle of length m_q (Step 1),
  and the value sequence forms a cyclic permutation:
  q returns to its start after a_q steps in the permutation iff a_q = 0 mod m_q.
  Since 0 <= a_q <= m_q: a_q in {0, m_q}.

STEP 3 (Divisibility Contradiction):
  Let S = {q != p : a_q = m_q}. Then:
    d = a_p + sum_{q in S} m_q
    CL - d = (m_p - a_p) + sum_{q not in S, q!=p} m_q

  where 1 <= a_p <= m_p - 1 (p fires in both arcs but doesn't complete
  a full cycle in either, since g_j[p] != g_k[p]).

  Now: d and CL-d must both be positive integers >= 2.

  KEY: d mod 2 and d mod 3 analysis.

  Consider d modulo 2:
    d = a_p + sum_S m_q.
    sum_S m_q = 2 * |{binary in S}| + 3 * |{ternary in S}|
              = 2b_S + 3t_S (where b_S, t_S count binary/ternary in S).
    Similarly CL = m_p + 2B + 3T where B = total binary (excluding p),
    T = total ternary (excluding p).

  Consider d modulo 3:
    If m_p = 2: a_p in {1}. (m_p - 1 = 1.)
      d = 1 + 2b_S + 3t_S = 1 + 2b_S mod 3.
    If m_p = 3: a_p in {1, 2}.
      d = a_p + 2b_S + 3t_S = a_p + 2b_S mod 3.

  Hmm, this doesn't immediately give a contradiction either.

  Let me try a different approach for Step 3.

STEP 3 (REVISED — Direct counting):

  d = a_p + sum_{q in S} m_q. With a_p in {1, ..., m_p - 1}:

  If m_p = 2: a_p = 1.
    d = 1 + sum_S m_q. Since each m_q >= 2: d >= 1 + 2|S| if S nonempty.
    Also d <= CL - 2 (since CL-d >= 2).
    CL - d = 1 + sum_{S^c} m_q. Same structure: CL-d >= 1 + 2|S^c|.

    If S is empty: d = 1. Not in {2,...,CL-2} range. ✗
    If S^c is empty: CL-d = 1. Not in range. ✗
    If both nonempty: both d >= 3 and CL-d >= 3. OK so far.

  If m_p = 3: a_p in {1, 2}.
    d = a_p + sum_S m_q.
    If S empty: d = a_p in {1,2}. d >= 2 requires a_p = 2, giving d = 2. OK?
      CL - d = CL - 2 = (3 - 2) + sum_{all q != p} m_q = 1 + sum m_q.
      CL - 2 >= 2 requires CL >= 4, which holds for n >= 3.
      So d = 2 is possible if S is empty and a_p = 2.

      But: with S empty, NO non-p proc fires in arc 1 (steps j..k-1).
      Arc 1 has length d = 2. In these 2 steps, only p fires (a_p = 2 times).
      So: moverAt(j) = p and moverAt(j+1) = p. p fires consecutively!

      After p fires twice: p goes v -> v' -> v''. Since p is ternary (m_p=3)
      and visits all values in order: v'' = the third value != v and != v'.
      g_k[p] = v'' != v = g_j[p]. ✓ (Hamming-1.)

      For the non-p procs: they don't fire in arc 1. So at every step in arc 1,
      they are NOT privileged. moverAt(j) = p and moverAt(j+1) = p.
      At g_j: p is the unique privileged proc.
      At g_{j+1}: p is the unique privileged proc (fires again).

      Is it possible for p to be privileged at g_{j+1}?
      g_{j+1}[p] = v' (just fired from v to v'). The context is
      (g_{j+1}[p-1], v', g_{j+1}[p+1]) = (g_j[p-1], v', g_j[p+1]).
      (Neighbors unchanged since only p fired.)
      f_p(L, v', R) should != v' for p to be privileged at g_{j+1}.
      This is a condition on the transition function. It CAN hold.

      But: does this create a valid good cycle? We need to check that
      the entire cycle is self-consistent. This is a dynamical question.

  OK, the counting argument alone CANNOT prove H-1 Uniqueness.
  The counterexample at n=3 (ms=[2,2,3], all fire, gcd=2) shows that
  the arc structure CAN be realized dynamically.

  The question is: can it be realized with gcd(ms)=1 and fc=m_p?

  Let me check: can d=2 (from the case a_p=2, S empty, m_p=3) happen
  in a system with gcd(ms)=1 and fc=m_p?

  d=2, S empty: in arc 1, p fires twice (consecutively).
  In arc 2 (length CL-2): all non-p procs fire, plus p fires once.

  For gcd(ms)=1: need both binary (m=2) and ternary (m=3) procs.
  All non-p procs must fire ENTIRELY in arc 2. Arc 2 has CL-2 steps.
  Arc 2: p fires 1 time, each non-p proc fires m_q times.
  Length = 1 + sum_{q!=p} m_q = CL - m_p + 1 = CL - 2 (since m_p = 3). ✓

  This is geometrically possible. Whether the dynamics support it:
  that depends on the transition functions.

  For this to happen: p must fire twice consecutively. Both times, p is
  the unique privileged proc. No other proc is privileged at g_j and g_{j+1}.

  At g_j: only p is privileged. For no other proc to be privileged:
  every other proc q has f_q(L, S, R) = S at its current context.
  At g_{j+1}: same requirement (p fires again, changing to v', but
  neighbors unchanged). Now p's value is v', and we need f_p(L, v', R) != v'.
  Also: every other proc q still has f_q(L, S, R) = S (same contexts
  since only p changed, and q's context depends on its neighbors, not p
  directly — unless q is adjacent to p).

  For q NOT adjacent to p: same context at g_j and g_{j+1}. So if q is
  not privileged at g_j, it's also not privileged at g_{j+1}. ✓

  For q = p-1: context (g[p-2], g[p-1], g[p]). g[p] changed from v to v'.
  So q sees different R. Could become privileged!

  For q = p+1: context (g[p], g[p+1], g[p+2]). g[p] changed from v to v'.
  So q sees different L. Could become privileged!

  For p to fire twice: p-1 and p+1 must NOT become privileged when p's
  value changes from v to v'. This is a constraint on the transition functions
  at p-1 and p+1.

  For n >= 3 with binary/ternary: this constraint CAN be satisfied
  (transition function at neighbors ignores p's value for those contexts).

  But: this means p+1 is NOT privileged at g_{j+1}. Let's trace forward.
  p fires again at g_{j+1}: g_{j+2}[p] = v''. Now p has visited all 3 values.
  At g_{j+2}: who is privileged? p has value v''. Is p privileged?
  f_p(L, v'', R) = ? (context: L=g[p-1], R=g[p+1], unchanged from g_j).
  If f_p(L, v'', R) = v'': p is NOT privileged. Good — arc 1 ends.
  If f_p(L, v'', R) != v'': p IS privileged. p fires AGAIN!
  But fc(p) = 3, and p already fired twice. A third firing in arc 1
  would mean a_p = 3 = m_p, contradicting a_p <= m_p - 1.

  So: after 2 firings in arc 1, p must NOT be privileged at g_{j+2}.
  This means: f_p(L, v'', R) = v'' at that specific context. ✓

  At g_{j+2} = g_k: some other proc must be privileged (start of arc 2).
  This is possible.

  SO: the d=2 case IS dynamically realizable in principle.
  The question: does it ACTUALLY occur with gcd(ms)=1, fc=m_p, n >= 3?

  If it does: H-1 Uniqueness fails even under our "correct" conditions!
  If it doesn't: we need a PROOF that the dynamics prevent it.

  Let me check computationally for small n.
"""

from itertools import product as iprod
import random

def test_full(ms, tables):
    """Full test: fc=m_p check + H-1 check."""
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
    for _ in range(10000):
        nxt = fire(cur, good[cur])
        if nxt == start: break
        if nxt not in good: return None
        cycle.append(nxt); movers.append(good[nxt]); cur = nxt
    else: return None
    CL = len(cycle)
    fc = [movers.count(p) for p in range(n)]
    if not all(fc[p] == ms[p] for p in range(n)): return None  # not fc=m_p

    for j in range(CL):
        for k in range(j+1, CL):
            diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
            if diff == 1 and min(k-j, CL-(k-j)) > 1:
                return False, cycle, movers, j, k
    return True, cycle, movers, -1, -1

# Search for fc=m_p systems with binary+ternary at n=3,4,5
random.seed(0)
for ms_test in [[2,2,3], [2,3,3], [2,2,2,3], [2,3,3,3], [2,2,3,3],
                 [2,2,2,3,3], [2,3,3,3,3]]:
    n = len(ms_test)
    found = 0; viols = 0
    for trial in range(200000):
        tables = []
        for p in range(n):
            t = {}
            mL = ms_test[(p-1)%n]; mS = ms_test[p]; mR = ms_test[(p+1)%n]
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        t[(L,S,R)] = random.randrange(mS)
            tables.append(t)
        result = test_full(ms_test, tables)
        if result is None: continue
        ok, cycle, movers, vj, vk = result
        found += 1
        if not ok:
            viols += 1
            if viols <= 2:
                CL = len(cycle)
                p = [i for i in range(n) if cycle[vj][i] != cycle[vk][i]][0]
                print(f"VIOLATION: ms={ms_test}, CL={CL}, j={vj}, k={vk}, p={p}")
                print(f"  movers={movers}")
    print(f"ms={ms_test}: {found} fc=m_p systems, {viols} violations (200k trials)")
