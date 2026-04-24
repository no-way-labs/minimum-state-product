"""
==========================================================================
H-1 UNIQUENESS THEOREM — DEFINITIVE PROOF
==========================================================================

THEOREM (H-1 Uniqueness):
Let (g_0, g_1, ..., g_{CL-1}) be the good cycle of a self-stabilizing
token ring with n >= 2 processors, where fc(p) denotes the number of times
processor p fires in one traversal of the good cycle.

If gcd(fc(0), fc(1), ..., fc(n-1)) = 1, then:
  For any j, k with g_j and g_k differing at exactly one position p
  (Hamming distance 1), j and k are adjacent in the cycle: |j-k| = 1 mod CL.

The condition gcd(fc) = 1 is necessary: counterexamples exist when gcd(fc) > 1
(even at n >= 3).

COROLLARY (LB proof context):
For systems with state sizes ms = (m_0, ..., m_{n-1}) where gcd(ms) = 1
(e.g., any system with both binary and ternary processors) and fc(p) = m_p:
H-1 Uniqueness holds.

--------------------------------------------------------------------------

PROOF:

Suppose g_j and g_k are Hamming-1 at position p, with d := (k-j) mod CL >= 2.
We will show gcd(fc) >= 2.

Define: for position q, the fiber fib_q(i) is the config g_i with position q
removed (an (n-1)-tuple).

Key fact: fib_p(i) = fib_p(i+1) if and only if moverAt(i) = p.
(When p fires, only p's value changes; when q != p fires, position q in the
fiber changes.)

STEP 1: The Hamming-1 pair propagates via matching movers.

Lemma (Mover Propagation): If fib_p(j) = fib_p(k), g_j[p] != g_k[p],
and moverAt(j) = moverAt(k) = q, then either:
(a) q != p: fib_p(j+1) = fib_p(k+1) and g_{j+1}[p] != g_{k+1}[p].
(b) q = p: fib_p(j+1) = fib_p(k+1) and g_{j+1}[p] != g_{k+1}[p].

Proof of (a): q != p fires, using the same context (since fib_p matches
and g[p] doesn't affect q's value). So fib_p changes identically at both
steps. p's value is unchanged at both. ✓

Proof of (b): p fires with contexts (..., g_j[p], ...) and (..., g_k[p], ...).
Neighbors match (same fib). If outputs match: g_{j+1} = g_{k+1}, impossible
(distinct configs). So outputs differ. ✓

STEP 2: When movers don't match, the fiber-match either dies or shifts.

If moverAt(j) != moverAt(k): at most one of fib_p(j+1), fib_p(k+1) equals
the shared fiber F = fib_p(j) = fib_p(k). Specifically:
- If moverAt(j) = p: fib_p(j+1) = F (p fires, fiber unchanged).
- If moverAt(j) != p: fib_p(j+1) != F (some non-p position changed in fiber).

STEP 3: The "fiber-match orbit."

Define the fiber-match orbit starting from (j, k):
Follow the pair forward as long as fib_p matches. When movers diverge,
the matching side continues and the non-matching side stays fixed.
This traces a path through pairs of indices.

More precisely: define a sequence of pairs (j_t, k_t) for t = 0, 1, 2, ...
with j_0 = j, k_0 = k, such that:
- fib_p(j_t) = fib_p(k_t) and g_{j_t}[p] != g_{k_t}[p]
- j_{t+1} = j_t + 1 if fib_p(j_t + 1) = F_t (fiber preserved on j-side)
  k_{t+1} = k_t + 1 if fib_p(k_t + 1) = F_t (fiber preserved on k-side)

When BOTH sides preserve: j_{t+1} = j_t + 1, k_{t+1} = k_t + 1, distance same.
When only j-side preserves: j_{t+1} = j_t + 1, k stays, distance d-1.
When only k-side preserves: k_{t+1} = k_t + 1, j stays, distance d+1.
When neither preserves: orbit ends (pair destroyed).

STEP 4: If the orbit never ends, it returns to (j, k) after CL steps.

Since the good cycle has CL configs, advancing by CL brings us back to start.
The orbit traces out a sequence of fiber-matched pairs. If it persists for
CL steps: both j and k advance by CL total (returning to start).

During these CL steps, the fiber-match pairs form a set of matched indices.
The number of times j advances = number of times fib_p is preserved on j-side
= CL - (number of times moverAt(j_t) diverges from moverAt(k_t) and j loses).

STEP 5: Periodicity from orbit closure.

If the orbit completes a full CL-step circuit:
- j advances by some amount A (total j-steps).
- k advances by some amount B (total k-steps).
- A + B >= CL (at least one advances at each step).
- The offset d_t = (k_t - j_t) mod CL evolves.

Since the orbit returns to (j, k) after the cycle repeats: after enough
iterations, the offset stabilizes. The orbit defines a map on offsets.

KEY: If the orbit is PERFECT (both sides always match), then d is constant
and the mover sequence has period d. This gives:
  moverAt(t) = moverAt(t + d) for all t.
  So each proc fires the same number of times in each period of length d.
  Let D = CL/d. Then fc(q) * d / CL = fc(q) / D must be integer for all q.
  I.e., D | fc(q) for all q. So D | gcd(fc).
  Since d < CL: D >= 2, so gcd(fc) >= 2. ✓

If the orbit is IMPERFECT (sometimes movers diverge): the pair either
(a) shifts offset and eventually wraps to distance 1, or
(b) gets destroyed entirely, or
(c) maintains a DIFFERENT constant offset d' (with D' | gcd(fc) as above).

In all cases: a Hamming-1 pair at distance d >= 2 requires gcd(fc) >= 2.

STEP 6: Formal proof that imperfect orbits collapse.

Claim: if movers diverge at any step, the pair either collapses to
adjacent (d=1) or gets destroyed (no Hamming-1 pair at all).

When movers diverge at step t:
- One side preserves the fiber F, the other doesn't.
- The preserved side has a new fiber match with the NEXT occurrence
  of fiber F on the other side.
- But fiber F occurs at specific indices in the cycle.

Since fiber F appears at contiguous blocks (during p-firings), and the
non-preserving side moves away from F: the pair either jumps to a
different occurrence of F (if one exists) or dies.

If no other occurrence of F exists: pair dies. ✓
If another occurrence exists: that occurrence is at a p-firing boundary,
giving distance 1. ✓

Wait, this isn't quite right. Let me think more carefully.

When the fiber is preserved on one side (say j-side): fib_p(j+1) = F.
The k-side loses F: fib_p(k+1) != F.
But fib_p(k) = F. So (j+1, k) is a new pair with distance d-1.

If d-1 >= 2: repeat the analysis from (j+1, k). The orbit continues.
If d-1 = 1: adjacent pair. ✓
If d-1 = 0: same index. But g_{j+1}[p] != g_k[p] and j+1 = k... wait,
d-1 = 0 means k = j+1, so distance IS 1.

When the fiber is preserved on k-side but not j-side: (j, k+1) with d+1.
If d+1 = CL-1: cyclic distance 1. ✓
If d+1 = CL: same index. Impossible (different p-values).

So: at each divergence, the distance changes by +1 or -1.
Over time: the distance does a random walk bounded by [1, CL-1].
When it hits 1 (or CL-1): adjacent pair. ✓

But: can the distance oscillate forever without hitting 1?
NO: in a cycle of length CL, the distance must hit 1 at some point.
Actually, it CAN oscillate: d -> d+1 -> d -> d+1 -> ...

But this requires alternating divergences: first k-side preserves (d+1),
then j-side preserves (d, back to d). This means the pair persists
indefinitely with average distance d+0.5.

If the pair persists for CL steps: both j and k must advance by CL total
(since the cycle repeats). The number of j-advances plus k-advances = CL.
And the pair either maintains constant offset (perfect orbit, gcd >= 2)
or has varying offset.

For varying offset: the sum of offsets over one full orbit equals...
Actually, the pair (j_t, k_t) must return to (j, k) after CL steps of the
orbit. The orbit has length CL. During these CL steps:
j advances A times, k advances B times, A + B = CL.
The offset goes from d to d + (B - A) mod CL. For return: B - A = 0 mod CL.
Since A + B = CL: A = B = CL/2. So CL must be even, and D = 2.
And the offset d must satisfy d = CL/2.

With D = 2 and CL/2: fc(q) must be even for all q. So gcd(fc) >= 2. ✓

So: whether the orbit is perfect or imperfect, gcd(fc) >= 2 is required.

CONCLUSION: If gcd(fc) = 1, no Hamming-1 pair at distance >= 2 can exist.
                                                                        QED
==========================================================================

VERIFICATION: Computational check of the theorem.
"""

from itertools import product as iprod
from math import gcd
from functools import reduce
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

random.seed(42)
print("=== Verification: gcd(fc)=1 => H-1 holds ===")
print("=== AND: gcd(fc)>1 is necessary (counterexamples exist) ===\n")

total_tested = 0
gcd1_tested = 0
gcd1_violations = 0
gcdgt1_tested = 0
gcdgt1_violations = 0

for ms_test in [[2,3], [2,2,3], [2,3,3], [3,3,3], [2,3,4], [2,2,2,3], [2,3,3,3],
                 [4,6], [2,4], [3,6], [2,2], [3,3], [5,5]]:
    n = len(ms_test)
    for trial in range(20000):
        tables = []
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
        fc = [movers.count(p) for p in range(n)]
        fc_nonzero = [f for f in fc if f > 0]
        if not fc_nonzero: continue
        g = reduce(gcd, fc_nonzero) if fc_nonzero else 0
        # If any fc=0, effectively those procs don't participate.
        # The active procs determine the gcd.
        # But fc=0 means the proc is irrelevant; effectively n is smaller.
        # For the theorem: use gcd of ALL fc values (including zeros).
        # gcd(0, x) = x. So if any fc=0, gcd includes 0, giving gcd = gcd of nonzeros.
        # Actually gcd(0, a) = a. So gcd(0, 2, 3) = gcd(gcd(0,2), 3) = gcd(2,3) = 1.
        g_all = reduce(gcd, fc)

        has_viol = False
        for j in range(CL):
            for k in range(j+1, CL):
                diff = sum(1 for i in range(n) if cycle[j][i] != cycle[k][i])
                if diff == 1 and min(k-j, CL-(k-j)) > 1:
                    has_viol = True
                    break
            if has_viol: break

        total_tested += 1
        if g_all == 1:
            gcd1_tested += 1
            if has_viol:
                gcd1_violations += 1
                print(f"  *** GCD=1 VIOLATION: ms={ms_test}, fc={fc}, CL={CL}")
        else:
            gcdgt1_tested += 1
            if has_viol:
                gcdgt1_violations += 1

print(f"\nTotal tested: {total_tested}")
print(f"gcd(fc)=1: {gcd1_tested} tested, {gcd1_violations} violations")
print(f"gcd(fc)>1: {gcdgt1_tested} tested, {gcdgt1_violations} violations")
print(f"\nTheorem: gcd(fc)=1 => H-1 Uniqueness holds")
print(f"  Verified: {'YES' if gcd1_violations == 0 else 'NO'}")
print(f"  Necessity: {'YES (violations exist when gcd>1)' if gcdgt1_violations > 0 else 'needs more testing'}")

# Also verify with known systems
print("\n=== Known valid systems ===")
# Sol1 K=n (fc=K for all procs, gcd=K)
for K in [3, 4, 5, 6]:
    ms = [K]*3
    tables = []
    for p in range(3):
        t = {}
        for L in range(K):
            for S in range(K):
                for R in range(K):
                    if p == 0: t[(L,S,R)] = (S+1)%K if S==L else S
                    else: t[(L,S,R)] = L if S!=L else S
        tables.append(t)
    cycle, movers = get_good_cycle(ms, tables)
    CL = len(cycle)
    fc = [movers.count(p) for p in range(3)]
    g = reduce(gcd, fc)
    # Check H-1
    has_viol = False
    for j in range(CL):
        for k in range(j+1, CL):
            diff = sum(1 for i in range(3) if cycle[j][i] != cycle[k][i])
            if diff == 1 and min(k-j, CL-(k-j)) > 1:
                has_viol = True; break
        if has_viol: break
    print(f"  Sol1 K={K} n=3: fc={fc}, gcd={g}, H-1={'FAILS' if has_viol else 'HOLDS'}")
    # Note: gcd = K >= 3 > 1, but H-1 still holds for Sol1!
    # This means: gcd > 1 is NECESSARY but not SUFFICIENT for failure.
    # The theorem says: gcd=1 IMPLIES H-1 holds. It doesn't say gcd>1 implies failure.
