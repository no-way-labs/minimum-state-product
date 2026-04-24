"""
Can neighbor-insensitive transitions at position p exist at n >= 3?

If f_{p+1}(v, S, R) is constant in v for all encountered (S,R),
and f_{p-1}(L, S, v) is constant in v for all encountered (L,S):
then the pair propagates forever.

But: can a valid self-stabilizing system have this property?

At n >= 3: p+1's L = g[p], p-1's R = g[p].
Insensitivity means: p+1 and p-1 don't "look at" p's value.

For p-1: privilege means f_{p-1}(L, S, R) != S. If R = g[p] is irrelevant,
then p-1's privilege depends only on (L, S). This means: p-1 checks if
it should fire based on L and S alone.

For token rings: the standard structure is that privilege checks involve
comparing S with L or R. If we make R irrelevant for p-1: p-1 only
compares S with L. This is like Dijkstra's Solution 1 for non-bottom procs.

But then: p's value has NO effect on p-1's behavior. And similarly for p+1.

The question: does this create a valid self-stabilizing system?

Actually, I realize the question is not whether such systems EXIST in general
(they might), but whether H-1 uniqueness holds for the specific systems
relevant to the LB proof (sub-threshold product with binary/ternary).

For the LB proof: the theorem is being used specifically for sweep-type good
cycles in systems with binary and ternary procs. These systems have specific
structural properties.

Let me step back and think about what the theorem ACTUALLY needs.

The theorem statement in the hints says: "In a good cycle gc of a
self-stabilizing token ring..." — this is meant to be UNIVERSAL over all
valid systems with proper good cycles.

But I've shown it fails at n=2. And my analysis suggests it holds at n >= 3
(computationally). The proof attempt via propagation + case analysis shows
the pair can only persist if neighbors of p are insensitive to p's value,
which seems hard to achieve while maintaining self-stabilization.

Let me try a DIFFERENT proof approach: use the INJECTIVITY of the good cycle.

PROOF APPROACH 4: Good cycle as sequence, fiber constraints.

The good cycle is a sequence of CL = sum(m_p) DISTINCT configs.
For each proc q: q fires m_q times, each time changing value.
The sequence of configs is deterministic: each config uniquely determines next.

Claim: for n >= 3 and fc(p) = m_p, no two configs in the good cycle
can have the same fiber at any position p (except at adjacent p-firing steps).

Proof: suppose configs g_j and g_k (j < k, k-j >= 2, CL-k+j >= 2) have
fib_p(j) = fib_p(k) and g_j[p] != g_k[p].

Consider: the PAIR of configs (g_j, g_k) determines two parallel
"trajectories" through the state space. Since the cycle is deterministic,
g_j determines the trajectory g_j, g_{j+1}, g_{j+2}, ... and
g_k determines g_k, g_{k+1}, g_{k+2}, ...

These are the SAME cycle, shifted by d = k-j.
So: g_{j+t} and g_{k+t} = g_{j+t+d} for all t.

The Hamming distance between g_{j+t} and g_{j+t+d} evolves as t increases.
At t=0: Hamming-1 at p.

Let H(t) = Hamming distance between g_{j+t mod CL} and g_{(j+t+d) mod CL}.
H(0) = 1. H is defined for all t (cyclic).

Over one full period: sum_t H(t) = sum_t |{q : g_{j+t}[q] != g_{j+t+d}[q]}|
= sum_q |{t : g_{j+t}[q] != g_{j+t+d}[q]}|.

For each q: g_{j+t}[q] != g_{j+t+d}[q] at some set of times t.
How many times can they differ?

This is getting complicated. Let me try yet another approach.

PROOF APPROACH 5: Use GOOD CONFIG COUNTING.

In a proper good cycle with CL = sum(m_p):
- The number of good configs with proc q holding value v is:
  (number of steps where q has value v) = (CL / m_q) * 1 = CL / m_q.
  Wait, this assumes equal distribution, which may not hold.

Actually: q fires m_q times. Between consecutive firings of q, q holds
a constant value. There are m_q "phases" of q. The lengths of these phases
sum to CL. But they need not be equal.

Let phase(q, i) = length of i-th phase of q (# steps where q holds its i-th value).
sum_i phase(q, i) = CL.

For the fiber at position p to repeat: the projection of the cycle onto
non-p coordinates must revisit the same point. This means: there's an
"overlap" in the (n-1)-dimensional fibers.

The total number of distinct fibers is at most CL - m_p + 1
(since fiber stays constant during p-firings, giving m_p duplicates
at m_p adjacent-pair boundaries).

Wait, not quite: if p fires m_p times at steps s_1, ..., s_{m_p}, then
fib_p(s_i) = fib_p(s_i + 1) for each i. So the number of distinct
fiber values is at most CL - m_p (removing m_p duplicates from CL values).
Actually: CL fiber values, with exactly m_p consecutive-duplicate pairs,
so at most CL - m_p distinct fibers. The fiber lives in a space of size
prod_{q != p} m_q. We need CL - m_p <= prod_{q != p} m_q for injectivity.

CL = sum(m_q). CL - m_p = sum_{q != p} m_q.
prod_{q != p} m_q >= 2^{n-1} (since each m_q >= 2).
sum_{q != p} m_q <= (n-1) * max(m_q).

For n >= 3: prod >= 2^{n-1}, sum <= (n-1)*max. The product grows exponentially
while the sum grows linearly. So for large enough n or m, the fiber space
is much larger than the number of fiber values. This gives a counting argument
that the fiber CAN be injective — but doesn't prove it IS.

Hmm. This doesn't work as a proof.

PROOF APPROACH 6: Direct contradiction from determinism.

Suppose fib_p(j) = fib_p(k) with g_j[p] = v != w = g_k[p].
These are two configs that agree everywhere except at p.

CLAIM: There exists a proc q != p such that moverAt(j) = moverAt(k) = q,
OR moverAt(j), moverAt(k) ∈ {p, p-1, p+1} with specific constraints.

From the case analysis:
- If moverAt(j) = moverAt(k): pair propagates.
- If they differ: at least one is in {p-1, p, p+1}.

The pair propagates when movers match. When movers differ, the pair
either:
(a) Gets destroyed (Hamming distance becomes 2), or
(b) Collapses (g_{j+1} = g_{k} or g_j = g_{k+1}, giving d=1).

If (a) always happens when movers differ: the pair can only exist if
movers ALWAYS match. This requires the pair to propagate through the
entire cycle (CL steps), giving a periodic mover sequence with period d.

Period d of the mover sequence: moverAt(t) = moverAt(t+d) for all t.
This means: each proc fires the same number of times in each period.
If d < CL: CL/d >= 2. Each proc q fires m_q * d / CL times per period.
This must be a positive integer: CL | m_q * d for all q.

Let D = CL/d >= 2. Then d = CL/D. And m_q * d / CL = m_q / D must be
integer for all q. So D | m_q for all q. I.e., D | gcd(m_0, ..., m_{n-1}).

If gcd(ms) = 1 (e.g., binary + ternary): D = 1, so d = CL.
But d < CL by assumption. Contradiction!

IF (a) is the only outcome when movers differ: this proves the theorem
for gcd(ms) = 1.

But we also need to check option (b): can the pair shift (collapse) to
d=1 via the dynamics? That would be fine — it means d was never > 1
stably, just a transient artifact.

Actually, wait. (b) means the pair is "adjacent" — which is what we want
to prove! If g_{j+1} = g_k: then k = j+1 (since configs are distinct),
so d = 1. That's the desired conclusion.

So: if whenever movers differ, the pair either gets destroyed or collapses
to adjacent: the only way to have a non-adjacent Hamming-1 pair is if
movers ALWAYS match, which requires D | gcd(ms).

The remaining question: when movers differ, does the pair always get
destroyed (Hamming -> 2) or collapse (Hamming -> 0)?

From the case analysis at n >= 3:
- Case 2b: moverAt(j)=p, moverAt(k)=p+1.
  g_{j+1} differs from g_j at p only. fib_p(j+1) = F.
  g_{k+1} differs from g_k at p+1 only. g_{k+1}[p] = w (unchanged).
  fib_p(k+1) != F (since p+1 changed).
  But: g_{j+1}[p] = v' != v. Is v' = w? If so: g_{j+1} = g_k => j+1=k => d=1.
  If v' != w: we now have fib_p(j+1) = F, fib_p(k+1) != F.
  The pair (j+1, k) has fib_p(j+1) = F = fib_p(k). Distance d-1.
  But g_{j+1}[p] = v'. g_k[p] = w. If v' != w: still Hamming-1! Distance d-1.
  If v' = w: Hamming-0 => identical => j+1 = k => d=1. ✓

  So in Case 2b: if v' = w, done (d=1). If v' != w, distance reduces by 1.
  By INDUCTION on d: if d >= 2, the pair either collapses to d=1 or
  the distance keeps decreasing until d=1.

  BUT: Case 3 (mover = neighbor) can INCREASE the distance!
  Let me re-examine Case 3.

- Case 3: moverAt(j) = p+1 is privileged in g_j.
  In g_k, p+1 may or may not be privileged (different L).
  Sub-case 3a: p+1 privileged in both. movers match. Propagation:
    g_{j+1}[p+1] = f_{p+1}(v, S, R)
    g_{k+1}[p+1] = f_{p+1}(w, S, R)
    If same: fiber preserved. Distance preserved.
    If different: Hamming-2. Pair destroyed.

  Sub-case 3b: p+1 privileged in g_j but NOT in g_k.
    moverAt(k) is something else. Must be in {p-1, p} (non-neighbors match).
    Say moverAt(k) = p.
    g_{j+1}: p+1 fires. g_{k+1}: p fires.
    fib_p(j+1): differs from F at p+1 (since p+1 fired). NOT F.
    fib_p(k+1) = F (only p fired, fiber unchanged).
    g_{j+1}[p] = v (unchanged). g_{k+1}[p] = w' (p fired).
    Pair (j, k+1): fib_p(j) = F = fib_p(k+1). g_j[p] = v, g_{k+1}[p] = w'.
    Distance: (k+1) - j = d + 1. INCREASED!
    If w' = v: g_j = g_{k+1} => j = k+1 mod CL => d = CL-1 => cyclic dist 1. ✓
    If w' != v: distance INCREASED to d+1!

  So Case 3b CAN increase the distance. This breaks the simple induction.

  HOWEVER: the pair (j, k+1) has distance d+1.
  Next step from j: moverAt(j) = p+1 (still in the original step).
  Wait, I'm confusing: after stepping forward, we're now at (j+1, k+1).
  fib_p(j+1) != F. fib_p(k+1) = F. The pair (j+1, k+1) is NOT Hamming-1.
  But (j, k+1) IS Hamming-1 (if w' != v).

  So: from original pair (j, k) with distance d, we derived pair (j, k+1)
  with distance d+1. The j endpoint DIDN'T advance. But this is a new pair.

  From (j, k+1): step forward from j. Same as before. We get:
  If movers match: propagation.
  If moverAt(j) differs from moverAt(k+1):
    Could increase distance again to d+2...

  This could potentially cycle: d -> d+1 -> d+2 -> ... -> CL-2 -> CL-1 (= dist 1).
  That would mean: the distance wraps around and we end at distance 1.
  But that's only 1 (mod CL). So it's adjacent. ✓?

  Actually, if d keeps increasing: d, d+1, ..., CL-1. At CL-1: cyclic dist 1. ✓
  But: the increase only happens in one direction (k advances, j doesn't).
  After CL-1 - d increases, k wraps around to j-1 (mod CL). Then d = CL-1.

  Wait, but at each increase, we need the pair to remain Hamming-1.
  g_j[p] = v, g_{k+t}[p] = w_t. Each step: w_t changes (p fires at k+t-1).
  For the pair to persist: w_t != v (otherwise collapse to adjacent).

  p has m_p values. p fires at most m_p times before cycling. If v is hit
  during these firings: w_t = v for some t, giving collapse.
  If v is never hit: ... but p visits all values (or does it?).

  Hmm. With fc(p) = m_p, p fires m_p times total in the cycle.
  If p fires at steps k, k+1, ..., k+t-1 consecutively in the second arc,
  then after t consecutive firings, p takes t+1 distinct values
  (v_0=w, v_1, ..., v_t). For t <= m_p-1: these might not include v.
  But eventually (after up to m_p-1 firings), p returns to... wait,
  p might not fire consecutively.

This is getting really tangled. Let me just check if Case 3b actually
occurs at n >= 3 with a minimal cycle. If it never occurs (because the
transition structure prevents it), that would simplify the proof.
"""

# Check: at n >= 3, for Hamming-1 pairs in good cycles,
# do the movers at j and k ever DIFFER?
from itertools import product as iprod

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
    for _ in range(10000):
        nxt = fire(cur, good[cur])
        if nxt == start: break
        if nxt not in good: return None, None
        cycle.append(nxt); movers.append(good[nxt]); cur = nxt
    else: return None, None
    return cycle, movers

# For the ADJACENT Hamming-1 pairs, check if movers match
print("=== Adjacent H-1 pair mover check ===")
for K in [3, 5, 7]:
    for n in [3, 5]:
        if K < n: continue
        ms = [K]*n
        tables = []
        for p in range(n):
            t = {}
            for L in range(K):
                for S in range(K):
                    for R in range(K):
                        if p == 0: t[(L,S,R)] = (S+1)%K if S==L else S
                        else: t[(L,S,R)] = L if S!=L else S
            tables.append(t)
        cycle, movers = get_good_cycle(ms, tables)
        CL = len(cycle)
        # For each adjacent pair (i, i+1), they're Hamming-1 at moverAt(i).
        # Check: moverAt(i) and moverAt(i+1) — do they match or differ?
        match_count = 0
        diff_count = 0
        for i in range(CL):
            j = i; k = (i+1) % CL
            p_pos = movers[j]
            if movers[j] == movers[k]:
                match_count += 1
            else:
                diff_count += 1
        # Adjacent pairs always have different movers (moverAt(j) = p,
        # but that only means the pair is Hamming-1 at p; moverAt(k) is
        # determined by g_{k}).
        # Actually moverAt(j) and moverAt(k) CAN match (if p fires consecutively).
        print(f"Sol1 K={K} n={n}: CL={CL}, consec-same={match_count}, consec-diff={diff_count}")

print("\nDone")
