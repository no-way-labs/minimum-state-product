r"""
==========================================================================
H-1 UNIQUENESS THEOREM — FINAL PROOF
==========================================================================

THEOREM (H-1 Uniqueness for Coprime Systems):
Let (g_0, g_1, ..., g_{CL-1}) be the good cycle of a self-stabilizing
token ring with n >= 2 processors, state sizes (m_0, ..., m_{n-1}),
and fire counts fc(p) = m_p for all p.

If gcd(m_0, m_1, ..., m_{n-1}) = 1, then:
for all j, k with Hamming(g_j, g_k) = 1: |j - k| = 1 (mod CL).

COROLLARY: For systems with both binary (m=2) and ternary (m=3) processors:
H-1 Uniqueness holds (since gcd(2,3) = 1).

--------------------------------------------------------------------------

PROOF:

PART 1: Value Coverage Lemma.

Lemma 1: If fc(p) = m_p with m_p in {2, 3}, then proc p visits all m_p
values in the good cycle.

Proof: The value walk at p is a closed walk of length m_p with no consecutive
repeats (since each firing changes the value). For m_p = 2: the walk is
0 -> 1 -> 0, visiting both values. For m_p = 3: the walk is v_0, v_1, v_2, v_0
with v_1 != v_0, v_2 != v_1, v_0 != v_2. Since all three are distinct, all
three values {0,1,2} are visited. QED

PART 2: Arc Return Constraint.

Lemma 2: If g_j and g_k are Hamming-1 at position p (j < k, d = k-j),
and fc(q) = m_q for all q, and q visits all m_q values, then:
for each q != p, the number of times q fires in steps j..k-1 (call it a_q)
satisfies: a_q is a multiple of m_q.

Proof: Between steps j and k, q fires a_q times. Since g_j[q] = g_k[q]
(Hamming-1 at p means they agree at all non-p positions): q returns to
its starting value after a_q firings.

Now: q's value walk in the full cycle visits all m_q values exactly once
(by Lemma 1 + fc(q) = m_q), forming a Hamiltonian cycle on {0,...,m_q-1}.
Crucially, this means each value of q appears at exactly one "phase" of q.

Wait — the value walk IS context-dependent. Different firings from the same
value can go to different targets. So the walk is NOT a simple permutation.

However: for m_q in {2,3}, the walk MUST be a permutation cycle (as shown
in Lemma 1). For m_q = 2: always 0->1->0. For m_q = 3: always a 3-cycle.
So the value transitions form a FIXED cyclic permutation.

ACTUALLY: No! The transition at step i is f_q(L_i, S_i, R_i), and L_i, R_i
change at each step. So q could fire from value 0 to value 1 at one step,
and from value 0 to value 2 at another step (with different context).

But: fc(q) = m_q = 3 means q fires exactly 3 times, and the walk is
v_0 -> v_1 -> v_2 -> v_0. Each v is distinct (Lemma 1). So:
v_0 is visited once, v_1 once, v_2 once. The walk IS a permutation cycle
(though the TRANSITION that produces it depends on context).

The key point: q visits each value exactly once. So: the value at q
uniquely determines "where we are" in q's firing cycle.

If q returns to v_0 after a_q firings: q has traversed a_q steps in
its permutation cycle of length m_q. For a cyclic permutation of length m_q,
returning to start after a_q steps requires a_q = 0 (mod m_q). QED

PART 3: Divisibility Constraint.

From Lemma 2: for each q != p, a_q = 0 (mod m_q).
Since a_q + b_q = m_q (total = m_q): a_q in {0, m_q}.
(The only multiples of m_q in [0, m_q] are 0 and m_q.)

So: each non-p proc fires ENTIRELY in one arc or the other.

Let S = {q != p : a_q = m_q} (procs that fire entirely in the first arc).
First arc length: d = a_p + sum_{q in S} m_q.
Second arc length: CL - d = (m_p - a_p) + sum_{q not in S, q!=p} m_q.

PART 4: Period of the Mover Sequence.

The mover sequence has CL entries. Consider it as a cyclic sequence.
The Hamming-1 pair at distance d means: at every step t, the configs
g_t and g_{t+d} agree on all non-p positions.

Wait — this is the "propagation" argument, which doesn't work when
the pair doesn't propagate. Let me use the arc argument instead.

From Part 3: each non-p proc fires entirely in one arc. This means:
in the first arc (steps j..k-1), only p and procs in S fire.
In the second arc (steps k..j+CL-1), only p and procs NOT in S fire.

Now: CL = d + (CL - d). And:
d = a_p + sum_{q in S} m_q.
CL - d = (m_p - a_p) + sum_{q not in S, q != p} m_q.

sum_{q in S} m_q + sum_{q not in S, q != p} m_q = sum_{q != p} m_q = CL - m_p.

So: d + (CL - d) = m_p + (CL - m_p) = CL. ✓ (Consistent.)

PART 5: Deriving the GCD Constraint.

Consider the multiset of movers in the first arc. It contains:
- Proc p: a_p times.
- Each q in S: m_q times.
Total: a_p + sum_{q in S} m_q = d.

Consider the multiset of movers in the second arc. It contains:
- Proc p: m_p - a_p times.
- Each q not in S: m_q times.
Total: (m_p - a_p) + sum_{q not in S, q != p} m_q = CL - d.

Now: the mover at step j is some proc. The mover at step j+d = k is
some other proc. These can be different. The "split" of procs into
S and its complement constrains the mover sequence.

KEY: The first arc and second arc have DISJOINT non-p proc sets.
Proc q in S fires only in the first arc. Proc q not in S fires only
in the second arc.

So: the mover sequence restricted to non-p procs has support S in arc 1
and support complement(S) in arc 2.

Now: consider the cyclic mover sequence. After CL steps, it repeats.
The "arc split" means: the mover sequence has a specific structure
where non-p procs segregate into two arcs.

For d | CL: if we split the cycle into D = CL/d equal parts, each part
would need to contain m_q/D firings of q. But our split has unequal
distribution (all of q's firings in one part).

For this to be consistent: if q is in S (all firings in first arc of length d):
q fires m_q times in d steps. The density of q-firings in arc 1 is m_q/d.
In arc 2: 0 firings.

Now: d = a_p + sum_{q in S} m_q. And a_p >= 1, a_p <= m_p - 1
(p fires a_p times in arc 1 and returns, but p's value changes, so
0 < a_p < m_p — actually we need a_p != 0 and a_p != m_p since p must
fire in both arcs to change from g_j[p] to g_k[p] and back).

Wait: does p fire in both arcs? In arc 1, p fires a_p times, going from
g_j[p] = v to g_k[p] = w (different values). In arc 2, p fires m_p - a_p
times, going from w back to v. So yes: a_p >= 1 and m_p - a_p >= 1.

Now: CL = sum(m_q). d = a_p + sum_{q in S} m_q.

Claim: d = CL * |some fraction|, and gcd(m_0,...,m_{n-1}) | CL/D.

Actually: let me compute d mod gcd.
Let G = gcd(m_0, ..., m_{n-1}).
Each m_q is a multiple of G. So:
CL = sum(m_q) is a multiple of G (if... wait, sum of multiples of G
is a multiple of G only if n*G | ... no. sum of multiples of G IS a
multiple of G. CL = n*G*... no. m_q = G * k_q. CL = G * sum(k_q).)
So CL is a multiple of G.

d = a_p + sum_{q in S} m_q = a_p + G * sum_{q in S} k_q.
CL - d = (m_p - a_p) + G * sum_{q not in S, q!=p} k_q.

d = a_p + G * (sum of some k's).
CL - d = (m_p - a_p) + G * (sum of other k's).

d + (CL - d) = m_p + G * (sum all k's except k_p) = m_p + CL - m_p = CL. ✓

Now: a_p is between 1 and m_p - 1. And m_p = G * k_p.
d mod G = a_p mod G.
CL - d mod G = (m_p - a_p) mod G = (G*k_p - a_p) mod G = (-a_p) mod G.

For d and CL-d to be well-defined arc lengths, we need 2 <= d <= CL-2.

If G = 1: a_p mod 1 = 0 always. d mod 1 = 0. This gives no constraint.

So: the GCD argument alone doesn't work to get a contradiction. I was wrong.

Hmm. Let me reconsider.

THE KEY ISSUE: Parts 1-4 don't actually lead to gcd(fc) > 1. They
describe the arc structure but don't derive a contradiction.

The arc structure says: non-p procs segregate into two arcs.
This IS possible. The question is whether the DYNAMICS support it.

Let me reconsider whether the "a_q = 0 or m_q" conclusion is actually
correct for the n=3 counterexample.
"""

# Check the n=3 counterexample arc structure
print("=== Arc structure for n=3 counterexample ===")
cycle = [(0,0,0), (1,0,0), (1,1,0), (1,1,1), (0,1,1), (0,1,0)]
movers = [0, 1, 2, 0, 2, 1]
CL = 6
n = 3
# Violation: j=2, k=5, p=0, d=3
j, k, p = 2, 5, 0

# First arc: steps 2, 3, 4 (movers 2, 0, 2)
arc1_movers = [movers[i] for i in range(j, k)]
# Second arc: steps 5, 0, 1 (movers 1, 0, 1)
arc2_movers = [movers[i % CL] for i in range(k, j + CL)]

print(f"Arc 1 (steps {j}..{k-1}): movers = {arc1_movers}")
print(f"Arc 2 (steps {k}..{j+CL-1}): movers = {arc2_movers}")

# Fire counts per arc
for q in range(n):
    a1 = arc1_movers.count(q)
    a2 = arc2_movers.count(q)
    print(f"  Proc {q}: arc1={a1}, arc2={a2}, total={a1+a2}, m_q=?")
    # Check: does q return in arc 1?
    val_start = cycle[j][q]
    val_end = cycle[k][q]
    print(f"    value at start of arc1 (g_j): {val_start}")
    print(f"    value at end of arc1 (g_k): {val_end}")
    if q != p:
        assert val_start == val_end, f"Non-p proc {q} doesn't return!"
        print(f"    Returns: YES")
    else:
        print(f"    Differs (p): {val_start} -> {val_end}")

# So: proc 0 (p): fires 1 time in arc1, 1 time in arc2 (a_p=1)
# proc 1: fires 0 times in arc1, 2 times in arc2 (a_1=0)
# proc 2: fires 2 times in arc1, 0 times in arc2 (a_2=2)
# ms = [2, 2, 3]. fc = [2, 2, 2].
# For proc 1: a_1 = 0 = 0 * m_1. Consistent (0 is multiple of m_1=2). ✓
# For proc 2: a_2 = 2. m_2 = 3. 2 is NOT a multiple of 3! VIOLATION of Lemma 2!

# But proc 2 returns to its start after 2 firings!
# How? Let me check the value walk at proc 2:
print("\nProc 2 value walk:")
for i in range(CL):
    print(f"  [{i}] g[2]={cycle[i][2]} mover={movers[i]}")

# g[2]: 0, 0, 0, 1, 1, 0. Proc 2 fires at steps 2 and 4.
# Value: 0 -> 1 (step 2), 1 -> 0 (step 4). Returns to 0 after 2 firings.
# But m_2 = 3. fc(2) = 2 != m_2 = 3.
# The value cycle at proc 2 has length 2, not 3.
# So Lemma 2 applies with the VALUE CYCLE LENGTH, not m_q!

# The value cycle length at proc 2 is 2 (visits 0 and 1 only).
# With value cycle length 2: a_2 = 2 is a multiple of 2. ✓

# So: Lemma 2 should use the VALUE CYCLE LENGTH, not m_q.
# When fc(q) = m_q AND m_q in {2,3}: value cycle length = m_q (Lemma 1).
# So for binary/ternary with fc=m_q: Lemma 2 gives a_q = 0 or m_q.

# The n=3 counterexample has fc(2) = 2 != m_2 = 3, so Lemma 1 doesn't apply.
# Value cycle length at proc 2 is 2 (not 3). So a_2 = 2 = 1 * 2 works.

print("\n=== CONCLUSION ===")
print("Lemma 2 (corrected): a_q must be a multiple of the VALUE CYCLE LENGTH v_q.")
print("When fc(q) = m_q and m_q in {2,3}: v_q = m_q. So a_q in {0, m_q}.")
print("This gives the GCD constraint: d = a_p + sum_S m_q with a_p in {1,...,m_p-1}.")
print()
print("For gcd(m_q) = 1 with m_q in {2,3}:")
print("  The non-p procs split: S has some binary and ternary, complement has rest.")
print("  d = a_p + 2*|binary in S| + 3*|ternary in S|")
print("  CL - d = (m_p - a_p) + 2*|binary not in S| + 3*|ternary not in S|")
print("  Need: d >= 2 and CL - d >= 2.")
print()
print("  For this to be consistent with ALL configs: the dynamics must support")
print("  the segregation of procs into two arcs. This is a NECESSARY condition.")
print("  The question is whether it's also sufficient for the pair to exist.")
print()
print("  The segregation means: in arc 1, procs in S fire ALL their m_q times.")
print("  The arc 1 has length d. The config at each step in arc 1 must have")
print("  exactly one privileged proc (unique privilege). The only procs that CAN")
print("  be privileged are p and procs in S (since complement procs don't fire).")
print()
print("  Complement procs don't fire in arc 1 means: at every step in arc 1,")
print("  each complement proc q is NOT privileged. This constrains the transition")
print("  functions. It's POSSIBLE in principle but very restrictive.")
print()
print("  The key: with gcd(ms) = 1 (binary + ternary), and fc = m_p for all p,")
print("  the arc-segregation creates a divisibility constraint:")
print("  a_p + sum_S m_q = d and a_p + sum_complement m_q = CL - d.")
print("  Hmm, this doesn't directly give gcd > 1...")

# Actually, let me reconsider the proof strategy.
# The key is NOT that the arc-segregation is impossible,
# but that the PERIODICITY of the mover sequence is forced.

# Wait, I already showed (in the counterexample) that the pair
# does NOT propagate — it's destroyed after 1 step. So the propagation
# argument gives nothing.

# The arc-segregation IS the right approach, but I need a different
# way to derive a contradiction.

# Let me think about it as a COMBINATORIAL constraint.
# In the good cycle with CL = sum(m_p), the fiber at position p
# has at most CL - m_p distinct values (since p-firings don't change fiber).
# For a non-adjacent Hamming-1 pair: the fiber repeats at a non-adjacent index.
# The number of distinct fibers is CL - m_p = sum_{q!=p} m_q.
# The fiber space has size prod_{q!=p} m_q.
# For the fiber to be injective: sum_{q!=p} m_q <= prod_{q!=p} m_q.
# This holds (and is strict) for n >= 3 and m_q >= 2.
# But injection isn't guaranteed.

# However: the arc-segregation gives additional structure.
# In each arc, only a SUBSET of procs change their values in the fiber.
# In arc 1: procs in S change, complement procs stay fixed.
# In arc 2: complement procs change, S procs stay fixed.
# The fiber must start and end at the same point in each arc
# (same fiber at j and k).

# In arc 1: the fiber changes at coordinates in S, starting from F
# and returning to F. But only S-coordinates change, so:
# F_S (the S-coordinates of F) must return to themselves after all
# S-procs fire m_q times each.
# And F_complement stays fixed throughout arc 1.

# Similarly in arc 2: F_complement returns after complement procs fire,
# and F_S stays fixed.

# So: the arc-segregation means:
# In the S-subspace of the fiber: the S-procs form a "closed walk"
# that starts and ends at F_S. This walk has length sum_{q in S} m_q + a_p
# but only S-procs change the S-subspace.

# Wait, p also fires in arc 1, but p is NOT in the fiber. So:
# p's firings in arc 1 don't directly affect the fiber. But they affect
# the CONTEXT of S-procs (since p-1 and p+1 see p's changing value).

# Hmm, this is getting complicated. Let me just state the theorem
# with the correct conditions and verify it thoroughly.
