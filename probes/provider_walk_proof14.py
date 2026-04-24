"""
PROOF: Binary fc=2 exists via cycle length bound.

Approach: Use the sub-threshold product to bound the cycle length.

Key fact: In a good cycle, CL <= product of state counts.
(Actually, CL = number of good configs in the cycle, which is at most product.)

With sub-threshold: product < 4 * 3^(n-2).

If all binary fc >= 4 (there are B >= 3 binary procs):
  CL = sum fc >= 4B + 2(n-B) = 2n + 2B

For the good cycle to exist: CL <= product < 4 * 3^(n-2).
So 2n + 2B <= 4 * 3^(n-2) - 1. This is easily satisfied for n >= 9 (24 << 8748).

So the counting argument ALONE doesn't give a contradiction. We need something more.

ACTUAL APPROACH: Forget sub-threshold. Use the WALK STRUCTURE directly.

The walk is on Z_n with moves +-1. Zero winding means net displacement = 0.
The cycle visits all procs (fc >= 2 for all, no safe proc).

CLAIM: In such a walk, the number of DIRECTION CHANGES (reversals) determines
the fire count distribution. A reversal at position p means the walk bounces:
..., p-1, p, p-1, ... or ..., p+1, p, p+1, ...

At a reversal at p, the walk fires p and then goes back. This contributes
an extra firing at p (beyond the minimum of 2 for a sweep-like pattern).

BETTER APPROACH: Use the fact that in a good cycle, configs are distinct.
The total number of distinct configs = CL. Configs are vectors (v_0, ..., v_{n-1})
with v_i in Z_{m_i}. At each step, exactly one coordinate changes.

The configs form a Hamiltonian path/cycle in the "transition graph" on configs.

For a BINARY proc b: its value alternates 0,1,0,1,... at each firing.
Between consecutive firings of b, b's value is constant. The run of nonmover
steps between two firings of b: all have the same b-value.

With fc(b) >= 4: b fires at steps s1 < s2 < s3 < s4 (and maybe more).
The value at s1: v, at s2: 1-v, at s3: v, at s4: 1-v.

The interval [s1, s2): b's value is v (just fired at s1, flipped to some value,
wait no -- at step s1, b is the mover, so b's value CHANGES from v to 1-v.
The config at step s1 has b=v. After step s1, config has b=1-v. So between s1
and s2, b's value is 1-v. At step s2, b fires again: changes from 1-v to v.

So:
  Before s1: b = v
  Step s1: b fires, changes to 1-v
  Between s1 and s2: b = 1-v
  Step s2: b fires, changes to v
  Between s2 and s3: b = v
  Step s3: b fires, changes to 1-v
  Between s3 and s4: b = 1-v

The config sequence has b alternating between v and 1-v at each firing.

With 4 firings of b: the intervals are [0, s1), [s1, s2), [s2, s3), [s3, s4), [s4, ...).
In a cycle, this wraps around.

The key: between s2 and s3, b = v. This is the same value as before s1.
The configs in [s2, s3) have b = v, and configs before s1 have b = v.
These configs must all be DISTINCT (good cycle). The parts where b ≠ v
use different b-values, so they're automatically distinct from b=v configs.

For entry conflict: we need a step in [s2, s3) where b is nonmover with
local context matching b's mover context at s1 (where b has value v).
At s1: b fires, b = v, context = (L(s1), v, R(s1)).
Between s2 and s3: b = v, nonmover. At each step k in (s2, s3):
  context = (L(k), v, R(k)).
  If (L(k), R(k)) = (L(s1), R(s1)): entry conflict!

So: among all nonmover appearances of b with val=v, if any matches the mover
context at s1 (or s3, which also has val=v), we get entry conflict.

The mover context at s1: (L, v, R) where L = config(s1)[left(b)], R = config(s1)[right(b)].
The mover context at s3: (L', v, R') — could be different.

For NO entry conflict: all nonmover appearances of b with val=v must avoid
both (L, R) and (L', R') pairs.

Total (L, R) pairs: m_L * m_R. With non-consecutive binary: m_L >= 3, m_R >= 3.
So at most 9 (L,R) pairs with m_L = m_R = 3.

Mover pairs with val=v: up to ceil(fc/2) pairs. With fc=4: 2 pairs.
So 2 "forbidden" (L, R) pairs out of 9+ possible.

The remaining 7+ pairs can be used for nonmover steps.
So NO entry conflict is possible if the nonmover steps at b with val=v
use different (L, R) pairs, avoiding the 2 mover pairs.

This means the counting argument doesn't work for fc=4 when neighbors are ternary.

CONCLUSION: The pigeonhole argument doesn't directly prove entry conflict
from fc(b) >= 4 when neighbors are ternary (9+ possible contexts).

NEW STRATEGY: Use the specific structure of the walk to get a STRONGER result.

The walk's structure constrains which (L, R) pairs can appear at b.
Between consecutive firings of b, the walk makes an excursion. The excursion
determines which neighbor values are "reachable." If the excursion is short
(one-sided), only nearby neighbors change, limiting the (L, R) space.

Actually, let me just try PROVING that fc(binary) = 2 ALWAYS when some fc >= 3.

The CaseObstructionsCore.lean already has: allFireCount_eq_2_of_zeroWinding
at line 350. This proves fc = 2 for ALL procs (not just binary). It uses
zeroWinding_no_fireCount_ge3 as a subroutine. And zeroWinding_no_fireCount_ge3
uses the provider.

So the CIRCULAR dependency is:
  allFireCount_eq_2 uses no_fc_ge3
  no_fc_ge3 uses provider
  provider uses passthrough
  passthrough uses exists_binary_fc2

The approach that BREAKS the circularity: prove exists_binary_fc2 DIRECTLY.

exists_binary_fc2 says: with ZW, cw > 0, fc >= 2 all, some fc >= 3, >= 3 binary,
sub-threshold, n >= 9: some binary has fc = 2.

Proof: By contradiction. Assume all binary fc >= 4.
CL >= 4*3 + 2*(n-3) = 2n + 6.

Now use the ZW STRUCTURE. CL = 2*cw (no stay steps in a clean ZW walk? not necessarily).
Actually CL = cw + ccw + stay. With ZW: cw = ccw (net = 0). So CL = 2*cw + stay.

The walk visits all n procs. Each proc fires >= 2 times.
CW steps: cw >= n (must traverse all n edges CW to visit all procs via CW direction).
Wait, that's not necessarily true. The walk could visit all procs via CCW too.

Let me approach from a different angle.

In a ZW walk, the walk goes CW sometimes and CCW sometimes. It reverses direction
at "reversal points." The number of reversals is even (since the walk starts and
ends at the same position with the same direction).

Each reversal contributes an extra firing at the reversal position. The minimum
CL with all fc = 2 is 2n (each proc fires exactly twice: once CW, once CCW).
With any fc >= 3: CL >= 2n + 1.

With all binary fc >= 4: the extra firings at binary procs add up to at least
2 per binary (fc 4 vs fc 2). Total extra: >= 2*3 = 6. CL >= 2n + 6.

Each extra firing corresponds to a reversal or stay at a binary proc. With 6+
extra firings at binary procs and 6+ at ternary (to keep some fc >= 3 at ternary),
the walk has many oscillations.

OK I think I'm going in circles. Let me take the SIMPLEST approach that works:

Prove: all binary fc even + sum fc = CL + all fc >= 2 + some fc >= 3 + B >= 3
→ some binary has fc = 2.

By contrapositive: if all binary fc >= 4:
  sum binary fc >= 4B >= 12
  sum ternary fc >= 2(n-B)
  CL = sum binary + sum ternary >= 2n + 2B >= 2n + 6

Now I need an UPPER BOUND on CL. From the ZW + sub-threshold + no safe proc.

Actually, let me check: is there a constraint from ZW + no safe proc that
gives CL = 2n? The Lean code (allFireCount_eq_2_of_zeroWinding) proves exactly
this: CL = 2n under these hypotheses. But it uses no_fc_ge3 which uses the
provider — circular.

The KEY QUESTION: can CL = 2n be proved WITHOUT the provider?

If CL = 2n, then sum fc = 2n with all fc >= 2 → all fc = 2. Done.
But proving CL = 2n is equivalent to proving all fc = 2, which is what we want.

So we can't just use CL = 2n without going through no_fc_ge3.

DIFFERENT APPROACH: Let me prove the provider exists EVEN WITHOUT fc(binary) = 2.

From my computation: the provider (with BINARY active side) exists for ALL walks
at n=5 where some fc >= 3. The only CEs are at walks where NO binary has fc=2
AND the walk has oscillation patterns. But these walks DON'T have binary provider.

Yet, the generalized provider (ternary active) DOES exist for all walks. And
the generalized provider DOES give entry conflict if the ternary proc's value
returns after 3k fires. This return IS guaranteed if the transition at each
firing is a cyclic permutation... but that's not generally true.

WAIT: there's another approach. The entry conflict at the provider doesn't
need the ACTIVE side's value to return. It needs the (L, S, R) context to
match between mover and nonmover steps at t.

For the phase [a, s):
  config(a)[left(t)] and config(s)[left(t)] need to match.
  config(a)[right(t)] and config(s)[right(t)] need to match.

For the SILENT side (say right(t)): fire count = 0, so value preserved. Match.
For the ACTIVE side (say left(t)): fire count = k.
  config(s)[left(t)] = config(a)[left(t)] after k firings.
  For binary: even k → value returns (binary parity). Match.
  For ternary: k = 3j → match NOT guaranteed (depends on transitions).

So for ternary active side, we need a DIFFERENT entry conflict argument.
It's not just value return. Let me think...

For the Toggle-FR mechanism: we need two nonmover steps at t with DISTINCT
values of the active neighbor. This gives entry conflict regardless of
whether the value returns.

In the phase [a, s) of t with left(t) ternary and firing 3 times:
  Left(t) fires at steps p1, p2, p3 in (a, s).
  At each pi: left(t) is the mover, t is nonmover.
  t's context at pi: (config(pi)[left(t)], config(pi)[t], config(pi)[right(t)]).
  Since t doesn't fire: config(pi)[t] is the same for all i.
  Since right(t) is silent: config(pi)[right(t)] is the same for all i.
  So the contexts at p1, p2, p3 differ ONLY in config(pi)[left(t)].

  With 3 firings, left(t) goes through 3 value changes. Its values at
  the 3 nonmover steps (just BEFORE each firing) are some v1, v2, v3.
  Each vi != v_{i+1} (firing changes value).

  Since left(t) is ternary (m=3): v1, v2, v3 ∈ {0, 1, 2}.
  With v1 != v2, v2 != v3: there are 3*2*2 = 12 possible sequences.
  Some have v1 = v3 (if v1 != v2 and v3 = v1: like 0,1,0).

  Now: at step s, t fires. t's mover context is:
  (config(s)[left(t)], config(s)[t], config(s)[right(t)]).
  config(s)[t] = config(a)[t] (t doesn't fire).
  config(s)[right(t)] = config(a)[right(t)] (silent side).
  config(s)[left(t)] = some value after 3 firings of left(t).

  The mover context has left(t) = v4 (value after 3rd firing).
  v4 != v3 (3rd firing changes value).

  Now: among the nonmover contexts (v1, ..., v3) and the mover context (v4):
  If v4 = v1 or v4 = v2 or v4 = v3: then the mover context matches a nonmover
  context (since t and right(t) values are the same).

  v4 != v3 is guaranteed. But v4 could equal v1 or v2.

  Actually: v1, v2, v3 ∈ {0,1,2} with consecutive different. v4 != v3.
  Can we always find vi = v4? Not necessarily.

  Example: v1=0, v2=1, v3=0, v4=1 (or 2).
  If v4=1: v4 = v2. Match!
  If v4=2: v4 != v1,v2,v3. No match.

  So there's a case where the ternary active side doesn't give entry conflict
  even with 3 firings and Toggle-FR.

  Hmm. But with 3 firings, we have 3 nonmover contexts plus 1 mover context.
  Values: v1, v2, v3 (nonmover), v4 (mover). With v_i != v_{i+1} and m=3.

  Possible sequences: v1,v2,v3,v4 where consecutive differ, all in {0,1,2}.
  The only case with no match is: all 4 values are covered, but with m=3
  and 4 values, by pigeonhole at least 2 must be equal. Since consecutive
  differ, the pattern must be 0,1,0,2 or similar.

  v1=0, v2=1, v3=0, v4=2: nonmover values {0,1,0}, mover value 2.
  Mover value 2 ≠ 0 and ≠ 1. But 0 appears twice! The nonmover values are
  {0, 1} (as a set). Mover value is 2. No match!

  So Toggle-FR FAILS here. With ternary active side and 3 firings, the mover
  value can be a "new" value not seen in nonmover contexts.

CONCLUSION: the generalized provider with ternary active side does NOT always
give entry conflict. Both the "value return" approach and the "Toggle-FR"
approach can fail.

FINAL ANSWER: We MUST prove fc(binary) = 2. The approach in the Lean code
is correct. The gap is the "exists_passthrough" sorry and the pigeonhole.

But as I showed, simple pigeonhole doesn't work for fc >= 4 binary with
ternary neighbors. We need a more sophisticated argument.

LET ME TRY THE WALK STRUCTURE ARGUMENT ONE MORE TIME.

In a ZW walk with all binary fc >= 4:
Each binary fires >= 4 times. Between consecutive firings, there's an excursion.
With fc >= 4: >= 4 excursions (cyclically).

In a ZW walk, the walk reverses direction at least twice. Each reversal creates
a bounce. At each bounce, the walk visits the bounce position and its immediate
neighbors, then reverses.

With >= 3 binary (non-consecutive), the binary procs divide the ring into >= 3
ternary arcs. Each arc has >= 1 ternary proc.

Now: the walk, being ZW, traverses arcs CW and CCW. In a CW pass through an arc
(from binary b1 to binary b2), each ternary proc in the arc fires once. In a CCW
pass, each fires once again. With additional oscillations, they fire more.

The key constraint: the TERNARY procs have m = 3, so they can fire at most...
well, there's no upper bound from m alone. But the walk structure constrains it.

Hmm, I keep going in circles. Let me just ACCEPT that proving fc(binary) = 2
is the right approach and that the pigeonhole needs additional structure from
the walk, and write a CLEAN proof of the provider existence using the walk
reversal approach, ASSUMING that fc(binary) = 2 can be proved (with the
pigeonhole sorry to be filled later).

ACTUALLY: re-reading the user's request, they want me to prove the provider
exists. The current Lean code has TWO sorrys in passthrough_excursion_oneSided:
  1. exists_passthrough (fc(binary) = 2)
  2. passthrough_provider (from fc=2 binary, construct the TernaryPhase)

Both are sorry'd. The user wants me to prove the provider exists REGARDLESS
of fc values. But my analysis shows this requires fc(binary) = 2.

So let me prove BOTH:
  A) fc(binary) = 2 exists (the "exists_passthrough" sorry)
  B) From fc=2 binary, construct the provider (the "passthrough_provider" sorry)

For (A): use the counting argument. All binary fc even (parity) and >= 2.
If no binary has fc = 2, all have fc >= 4. Sum binary fc >= 4B. CL >= 2n + 2B.

For contradiction: we need CL <= something.

INSIGHT: In a good cycle, the configs in the cycle are DISTINCT. The number of
good configs = CL. With product < 4*3^(n-2), the TOTAL number of configs is
< 4*3^(n-2). So CL < 4*3^(n-2).

But 2n + 2B with B >= 3 and n >= 9 gives 2*9 + 6 = 24, which is way less than
4*3^7 = 8748. So the sub-threshold bound is too weak.

MAYBE: use additional structural constraints to bound CL more tightly.
In a ZW good cycle with no safe proc: every edge is traversed at least once
in each direction (CW and CCW). This gives CL >= 2n.

Also: in a good cycle, the number of DISTINCT local contexts at each proc
is bounded by 2*m_L*m_R (mover + nonmover). So:
  CL = sum fc <= sum_{p} 2*m_{L(p)}*m_{R(p)} ... no that's not right either.

Actually, let me revisit. For entry conflict at binary b:
  Suppose b fires k >= 4 times. Among these k firings, ceil(k/2) have val=v
  and floor(k/2) have val=1-v.

  At each mover step of b, b is privileged: f(L,v,R) != v (for val=v firings).
  At each nonmover step of b with val=v: f(L,v,R) = v.

  So the SET of (L,R) pairs at mover steps with val=v is a subset of
  {(L,R) : f(L,v,R) != v}, and the set at nonmover steps with val=v is a subset
  of {(L,R) : f(L,v,R) = v}. These are DISJOINT.

  Number of (L,R) with f(L,v,R) != v: call it P_v (privileged contexts).
  Number of (L,R) with f(L,v,R) = v: call it Q_v = m_L*m_R - P_v.

  Mover steps at b with val=v: at most P_v.
  Nonmover steps at b with val=v: at most Q_v.
  Total steps with val=v: at most P_v + Q_v = m_L*m_R.

  The configs are globally distinct, but local contexts can repeat (same (L,v,R)
  with different values at other procs). So the local context bound doesn't
  directly limit the number of steps.

  BUT: In a good cycle, each CONFIG is distinct. The number of configs with
  b = v is at most (product / m_b) = product / 2. Among these, the number with
  b privileged is at most (product / 2) * (P_v / (m_L * m_R)) roughly. But
  this is too loose.

I think I need to abandon the counting approach and use the WALK STRUCTURE.
Let me just verify the key claim at n=9 computationally and write the proof.
"""

# Just output the analysis
print("ANALYSIS COMPLETE. Key findings:")
print()
print("1. The binary provider exists for ALL abstract walks at n=5 with fc >= 2, some fc >= 3.")
print("2. When binary fc = 2 exists (always at L = 2n+1), the binary provider follows easily.")
print("3. At larger L, walks with all binary fc >= 4 can exist as abstract walks but")
print("   may not be realizable as good cycles.")
print("4. The generalized provider (ternary active) exists for all abstract walks")
print("   but doesn't always produce entry conflict (ternary value may not return).")
print("5. The correct proof strategy: prove fc(binary) = 2 exists, then use passthrough.")
print()
print("PROOF OF fc(binary) = 2:")
print("  By contradiction. Assume all binary fc >= 4.")
print("  Binary proc b fires >= 4 times. Walk reverses at b at least twice.")
print("  Each reversal at b creates two consecutive firings in the same direction.")
print("  With 2 reversals and fc >= 4: b has 2 'excursions' on each side.")
print("  The excursions on the same side must use different neighbor configurations")
print("  (good cycle = distinct configs). With ternary neighbors: 3^2 = 9 possible (L,R).")
print("  With 2 same-side excursions per side: 2 * 2 = 4 mover contexts with val=v.")
print("  The nonmover contexts with val=v cover the remaining configs.")
print("  THIS DOESN'T directly give EC via counting.")
print()
print("ALTERNATIVE: Use ZW structure more carefully.")
print("  In a ZW walk with B >= 3 binary all with fc >= 4:")
print("  Total binary firings >= 4B >= 12. Total CW binary firings >= 6 (half by ZW).")
print("  Each binary CW firing = one CW step at the binary position.")
print("  With B >= 3 binary positions and >= 6 CW firings: some binary has >= 3 CW firings.")
print("  But a binary proc CW-fires with value alternating: v, 1-v, v at CW firings.")
print("  The CW contexts (L, v, R) with same v: at least ceil(3/2) = 2 with same val.")
print("  These 2 CW mover contexts must differ in (L,R) (else EC).")
print("  With ternary neighbors: possible, since 9 (L,R) pairs.")
print()
print("  This argument doesn't close either. The walk structure is too unconstrained")
print("  for pure counting.")
print()
print("FINAL APPROACH: Just prove it for the EXISTING walk structure in CaseObstructionsCore.lean")
print("by showing the passthrough binary always exists via the walk's arc structure.")
