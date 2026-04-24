#!/usr/bin/env python3
"""
LAYER 2 PROOF: Binary-context pigeonhole argument.

SETUP: Sandwiched ternary t with m(t)=3, left/right neighbors binary (m=2).
Context space at t: L in {0,1}, R in {0,1}, S in {0,1,2}. Total = 12 contexts.

Each context (L, S, R) appears at most once in the good cycle (distinctness).
So at most 12 steps have distinct boundary triples at t.

Among those 12 contexts:
- 3 are mover contexts (one per S-level, when t fires).
- At most 9 are nonmover contexts.

For EC-freedom at t: at each S-level, mover (L,R) != any nonmover (L,R).
With only 4 possible (L,R) pairs per S-level: mover claims 1, leaving 3 for nonmover.

KEY CONSTRAINT: the binary neighbors toggle (m=2), so as we trace through
the cycle, L alternates 0->1->0->1... with each bL firing.

WITHIN A PHASE (between consecutive t-fires):
  The S-level is constant (say v). The binary neighbors fire J and K times.
  The (L,R) context evolves: each bL firing toggles L, each bR firing toggles R.

  Starting at (L0, R0) after the t-fire that set S=v:
  After the phase's J left-fires and K right-fires:
    L ends at (L0 + J) mod 2
    R ends at (R0 + K) mod 2

  The mover context at the END of the phase (when t fires next) is
  ((L0 + J) mod 2, v, (R0 + K) mod 2).

The key: with normalForm phases, J and K have specific parities.
(1,0): J odd, K even => L toggles, R stays. Mover L-parity = 1-L0.
(0,1): J even, K odd => L stays, R toggles. Mover R-parity = 1-R0.
(1,1): J odd, K odd => both toggle. Mover = (1-L0, 1-R0).
(2,1): J even, K odd => L stays, R toggles.
(1,2): J odd, K even => L toggles, R stays.

Let me trace the mover pair evolution around the full cycle (3 phases).

Phase 0: S=0->1. Start: (L0, 0, R0). After J0 L-fires, K0 R-fires:
  mover pair = ((L0 + J0) mod 2, (R0 + K0) mod 2)
  Next S = 1.
Phase 1: S=1->2. Start: ((L0+J0)%2, 1, (R0+K0)%2). After J1, K1:
  mover pair = ((L0 + J0 + J1) mod 2, (R0 + K0 + K1) mod 2)
Phase 2: S=2->0. Start after J0+J1 L-fires, K0+K1 R-fires.
  mover pair = ((L0 + J0 + J1 + J2) mod 2, (R0 + K0 + K1 + K2) mod 2)

CLOSURE: after all 3 phases, must return to start => L0 + J_total = L0 (mod 2)
  => J_total = J0+J1+J2 must be even (fc(bL) is even for binary).
  Similarly K_total must be even.

MOVER PAIRS (mod 2 parities):
  Phase 0 mover: (L0 + J0, R0 + K0) mod 2
  Phase 1 mover: (L0 + J0 + J1, R0 + K0 + K1) mod 2
  Phase 2 mover: (L0 + J_total, R0 + K_total) = (L0, R0) mod 2

So the phase 2 mover has the SAME (L,R) parity as the initial context!

Phase 0 mover: (L0 + J0, R0 + K0) mod 2
Phase 1 mover: (L0 + J0 + J1, R0 + K0 + K1) mod 2
Phase 2 mover: (L0, R0) = initial pair

Now, the initial context (L0, 0, R0) is a NONMOVER at S=0 (it's the step
right after the phase-2 t-fire, which transitions to S=0). Actually wait:
the step right after a t-fire is the FIRST step of the NEXT phase. The t-fire
at the end of phase 2 transitions the system to S=0. The next step (first of
phase 0) sees config with S=0 and (L,R) = (L0, R0).

So at S=0: (L0, R0) is a nonmover pair.
Phase 0 mover at S=0: also (L0 + J0, R0 + K0) mod 2.

Wait, the mover at phase 0 is the t-fire at the END of phase 0, when S=0
(S transitions 0->1). The mover context is the config WHEN t fires, which has
S=0. So:
  Phase 0 mover S-level: 0. Mover pair: ((L0 + J0) mod 2, (R0 + K0) mod 2).
  Phase 1 mover S-level: 1. Mover pair: ((L0+J0+J1) mod 2, (R0+K0+K1) mod 2).
  Phase 2 mover S-level: 2. Mover pair: (L0, R0).

At S=0, the nonmover contexts include the step right after phase 2's t-fire,
which has (L,R) = (L0, R0). (This is the first nonmover step of phase 0.)

So at S=0: mover pair = (L0+J0, R0+K0) mod 2.
  For EC-freedom: (L0+J0, R0+K0) != (L0, R0) mod 2.
  => (J0, K0) != (0, 0) mod 2 => not both J0 and K0 even.
  This is exactly the BothEven constraint! Since normalForm excludes BothEven,
  we get (J0, K0) mod 2 != (0, 0), so the mover pair != nonmover pair (L0, R0).

But the nonmover set at S=0 has OTHER pairs too!
The nonmover set at S=0 includes ALL steps where c[t]=0 and the mover is not t.
As bL and bR fire during phase 0, the (L,R) pair evolves.
With J0 L-fires and K0 R-fires, the walk visits intermediate (L,R) values.

The WALK at S=0: starts at (L0, R0), then bL/bR fires interleave, creating
a sequence of (L,R) values: each bL firing toggles L, each bR firing toggles R.

The walk visits J0+K0+1 (L,R) values (including start).
But the walk on {0,1}^2 can only visit 4 distinct values.

IF J0+K0+1 > 4: some (L,R) pair appears at both a mover step and a nonmover step.
But the mover is only 1 step (the t-fire). The walk visits intermediate values
as nonmover steps.

Actually, the (L,R) walk during phase 0 at S=0:
  Start: (L0, R0). This is a nonmover context.
  Then J0 bL-fires and K0 bR-fires happen, each toggling L or R.
  End: ((L0+J0)%2, (R0+K0)%2). This is the mover context (t fires here).

  The walk is a path on {0,1}^2 of length J0+K0.
  Each step toggles exactly one coordinate.

  Nonmover (L,R) pairs at S=0: all intermediate values PLUS the start.
  Mover (L,R) pair: the end value.

  For EC-freedom at S=0: end value != any intermediate value or start value.

  On {0,1}^2, the walk is on a 4-vertex graph (square):
    (0,0) -- (1,0) -- (1,1) -- (0,1) -- (0,0)
  and diagonal toggles are not possible (only one coord toggles per step).

  A walk of length J0+K0 on the square starting at (L0, R0).
  The walk visits J0+K0+1 vertices (with repeats).
  The endpoint is ((L0+J0)%2, (R0+K0)%2).

  For EC-freedom: the endpoint must not equal any previously visited vertex.
  On a 4-vertex graph, after >=4 steps, the walk must revisit a vertex.
  So if J0+K0 >= 4: the walk revisits, and the endpoint is at distance
  (J0+K0) from start. Since the square has diameter 2, if J0+K0 >= 3,
  the walk must revisit its path.

ACTUALLY: this is getting complicated. Let me just verify the PIGEONHOLE
computationally. The real question: with 3 phases and normalForm, is
EC ALWAYS present at the sandwiched ternary?

Let me check: for EVERY possible combination of (L0, R0) and (J_i, K_i)
satisfying normalForm + binary parity, does EC always arise?
"""

from itertools import product as iterproduct

print("=" * 70)
print("EXHAUSTIVE CHECK: normalForm + binary parity => EC")
print("=" * 70)

# NormalForm (J,K) patterns with maximum fire count per phase
# For m_t=3, each phase has fc_t = 1, so J and K are bounded by phase length
# But phase length can vary. For sub-threshold product and n>=7,
# the phase fire counts are bounded. Let's check small values.

# First: what (J,K) combinations sum to fc(bL) and fc(bR)?
# fc(bL) = 2j (even), fc(bR) = 2k (even) for some j, k >= 1.
# 3 phases: J0+J1+J2 = 2j, K0+K1+K2 = 2k.

# For minimum fire counts (fc = 2): 2j = 2, j = 1. 2k = 2, k = 1.
# So J0+J1+J2 = 2, K0+K1+K2 = 2.

# NormalForm patterns with small J,K:
# (1,0), (0,1), (1,1), (2,1), (1,2), (3,0)?->NO (toggleFR), (0,3)?->NO
# With J+K>0 and normalForm:
#   (1,0), (0,1), (1,1), (2,1), (1,2), (3,1), (1,3), (2,3), (3,2), ...

# For J0+J1+J2 = 2 and K0+K1+K2 = 2:
# Possible NF triples:
# Each (Ji, Ki) must be normalForm.

def is_nf(J, K):
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True


# Enumerate all NF phase triples with sum constraints
def check_ec_for_params(L0, R0, phases):
    """Check if EC exists for given initial (L0, R0) and phase (J,K) list.

    Model: 3 phases. Phase i has S-level i.
    Binary walk during phase i: J_i left-fires, K_i right-fires.
    Starting (L,R) for phase 0: (L0, R0).

    At each phase: the nonmover (L,R) values are all intermediate walk values.
    The mover (L,R) value is the endpoint of the walk in that phase.

    For simplicity, model the walk as visiting vertices in ORDER:
    the walk starts at some (L,R) and makes J+K steps, each toggling one coord.
    The order of toggles matters for which vertices are visited!

    But for EC purposes: we need the ENDPOINT to match some previously visited
    vertex. The set of visited vertices depends on the walk ORDER.

    For a WORST CASE (EC-avoiding) analysis: choose the walk order to MINIMIZE
    the visited set. This means spreading the toggles to avoid revisiting.

    On {0,1}^2, maximum distinct vertices = 4.
    Walk of length J+K starting from v:
    - If J+K = 0: just v (impossible for NF with J+K > 0 usually, but (1,0) has J+K=1)
    - If J+K = 1: visits v and one neighbor (2 distinct)
    - If J+K = 2: visits v, a neighbor, and either back to v (if same coord toggled)
      or a diagonal (if different coord toggled). Worst case: 3 distinct.
    - If J+K >= 3: visits at least 3 distinct; if J+K >= 4: all 4.

    For the endpoint: if J is odd, L is toggled; if K is odd, R is toggled.
    Endpoint = (L0 xor (J%2), R0 xor (K%2)).

    The endpoint matches the start iff J even AND K even => BothEven => not NF.
    So for NF phases: endpoint != start. Always 1 safe exclusion.

    But we need endpoint != ALL visited nonmover vertices, not just start.
    """
    L, R = L0, R0
    ec = False

    for i, (Ji, Ki) in enumerate(phases):
        # Phase i: S-level i.
        # Start (L, R). Walk Ji+Ki steps.
        # Nonmover: all visited vertices INCLUDING start.
        # Mover: endpoint.

        # Generate ALL possible walk orderings (interleave Ji L-toggles and Ki R-toggles)
        # For EC analysis: check if ANY ordering gives endpoint in visited set.
        # For EC-freedom: need ALL orderings to have endpoint NOT in visited set.

        # The visited set depends on the ordering.
        # Endpoint is FIXED: (L xor Ji%2, R xor Ki%2).
        endpoint = ((L + Ji) % 2, (R + Ki) % 2)

        # Check: does endpoint equal start?
        if endpoint == (L, R):
            # BothEven: not NF, should not happen
            return True  # EC

        # Check: for the BEST walk ordering, can endpoint avoid all nonmover vertices?
        # Nonmover vertices include start (L, R) and all intermediate vertices.

        # For a walk on {0,1}^2, the set of visited vertices is determined by
        # the subsequence of L-toggles and R-toggles. Let me enumerate all orderings.

        # Generate all interleavings of Ji L-toggles and Ki R-toggles
        from itertools import combinations
        total_steps = Ji + Ki
        if total_steps == 0:
            # No neighbor fires. Endpoint = start. BothEven. Skip (not NF).
            continue

        # Choose which steps are L-toggles (the rest are R-toggles)
        any_ordering_avoids = False
        for l_positions in combinations(range(total_steps), Ji):
            visited = set()
            cl, cr = L, R
            visited.add((cl, cr))
            for step in range(total_steps):
                if step in l_positions:
                    cl = 1 - cl
                else:
                    cr = 1 - cr
                if step < total_steps - 1:  # intermediate = nonmover
                    visited.add((cl, cr))
            # Last step = endpoint = mover
            assert (cl, cr) == endpoint

            if endpoint not in visited:
                any_ordering_avoids = True
                break

        if not any_ordering_avoids:
            # For ALL orderings: endpoint is in nonmover set => EC
            return True

        # Update (L, R) for next phase
        L, R = endpoint

    return ec  # False if no EC found


# Enumerate all valid NF phase triples
nf_patterns = []
for J in range(10):
    for K in range(10):
        if is_nf(J, K):
            nf_patterns.append((J, K))

print(f"NormalForm patterns up to J,K=9: {nf_patterns}")

# Check all triples with J_sum even, K_sum even
total_checked = 0
ec_count = 0
no_ec_cases = []

for Jsum in range(2, 12, 2):  # even J_sum
    for Ksum in range(2, 12, 2):  # even K_sum
        for p0 in nf_patterns:
            for p1 in nf_patterns:
                J2 = Jsum - p0[0] - p1[0]
                K2 = Ksum - p0[1] - p1[1]
                if J2 < 0 or K2 < 0:
                    continue
                if not is_nf(J2, K2):
                    continue

                phases = [p0, p1, (J2, K2)]

                # Check all starting (L0, R0)
                for L0, R0 in iterproduct([0, 1], repeat=2):
                    total_checked += 1
                    if check_ec_for_params(L0, R0, phases):
                        ec_count += 1
                    else:
                        no_ec_cases.append((L0, R0, phases))

print(f"\nTotal checked: {total_checked}")
print(f"EC found: {ec_count}")
print(f"No EC: {len(no_ec_cases)}")

if no_ec_cases:
    print(f"\nNo-EC cases (first 10):")
    for L0, R0, phases in no_ec_cases[:10]:
        print(f"  L0={L0}, R0={R0}, phases={phases}")
else:
    print(f"\n*** ALL CASES HAVE EC ***")
