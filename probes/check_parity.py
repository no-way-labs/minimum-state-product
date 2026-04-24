#!/usr/bin/env python3
"""Check: with 3 consecutive binary, isolated ri firings, fc(ri) >= 2,
   does the min gap always have even L-fires and even R-fires?"""

from itertools import product as iterproduct

def check_parity_for_n(n, ms):
    """For given n and state sizes ms, enumerate all good cycles with
    3 consecutive binary at positions 0,1,2, where proc 1 (=ri) has
    isolated firings and fc >= 2. Check if min gap has even L and R fires."""

    # This is too expensive for full enumeration.
    # Instead, let's check a simpler structural property:
    # With isolated firings of ri, in the min gap, do L and R have even fires?

    # Actually, let's just check: for n=9 with ms=(2,2,2,3,3,3,3,3,3),
    # enumerate all good cycles and check the parity.

    # But this is O(product!) which is way too large.
    # Let's think about it differently.

    # Key fact: in the min gap of ri, the mover starts at i or rri.
    # The mover walk is nearest-neighbor.
    # With isolated firings, gap >= 2.
    # At the END of the gap, the mover must be at i or rri (to return to ri).
    # So the mover does a walk from {i, rri} to {i, rri} in the gap.

    # During this walk, i fires each time moverAt = i, rri fires each time moverAt = rri.
    # The parity of i-fires = parity of number of times moverAt = i.
    # Similarly for rri.

    # For entry conflict: we need both parities to be even.

    # Claim: with the walk starting at i or rri and ending at i or rri,
    # the start and end contribute to the fire count.
    # If start = end = i: i fires at start and end positions + interior.
    # Actually, "fires" means moverAt = i at that step.
    # Start: moverAt(a+1) = i or rri.
    # End: moverAt(b-1) = i or rri (and moverAt(b) = ri).

    # Wait, actually the mover walk in the gap is:
    # Step a: moverAt(a) = ri (fires)
    # Step a+1: moverAt(a+1) ∈ {i, rri} (not ri, isolated)
    # Steps a+1 to b-1: mover walks
    # Step b: moverAt(b) = ri (fires again)
    # The mover at step b-1 must be in {i, ri, rri} (so that ri can fire at b)
    # And moverAt(b-1) ≠ ri (because isolated on BOTH sides? No, isolated means
    # the step AFTER ri fires is not ri. It says nothing about the step BEFORE.)

    # Actually, _hiso says: for all a, moverAt(a) = ri → moverAt(nextIndex(a)) ≠ ri.
    # This means: after each ri-firing, the next step is NOT ri.
    # It does NOT say: the step before ri-firing is not ri.

    # So at step b-1: moverAt(b-1) could be ri! (a stay step at ri)
    # Wait no: if moverAt(b-1) = ri, then moverAt(nextIndex(b-1)) = moverAt(b) = ri.
    # But _hiso says: moverAt(b-1) = ri → moverAt(nextIndex(b-1)) ≠ ri. Contradiction.
    # So actually, _hiso DOES prevent the step before ri from being ri (since the
    # step after the step before ri is ri itself).

    # Wait: _hiso says moverAt(a) = ri → moverAt(nextIndex(a)) ≠ ri.
    # If moverAt(b-1) = ri, then nextIndex(b-1) = b, and moverAt(b) = ri.
    # So _hiso applied at a=b-1: moverAt(b-1) = ri → moverAt(b) ≠ ri. Contradiction!
    # So moverAt(b-1) ≠ ri. ✓

    # So in the gap [a+1, b-1], the mover never equals ri.
    # moverAt(a+1) ∈ {i, rri} (from next_mover_is_local at a, excluding ri)
    # moverAt(b-1) ∈ {i, rri} (since moverAt(b) = ri and moverAt(b-1) must be adjacent, excluding ri)
    # Wait, moverAt(b-1) must be such that next_mover_is_local gives moverAt(b) ∈ {left(m), m, right(m)}.
    # moverAt(b) = ri. So ri ∈ {left(moverAt(b-1)), moverAt(b-1), right(moverAt(b-1))}.
    # ri = moverAt(b-1) is ruled out.
    # ri = left(moverAt(b-1)) → moverAt(b-1) = right(ri) = rri.
    # ri = right(moverAt(b-1)) → moverAt(b-1) = left(ri) = i.
    # So moverAt(b-1) ∈ {i, rri}. ✓

    # Now: in the walk from a+1 to b-1, the mover is NEVER ri.
    # The walk visits i, rri, and potentially other processors.
    # i-fires in gap = number of steps k ∈ [a+1, b-1] with moverAt(k) = i.
    # rri-fires in gap = number of steps k ∈ [a+1, b-1] with moverAt(k) = rri.

    # For the parity of i-fires to be even: the number of visits to i is even.
    # Similarly for rri.

    # Key observation: the walk from moverAt(a+1) to moverAt(b-1) on the ring
    # (excluding ri) can be modeled as a walk on a path/arc graph.

    # With n >= 9: the ring minus ri has n-1 >= 8 vertices.
    # i and rri are adjacent to the removed vertex ri.
    # The walk starts at i or rri and ends at i or rri.

    # Actually, I realize this is getting too complex for a quick check.
    # Let me just verify: is the parity always even for the MIN gap?

    # For the MIN gap: the gap is the smallest gap. If the gap has size 2:
    # Steps a+1 and b-1 are the same step (b = a+2).
    # moverAt(a+1) ∈ {i, rri} and moverAt(a+1) = moverAt(b-1) ∈ {i, rri}.
    # In a gap of size 2 (gap = b - a = 2): there's exactly 1 step in [a+1, b-1]: step a+1.
    # The mover at a+1 is either i or rri.
    # i-fires in gap = 1 if moverAt(a+1) = i, else 0.
    # rri-fires in gap = 1 if moverAt(a+1) = rri, else 0.
    # So one parity is 1 (odd) and the other is 0 (even).
    # The parity vector is (1,0) or (0,1) → NOT (even, even)!

    # This means: for a gap of size 2, the parity condition is NOT met!
    # So fc2_isolated_ec_of_even_gap would NOT give EC for gap = 2.

    # HOWEVER: this is the MIN gap. Maybe the complement gap has even parities?
    # From fc2_parity_vectors_agree: gap and complement have the same parity vector.
    # If gap has (odd, even): complement also has (odd, even).
    # So neither gap gives the (even, even) parity needed for EC.

    # CONCLUSION: The parity-walk EC approach does NOT work for gap = 2!
    # A different proof technique is needed.

    print("Gap = 2 analysis:")
    print("  moverAt(a+1) ∈ {i, rri}")
    print("  If moverAt(a+1) = i: i-fires=1(odd), rri-fires=0(even) → no EC")
    print("  If moverAt(a+1) = rri: i-fires=0(even), rri-fires=1(odd) → no EC")
    print("  Parity (even,even) is NOT guaranteed for gap=2!")
    print()
    print("BUT: with gap=2, we have a tight bounce: ri → i → ri or ri → rri → ri")
    print("This means the mover ONLY visits {ri, i} or {ri, rri} in this gap.")
    print("With n >= 9: processors at distance >= 4 from ri are never visited.")
    print("Such processors form a safe zone → safe processor exists!")
    print("→ small_arc_contradicts_convergence applies!")
    print()

    # Wait! For the ENTIRE cycle (not just one gap):
    # If ALL gaps have size exactly 2 (the minimum), and fc(ri) >= 2:
    # In each gap, the mover visits only 1 position (i or rri).
    # Between gaps, the mover is at ri.
    # So the mover ONLY visits {i, ri, rri}.
    # With n >= 9: processors at distance >= 3 are safe.
    # But we need distance >= 2 for safe (q, left(q), right(q) all never mover).
    # right(rri) = right(right(right(i))). With n >= 9, there are processors at distance >= 4.
    # Say q = right(right(right(right(i)))). Then q, left(q)=right(right(right(i))), right(q) are all
    # at distance >= 3 from {i, ri, rri}. So they're never the mover.
    # This gives a safe processor → small_arc_contradicts_convergence → False!

    print("If ALL gaps have size 2 (mover only visits {i, ri, rri}):")
    print("  With n >= 9: processor at distance 4+ from ri is safe")
    print("  → small_arc_contradicts_convergence → False ✓")
    print()

    # But what if SOME gap has size > 2?
    # Then the mover might escape further.
    # However, the MINIMUM gap has size 2, and in THAT gap the mover is confined.
    # But in OTHER gaps, the mover might go far.
    # The safe processor argument requires ALL steps to avoid q's neighborhood.
    # If the mover visits far-away processors in big gaps, no safe processor.

    # KEY INSIGHT: We need a DIFFERENT argument for large gaps.
    # For large gaps: the parity argument might work!
    # For gap >= 4: both i and rri fire at least twice → even fires → EC.
    # Wait, not necessarily. The mover might visit other processors too.
    # With a gap of size g: i-fires + rri-fires <= g.
    # If the mover bounces: ri → i → ri (gap=2), then in a bigger gap:
    # ri → i → left(i) → ... → i → ri.
    # i fires twice (at start and near end): even!
    # rri fires 0 times: even!
    # EC from (even, even)!

    # Actually wait. In a gap of size g >= 4:
    # moverAt(a+1) = i, then the mover goes to left(i) or ri (but not ri since gap).
    # If it goes to left(i), then left(left(i)), etc.
    # Eventually it must return to {i, rri} by step b-1.
    # The path is: i → left(i) → ... → rri → ... → i or rri.
    # Or: i → left(i) → i → left(i) → ... (bouncing)

    # The parity of i-visits depends on the path.
    # If the mover goes: i → left(i) → i → left(i) → i → rri (at b-1):
    #   i-fires = 3 (odd), rri-fires = 1 (odd) → (odd, odd) → no EC.
    # If: i → rri → i → rri → i → ...
    #   Wait, can moverAt go from i to rri directly? Only if rri = right(i) or left(i).
    #   rri = right(right(i)). With n >= 5: rri ≠ right(i) and rri ≠ left(i).
    #   So the mover can't go from i to rri in one step.

    # Hmm wait: right(i) = ri. So from i, the mover can go to: left(i), i, or right(i)=ri.
    # But ri doesn't fire in the gap. So if the mover goes to ri... it can't fire ri (but
    # next_mover_is_local says moverAt(k+1) ∈ {left(moverAt(k)), moverAt(k), right(moverAt(k))}.
    # If moverAt(k) = i and moverAt(k+1) = ri: ri fires at step k+1. But we said ri doesn't
    # fire in the gap [a+1, b-1]. So if k+1 < b: moverAt(k+1) ≠ ri.

    # Wait, I confused "mover" with "fire". moverAt(k) = p means p fires at step k.
    # In the gap [a+1, b-1], ri doesn't fire: moverAt(k) ≠ ri for a < k < b.
    # (More precisely: for a+1 <= k <= b-1, moverAt(k) ≠ ri.)
    # At step b: moverAt(b) = ri.

    # So in the gap, the mover can't be ri. From i, next step can be left(i), i, or ri.
    # But moverAt ≠ ri in the gap → from i, next step is left(i) or i.

    # Similarly from rri = right(right(i)): next step can be right(i)=ri, rri, or right(rri).
    # But moverAt ≠ ri in gap → from rri, next step is rri or right(rri).

    # So the mover in the gap CANNOT cross ri!
    # From i: can go left or stay.
    # From rri: can go right or stay.

    # This means: if the mover starts at i (step a+1), it can ONLY visit
    # {i, left(i), left(left(i)), ...} in the gap. It can NEVER reach rri!
    # (Because to get from i-side to rri-side, you'd have to cross ri.)

    # Similarly, if the mover starts at rri, it can ONLY visit
    # {rri, right(rri), ...} and NEVER reach i!

    # THIS IS THE KEY INSIGHT!

    print("KEY INSIGHT: In the gap [a+1, b-1], the mover cannot cross ri!")
    print("  From i: can only visit i's left arc")
    print("  From rri: can only visit rri's right arc")
    print("  So moverAt(a+1) determines which side the mover is on.")
    print()

    # Case 1: moverAt(a+1) = i → mover is on i's side (left arc)
    #   rri NEVER fires in the gap → rri-fires in gap = 0 (even)
    #   i fires at step a+1, then the mover might leave and come back.
    #   At step b-1: moverAt(b-1) ∈ {i, rri}. But mover is on i's side → moverAt(b-1) = i.
    #   So the mover starts and ends at i on the i-side arc.
    #   The walk on the arc: i → left(i) → ... → i.
    #   i fires at step a+1 and step b-1, plus any intermediate visits.
    #   Actually, the walk might be: i → left(i) → i → left(i) → ... → i.
    #   The number of i-visits includes the start and end.
    #   Wait, but moverAt(b-1) = i means i fires at step b-1.
    #   And moverAt(a+1) = i means i fires at step a+1.
    #   If gap = 2: only step a+1 (= b-1). i-fires = 1 (odd).
    #   If gap = 3: steps a+1, a+2. moverAt(a+1) = i, moverAt(a+2) ∈ {left(i), i}.
    #     If moverAt(a+2) = i: b-1 = a+2, so i-fires = 2 (even) → EC for R-parity!
    #     If moverAt(a+2) = left(i): b-1 = a+2, but moverAt(b-1) must be i. Contradiction.
    #     So gap = 3 with start=i: moverAt(a+2) = i → i-fires = 2 (even), rri-fires = 0 (even) → EC!

    print("Case: moverAt(a+1) = i, gap = 3:")
    print("  moverAt(a+2) must be i (since moverAt(b-1)=moverAt(a+2) must be i)")
    print("  i-fires = 2 (even), rri-fires = 0 (even) → EC!")
    print()

    # For gap = 2 with start=i: i-fires = 1 (odd), rri-fires = 0 (even).
    # Parity (odd, even) → no EC from this gap alone.

    # KEY: Can the min gap be exactly 2?
    # Yes, from isolated_minFiringGap_gap_ge2: gap >= 2.
    # So min gap could be exactly 2.

    # For gap = 2 with start=i:
    # In the entire cycle: mover visits {ri, i} in this gap.
    # All other gaps: mover starts at i or rri.
    # If ALL gaps start at i: mover only visits {ri, i, left(i), ...}.
    #   rri never fires → rri is constant. left(rri) = ri fires, but...
    #   Actually, with the mover on i's side: rri, right(rri) are never the mover.
    #   With n >= 9: many processors are never the mover.
    #   If some processor q has {q, left(q), right(q)} all on rri's side: safe!
    #   → small_arc_contradicts_convergence → False!

    # If some gap starts at rri: that gap visits rri's side.
    # We have at least one gap starting at i (the min gap) and potentially one starting at rri.

    # CRITICAL: Can both i-start and rri-start gaps coexist?
    # Yes. With fc(ri) >= 2: at least 2 gaps. Each starts at i or rri.
    # If one starts at i and another at rri: the mover visits BOTH sides.
    # Potentially covers all processors → no safe processor.

    # BUT: in each gap, the mover is confined to ONE side.
    # The TOTAL set of visited processors is the union across all gaps.
    # For a safe processor argument: we need a 3-wide zone never visited in ANY gap.

    # With n >= 9 and the mover visiting at most distance d_left on i's side
    # and distance d_right on rri's side:
    # The covered arc on i's side has width d_left + 1 (from i leftward).
    # The covered arc on rri's side has width d_right + 1 (from rri rightward).
    # Plus ri itself.
    # Total covered: d_left + d_right + 3 processors.
    # Uncovered: n - d_left - d_right - 3.
    # For a safe 3-wide zone: need n - d_left - d_right - 3 >= 3 → n >= d_left + d_right + 6.

    # With n >= 9: need d_left + d_right <= 3.
    # Meaning: the mover reaches at most 3 positions beyond {i, ri, rri}.

    # The min gap has size g_min = 2. In this gap: mover visits 1 step.
    # On i's side: d_left = 0 (just i). On rri's side: d_right = 0 (or vice versa).
    # But OTHER gaps might be larger.

    # What bounds do we have on the total distances?
    # In a gap of size g starting at i: the mover can reach distance g-1 from i.
    #   But must return to i by step b-1. So the walk is out-and-back.
    #   Maximum distance = (g-1)/2 (round trip).
    #   Actually, the mover might not need to return to i in the interior.
    #   It starts at i and ends at i (since moverAt(b-1) = i on i's side).
    #   Walk length = b-1-(a+1)+1 = g-2 steps (from a+1 to b-1 inclusive... wait).
    #   Wait, moverAt(a+1) = i (start), moverAt(b-1) = i (end).
    #   Number of steps from a+1 to b-1: g-2.
    #   Maximum distance from i: floor((g-2)/2) (since round trip).
    #   No wait: the walk has g-2 steps total. Starting and ending at i.
    #   It's a closed walk of length g-2 on a path (one-dimensional).
    #   The maximum distance from i is floor((g-2)/2).

    # Hmm, but this is per-gap. The total d_left is the MAX over all i-starting gaps
    # of floor((g-2)/2). Similarly d_right.

    # For the safe processor argument to work with n >= 9:
    # Need d_left + d_right <= 3.
    # If all gaps have size <= 5: max distance = floor(3/2) = 1. d_left+d_right <= 2. ✓
    # If any gap has size >= 6: max distance = floor(4/2) = 2. d_left+d_right <= 4. Maybe OK.

    # Actually, with fc(ri) >= 2 and ALL firings isolated:
    # Total cycle length L = sum of gaps. L = ∑ g_j.
    # Number of gaps = fc(ri). Min gap = g_min >= 2.
    # Sum of gaps = L.
    #
    # But we have no upper bound on L from the hypotheses.
    # With large L: some gaps could be huge, reaching far.

    # So the safe processor argument alone doesn't work for large gaps.

    # HOWEVER: for the PARITY argument, large gaps DO work!
    # With start=i and end=i (on i's side):
    # i fires at start (a+1) and end (b-1) and potentially in between.
    # The number of i-fires = number of visits to i in [a+1, b-1].
    # On a path graph (i-side arc), starting and ending at i:
    # The walk visits i at least twice (start and end, if g >= 3).
    # With g = 2: visits i once.
    # With g >= 3: visits i at start and end: at least 2 times.
    # If g >= 3 and on i-side: i-fires >= 2, and i-fires has parity...
    # Hmm, i-fires could be 2, 3, 4, ... depending on the walk.

    # WAIT: Here's the key insight for the proof!
    # If the min gap g_min >= 3: then i-fires >= 2 in that gap.
    # And if start=i: i-fires in gap >= 2.
    # rri-fires in gap = 0 (on i-side).
    # i-fires even? Not necessarily (could be 2=even or 3=odd).
    # But rri-fires = 0 = even. ✓
    # For EC: need both even. i-fires might be odd.

    # For gap_min = 2: no EC from parity. But small arc → safe processor (maybe).
    # For gap_min >= 3: i-fires >= 2 in gap, but parity undetermined.

    # ACTUALLY: wait. For start=i, end=i, on a path graph:
    # The walk from i to i has even length (since g-2 = b-1-(a+1) steps,
    # and the walk on a path has even/odd length determining if it returns).
    # On a path graph with vertex i at one end:
    # From i, the walk goes left to left(i), left(left(i)), etc., then back.
    # Each excursion from i has even length.
    # So the total walk from i back to i has EVEN number of i-visits?
    # No, that's not right. The number of visits to i is not the walk length.

    # Let me think about this more carefully.
    # Walk on integers: start at 0, each step ±1, return to 0 after k steps.
    # Number of visits to 0: at least 2 (start and end).
    # Can be 2, 3, 4, ...
    # With k=2: 0 → -1 → 0. Visits to 0: 2 (even).
    # With k=3: 0 → -1 → 0 → -1 → ?. Wait, k=3 means 3 steps from start.
    # Actually, k = g-2 = number of edges in the walk.
    # Walk of length 2: 0 → x → 0. Visits to 0: 2 (even).
    # Walk of length 3: 0 → x → y → 0. Visits: 2 or 3.
    #   0 → -1 → 0 → -1: doesn't return. So with return: 0 → -1 → 0 → 0.
    #   But 0 → 0 is a stay step (ok, mover stays at i).
    #   Visits to 0: 3 (odd).

    # So the parity of i-visits depends on the walk. No universal guarantee.

    print("Conclusion: The parity argument alone doesn't close the gap.")
    print("The safe processor argument works when ALL gaps are small (gap=2).")
    print("For larger gaps, a hybrid approach is needed.")
    print()
    print("HYBRID APPROACH:")
    print("  Case split on gap_min:")
    print("  - gap_min = 2: mover confined to 1 position per gap")
    print("    Subcases on how many SIDES are visited:")
    print("    a) Only i-side OR only rri-side: safe processor on the other side → False")
    print("    b) Both sides: but with gap=2, each gap visits only 1 position")
    print("       So mover visits {ri, i, rri}. Safe processor at distance >= 3 from ri.")
    print("       With n >= 9: right(right(right(right(i)))) is safe.")
    print("  - gap_min >= 3 AND gap_min is odd: i-fires might be odd. Need more analysis.")
    print("  - gap_min >= 3 AND gap_min is even: i-fires is... also not determined.")
    print()
    print("Actually, for gap_min = 2:")
    print("  The mover in EACH gap visits exactly 1 non-ri position.")
    print("  Across ALL gaps, the mover visits ri and at most {i, rri}.")
    print("  Total mover positions: subset of {i, ri, rri}.")
    print("  With n >= 9: processors at ring-distance >= 4 from ri are safe.")
    print("  Specifically: right^4(i) has {right^4(i), right^3(i), right^5(i)}")
    print("  all at distance >= 3 from {i, ri=right(i), rri=right^2(i)}.")
    print("  So right^4(i) is safe.")
    print("  → small_arc_contradicts_convergence → False!")

check_parity_for_n(9, None)
