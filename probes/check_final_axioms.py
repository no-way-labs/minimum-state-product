"""
Analysis of the two remaining LB axioms.
No external dependencies needed - pure structural analysis.
"""

def check_axiom_cases():
    """
    Axiom 1: large_arc_zeroWinding_obstruction
      Hypotheses: n>=9, convergence, sub-threshold, zero winding, cwStepCount > 0, no safe proc

    Axiom 2: nonZeroWinding_obstruction
      Hypotheses: n>=9, convergence, sub-threshold, non-zero winding
    """

    # === Analysis of mover word structure ===
    #
    # A mover word is a sequence p_0, p_1, ..., p_{L-1} where p_{k+1} is
    # adjacent to p_k on C_n (left, self, or right).
    #
    # Zero winding: sum of signed steps = 0
    # cwStepCount > 0: at least one CW step
    # No safe processor: for all q, exists k with p_k in {q, left q, right q}
    #
    # The set of positions visited by the mover is a connected arc on C_n
    # (since consecutive movers are adjacent). Let the arc have length a
    # (number of distinct positions visited).
    #
    # The distance-1 envelope covers a + 2 positions (the arc plus 1 on each end).
    # Wait: on C_n, the envelope of a contiguous arc of length a covers
    # a + 2 positions (unless a = n, in which case it covers n).
    # For a < n: uncovered = n - a - 2 (if a <= n-2), or 0 (if a >= n-1).
    #
    # No safe processor <==> envelope covers all n positions
    # <==> a + 2 >= n (for a connected arc)
    # <==> a >= n - 2

    for n in [9, 10, 11, 12]:
        print(f"\n=== n = {n} ===")
        print(f"Threshold = 4 * 3^{n-2} = {4 * 3**(n-2)}")
        print(f"No safe proc <==> mover visits >= {n-2} distinct positions")
        print(f"Minimum arc for no safe proc: {n-2}")
        print(f"Maximum unvisited with no safe proc: {n - (n-2)} = 2")

        # With >= 3 binary and at most 2 outside the arc:
        # >= 1 binary inside the arc (fires even >= 2 times)
        print(f"With >=3 binary and <=2 outside arc: >=1 binary inside arc")

    print("\n" + "="*60)
    print("STRATEGY FOR AXIOM 1 (large_arc_zeroWinding_obstruction)")
    print("="*60)
    print("""
The hypotheses give:
  1. n >= 9
  2. sub-threshold => >= 3 binary processors
  3. zero winding => cwStepCount = ccwStepCount > 0
  4. no safe processor => mover visits >= n-2 positions (connected arc)
  5. converges

Since the arc has >= n-2 positions and there are >= 3 binary procs
with at most 2 outside the arc, at least 1 binary proc is INSIDE the arc.

For a binary proc p inside the arc:
  - p fires even >= 2 times (binary_fireCount_even + fireCount_ne_one)
  - Both edges adjacent to p are crossed by the mover

With zero winding and p inside the arc, the edge (left p, p) has
both CW and CCW crossings (edgeNetFlow = 0 at zero winding).

The paired crossing at edge (left p, p) gives steps a (CW) and b (CCW)
with no intervening crossings. Between a and b:
  - The mover stays on one side of the edge
  - left p doesn't fire between the two crossings

Actually, the cleaner argument: since p is inside the arc and fires >= 2,
there exist at least 2 firing steps for p. Between consecutive firings
of p, p's state changes and returns (since binary: 0->1->0 or 1->0->1).
The neighbors see... hmm, this needs more structure.

SIMPLEST APPROACH: Prove large_arc is vacuously true by showing
that 'no safe processor' + 'zero winding' + 'cwStepCount > 0' + 'convergence'
leads to contradiction via the EXISTING parallel orbit argument.

Wait - we already have small_arc_contradicts_convergence for when a safe
processor EXISTS. For when it doesn't exist, we need a different approach.

ACTUAL SIMPLEST APPROACH: Instead of proving the axiom's body, restructure
the proof so the axiom isn't needed. The zeroWinding_obstruction theorem
case-splits into three cases:
  (1) cwStepCount = 0 -> all_stay_contradicts_convergence [PROVED]
  (2) cwStepCount > 0, safe q -> small_arc_contradicts_convergence [PROVED]
  (3) cwStepCount > 0, no safe q -> large_arc_zeroWinding_obstruction [AXIOM]

Can we extend (2) to handle (3)? The parallel orbit in (2) needs q far from
all movers. In (3), no such q exists. But we can use a WEAKER condition:
q only needs to never be the mover itself (not necessarily far from movers).

If q never fires, q's state is constant. But flipping q changes the context
at adjacent movers. So the parallel orbit doesn't work directly.

HOWEVER: we don't need the full parallel orbit. We just need to show
convergence fails. Can we find a cycle of bad configs?
""")

    print("="*60)
    print("STRATEGY FOR AXIOM 2 (nonZeroWinding_obstruction)")
    print("="*60)
    print("""
The hypotheses give:
  1. n >= 9
  2. sub-threshold => >= 3 binary
  3. non-zero winding => displacement != 0
  4. converges

From zeroWinding_or_isOddWinding_of_not_sweep:
  Either |disp| >= 2n (sweep) or |disp| = n (odd winding) or disp = 0 (zero).
  Since disp != 0: either sweep or odd winding.

For SWEEP: shadow_cycle_mirror_theorem gives ¬converges directly.
  This is ALREADY PROVED in the codebase.

For ODD WINDING:
  - Uniform direction: killed by not_uniformDirection_and_isOddWinding_of_hasGe3Binary
    (binary parity constraint). ALREADY PROVED.
  - Non-uniform direction: needs separate argument.

For non-uniform odd winding:
  - |disp| = n, both CW and CCW steps exist
  - edgeNetFlow = ±1 at every edge
  - Every edge is crossed at least once

  Does a safe processor exist? edgeNetFlow ±1 means cwMoveCount(p) + ccwMoveCount(right p) >= 1
  for every p. So every edge has at least one crossing, meaning every position is either
  a mover or adjacent to a mover at some step. So NO SAFE PROCESSOR exists.

  This means small_arc_contradicts_convergence doesn't apply!

  We need a direct argument for non-uniform odd winding.

  Key: with non-uniform odd winding, there exist both CW and CCW steps.
  With >=3 binary, some binary proc fires. The fire count structure
  is constrained.

  Actually, for non-uniform odd winding:
    cwStepCount > 0 AND ccwStepCount > 0
    cwStepCount - ccwStepCount = ±n
    cwStepCount + ccwStepCount <= configs.length

  So cwStepCount >= (n+1)/2 (roughly). The mover covers significant ground.

PLAN: Handle non-uniform odd winding via entry conflict.
  With |disp| = n and non-uniform: the mover has both CW and CCW steps.
  Since edgeNetFlow = ±1, at edges where the flow is +1 (CW dominates),
  cwMoveCountAt(p) >= 1. At edges where flow is -1, ccwMoveCountAt(right p) >= 1.
  The CW-dominant edges and CCW-dominant edges alternate or cluster.

  For a CW-dominant edge with also CCW crossings (non-uniform):
    cwMoveCount(p) >= 2 (since net +1 and ccw >= 1 → cw >= 2)
    This gives paired crossings → potential entry conflict.

  Actually, non-uniform just means SOME step is non-CW and SOME is non-CCW.
  It's possible that ALL edges have net flow +1 (uniform CW net flow).
  In that case, edges with CCW crossings must have cw >= 2.

  Hmm, but with uniform net flow +1 and non-uniform direction:
  some edge has both CW and CCW crossings. Those edges have cw >= 2.
  The paired crossing argument gives entry conflict at those edges.

Wait, but the paired crossing argument needs zero winding to guarantee
opposite crossings at the SAME edge. For odd winding, the edge net flow
is ±1, not 0. So at an edge with net flow +1, we have cw - ccw = 1.
If ccw >= 1, then cw >= 2, and we have BOTH types of crossings at this edge.

So the paired crossing DOES apply for odd winding non-uniform!
We just need one edge with both CW and CCW crossings.

With non-uniform direction: both CW and CCW steps exist.
  ∃ k1 with stepDir = CW: moverAt k1 = p1, next = right p1
  ∃ k2 with stepDir = CCW: moverAt k2 = p2, next = left p2

  Edge (p1, right p1) has a CW crossing.
  Edge (left p2, p2) has a CCW crossing.

  Are these the same edge? Not necessarily.

  But for the SAME edge to have both: need an edge with cw >= 1 and ccw >= 1.
  With net flow ±1 everywhere:
    If net flow = +1: cw = ccw + 1. If ccw >= 1 → cw >= 2. Both types.
    If net flow = -1: ccw = cw + 1. If cw >= 1 → ccw >= 2. Both types.

  So we need: ∃ edge with net flow +1 and ccw ≥ 1, OR ∃ edge with net flow -1 and cw ≥ 1.

  Equivalently: ∃ edge with both CW and CCW crossings.

  By pigeonhole: total CW steps = Σ cwMoveCountAt(p) = cwStepCount
  total CCW crossings at edge (p, right p) = ccwMoveCountAt(right p)
  Σ ccwMoveCountAt(right p) = ccwStepCount > 0

  With ccwStepCount > 0: some edge has ccw >= 1. That edge has net flow ±1.
    If net flow +1: cw = ccw + 1 >= 2. Both types exist. ✓
    If net flow -1: ccw = cw + 1. But ccw >= 1 always. cw = ccw - 1 >= 0.
      If ccw = 1: cw = 0. Only CCW crossing. No both types.
      If ccw >= 2: cw >= 1. Both types. ✓

  So the edge might have only CCW crossings (ccw=1, cw=0, net=-1).

  Similarly with cwStepCount > 0: some edge has cw >= 1.
    If net flow -1: ccw = cw + 1 >= 2. Both types. ✓
    If net flow +1: cw = ccw + 1. cw >= 1 always. ccw = cw - 1 >= 0.
      If cw = 1: ccw = 0. Only CW crossing. No both types.

  So it's possible that no single edge has both CW and CCW crossings!
  Example: all CW crossings at edges 0..3, all CCW crossings at edges 4..7.
  Each CW edge: net +1, ccw=0, cw=1.
  Each CCW edge: net -1, cw=0, ccw=1.

  But wait: n=9, so 9 edges. cwStepCount - ccwStepCount = ±9.
  If disp = +n = +9: cwStepCount = ccwStepCount + 9.
  cwStepCount >= 9, ccwStepCount >= 1 (non-uniform).

  Hmm, if ccwStepCount = 1: only one CCW step. That CCW step is at some edge e.
  Edge e has ccw = 1, net flow = cw - 1 = +1 (if net flow is +1).
  So cw = 2 at edge e. Both types! ✓

  Wait, I made an error. Net flow at edge e = cwMoveCountAt(p_e) - ccwMoveCountAt(right p_e).
  All edges have net flow = 1 (since total displacement = +n and each edge has the same
  net flow... wait, is that true?)

  From edgeNetFlow_constant: ALL edges have the SAME net flow!
  With displacement = n: n * netFlow = n. So netFlow = 1 at every edge.

  So every edge has cwMoveCountAt(p) - ccwMoveCountAt(right p) = 1.

  With ccwStepCount >= 1: some edge has ccwMoveCountAt(right p) >= 1.
  At that edge: cwMoveCountAt(p) = ccwMoveCountAt(right p) + 1 >= 2.
  So that edge has BOTH CW and CCW crossings. ✓✓✓

  Similarly for displacement = -n: netFlow = -1 everywhere.
  cwStepCount >= 1 (non-uniform): some edge has cwMoveCountAt(p) >= 1.
  At that edge: ccwMoveCountAt(right p) = cwMoveCountAt(p) + 1 >= 2.
  Both types. ✓

So for non-uniform odd winding: there ALWAYS exists an edge with both
CW and CCW crossings. The exists_paired_edge_crossing machinery applies!

BUT exists_paired_edge_crossing currently has hypothesis (hzero : gc.zeroWinding).
This is only used to invoke ccwMoveCountAt_pos_of_cwMoveCountAt_pos_zeroWinding.
For odd winding, we can prove the same result differently.
""")

    print("="*60)
    print("REFINED PLAN")
    print("="*60)
    print("""
FOR AXIOM 2 (nonZeroWinding_obstruction):
  Step 1: Prove that non-zero winding + sub-threshold + n>=9 →
          either sweep or (odd winding + non-uniform).
          [Already done in cycle_classification]

  Step 2: For sweep: shadow_cycle_mirror_theorem → ¬converges.
          [Already proved]

  Step 3: For odd winding non-uniform:
    3a: Use small_arc_contradicts_convergence if safe proc exists.
        But we showed NO safe proc exists for odd winding.
    3b: Need direct argument. Use entry conflict from paired crossings.
        Show ∃ edge with both CW and CCW crossings (proved above).
        Apply paired crossing → entry conflict.

  Actually, for step 3b: we can just use the convergence argument.
  With both CW and CCW crossings at some edge, we have the paired crossing.
  Between paired crossings, the states are constrained.
  The entry conflict gives False via entryConflict_impossible.

  BUT: the paired crossing → entry conflict step is NOT YET PROVED in Lean.
  The PairedCrossing.lean file only proves exists_paired_edge_crossing,
  not that paired crossings imply entry conflicts.

FOR AXIOM 1 (large_arc_zeroWinding_obstruction):
  Same approach: use paired crossing entry conflict.
  The zero winding + cwStepCount > 0 already gives us paired crossings.

COMMON NEEDED LEMMA:
  paired_crossing_implies_entry_conflict:
    Given paired crossings a (CW) and b (CCW) at edge (p, right p)
    with no intervening crossings:
    → hasEntryConflict gc

  This is the HARD part. The mathematical argument is about state
  tracking between the crossings.

  ALTERNATIVE: Instead of proving the full entry conflict from paired crossings,
  use a DIFFERENT approach to eliminate these axioms.
""")

    print("="*60)
    print("ACTUALLY SIMPLEST APPROACH")
    print("="*60)
    print("""
For BOTH axioms: the key is that convergence gives us WellFoundedness.

For nonZeroWinding_obstruction:
  The non-zero winding cases are:
    (a) Sweep: shadow_cycle_mirror_theorem gives ¬converges. Already proved.
    (b) Odd winding, uniform: killed by binary parity. Already proved.
    (c) Odd winding, non-uniform: need to show ¬converges.

  For (c): Show that odd winding + non-uniform + sub-threshold + n>=9
  implies the existence of a shadow trap (cycle of bad configs).

  The shadow_cycle_mirror_theorem works for WaterfallCycle.
  Can we show that odd winding non-uniform cycles have waterfall structure?

  Actually NO: odd winding non-uniform cycles do NOT have waterfall structure.
  They have displacement n, not 2n.

  So we need a different shadow construction for odd winding.

  OR: we can show that odd winding non-uniform + sub-threshold + n>=9
  is impossible by finding an entry conflict directly.

  The mathematical proof (from the memory) says odd winding non-uniform
  is killed by entry conflict via 4 mechanisms + 2 ring-level lemmas.
  This is very complex to formalize.

SIMPLEST PRACTICAL APPROACH:
  Factor both axioms through a single new axiom that's more obviously true,
  or prove one of them using available machinery.

  For large_arc_zeroWinding_obstruction:
    We have cwStepCount > 0, zero winding, no safe proc, convergence.
    cwStepCount > 0 + zeroWinding => both CW and CCW exist.
    The paired_edge_crossing gives us crossings in both directions.

    Can we directly construct a shadow trap from the paired crossings?
    Between CW crossing a and CCW crossing b at edge (p, right p):
    - The states at p and right p at step a vs step b differ
    - This structural mismatch, combined with the convergence WF, gives False

    Actually, the SIMPLEST approach is: the entry conflict IS just the
    paired crossing combined with the freeze lemma. Let me formalize this.

    At step a (CW crossing): moverAt a = p. Config = g_a.
    After step a: move(g_a, p) = g_{a+1}.
    g_{a+1}[p] = f_p(g_a[left p], g_a[p], g_a[right p]) ≠ g_a[p].

    The non-mover at step a at right p sees: (g_a[p], g_a[right p], g_a[right^2 p]).
    Not privileged: f_{right p}(g_a[p], g_a[right p], g_a[right^2 p]) = g_a[right p].

    At step b (CCW crossing): moverAt b = right p.
    right p sees: (g_b[p], g_b[right p], g_b[right^2 p]).
    Privileged: f_{right p}(g_b[p], g_b[right p], g_b[right^2 p]) ≠ g_b[right p].

    For entry conflict at right p: need g_a context = g_b context.
    i.e., g_a[p] = g_b[p] AND g_a[right p] = g_b[right p] AND g_a[right^2 p] = g_b[right^2 p].

    Between a and b (no crossing of edge (p, right p)):
    - Does p fire? Maybe. If p fires, g[p] changes.
    - Does right p fire? Maybe. If right p fires, g[right p] changes.
    - Does right^2 p fire? Maybe.

    So the states CAN change between a and b, and we can't guarantee
    the contexts are equal. The entry conflict argument needs more structure.

    The ACTUAL mathematical proof uses the palindromic structure: for a BAF
    word, the CW pass and CCW pass create a mirror symmetry that forces
    specific context equalities. This requires detailed tracking of the
    mover word structure, not just paired crossings.

    This is too complex to formalize in a single session.
""")

    print("="*60)
    print("PRACTICAL PLAN: ELIMINATE nonZeroWinding_obstruction")
    print("="*60)
    print("""
nonZeroWinding_obstruction can be eliminated WITHOUT proving entry conflict!

The proof of nonZeroWinding_obstruction follows this chain:
  Non-zero winding → either sweep or odd winding.

  For SWEEP: shadow_cycle_mirror_theorem proves ¬converges.
    This is ALREADY PROVED. No axiom needed.

  For ODD WINDING:
    Uniform → binary parity contradiction. ALREADY PROVED.
    Non-uniform → need to prove False.

    For non-uniform odd winding with sub-threshold + n>=9:
      We can use small_arc_contradicts_convergence IF a safe proc exists.
      But we showed NO safe proc exists.

      However, we CAN extend small_arc to work with a WEAKER condition.

      IDEA: Even without a fully safe processor, we can find a processor q
      that is never the mover (even if it's adjacent to a mover).

      If q never fires: q's value is constant throughout the cycle.
      Flipping q creates configs that MIGHT be good configs (since q is
      adjacent to a mover, flipping q could change privileged-ness).

      But we can check: is the flipped config a good config?

      Actually, for the parallel orbit to work, we need:
      1. Flipped configs are NOT good configs
      2. Same mover fires at each flipped config
      3. Move at flipped config = next flipped config

      Condition 2 and 3 work if the mover never sees q's value
      (q is far from mover). This fails when q is adjacent to mover.

      Hmm. Let me think of another approach.

ALTERNATIVE: Prove nonZeroWinding_obstruction by inlining the case split.

theorem nonZeroWinding_obstruction ... : False := by
  -- Non-zero winding: either sweep or odd winding
  by_cases hsweep : gc.isSweep
  · -- Sweep: shadow cycle mirror theorem
    have h3bin : hasGe3Binary sys.rs := subThreshold_ge3_binary sys.rs hsub
    -- Need WaterfallCycle. Can we get one from isSweep?
    -- cycle_classification already routes sweeps through shadow...
    -- but cycle_classification itself calls nonZeroWinding_obstruction!
    sorry
  · -- Not sweep: zero or odd winding
    rcases gc.zeroWinding_or_isOddWinding_of_not_sweep hsweep with hzw | hodd
    · -- Zero winding: contradicts hnonzero
      exact absurd hzw hnonzero  -- Wait, hnonzero says NOT zero winding...
      -- Actually hnonzero : ¬gc.zeroWinding, and hzw : gc.zeroWinding
      -- So exact absurd hzw hnonzero ✓
      -- BUT WAIT: hzw says zeroWinding, and hnonzero says ¬zeroWinding.
      -- These contradict! So this case is impossible. ✓
    · -- Odd winding, non-uniform
      -- Need: sweep or (uniform + odd) are already excluded.
      -- Uniform + odd: killed by binary parity
      have h3bin := subThreshold_ge3_binary sys.rs hsub
      by_cases hunif : gc.uniformDirection
      · exact (gc.not_uniformDirection_and_isOddWinding_of_hasGe3Binary h3bin ⟨hunif, hodd⟩).elim
      · -- Non-uniform odd winding: THIS is the hard case.
        sorry

So the SWEEP case needs a WaterfallCycle, which requires knowing the cycle
has waterfall structure. But isSweep just says |displacement| >= 2n.
The gap: how to get WaterfallCycle from isSweep + sub-threshold + >=3 binary.

Actually, looking at cycle_classification more carefully:
  It says "sub-threshold + sweep → shadow_cycle_mirror_theorem → False"
  via sweep_obstruction, which calls nonZeroWinding_obstruction.

  BUT sweep_obstruction is proved by:
    apply nonZeroWinding_obstruction
    intro hzero
    -- zeroWinding means disp = 0, but isSweep means |disp| >= 2n
    -- contradiction

  So sweep_obstruction just says "a sweep is non-zero winding" and delegates.

  We need to handle sweep WITHOUT going through nonZeroWinding_obstruction.
  The shadow_cycle_mirror_theorem needs a WaterfallCycle, not just isSweep.

Where does WaterfallCycle come from? Let me check cycle_classification_residual.
It says: "does not identify isSweep with waterfall". So there's a gap.

The cycle_classification theorem produces WaterfallCycle ∨ zeroWinding.
But it doesn't say HOW to get WaterfallCycle from the hypotheses.
Looking at the proof: it case-splits on isSweep. For sweep case, it calls
sweep_obstruction which calls nonZeroWinding_obstruction to get False,
then any conclusion follows (including ∃ wc). Wait no, it says:
  exact False.elim (sweep_obstruction ...)

So it gets False and derives anything. The WaterfallCycle branch is NEVER
actually constructed in the proof! It's vacuously true because sweep → False.

This means: the entire proof chain works like this:
  case3a_impossible:
    cycle_classification gives (WaterfallCycle ∨ zeroWinding)
    WaterfallCycle → shadow_cycle_mirror_theorem → ¬converges → False
    zeroWinding → palindromic_entry_conflict_theorem → ... → axiom

  But cycle_classification for sweep uses nonZeroWinding_obstruction (axiom)
  to get False. So sweep is handled vacuously.

  If we could handle sweep WITHOUT the axiom, we'd be in business.

  The shadow_cycle_mirror_theorem needs WaterfallCycle as input.
  If we could construct WaterfallCycle from isSweep + sub-threshold,
  we could apply shadow_cycle_mirror_theorem directly.

  Alternatively: route the sweep case differently. Use the Shadow/Theorem
  machinery with isSweep directly.

Actually, let me check: does shadow_cycle_mirror_theorem work with just
GoodCycle (not WaterfallCycle)?
""")

    print("KEY QUESTION: Can we construct WaterfallCycle from isSweep + sub-threshold?")
    print("Or can shadow_cycle_mirror_theorem be generalized to GoodCycle?")

check_axiom_cases()
