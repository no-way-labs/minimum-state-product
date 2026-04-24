"""
ra9_mutual_recursion_analysis.py — Trace the mutual recursion in ZeroWindingAssembly.lean

The 4 sorrys in ZeroWindingAssembly.lean correspond to providing cycle-type callbacks
for the core impossibility proof. The core proof (`subThreshold_binary_core_false_clean`)
needs 4 callbacks:

  hConsecZW       : gc.zeroWinding -> cwStepCount > 0 -> 3 consecutive binary -> False
  hNonConsecZW    : gc.zeroWinding -> cwStepCount > 0 -> NOT 3 consecutive binary -> False
  hSweepFalse     : gc.isSweep -> False
  hOddNonUnifFalse: gc.isOddWinding -> NOT uniformDirection -> False

The top-level proof (`subThreshold_obstruction_v2`) case-splits on cycle type
and delegates to:
  - zeroWinding_large_arc_false (sorry A + B)
  - nonZeroWinding_false (sorry C + D)

Each sorry corresponds to one cycle-type branch. The question: can we use
`subThreshold_binary_core_false_clean` to fill each sorry by providing the
other 3 callbacks trivially (since we KNOW the cycle type)?

ANALYSIS:
"""

analysis = """
==========================================================================
MUTUAL RECURSION TRACE
==========================================================================

The core function is `subThreshold_binary_core_false_clean` (PhaseExtractionClean.lean).
It takes 4 callbacks and derives False. Internally, it eventually invokes those
callbacks in specific branches. The question is whether filling one callback
with the core function creates a loop.

==========================================================================
SORRY A: consecutive binary + zero winding + cw > 0
==========================================================================

Location: ZeroWindingAssembly.lean line 518
Context: fun _h3consec => sorry
  where _h3consec : exists i, threeConsecutiveBinary sys.rs i

Known at this point:
  - hzero : gc.zeroWinding
  - hcw_pos : 0 < gc.cwStepCount
  - hno_safe : no safe processor
  - hsub : subThreshold
  - hn : n >= 9
  - hconv : converges

This callback is the `hConsecResidual` parameter to `large_arc_zeroWinding_ec_proof`.

Where `large_arc_zeroWinding_ec_proof` calls hConsecResidual:
  - GlobalMinGap.lean line 204: gap=1 OR non-binary endpoint, consecutive case
  - GlobalMinGap.lean line 206: right(p0) not binary, consecutive case
  - GlobalMinGap.lean line 307: gap=1, CCW-CW case
  - GlobalMinGap.lean line 309: p0 not binary, CCW-CW case

CAN WE USE subThreshold_binary_core_false_clean here?
  We need to provide its 4 callbacks. At sorry A we know:
  - gc.zeroWinding = True
  - gc.cwStepCount > 0
  - 3 consecutive binary EXISTS

  For hConsecZW: this IS sorry A itself -> RECURSIVE! Can't use directly.
  For hNonConsecZW: we know 3 consec binary exists, so hn3consec would be False.
    Callback: fun hzw hcw hnoncons => absurd h3consec_proof hnoncons
    where h3consec_proof comes from _h3consec. TRIVIAL.
  For hSweepFalse: we know gc.zeroWinding, sweep -> |W| >= 2n > 0, contradicts zeroWinding.
    Callback: fun hsweep => by { unfold isSweep at hsweep; unfold zeroWinding at hzero; omega }
    TRIVIAL.
  For hOddNonUnifFalse: we know gc.zeroWinding, oddWinding -> |W| = n > 0, contradicts.
    Callback: fun hodd _ => by { unfold isOddWinding at hodd; unfold zeroWinding at hzero; omega }
    TRIVIAL.

  So hConsecZW is the ONLY problematic callback. But wait — this IS sorry A.
  We're trying to fill sorry A = hConsecResidual, and the core function needs
  hConsecZW which is essentially the same callback.

  KEY INSIGHT: The core function's hConsecZW callback is:
    gc.zeroWinding -> cwStepCount > 0 -> (exists i, threeConsecutiveBinary) -> False

  And sorry A provides exactly this. So using subThreshold_binary_core_false_clean
  to fill sorry A would create: sorry A calls core, core calls hConsecZW = sorry A.

  BUT: we can check if core's internal logic actually USES hConsecZW.
  In PhaseExtractionClean.lean, binary_ring_impossibility_clean calls hConsecZW at:
    - Line 106: hConsecZW hzero _hcw_pos h3consec (in Z=0, pivot, all normal form, m(t)=2 branch)
    - Line 193: hConsecZW _hzw _hcw_pos h3consec (in Z>=1 branch)
    - Line 154: hNonConsecZW hzero _hcw_pos hnoncons (in Z=0, no pivot branch)

  So hConsecZW IS called by the core function. This means using core for sorry A
  would be genuinely recursive.

  HOWEVER: The place where hConsecZW is called in the core function is when
  m(t) = 2 (binary pivot) and all phases are normal form. At that point,
  we know BOTH zero winding AND 3 consecutive binary. The core function
  can't resolve this internally because allNormalForm_false2 requires m(t) >= 3.

  ALTERNATIVE FOR SORRY A:
  Use `consecutive_binary_zeroWinding_false` (ConsecutiveBinaryEC.lean line 152).
  It takes hCR and hNCC callbacks (the same two callbacks as large_arc_zeroWinding_ec_proof).
  So sorry A would call consecutive_binary_zeroWinding_false, which calls
  large_arc_zeroWinding_ec_proof, which calls hConsecResidual = sorry A.
  STILL RECURSIVE through the same path.

  The REAL question: can we break the cycle by providing a DIFFERENT proof
  for the specific sub-case where hConsecResidual is called?

  At the call sites (GlobalMinGap lines 204, 206, 307, 309), what's happening is:
  the global min gap analysis found a gap-1 pair or non-binary endpoint.
  These are exactly the cases that need palindromic EC from the full
  PhaseExtraction chain. The core function's allNormalForm_false2 handles
  the ternary pivot case but NOT the binary pivot case (m(t) = 2).

  CONCLUSION for Sorry A: This is genuinely hard. The recursion is real.
  The core obstruction for binary pivot (m(t) = 2 with both binary neighbors)
  reduces back to "3 consecutive binary + zero winding" which IS sorry A.

==========================================================================
SORRY B: non-consecutive binary + zero winding + cw > 0
==========================================================================

Location: ZeroWindingAssembly.lean line 523
Context: fun _hnoncons => sorry
  where _hnoncons : NOT (exists i, threeConsecutiveBinary sys.rs i)

Known at this point:
  - hzero : gc.zeroWinding
  - hcw_pos : 0 < gc.cwStepCount
  - hno_safe, hsub, hn, hconv
  - NOT 3 consecutive binary

CAN WE USE subThreshold_binary_core_false_clean?
  For hConsecZW: we know NOT 3 consecutive binary, so if hConsecZW is called
    with (exists i, threeConsecutiveBinary), we have absurd h3consec _hnoncons.
    But wait — hConsecZW's 3rd arg is the existence of 3 consec binary. We have
    _hnoncons : NOT exists. So:
    Callback: fun _ _ h3consec => absurd h3consec _hnoncons. TRIVIAL.
  For hNonConsecZW: this IS sorry B itself -> RECURSIVE!
  For hSweepFalse: contradicts zeroWinding. TRIVIAL.
  For hOddNonUnifFalse: contradicts zeroWinding. TRIVIAL.

  The core function's hNonConsecZW is called at:
    - PhaseExtractionClean.lean line 154: Z=0, no pivot, zeroWinding branch
    - PhaseExtractionClean.lean line 194: Z>=1 branch

  So using core for sorry B creates: sorry B calls core, core calls hNonConsecZW = sorry B.
  GENUINELY RECURSIVE.

  ALTERNATIVE: The non-consecutive case is resolved by the 4-mechanism universal EC
  (Both-Even Return, Toggle-FR, Zero-Side EC, Traversal Return). This proof needs
  ring_alternation + traversal_return from the PhaseExtraction chain. These are the
  functions in CaseObstructionsCore that are sorry'd.

  CONCLUSION for Sorry B: Genuinely recursive. Needs direct proof of
  non-consecutive universal EC.

==========================================================================
SORRY C: Sweep
==========================================================================

Location: ZeroWindingAssembly.lean line 554
Context: gc.isSweep, NOT gc.zeroWinding

Known at this point:
  - hsweep : gc.isSweep
  - hnz : NOT gc.zeroWinding
  - h3bin, hsub, hn, hconv

CAN WE USE subThreshold_binary_core_false_clean?
  Need hno_safe first. Sweep -> nonzero winding -> no safe processor. Available
  via no_safeProcessor_of_nonZeroWinding.

  For hConsecZW: callback gets gc.zeroWinding, but we know NOT gc.zeroWinding.
    Callback: fun hzw _ _ => absurd hzw hnz. TRIVIAL.
  For hNonConsecZW: same. fun hzw _ _ => absurd hzw hnz. TRIVIAL.
  For hSweepFalse: this IS sorry C itself -> RECURSIVE!
  For hOddNonUnifFalse: isSweep -> |W| >= 2n. isOddWinding -> |W| = n.
    If both: 2n <= |W| and |W| = n. But isSweep says natAbs >= 2*n. Not direct contradiction.
    Actually: isSweep is defined as |totalDisplacement|.natAbs >= 2 * n.
    isOddWinding is |totalDisplacement|.natAbs = n.
    If both: n >= 2*n, so n = 0. But n >= 9. Contradiction.
    Callback: fun hodd _ => by { unfold isSweep at hsweep; unfold isOddWinding at hodd; omega }
    TRIVIAL.

  The core function's hSweepFalse is called at:
    - PhaseExtractionClean.lean line 109 (Z=0, pivot, all NF, m(t)=2, non-ZW, sweep)
    - PhaseExtractionClean.lean line 157 (Z=0, no pivot, non-ZW, sweep)

  At these call sites, the core function has determined: NOT gc.zeroWinding and gc.isSweep.
  It calls hSweepFalse hsweep. If we fill hSweepFalse with sorry C's code, which uses
  the core function... that creates recursion.

  BUT WAIT: at the core function's call sites for hSweepFalse, we're inside
  binary_ring_impossibility_clean which already has hno_safe. And inside that
  function, when it calls hSweepFalse, it's in a branch where:
  - |Z| = 0 or |Z| = 1 or 2 (but |Z| < 3)
  - pivot exists or not
  - all phases are normal form (or not — if not, mechanism triggers EC)
  - m(t) = 2 (binary pivot) or m(t) >= 3 (handled by allNormalForm_false2)
  - NOT zeroWinding (non-ZW branch)
  - isSweep

  For sorry C: we want to prove sweep -> False.
  The existing CaseObstructions approach: sweep -> shadow cycle mirror theorem -> NOT converges.
  This does NOT require the core function at all! It's a completely separate argument.

  The problem is just that the shadow cycle argument (in Shadow.Theorem) requires
  WaterfallCycle extraction (from WaterfallBridge.lean), which imports PhaseExtractionBase.

  CONCLUSION for Sorry C: NOT genuinely recursive in the logical sense.
  The sweep case is proved by the shadow cycle mirror theorem, which is an
  independent argument. The sorry exists because of an import dependency
  (WaterfallBridge.lean -> PhaseExtractionBase), not because of logical circularity.

  RESOLUTION: Import WaterfallBridge.lean in ZeroWindingAssembly.lean and call
  the shadow cycle argument directly. This pulls in PhaseExtractionBase's 2 sorrys
  but closes sorry C entirely.

==========================================================================
SORRY D: Odd-winding + non-uniform direction
==========================================================================

Location: ZeroWindingAssembly.lean line 569
Context: gc.isOddWinding, NOT gc.uniformDirection, NOT gc.zeroWinding

Known at this point:
  - hodd : gc.isOddWinding
  - hunif : NOT gc.uniformDirection
  - hnz : NOT gc.zeroWinding
  - h3bin, hsub, hn, hconv

CAN WE USE subThreshold_binary_core_false_clean?
  Need hno_safe: oddWinding -> |W| = n > 0 -> nonzero winding -> no safe processor.

  For hConsecZW: NOT zeroWinding. fun hzw _ _ => absurd hzw hnz. TRIVIAL.
  For hNonConsecZW: NOT zeroWinding. fun hzw _ _ => absurd hzw hnz. TRIVIAL.
  For hSweepFalse: oddWinding -> |W| = n. Sweep -> |W| >= 2n.
    If n >= 9: n < 2n. Contradiction.
    Callback: fun hsweep => by { unfold isSweep at hsweep; unfold isOddWinding at hodd; omega }
    TRIVIAL.
  For hOddNonUnifFalse: this IS sorry D itself -> RECURSIVE!

  The core function's hOddNonUnifFalse is called at:
    - PhaseExtractionClean.lean line 115 (Z=0, pivot, all NF, m(t)=2, non-ZW, non-sweep, odd, non-uniform)
    - PhaseExtractionClean.lean line 163 (Z=0, no pivot, non-ZW, non-sweep, odd, non-uniform)

  So sorry D -> core -> hOddNonUnifFalse = sorry D. RECURSIVE.

  The odd-winding non-uniform case uses the same 4-mechanism universal EC as sorry B.
  CaseObstructions.lean (line 1053-1119) handles it by finding a binary processor,
  getting isolated firings, then calling subThreshold_binary_core_false_residual
  (at line 1119) in the non-consecutive sub-case.

  CONCLUSION for Sorry D: Genuinely recursive for the same reason as sorry B.
  The odd-winding non-uniform non-consecutive case reduces to the same
  4-mechanism universal EC that sorry B needs.

==========================================================================
SUMMARY TABLE
==========================================================================

| Sorry | Callback being filled | Where recursion happens | What's known at recursion point | How to break it |
|-------|----------------------|------------------------|-------------------------------|----------------|
| A | hConsecResidual (consec binary, ZW, cw>0) | Core calls hConsecZW in binary-pivot (m(t)=2) all-NF branch | ZW=true, cw>0, 3 consec binary, binary pivot with all phases normal form | Need direct proof for binary-pivot case OR break the binary_ring_impossibility at m(t)=2 |
| B | hNonConsecCore (non-consec binary, ZW, cw>0) | Core calls hNonConsecZW in |Z|=0-no-pivot or |Z|>=1 branch | ZW=true, cw>0, NOT 3 consec binary | Need direct non-consecutive universal EC proof |
| C | hSweepFalse (sweep) | Core calls hSweepFalse in non-ZW sweep branch | Sweep=true, NOT ZW | NOT genuinely recursive. Shadow cycle mirror theorem is independent. Import WaterfallBridge. |
| D | hOddNonUnifFalse (odd + non-uniform) | Core calls hOddNonUnifFalse in non-ZW odd non-uniform branch | Odd=true, non-uniform=true, NOT ZW | Same as sorry B: need direct non-consecutive universal EC |

==========================================================================
PLAN TO BREAK ALL RECURSION
==========================================================================

TIER 1 (immediate, no new proofs needed):

  Sorry C: Import WaterfallBridge.lean. Call the sweep -> shadow cycle mirror
  theorem path directly. This is NOT logically recursive — the sorry exists only
  because of import dependencies. WaterfallBridge.lean pulls in PhaseExtractionBase
  (2 sorrys in suffix-sparsity), but those are separate sorrys, not circular.

TIER 2 (requires understanding the internal dispatch):

  For sorrys A, B, D: the key realization is that subThreshold_binary_core_false_clean
  can fill the OTHER 3 callbacks trivially when one cycle type is known. The
  recursion only occurs through the ONE callback that matches the current cycle type.

  For sorry B and D: they both need the non-consecutive universal EC. If we had
  a direct proof of that (without going through the core function), both would close.

  For sorry A: the binary-pivot all-NF case with m(t)=2 creates 3 consecutive
  binary processors. The core function's allNormalForm_false2 only handles m(t)>=3.
  For m(t)=2, it delegates to hConsecZW. This is the genuine circularity.

  BREAKING STRATEGY:

  1. For the ZW callbacks (A, B): Instead of calling the core function, use
     `consecutive_binary_zeroWinding_false` (for A) and
     `nonConsecutive_zeroWinding_false` (for B) directly. BUT these also take
     hConsecResidual/hNonConsecCore callbacks and feed them to
     large_arc_zeroWinding_ec_proof. The recursion persists.

  2. TRUE FIX: The mutual recursion exists because:
     - The core proof (phase extraction) sometimes discovers it's in a
       zero-winding or sweep or odd-winding sub-case.
     - It delegates those to callbacks.
     - Those callbacks use the core proof for their non-trivial sub-cases.

     To break this, we need ONE of:
     (a) Make the core proof handle ALL cycle types internally (no callbacks).
     (b) Prove each cycle type case WITHOUT the core proof.
     (c) Use well-founded recursion on a decreasing measure.

  Option (a): Modify binary_ring_impossibility_clean to handle the m(t)=2
  case without delegating to hConsecZW. When m(t)=2 and both neighbors binary,
  we have 3 consecutive binary at the pivot. Instead of calling hConsecZW,
  use allNormalForm_false2 applied to a DIFFERENT pivot (one that's ternary).

  Since we have >=3 binary and sub-threshold, and since the product is < 4*3^(n-2),
  there must be a ternary processor. If that ternary processor also has both
  binary neighbors, we can use allNormalForm_false2 on it (since m(t)>=3).
  If no ternary processor has both binary neighbors, then the non-consecutive
  binary path applies.

  This would ELIMINATE the need for hConsecZW entirely — the core proof would
  be self-contained for the all-NF binary-pivot case by redirecting to a
  ternary pivot.

  Option (c): The callbacks carry strictly "less information" in some sense.
  When the core function calls hConsecZW, it's in a context where MORE is known
  (specific pivot, all phases normal form, zero set size, etc.). A well-founded
  argument could potentially work, but Lean 4's termination checker would need
  a decreasing measure.

RECOMMENDED PLAN:
  1. Close sorry C by importing WaterfallBridge. (Easy, no recursion.)
  2. For sorrys A, B, D: modify binary_ring_impossibility_clean to eliminate
     the m(t)=2 case without hConsecZW, by finding an alternative ternary pivot.
     This removes hConsecZW from the callback list. Then:
     - Sorry A disappears (no longer needed).
     - Sorry B: provide hNonConsecZW directly.
     - Sorry D: provide hOddNonUnifFalse via the core function with:
       hConsecZW = trivial (not ZW), hNonConsecZW = trivial (not ZW),
       hSweepFalse = trivial (odd vs sweep), and hOddNonUnifFalse still recursive.

     Actually sorrys B and D remain because hNonConsecZW and hOddNonUnifFalse
     callbacks are still used by the core function.

  BOTTOM LINE: The 4 callbacks exist because the core impossibility proof
  (phase extraction + allNormalForm_false2) only handles the "ternary pivot
  with both binary neighbors" case. All other cases (no pivot, binary pivot,
  non-ZW cycle types) must be handled externally. There is no way to avoid
  these callbacks without either:
  (a) Extending allNormalForm_false2 to handle binary pivots, OR
  (b) Having independent proofs for each cycle type that don't go through
      the core phase extraction.
"""

print(analysis)
