# How the Lower Bound Was Closed

## The theorem

**M_n = 4·3^(n-2) for all n ≥ 9.**

`lower_bound_theorem` in `Theorem.lean`: for any ring with n ≥ 9 processors and state product < 4·3^(n-2), no valid self-stabilizing token ring system exists. Zero sorry, zero axiom. Lean kernel verified.

## The architecture

The proof never mentions token rings or Dijkstra directly. It shows that no convergent good cycle can exist in a sub-threshold system. The argument is a winding classification:

1. **Sweep** (|totalDisplacement| ≥ 2n): shadow cycle mirror theorem → the cycle creates a shadow configuration that traps the adversary → ¬converges.

2. **Odd winding** (|totalDisplacement| = n), uniform direction: excluded by binary processor parity — uniform direction forces all fire counts equal, but binary processors need even fire counts while odd winding needs odd displacement. Contradiction.

3. **Odd winding, non-uniform direction**: entry conflict via four mechanisms (Both-Even Return, Toggle-FR, Zero-Side EC, Traversal Return) plus two ring-level lemmas (Parity Obstruction, Ring Alternation). Every good cycle in this class has a processor that sees the same (L, S, R) context at both a mover step and a non-mover step, which is impossible since the transition function would need to both change and preserve the value.

4. **Zero winding** (totalDisplacement = 0): three sub-cases.
   - All-stay (cwStepCount = 0): every step has moverAt(k+1) = moverAt(k), meaning one processor fires forever. Contradicts convergence.
   - Safe processor exists: a processor and its neighbors never fire. Parallel orbit argument → ¬converges.
   - Large arc, no safe processor: wiggle shadow cycle construction → ¬converges.

All four cases are proved in `CaseObstructions.lean`. The master dispatch is `subThreshold_obstruction`, which takes only n ≥ 9, a good cycle, convergence, and sub-threshold product, and returns False.

## The 9K-line detour

The original proof plan had a different structure. Between `Theorem.lean` and `CaseObstructions.lean` sat a chain:

```
PhaseExtraction.lean → AllNormalFormFalse.lean → EndgameStubs.lean
```

`AllNormalFormFalse.lean` was 9,402 lines. It tried to prove: if a ternary "pivot" processor t has binary neighbors, all processors fire, and every extracted phase of t is "normal form" (not mechanism-triggering), then False.

The proof worked by case-splitting on the (J, K) fire counts of each phase — how many times left(t) and right(t) fire in the gap between consecutive t-firings. Each case led to more cases:

- K = 0: one-sided phase, right fires outside the gap
- J = 0: mirror
- J ≥ 1, K ≥ 1, interleaving: entry conflict via parity
- J ≥ 1, K ≥ 1, non-interleaving, J = K = 1: bridge theorems
- J ≥ 1, K ≥ 1, non-interleaving, J + K ≥ 3: reversal argument

The one-sided cases (K = 0 and J = 0) resisted six documented approaches. The J = K = 1 case needed bridge theorems that required fc(t) = 2, which couldn't be derived from the hypotheses. The file had 10 admits and was still growing.

## The v2 rewrite

The v2 rewrite started as an attempt to find a cleaner proof of the same theorem. It went through several phases:

**Phase 1: prefix-EC (successful).** If all t-firings are consecutive from step 0, the cycle wraps back to its initial config. Left(t) and right(t) don't fire during the consecutive block (every step fires t). So the context at t is the same at step 0 (mover) and step j (first non-t step, non-mover). Entry conflict. This closed the "consecutive t-firings" edge case that the v1 had as a sorry.

**Phase 2: case splitting (failed).** Attempted to handle (J, K) cases one by one. K = 0 led to second-phase construction. J = K = 1 led to bridge theorem wiring. J + K ≥ 3 led to (1, 1) suffix extraction via parity walk analysis. Each sorry closed spawned two new sorrys. The file grew from 348 to 523 lines with 7 sorrys, heading for the same explosion as v1.

**Phase 3: collapse (successful).** Reverted all case splits. Collapsed 4 sorrys back to 1 with a single sorry and a comment describing the global argument needed. 345 lines, 1 sorry.

**Phase 4: the discovery.** While researching the global argument, found that `subThreshold_obstruction` in `CaseObstructions.lean` already proves False for ANY convergent sub-threshold good cycle with n ≥ 9. The all-normal-form hypothesis is vacuously unused — the cycle can't exist regardless of phase structure. The sorry became one line:

```lean
exact subThreshold_obstruction _hn gc _hconv _hsub
```

No import cycle: v2 imports `CaseObstructions` which imports `PhaseExtraction` which imports `AllNormalFormFalse` (v1), but v2 ≠ v1. Linear chain, not circular.

## The punchline

The 9K-line `AllNormalFormFalse.lean` was proving a theorem whose hypothesis — "every phase is normal form" — was already impossible. The winding classification in `CaseObstructions.lean` showed that no convergent sub-threshold good cycle exists at all, for any n ≥ 9, regardless of what its phases look like.

The v1 was trying to prove False from a hypothesis that was ITSELF False. Any proof works. The correct proof is: don't analyze the phases. Just point out the cycle can't exist.

**Final: 330 lines, 0 sorry, replacing 9,402 lines with 10 admits.**

## File map

| File | Role | Sorry |
|------|------|-------|
| `Theorem.lean` | Final theorem: M_n ≥ 4·3^(n-2) | 0 |
| `CaseObstructions.lean` | Winding classification dispatch | 0 |
| `EntryConflict/AllNormalFormFalse.lean` | Phase normal-form impossibility (330 lines) | 0 |
| `EntryConflict/PhaseExtraction.lean` | Phase extraction chain | 0 |
| `EntryConflict/PhaseExtractionBase.lean` | TernaryPhase infrastructure | 0 |
| `EntryConflict/WaterfallBridge.lean` | Sweep → shadow → ¬converges | 0 |
| `Shadow/Theorem.lean` | Shadow cycle mirror theorem | 0 |
| `Wiggle/ShadowTrap.lean` | Wiggle → shadow → ¬converges | 0 |
| `CycleTypes.lean` | Winding definitions and classification | 0 |
| `GoodCycleBasics.lean` | Entry conflict impossibility | 0 |
| `EntryConflict/AllNormalFormFalse_old.lean` | Old 9K-line v1 (preserved for reference) | 10 |

## Timeline

- **Months prior**: Shadow cycle mirror theorem, wiggle shadow, waterfall bridge, entry conflict mechanisms, phase extraction infrastructure — all proved sorry-free.
- **2026-03-26 session start**: 4 sorrys in v2 (348 lines). Consecutive t-firings, K=0 one-sided, J=0 one-sided, non-interleaving.
- **Hour 1**: Closed consecutive t-firings sorry via prefix-EC. Fixed J+K case split bug.
- **Hours 2-4**: Chased case splits. Expanded to 7 sorrys / 523 lines. User intervention: "stop splitting."
- **Hour 5**: Collapsed back to 1 sorry / 345 lines. Researched global argument.
- **Hour 6**: Discovered `subThreshold_obstruction` handles everything. One-line proof. 0 sorry / 330 lines.
- **Hour 7**: Verified full `M_n_lower_bound` builds clean. Renamed files. Done.
