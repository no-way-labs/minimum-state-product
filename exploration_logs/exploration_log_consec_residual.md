# Exploration Log: 3CB Consecutive Residual Sorry

## Date: 2026-04-10

## Question

The last 2 hard sorrys in the lower bound proof (Sweep:312 and OddWinding:153) target the "residual" case at a 3CB middle binary proc: isolated firing, odd parity, J+K=1 phase where the standard dispatch mechanisms fail. An RA counterexample killed the `normalForm_gives_ec` standalone theorem. What mechanism actually closes this gap?

## Key Scripts

- `ra_consec_residual.py` — Parts 1-9: counterexample analysis, sweep enumeration, random survey
- `ra_consec_residual2.py` — EC source survey, mechanism analysis, smaller n tests
- `ra_consec_residual3.py` — Complementary phase verification, fc>=4 analysis
- `ra_consec_residual4.py` — Cross-phase proof, triple pigeonhole, non-increment transitions
- `ra_consec_residual5.py` — Ordering analysis (when predicted EC triple fails)
- `ra_consec_residual6.py` — Definitive multi-ms, mixed-transitions, outlier analysis
- `ra_consec_residual7.py` — Outlier details, final summary

## Results

### 1. The Counterexample Doesn't Block the Real Proof

The normalForm counterexample (ms=(3,2,...,2), mover word (0,0,8,7,...,1)):
- **IS** sub-threshold (product=768 < 8748=threshold)
- **IS** locally consistent (no table conflict)
- Does **NOT** converge (completion fails — both identity and privileged completions fail)
- Does **NOT** produce the residual at any 3CB block: at every 3CB triplet among procs 1-8, phases have J+K=2 (both neighbors fire once per gap)
- Blocks `normalForm_gives_ec` (standalone theorem: all-normal-form → EC) correctly
- Does NOT block the actual sorry target (which works inside a stronger branch with convergence, sub-threshold, sweep/odd-winding hypotheses)

### 2. EC Always Holds (100%, No Exceptions)

**Every good cycle with 3CB sub-threshold has entry conflict.** Zero exceptions across:

| Test | Samples | EC Rate |
|------|---------|---------|
| n=9, ms=(2,2,2,3,3,3,3,3,3), inc only | 315,973 | 100.000% |
| n=9, same ms, mixed inc/dec | 540,696 | 100.000% |
| n=9, ms=(2,2,2,3,3,3,3,3,4) | 69,735 | 100.000% |
| n=9, ms=(2,2,2,2,3,3,3,3,3) | 60,232 | 100.000% |
| n=9, ms=(2,2,2,2,2,3,3,3,3) | 53,275 | 100.000% |
| n=5, ms=(2,2,2,3,3), all combos | 375,176 | 100.000% |
| Residual-specific (J+K=1) at n=9 | 27,959 | 100.000% |
| Residual-specific at n=5 | 44,029 | 100.000% |

### 3. EC Location

EC is at the 3CB block 99.998% of the time:
- At middle binary (proc 1): 98.3%
- At boundary binary (proc 0 or 2): covers the remaining 1.7% within 3CB
- Only 5 out of 315,973 cycles had EC exclusively at ternary procs (outside 3CB)

### 4. The Mechanism: Cross-Phase EC

**For fc(mid)=2** (the dominant case in residual):

Two phases at the middle binary. Residual phase has J+K=1. Complementary phase has:
```
J' + K' = fc(left) + fc(right) - (J + K) = fc(left) + fc(right) - 1 >= 2+2-1 = 3
```
This is proved by: sum of J across phases = fc(left), sum of K = fc(right), both even and >= 2.

**Cross-phase triple propagation**: With J=1, K=0 in residual:
- Mover triple at s1: T1 = (L1, v, R1)
- Mover triple at s2: T2 = (1-L1, 1-v, R1)
- In the other phase (s2→s1): left fires 1 time, right fires 2 times
- After left fires: c0 = L1. After right fires twice: c2 = R1.
- At some non-mover step: triple = (L1, v, R1) = T1. **EC!**

The only edge case: when the neighbor fires are packed such that (L1, v, R1) never coincides with a non-mover step at proc 1. This happens ~1.7% of the time. In those cases, EC appears at proc 0 or proc 2 instead (the boundary procs have a ternary neighbor providing additional context variety).

**For fc(mid)>=4**: All phases CAN have J+K<=1 (~5.7% of cases). The mechanism is more complex but still gives 100% EC, via multi-phase binary toggle interactions across the full cycle.

### 5. Proof Strategy for Lean

**Recommended: Option B (Complementary Phase)**

In the exact branch where the sorry lives (inside `consec_isolated_false`):

1. The hypothesis gives fc(mid) >= 2, isolated, odd parity, non-dispatched phase.
2. Extract ALL phases at mid (not just the residual one).
3. Prove: some other phase has J+K >= 2 (via the sum argument).
4. Invoke existing dispatch on that other phase → `hasEntryConflict gc`.
5. Since `hasEntryConflict gc` is the goal (or derives `False` from `¬hasEntryConflict`), done.

**Critical detail**: The proof works for fc(mid)=2 cleanly. For fc(mid)>=4, need:
- Either show that fc(mid) >= 4 cannot occur under the sorry's hypotheses (possible — the sorry has isolated firing + odd parity, which may force fc(mid)=2)
- Or extend the complementary phase argument to handle multiple phases

**Alternative: Option A (Universal Binary EC)**

Prove directly: any good cycle with ≥3 binary procs (consecutive) has EC. This is a stronger statement that subsumes the residual, but may be harder to formalize.

### 6. Counterexample Guardrail

The counterexample ms=(3,2,2,2,2,2,2,2,2) with its mover word:
- Has no EC at any 3CB block (proved: M and N are disjoint at every 3CB middle binary)
- Shows that "all phases normal form → EC" is FALSE as a standalone theorem
- But its phases have J+K=2 (not J+K=1), so it's NOT in the residual branch
- Any proof that uses J+K=1 or the complementary phase argument safely avoids this counterexample
