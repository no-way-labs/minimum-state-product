# PA: 3CB Convergence Failure Investigation — Results

## Task

Investigate whether 3 consecutive binary processors (3CB) forces convergence failure (recurrent bad SCCs / shadow traps) at sub-threshold product.

## Key Findings

### 1. The premise is WRONG for n <= 7

Valid 3CB systems exist at the minimum achievable product for n = 5, 6, 7:

| n | ms | Product | M_n | Threshold | 3CB? | Valid? |
|---|-----|---------|-----|-----------|------|--------|
| 4 | (2,2,2,3) | 24 | 24 | 36 | Yes {0,1,2} | Yes (19 systems found) |
| 5 | (2,2,2,3,4) | 96 | 96 | 108 | Yes {0,1,2} | **Yes** (verified witness) |
| 6 | (2,2,2,4,3,3) | 288 | 288 | 324 | Yes {0,1,2} | **Yes** (verified witness) |
| 7 | (3,2,2,2,3,4,3) | 864 | 864 | 972 | Yes {1,2,3} | **Yes** (verified witness) |
| 8 | (2,2,3,4,3,3,2,3) | 2592 | 2592 | 2916 | **No** {0,1,6} | Yes (verified witness) |

All witnesses are from `gpt/scripts/verify_witnesses.py`, verified by independent verifier.

### 2. The M_5 witness structure

The M_5 = 96 witness has:
- ms = (2,2,2,3,4), product = 96 < 108 = 4*3^3 (sub-threshold)
- 3 consecutive binary at {0,1,2}
- Good cycle length 18 (not the minimum 10 = 2n)
- Fire counts: {0:2, 1:2, 2:4, 3:6, 4:4}
- Winding number W = 2 (uniform net flow 2 on every edge)
- **Zero entry conflict** at ALL procs: every mover context is disjoint from every non-mover context
- The cycle is a sweep (|W| = 2n) but NOT a uniform sweep (different procs fire different numbers of times)

### 3. How the M_5 witness avoids the shadow

The Shadow Cycle Mirror Theorem (Claim 4.4.1) constructs a shadow trap from a uniform sweep of length 2n. The M_5 witness avoids this by:

1. **Non-minimal cycle length**: Length 18 vs minimum 2n = 10. Proc 2 fires 4 times (2x minimum), proc 3 fires 6 times (2x minimum), proc 4 fires 4 times (1x minimum).

2. **More transition entries used**: With 18 steps, the good cycle touches 18 mover entries and 18 * (n-1) = 72 non-mover entries. This is almost the full context space, leaving no room for a shadow cycle to reuse entries without creating entry conflict.

3. **Bidirectional edge usage**: Edges (2,3) and (3,4) are traversed both CW and CCW. This creates a richer set of transition constraints that the shadow construction cannot exploit.

### 4. The proof architecture handles this correctly

The lower bound proof in the Lean formalization (`CaseObstructions.lean`) applies `sweep_sub_threshold_false` only for **n >= 9**. For n = 5, 6, 7, 8, the proof uses finite checks (Section 5, Appendix B) that enumerate all sub-threshold state vectors and verify impossibility at each specific product/multiset combination.

The Case 3a claims in `verification_claims_v2.md` are stated for "all n >= 5" but this refers to the analytical machinery being applicable from n = 5 onward. The actual application of these claims depends on whether the specific state vector under consideration has product strictly less than 4*3^(n-2) AND whether the good cycle type matches the proof's prerequisites.

The M_n witnesses achieve product = 32*3^(n-4), which IS less than 4*3^(n-2) = 36*3^(n-4), so they ARE sub-threshold. But the proof handles n <= 8 via finite case analysis, not via the general-n shadow theorem.

### 5. What happens at n = 8

At n = 8, the M_8 witness uses **non-consecutive** binary at positions {0,1,6}. The RA data stating "ALL 768 constructions at ms=(2,2,2,3,3,3,3,4) fail" is about a specific construction method (Dijkstra-style rules), not about all possible transition functions.

Whether 3CB is genuinely impossible at n = 8 with product 2592 remains an open question that requires either:
- Exhaustive search over all transition function combinations (infeasible for P = 2592), or
- A proof argument that extends the shadow/EC mechanism to non-uniform sweeps at n = 8.

### 6. The n >= 9 theorem

For n >= 9, M_n = 4*3^(n-2). Any sub-threshold system has product < 4*3^(n-2). The proof handles all cycle types:
- Sweep (|W| >= 2n): shadow cycle mirror theorem
- Odd winding, non-uniform: 4-mechanism entry conflict
- Zero winding: palindromic EC + wiggle shadow

These proofs work for ALL mover words (including non-uniform sweeps) at n >= 9. The argument does not rely on 3CB specifically -- it works for any placement of >= 3 binary processors.

### 7. Counting argument assessment

The counting argument (privilege persistence, drain bottleneck) shows exponential growth of bad-to-good ratio:

| n | P_rest | Good cycle len | Ratio |
|---|--------|---------------|-------|
| 4 | 3 | 9 | 0.3 |
| 5 | 9 | 12 | 0.75 |
| 7 | 81 | 18 | 4.5 |
| 8 | 243 | 21 | 11.6 |
| 9 | 729 | 24 | 30.4 |

This ratio is suggestive but not sufficient for a proof. Valid systems at n = 4-7 demonstrate that the counting obstruction alone does not force bad SCCs -- the detailed structure of transition functions matters.

## Conclusion

**The task as stated cannot be proved.** 3CB does NOT universally force convergence failure. Valid 3CB systems exist at n = 5, 6, 7 with product at the minimum M_n, all of which are sub-threshold.

The actual lower bound proof uses a different architecture:
1. For n >= 9: analytical proof covering all cycle types (shadow + EC + wiggle shadow)
2. For n = 5-8: finite case analysis at each specific product level
3. The 3CB/non-3CB distinction matters only for small n; for n >= 9, the proof handles all binary placements uniformly.

## Scripts

- `pa_3cb_convergence.py`: Initial counting analysis, privilege set enumeration
- `pa_3cb_convergence2.py`: Direct system construction at n=4,5
- `pa_3cb_convergence3.py`: Convergence failure rate by n, valid n=4 system analysis
- `pa_3cb_convergence4.py`: Closure failure analysis, M_5 witness search
- `pa_3cb_convergence5.py`: Witness binary position analysis, n=7 drainage
- `pa_3cb_convergence6.py`: Shadow/EC check on M_5, entry conflict verification
- `pa_3cb_convergence7.py`: Precise winding analysis, cycle length comparison
