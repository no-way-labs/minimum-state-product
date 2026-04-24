# Exploration Log: 3CB Context Saturation

## Strategy Register
- **Eliminated**: (none yet)
- **Obstructions**: Bottleneck ratio = bad/(cycle_len * mover_ctx) grows exponentially (~2*3^(n-2)/n). Crosses ~10 between n=7 and n=8. Middle binary fires exactly 2x per cycle (fires/m_p = 1.0), maximally constrained.
- **Building blocks**: Valid-system saturation table (n=4..7 with convergence depths). Bottleneck ratio formula. Binary-all-or-nothing valve characterization.
- **Known reformulations**: The middle binary is a "coarse all-or-nothing valve" — when it fires on a context, all 324 (at n=8) configs with that context fire identically. Cannot discriminate between far states.

---

## Exploration 1 (mixed-sweep construction, all n)

### Strategy
Measure context saturation using mixed-sweep + good-targeting across n=4..8.

### Outcome
PARTIALLY SUCCEEDED — construction fails convergence at all n, can't distinguish valid from invalid.

### Concrete Artifacts
Mixed-sweep table (all have recurrent bad SCCs, even n=4..7 where valid systems exist):

| n | product | good | bad | recurrent | drain_mid% |
|---|---------|------|-----|-----------|------------|
| 4 | 24 | 8 | 16 | 8 | 25.0% |
| 5 | 96 | 10 | 86 | 20 | 7.0% |
| 6 | 288 | 12 | 276 | 52 | 2.9% |
| 7 | 864 | 14 | 850 | 160 | 1.2% |
| 8 | 2592 | 16 | 2576 | 384 | 0.5% |

---

## Exploration 2 (valid witnesses, n=4..7 + n=8 failure)

### Strategy
Use actual valid 3CB witnesses at n=4..7 to measure true convergence depths and context usage. Compare with n=8 failure.

### Outcome
SUCCEEDED — valid system data collected with real convergence depths

### Concrete Artifacts

COMPUTED EXAMPLES — Valid-system saturation table:

| n | product | cfg/ctx | cycle | mctx | bad | depth | bottleneck | drain% | valid |
|---|---------|---------|-------|------|-----|-------|------------|--------|-------|
| 4 | 32 | 4 | 12 | 2 | 19 | 11 | 0.79 | 26.3% | YES |
| 5 | 96 | 12 | 18 | 2 | 77 | 21 | 2.14 | 15.6% | YES |
| 6 | 288 | 36 | 35 | 2 | 231 | 43 | 3.30 | 15.2% | YES |
| 7 | 864 | 108 | 52 | 2 | 789 | 65 | 7.59 | 4.7% | YES |
| 8 | 2592 | 324 | ~16 | 2 | 2576 | INF | 80.5 | N/A | NO |

Note: n=4 uses ms=(2,2,2,4) product=32 (not ms=(2,2,2,3) product=24).

STRUCTURAL RESULTS:
1. **Mover contexts locked at 2/8** for ALL n. Middle binary fires on exactly 2 context triples. Zero overlap with non-mover contexts.
2. **Middle binary fires exactly 2 times per cycle** (fires/m_p = 1.0). Maximally constrained proc.
3. **cfg/ctx grows exactly 3x per n** (adding ternary proc triples total while 8 contexts are fixed).
4. **Cycle length grows sublinearly**: 12, 18, 35, 52 for n=4..7 (~O(n)). Collapses to ~16 at n=8.
5. **Convergence depth**: 11, 21, 43, 65 for n=4..7 — roughly O(n) or O(n log n). INF at n=8.
6. **Bottleneck ratio**: 0.79, 2.14, 3.30, 7.59, 80.5 — explodes at n=8 (10.6x jump vs ~2-3x prior).

REPRESENTATIONS:
- Bottleneck = bad/(cycle_len * mover_ctx) ≈ 2*3^(n-2)/n (exponential/linear)
- The "valve saturation" model: mid binary is all-or-nothing per context. With 324 configs per context at n=8, each mover-context step must drain ~162 bad configs. Only 2 possible outputs per context.

### Key Parameters
- n=4..7: valid systems with finite convergence depth (11..65)
- n=8: INF convergence, 384 recurrent in 75 SCCs, uniform across all 8 contexts

### Open Questions
1. The bottleneck ratio jumps 10.6x at n=8 vs ~2-3x for prior steps. Is this because cycle length COLLAPSES (from 52 to ~16)? Or does the valid-system cycle length also plateau?
2. Convergence depth growth: 11, 21, 43, 65. This is roughly linear (slope ~18/step). Does it diverge at n=8?
3. The n=4 witness has product=32 not 24. Do different witnesses give different saturation measurements?
4. Can the "packing problem" (162 bad configs per context, 2 outputs) be formalized as a combinatorial impossibility?
