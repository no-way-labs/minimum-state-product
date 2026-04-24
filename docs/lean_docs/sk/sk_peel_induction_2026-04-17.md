# SK Peel-Trajectory Induction — Lemma C attack

**Date**: 2026-04-17
**Target**: `|SK(C)| ≥ 2^(n-1)` when `L ≥ 2n+2` and ms sub-threshold.

## Status
- Empirically: (A)/(F) hold with slack at n=5..10 across many ms variants.
- n=10 (3 ms variants, L=22, |SK|=1258, (F) min=576/640, (A) max=701/764 vs bound=512). n=11 DFS did not find cycles in 10 min.
- Peel invariant `∀k ∀p. |π_p(S_k)| ≥ 2^(n-1)` holds at n=7,8,9,10. Drops per step are small (5–16).

## Strategy (A): `∃p. |π_{drop-p}(SK)| ≥ 2^(n-1)`
Implies Lemma C since `|π(S)| ≤ |S|`.

## Peel trajectory S_0 ⊇ S_1 ⊇ … ⊇ SK
- `S_0 = VC_NG = ∏V \ C`
- `S_{k+1} = S_k \ sinks(S_k)` where `sinks(S_k)` = configs with no out-neighbor in S_k under forced determinism.

## Decomposition
`|π_p(SK)| = |π_p(S_0)| − Σ_k Δπ_p(k)`

### Base case `|π_p(S_0)|`
Let `D_p = {b ∈ π_p(∏V) : full fiber ⊂ C}`. Then
`|π_p(S_0)| = |π_p(∏V)| − |D_p| = (∏_{i≠p}|V_i|) − |D_p|`.
- `|D_p| ≤ L / |V_p|` (each dead b consumes ≥ |V_p| cycle configs).
- With ms sub-threshold, `∃ i*` with `|V_{i*}| ≥ 3`. For `p ≠ i*`:
  `∏_{i≠p}|V_i| ≥ 3 · 2^{n−2} = 2^{n−1} · (3/2)`.
- **Margin**: `|π_p(S_0)| − 2^{n−1} ≥ 2^{n−2} − L/|V_p|`.
  At `V_p = 2`, n=7, L=16: margin ≥ 32 − 8 = 24. ✓

### Inductive step (OPEN)
Need: `Σ_k Δπ_p(k) ≤ 2^{n−2} − L/|V_p|`.

**Data observation** (probe_sk_peel_drop_structure):
  At k≥1, `Δπ_p(k) ≈ |{x ∈ sinks(S_k) : singleton drop-p fiber}|` (near-equality). At k=0 there are "cascaded" drops where multiple sinks share a fiber.

**Σ relation is WRONG direction** (probe_sk_charging_singletons):
  At n=7 p=0: `Σ_k σ_p(k) = 51 < 64 = Σ_k Δπ_p(k)`.
  At n=8 p=0: `Σ σ = 108 < 128 = Σ Δπ`.
  So `σ_p` is a LOWER bound on total drops, not an upper bound. Cascaded fiber coverage creates drops that σ misses.

**Charge-to-C is empty**: 0/σ_p sinks have a forced edge directly into C; 100% go to earlier peel layers. Simple charging bound `σ_p ≤ L·branching` DEAD — the bad graph is internally closed.

### What would close this?
Ruled out this session:
- (α) Charge σ_p to C via forced edge — empirically 0/σ_p charges reach C directly.
- (γ) Σ σ_p ≤ L·branching — σ_p is a lower bound on Δπ, not upper; also σ_p can exceed L.

Still open:
- (β) Invariant quantity that combines |π_p| with "cascade potential". Candidate: `Φ_p(S) = |π_p(S)| + Σ_{b} max(0, 1 - |π_p^{-1}(b) ∩ S|/θ)` for some threshold θ. Untried.
- (δ) **Recursive charging**: since forced edges go to earlier peel layers, iterate. Each sink x at layer k → target at layer j<k. Question: does the chain `x → t_1 → t_2 → …` terminate in C within bounded hops? Probe-worthy.
- (ε) **Parity / layer-size bound**: layer sizes `|X_k|` sum to `|VC_NG| − |SK|`. If singleton-sinks are `O(|X_k|/k)` or similar, total is bounded by `|VC_NG| log|VC_NG|`. Depends on layer geometry.

## Alternative route (F) dead end
`(F): ∀p. |π_p(SK ∪ C)| ≥ 2^{n−1}` holds universally at n=5..9 but does **not** imply Lemma C: gives `|SK| ≥ 2^{n−1} − L` only. Useful as auxiliary invariant, not primary.

## Dead directions ruled out this session
- Binary cube `{0,1}^n ⊆ SK ∪ C` — fails at n=6 (0/6), partial at n=7,8.
- Single `ms` universally: at n=9, ms=(2,2,3,2,3^5) gives 9/9 full binary lift; other ms give 3/9.
- Bounce CLB at n=9..12 — SK=∅ (valid system, outside Lemma C hypothesis).
- STRONG CLAIM (full binary sub-codomain ⊆ π_q(SK)) — short by 1–2 configs consistently.

## Handoff
The inductive-step bound `Σ_k #singleton-fiber-sinks ≤ margin(n, V_p, L)` is the single remaining combinatorial obligation. Peel invariant is empirically clean; base case is analytic. The reduction is sound modulo this one combinatorial lemma.

Next session: attack `σ_p` bound, ideally via a charging scheme from singleton-fiber sinks into `C` or into previously-peeled configs.

## 2026-04-17 — Session extension ("do it all")

### (δ) Recursive chain — DEAD
Probe `probe_sk_charging_singletons_2026-04-17.py` and `probe_sk_all_directions_2026-04-17.py`:
- **100% of sinks have forced-chain terminating in dead-end** (config with no determined move). Never reach C directly or via chain.
- n=7: 130/130 dead. Max chain 6. Avg 2.22.
- n=8: 256/256 dead. Max 9. Avg 3.44.
- n=9: 1018/1018 dead. Max 14. Avg 4.86.
Reason: `det` is only defined by the good cycle; off-cycle configs have no forced transitions by default. Charging-to-C fails because the chain exits `det` before reaching C.

### (ε) Layer sizes — no clean bound
Layer sizes are peaked (rise then fall). σ_p(k) correlates with layer size but no cascade-density bound like `σ_p(k) ≤ |X_k|/k` emerges.

### (β) Monotone potential — IS π_p itself
- `|π_p(S_{k+1})| ≤ |π_p(S_k)|` holds trivially (S shrinks ⟹ π shrinks).
- Empirically `|π_p(SK)| ≥ 2^{n-1}` for ALL p at n=7,8,9,10.
- Auxiliary candidates tested (pi+multi, pi-multi, pi+heavy) all monotone but all reduce to π.

### Drop decomposition (clean structural finding)
At binary p:
  `Δπ_p(k) = #singles_peeled(k) + #doubles_fully_peeled(k)`
where "singles" = sinks with 1-fiber, "doubles" = 2-fiber with both lifts peeled at step k.

| n | pi start | pi end | drops | singles | doubles |
|---|---|---|---|---|---|
| 7 | 142 | 78 | 64 | 51 (80%) | 13 |
| 8 | 286 | 158 | 128 | 108 (84%) | 20 |
| 9 | 862 | 354 | 508 | 447 (88%) | 61 |

Doubles are a minority (~12-20%) but existent — so `Σ σ_p ≤ Σ Δπ` (lower bound, unusable).

### n=11 blocked
DFS from multi-start (single-flip corners + alternating) at L=24, L=25 yields 0 cycles in 8 min. Enumeration too sparse. Conclusions rest on n=5..10.

### Trivial at binary p: `π_p(SK) ≥ |SK|/2`
Since fibers at binary p have size ≤ 2: `|SK| = n1(SK) + 2·n2(SK)`, `π_p(SK) = n1 + n2`, so `2π_p ≥ |SK|`.

Applied:
- If `|SK| ≥ 2^n`: then `π_p(SK) ≥ 2^{n-1}` automatically. But `|SK| ≥ 2^n` is STRONGER than what we're trying to prove.
- So this gives `|SK| ≥ 2^{n-1} ⟺ π_p(SK) ≥ 2^{n-1}` — circular.

### Net status
Strategy (A) reduction is sound. Peel invariant empirically clean n=5..10. **Every attempted analytical route to bound drops failed this session**:
- σ_p as upper bound on drops — FALSE (it's a lower bound).
- Charging σ_p to C — FAILS (chains dead-end).
- Layer-density — no clean rate.
- Auxiliary potential — collapses to π_p.
- Fiber identity at binary p — circular.

The inductive-step bound `Σ Δπ_p ≤ surplus` remains OPEN with no obvious structural handle.

### Alternative framings to explore next session
- **Bad-graph SCC structure**: since all chains dead-end (no good target), SK consists of configs whose "fate under any completion of det" is determined. SK = configs with NO forced move at all? Or configs in SCCs of the det-restricted graph? Re-examine definition.
- **Clouds A-side**: Lemma A gives the cycle-length contribution. Maybe Lemma C can be weakened: show `|SK ∪ C| ≥ 2^{n-1} + L` and combine with Lemma A, instead of `|SK| ≥ 2^{n-1}`.
- **Peel at a specific privileged position**: some p maximizes π_p(S_0); show drops at this p are bounded by a quantity depending on |V_p|.

## 2026-04-17 — Revisit Hamming kernels (session round 3)

Prior memory: `peel(N_1(C))` proves SK-nonempty but fails Lemma C at n=8 (min=84<128).

**Probe `probe_sk_hamming_radius_2026-04-17.py` results** (ratio = |peel|/2^(n-1)):

| n | ms | peel(N_≤1) | peel(N_≤2) | peel(N_≤3) | SK direct |
|---|---|---|---|---|---|
| 5 | (2,2,2,3,3) | 1.50 | 1.62 | 1.62 | 1.62 |
| 5 | (2,2,3,3,3) | 1.50 | 1.62 | 1.62 | 1.62 |
| 6 | (2,2,2,3,3,3) | 1.31 | 2.06 | 2.06 | 2.06 |
| 6 | (2,2,3,2,3,3) | 1.31 | 2.06 | 2.06 | 2.06 |
| 7 | (2,2,2,3⁴) | 1.00 (tight) | 2.16 | 2.22 | 2.22 |
| 7 | (2,2,3,2,3³) | 1.00 (tight) | 2.16 | 2.22 | 2.22 |
| 8 | (2,2,2,3⁵) | 0.70 ✗ | 1.94 | 2.36 | 2.36 |
| 8 | (2,2,3,2,3⁴) | 0.70 ✗ | 1.94 | 2.36 | 2.36 |
| 9 | (2,2,3,2,3⁵) | 0.49 ✗ | 1.67 | 2.63 | 2.69 |
| 9 | (2,2,2,3⁶) | 0.44 ✗ | 1.43 | 2.23 | 2.29 |
| 10 | — | DFS no cycles in 3min | — | — | 2.46 (prior) |

**Key**: `peel(N_≤2(C))` passes bound at all tested n with ratio ≥ 1.43. But `|N_≤2| ≈ L·n²` grows polynomially vs `2^{n-1}` exponential. Projected failure around n=11-12.

**Slice peel also DEAD**: `probe_sk_slice_peel_2026-04-17.py` — coord-wise slice `{c : c[p]=v}` peels down to <0.5 ratio at all tested positions. Slicing is too aggressive.

### Net net status
Multiple empirical proof-routes for Lemma C (`|SK| ≥ 2^{n-1}`) but NONE analytically closed:
- peel-trajectory invariant — empirically clean n=5..10; no inductive bound.
- peel(N_≤2(C)) — empirically clean n=5..9; no uniform k(n) works for large n.
- direct SK bound — empirically clean n=5..10; no handle.

A structural invariant is hiding but hasn't surfaced. The consistent 12-20% "cascade doubles" in drop decomposition, the dead-end forced chains, and the Hamming-radius-dependent closures all point to something non-obvious about SK's combinatorics.

Pragmatic path for Lean: SlabBridge sorry in current `CloudsTheorem.lean` is `SK.Nonempty`, not full Lemma C. Hamming-1 route CLOSES that sorry via the monotonicity argument (memory `project_sk_hamming1_discovery_2026-04-16.md`). Full Lemma C remains open research.


