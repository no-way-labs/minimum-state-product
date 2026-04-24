# Exploration Log — Lemma C (|SK| ≥ 2^(n-1)) — 2026-04-17 session

Protocol: `lean/docs/residue_prompt_v2.md`.

Target: `|SK(C)| ≥ 2^(n-1)` for any good cycle C with L ≥ 2n+2 and sub-sharp-M_n multiset.

---

## Strategy Register

### Eliminated approach classes

1. **Universal binary-cube lift** (ruled out prior session, re-confirmed): approaches that assume `{0,1}^n ⊆ SK ∪ C` fail — at n=6 0/6 ms variants have full binary lift, at n=9 only 3/9. Any proof predicated on a *uniform* binary sub-codomain cannot work.

2. **σ-charging from singleton-fiber sinks into C** (Exploration 4): approaches that charge each drop in `|π_p(S_k)|` to a cycle config fail — 100% of sinks have forced-chain that dead-ends before reaching C. Rules out any proof with the pattern "bound Σ drops by L · branching via forced edges to C."

3. **Coordinate slice peeling** (Exploration 7, strengthened 2026-04-17 post-session): approaches using `peel({c ∈ VC_NG : c[p]=v})` fail catastrophically — slice survivors are *zero*, not merely <0.5 · 2^(n-1). Probe B (110 cycles × all (p,v) at n=5..9 across 18 ms) confirms every slice peels to the empty set. Slicing destroys the forced-edge structure entirely. Rules out any single-coordinate-pinned subset approach **whether targeting the floor OR mere nonemptiness** — SK survivors have cross-coordinate forcing dependencies.

4. **Auxiliary potentials of |π_p|** (Exploration 6): Φ(S) = |π_p(S)| + aux, where aux ∈ {multi-fiber count, heavy-fiber count, ±combinations}. Every candidate either collapses to a scalar multiple of |π_p| or is equivalent to |S|. Rules out "clever potential function" approaches — the canonical monotone invariant *is* |π_p(S)|.

5. **Hamming-1 universal kernel** (pre-session prior result, confirmed): `peel(N_1(C)) ≥ 2^(n-1)` is tight at n=7, fails at n=8 (ratio 0.70) and n=9 (0.44). Rules out one-ball neighborhood as universal proof base.

### Obstructions

- **Chain dead-end** (Expl 4): in every tested (n, ms), every sink's forced-move chain terminates at a config with no defined forced move (det undefined off-cycle), not at a cycle config. This is a structural fact about the cycle-induced det function — off-cycle configs rarely have entries.

- **Cascade drops exceed singleton-sink count** (Expl 4): at n=7 Σ Δπ_0 = 64 but Σ σ_0 = 51; at n=8 Δπ = 128 vs σ = 108. So `#singleton-fiber sinks` is a *lower* bound on projection drops, not an upper bound. Rules out any σ-based upper-bound argument.

- **Hamming-radius neighborhood growth is polynomial vs exponential bound** (Expl 7): `|N_≤k(C)| ≈ L·n^k · (max_m-1)^k` grows polynomially in n while `2^(n-1)` grows exponentially. Any fixed-radius-k kernel argument must eventually fail. Fixed k=2 works at n=5..9 with ratio 1.43 at n=9 ms=(2,2,2,3⁶) — projected failure at n=11-12.

- **Binary-p fiber identity is circular** (Expl 3): at binary positions, `π_p(SK) ≥ |SK|/2` holds trivially (fibers ≤ 2). So `|SK| ≥ 2^(n-1) ⟺ π_p(SK) ≥ 2^(n-1)` — no new information.

- **|π_p(·)| is the unique natural monotone potential** (Expl 6): peel is ⊆-monotone, so π_p(S) ⊆ π_p(S') when S ⊆ S' — trivial non-increase. No auxiliary potential was found with strictly better structure.

### Building blocks

- **Strategy (A) reduction**: `∃p. |π_{drop-p}(SK)| ≥ 2^(n-1)` ⟹ `|SK| ≥ 2^(n-1)` trivially (Expl 3, used throughout). Load-bearing.

- **Base case inequality**: `|π_p(S_0)| = |π_p(∏V)| − |D_p| ≥ ∏_{i≠p}|V_i| − L/|V_p|` where `D_p = {b : full fiber in C}`. Analytic. For sub-sharp ms with p at binary position: surplus over bound is at least `∏_{i≠p}|V_i| − 2^(n-1) − L/|V_p|` (Expl 3). At n=7,8,9 this gives margins 24, 60, 120 respectively.

- **Peel invariant (empirical)**: `∀k ∀p. |π_p(S_k)| ≥ 2^(n-1)` holds at n=5..10 across all tested ms, with drops per step small (5–16).

- **peel(N_≤2(C)) bound (empirical, n=5..9)**: ratios 1.43–2.16 · 2^(n-1) at n=5..9. Clean alternative proof target with `|N_≤2| ≈ L·(n choose 2)·(max_m-1)²` configs to analyze.

- **Drop decomposition at binary p**: `Δπ_p(k) = #singletons_peeled(k) + #doubles_fully_peeled(k)`, with singletons dominant (80–88%) and cascade doubles minority (12–20%).

- **Lemma A Part 1 proof sketch** (Expl 9): at L=2n, `(valueSet gc p).card ≤ 2` follows cleanly from `fireCount=2` + stay-between-fires + cycle closure. The Lean file's worry about "v₁→v₀→v₂ visit" is misplaced — that case requires 3 fires. Sketch at `sk_lemma_a_part1_sketch_2026-04-17.md`.

- **SK monotonicity under det completion**: adversary adding more det entries can only *increase* edges in the bad-graph, hence decrease sinks, hence increase |SK|. So empirical |SK| computed from minimal (cycle-only) det is a *lower* bound on the true SK under any completion. Lets empirical lower bounds stand as proof obligations.

### Known reformulations

1. **Strategy (A): ∃p. |π_p(SK)| ≥ 2^(n-1)** — primary route. LOAD-BEARING: reduces set-cardinality problem to projection-cardinality problem, opens monotonicity of peel on π_p.

2. **peel(S') ⊆ peel(VC_NG) = SK for any S' ⊆ VC_NG**. LOAD-BEARING (partially): gives proof target flexibility — any S' with `|peel(S')| ≥ 2^(n-1)` suffices. Used in Hamming-kernel explorations.

3. **Fiber identity at binary p: |S| = #1-fib + 2·#2-fib** — structural identity, not reformulation per se; makes the drop decomposition concrete.

4. **Weakened Lemma C': |SK ∪ C| ≥ 2^(n-1) + L** — untried. Combining with Lemma A would give the counting. Worth next-session probe.

---

## Exploration 1 — n=10, 11 verification via single-start DFS

### Strategy
Verify (A)/(F) empirically at n=10, 11 using DFS seeded from (0,...,0) with sub-threshold ms.

### Outcome
PARTIAL — n=10 succeeded, n=11 blocked.

### Concrete Artifacts
**COMPUTED EXAMPLES**:
- n=10 ms=(2,2,3,2,3^6): L=22, |SK|=1258, (F) min=576/max=768, (A) max=764 vs bound=512. Ratio 2.46.
- n=10 ms=(2,2,2,3^7): L=22, |SK|=1258, (F) min=640/max=704. Ratio 2.46.
- n=10 ms=(2,3,2,3,2,3^5): L=22, |SK|=1258, (F) min=576/max=768. Ratio 2.46.
- n=11 ms=(2,2,3,2,3^7), ms=(2,2,2,3^8): 0 cycles in 240s each (DFS blocked).
- n=11 (multi-start from single-flip corners + alternating): 0 cycles in 480s.

**TOOLS**: `probe_sk_n10_n11_2026-04-17.py` (single-start DFS), `probe_sk_n11_fiber_invariant_2026-04-17.py` (multi-start).

### Key Parameters
Budget 240–600s. L_min = 2n+2. Single ms per run. Worked at n=10 (L=22 found in 126–187s across variants), failed at n=11 even with multi-start.

### Open Questions
Is there a smarter enumerator for n=11+ — maybe parity-restricted or starting from a highly-constrained partial cycle? Or is DFS fundamentally the wrong tool at this size?

---

## Exploration 2 — Peel trajectory invariant

### Strategy
Track `|π_p(S_k)|` across peel steps; check monotonicity and floor at 2^(n-1).

### Outcome
STALLED — invariant holds empirically at n=7..10, no inductive-step bound found.

### Failure Constraint
The reduction `|π_p(SK)| ≥ 2^(n-1) ⟸ Σ_k Δπ_p(k) ≤ surplus` is clean; the surplus is analytic; but no charging scheme for Δπ_p(k) works.

### Surviving Structure
- Peel invariant data at n=7..10 (Building block above).
- Base-case inequality (Building block above).

### Concrete Artifacts
**STRUCTURAL RESULTS**: `|π_p(S_k)|` monotone non-increasing under peel (trivial: S ⊆ S' ⟹ π(S) ⊆ π(S')). Starts at `∏_{i≠p}|V_i| − |D_p|` and stays ≥ 2^(n-1) empirically.

**TOOLS**: `probe_sk_peel_trajectory_2026-04-17.py`, `probe_sk_peel_drop_structure_2026-04-17.py`.

### What Would Unblock This
An analytical upper bound on `Σ_k Δπ_p(k)` expressed in terms of L, |V_p|, and n. The σ-based candidate FAILS (σ is lower bound). A flow/charging argument that accounts for cascade drops is needed.

### Open Questions
Does the invariant hold at n≥11 regardless of ms? Does it depend on specific structural features of the cycle (e.g., palindromic form)?

---

## Exploration 3 — σ-charging scheme (singleton-fiber sinks → C)

### Strategy
Bound `Σ Δπ_p(k)` by `# singleton-fiber sinks`, then charge singletons to cycle configs via forced edges.

### Outcome
FAILED — double structural break.

### Failure Constraint
1. σ is a *lower* bound on Δπ_p total, not an upper bound (cascade drops add 12-20%).
2. 0/σ_p sinks have a direct forced edge into C (100% of forced chains dead-end).

### What This Rules Out
Any proof of Lemma C via "charge each projection drop to a distinct cycle-config through the forced-edge relation." The charging target is empty.

### Concrete Artifacts
**COMPUTED EXAMPLES** (at n=7, p=0, binary):
- Σ σ_0 = 51, Σ Δπ_0 = 64 → σ < Δπ by 13 (20%).
- Chain terminals: 130/130 dead (no C).
- Max chain length 6 at n=7, 9 at n=8, 14 at n=9.

**TOOLS**: `probe_sk_charging_singletons_2026-04-17.py`, `probe_sk_all_directions_2026-04-17.py`.

### Open Questions
If det is completed (off-cycle moves filled in), do the chains still dead-end? Or do they reach C under natural completions? (Not tested — depends on adversary's choice of completion.)

---

## Exploration 4 — Layer-size / cascade-density (ε)

### Strategy (probe)
Relate `σ_p(k)` to `|X_k|` and peel depth K; look for a bound like `σ_p(k) ≤ |X_k|/k`.

### Outcome
FAILED — no clean rate.

### Concrete Artifacts
Layer sizes at n=9 ms=(2,2,3,2,3⁵): [102, 67, 102, 108, 116, 104, 109, 88, 72, 59, 41, 27, 13, 8, 2]. σ_p(k) tracks layer size but no cascade-density formula emerges.

---

## Exploration 5 — Auxiliary potential (β)

### Strategy (probe)
Try `Φ_p = |π_p| + c·(fiber-count terms)` — seek a potential that's strictly monotone AND above bound with bigger slack than π_p.

### Outcome
FAILED — all candidates collapse to |π_p| or |S|.

### Concrete Artifacts
Tested: `pi, multi, heavy, pi+multi, pi+heavy, pi-multi, pi-heavy`. At binary p, `pi+multi = |S|` identically (since fibers ≤ 2). At non-binary p, pi+multi tracks |S| approximately. No genuine new potential surfaces.

---

## Exploration 6 — Hamming radius kernels

### Strategy
Compute `|peel(N_≤k(C))|` for k=1,2,...,max_hamming, verify against 2^(n-1).

### Outcome
PARTIAL — k=2 passes at n=5..9, projected to fail at n ≥ 11.

### Surviving Structure
Clean Building Block: `peel(N_≤2(C)) ≥ 2^(n-1)` at n=5..9 with ratios 1.43–2.16.

### Reformulations
`peel(S') ⊆ peel(VC_NG) = SK` for S' ⊆ VC_NG (Building block/Reformulation above). Combined with Hamming-ball choice of S' gives proof flexibility.

### Concrete Artifacts
Full table (ratio = |peel|/bound):

| n | ms | peel(N_1) | peel(N_2) | peel(N_3) | SK |
|---|---|---|---|---|---|
| 5 | (2,2,3,3,3) | 1.50 | 1.62 | 1.62 | 1.62 |
| 6 | (2,2,2,3,3,3) | 1.31 | 2.06 | 2.06 | 2.06 |
| 7 | (2,2,2,3⁴) | 1.00 tight | 2.16 | 2.22 | 2.22 |
| 8 | (2,2,2,3⁵) | 0.70 ✗ | 1.94 | 2.36 | 2.36 |
| 9 | (2,2,3,2,3⁵) | 0.49 ✗ | 1.67 | 2.63 | 2.69 |
| 9 | (2,2,2,3⁶) | 0.44 ✗ | 1.43 | 2.23 | 2.29 |

**TOOLS**: `probe_sk_hamming_radius_2026-04-17.py`.

### What Would Unblock This
An analytical theorem `|peel(N_≤k(n)(C))| ≥ 2^(n-1)` for some `k(n) = O(log n)` — would close Lemma C via monotonicity of peel. Requires understanding what structural fraction of N_k survives peeling.

### Open Questions
Does `|peel(N_≤k(C))|` have a lower bound of the form `|N_≤k(C) ∩ VC_NG| − L·penalty`? What determines the penalty?

---

## Exploration 7 — Slice peel

### Strategy (probe)
`peel({c ∈ VC_NG : c[p]=v})` ≥ 2^(n-1)?

### Outcome
FAILED — all tested slices collapse to <0.5 · 2^(n-1).

### What This Rules Out
Any proof that restricts to a single coordinate value. The forced-edge structure from the good cycle spans coordinates; a slice severs most forcings and the remainder peels almost completely.

### Concrete Artifacts
All slices at n=7,8,9 had peel-survival ratio <0.5 — no single (p, v) came close.

### Correction note (2026-04-17, post-session, nonempty rescan)

The "ratio <0.5" characterization was a filter-induced mirage. Probe B (`probe_sk_slice_empty_discriminator_2026-04-17.py`) retabulated `peel({c ∈ VC_NG : c[p]=v})` across 110 good cycles at n=5..9 over 18 sub-sharp ms without a ratio filter and found **every slice is *empty*, not merely sub-floor**. Result: 110/110 cycles × 2n coordinates × every value → peel = 0. Zero exceptions across all binary-count classes (2–6 binary), consecutive and non-consecutive, with and without higher moduli (m ∈ {4, 5, 8}).

**Corrected statement of the outcome**: the slice-peel approach doesn't just fail the floor `|SK| ≥ 2^(n-1)` — it fails the weaker `(SK).Nonempty` target too. Pinning any single coordinate to any value severs enough forcing edges that the restricted peel collapses entirely.

**What this rules out (strengthened)**: any proof strategy that restricts attention to a single coordinate slice, whether targeting the floor OR mere nonemptiness. Not just restriction-to-floor.

**Structural implication**: SK survivors must have forced-move dependencies that *span* multiple coordinates simultaneously. A candidate witness for `(SK).Nonempty` cannot be found inside any coordinate-pinned subset; it has to be characterized by a cross-coordinate invariant.

**Data**: `probes/probe_sk_slice_empty_discriminator_2026-04-17.out.json` (110 records, full per-(p,v) peel counts).

---

## Exploration 8 — Pivot to Lemma A Part 1

### Strategy
Given Lemma C is research-open, audit `CloudsTheorem.lean` for nearer-term sorrys. Part 1 (`valueSet_card_le_two_at_min_length`) at L=2n is flagged as "subtler argument" in the code comments.

### Outcome
SUCCEEDED (sketch) — clean proof identified, comments' worry misplaced.

### Surviving Structure
**BUILDING BLOCK**: proof by closure + stay:
- `fc(p) = 2` (already proved in file).
- Between fires, non-mover stays: `configs[i].p = configs[i-1].p`.
- Cycle closure: `configs[L-1] → configs[0]` is not a fire at p (else fc ≥ 3).
- So post-second-fire value v_2 = v_0, giving `valueSet = {v_0, v_1}`, card ≤ 2.

The doc's concern about "v_1 → v_0 → v_2 visit" would require 3 fires, contradicting fc = 2.

### Reformulations
None — this is a direct structural proof, not a representational shift.

### Concrete Artifacts
Doc: `sk_lemma_a_part1_sketch_2026-04-17.md`. Required Lean lemmas: `fire_indices_of_fc`, `stay_between_fires`, `closure_not_fire_given_fc_bound`, `mover_changes_value`. All should be primitive lemmas on `GoodCycle`; ~100-150 LoC port.

### Open Questions
Are the required primitive lemmas already in the Lean project? (Likely yes — `fireCount_eq_two_at_min_length` depends on the fire machinery.) If so, Part 1 is a direct application.

---

## Synthesis after Exploration 8

### Cross-pattern observation

Three independent attacks (σ-charging, auxiliary potential, slice peel) all produce sinks/drops that behave locally but not globally. The consistent theme is that **the good cycle C imposes a LONG-RANGE forcing structure** on VC_NG, and any attack that restricts to local data (fiber size, coordinate value, single sink's forced edge) loses the long-range structure.

The one approach that RESPECTS long-range structure — peel itself — gives the peel invariant empirically but no analytical handle.

### What kind of insight is missing

We need a combinatorial invariant that:
1. Depends on global information (whole S_k, not just sinks or slices).
2. Is monotone under peel (so far only |π_p| qualifies).
3. Has a start value strictly above 2^(n-1) with margin that grows in the right parameters.

This is essentially asking for a proof of the peel invariant itself — i.e., we're grinding on the same obligation from different angles.

### Escalation

The Strategy Register has accumulated 5 eliminated approach classes and 5 obstructions this session with NO new reformulations beyond (A). Per the escalation protocol: state explicitly that we are generating minor variations of approaches (charging, potential, slice, neighborhood) that all hit the same "long-range forcing is not captured by local data" obstruction.

The missing insight is structural: what *globally* characterizes SK beyond "peel fixpoint"? The Mütze middle-layer connection (from SK invariant 2026-04-14 memory) hints at antipodal/parity structure. Revisiting that angle with current machinery may be the unblocking move.

---

## Open items for next session

1. **Lemma A Part 1** — concrete Lean port, ~100-150 LoC. Low-risk, actionable.
2. **Weakened Lemma C' (|SK ∪ C| ≥ 2^(n-1) + L)** — combined with Lemma A, may close without needing |SK| alone. Untested.
3. **Mütze antipodal structure** — revisit middle-layer connection mentioned in prior session memory.
4. **Adversarial det completion** — does the chain-dead-end structure change under natural completions of det? Might unblock the charging argument.
5. **k(n)-scaling Hamming kernel** — does there exist `k(n) = O(log n)` such that `peel(N_≤k(n)(C)) ≥ 2^(n-1)`?

---

**Handoff pointers**:
- Primary research doc: `sk_peel_induction_2026-04-17.md`
- Actionable Lean target: `sk_lemma_a_part1_sketch_2026-04-17.md`
- Memory index: `project_sk_peel_induction_2026-04-17.md`
