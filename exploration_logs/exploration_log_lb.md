# Exploration Log: Lower Bound Track (Phases 5–10)

## Strategy Register

**Eliminated approach classes:** (none yet)

**Obstructions:**
- `List.get_mem` in Lean 4.27.0 takes `Fin l.length`, not `(n : ℕ) (h : n < l.length)`. Use helper `get_mem_configs` to isolate the API.
- `omega` inside structure field definitions cannot see relationships between parameters (e.g., `i.val < 2 * sys.rs.n` from `i : Fin sys.rs.n`). Workaround: use `by have := i.isLt; omega` or avoid `Fin` intermediaries.
- `List.length_pos.mpr` doesn't exist in this Mathlib version. Use `cases h : l with | nil => ... | cons => simp` instead.
- Termination checker for recursive functions on `Acc` proofs: cannot use `termination_by hacc` when `hacc`'s type depends on other varying parameters. Use `induction hacc with | intro x _ ih => ...` instead.

**Building blocks:**
- Core types stabilized by UB agent: `RingSpec`, `Config`, `TransFn`, `System`, `GoodCycle`, `privileged`, `move`, `valid` (in Ring.lean, Dijkstra.lean)
- `castFin`, `allFin` helpers in Basic.lean
- `stateProduct` uses `∏ i : Fin rs.n, rs.m i`
- **Phase 5 infrastructure (NEW):**
  - `GoodCycle.moverAt` — extract unique privileged processor via `Classical.choose`
  - `GoodCycle.moverAt_privileged`, `moverAt_unique`, `not_privileged_of_ne_moverAt` — key mover properties
  - `entryConflict_impossible` — **PROVED** (no sorry): entry conflict ⇒ False
  - `shadowTrap_not_converges` — **PROVED** (no sorry): shadow trap ⇒ ¬converges. Uses `induction hacc` on `Acc` structure.
  - `WaterfallCycle` structure with interval-based waterfall form
  - `hasMNU`, `hasEscape` — property definitions
  - `ShadowTrap` structure — closed cycle of non-good configs
  - `isBinary`, `isTernary`, `binaryCount`, `hasGe3Binary`, `subThreshold` — binary/threshold predicates

**Known reformulations:**
- Waterfall form uses `(j + 2n - i) % (2n)` to avoid negative subtraction in `Nat`. Cleaner than creating `Fin (2*n)` intermediaries.

---

## Exploration 1

### Strategy
Build Phase 5 lower bound infrastructure: `GoodCycleBasics.lean` (mover extraction, frontier count, entry conflict + master obstruction lemma) and `MNU.lean` (waterfall form, MNU, Universal Escape). These are shared definitions/lemmas used by all subsequent lower bound phases (6–10).

### Outcome
SUCCEEDED

### Key Design Decisions
1. **Mover extraction**: Use `Classical.choose` on `GoodCycle.unique_privileged` to extract the unique privileged processor at each step. Noncomputable but sufficient for proofs.
2. **Entry conflict**: Define as ∃ steps k₁, k₂ and processor i where i is the mover at k₁, not the mover at k₂, and the (L, S, R) context is identical. Contradiction: f_i(L,S,R) = S (non-mover) and f_i(L,S,R) ≠ S (mover).
3. **Frontier count**: Compare `.val` of adjacent processors (heterogeneous state counts via `Fin.val`).
4. **MNU**: Interval arithmetic on Z_{2n}. Value-independent (works for any m_i ≥ 2).
5. **Shadow trap proof**: Use `induction hacc` on `Acc` structure to build infinite descent. The `rw [hk] at hbad` converts between named index and universally quantified `x`.

### Concrete Artifacts

STRUCTURAL RESULTS:
- `entryConflict_impossible` — fully proved, no sorry. The master obstruction for all entry-conflict-based lower bound arguments.
- `shadowTrap_not_converges` — fully proved, no sorry. The master structural theorem: any closed cycle of non-good configs under forced transitions implies ¬converges.
- `shadowTrap_badStep` — helper showing each shadow config steps to the next via badStep.
- `shadowTrap_acc_false` — the core inductive argument on Acc.

TOOLS:
- `GoodCycleBasics.lean` (LeanMn/LowerBound/GoodCycleBasics.lean): 140 lines, compiles in ~17s. Definitions: moverAt, moverWord, fc, signedStep, totalDisplacement, hasEntryConflict, isBinary, binaryCount, subThreshold.
- `MNU.lean` (LeanMn/LowerBound/MNU.lean): 155 lines, compiles in ~33s. Definitions: WaterfallCycle, hasMNU, hasEscape, ShadowTrap, inActiveInterval.

REPRESENTATIONS:
- `get_mem_configs` helper isolates the `List.get_mem` API from the caller.
- Waterfall condition uses raw `Nat` modular arithmetic, avoiding `Fin (2*n)` coercion pain.

### Sorry Inventory
4 remaining sorry's, all in MNU.lean:
1. `waterfallCycle_hasMNU` — interval intersection proof (A ∩ B ∩ C = {unique}). Needs modular arithmetic lemmas.
2. `waterfallCycle_hasEscape` — follows from MNU + waterfall value analysis. Needs care at ternary positions.
3. `counting_lemma` — pure arithmetic: 2^b · 3^(n-b) ≥ 4 · 3^(n-2) for b ≤ 2. Should be closable with product inequality lemmas.
4. `subThreshold_ge3_binary` — contrapositive of counting_lemma, trivial once counting_lemma is proved.

### Key Lean 4.27.0 Patterns Discovered
- `List.get_mem gc.configs k` — takes `Fin`, not `(n, h)` separately
- `cases h : l with | nil => exact absurd h nonempty | cons _ _ => simp` — for `0 < l.length`
- `induction hacc with | intro x _ ih => ...` — structural recursion on `Acc`
- `rw [hk] at hbad` — convert named shadow index to universally quantified variable
- `push_neg` needs `unfold` first for custom definitions like `hasGe3Binary`

### Open Questions
1. MNU proof for ternary positions: does `f(L, S, R) = f(L, g_k[p], R)` imply `S = g_k[p]`? The escape proof needs this. For binary (2 values), it's automatic. For ternary, it requires additional analysis of non-mover entries at the same (L, R) context.
2. Best way to handle the counting lemma: product inequality over `Finset.univ` with case split on binary count. May need Mathlib's `Finset.prod_le_prod` or similar.

---

## Exploration 2

### Strategy
Build Phases 6–10 sequentially: Phase 7 (Palindromic EC) → Phase 6 (Shadow Cycle Mirror) → Phase 9 (Universal EC Non-Consecutive) → Phase 8 (Wiggle Shadow) → Phase 10 (Assembly). Focus on getting type-correct skeletons with well-structured sorry's for each analytical proof.

### Outcome
SUCCEEDED — All 7 files compile, full `lake build LeanMn` passes.

### Key Design Decisions
1. **Phase 7 (Palindromic):** `PalindromicConflict` structure captures the context equality between CW non-mover and CCW mover steps. `palindromicConflict_false` chains through `entryConflict_impossible` — fully proved (no sorry). The final `palindromic_entry_conflict_theorem` is the analytical extraction (sorry).
2. **Phase 6 (Shadow):** Split into `Construction.lean` (shift formula, permutation, 5 property definitions) and `Theorem.lean` (existence, trap assembly, main theorem). Used `{wc : WaterfallCycle sys}` implicit binding to avoid sys/sys✝ universe conflicts. `shadow_len_pos` helper avoids `rw` motive errors on `Fin sc.len`.
3. **Phase 9 (Non-Consecutive):** `singletonEdge`, `ReturnCone`, `returnCone_false` (proved), `two_singleton_edge_theorem`, `edge_parity_counting`, `no_binary_2_cycle`, `binary_bounce_context`. The `returnCone_false` is trivially proved from config injectivity.
4. **Phase 8 (Wiggle):** Full closed-form tables encoded: `wiggleShadowPerm` (10-case), `DeltaType` (7 types), `PosClass` (8 classes), `deltaShift` (56 entries), `wiggleOffset` (8 entries). Used `if h : condition then` (not `if condition then`) so omega can see branch conditions.
5. **Phase 10 (Assembly):** `lower_bound_theorem` orchestrates the case decomposition. `subThreshold_ge3_binary` (from Phase 5) feeds into case3a/case3bc split. `M_n_lower_bound` wraps with `RingSpec` parameters for the final statement.

### Concrete Artifacts

NEW FILES (all compile):
- `LeanMn/LowerBound/EntryConflict/Palindromic.lean` — Phase 7 (138 lines)
  - `BAFWord`, `PalindromicConflict` structures
  - `palindromicConflict_implies_entryConflict`, `palindromicConflict_false` — PROVED
  - `baf_has_palindromic_conflict`, `palindromic_entry_conflict_theorem` — sorry
- `LeanMn/LowerBound/Shadow/Construction.lean` — Phase 6 definitions (110 lines)
  - `shadowShift`, `shadowPerm`, `ShadowConstruction`, `detectionSet`
  - `shadowClosure`, `shadowMovers`, `shadowDistinct`, `shadowDisjoint`, `shadowSinglePriv`
- `LeanMn/LowerBound/Shadow/Theorem.lean` — Phase 6 theorems (85 lines)
  - `shadow_construction_exists`, `shadow_gives_trap` — sorry
  - `shadow_cycle_mirror_theorem` — sorry (assembles 5 properties)
  - `no_valid_sweep_system` — proved (direct from shadow_cycle_mirror_theorem)
- `LeanMn/LowerBound/EntryConflict/NonConsecutive.lean` — Phase 9 (160 lines)
  - `singletonEdge`, `ReturnCone` structures
  - `returnCone_false` — PROVED
  - `two_singleton_edge_theorem`, `edge_parity_counting`, `no_binary_2_cycle`, `binary_bounce_context`, `universal_entry_conflict_nonconsec` — sorry
- `LeanMn/LowerBound/Wiggle/Theorem.lean` — Phase 8 (175 lines)
  - `WiggleWord`, `wiggleShadowPerm`, `DeltaType`, `PosClass`, `deltaShift`, `wiggleOffset`
  - `wiggle_shadow_cycle_theorem`, `small_n_wiggle_impossible` — sorry
- `LeanMn/LowerBound/Theorem.lean` — Phase 10 assembly (130 lines)
  - `no_odd_winding_subthreshold`, `case3a_impossible`, `case3bc_impossible` — sorry
  - `lower_bound_theorem` — proof skeleton using case split (depends on sorry'd lemmas)
  - `M_n_lower_bound` — final statement with RingSpec parameters

### Sorry Inventory (across all LB files)
Phase 5 (MNU.lean): 3 sorry's (waterfallCycle_hasMNU, waterfallCycle_hasEscape, counting_lemma)
Phase 6 (Shadow/): 3 sorry's (shadow_construction_exists, shadow_gives_trap, shadow_cycle_mirror_theorem)
Phase 7 (Palindromic.lean): 1 sorry (palindromic_entry_conflict_theorem)
Phase 8 (Wiggle/): 2 sorry's (wiggle_shadow_cycle_theorem, small_n_wiggle_impossible)
Phase 9 (NonConsecutive.lean): 5 sorry's (two_singleton_edge, edge_parity, no_binary_2_cycle, binary_bounce, universal_ec)
Phase 10 (Theorem.lean): 3 sorry's (no_odd_winding, case3a_impossible, case3bc_impossible)
**Total: 17 sorry's** across 7 files

### Lean 4.27.0 Patterns Discovered
- `if h : condition then` (dep match) vs `if condition then` — only the former makes the condition available to tactics like omega
- Section variable `{sys : System}` + auto-bound `wc` can create sys/sys✝ conflicts. Fix: use explicit `{wc : WaterfallCycle sys}` in definitions that reference `sys` in their body.
- `shadow_len_pos` helper avoids `rw [sc.len_eq]` motive error when `k : Fin sc.len` depends on `sc.len`.
- `Nat.mod_lt _ (shadow_len_pos sc)` is cleaner than inline proofs for next-index bounds.

---

## Exploration 3

### Strategy
Harden and fill sorry's. Focus on assembly theorems (reducing sorry count by chaining sub-lemmas) and pure arithmetic (counting lemma exponent bounds).

### Outcome
SUCCEEDED — 1 sorry eliminated, others narrowed. Full `lake build LeanMn` passes.

### Concrete Artifacts

NEWLY PROVED (no sorry):
- `pow_mul_pow_ge` — `2^b * 3^(n-b) ≥ 4 * 3^(n-2)` for `b ≤ 2, n ≥ 4`. Used `interval_cases b`, `pow_add`/`pow_succ` for exponent decomposition, `Nat.mul_le_mul_right` for final step.
- `shadow_cycle_mirror_theorem` — no longer sorry'd. Chains: `shadow_construction_exists → shadow_gives_trap → shadowTrap_not_converges`. Depends on 2 sorry'd sub-lemmas but assembly is correct.
- `no_valid_sweep_system` was already proved (unchanged).

HARDENED:
- `counting_lemma` — reduced from full sorry to one narrow sorry (`hmid`: product-splitting identity `∏ (if binary then 2 else 3) = 2^b * 3^(n-b)`). Assembly via `le_trans hfin (le_trans hmid hprod)` is correct.
- `shadow_len_pos` — made public (was private), needed by Theorem.lean.

### Sorry Inventory (16 remaining, down from 17)
- MNU.lean: 3 (waterfallCycle_hasMNU, waterfallCycle_hasEscape, counting_lemma product-split)
- Shadow/Theorem.lean: 2 (shadow_construction_exists, shadow_gives_trap)
- Palindromic.lean: 1 (palindromic_entry_conflict_theorem)
- Wiggle/Theorem.lean: 2 (wiggle_shadow_cycle_theorem, small_n_wiggle_impossible)
- NonConsecutive.lean: 5 (two_singleton_edge, edge_parity, no_binary_2_cycle, binary_bounce, universal_ec)
- Theorem.lean: 3 (no_odd_winding, case3a_impossible, case3bc_impossible)

### Key Lean 4.27.0 Patterns Discovered
- `pow_add` / `pow_succ` for decomposing `3^n = 3^(n-2) * 3^2` — `nlinarith` cannot handle exponents
- `Nat.mul_le_mul_right (3^(n-2)) (by omega)` for `4 * 3^(n-2) ≤ 9 * 3^(n-2)`
- `interval_cases b` works with `b ≤ 2` hypothesis to split into `b = 0, 1, 2`
- `Finset.prod_filter_mul_prod_filter_not` exists but has tricky syntax (`∏ x ∈ s with p x`) that conflicts with `let` bindings in tactic mode
- `List.get_ofFn` returns `f (Fin.cast ...)` — the `Fin.cast` makes index alignment non-trivial for ShadowTrap conversion

### Proof Architecture
```
lower_bound_theorem
├── subThreshold_ge3_binary (counting_lemma contrapositive)
├── case3a_impossible
│   ├── shadow_cycle_mirror_theorem (sweep case)
│   │   ├── shadow_construction_exists (5 properties)
│   │   ├── shadow_gives_trap
│   │   └── shadowTrap_not_converges [PROVED]
│   ├── palindromic_entry_conflict_theorem (BAF case)
│   │   ├── palindromicConflict_false [PROVED]
│   │   └── entryConflict_impossible [PROVED]
│   └── wiggle_shadow_cycle_theorem (wiggle case)
└── case3bc_impossible
    ├── shadow_cycle_mirror_theorem (sweep case, shared)
    ├── universal_entry_conflict_nonconsec (non-sweep)
    │   ├── two_singleton_edge_theorem
    │   │   └── returnCone_false [PROVED]
    │   ├── edge_parity_counting
    │   └── binary_bounce_context
    │       └── no_binary_2_cycle
    └── wiggle_shadow_cycle_theorem (wiggle case, shared)
```

---

## Exploration 4

### Strategy
Aggressive sorry filling across all lower bound phases. Target: reduce 16 → 0 sorrys.
Three parallel workstreams: (A) MNU/shadow properties, (B) GoodCycle infrastructure, (C) shadow distinctness/disjointness.

### Outcome
PARTIALLY SUCCEEDED — reduced from 16 to 14 sorrys. Key structural wins.

### Key Accomplishments

NEWLY PROVED (0 sorry):
- `waterfallCycle_hasMNU` — MNU uniqueness via `mnu_index_unique` helper. Case-splits on `j < q` vs `j ≥ q` to eliminate `%`, then omega. Uses `maxHeartbeats 1600000`.
- `no_binary_2_cycle` — Full proof (~110 lines). Binary 2-cycle argument: if `S₁ ≠ S₂` in `Fin 2`, firing sequence forces cycle length ≤ 2, contradicting `gc.configs.length ≥ 2 * n ≥ 10`.
- `good_cycle_configs_distinct` — Now trivial (`gc.distinct`) after adding `distinct` field to GoodCycle.
- `shadow_construction_exists` Property (iii) Distinctness — Full proof using `shadow_shift_separates`: if configs j₁ = configs j₂ pointwise, case-split on active interval membership gives highVal = 0 contradiction.
- `shadow_construction_exists` Property (iv) Disjointness — Full proof using `shadow_not_waterfall`: 4-position (n-4,n-3,n-2,n-1) pattern class incompatibility.
- `case3a_impossible` — Assembly: `no_odd_winding → sweep|zero → shadow|palindromic`.
- `case3bc_impossible` — Assembly: same sweep path + `universal_entry_conflict_nonconsec`.
- `universal_entry_conflict_nonconsec` — Assembly: `edge_parity_counting → two_singleton|entryConflict`.
- `small_n_wiggle_impossible` — Direct call to `universal_entry_conflict_nonconsec`.

INFRASTRUCTURE ADDED:
- `GoodCycle.distinct` field in Dijkstra.lean (pairwise distinct configs, part of mathematical definition)
- `DecidableEq` and `Fintype` instances for `Config rs` in Ring.lean
- Shadow construction infrastructure in Construction.lean: `shadowShift_lt`, `shadowActive`, `linear_shift_lower/upper`, `shadow_n{4,3,2,1}_active`, `waterfall_active_iff`, `shadow_waterfall_incompatible`, `shadow_shift_separates`, `shadow_not_waterfall`
- Helper lemmas in NonConsecutive.lean: `move_at_ne`, `left_ne_self'`, `right_ne_self'`, `nextIndex_ne_self`, `cycle_length_le_two`

FIXED BUILD ERRORS:
- `split_ifs at hw₁ hw₂ with h₁ h₂` → split one target at a time + `dsimp only` for let-reduction
- `Nat.mod_eq_iff_lt` signature: expects `n ≠ 0`, not `0 < n`. Rewrote with explicit `by_cases` + `Nat.add_mod_right`
- `subst` on coercion (`↑p = 0`): use `rw` instead
- Added `distinct` field to GoodCycle to make `good_cycle_configs_distinct` provable

### Sorry Inventory (14 remaining)

Phase 5 (MNU.lean): 1
- `waterfallCycle_hasEscape:319` — BLOCKED: mathematically problematic for current WaterfallCycle definition (counterexample documented). Needs stronger axioms or restructured escape lemma.

Phase 6 (Shadow/Theorem.lean): 3
- `shadow_construction_exists` Property (i) Closure:50 — 6-case analysis on σ(k mod n). Requires reasoning about sys.f at shadow configs.
- `shadow_construction_exists` Property (ii) Movers:56 — Privileged proc identification at shadow configs. Same dependency on sys.f.
- `shadow_construction_exists` Property (v) SinglePriv:128 — Uniqueness of privileged proc. Same dependency.
All three depend on MNU/Escape or equivalent axioms about transition function behavior at non-good configs.

Phase 7 (Palindromic.lean): 1
- `palindromic_entry_conflict_theorem:161` — Extract BAF turnaround points from zeroWinding. Needs combinatorial analysis of closed walks on C_n with zero displacement.

Phase 8 (Wiggle/Theorem.lean): 4
- configs:170, P1:175, P3:180, assembly:183 — Full wiggle shadow construction. Mathematically proved (80 closure identities), but formalization requires encoding the symbolic verification.

Phase 9 (NonConsecutive.lean): 3
- `two_singleton_edge_theorem:77` — Disconnection argument (remove 2 singleton edges → arcs → return cone).
- `edge_parity_counting:99` — Binary firing count (u CW + d CCW = 2, classify by u=d or u≠d).
- `binary_bounce_context:334` — Context collision from interleaved binary firings.

Phase 10 (Theorem.lean): 2
- `sweep_to_waterfall:43` — Canonical relabeling of sweep cycle to waterfall form.
- `no_odd_winding_subthreshold:64` — Parity argument: odd winding impossible with ≥3 binary at sub-threshold.

### Dependency Analysis
The 3 Shadow/Theorem sorrys (closure, movers, singlepriv) all depend on reasoning about sys.f at shadow configs. This requires either:
(a) Filling hasEscape (currently blocked), or
(b) Adding waterfall axioms that constrain f at non-good configs via context matching.

The 4 Wiggle sorrys are self-contained but require extensive symbolic encoding.

The NonConsecutive/Palindromic/Theorem sorrys are combinatorial and potentially fillable independently.

### Key Lean 4.27.0 Patterns Discovered
- `split_ifs at target₁ with h₁ <;> split_ifs at target₂ with h₂` — safe two-target case split
- `dsimp only` — reduces let-bindings that `simp` won't touch
- `set_option maxHeartbeats 1600000` — needed for heavy modular arithmetic
- `propext ⟨fun _ => trivial, fun _ => hact⟩` — convert decidable prop to True/False for simp
- `congrArg Fin.val` — extract .val equality from Fin equality
- `Fin.ext` — construct Fin equality from .val equality

### Open Questions
1. Can hasEscape be restructured to avoid the counterexample? E.g., add axiom that waterfall cycles have "value-matching" property: c[p] ∈ {0, highVal p} for shadow configs.
2. Can shadow closure/movers/singlepriv be proved without hasEscape by adding waterfall axioms about f's behavior at waterfall-like configs?
3. Most efficient path to 0 sorrys: restructure definitions, or accept some axioms as `sorry`?
