/-
  LowerBound/SK/HammingTube.lean — R4 peel-direct infrastructure

  Phase A of the R4 route (`sk_peel_direct_scope_2026-04-19.md`):
  construct the Hamming-1 tube around a good cycle, intersect with
  the value-consistent non-good configs, peel to a forced-closed
  Finset, and hand it to `sk_nonempty_of_closed_forced_subset`.

  Empirical basis (2026-04-20, 164 cycles, n=5..8, sub/at/super):
  `|E_N1| − (|T_N1| − |sinks_N1|) ≥ 8`, uniformly. The analytical
  target for Phase B2' is ≥ 1; the probe overshoots 8×. No case
  splits; no routing through `sourceTripleOfStep_injective`.

  This file: definitions + bridge theorems. Research sorries are
  the two piecewise Phase B2' obligations `peelTube_nonempty_small_n`
  (sharp `32·3^(n-4)` at `n ∈ {5..8}`) and `peelTube_nonempty_large_n`
  (sharp `4·3^(n-2)` at `n ≥ 9`). The unified `< 4·3^(n-2)` form is
  refuted by `witness_n5/6/7/8`, so the split is necessary.
  Once both close, the two SK sorries in `CloudsTheorem.lean` close
  simultaneously.
-/
import LeanMn.LowerBound.SK.SinkKernel
import LeanMn.LowerBound.GoodCycleBasics

namespace LeanMn.SK

open LeanMn

variable {sys : System}

/-! ## §1. Hamming distance and N_1 ball -/

/-- Hamming distance between two configs: count of positions where
    they differ. -/
def hammingDist {rs : RingSpec} (c c' : Config rs) : ℕ :=
  (Finset.univ.filter (fun i : Fin rs.n => c i ≠ c' i)).card

@[simp] theorem hammingDist_self {rs : RingSpec} (c : Config rs) :
    hammingDist c c = 0 := by
  unfold hammingDist
  simp

theorem hammingDist_comm {rs : RingSpec} (c c' : Config rs) :
    hammingDist c c' = hammingDist c' c := by
  unfold hammingDist
  congr 1
  ext i
  simp [eq_comm]

/-- Hamming-1 ball around a single config. -/
def N_1Of {rs : RingSpec} (c : Config rs) : Finset (Config rs) :=
  Finset.univ.filter (fun c' => hammingDist c c' = 1)

theorem N_1Of_not_self {rs : RingSpec} (c : Config rs) :
    c ∉ N_1Of c := by
  unfold N_1Of
  simp [hammingDist_self]

/-- Hamming-1 ball around a Finset. -/
def N_1Set {rs : RingSpec} (S : Finset (Config rs)) : Finset (Config rs) :=
  S.biUnion N_1Of

/-- The Hamming-1 ball of the cycle, as a Finset. -/
def cycleFinset (gc : GoodCycle sys) : Finset (Config sys.rs) :=
  gc.configs.toFinset

theorem mem_cycleFinset (gc : GoodCycle sys) (c : Config sys.rs) :
    c ∈ cycleFinset gc ↔ c ∈ gc.configs := by
  unfold cycleFinset
  exact List.mem_toFinset

/-- Hamming-1 neighborhood of the cycle. -/
def N_1Tube (gc : GoodCycle sys) : Finset (Config sys.rs) :=
  N_1Set (cycleFinset gc)

/-! ## §2. Value-consistency filter -/

/-- The set of values processor `p` takes across the good cycle. -/
def valueSetTube (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    Finset (Fin (sys.rs.m p)) :=
  (Finset.univ : Finset (Fin gc.configs.length)).image
    (fun k => (gc.configs.get k) p)

/-- A config is value-consistent (VC) w.r.t. the cycle if at every
    position `p`, its value lies in the cycle's value-set at `p`. -/
def VC (gc : GoodCycle sys) (c : Config sys.rs) : Prop :=
  ∀ p : Fin sys.rs.n, c p ∈ valueSetTube gc p

instance (gc : GoodCycle sys) (c : Config sys.rs) : Decidable (VC gc c) := by
  unfold VC
  infer_instance

/-- The VC ∩ NG Finset. -/
def VC_NG (gc : GoodCycle sys) : Finset (Config sys.rs) :=
  Finset.univ.filter (fun c => VC gc c ∧ NonGood gc c)

theorem mem_VC_NG (gc : GoodCycle sys) (c : Config sys.rs) :
    c ∈ VC_NG gc ↔ VC gc c ∧ NonGood gc c := by
  unfold VC_NG
  simp

/-! ## §3. The N_1 tube intersected with VC ∩ NG — the peel input -/

/-- `T_N1` in the probe: N_1 tube intersected with VC-NG. -/
def N_1VC_NG (gc : GoodCycle sys) : Finset (Config sys.rs) :=
  N_1Tube gc ∩ VC_NG gc

theorem N_1VC_NG_subset_VC_NG (gc : GoodCycle sys) :
    N_1VC_NG gc ⊆ VC_NG gc :=
  Finset.inter_subset_right

theorem N_1VC_NG_subset_nonGood (gc : GoodCycle sys) :
    ∀ c ∈ N_1VC_NG gc, NonGood gc c := by
  intro c hc
  have : c ∈ VC_NG gc := N_1VC_NG_subset_VC_NG gc hc
  exact ((mem_VC_NG gc c).mp this).2

/-! ## §4. Peel and its forced-closure -/

/-- Peel of the N_1 tube: iterate sink-removal to the fixpoint.
    After `|Config|` iterations any descending chain has stabilized. -/
noncomputable def peelTube (gc : GoodCycle sys) : Finset (Config sys.rs) :=
  iterateRemove (detOf gc) (N_1VC_NG gc) (Fintype.card (Config sys.rs))

theorem peelTube_subset_N_1VC_NG (gc : GoodCycle sys) :
    peelTube gc ⊆ N_1VC_NG gc :=
  iterateRemove_subset (detOf gc) _ _

theorem peelTube_subset_nonGood (gc : GoodCycle sys) :
    ∀ c ∈ peelTube gc, NonGood gc c := by
  intro c hc
  exact N_1VC_NG_subset_nonGood gc c (peelTube_subset_N_1VC_NG gc hc)

/-- The peel is a fixed point of `removeOnce`. Past `|Config|`
    iterations, iterateRemove has stabilized. -/
theorem peelTube_eq_removeOnce (gc : GoodCycle sys) :
    removeOnce (detOf gc) (peelTube gc) = peelTube gc := by
  unfold peelTube
  exact iterateRemove_stabilize (detOf gc) (N_1VC_NG gc)
    (Fintype.card (Config sys.rs))
    (le_trans (Finset.card_le_univ _) (le_refl _))

/-- The peel is forced-closed: every config in the peel has a forced
    successor also in the peel. Mirrors `SK_closed` proof pattern. -/
theorem peelTube_forced_closed (gc : GoodCycle sys) :
    ∀ c ∈ peelTube gc,
      ∃ c' ∈ peelTube gc, c' ∈ forcedNeighbors (detOf gc) c := by
  intro c hc
  rw [← peelTube_eq_removeOnce gc] at hc
  simp only [removeOnce, Finset.mem_filter] at hc
  simp only [hasForcedNeighborIn, List.any_eq_true, decide_eq_true_eq] at hc
  obtain ⟨_, c', hc'_nbrs, hc'_peel⟩ := hc
  exact ⟨c', hc'_peel, hc'_nbrs⟩

/-! ## §5. B2' — the core research sorry

    (Note: `N_1VC_NG_nonempty` is derivable as a corollary from
    `peelTube_nonempty` via `peelTube_subset_N_1VC_NG`, so no standalone
    lemma is needed. We go directly to `peelTube_nonempty`.) -/

/-- **Phase B2' — core research obligation (R4 peel-direct), small-n regime.**

    The peel of `N_1 ∩ VC-NG` is nonempty at the sharp small-n
    threshold `M_n = 32·3^(n-4)` for `n ∈ {5, 6, 7, 8}`.

    Stated piecewise (n ≤ 8 / n ≥ 9) because the unified
    `stateProduct < 4·3^(n-2)` form is refuted by the small-n
    witnesses `witness_n5..8` at products `{96, 288, 864, 2592}`:
    each is valid, has `SK = ∅`, and sits in the gap
    `32·3^(n-4) ≤ product < 4·3^(n-2)`. Widening the hypothesis of
    this target lemma would move in the wrong direction of the
    deductive chain. -/
theorem peelTube_nonempty_small_n (gc : GoodCycle sys)
    (hn_lo : 5 ≤ sys.rs.n) (hn_hi : sys.rs.n ≤ 8)
    (hsub : stateProduct sys.rs < 32 * 3 ^ (sys.rs.n - 4)) :
    (peelTube gc).Nonempty := by
  sorry

/-- **Phase B2' — core research obligation (R4 peel-direct), n ≥ 9 regime.**

    The peel of `N_1 ∩ VC-NG` is nonempty at the sharp large-n
    threshold `M_n = 4·3^(n-2)` for `n ≥ 9`.

    Equivalent formulation via edge-sink margin (probe E13,
    2026-04-20, 164 cycles, margin ≥ 8 uniformly):
    `|E_N1| − (|T_N1| − |sinks_N1|) ≥ 1` on the forced-NG subgraph
    of `N_1 ∩ VC-NG`. By pigeonhole, this margin forces a cycle in
    the induced graph, so the peel is nonempty.

    Proof route: graph-counting on the N_1 tube, uniform in (n, L,
    ms, cycle structure). Does NOT require
    `sourceTripleOfStep_injective` or any cycle-triple injectivity
    claim. No case splits. Single uniform counting inequality. -/
theorem peelTube_nonempty_large_n (gc : GoodCycle sys)
    (hn : 9 ≤ sys.rs.n)
    (hsub : stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2)) :
    (peelTube gc).Nonempty := by
  sorry

/-! ## §6. Bridge to SK — consumer for CloudsTheorem -/

/-- Bridge: peel nonempty + forced-closed + NG-subset gives SK nonempty.
    This is the one-shot consumer for `sk_nonempty_small_n` and
    `sk_nonempty_large_n` in `CloudsTheorem.lean`. -/
theorem sk_nonempty_of_peelTube
    (gc : GoodCycle sys)
    (hpeel : (peelTube gc).Nonempty) :
    (SK gc).Nonempty :=
  sk_nonempty_of_closed_forced_subset gc (peelTube gc)
    hpeel
    (peelTube_subset_nonGood gc)
    (peelTube_forced_closed gc)

/-- Consumer for `sk_nonempty_small_n`: at the sharp small-n threshold
    with `n ∈ {5..8}`, `SK(C)` is nonempty via the peel tube. -/
theorem sk_nonempty_via_tube_small_n
    (gc : GoodCycle sys)
    (hn_lo : 5 ≤ sys.rs.n) (hn_hi : sys.rs.n ≤ 8)
    (hsub : stateProduct sys.rs < 32 * 3 ^ (sys.rs.n - 4)) :
    (SK gc).Nonempty :=
  sk_nonempty_of_peelTube gc
    (peelTube_nonempty_small_n gc hn_lo hn_hi hsub)

/-- Consumer for `sk_nonempty_large_n`: at the sharp large-n threshold
    with `n ≥ 9`, `SK(C)` is nonempty via the peel tube. -/
theorem sk_nonempty_via_tube_large_n
    (gc : GoodCycle sys)
    (hn : 9 ≤ sys.rs.n)
    (hsub : stateProduct sys.rs < 4 * 3 ^ (sys.rs.n - 2)) :
    (SK gc).Nonempty :=
  sk_nonempty_of_peelTube gc (peelTube_nonempty_large_n gc hn hsub)

end LeanMn.SK
