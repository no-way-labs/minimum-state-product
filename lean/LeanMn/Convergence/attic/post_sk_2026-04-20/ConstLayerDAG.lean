/-
  ConstLayerDAG.lean — Convergence of constant-layer (CΦ) steps

  Uses wf_of_inner_segment decomposition:
  - Inner: boundary-fixed SyntheticOuterSteps, WF via (fc, deep) lex
  - Segment: boundary-changing steps with Ψ drop, WF via psiRank

  Every cup2SyntheticOuterStep either:
  - Changes boundary → Ψ drops (bad_boundary_Ψ_drop)
  - Fixes boundary → (fc, deep) lex drops (fixed_boundary_fc_or_deep_drop)
-/
import LeanMn.Convergence.Interior
import LeanMn.Convergence.Anomalous
import LeanMn.Convergence.P0001C2Scratch
import LeanMn.Convergence.P0001CappedScratch
import LeanMn.Convergence.Pn011C1TwoScratch
import LeanMn.Convergence.SyntheticPotential
import LeanMn.Convergence.Pn1200Scratch

namespace LeanMn

/-! ### Generic well-foundedness combinator for inner/segment decomposition -/

/-- If `inner` is WF and `segment` is WF, and inner steps compose into segments,
    then their union is well-founded. -/
private theorem wf_of_inner_segment {α : Type*}
    {inner segment : α → α → Prop}
    (h_inner : WellFounded inner)
    (h_segment : WellFounded segment)
    (h_compose : ∀ {a b c : α}, inner b a → segment c b → segment c a) :
    WellFounded (fun x y => inner x y ∨ segment x y) := by
  apply WellFounded.intro
  intro a₀
  have h_seg_acc := h_segment.apply a₀
  induction h_seg_acc with
  | intro a₀ _ ih_seg =>
    suffices ∀ a₁, Acc inner a₁ →
        (∀ x, segment x a₁ → segment x a₀) →
        Acc (fun x y => inner x y ∨ segment x y) a₁ from
      this a₀ (h_inner.apply a₀) (fun x h => h)
    intro a₁ h_acc h_lift
    induction h_acc with
    | intro a₁ _ ih_inner =>
      constructor
      intro x hx
      cases hx with
      | inl h_i =>
        exact ih_inner x h_i (fun y hy => h_lift y (h_compose h_i hy))
      | inr h_s =>
        exact ih_seg x (h_lift x h_s)

/-! ### Boundary-fixed SyntheticOuterStep: WF via (fc, deep) lex -/

/-- A boundary-fixed synthetic outer step. -/
private def cup2BoundaryFixedOuterStep (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c' c : Config (cup2Spec n hn4)) : Prop :=
  cup2SyntheticOuterStep n hn4 c' c ∧
    cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c

/-- A boundary-fixed `CΦ` step. This is the fixed-boundary subrelation of the
    actual theorem target `cup2CPhiStep`. -/
private def cup2BoundaryFixedCPhiStep (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c' c : Config (cup2Spec n hn4)) : Prop :=
  cup2CPhiStep n hn4 c' c ∧
    cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c

/-- A destination carries a deep copy pair if some site in the deep interior
    band `{4, ..., n-4}` matches one of its immediate neighbors. This is the
    active/passive split used by the existing `PhiFull10`/`PhiFull11` base
    checks. -/
private def cup2HasDeepCopyPair (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) : Prop :=
  ∃ k : Fin n, 4 ≤ k.1 ∧ k.1 + 4 ≤ n ∧
    ((c k).1 = (c (left k)).1 ∨ (c k).1 = (c (right k)).1)

/-- Passive/no-copy branch complementary to `cup2HasDeepCopyPair`. -/
private def cup2NoDeepCopyPair (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) : Prop :=
  ¬ cup2HasDeepCopyPair n hn4 c

/-- Fixed-boundary bad TP step → either fc drops or deepMidHopPotential drops.
    The mover is at a deep interior position (3 ≤ i, i+2 < n for n ≥ 9).
    Deep interior TP moves have fc non-increasing (copy-neighbor property).
    When fc is constant, the step is cup2DeepMidTpZeroStep and deepMidHopPotential drops. -/
private theorem fixed_boundary_fc_or_deep_drop (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (_hstep : cup2SyntheticOuterStep n hn4 c' c)
    (_hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c) :
    cup2Fc n hn4 c' < cup2Fc n hn4 c ∨
      (cup2Fc n hn4 c' = cup2Fc n hn4 c ∧
        deepMidHopPotential n hn4 c' < deepMidHopPotential n hn4 c) := by
  rcases _hstep with ⟨hbad, htp⟩
  rcases hbad.2.2 with ⟨i, hpriv, rfl⟩
  have htpMove : cup2TpPreservingMove n hn4 c i := by
    simpa [cup2TpPreservingMove] using htp
  have hfixed6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i) =
        cup2Boundary6 n hn4 hn9 c := by
    have hdecode := congrArg (fun s : SixState => decodeSixBoundary s.1) _hfixed
    simpa [cup2BoundaryState, decodeSixBoundary_encode] using hdecode
  have hnotboundary : ¬ (i.1 ≤ 2 ∨ n - 3 ≤ i.1) := by
    intro hboundary
    exact (cup2Boundary6_changed_of_boundary_move n hn4 hn9 c i hpriv hboundary) hfixed6
  have h3 : 3 ≤ i.1 := by
    omega
  have htop : i.1 + 2 < n := by
    omega
  have hcopy :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = (c (left i)).1 ∨
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = (c (right i)).1 := by
    exact cup2TpPreserving_mid_copyNeighbor_val n hn4 c i h3 htop htpMove hpriv
  have hfc_le : cup2Fc n hn4 (move (cup2System n hn4) c i) ≤ cup2Fc n hn4 c := by
    rw [cup2Fc_move_split n hn4 c i, cup2Fc_split n hn4 c i, cup2Fc_rest_move_eq n hn4 c i]
    have hlocal :=
      localFcAfter_le_of_copyNeighbor
        (c (left i)).1 (c i).1 (c (right i)).1
        (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) hcopy
    omega
  rcases lt_or_eq_of_le hfc_le with hfc_drop | hfc_eq
  · exact Or.inl hfc_drop
  · right
    have hstepMove : step (cup2System n hn4) c (move (cup2System n hn4) c i) := by
      exact ⟨i, hpriv, rfl⟩
    rcases cup2TpPreserving_zero_fc_step_boundary_or_deep n hn4 hstepMove hfc_eq htp with
        hboundary | hdeep
    · rcases hboundary with ⟨j, hprivj, hmovej, hboundaryj⟩
      have hfixed6j :
          cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c j) =
            cup2Boundary6 n hn4 hn9 c := by
        rw [← hmovej]
        exact hfixed6
      exact False.elim <|
        (cup2Boundary6_changed_of_boundary_move n hn4 hn9 c j hprivj hboundaryj) hfixed6j
    · exact ⟨hfc_eq, cup2DeepMidTpZeroStep_potential_drop n hn4 hdeep⟩

private def fcDeepLex : Nat × Nat → Nat × Nat → Prop :=
  Prod.Lex (· < ·) (· < ·)

/-- Boundary-fixed SyntheticOuterStep is WF via (fc, deepMidHopPotential) lex. -/
private theorem cup2BoundaryFixedOuterStep_wf (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n) :
    WellFounded (cup2BoundaryFixedOuterStep n hn4 hn9) := by
  refine Subrelation.wf
    (r := InvImage fcDeepLex
      fun c => (cup2Fc n hn4 c, deepMidHopPotential n hn4 c)) ?_ ?_
  · intro c' c ⟨hstep, hfixed⟩
    rcases fixed_boundary_fc_or_deep_drop n hn4 hn9 hstep hfixed with hfc | ⟨hfc_eq, hdeep⟩
    · show InvImage fcDeepLex _ c' c
      exact Prod.Lex.left _ _ hfc
    · show InvImage fcDeepLex _ c' c
      simp only [InvImage, fcDeepLex]
      rw [hfc_eq]
      exact Prod.Lex.right _ hdeep
  · exact InvImage.wf _ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)

/-- Boundary-fixed `CΦ` steps inherit well-foundedness from the larger
    boundary-fixed synthetic-outer relation. -/
private theorem cup2BoundaryFixedCPhiStep_wf (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n) :
    WellFounded (cup2BoundaryFixedCPhiStep n hn4 hn9) := by
  refine Subrelation.wf ?_ (cup2BoundaryFixedOuterStep_wf n hn4 hn9)
  intro c' c h
  exact ⟨⟨h.1.1.1, h.1.2.1⟩, h.2⟩

/-- If a `CΦ` step changes the boundary projection, then its mover is one of the
    six visible boundary indices. This is the precise setup needed for the
    future `CΦ -> sixTupleEdge` bridge. -/
private theorem cphi_boundary_change_has_boundary_mover
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c) :
    ∃ i, privileged (cup2System n hn4) c i ∧
      c' = move (cup2System n hn4) c i ∧
      (i.1 ≤ 2 ∨ n - 3 ≤ i.1) := by
  rcases h.1.1 with ⟨_, _, i, hpriv, rfl⟩
  exact ⟨i, hpriv, rfl,
    cup2BoundaryState_changed_implies_boundary_index n hn4 hn9 c i hchange⟩

private def non617LocalClass (p : PosType) (L S R : Nat) : Prop :=
  match p.1 with
  | 0 =>
      (L = 0 ∧ S = 0 ∧ R = 1) ∨
        (L = 1 ∧ S = 0 ∧ R = 1)
  | 1 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 0 ∧ S = 1 ∧ R = 2) ∨
        (L = 0 ∧ S = 2 ∧ R = 0) ∨
        (L = 1 ∧ S = 0 ∧ R = 1) ∨
        (L = 1 ∧ S = 0 ∧ R = 2) ∨
        (L = 1 ∧ S = 2 ∧ R = 0) ∨
        (L = 1 ∧ S = 2 ∧ R = 1)
  | 2 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 0 ∧ S = 1 ∧ R = 2) ∨
        (L = 2 ∧ S = 0 ∧ R = 2) ∨
        (L = 2 ∧ S = 1 ∧ R = 2)
  | 3 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 0 ∧ S = 1 ∧ R = 2) ∨
        (L = 1 ∧ S = 0 ∧ R = 1) ∨
        (L = 1 ∧ S = 0 ∧ R = 2)
  | 4 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 0 ∧ S = 2 ∧ R = 0) ∨
        (L = 0 ∧ S = 2 ∧ R = 1) ∨
        (L = 1 ∧ S = 2 ∧ R = 0)
  | 5 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 0 ∧ S = 1 ∧ R = 1) ∨
        (L = 1 ∧ S = 0 ∧ R = 1) ∨
        (L = 2 ∧ S = 0 ∧ R = 0) ∨
        (L = 2 ∧ S = 0 ∧ R = 1)
  | _ => False

private def non617EasyClass (p : PosType) (L S R : Nat) : Prop :=
  match p.1 with
  | 1 =>
      (L = 0 ∧ S = 1 ∧ R = 2) ∨
        (L = 1 ∧ S = 0 ∧ R = 2) ∨
        (L = 1 ∧ S = 2 ∧ R = 0) ∨
        (L = 1 ∧ S = 2 ∧ R = 1)
  | 2 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 0 ∧ S = 1 ∧ R = 2)
  | 3 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 0 ∧ S = 1 ∧ R = 2) ∨
        (L = 1 ∧ S = 0 ∧ R = 1) ∨
        (L = 1 ∧ S = 0 ∧ R = 2)
  | 4 =>
      (L = 0 ∧ S = 2 ∧ R = 1) ∨
        (L = 1 ∧ S = 2 ∧ R = 0)
  | 5 =>
      L = 2 ∧ S = 0 ∧ R = 1
  | _ => False

private def non617NonnegClass (p : PosType) (L S R : Nat) : Prop :=
  match p.1 with
  | 0 => L = 0 ∧ S = 0 ∧ R = 1
  | 5 =>
      (L = 0 ∧ S = 1 ∧ R = 1) ∨
        (L = 2 ∧ S = 0 ∧ R = 0)
  | _ => False

private def non617ExceptionalClass (p : PosType) (L S R : Nat) : Prop :=
  match p.1 with
  | 0 => L = 1 ∧ S = 0 ∧ R = 1
  | 1 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 0 ∧ S = 2 ∧ R = 0) ∨
        (L = 1 ∧ S = 0 ∧ R = 1)
  | 2 =>
      (L = 2 ∧ S = 0 ∧ R = 2) ∨
        (L = 2 ∧ S = 1 ∧ R = 2)
  | 3 =>
      L = 1 ∧ S = 0 ∧ R = 1
  | 4 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 0 ∧ S = 2 ∧ R = 0)
  | 5 =>
      (L = 0 ∧ S = 1 ∧ R = 0) ∨
        (L = 1 ∧ S = 0 ∧ R = 1)
  | _ => False

private def non617ExceptionalProfileA (p : PosType) (L S R : Nat) : Prop :=
  (p = P1 ∧ ((L = 0 ∧ S = 1 ∧ R = 0) ∨ (L = 0 ∧ S = 2 ∧ R = 0))) ∨
    (p = P2 ∧ ((L = 2 ∧ S = 0 ∧ R = 2) ∨ (L = 2 ∧ S = 1 ∧ R = 2)))

private def non617ExceptionalProfileB (p : PosType) (L S R : Nat) : Prop :=
  (p = P0 ∧ L = 1 ∧ S = 0 ∧ R = 1) ∨
    (p = P1 ∧ L = 1 ∧ S = 0 ∧ R = 1)

private def non617ExceptionalProfileC (p : PosType) (L S R : Nat) : Prop :=
  p = Pn1 ∧ L = 0 ∧ S = 1 ∧ R = 0

private def non617ExceptionalProfileD (p : PosType) (L S R : Nat) : Prop :=
  (p = Pn1 ∧ L = 1 ∧ S = 0 ∧ R = 1) ∨
    (p = Pn2 ∧ ((L = 0 ∧ S = 1 ∧ R = 0) ∨ (L = 0 ∧ S = 2 ∧ R = 0))) ∨
    (p = Pn3 ∧ L = 1 ∧ S = 0 ∧ R = 1)

private theorem non617LocalClass_split
    (p : PosType) (L S R : Nat)
    (h : non617LocalClass p L S R) :
    non617EasyClass p L S R ∨
      non617NonnegClass p L S R ∨
      non617ExceptionalClass p L S R := by
  fin_cases p
  · right
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases h with h | h | h | h | h | h | h
    · right; right; exact Or.inl h
    · left; exact Or.inl h
    · right; right; exact Or.inr (Or.inl h)
    · right; right; exact Or.inr (Or.inr h)
    · left; exact Or.inr (Or.inl h)
    · left; exact Or.inr (Or.inr (Or.inl h))
    · left; exact Or.inr (Or.inr (Or.inr h))
  · rcases h with h | h | h | h
    · left; exact Or.inl h
    · left; exact Or.inr h
    · right; right; exact Or.inl h
    · right; right; exact Or.inr h
  · rcases h with h1 | h2 | h3 | h4
    · left; exact Or.inl h1
    · left; exact Or.inr (Or.inl h2)
    · left; exact Or.inr (Or.inr (Or.inl h3))
    · left; exact Or.inr (Or.inr (Or.inr h4))
  · rcases h with h | h | h | h
    · right; right; exact Or.inl h
    · right; right; exact Or.inr h
    · left; exact Or.inl h
    · left; exact Or.inr h
  · rcases h with h | h | h | h | h
    · right; right; exact Or.inl h
    · right; left; exact Or.inl h
    · right; right; exact Or.inr h
    · right; left; exact Or.inr h
    · left; exact h
  · cases h

private theorem non617ExceptionalClass_profile_split
    (p : PosType) (L S R : Nat)
    (h : non617ExceptionalClass p L S R) :
    non617ExceptionalProfileA p L S R ∨
      non617ExceptionalProfileB p L S R ∨
      non617ExceptionalProfileC p L S R ∨
      non617ExceptionalProfileD p L S R := by
  fin_cases p
  · exact Or.inr (Or.inl (Or.inl ⟨rfl, h⟩))
  · rcases h with h | h | h
    · left
      exact Or.inl ⟨rfl, Or.inl h⟩
    · left
      exact Or.inl ⟨rfl, Or.inr h⟩
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, h⟩))
  · rcases h with h | h
    · left
      exact Or.inr ⟨rfl, Or.inl h⟩
    · left
      exact Or.inr ⟨rfl, Or.inr h⟩
  · right; right; right
    exact Or.inr (Or.inr ⟨rfl, h⟩)
  · rcases h with h | h
    · right; right; right
      exact Or.inr (Or.inl ⟨rfl, Or.inl h⟩)
    · right; right; right
      exact Or.inr (Or.inl ⟨rfl, Or.inr h⟩)
  · rcases h with h | h
    · right; right; left
      exact ⟨rfl, h⟩
    · right; right; right
      exact Or.inl ⟨rfl, h⟩
  · cases h

private def non617LocalOut (p : PosType) (L S R : Nat) : Nat :=
  match p.1 with
  | 0 => TBotVal L S R
  | 1 => TLowVal L S R
  | 2 => TMidVal L S R
  | 3 => TMidVal L S R
  | 4 => THighVal L S R
  | 5 => TTopVal L S R
  | _ => S

private theorem non617EasyClass_localFc_drop
    (p : PosType) (L S R : Nat)
    (h : non617EasyClass p L S R) :
    localFcAfter L S R (non617LocalOut p L S R) < localFcBefore L S R := by
  fin_cases p
  · cases h
  · rcases h with h | h | h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
  · rcases h with h | h | h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, THighVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, THighVal]
  · rcases h with h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TTopVal]
  · cases h

private theorem non617NonnegClass_localFc_nonneg
    (p : PosType) (L S R : Nat)
    (h : non617NonnegClass p L S R) :
    localFcBefore L S R ≤ localFcAfter L S R (non617LocalOut p L S R) := by
  fin_cases p
  · rcases h with ⟨rfl, rfl, rfl⟩
    simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TBotVal]
  · cases h
  · cases h
  · cases h
  · cases h
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TTopVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TTopVal]
  · cases h

private theorem non617ExceptionalClass_localFc_drop_two
    (p : PosType) (L S R : Nat)
    (h : non617ExceptionalClass p L S R) :
    localFcAfter L S R (non617LocalOut p L S R) + 2 = localFcBefore L S R := by
  fin_cases p
  · rcases h with ⟨rfl, rfl, rfl⟩
    simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TBotVal]
  · rcases h with h | h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
  · rcases h with h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, THighVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, THighVal]
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TTopVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TTopVal]
  · cases h

private theorem non617EasyClass_localFc_drop_at_most_two
    (p : PosType) (L S R : Nat)
    (h : non617EasyClass p L S R) :
    localFcBefore L S R ≤ localFcAfter L S R (non617LocalOut p L S R) + 2 := by
  fin_cases p
  · cases h
  · rcases h with h | h | h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TLowVal]
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
  · rcases h with h | h | h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TMidVal]
  · rcases h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, THighVal]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, THighVal]
  · rcases h with h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [non617LocalOut, localFcAfter, localFcBefore, frontierBitVal, TTopVal]
  · cases h

private theorem non617LocalClass_localFc_drop_at_most_two
    (p : PosType) (L S R : Nat)
    (h : non617LocalClass p L S R) :
    localFcBefore L S R ≤ localFcAfter L S R (non617LocalOut p L S R) + 2 := by
  rcases non617LocalClass_split p L S R h with heasy | hnonneg | hexc
  · exact non617EasyClass_localFc_drop_at_most_two p L S R heasy
  · have hle := non617NonnegClass_localFc_nonneg p L S R hnonneg
    omega
  · rw [non617ExceptionalClass_localFc_drop_two p L S R hexc]

private theorem fc_drop_at_most_two_of_move_local_bound
    (n : Nat) (hn4 : 4 ≤ n)
    {c' c : Config (cup2Spec n hn4)} {i : Fin n} {out : Nat}
    (hmove : c' = move (cup2System n hn4) c i)
    (hout :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = out)
    (hlocal :
      localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 ≤
        localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 out + 2) :
    cup2Fc n hn4 c ≤ cup2Fc n hn4 c' + 2 := by
  rw [hmove, cup2Fc_move_split n hn4 c i, cup2Fc_split n hn4 c i,
    cup2Fc_rest_move_eq n hn4 c i, hout]
  omega

/- private theorem cphi_boundary_non617_fc_drop_at_most_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    cup2Fc n hn4 c ≤ cup2Fc n hn4 c' + 2 := by
  rcases cphi_boundary_non617_stateClass n hn4 hn9 h hchange hnotedge with
    h0 | h1 | h2 | hN3 | hN2 | hN1
  · have hclass :
        non617LocalClass P0
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 := by
      rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
      simpa [cup2Boundary6] using h0.2
    have hout :
        cup2OutVal n (cup2BoundaryIdx0 n hn9)
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 =
        non617LocalOut P0
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 := by
      simpa [non617LocalOut, P0] using
        cup2OutVal_boundaryIdx0 n hn9
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1
    exact fc_drop_at_most_two_of_move_local_bound n hn4 h0.1 hout
      (non617LocalClass_localFc_drop_at_most_two P0
        (c (left (cup2BoundaryIdx0 n hn9))).1
        (c (cup2BoundaryIdx0 n hn9)).1
        (c (right (cup2BoundaryIdx0 n hn9))).1 hclass)
  · have hclass :
        non617LocalClass P1
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 := by
      rw [left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
      simpa [cup2Boundary6] using h1.2
    have hout :
        cup2OutVal n (cup2BoundaryIdx1 n hn9)
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 =
        non617LocalOut P1
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 := by
      simpa [non617LocalOut, P1] using
        cup2OutVal_boundaryIdx1 n hn9
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1
    exact fc_drop_at_most_two_of_move_local_bound n hn4 h1.1 hout
      (non617LocalClass_localFc_drop_at_most_two P1
        (c (left (cup2BoundaryIdx1 n hn9))).1
        (c (cup2BoundaryIdx1 n hn9)).1
        (c (right (cup2BoundaryIdx1 n hn9))).1 hclass)
  · have hclass :
        non617LocalClass P2
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 := by
      rw [left_cup2BoundaryIdx2 n hn9]
      simpa [cup2Boundary6, stateAsFin3] using h2.2
    have hout :
        cup2OutVal n (cup2BoundaryIdx2 n hn9)
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 =
        non617LocalOut P2
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 := by
      simpa [non617LocalOut, P2] using
        cup2OutVal_boundaryIdx2 n hn9
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1
    exact fc_drop_at_most_two_of_move_local_bound n hn4 h2.1 hout
      (non617LocalClass_localFc_drop_at_most_two P2
        (c (left (cup2BoundaryIdx2 n hn9))).1
        (c (cup2BoundaryIdx2 n hn9)).1
        (c (right (cup2BoundaryIdx2 n hn9))).1 hclass)
  · have hclass :
        non617LocalClass Pn3
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 := by
      rw [right_cup2BoundaryIdxN3 n hn9]
      simpa [cup2Boundary6, stateAsFin3] using hN3.2
    have hout :
        cup2OutVal n (cup2BoundaryIdxN3 n hn9)
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 =
        non617LocalOut Pn3
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 := by
      simpa [non617LocalOut, Pn3] using
        cup2OutVal_boundaryIdxN3 n hn9
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1
    exact fc_drop_at_most_two_of_move_local_bound n hn4 hN3.1 hout
      (non617LocalClass_localFc_drop_at_most_two Pn3
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (right (cup2BoundaryIdxN3 n hn9))).1 hclass)
  · have hclass :
        non617LocalClass Pn2
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 := by
      rw [left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9]
      simpa [cup2Boundary6] using hN2.2
    have hout :
        cup2OutVal n (cup2BoundaryIdxN2 n hn9)
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 =
        non617LocalOut Pn2
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 := by
      simpa [non617LocalOut, Pn2] using
        cup2OutVal_boundaryIdxN2 n hn9
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1
    exact fc_drop_at_most_two_of_move_local_bound n hn4 hN2.1 hout
      (non617LocalClass_localFc_drop_at_most_two Pn2
        (c (left (cup2BoundaryIdxN2 n hn9))).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 hclass)
  · have hclass :
        non617LocalClass Pn1
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 := by
      rw [left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
      simpa [cup2Boundary6] using hN1.2
    have hout :
        cup2OutVal n (cup2BoundaryIdxN1 n hn9)
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 =
        non617LocalOut Pn1
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 := by
      simpa [non617LocalOut, Pn1] using
        cup2OutVal_boundaryIdxN1 n hn9
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1
    exact fc_drop_at_most_two_of_move_local_bound n hn4 hN1.1 hout
      (non617LocalClass_localFc_drop_at_most_two Pn1
        (c (left (cup2BoundaryIdxN1 n hn9))).1
        (c (cup2BoundaryIdxN1 n hn9)).1
        (c (right (cup2BoundaryIdxN1 n hn9))).1 hclass)
-/

private theorem non617LocalClass_localFc_cases
    (p : PosType) (L S R : Nat)
    (h : non617LocalClass p L S R) :
    localFcAfter L S R (non617LocalOut p L S R) < localFcBefore L S R ∨
      localFcBefore L S R ≤ localFcAfter L S R (non617LocalOut p L S R) ∨
      localFcAfter L S R (non617LocalOut p L S R) + 2 = localFcBefore L S R := by
  rcases non617LocalClass_split p L S R h with heasy | hnonneg | hexc
  · exact Or.inl (non617EasyClass_localFc_drop p L S R heasy)
  · exact Or.inr (Or.inl (non617NonnegClass_localFc_nonneg p L S R hnonneg))
  · exact Or.inr (Or.inr (non617ExceptionalClass_localFc_drop_two p L S R hexc))

private lemma cup2Boundary6_move_eq_boundarySuccP0
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
      boundarySuccP0 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idx0 n hn4 hn9 c]
  ext
  · simp [boundarySuccP0, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx0 n hn9)
    have hright : (c (right (cup2BoundaryIdx0 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx0 n hn9)
    rw [hleft, hright]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]
  · simp [boundarySuccP0]

private lemma cup2Boundary6_move_eq_boundarySuccP1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
      boundarySuccP1 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idx1 n hn4 hn9 c]
  ext
  · simp [boundarySuccP1]
  · simp [boundarySuccP1, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx1 n hn9)
    have hright : (c (right (cup2BoundaryIdx1 n hn9))).1 = (c (cup2BoundaryIdx2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdx1 n hn9)
    rw [hleft, hright]
  · simp [boundarySuccP1]
  · simp [boundarySuccP1]
  · simp [boundarySuccP1]
  · simp [boundarySuccP1]

private lemma cup2Boundary6_move_eq_boundarySuccP2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
      boundarySuccP2 (cup2Boundary6 n hn4 hn9 c)
        (stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))) := by
  rw [cup2Boundary6_move_idx2 n hn4 hn9 c]
  ext
  · simp [boundarySuccP2]
  · simp [boundarySuccP2]
  · simp [boundarySuccP2, stateAsFin3, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdx2 n hn9))).1 = (c (cup2BoundaryIdx1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdx2 n hn9)
    rw [hleft]
  · simp [boundarySuccP2]
  · simp [boundarySuccP2]
  · simp [boundarySuccP2]

private lemma cup2Boundary6_move_eq_boundarySuccPN3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
      boundarySuccPN3 (cup2Boundary6 n hn4 hn9 c)
        (stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))) := by
  rw [cup2Boundary6_move_idxN3 n hn4 hn9 c]
  ext
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3, stateAsFin3, cup2Boundary6, move_apply_self_val]
    have hright : (c (right (cup2BoundaryIdxN3 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN3 n hn9)
    rw [hright]
  · simp [boundarySuccPN3]
  · simp [boundarySuccPN3]

private lemma cup2Boundary6_move_eq_boundarySuccPN2
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
      boundarySuccPN2 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idxN2 n hn4 hn9 c]
  ext
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2]
  · simp [boundarySuccPN2, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN3 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN2 n hn9)
    have hright : (c (right (cup2BoundaryIdxN2 n hn9))).1 = (c (cup2BoundaryIdxN1 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN2 n hn9)
    rw [hleft, hright]
  · simp [boundarySuccPN2]

private lemma cup2Boundary6_move_eq_boundarySuccPN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
      boundarySuccPN1 (cup2Boundary6 n hn4 hn9 c) := by
  rw [cup2Boundary6_move_idxN1 n hn4 hn9 c]
  ext
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1]
  · simp [boundarySuccPN1, cup2Boundary6, move_apply_self_val]
    have hleft : (c (left (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdxN2 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (left_cup2BoundaryIdxN1 n hn9)
    have hright : (c (right (cup2BoundaryIdxN1 n hn9))).1 = (c (cup2BoundaryIdx0 n hn9)).1 := by
      simpa using congrArg (fun j => (c j).1) (right_cup2BoundaryIdxN1 n hn9)
    rw [hleft, hright]

private theorem non617LocalClass_P0_of_notedge
    (s : SixBoundary)
    (hchange : (boundarySuccP0 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccP0 s).encode s.encode) :
    non617LocalClass P0 s.cN1.1 s.c0.1 s.c1.1 := by
  have hclosed :
      ∀ s : SixBoundary,
        (boundarySuccP0 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccP0 s).encode s.encode →
          ((s.cN1.1 = 0 ∧ s.c0.1 = 0 ∧ s.c1.1 = 1) ∨
            (s.cN1.1 = 1 ∧ s.c0.1 = 0 ∧ s.c1.1 = 1)) := by
    native_decide
  simpa [non617LocalClass, P0] using hclosed s hchange hnotedge

private theorem non617LocalClass_P1_of_notedge
    (s : SixBoundary)
    (hchange : (boundarySuccP1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccP1 s).encode s.encode) :
    non617LocalClass P1 s.c0.1 s.c1.1 s.c2.1 := by
  have hclosed :
      ∀ s : SixBoundary,
        (boundarySuccP1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccP1 s).encode s.encode →
          ((s.c0.1 = 0 ∧ s.c1.1 = 1 ∧ s.c2.1 = 0) ∨
            (s.c0.1 = 0 ∧ s.c1.1 = 1 ∧ s.c2.1 = 2) ∨
            (s.c0.1 = 0 ∧ s.c1.1 = 2 ∧ s.c2.1 = 0) ∨
            (s.c0.1 = 1 ∧ s.c1.1 = 0 ∧ s.c2.1 = 1) ∨
            (s.c0.1 = 1 ∧ s.c1.1 = 0 ∧ s.c2.1 = 2) ∨
            (s.c0.1 = 1 ∧ s.c1.1 = 2 ∧ s.c2.1 = 0) ∨
            (s.c0.1 = 1 ∧ s.c1.1 = 2 ∧ s.c2.1 = 1)) := by
    native_decide
  simpa [non617LocalClass, P1] using hclosed s hchange hnotedge

private theorem p1_102_non617_boundary_family
    (s : SixBoundary)
    (h102 : s.c0.1 = 1 ∧ s.c1.1 = 0 ∧ s.c2.1 = 2)
    (hchange : (boundarySuccP1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccP1 s).encode s.encode) :
    s.cN1.1 = 0 ∧
      ((s.cN3.1 = 0 ∧ s.cN2.1 = 1) ∨
        (s.cN3.1 = 0 ∧ s.cN2.1 = 2) ∨
        (s.cN3.1 = 1 ∧ s.cN2.1 = 2) ∨
        (s.cN3.1 = 2 ∧ s.cN2.1 = 0) ∨
        (s.cN3.1 = 2 ∧ s.cN2.1 = 1) ∨
        (s.cN3.1 = 2 ∧ s.cN2.1 = 2)) := by
  have hclosed :
      ∀ s : SixBoundary,
        s.c0.1 = 1 ∧ s.c1.1 = 0 ∧ s.c2.1 = 2 →
        (boundarySuccP1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccP1 s).encode s.encode →
        s.cN1.1 = 0 ∧
          ((s.cN3.1 = 0 ∧ s.cN2.1 = 1) ∨
            (s.cN3.1 = 0 ∧ s.cN2.1 = 2) ∨
            (s.cN3.1 = 1 ∧ s.cN2.1 = 2) ∨
            (s.cN3.1 = 2 ∧ s.cN2.1 = 0) ∨
            (s.cN3.1 = 2 ∧ s.cN2.1 = 1) ∨
            (s.cN3.1 = 2 ∧ s.cN2.1 = 2)) := by
    native_decide
  exact hclosed s h102 hchange hnotedge

private theorem non617LocalClass_PN1_of_notedge
    (s : SixBoundary)
    (hchange : (boundarySuccPN1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode) :
    non617LocalClass Pn1 s.cN2.1 s.cN1.1 s.c0.1 := by
  have hclosed :
      ∀ s : SixBoundary,
        (boundarySuccPN1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode →
          ((s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 0) ∨
            (s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1) ∨
            (s.cN2.1 = 1 ∧ s.cN1.1 = 0 ∧ s.c0.1 = 1) ∨
            (s.cN2.1 = 2 ∧ s.cN1.1 = 0 ∧ s.c0.1 = 0) ∨
            (s.cN2.1 = 2 ∧ s.cN1.1 = 0 ∧ s.c0.1 = 1)) := by
    native_decide
  simpa [non617LocalClass, Pn1] using hclosed s hchange hnotedge

private theorem pn1_200_c1_zero_or_two
    (s : SixBoundary)
    (h200 : s.cN2.1 = 2 ∧ s.cN1.1 = 0 ∧ s.c0.1 = 0)
    (hchange : (boundarySuccPN1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode) :
    s.c1.1 = 0 ∨ s.c1.1 = 2 := by
  have hclosed :
      ∀ s : SixBoundary,
        s.cN2.1 = 2 ∧ s.cN1.1 = 0 ∧ s.c0.1 = 0 →
        (boundarySuccPN1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode →
        (s.c1.1 = 0 ∨ s.c1.1 = 2) := by
    native_decide
  exact hclosed s h200 hchange hnotedge

private theorem pn1_200_c1_two_implies_c2_two
    (s : SixBoundary)
    (h200 : s.cN2.1 = 2 ∧ s.cN1.1 = 0 ∧ s.c0.1 = 0)
    (hc1 : s.c1.1 = 2)
    (hchange : (boundarySuccPN1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode) :
    s.c2.1 = 2 := by
  have hclosed :
      ∀ s : SixBoundary,
        s.cN2.1 = 2 ∧ s.cN1.1 = 0 ∧ s.c0.1 = 0 →
        s.c1.1 = 2 →
        (boundarySuccPN1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode →
        s.c2.1 = 2 := by
    native_decide
  exact hclosed s h200 hc1 hchange hnotedge

private theorem p0_001_cN2_two_or_c2_two
    (s : SixBoundary)
    (h001 : s.cN1.1 = 0 ∧ s.c0.1 = 0 ∧ s.c1.1 = 1)
    (hchange : (boundarySuccP0 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccP0 s).encode s.encode) :
    s.cN2.1 = 2 ∨ s.c2.1 = 2 := by
  have hclosed :
      ∀ s : SixBoundary,
        s.cN1.1 = 0 ∧ s.c0.1 = 0 ∧ s.c1.1 = 1 →
        (boundarySuccP0 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccP0 s).encode s.encode →
        (s.cN2.1 = 2 ∨ s.c2.1 = 2) := by
    native_decide
  exact hclosed s h001 hchange hnotedge

private theorem pn1_011_c1_one_or_two
    (s : SixBoundary)
    (h011 : s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1)
    (hchange : (boundarySuccPN1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode) :
    s.c1.1 = 1 ∨ s.c1.1 = 2 := by
  have hclosed :
      ∀ s : SixBoundary,
        s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1 →
        (boundarySuccPN1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode →
        (s.c1.1 = 1 ∨ s.c1.1 = 2) := by
    native_decide
  exact hclosed s h011 hchange hnotedge

private theorem pn1_011_c1_one_implies_c2_two
    (s : SixBoundary)
    (h011 : s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1)
    (hc1 : s.c1.1 = 1)
    (hchange : (boundarySuccPN1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode) :
    s.c2.1 = 2 := by
  have hclosed :
      ∀ s : SixBoundary,
        s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1 →
        s.c1.1 = 1 →
        (boundarySuccPN1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode →
        s.c2.1 = 2 := by
    native_decide
  exact hclosed s h011 hc1 hchange hnotedge

private theorem pn1_011_c1_one_implies_cN3_two
    (s : SixBoundary)
    (h011 : s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1)
    (hc1 : s.c1.1 = 1)
    (hchange : (boundarySuccPN1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode) :
    s.cN3.1 = 2 := by
  have hclosed :
      ∀ s : SixBoundary,
        s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1 →
        s.c1.1 = 1 →
        (boundarySuccPN1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode →
        s.cN3.1 = 2 := by
    native_decide
  exact hclosed s h011 hc1 hchange hnotedge

private theorem pn1_011_c1_two_c2_zero_or_two_implies_cN3_two
    (s : SixBoundary)
    (h011 : s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1)
    (hc1 : s.c1.1 = 2)
    (hc2 : s.c2.1 = 0 ∨ s.c2.1 = 2)
    (hchange : (boundarySuccPN1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode) :
    s.cN3.1 = 2 := by
  have hclosed :
      ∀ s : SixBoundary,
        s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1 →
        s.c1.1 = 2 →
        (s.c2.1 = 0 ∨ s.c2.1 = 2) →
        (boundarySuccPN1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode →
        s.cN3.1 = 2 := by
    native_decide
  exact hclosed s h011 hc1 hc2 hchange hnotedge

private theorem pn1_011_c1_two_c2_one_implies_cN3_two
    (s : SixBoundary)
    (h011 : s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1)
    (hc1 : s.c1.1 = 2)
    (hc2 : s.c2.1 = 1)
    (hchange : (boundarySuccPN1 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode) :
    s.cN3.1 = 2 := by
  have hclosed :
      ∀ s : SixBoundary,
        s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1 →
        s.c1.1 = 2 →
        s.c2.1 = 1 →
        (boundarySuccPN1 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode →
        s.cN3.1 = 2 := by
    native_decide
  exact hclosed s h011 hc1 hc2 hchange hnotedge

private theorem pn1_200_c1_zero_idx0_fc_gain
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
      cup2Fc n hn4 c + 2 := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx0 n hn9)
        (c (left (cup2BoundaryIdx0 n hn9))).1
        (c (cup2BoundaryIdx0 n hn9)).1
        (c (right (cup2BoundaryIdx0 n hn9))).1 = 1 := by
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hcN1, hc0, hc1] using lookup_bot_000
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdx0 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
  rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
  unfold localFcAfter localFcBefore frontierBitVal
  simp [hcN1, hc0, hc1]
  omega

private theorem p0_001_idx0_fc_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
      cup2Fc n hn4 c := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx0 n hn9)
        (c (left (cup2BoundaryIdx0 n hn9))).1
        (c (cup2BoundaryIdx0 n hn9)).1
        (c (right (cup2BoundaryIdx0 n hn9))).1 = 1 := by
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot001 : TBotVal 0 0 1 = 1 := by native_decide
    simpa [hcN1, hc0, hc1] using hbot001
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdx0 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
  rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
  simp [localFcAfter, localFcBefore, frontierBitVal, hcN1, hc0, hc1]

private theorem lookup_low_012 : TLowVal 0 1 2 = 0 := by
  native_decide

private theorem lookup_low_102 : TLowVal 1 0 2 = 1 := by
  native_decide

private theorem p0_012_idx1_fc_down_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) + 1 =
      cup2Fc n hn4 c := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx1 n hn9)
        (c (left (cup2BoundaryIdx1 n hn9))).1
        (c (cup2BoundaryIdx1 n hn9)).1
        (c (right (cup2BoundaryIdx1 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2] using lookup_low_012
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdx1 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
  rw [left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
  simp [localFcAfter, localFcBefore, frontierBitVal, hc0, hc1, hc2]
  omega

private theorem pn1_200_c1_two_idx1_fc_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
      cup2Fc n hn4 c := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx1 n hn9)
        (c (left (cup2BoundaryIdx1 n hn9))).1
        (c (cup2BoundaryIdx1 n hn9)).1
        (c (right (cup2BoundaryIdx1 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2] using lookup_low_022
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdx1 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
  rw [left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
  simp [localFcAfter, localFcBefore, frontierBitVal, hc0, hc1, hc2]

private theorem pn1_011_idxN1_fc_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
      cup2Fc n hn4 c := by
  have hout :
      cup2OutVal n (cup2BoundaryIdxN1 n hn9)
        (c (left (cup2BoundaryIdxN1 n hn9))).1
        (c (cup2BoundaryIdxN1 n hn9)).1
        (c (right (cup2BoundaryIdxN1 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    have htop011 : TTopVal 0 1 1 = 0 := by native_decide
    simpa [hcN2, hcN1, hc0] using htop011
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdxN1 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9), hout]
  rw [left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
  simp [localFcAfter, localFcBefore, frontierBitVal, hcN2, hcN1, hc0]

private theorem pn1_200_c1_two_idx1_then_idx0_fc_gain
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Fc n hn4
        (move (cup2System n hn4)
          (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
          (cup2BoundaryIdx0 n hn9)) =
      cup2Fc n hn4 c + 2 := by
  have hfc_eq := pn1_200_c1_two_idx1_fc_eq n hn4 hn9 c hc0 hc1 hc2
  let c1' := move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)
  have hN1_ne_1 : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
    intro hEq
    have hval := congrArg Fin.val hEq
    simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
    omega
  have h0_ne_1 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
    intro hEq
    have hval := congrArg Fin.val hEq
    simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
  have hcN1' : (c1' (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hN1_ne_1]
    exact hcN1
  have hc0' : (c1' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) h0_ne_1]
    exact hc0
  have hc1' : (c1' (cup2BoundaryIdx1 n hn9)).1 = 0 := by
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2] using lookup_low_022
  have hgain :=
    pn1_200_c1_zero_idx0_fc_gain n hn4 hn9 c1' hcN1' hc0' hc1'
  simpa [c1', hfc_eq] using hgain

private theorem cycleConfig_n1_zero_n2_ne_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (t : Fin (cup2CycleLen n))
    (hN1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 0) :
    (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 := by
  have hN1' : cup2CycleVal n t.1 (cup2BoundaryIdxN1 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using hN1
  have ht1 : t.1 < n := by
    by_contra ht1
    by_cases ht2 : t.1 < 2 * n - 2
    · rw [cup2CycleVal_phase2 ht1 ht2] at hN1'
      simp [cup2BoundaryIdxN1] at hN1'
    · by_cases hboundary : t.1 = 2 * n - 2
      · rw [cup2CycleVal_phase3_boundary ht1 ht2 hboundary] at hN1'
        simp [cup2BoundaryIdxN1] at hN1'
      · rw [cup2CycleVal_phase3 ht1 ht2 hboundary] at hN1'
        have hk_ne : t.1 - (2 * n - 2) ≠ 0 := by
          have htlt : t.1 < cup2CycleLen n := t.2
          unfold cup2CycleLen at htlt
          omega
        have hk_not : ¬ (n - 1 < t.1 - (2 * n - 2)) := by
          have htlt : t.1 < cup2CycleLen n := t.2
          unfold cup2CycleLen at htlt
          omega
        simp [cup2BoundaryIdxN1, hk_ne, hk_not] at hN1'
  have hN2lt :
      cup2CycleVal n t.1 (cup2BoundaryIdxN2 n hn9).1 < 2 := by
    rw [cup2CycleVal_phase1 ht1]
    simp [cup2BoundaryIdxN2]
    split_ifs <;> omega
  have hN2' : cup2CycleVal n t.1 (cup2BoundaryIdxN2 n hn9).1 ≠ 2 := by omega
  simpa [cup2CycleConfig] using hN2'

private theorem not_mem_goodCycle_of_cN2_two_cN1_zero
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0) :
    c ∉ (cup2GoodCycle n hn4).configs := by
  intro hmem
  have hmem' : c ∈ cup2CycleConfigs n hn4 := by
    simpa [cup2GoodCycle, cup2GoodCycleOfUniquePrivileged] using hmem
  rcases List.mem_ofFn.mp hmem' with ⟨t, ht⟩
  have hN2' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
    simpa [ht] using hN2
  have hN1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    simpa [ht] using hN1
  exact cycleConfig_n1_zero_n2_ne_two n hn4 hn9 t hN1' hN2'

private theorem cycleConfig_n1_one_c0_zero_c1_ne_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (t : Fin (cup2CycleLen n))
    (hN1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (h0 : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 0) :
    (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 ≠ 1 := by
  intro h1
  have hN1' : cup2CycleVal n t.1 (cup2BoundaryIdxN1 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using hN1
  have h0' : cup2CycleVal n t.1 (cup2BoundaryIdx0 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using h0
  have h1' : cup2CycleVal n t.1 (cup2BoundaryIdx1 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using h1
  by_cases ht1 : t.1 < n
  · rw [cup2CycleVal_phase1 ht1] at h0'
    have ht0 : t.1 = 0 := by
      by_cases htz : t.1 = 0
      · exact htz
      · have hpos : 0 < t.1 := Nat.pos_of_ne_zero htz
        simp [cup2BoundaryIdx0, hpos] at h0'
    rw [cup2CycleVal_phase1 ht1] at hN1'
    simp [cup2BoundaryIdxN1, ht0] at hN1'
  · by_cases ht2 : t.1 < 2 * n - 2
    · rw [cup2CycleVal_phase2 ht1 ht2] at h0'
      have htlt : t.1 < 2 * n - 1 := by omega
      simp [cup2BoundaryIdx0, htlt] at h0'
    · by_cases hboundary : t.1 = 2 * n - 2
      · rw [cup2CycleVal_phase3_boundary ht1 ht2 hboundary] at h0'
        simp [cup2BoundaryIdx0] at h0'
      · rw [cup2CycleVal_phase3 ht1 ht2 hboundary] at h1'
        have hk_ne : t.1 - (2 * n - 2) ≠ 0 := by
          intro hk0
          apply hboundary
          omega
        have hidx1 : (cup2BoundaryIdx1 n hn9).1 = 1 := by
          simp [cup2BoundaryIdx1]
        rw [hidx1] at h1'
        by_cases hk1 : 1 < t.1 - (2 * n - 2)
        · simp [hk_ne, hk1] at h1'
        · have h1_lt : 1 < n - 1 := by omega
          simp [hk_ne, hk1, h1_lt] at h1'

private theorem not_mem_goodCycle_of_cN1_one_c0_zero_c1_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (h0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (h1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1) :
    c ∉ (cup2GoodCycle n hn4).configs := by
  intro hmem
  have hmem' : c ∈ cup2CycleConfigs n hn4 := by
    simpa [cup2GoodCycle, cup2GoodCycleOfUniquePrivileged] using hmem
  rcases List.mem_ofFn.mp hmem' with ⟨t, ht⟩
  have hN1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    simpa [ht] using hN1
  have h0' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    simpa [ht] using h0
  have h1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 = 1 := by
    simpa [ht] using h1
  exact cycleConfig_n1_one_c0_zero_c1_ne_one n hn4 hn9 t hN1' h0' h1'

private theorem cycleConfig_n1_zero_c0_zero_c2_ne_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (t : Fin (cup2CycleLen n))
    (hN1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (h0 : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 0) :
    (cup2CycleConfig n hn4 t (cup2BoundaryIdx2 n hn9)).1 ≠ 2 := by
  have hN1' : cup2CycleVal n t.1 (cup2BoundaryIdxN1 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using hN1
  have h0' : cup2CycleVal n t.1 (cup2BoundaryIdx0 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using h0
  intro h2
  have h2' : cup2CycleVal n t.1 (cup2BoundaryIdx2 n hn9).1 = 2 := by
    simpa [cup2CycleConfig] using h2
  have ht1 : t.1 < n := by
    by_contra ht1
    by_cases ht2 : t.1 < 2 * n - 2
    · rw [cup2CycleVal_phase2 ht1 ht2] at hN1'
      simp [cup2BoundaryIdxN1] at hN1'
    · by_cases hboundary : t.1 = 2 * n - 2
      · rw [cup2CycleVal_phase3_boundary ht1 ht2 hboundary] at hN1'
        simp [cup2BoundaryIdxN1] at hN1'
      · rw [cup2CycleVal_phase3 ht1 ht2 hboundary] at hN1'
        have hk_ne : t.1 - (2 * n - 2) ≠ 0 := by
          have htlt : t.1 < cup2CycleLen n := t.2
          unfold cup2CycleLen at htlt
          omega
        have hk_not : ¬ (n - 1 < t.1 - (2 * n - 2)) := by
          have htlt : t.1 < cup2CycleLen n := t.2
          unfold cup2CycleLen at htlt
          omega
        simp [cup2BoundaryIdxN1, hk_ne, hk_not] at hN1'
  rw [cup2CycleVal_phase1 ht1] at h0'
  have ht0 : t.1 = 0 := by
    by_cases htz : t.1 = 0
    · exact htz
    · have hpos : 0 < t.1 := Nat.pos_of_ne_zero htz
      simp [cup2BoundaryIdx0, hpos] at h0'
  rw [cup2CycleVal_phase1 ht1] at h2'
  simp [cup2BoundaryIdx2, ht0] at h2'

private theorem not_mem_goodCycle_of_cN1_zero_c0_zero_c2_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (h0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (h2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    c ∉ (cup2GoodCycle n hn4).configs := by
  intro hmem
  have hmem' : c ∈ cup2CycleConfigs n hn4 := by
    simpa [cup2GoodCycle, cup2GoodCycleOfUniquePrivileged] using hmem
  rcases List.mem_ofFn.mp hmem' with ⟨t, ht⟩
  have hN1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    simpa [ht] using hN1
  have h0' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    simpa [ht] using h0
  have h2' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    simpa [ht] using h2
  exact cycleConfig_n1_zero_c0_zero_c2_ne_two n hn4 hn9 t hN1' h0' h2'

private theorem cycleConfig_n1_zero_c0_one_c1_zero_c2_ne_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (t : Fin (cup2CycleLen n))
    (hN1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (h0 : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 1)
    (h1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 = 0) :
    (cup2CycleConfig n hn4 t (cup2BoundaryIdx2 n hn9)).1 ≠ 2 := by
  have hN1' : cup2CycleVal n t.1 (cup2BoundaryIdxN1 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using hN1
  have h0' : cup2CycleVal n t.1 (cup2BoundaryIdx0 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using h0
  have h1' : cup2CycleVal n t.1 (cup2BoundaryIdx1 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using h1
  intro h2
  have h2' : cup2CycleVal n t.1 (cup2BoundaryIdx2 n hn9).1 = 2 := by
    simpa [cup2CycleConfig] using h2
  have ht1 : t.1 < n := by
    by_contra ht1
    by_cases ht2 : t.1 < 2 * n - 2
    · rw [cup2CycleVal_phase2 ht1 ht2] at hN1'
      simp [cup2BoundaryIdxN1] at hN1'
    · by_cases hboundary : t.1 = 2 * n - 2
      · rw [cup2CycleVal_phase3_boundary ht1 ht2 hboundary] at hN1'
        simp [cup2BoundaryIdxN1] at hN1'
      · rw [cup2CycleVal_phase3 ht1 ht2 hboundary] at hN1'
        have hk_ne : t.1 - (2 * n - 2) ≠ 0 := by
          have htlt : t.1 < cup2CycleLen n := t.2
          unfold cup2CycleLen at htlt
          omega
        have hk_not : ¬ (n - 1 < t.1 - (2 * n - 2)) := by
          have htlt : t.1 < cup2CycleLen n := t.2
          unfold cup2CycleLen at htlt
          omega
        simp [cup2BoundaryIdxN1, hk_ne, hk_not] at hN1'
  rw [cup2CycleVal_phase1 ht1] at h0' h1' h2'
  have hpos : 0 < t.1 := by
    by_contra hnotpos
    have ht0 : t.1 = 0 := by omega
    simp [cup2BoundaryIdx0, ht0] at h0'
  have hnot_gt1 : ¬ 1 < t.1 := by
    intro hgt
    simp [cup2BoundaryIdx1, hgt] at h1'
  have ht1eq : t.1 = 1 := by omega
  simp [cup2BoundaryIdx2, ht1eq] at h2'

private theorem not_mem_goodCycle_of_cN1_zero_c0_one_c1_zero_c2_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (h0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (h1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0)
    (h2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    c ∉ (cup2GoodCycle n hn4).configs := by
  intro hmem
  have hmem' : c ∈ cup2CycleConfigs n hn4 := by
    simpa [cup2GoodCycle, cup2GoodCycleOfUniquePrivileged] using hmem
  rcases List.mem_ofFn.mp hmem' with ⟨t, ht⟩
  have hN1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    simpa [ht] using hN1
  have h0' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    simpa [ht] using h0
  have h1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 = 0 := by
    simpa [ht] using h1
  have h2' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    simpa [ht] using h2
  exact cycleConfig_n1_zero_c0_one_c1_zero_c2_ne_two n hn4 hn9 t hN1' h0' h1' h2'

private theorem cycleConfig_nN2_zero_nN1_one_c0_zero_c1_ne_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (t : Fin (cup2CycleLen n))
    (hN2 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (h0 : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 0) :
    (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 ≠ 2 := by
  have hN2' : cup2CycleVal n t.1 (cup2BoundaryIdxN2 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using hN2
  have hN1' : cup2CycleVal n t.1 (cup2BoundaryIdxN1 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using hN1
  have h0' : cup2CycleVal n t.1 (cup2BoundaryIdx0 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using h0
  intro h2
  have h2' : cup2CycleVal n t.1 (cup2BoundaryIdx1 n hn9).1 = 2 := by
    simpa [cup2CycleConfig] using h2
  by_cases ht1 : t.1 < n
  · rw [cup2CycleVal_phase1 ht1] at hN1'
    have hnot : ¬ (n - 1 < t.1) := by omega
    simp [cup2BoundaryIdxN1, hnot] at hN1'
  · by_cases ht2 : t.1 < 2 * n - 2
    · rw [cup2CycleVal_phase2 ht1 ht2] at hN2'
      have hlt : n - 2 < n - 1 := by omega
      by_cases hcond : n - 2 < 2 * n - 1 - t.1
      · simp [cup2BoundaryIdxN2, hlt, hcond] at hN2'
      · simp [cup2BoundaryIdxN2, hlt, hcond] at hN2'
    · by_cases hboundary : t.1 = 2 * n - 2
      · rw [cup2CycleVal_phase3_boundary ht1 ht2 hboundary] at hN2'
        have hlt : n - 2 < n - 1 := by omega
        have hne : n - 2 ≠ 0 := by omega
        simp [cup2BoundaryIdxN2, hlt, hne] at hN2'
      · rw [cup2CycleVal_phase3 ht1 ht2 hboundary] at h0' h2' hN2'
        have hk_ne : t.1 - (2 * n - 2) ≠ 0 := by
          intro hk0
          apply hboundary
          omega
        have hk_not_gt_one : ¬ 1 < t.1 - (2 * n - 2) := by
          intro hgt
          have h1_lt : 1 < n - 1 := by omega
          simp [cup2BoundaryIdx1, hk_ne, hgt, h1_lt] at h2'
        have hk_le_one : t.1 - (2 * n - 2) ≤ 1 := by
          omega
        by_cases hcond : n - 2 < t.1 - (2 * n - 2)
        · omega
        · have hlt : n - 2 < n - 1 := by omega
          simp [cup2BoundaryIdxN2, hk_ne, hcond, hlt] at hN2'

private theorem not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c1_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (h0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (h1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2) :
    c ∉ (cup2GoodCycle n hn4).configs := by
  intro hmem
  have hmem' : c ∈ cup2CycleConfigs n hn4 := by
    simpa [cup2GoodCycle, cup2GoodCycleOfUniquePrivileged] using hmem
  rcases List.mem_ofFn.mp hmem' with ⟨t, ht⟩
  have hN2' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    simpa [ht] using hN2
  have hN1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    simpa [ht] using hN1
  have h0' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    simpa [ht] using h0
  have h1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    simpa [ht] using h1
  exact cycleConfig_nN2_zero_nN1_one_c0_zero_c1_ne_two n hn4 hn9 t hN2' hN1' h0' h1'

private theorem cycleConfig_nN2_zero_nN1_one_c0_one_c1_ne_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (t : Fin (cup2CycleLen n))
    (hN2 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (h0 : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 1) :
    (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 ≠ 2 := by
  have hN2' : cup2CycleVal n t.1 (cup2BoundaryIdxN2 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using hN2
  have hN1' : cup2CycleVal n t.1 (cup2BoundaryIdxN1 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using hN1
  have h0' : cup2CycleVal n t.1 (cup2BoundaryIdx0 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using h0
  intro h1
  by_cases ht1 : t.1 < n
  · rw [cup2CycleVal_phase1 ht1] at hN1'
    have hnot : ¬ (n - 1 < t.1) := by omega
    simp [cup2BoundaryIdxN1, hnot] at hN1'
  · by_cases ht2 : t.1 < 2 * n - 2
    · rw [cup2CycleVal_phase2 ht1 ht2] at hN2'
      have hlt : n - 2 < n - 1 := by omega
      by_cases hcond : n - 2 < 2 * n - 1 - t.1
      · simp [cup2BoundaryIdxN2, hlt, hcond] at hN2'
      · simp [cup2BoundaryIdxN2, hlt, hcond] at hN2'
    · by_cases hboundary : t.1 = 2 * n - 2
      · rw [cup2CycleVal_phase3_boundary ht1 ht2 hboundary] at hN2'
        have hlt : n - 2 < n - 1 := by omega
        have hne : n - 2 ≠ 0 := by omega
        simp [cup2BoundaryIdxN2, hlt, hne] at hN2'
      · rw [cup2CycleVal_phase3 ht1 ht2 hboundary] at h0'
        have hk_ne : t.1 - (2 * n - 2) ≠ 0 := by
          intro hk0
          apply hboundary
          omega
        have hk_pos : 0 < t.1 - (2 * n - 2) := by omega
        simp [cup2BoundaryIdx0, hk_ne, hk_pos] at h0'

private theorem not_mem_goodCycle_of_cN2_zero_cN1_one_c0_one_c1_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (h0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (h1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2) :
    c ∉ (cup2GoodCycle n hn4).configs := by
  intro hmem
  have hmem' : c ∈ cup2CycleConfigs n hn4 := by
    simpa [cup2GoodCycle, cup2GoodCycleOfUniquePrivileged] using hmem
  rcases List.mem_ofFn.mp hmem' with ⟨t, ht⟩
  have hN2' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    simpa [ht] using hN2
  have hN1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    simpa [ht] using hN1
  have h0' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    simpa [ht] using h0
  have h1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    simpa [ht] using h1
  exact cycleConfig_nN2_zero_nN1_one_c0_one_c1_ne_two n hn4 hn9 t hN2' hN1' h0' h1'

private theorem cycleConfig_nN2_zero_nN1_one_c0_ne_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (t : Fin (cup2CycleLen n))
    (hN2 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1) :
    (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 ≠ 1 := by
  have hN2' : cup2CycleVal n t.1 (cup2BoundaryIdxN2 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using hN2
  have hN1' : cup2CycleVal n t.1 (cup2BoundaryIdxN1 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using hN1
  intro h0
  have h0' : cup2CycleVal n t.1 (cup2BoundaryIdx0 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using h0
  by_cases ht1 : t.1 < n
  · rw [cup2CycleVal_phase1 ht1] at hN1'
    have hnot : ¬ (n - 1 < t.1) := by omega
    simp [cup2BoundaryIdxN1, hnot] at hN1'
  · by_cases ht2 : t.1 < 2 * n - 2
    · rw [cup2CycleVal_phase2 ht1 ht2] at hN2'
      have hlt : n - 2 < n - 1 := by omega
      by_cases hcond : n - 2 < 2 * n - 1 - t.1
      · simp [cup2BoundaryIdxN2, hlt, hcond] at hN2'
      · simp [cup2BoundaryIdxN2, hlt, hcond] at hN2'
    · by_cases hboundary : t.1 = 2 * n - 2
      · rw [cup2CycleVal_phase3_boundary ht1 ht2 hboundary] at hN2'
        have hlt : n - 2 < n - 1 := by omega
        have hne : n - 2 ≠ 0 := by omega
        simp [cup2BoundaryIdxN2, hlt, hne] at hN2'
      · rw [cup2CycleVal_phase3 ht1 ht2 hboundary] at hN2' h0'
        have hk_ne : t.1 - (2 * n - 2) ≠ 0 := by
          intro hk0
          apply hboundary
          omega
        have hk_pos : 0 < t.1 - (2 * n - 2) := by omega
        have hk_big : n - 2 < t.1 - (2 * n - 2) := by
          by_cases hcond : n - 2 < t.1 - (2 * n - 2)
          · exact hcond
          · have hlt : n - 2 < n - 1 := by omega
            simp [cup2BoundaryIdxN2, hk_ne, hcond, hlt] at hN2'
        simp [cup2BoundaryIdx0, hk_ne, hk_pos] at h0'

private theorem not_mem_goodCycle_of_cN2_zero_cN1_one_c0_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (h0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1) :
    c ∉ (cup2GoodCycle n hn4).configs := by
  intro hmem
  have hmem' : c ∈ cup2CycleConfigs n hn4 := by
    simpa [cup2GoodCycle, cup2GoodCycleOfUniquePrivileged] using hmem
  rcases List.mem_ofFn.mp hmem' with ⟨t, ht⟩
  have hN2' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    simpa [ht] using hN2
  have hN1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    simpa [ht] using hN1
  have h0' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    simpa [ht] using h0
  exact cycleConfig_nN2_zero_nN1_one_c0_ne_one n hn4 hn9 t hN2' hN1' h0'

private theorem cycleConfig_nN2_zero_nN1_one_c0_zero_c2_ne_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (t : Fin (cup2CycleLen n))
    (hN2 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (h0 : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 0) :
    (cup2CycleConfig n hn4 t (cup2BoundaryIdx2 n hn9)).1 ≠ 2 := by
  have hN2' : cup2CycleVal n t.1 (cup2BoundaryIdxN2 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using hN2
  have hN1' : cup2CycleVal n t.1 (cup2BoundaryIdxN1 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using hN1
  have h0' : cup2CycleVal n t.1 (cup2BoundaryIdx0 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using h0
  intro h2
  have h2' : cup2CycleVal n t.1 (cup2BoundaryIdx2 n hn9).1 = 2 := by
    simpa [cup2CycleConfig] using h2
  by_cases ht1 : t.1 < n
  · rw [cup2CycleVal_phase1 ht1] at hN1'
    have hnot : ¬ (n - 1 < t.1) := by omega
    simp [cup2BoundaryIdxN1, hnot] at hN1'
  · by_cases ht2 : t.1 < 2 * n - 2
    · rw [cup2CycleVal_phase2 ht1 ht2] at hN2'
      have hlt : n - 2 < n - 1 := by omega
      by_cases hcond : n - 2 < 2 * n - 1 - t.1
      · simp [cup2BoundaryIdxN2, hlt, hcond] at hN2'
      · simp [cup2BoundaryIdxN2, hlt, hcond] at hN2'
    · by_cases hboundary : t.1 = 2 * n - 2
      · rw [cup2CycleVal_phase3_boundary ht1 ht2 hboundary] at hN2'
        have hlt : n - 2 < n - 1 := by omega
        have hne : n - 2 ≠ 0 := by omega
        simp [cup2BoundaryIdxN2, hlt, hne] at hN2'
      · rw [cup2CycleVal_phase3 ht1 ht2 hboundary] at hN2' h0' h2'
        have hk_ne : t.1 - (2 * n - 2) ≠ 0 := by
          intro hk0
          apply hboundary
          omega
        have hk_pos : 0 < t.1 - (2 * n - 2) := by omega
        have hcond : n - 2 < t.1 - (2 * n - 2) := by
          by_cases hcond : n - 2 < t.1 - (2 * n - 2)
          · exact hcond
          · have hlt : n - 2 < n - 1 := by omega
            simp [cup2BoundaryIdxN2, hk_ne, hcond, hlt] at hN2'
        have hlt2 : 2 < t.1 - (2 * n - 2) := by omega
        simp [cup2BoundaryIdx0, cup2BoundaryIdx2, hk_ne, hk_pos, hlt2] at h0' h2'

private theorem not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c2_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (h0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (h2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    c ∉ (cup2GoodCycle n hn4).configs := by
  intro hmem
  have hmem' : c ∈ cup2CycleConfigs n hn4 := by
    simpa [cup2GoodCycle, cup2GoodCycleOfUniquePrivileged] using hmem
  rcases List.mem_ofFn.mp hmem' with ⟨t, ht⟩
  have hN2' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    simpa [ht] using hN2
  have hN1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    simpa [ht] using hN1
  have h0' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    simpa [ht] using h0
  have h2' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    simpa [ht] using h2
  exact cycleConfig_nN2_zero_nN1_one_c0_zero_c2_ne_two n hn4 hn9 t hN2' hN1' h0' h2'

private theorem cycleConfig_nN2_zero_nN1_zero_c0_one_c1_ne_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (t : Fin (cup2CycleLen n))
    (hN2 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (h0 : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 1) :
    (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 ≠ 2 := by
  have hN2' : cup2CycleVal n t.1 (cup2BoundaryIdxN2 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using hN2
  have hN1' : cup2CycleVal n t.1 (cup2BoundaryIdxN1 n hn9).1 = 0 := by
    simpa [cup2CycleConfig] using hN1
  have h0' : cup2CycleVal n t.1 (cup2BoundaryIdx0 n hn9).1 = 1 := by
    simpa [cup2CycleConfig] using h0
  intro h1
  have h1' : cup2CycleVal n t.1 (cup2BoundaryIdx1 n hn9).1 = 2 := by
    simpa [cup2CycleConfig] using h1
  by_cases ht1 : t.1 < n
  · rw [cup2CycleVal_phase1 ht1] at h0' h1'
    have hpos : 0 < t.1 := by
      by_contra hnotpos
      have ht0 : t.1 = 0 := by omega
      simp [cup2BoundaryIdx0, ht0] at h0'
    have hnot_gt1 : ¬ 1 < t.1 := by
      intro hgt
      simp [cup2BoundaryIdx1, hgt] at h1'
    have ht1eq : t.1 = 1 := by omega
    simp [cup2BoundaryIdx1, ht1eq] at h1'
  · by_cases ht2 : t.1 < 2 * n - 2
    · rw [cup2CycleVal_phase2 ht1 ht2] at hN1'
      simp [cup2BoundaryIdxN1] at hN1'
    · by_cases hboundary : t.1 = 2 * n - 2
      · rw [cup2CycleVal_phase3_boundary ht1 ht2 hboundary] at hN1'
        simp [cup2BoundaryIdxN1] at hN1'
      · rw [cup2CycleVal_phase3 ht1 ht2 hboundary] at h0'
        have hk_ne : t.1 - (2 * n - 2) ≠ 0 := by
          intro hk0
          apply hboundary
          omega
        have hk_pos : 0 < t.1 - (2 * n - 2) := by omega
        simp [cup2BoundaryIdx0, hk_ne, hk_pos] at h0'

private theorem not_mem_goodCycle_of_cN2_zero_cN1_zero_c0_one_c1_two
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (h0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (h1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2) :
    c ∉ (cup2GoodCycle n hn4).configs := by
  intro hmem
  have hmem' : c ∈ cup2CycleConfigs n hn4 := by
    simpa [cup2GoodCycle, cup2GoodCycleOfUniquePrivileged] using hmem
  rcases List.mem_ofFn.mp hmem' with ⟨t, ht⟩
  have hN2' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    simpa [ht] using hN2
  have hN1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    simpa [ht] using hN1
  have h0' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    simpa [ht] using h0
  have h1' : (cup2CycleConfig n hn4 t (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    simpa [ht] using h1
  exact cycleConfig_nN2_zero_nN1_zero_c0_one_c1_ne_two n hn4 hn9 t hN2' hN1' h0' h1'

/- private theorem p2_211_idx2_badStep_post
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 1) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx2] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx2] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    exact not_mem_goodCycle_of_cN2_zero_cN1_zero_c0_one_c1_two n hn4 hn9 hN2' hN1' h0' h1'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9, right_cup2BoundaryIdx2_eq_idx3 n hn9]
    have hmid : TMidVal 2 1 1 = 0 := by native_decide
    simpa [hc1, hc2, hc3, hmid] using (show (0 : Nat) ≠ 1 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx2 n hn9, hpriv, rfl⟩⟩

private theorem p3_100_idx3_badStep_post
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 0) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2Idx3 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2Idx3 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval : n - 2 = 3 := by
          simpa [cup2BoundaryIdxN2, cup2Idx3] using congrArg Fin.val hEq
        omega
        omega
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval : n - 1 = 3 := by
          simpa [cup2BoundaryIdxN1, cup2Idx3] using congrArg Fin.val hEq
        omega
        omega
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2Idx3] at hval
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2Idx3] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    exact not_mem_goodCycle_of_cN2_zero_cN1_zero_c0_one_c1_two n hn4 hn9 hN2' hN1' h0' h1'
  have h0i : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
  have h1i : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
  have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx3]
    omega
  have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx3]
    omega
  have hpriv : privileged (cup2System n hn4) c (cup2Idx3 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal, if_neg h0i, if_neg h1i, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx3 n hn9))).1 = 1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      exact hc2
    have hright : (c (right (cup2Idx3 n hn9))).1 = 0 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
      exact hc4
    simpa [hleft, hc3, hright, lookup_mid_100] using (show (1 : Nat) ≠ 0 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2Idx3 n hn9, hpriv, rfl⟩⟩

private theorem p4_022_idx4_badStep_post
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 2)
    (hc5 : (c (cup2Idx5 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2Idx4 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2Idx4 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2Idx4 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval : n - 2 = 4 := by
          simpa [cup2BoundaryIdxN2, cup2Idx4] using congrArg Fin.val hEq
        omega
        omega
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval : n - 1 = 4 := by
          simpa [cup2BoundaryIdxN1, cup2Idx4] using congrArg Fin.val hEq
        omega
        omega
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2Idx4 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2Idx4] at hval
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2Idx4 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2Idx4] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    exact not_mem_goodCycle_of_cN2_zero_cN1_zero_c0_one_c1_two n hn4 hn9 hN2' hN1' h0' h1'
  have h0i : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
  have h1i : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
  have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx4]
    omega
  have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx4]
    omega
  have hpriv : privileged (cup2System n hn4) c (cup2Idx4 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal, if_neg h0i, if_neg h1i, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx4 n hn9))).1 = 0 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
      exact hc3
    have hright : (c (right (cup2Idx4 n hn9))).1 = 2 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
      exact hc5
    simpa [hleft, hc4, hright, lookup_mid_022] using (show (0 : Nat) ≠ 2 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2Idx4 n hn9, hpriv, rfl⟩⟩

private theorem pn1_011_post_case00_normalizes
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (d : Config (cup2Spec n hn4))
    (hbad : d ∉ (cup2GoodCycle n hn4).configs)
    (hdN2 : (d (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hd1 : (d (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hd2 : (d (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hd3 : (d (cup2Idx3 n hn9)).1 = 0)
    (hd4 : (d (cup2Idx4 n hn9)).1 = 0) :
    let d1 := move (cup2System n hn4) d (cup2Idx3 n hn9)
    cup2TpReachable n hn4 d d1 ∧
      cup2Fc n hn4 d1 = cup2Fc n hn4 d ∧
      (d1 (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      (d1 (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
      (d1 (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      (d1 (cup2BoundaryIdx1 n hn9)).1 = 2 ∧
      (d1 (cup2BoundaryIdx2 n hn9)).1 = 1 ∧
      (d1 (cup2Idx3 n hn9)).1 = 1 := by
  let d1 := move (cup2System n hn4) d (cup2Idx3 n hn9)
  have hbad1 := p3_100_idx3_badStep_post n hn4 hn9 d hbad hdN2 hdN1 hd0 hd1 hd2 hd3 hd4
  have htp1 := tmp_p3_100_idx3_tpPreserving n hn4 hn9 d hd2 hd3 hd4
  have hreach1 : cup2TpReachable n hn4 d d1 :=
    cup2TpReachable_step n hn4 ⟨hbad1, by simpa [cup2TpPreservingMove] using htp1⟩
  have hfc1 : cup2Fc n hn4 d1 = cup2Fc n hn4 d := by
    simpa [d1] using p3_100_idx3_fc_eq n hn4 hn9 d hd2 hd3 hd4
  have hdN2' : (d1 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2Idx3] at hval
      omega
    rw [show d1 = move (cup2System n hn4) d (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hdN2
  have hdN1' : (d1 (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2Idx3] at hval
      omega
    rw [show d1 = move (cup2System n hn4) d (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hdN1
  have hd0' : (d1 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2Idx3] at hval
    rw [show d1 = move (cup2System n hn4) d (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hd0
  have hd1' : (d1 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2Idx3] at hval
      omega
    rw [show d1 = move (cup2System n hn4) d (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hd1
  have hd2' : (d1 (cup2BoundaryIdx2 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2Idx3] at hval
      omega
    rw [show d1 = move (cup2System n hn4) d (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx3 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hd2
  have hd3' : (d1 (cup2Idx3 n hn9)).1 = 1 := by
    rw [show d1 = move (cup2System n hn4) d (cup2Idx3 n hn9) by rfl,
      move_apply_self_val n hn4 d (cup2Idx3 n hn9)]
    have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
    have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
    have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx3]
      omega
    have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx3]
      omega
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (d (left (cup2Idx3 n hn9))).1 = 1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      exact hd2
    have hright : (d (right (cup2Idx3 n hn9))).1 = 0 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
      exact hd4
    simpa [hleft, hd3, hright] using lookup_mid_100
  refine ⟨hreach1, hfc1, hdN2', hdN1', hd0', hd1', hd2', hd3'⟩

private theorem pn1_011_post_case022_normalizes
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (d : Config (cup2Spec n hn4))
    (hbad : d ∉ (cup2GoodCycle n hn4).configs)
    (hdN2 : (d (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hd1 : (d (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hd2 : (d (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hd3 : (d (cup2Idx3 n hn9)).1 = 0)
    (hd4 : (d (cup2Idx4 n hn9)).1 = 2)
    (hd5 : (d (cup2Idx5 n hn9)).1 = 2) :
    let d1 := move (cup2System n hn4) d (cup2Idx4 n hn9)
    let d2 := move (cup2System n hn4) d1 (cup2Idx3 n hn9)
    cup2TpReachable n hn4 d d2 ∧
      cup2Fc n hn4 d2 = cup2Fc n hn4 d ∧
      (d2 (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      (d2 (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
      (d2 (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      (d2 (cup2BoundaryIdx1 n hn9)).1 = 2 ∧
      (d2 (cup2BoundaryIdx2 n hn9)).1 = 1 ∧
      (d2 (cup2Idx3 n hn9)).1 = 1 := by
  let d1 := move (cup2System n hn4) d (cup2Idx4 n hn9)
  have hbad1 := p4_022_idx4_badStep_post n hn4 hn9 d hbad hdN2 hdN1 hd0 hd1 hd3 hd4 hd5
  have htp1 := tmp_p4_022_idx4_tpPreserving n hn4 hn9 d hd3 hd4 hd5
  have hreach1 : cup2TpReachable n hn4 d d1 :=
    cup2TpReachable_step n hn4 ⟨hbad1, by simpa [cup2TpPreservingMove] using htp1⟩
  have hfc1 : cup2Fc n hn4 d1 = cup2Fc n hn4 d := by
    simpa [d1] using p4_022_idx4_fc_eq n hn4 hn9 d hd3 hd4 hd5
  have hdN2_1' : (d1 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2Idx4] at hval
      omega
    rw [show d1 = move (cup2System n hn4) d (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx4 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hdN2
  have hdN1_1' : (d1 (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2Idx4] at hval
      omega
    rw [show d1 = move (cup2System n hn4) d (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hdN1
  have hd0_1' : (d1 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2Idx4] at hval
    rw [show d1 = move (cup2System n hn4) d (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx4 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hd0
  have hd1_1' : (d1 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2Idx4] at hval
      omega
    rw [show d1 = move (cup2System n hn4) d (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx4 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hd1
  have hd2_1' : (d1 (cup2BoundaryIdx2 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2Idx4] at hval
      omega
    rw [show d1 = move (cup2System n hn4) d (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx4 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hd2
  have hd3_1' : (d1 (cup2Idx3 n hn9)).1 = 0 := by
    have hne : cup2Idx3 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx3, cup2Idx4] at hval
    rw [show d1 = move (cup2System n hn4) d (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 d (cup2Idx4 n hn9) (cup2Idx3 n hn9) hne]
    exact hd3
  have hd4_1' : (d1 (cup2Idx4 n hn9)).1 = 0 := by
    rw [show d1 = move (cup2System n hn4) d (cup2Idx4 n hn9) by rfl,
      move_apply_self_val n hn4 d (cup2Idx4 n hn9)]
    have h0 : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
    have h1 : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
    have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx4]
      omega
    have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx4]
      omega
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (d (left (cup2Idx4 n hn9))).1 = 0 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
      exact hd3
    have hright : (d (right (cup2Idx4 n hn9))).1 = 2 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
      exact hd5
    simpa [hleft, hd4, hright] using lookup_mid_022
  let d2 := move (cup2System n hn4) d1 (cup2Idx3 n hn9)
  have hbad2 := p3_100_idx3_badStep_post n hn4 hn9 d1 hbad1.2.1
    hdN2_1' hdN1_1' hd0_1' hd1_1' hd2_1' hd3_1' hd4_1'
  have htp2 := tmp_p3_100_idx3_tpPreserving n hn4 hn9 d1 hd2_1' hd3_1' hd4_1'
  have hreach2 : cup2TpReachable n hn4 d d2 :=
    cup2TpReachable_trans n hn4 hreach1
      (cup2TpReachable_step n hn4 ⟨hbad2, by simpa [cup2TpPreservingMove] using htp2⟩)
  have hfc2 : cup2Fc n hn4 d2 = cup2Fc n hn4 d := by
    calc
      cup2Fc n hn4 d2 = cup2Fc n hn4 d1 := by
        simpa [d2] using p3_100_idx3_fc_eq n hn4 hn9 d1 hd2_1' hd3_1' hd4_1'
      _ = cup2Fc n hn4 d := hfc1
  have hdN2_2' : (d2 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2Idx3] at hval
      omega
    rw [show d2 = move (cup2System n hn4) d1 (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d1 (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hdN2_1'
  have hdN1_2' : (d2 (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2Idx3] at hval
      omega
    rw [show d2 = move (cup2System n hn4) d1 (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d1 (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hdN1_1'
  have hd0_2' : (d2 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2Idx3] at hval
    rw [show d2 = move (cup2System n hn4) d1 (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d1 (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hd0_1'
  have hd1_2' : (d2 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2Idx3] at hval
      omega
    rw [show d2 = move (cup2System n hn4) d1 (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d1 (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hd1_1'
  have hd2_2' : (d2 (cup2BoundaryIdx2 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2Idx3] at hval
      omega
    rw [show d2 = move (cup2System n hn4) d1 (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 d1 (cup2Idx3 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hd2_1'
  have hd3_2' : (d2 (cup2Idx3 n hn9)).1 = 1 := by
    rw [show d2 = move (cup2System n hn4) d1 (cup2Idx3 n hn9) by rfl,
      move_apply_self_val n hn4 d1 (cup2Idx3 n hn9)]
    have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
    have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
    have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx3]
      omega
    have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx3]
      omega
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (d1 (left (cup2Idx3 n hn9))).1 = 1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      exact hd2_1'
    have hright : (d1 (right (cup2Idx3 n hn9))).1 = 0 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
      exact hd4_1'
    simpa [hleft, hd3_1', hright] using lookup_mid_100
  refine ⟨hreach2, hfc2, hdN2_2', hdN1_2', hd0_2', hd1_2', hd2_2', hd3_2'⟩

private theorem pn1_011_post_active_normalizes_to_case3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (d : Config (cup2Spec n hn4))
    (hbad : d ∉ (cup2GoodCycle n hn4).configs)
    (hdN2 : (d (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hd1 : (d (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hd2 : (d (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hactive : pn1_011_c1_two_c2_one_active n hn4 hn9 d) :
    ∃ y : Config (cup2Spec n hn4),
      cup2TpReachable n hn4 d y ∧
        cup2Fc n hn4 y = cup2Fc n hn4 d ∧
        (y (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
        (y (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
        (y (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
        (y (cup2BoundaryIdx1 n hn9)).1 = 2 ∧
        (y (cup2BoundaryIdx2 n hn9)).1 = 1 ∧
        (y (cup2Idx3 n hn9)).1 = 1 := by
  rcases pn1_011_c1_two_c2_one_active_cases n hn4 hn9 d hactive with
    hd3 | h00 | h022
  · refine ⟨d, cup2TpReachable_refl n hn4 d, rfl, hdN2, hdN1, hd0, hd1, hd2, hd3⟩
  · let d1 := move (cup2System n hn4) d (cup2Idx3 n hn9)
    have hnorm := pn1_011_post_case00_normalizes n hn4 hn9 d hbad hdN2 hdN1 hd0 hd1 hd2 h00.1 h00.2
    exact ⟨d1, hnorm.1, hnorm.2.1, hnorm.2.2.1, hnorm.2.2.2.1, hnorm.2.2.2.2.1,
      hnorm.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.2⟩
  · let d2 := move (cup2System n hn4) (move (cup2System n hn4) d (cup2Idx4 n hn9)) (cup2Idx3 n hn9)
    have hnorm := pn1_011_post_case022_normalizes n hn4 hn9 d hbad hdN2 hdN1 hd0 hd1 hd2
      h022.1 h022.2.1 h022.2.2
    exact ⟨d2, hnorm.1, hnorm.2.1, hnorm.2.2.1, hnorm.2.2.2.1, hnorm.2.2.2.2.1,
      hnorm.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.1, hnorm.2.2.2.2.2.2.2⟩

-/
private theorem pn1_200_idxN1_fc_up_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
      cup2Fc n hn4 c + 1 := by
  have hout :
      cup2OutVal n (cup2BoundaryIdxN1 n hn9)
        (c (left (cup2BoundaryIdxN1 n hn9))).1
        (c (cup2BoundaryIdxN1 n hn9)).1
        (c (right (cup2BoundaryIdxN1 n hn9))).1 = 1 := by
    rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    have htop200 : TTopVal 2 0 0 = 1 := by native_decide
    simpa [hcN2, hcN1, hc0] using htop200
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdxN1 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9), hout]
  rw [left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
  simp [localFcAfter, localFcBefore, frontierBitVal, hcN2, hcN1, hc0]
  omega

private theorem p0_001_cN2_two_idxN1_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
        cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
      have htop200 : TTopVal 2 0 0 = 1 := by native_decide
      simpa [hcN2, hcN1, hc0] using htop200
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    exact not_mem_goodCycle_of_cN1_one_c0_zero_c1_one n hn4 hn9 hN1' h0' h1'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    have htop200 : TTopVal 2 0 0 = 1 := by native_decide
    simpa [hcN2, hcN1, hc0, htop200] using (show (1 : Nat) ≠ 0 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdxN1 n hn9, hpriv, rfl⟩⟩

private theorem p0_001_cN2_two_idxN1_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0) :
    cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN1 n hn9) := by
  have hout :
      cup2OutVal n (cup2BoundaryIdxN1 n hn9)
        (c (left (cup2BoundaryIdxN1 n hn9))).1
        (c (cup2BoundaryIdxN1 n hn9)).1
        (c (right (cup2BoundaryIdxN1 n hn9))).1 = 1 := by
    rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    have htop200 : TTopVal 2 0 0 = 1 := by native_decide
    simpa [hcN2, hcN1, hc0] using htop200
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        cup2Exp2Count n hn4 c := by
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1 1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1 1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    rw [cup2Exp2_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Exp2_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9), hout]
    rw [localExp2After, localExp2Before, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9,
      hzero_left_after, hzero_left_before,
      hzero_right_after, hzero_right_before]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        cup2Int21Count n hn4 c := by
    have hzero_left_before :
        cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_left_after :
        cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1 1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_right_before :
        cup2Int21BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_after :
        cup2Int21BitVal n (cup2BoundaryIdxN1 n hn9).1 1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    rw [cup2Int21_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Int21_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9), hout]
    rw [localInt21After, localInt21Before, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9,
      hzero_left_after, hzero_left_before,
      hzero_right_after, hzero_right_before]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1 1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1 1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    rw [cup2Exp2Weight_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9), hout]
    rw [localExp2WeightAfter, localExp2WeightBefore,
      left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9,
      hzero_left_after, hzero_left_before,
      hzero_right_after, hzero_right_before]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem p0_001_cN2_two_phi_lower
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1) :
    cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
  have hbad1 :=
    p0_001_cN2_two_idxN1_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1
  have htp1 :=
    p0_001_cN2_two_idxN1_tpPreserving n hn4 hn9 c hcN2 hcN1 hc0
  have hreach1 : cup2TpReachable n hn4 c
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) :=
    cup2TpReachable_step n hn4 ⟨hbad1, by simpa [cup2TpPreservingMove] using htp1⟩
  calc
    cup2Fc n hn4 c + 1 =
        cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) := by
      symm
      exact pn1_200_idxN1_fc_up_one n hn4 hn9 c hcN2 hcN1 hc0
    _ ≤ cup2PhiFull n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) :=
      cup2Fc_le_cup2PhiFull n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
    _ ≤ cup2PhiFull n hn4 c := cup2PhiFull_mono n hn4 hreach1

private theorem p0_012_idx1_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
        cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
      simpa [hc0, hc1, hc2] using lookup_low_012
    have h2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2BoundaryIdx1] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
      exact hc2
    exact not_mem_goodCycle_of_cN1_zero_c0_zero_c2_two n hn4 hn9 hN1' h0' h2'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2, lookup_low_012] using (show (0 : Nat) ≠ 1 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx1 n hn9, hpriv, rfl⟩⟩

private theorem p0_012_idx1_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2TpPreservingMove n hn4 c (cup2BoundaryIdx1 n hn9) := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx1 n hn9)
        (c (left (cup2BoundaryIdx1 n hn9))).1
        (c (cup2BoundaryIdx1 n hn9)).1
        (c (right (cup2BoundaryIdx1 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2] using lookup_low_012
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1 0 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1 0
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    rw [localExp2After, localExp2Before, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Int21_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
    have hzero_left_before :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_left_after :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1 0 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_before :
        cup2Int21BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_after :
        cup2Int21BitVal n (cup2BoundaryIdx1 n hn9).1 0
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    rw [localInt21After, localInt21Before, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1 0 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1 0
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    rw [localExp2WeightAfter, localExp2WeightBefore,
      left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem p0_000_c2_two_idx0_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
        cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
      simpa [hcN1, hc0, hc1] using lookup_bot_000
    have h1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    have h2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
      exact hc2
    exact not_mem_goodCycle_of_cN1_zero_c0_one_c1_zero_c2_two n hn4 hn9 hN1' h0' h1' h2'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hcN1, hc0, hc1, lookup_bot_000] using (show (1 : Nat) ≠ 0 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx0 n hn9, hpriv, rfl⟩⟩

private theorem p0_112_idx0_fc_up_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
      cup2Fc n hn4 c + 1 := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx0 n hn9)
        (c (left (cup2BoundaryIdx0 n hn9))).1
        (c (cup2BoundaryIdx0 n hn9)).1
        (c (right (cup2BoundaryIdx0 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot112 : TBotVal 1 1 2 = 0 := lookup_bot_112
    simpa [hcN1, hc0, hc1] using hbot112
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdx0 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
  rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
  simp [localFcAfter, localFcBefore, frontierBitVal, hcN1, hc0, hc1]
  omega

private theorem p0_112_idx0_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
        cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
      have hbot112 : TBotVal 1 1 2 = 0 := lookup_bot_112
      simpa [hcN1, hc0, hc1] using hbot112
    have h1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    exact not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c1_two n hn4 hn9 hN2' hN1' h0' h1'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot112 : TBotVal 1 1 2 = 0 := lookup_bot_112
    simpa [hcN1, hc0, hc1, hbot112] using (show (0 : Nat) ≠ 1 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx0 n hn9, hpriv, rfl⟩⟩

private theorem p0_112_idx0_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2) :
    cup2TpPreservingMove n hn4 c (cup2BoundaryIdx0 n hn9) := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx0 n hn9)
        (c (left (cup2BoundaryIdx0 n hn9))).1
        (c (cup2BoundaryIdx0 n hn9)).1
        (c (right (cup2BoundaryIdx0 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot112 : TBotVal 1 1 2 = 0 := lookup_bot_112
    simpa [hcN1, hc0, hc1] using hbot112
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1 0 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1 0
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    rw [localExp2After, localExp2Before, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Int21_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
    have hzero_left_before :
        cup2Int21BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_left_after :
        cup2Int21BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1 0 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_before :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_after :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1 0
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    rw [localInt21After, localInt21Before, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1 0 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1 0
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    rw [localExp2WeightAfter, localExp2WeightBefore,
      left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem p1_012_idx0_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
        cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
      have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
      simpa [hcN1, hc0, hc1] using hbot101
    exact not_mem_goodCycle_of_cN2_zero_cN1_one_c0_one n hn4 hn9 hN2' hN1' h0'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
    simpa [hcN1, hc0, hc1, hbot101] using (show (1 : Nat) ≠ 0 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx0 n hn9, hpriv, rfl⟩⟩

private theorem p1_012_idx0_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1) :
    cup2TpPreservingMove n hn4 c (cup2BoundaryIdx0 n hn9) := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx0 n hn9)
        (c (left (cup2BoundaryIdx0 n hn9))).1
        (c (cup2BoundaryIdx0 n hn9)).1
        (c (right (cup2BoundaryIdx0 n hn9))).1 =
      1 := by
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
    simpa [hcN1, hc0, hc1] using hbot101
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1 1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1 1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    rw [localExp2After, localExp2Before, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Int21_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
    have hzero_left_before :
        cup2Int21BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_left_after :
        cup2Int21BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1 1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_before :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_after :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1 1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    rw [localInt21After, localInt21Before, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1 1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1 1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    rw [localExp2WeightAfter, localExp2WeightBefore,
      left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem p1_012_idx0_tpStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1) :
    cup2TpBadStepFwd n hn4 c
      (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) := by
  refine ⟨p1_012_idx0_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1, ?_⟩
  simpa [cup2TpPreservingMove] using p1_012_idx0_tpPreserving n hn4 hn9 c hcN1 hc0 hc1

private theorem p1_012_idx0_fc_down_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) + 2 =
      cup2Fc n hn4 c := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx0 n hn9)
        (c (left (cup2BoundaryIdx0 n hn9))).1
        (c (cup2BoundaryIdx0 n hn9)).1
        (c (right (cup2BoundaryIdx0 n hn9))).1 = 1 := by
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
    simpa [hcN1, hc0, hc1] using hbot101
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdx0 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
  rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
  simp [localFcAfter, localFcBefore, frontierBitVal, hcN1, hc0, hc1]
  omega

private theorem pn1_011_c1_two_phi_lower
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2) :
    cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
  have hbad0 :=
    p0_112_idx0_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1
  have htp0 :=
    p0_112_idx0_tpPreserving n hn4 hn9 c hcN1 hc0 hc1
  have hreach0 :
      cup2TpReachable n hn4 c
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) :=
    cup2TpReachable_step n hn4 ⟨hbad0, by simpa [cup2TpPreservingMove] using htp0⟩
  have hfc0 :=
    p0_112_idx0_fc_up_one n hn4 hn9 c hcN1 hc0 hc1
  calc
    cup2Fc n hn4 c + 1 =
        cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) := by
      symm
      exact p0_112_idx0_fc_up_one n hn4 hn9 c hcN1 hc0 hc1
    _ ≤ cup2PhiFull n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) :=
      cup2Fc_le_cup2PhiFull n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))
    _ ≤ cup2PhiFull n hn4 c := cup2PhiFull_mono n hn4 hreach0

private def cup2Idx3 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨3, by omega⟩

private def cup2Idx4 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨4, by omega⟩

private def cup2Idx5 (n : Nat) (hn9 : 9 ≤ n) : Fin n := ⟨5, by omega⟩

private def pn1_011_c1_two_c2_one_active
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : Prop :=
  (c (cup2Idx3 n hn9)).1 = 1 ∨
    ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 0) ∨
    ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 2 ∧
      (c (cup2Idx5 n hn9)).1 = 2)

private theorem pn1_011_c1_two_c2_one_active_cases
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    pn1_011_c1_two_c2_one_active n hn4 hn9 c →
      (c (cup2Idx3 n hn9)).1 = 1 ∨
        ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 0) ∨
        ((c (cup2Idx3 n hn9)).1 = 0 ∧ (c (cup2Idx4 n hn9)).1 = 2 ∧
          (c (cup2Idx5 n hn9)).1 = 2) := by
  simpa [pn1_011_c1_two_c2_one_active]

private theorem right_cup2BoundaryIdx2_eq_idx3
    (n : Nat) (hn9 : 9 ≤ n) :
    right (cup2BoundaryIdx2 n hn9) = cup2Idx3 n hn9 := by
  apply Fin.ext
  have hlt : 3 < n := by omega
  simp [right_val, cup2BoundaryIdx2, cup2Idx3, Nat.mod_eq_of_lt hlt]

private theorem left_cup2Idx3_eq_boundaryIdx2
    (n : Nat) (hn9 : 9 ≤ n) :
    left (cup2Idx3 n hn9) = cup2BoundaryIdx2 n hn9 := by
  apply Fin.ext
  have hlt : 2 < n := by omega
  simp [cup2Idx3, cup2BoundaryIdx2, left_val, Nat.mod_eq_of_lt hlt]

private theorem right_cup2Idx3_eq_idx4
    (n : Nat) (hn9 : 9 ≤ n) :
    right (cup2Idx3 n hn9) = cup2Idx4 n hn9 := by
  apply Fin.ext
  have hlt : 4 < n := by omega
  simp [cup2Idx3, cup2Idx4, right_val, Nat.mod_eq_of_lt hlt]

private theorem left_cup2Idx4_eq_idx3
    (n : Nat) (hn9 : 9 ≤ n) :
    left (cup2Idx4 n hn9) = cup2Idx3 n hn9 := by
  apply Fin.ext
  have hlt : 3 < n := by omega
  simp [cup2Idx4, cup2Idx3, left_val, Nat.mod_eq_of_lt hlt]

private theorem right_cup2Idx4_eq_idx5
    (n : Nat) (hn9 : 9 ≤ n) :
    right (cup2Idx4 n hn9) = cup2Idx5 n hn9 := by
  apply Fin.ext
  have hlt : 5 < n := by omega
  simp [cup2Idx4, cup2Idx5, right_val, Nat.mod_eq_of_lt hlt]

/- private theorem move_idx2_comm_idxN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    move (cup2System n hn4)
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2BoundaryIdx2 n hn9) =
      move (cup2System n hn4)
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))
        (cup2BoundaryIdxN1 n hn9) := by
  apply funext
  intro j
  by_cases hj2 : j = cup2BoundaryIdx2 n hn9
  · subst hj2
    apply Fin.eq_of_val_eq
    rw [move_apply_self_val n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2BoundaryIdx2 n hn9)]
    rw [move_apply_self_val n hn4 c (cup2BoundaryIdx2 n hn9)]
    have hne1 : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
      omega
    have hne2 : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
      omega
    have hne3 : cup2Idx3 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx3, cup2BoundaryIdxN1] at hval
      omega
    rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9,
      right_cup2BoundaryIdx2_eq_idx3 n hn9]
    rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9) hne1,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hne2,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx3 n hn9) hne3]
    rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))
      (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
        omega)]
    simp [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9,
      right_cup2BoundaryIdx2_eq_idx3 n hn9]
  · by_cases hjN1 : j = cup2BoundaryIdxN1 n hn9
    · subst hjN1
      apply Fin.eq_of_val_eq
      rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9) (by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
          omega)]
      rw [move_apply_self_val n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))
        (cup2BoundaryIdxN1 n hn9)]
      have hneN2 : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx2] at hval
        omega
      have hneN1 : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx2] at hval
        omega
      have hne0 : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdx2] at hval
      rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9) hneN2,
        move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9) hneN1,
        move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9) hne0]
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9)]
      simp [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    · rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2BoundaryIdx2 n hn9) j hj2]
      rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) j hjN1]
      rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))
        (cup2BoundaryIdxN1 n hn9) j hjN1]
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) j hj2]

private theorem move_idx3_comm_idxN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    move (cup2System n hn4)
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2Idx3 n hn9) =
      move (cup2System n hn4)
        (move (cup2System n hn4) c (cup2Idx3 n hn9))
        (cup2BoundaryIdxN1 n hn9) := by
  apply funext
  intro j
  by_cases hj3 : j = cup2Idx3 n hn9
  · subst hj3
    apply Fin.eq_of_val_eq
    rw [move_apply_self_val n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2Idx3 n hn9)]
    rw [move_apply_self_val n hn4 c (cup2Idx3 n hn9)]
    have hneL : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
      omega
    have hneS : cup2Idx3 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx3, cup2BoundaryIdxN1] at hval
      omega
    have hneR : cup2Idx4 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx4, cup2BoundaryIdxN1] at hval
      omega
    rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hneL,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx3 n hn9) hneS,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx4 n hn9) hneR]
    rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9))
      (cup2BoundaryIdxN1 n hn9) (cup2Idx3 n hn9) (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx3, cup2BoundaryIdxN1] at hval
        omega)]
    have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
    have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
    have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx3]
      omega
    have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx3]
      omega
    simp [cup2OutVal, h0, h1, htop, hhigh]
  · by_cases hjN1 : j = cup2BoundaryIdxN1 n hn9
    · subst hjN1
      apply Fin.eq_of_val_eq
      rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9) (by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2Idx3, cup2BoundaryIdxN1] at hval
          omega)]
      rw [move_apply_self_val n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9))
        (cup2BoundaryIdxN1 n hn9)]
      have hneN2 : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2Idx3] at hval
        omega
      have hneN1 : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2Idx3] at hval
        omega
      have hne0 : cup2BoundaryIdx0 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2Idx3] at hval
      rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9) hneN2,
        move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9) hneN1,
        move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9) hne0]
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9)]
      simp [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    · rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2Idx3 n hn9) j hj3]
      rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) j hjN1]
      rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9))
        (cup2BoundaryIdxN1 n hn9) j hjN1]
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) j hj3]

private theorem move_idx4_comm_idxN1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    move (cup2System n hn4)
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2Idx4 n hn9) =
      move (cup2System n hn4)
        (move (cup2System n hn4) c (cup2Idx4 n hn9))
        (cup2BoundaryIdxN1 n hn9) := by
  apply funext
  intro j
  by_cases hj4 : j = cup2Idx4 n hn9
  · subst hj4
    apply Fin.eq_of_val_eq
    rw [move_apply_self_val n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2Idx4 n hn9)]
    rw [move_apply_self_val n hn4 c (cup2Idx4 n hn9)]
    have hneL : cup2Idx3 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx3, cup2BoundaryIdxN1] at hval
      omega
    have hneS : cup2Idx4 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx4, cup2BoundaryIdxN1] at hval
      omega
    have hneR : cup2Idx5 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx5, cup2BoundaryIdxN1] at hval
      omega
    rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx3 n hn9) hneL,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx4 n hn9) hneS,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx5 n hn9) hneR]
    rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9))
      (cup2BoundaryIdxN1 n hn9) (cup2Idx4 n hn9) (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2Idx4, cup2BoundaryIdxN1] at hval
        omega)]
    have h0 : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
    have h1 : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
    have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx4]
      omega
    have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx4]
      omega
    simp [cup2OutVal, h0, h1, htop, hhigh]
  · by_cases hjN1 : j = cup2BoundaryIdxN1 n hn9
    · subst hjN1
      apply Fin.eq_of_val_eq
      rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9) (by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2Idx4, cup2BoundaryIdxN1] at hval
          omega)]
      rw [move_apply_self_val n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9))
        (cup2BoundaryIdxN1 n hn9)]
      have hneN2 : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2Idx4] at hval
        omega
      have hneN1 : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2Idx4] at hval
        omega
      have hne0 : cup2BoundaryIdx0 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2Idx4] at hval
      rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN2 n hn9) hneN2,
        move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9) hneN1,
        move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx0 n hn9) hne0]
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9)]
      simp [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    · rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
        (cup2Idx4 n hn9) j hj4]
      rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) j hjN1]
      rw [move_apply_ne n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9))
        (cup2BoundaryIdxN1 n hn9) j hjN1]
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) j hj4]

-/
private theorem p2_211_idx2_fc_up_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 1) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
      cup2Fc n hn4 c + 1 := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx2 n hn9)
        (c (left (cup2BoundaryIdx2 n hn9))).1
        (c (cup2BoundaryIdx2 n hn9)).1
        (c (right (cup2BoundaryIdx2 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9]
    have hright : (c (right (cup2BoundaryIdx2 n hn9))).1 = 1 := by
      rw [right_cup2BoundaryIdx2_eq_idx3 n hn9]
      exact hc3
    have hmid : TMidVal 2 1 1 = 0 := by native_decide
    simpa [hc1, hc2, hright] using hmid
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdx2 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdx2 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx2 n hn9), hout]
  have hright : (c (right (cup2BoundaryIdx2 n hn9))).1 = 1 := by
    rw [right_cup2BoundaryIdx2_eq_idx3 n hn9]
    exact hc3
  rw [left_cup2BoundaryIdx2 n hn9]
  simp [localFcAfter, localFcBefore, frontierBitVal, hc1, hc2, hright]
  omega

private theorem p3_100_idx3_fc_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 0) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9)) =
      cup2Fc n hn4 c := by
  have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by
    simp [cup2Idx3]
  have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by
    simp [cup2Idx3]
  have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx3]
    omega
  have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx3]
    omega
  have hout :
      cup2OutVal n (cup2Idx3 n hn9)
        (c (left (cup2Idx3 n hn9))).1
        (c (cup2Idx3 n hn9)).1
        (c (right (cup2Idx3 n hn9))).1 = 1 := by
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx3 n hn9))).1 = 1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      exact hc2
    have hright : (c (right (cup2Idx3 n hn9))).1 = 0 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
      exact hc4
    have hmid : TMidVal 1 0 0 = 1 := by native_decide
    simpa [hleft, hc3, hright] using hmid
  rw [cup2Fc_move_split n hn4 c (cup2Idx3 n hn9),
    cup2Fc_split n hn4 c (cup2Idx3 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2Idx3 n hn9), hout]
  have hleft : (c (left (cup2Idx3 n hn9))).1 = 1 := by
    rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
    exact hc2
  have hright : (c (right (cup2Idx3 n hn9))).1 = 0 := by
    rw [right_cup2Idx3_eq_idx4 n hn9]
    exact hc4
  simp [localFcAfter, localFcBefore, frontierBitVal, hleft, hc3, hright]

private theorem p4_022_idx4_fc_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 2)
    (hc5 : (c (cup2Idx5 n hn9)).1 = 2) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9)) =
      cup2Fc n hn4 c := by
  have h0 : (cup2Idx4 n hn9).1 ≠ 0 := by
    simp [cup2Idx4]
  have h1 : (cup2Idx4 n hn9).1 ≠ 1 := by
    simp [cup2Idx4]
  have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx4]
    omega
  have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx4]
    omega
  have hout :
      cup2OutVal n (cup2Idx4 n hn9)
        (c (left (cup2Idx4 n hn9))).1
        (c (cup2Idx4 n hn9)).1
        (c (right (cup2Idx4 n hn9))).1 = 0 := by
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx4 n hn9))).1 = 0 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
      exact hc3
    have hright : (c (right (cup2Idx4 n hn9))).1 = 2 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
      exact hc5
    have hmid : TMidVal 0 2 2 = 0 := by native_decide
    simpa [hleft, hc4, hright] using hmid
  rw [cup2Fc_move_split n hn4 c (cup2Idx4 n hn9),
    cup2Fc_split n hn4 c (cup2Idx4 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2Idx4 n hn9), hout]
  have hleft : (c (left (cup2Idx4 n hn9))).1 = 0 := by
    rw [left_cup2Idx4_eq_idx3 n hn9]
    exact hc3
  have hright : (c (right (cup2Idx4 n hn9))).1 = 2 := by
    rw [right_cup2Idx4_eq_idx5 n hn9]
    exact hc5
  simp [localFcAfter, localFcBefore, frontierBitVal, hleft, hc4, hright]

private theorem tmp_not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c1_two_after_move
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) (i : Fin n)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hiN2 : cup2BoundaryIdxN2 n hn9 ≠ i)
    (hiN1 : cup2BoundaryIdxN1 n hn9 ≠ i)
    (hi0 : cup2BoundaryIdx0 n hn9 ≠ i)
    (hi1 : cup2BoundaryIdx1 n hn9 ≠ i) :
    move (cup2System n hn4) c i ∉ (cup2GoodCycle n hn4).configs := by
  have hN2' :
      (move (cup2System n hn4) c i (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    rw [move_apply_ne n hn4 c i (cup2BoundaryIdxN2 n hn9) hiN2]
    exact hcN2
  have hN1' :
      (move (cup2System n hn4) c i (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    rw [move_apply_ne n hn4 c i (cup2BoundaryIdxN1 n hn9) hiN1]
    exact hcN1
  have h0' :
      (move (cup2System n hn4) c i (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [move_apply_ne n hn4 c i (cup2BoundaryIdx0 n hn9) hi0]
    exact hc0
  have h1' :
      (move (cup2System n hn4) c i (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    rw [move_apply_ne n hn4 c i (cup2BoundaryIdx1 n hn9) hi1]
    exact hc1
  exact not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c1_two n hn4 hn9 hN2' hN1' h0' h1'

private theorem tmp_p3_100_idx3_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 0) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2Idx3 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2Idx3 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    exact tmp_not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c1_two_after_move n hn4 hn9 c
      (cup2Idx3 n hn9) hcN2 hcN1 hc0 hc1
      (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2Idx3] at hval
        omega)
      (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2Idx3] at hval
        omega)
      (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2Idx3] at hval)
      (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2Idx3] at hval)
  have hpriv : privileged (cup2System n hn4) c (cup2Idx3 n hn9) := by
    have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
    have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
    have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx3]
      omega
    have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx3]
      omega
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx3 n hn9))).1 = 1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      exact hc2
    have hright : (c (right (cup2Idx3 n hn9))).1 = 0 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
      exact hc4
    simpa [hleft, hc3, hright, lookup_mid_100] using (show (1 : Nat) ≠ 0 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2Idx3 n hn9, hpriv, rfl⟩⟩

private theorem tmp_p3_100_idx3_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 0) :
    cup2TpPreservingMove n hn4 c (cup2Idx3 n hn9) := by
  have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
  have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
  have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx3]
    omega
  have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx3]
    omega
  have hout :
      cup2OutVal n (cup2Idx3 n hn9)
        (c (left (cup2Idx3 n hn9))).1
        (c (cup2Idx3 n hn9)).1
        (c (right (cup2Idx3 n hn9))).1 = 1 := by
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx3 n hn9))).1 = 1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      exact hc2
    have hright : (c (right (cup2Idx3 n hn9))).1 = 0 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
      exact hc4
    simpa [hleft, hc3, hright] using lookup_mid_100
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9)) =
        cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c (cup2Idx3 n hn9),
      cup2Exp2_split n hn4 c (cup2Idx3 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2Idx3 n hn9), hout]
    rw [localExp2After, localExp2Before, left_cup2Idx3_eq_boundaryIdx2 n hn9,
      right_cup2Idx3_eq_idx4 n hn9, hc2, hc3, hc4]
    simp [cup2Exp2BitVal, cup2BoundaryIdx2, cup2Idx3, cup2Idx4]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9)) =
        cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c (cup2Idx3 n hn9),
      cup2Int21_split n hn4 c (cup2Idx3 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2Idx3 n hn9), hout]
    rw [localInt21After, localInt21Before, left_cup2Idx3_eq_boundaryIdx2 n hn9,
      right_cup2Idx3_eq_idx4 n hn9, hc2, hc3, hc4]
    simp [cup2Int21BitVal, cup2BoundaryIdx2, cup2Idx3, cup2Idx4]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2Idx3 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c (cup2Idx3 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2Idx3 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2Idx3 n hn9), hout]
    rw [localExp2WeightAfter, localExp2WeightBefore,
      left_cup2Idx3_eq_boundaryIdx2 n hn9, right_cup2Idx3_eq_idx4 n hn9, hc2, hc3, hc4]
    simp [cup2Exp2BitVal, cup2BoundaryIdx2, cup2Idx3, cup2Idx4]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem tmp_p4_022_idx4_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 2)
    (hc5 : (c (cup2Idx5 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2Idx4 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2Idx4 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    exact tmp_not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c1_two_after_move n hn4 hn9 c
      (cup2Idx4 n hn9) hcN2 hcN1 hc0 hc1
      (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2Idx4] at hval
        omega)
      (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2Idx4] at hval
        omega)
      (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2Idx4] at hval)
      (by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2Idx4] at hval)
  have hpriv : privileged (cup2System n hn4) c (cup2Idx4 n hn9) := by
    have h0 : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
    have h1 : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
    have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx4]
      omega
    have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx4]
      omega
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx4 n hn9))).1 = 0 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
      exact hc3
    have hright : (c (right (cup2Idx4 n hn9))).1 = 2 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
      exact hc5
    simpa [hleft, hc4, hright, lookup_mid_022] using (show (0 : Nat) ≠ 2 by decide)

  exact ⟨hbadc, hdest_bad, ⟨cup2Idx4 n hn9, hpriv, rfl⟩⟩

private theorem tmp_p4_022_idx4_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 2)
    (hc5 : (c (cup2Idx5 n hn9)).1 = 2) :
    cup2TpPreservingMove n hn4 c (cup2Idx4 n hn9) := by
  have h0 : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
  have h1 : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
  have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx4]
    omega
  have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx4]
    omega
  have hout :
      cup2OutVal n (cup2Idx4 n hn9)
        (c (left (cup2Idx4 n hn9))).1
        (c (cup2Idx4 n hn9)).1
        (c (right (cup2Idx4 n hn9))).1 = 0 := by
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx4 n hn9))).1 = 0 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
      exact hc3
    have hright : (c (right (cup2Idx4 n hn9))).1 = 2 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
      exact hc5
    simpa [hleft, hc4, hright] using lookup_mid_022
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9)) =
        cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c (cup2Idx4 n hn9),
      cup2Exp2_split n hn4 c (cup2Idx4 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2Idx4 n hn9), hout]
    rw [localExp2After, localExp2Before, left_cup2Idx4_eq_idx3 n hn9,
      right_cup2Idx4_eq_idx5 n hn9, hc3, hc4, hc5]
    simp [cup2Exp2BitVal, cup2Idx3, cup2Idx4, cup2Idx5]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9)) =
        cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c (cup2Idx4 n hn9),
      cup2Int21_split n hn4 c (cup2Idx4 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2Idx4 n hn9), hout]
    rw [localInt21After, localInt21Before, left_cup2Idx4_eq_idx3 n hn9,
      right_cup2Idx4_eq_idx5 n hn9, hc3, hc4, hc5]
    simp [cup2Int21BitVal, cup2Idx3, cup2Idx4, cup2Idx5]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2Idx4 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c (cup2Idx4 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2Idx4 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2Idx4 n hn9), hout]
    rw [localExp2WeightAfter, localExp2WeightBefore,
      left_cup2Idx4_eq_idx3 n hn9, right_cup2Idx4_eq_idx5 n hn9, hc3, hc4, hc5]
    simp [cup2Exp2BitVal, cup2Idx3, cup2Idx4, cup2Idx5]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem p2_211_idx2_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 1) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx2] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx2] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    exact not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c1_two n hn4 hn9 hN2' hN1' h0' h1'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9, right_cup2BoundaryIdx2_eq_idx3 n hn9]
    have hmid : TMidVal 2 1 1 = 0 := by native_decide
    simpa [hc1, hc2, hc3, hmid] using (show (0 : Nat) ≠ 1 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx2 n hn9, hpriv, rfl⟩⟩

private theorem p2_211_idx2_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 1) :
    cup2TpPreservingMove n hn4 c (cup2BoundaryIdx2 n hn9) := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx2 n hn9)
        (c (left (cup2BoundaryIdx2 n hn9))).1
        (c (cup2BoundaryIdx2 n hn9)).1
        (c (right (cup2BoundaryIdx2 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9, right_cup2BoundaryIdx2_eq_idx3 n hn9]
    have hmid : TMidVal 2 1 1 = 0 := by native_decide
    simpa [hc1, hc2, hc3] using hmid
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
        cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Exp2_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2BoundaryIdx2 n hn9), hout]
    rw [localExp2After, localExp2Before, left_cup2BoundaryIdx2 n hn9,
      right_cup2BoundaryIdx2_eq_idx3 n hn9]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1 0 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx2 n hn9).1
          (c (cup2BoundaryIdx2 n hn9)).1 (c (cup2Idx3 n hn9)).1 = 0 := by
      rw [hc2, hc3]
      simp [cup2Exp2BitVal, cup2BoundaryIdx2]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx2 n hn9).1 0 (c (cup2Idx3 n hn9)).1 = 0 := by
      rw [hc3]
      simp [cup2Exp2BitVal, cup2BoundaryIdx2]
    rw [hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
        cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Int21_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2BoundaryIdx2 n hn9), hout]
    rw [localInt21After, localInt21Before, left_cup2BoundaryIdx2 n hn9,
      right_cup2BoundaryIdx2_eq_idx3 n hn9]
    have hzero_left_before :
        cup2Int21BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_left_after :
        cup2Int21BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1 0 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_before :
        cup2Int21BitVal n (cup2BoundaryIdx2 n hn9).1
          (c (cup2BoundaryIdx2 n hn9)).1 (c (cup2Idx3 n hn9)).1 = 0 := by
      rw [hc2, hc3]
      simp [cup2Int21BitVal, cup2BoundaryIdx2]
    have hzero_right_after :
        cup2Int21BitVal n (cup2BoundaryIdx2 n hn9).1 0 (c (cup2Idx3 n hn9)).1 = 0 := by
      rw [hc3]
      simp [cup2Int21BitVal, cup2BoundaryIdx2]
    rw [hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2BoundaryIdx2 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2BoundaryIdx2 n hn9), hout]
    rw [localExp2WeightAfter, localExp2WeightBefore,
      left_cup2BoundaryIdx2 n hn9, right_cup2BoundaryIdx2_eq_idx3 n hn9]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1 0 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx2 n hn9).1
          (c (cup2BoundaryIdx2 n hn9)).1 (c (cup2Idx3 n hn9)).1 = 0 := by
      rw [hc2, hc3]
      simp [cup2Exp2BitVal, cup2BoundaryIdx2]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx2 n hn9).1 0 (c (cup2Idx3 n hn9)).1 = 0 := by
      rw [hc3]
      simp [cup2Exp2BitVal, cup2BoundaryIdx2]
    rw [hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem p2_211_idx2_badStep_post
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 1) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx2] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx2] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx2 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2BoundaryIdx2] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx2 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    exact not_mem_goodCycle_of_cN2_zero_cN1_zero_c0_one_c1_two n hn4 hn9 hN2' hN1' h0' h1'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9, right_cup2BoundaryIdx2_eq_idx3 n hn9]
    have hmid : TMidVal 2 1 1 = 0 := by native_decide
    simpa [hc1, hc2, hc3, hmid] using (show (0 : Nat) ≠ 1 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx2 n hn9, hpriv, rfl⟩⟩

private theorem p3_100_idx3_badStep_post
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 0) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2Idx3 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2Idx3 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval : n - 2 = 3 := by
          simpa [cup2BoundaryIdxN2, cup2Idx3] using congrArg Fin.val hEq
        omega
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval : n - 1 = 3 := by
          simpa [cup2BoundaryIdxN1, cup2Idx3] using congrArg Fin.val hEq
        omega
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2Idx3] at hval
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx3 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2Idx3] at hval
      rw [move_apply_ne n hn4 c (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    exact not_mem_goodCycle_of_cN2_zero_cN1_zero_c0_one_c1_two n hn4 hn9 hN2' hN1' h0' h1'
  have h0i : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
  have h1i : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
  have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx3]
    omega
  have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx3]
    omega
  have hpriv : privileged (cup2System n hn4) c (cup2Idx3 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal, if_neg h0i, if_neg h1i, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx3 n hn9))).1 = 1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      exact hc2
    have hright : (c (right (cup2Idx3 n hn9))).1 = 0 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
      exact hc4
    simpa [hleft, hc3, hright, lookup_mid_100] using (show (1 : Nat) ≠ 0 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2Idx3 n hn9, hpriv, rfl⟩⟩

private theorem p4_022_idx4_badStep_post
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 2)
    (hc5 : (c (cup2Idx5 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2Idx4 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2Idx4 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2Idx4 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval : n - 2 = 4 := by
          simpa [cup2BoundaryIdxN2, cup2Idx4] using congrArg Fin.val hEq
        omega
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval : n - 1 = 4 := by
          simpa [cup2BoundaryIdxN1, cup2Idx4] using congrArg Fin.val hEq
        omega
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2Idx4 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2Idx4] at hval
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2Idx4 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx4 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2Idx4] at hval
      rw [move_apply_ne n hn4 c (cup2Idx4 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    exact not_mem_goodCycle_of_cN2_zero_cN1_zero_c0_one_c1_two n hn4 hn9 hN2' hN1' h0' h1'
  have h0i : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
  have h1i : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
  have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
    simp [cup2Idx4]
    omega
  have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
    simp [cup2Idx4]
    omega
  have hpriv : privileged (cup2System n hn4) c (cup2Idx4 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal, if_neg h0i, if_neg h1i, if_neg htop, if_neg hhigh]
    have hleft : (c (left (cup2Idx4 n hn9))).1 = 0 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
      exact hc3
    have hright : (c (right (cup2Idx4 n hn9))).1 = 2 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
      exact hc5
    simpa [hleft, hc4, hright, lookup_mid_022] using (show (0 : Nat) ≠ 2 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2Idx4 n hn9, hpriv, rfl⟩⟩

private theorem pn1_011_c1_two_c2_one_phi_lower_case3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 1) :
    cup2Fc n hn4 c + 2 ≤ cup2PhiFull n hn4 c := by
  let c0' := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
  have hbad0 := p0_112_idx0_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1
  have htp0 := p0_112_idx0_tpPreserving n hn4 hn9 c hcN1 hc0 hc1
  have hcN2_0' : (c0' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hcN1_0' : (c0' (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc0_0' : (c0' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hcN1, hc0, hc1] using lookup_bot_112
  have hc1_0' : (c0' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1
  have hc2_0' : (c0' (cup2BoundaryIdx2 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hc3_0' : (c0' (cup2Idx3 n hn9)).1 = 1 := by
    have hne : cup2Idx3 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx3, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx3 n hn9) hne]
    exact hc3
  have hbad1 := p2_211_idx2_badStep n hn4 hn9 c0' hbad0.2.1
    hcN2_0' hcN1_0' hc0_0' hc1_0' hc2_0' hc3_0'
  have htp1 := p2_211_idx2_tpPreserving n hn4 hn9 c0' hc1_0' hc2_0' hc3_0'
  have hreach0 : cup2TpReachable n hn4 c c0' :=
    cup2TpReachable_step n hn4 ⟨hbad0, by simpa [cup2TpPreservingMove] using htp0⟩
  have hreach1 : cup2TpReachable n hn4 c
      (move (cup2System n hn4) c0' (cup2BoundaryIdx2 n hn9)) :=
    cup2TpReachable_trans n hn4 hreach0
      (cup2TpReachable_step n hn4 ⟨hbad1, by simpa [cup2TpPreservingMove] using htp1⟩)
  have hfc_gain :
      cup2Fc n hn4 (move (cup2System n hn4) c0' (cup2BoundaryIdx2 n hn9)) =
        cup2Fc n hn4 c + 2 := by
    have hfc0 := p0_112_idx0_fc_up_one n hn4 hn9 c hcN1 hc0 hc1
    have hfc1 := p2_211_idx2_fc_up_one n hn4 hn9 c0' hc1_0' hc2_0' hc3_0'
    calc
      cup2Fc n hn4 (move (cup2System n hn4) c0' (cup2BoundaryIdx2 n hn9)) =
          cup2Fc n hn4 c0' + 1 := hfc1
      _ = cup2Fc n hn4 c + 2 := by
        rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl]
        rw [p0_112_idx0_fc_up_one n hn4 hn9 c hcN1 hc0 hc1]
  calc
    cup2Fc n hn4 c + 2 =
        cup2Fc n hn4 (move (cup2System n hn4) c0' (cup2BoundaryIdx2 n hn9)) := by
      omega
    _ ≤ cup2PhiFull n hn4 (move (cup2System n hn4) c0' (cup2BoundaryIdx2 n hn9)) :=
      cup2Fc_le_cup2PhiFull n hn4 (move (cup2System n hn4) c0' (cup2BoundaryIdx2 n hn9))
    _ ≤ cup2PhiFull n hn4 c := cup2PhiFull_mono n hn4 hreach1

private theorem pn1_011_c1_two_c2_one_phi_lower_case00
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 0) :
    cup2Fc n hn4 c + 2 ≤ cup2PhiFull n hn4 c := by
  let c0' := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
  have hbad0 := p0_112_idx0_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1
  have htp0 := p0_112_idx0_tpPreserving n hn4 hn9 c hcN1 hc0 hc1
  have hcN2_0' : (c0' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hcN1_0' : (c0' (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc0_0' : (c0' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hcN1, hc0, hc1] using lookup_bot_112
  have hc1_0' : (c0' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1
  have hc2_0' : (c0' (cup2BoundaryIdx2 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hc3_0' : (c0' (cup2Idx3 n hn9)).1 = 0 := by
    have hne : cup2Idx3 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx3, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx3 n hn9) hne]
    exact hc3
  have hc4_0' : (c0' (cup2Idx4 n hn9)).1 = 0 := by
    have hne : cup2Idx4 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx4, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx4 n hn9) hne]
    exact hc4
  have hbad1 := tmp_p3_100_idx3_badStep n hn4 hn9 c0' hbad0.2.1
    hcN2_0' hcN1_0' hc0_0' hc1_0' hc2_0' hc3_0' hc4_0'
  have htp1 := tmp_p3_100_idx3_tpPreserving n hn4 hn9 c0' hc2_0' hc3_0' hc4_0'
  let c1' := move (cup2System n hn4) c0' (cup2Idx3 n hn9)
  have hcN2_1' : (c1' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2Idx3] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2_0'
  have hcN1_1' : (c1' (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2Idx3] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1_0'
  have hc0_1' : (c1' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2Idx3] at hval
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0_0'
  have hc1_1' : (c1' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2Idx3] at hval
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1_0'
  have hc2_1' : (c1' (cup2BoundaryIdx2 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2Idx3] at hval
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx3 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2_0'
  have hc3_1' : (c1' (cup2Idx3 n hn9)).1 = 1 := by
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx3 n hn9) by rfl,
      move_apply_self_val n hn4 c0' (cup2Idx3 n hn9)]
    have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
    have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
    have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx3]
      omega
    have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx3]
      omega
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (c0' (left (cup2Idx3 n hn9))).1 = 1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      exact hc2_0'
    have hright : (c0' (right (cup2Idx3 n hn9))).1 = 0 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
      exact hc4_0'
    simpa [hleft, hc3_0', hright] using lookup_mid_100
  have hbad2 := p2_211_idx2_badStep n hn4 hn9 c1' hbad1.2.1
    hcN2_1' hcN1_1' hc0_1' hc1_1' hc2_1' hc3_1'
  have htp2 := p2_211_idx2_tpPreserving n hn4 hn9 c1' hc1_1' hc2_1' hc3_1'
  have hreach0 : cup2TpReachable n hn4 c c0' :=
    cup2TpReachable_step n hn4 ⟨hbad0, by simpa [cup2TpPreservingMove] using htp0⟩
  have hreach1 : cup2TpReachable n hn4 c c1' :=
    cup2TpReachable_trans n hn4 hreach0
      (cup2TpReachable_step n hn4 ⟨hbad1, by simpa [cup2TpPreservingMove] using htp1⟩)
  have hreach2 : cup2TpReachable n hn4 c
      (move (cup2System n hn4) c1' (cup2BoundaryIdx2 n hn9)) :=
    cup2TpReachable_trans n hn4 hreach1
      (cup2TpReachable_step n hn4 ⟨hbad2, by simpa [cup2TpPreservingMove] using htp2⟩)
  have hfc_gain :
      cup2Fc n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx2 n hn9)) =
        cup2Fc n hn4 c + 2 := by
    have hfc0 := p0_112_idx0_fc_up_one n hn4 hn9 c hcN1 hc0 hc1
    have hfc1 := p3_100_idx3_fc_eq n hn4 hn9 c0' hc2_0' hc3_0' hc4_0'
    have hfc2 := p2_211_idx2_fc_up_one n hn4 hn9 c1' hc1_1' hc2_1' hc3_1'
    calc
      cup2Fc n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx2 n hn9)) =
          cup2Fc n hn4 c1' + 1 := hfc2
      _ = cup2Fc n hn4 c0' + 1 := by
        rw [show c1' = move (cup2System n hn4) c0' (cup2Idx3 n hn9) by rfl]
        rw [p3_100_idx3_fc_eq n hn4 hn9 c0' hc2_0' hc3_0' hc4_0']
      _ = cup2Fc n hn4 c + 2 := by
        rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl]
        rw [p0_112_idx0_fc_up_one n hn4 hn9 c hcN1 hc0 hc1]
  calc
    cup2Fc n hn4 c + 2 =
        cup2Fc n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx2 n hn9)) := by
      omega
    _ ≤ cup2PhiFull n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx2 n hn9)) :=
      cup2Fc_le_cup2PhiFull n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx2 n hn9))
    _ ≤ cup2PhiFull n hn4 c := cup2PhiFull_mono n hn4 hreach2

private theorem pn1_011_c1_two_c2_one_phi_lower_case022
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hc3 : (c (cup2Idx3 n hn9)).1 = 0)
    (hc4 : (c (cup2Idx4 n hn9)).1 = 2)
    (hc5 : (c (cup2Idx5 n hn9)).1 = 2) :
    cup2Fc n hn4 c + 2 ≤ cup2PhiFull n hn4 c := by
  let c0' := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
  have hbad0 := p0_112_idx0_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1
  have htp0 := p0_112_idx0_tpPreserving n hn4 hn9 c hcN1 hc0 hc1
  have hcN2_0' : (c0' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hcN1_0' : (c0' (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc0_0' : (c0' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hcN1, hc0, hc1] using lookup_bot_112
  have hc1_0' : (c0' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1
  have hc2_0' : (c0' (cup2BoundaryIdx2 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hc3_0' : (c0' (cup2Idx3 n hn9)).1 = 0 := by
    have hne : cup2Idx3 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx3, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx3 n hn9) hne]
    exact hc3
  have hc4_0' : (c0' (cup2Idx4 n hn9)).1 = 2 := by
    have hne : cup2Idx4 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx4, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx4 n hn9) hne]
    exact hc4
  have hc5_0' : (c0' (cup2Idx5 n hn9)).1 = 2 := by
    have hne : cup2Idx5 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx5, cup2BoundaryIdx0] at hval
    rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2Idx5 n hn9) hne]
    exact hc5
  have hbad1 := tmp_p4_022_idx4_badStep n hn4 hn9 c0' hbad0.2.1
    hcN2_0' hcN1_0' hc0_0' hc1_0' hc3_0' hc4_0' hc5_0'
  have htp1 := tmp_p4_022_idx4_tpPreserving n hn4 hn9 c0' hc3_0' hc4_0' hc5_0'
  let c1' := move (cup2System n hn4) c0' (cup2Idx4 n hn9)
  have hcN2_1' : (c1' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2Idx4] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx4 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2_0'
  have hcN1_1' : (c1' (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2Idx4] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx4 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1_0'
  have hc0_1' : (c1' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2Idx4] at hval
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx4 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0_0'
  have hc1_1' : (c1' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2Idx4] at hval
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx4 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1_0'
  have hc2_1' : (c1' (cup2BoundaryIdx2 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2Idx4] at hval
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx4 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2_0'
  have hc3_1' : (c1' (cup2Idx3 n hn9)).1 = 0 := by
    have hne : cup2Idx3 n hn9 ≠ cup2Idx4 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2Idx3, cup2Idx4] at hval
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx4 n hn9) by rfl,
      move_apply_ne n hn4 c0' (cup2Idx4 n hn9) (cup2Idx3 n hn9) hne]
    exact hc3_0'
  have hc4_1' : (c1' (cup2Idx4 n hn9)).1 = 0 := by
    rw [show c1' = move (cup2System n hn4) c0' (cup2Idx4 n hn9) by rfl,
      move_apply_self_val n hn4 c0' (cup2Idx4 n hn9)]
    have h0 : (cup2Idx4 n hn9).1 ≠ 0 := by simp [cup2Idx4]
    have h1 : (cup2Idx4 n hn9).1 ≠ 1 := by simp [cup2Idx4]
    have htop : (cup2Idx4 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx4]
      omega
    have hhigh : (cup2Idx4 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx4]
      omega
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (c0' (left (cup2Idx4 n hn9))).1 = 0 := by
      rw [left_cup2Idx4_eq_idx3 n hn9]
      exact hc3_0'
    have hright : (c0' (right (cup2Idx4 n hn9))).1 = 2 := by
      rw [right_cup2Idx4_eq_idx5 n hn9]
      exact hc5_0'
    simpa [hleft, hc4_0', hright] using lookup_mid_022
  have hbad2 := tmp_p3_100_idx3_badStep n hn4 hn9 c1' hbad1.2.1
    hcN2_1' hcN1_1' hc0_1' hc1_1' hc2_1' hc3_1' hc4_1'
  have htp2 := tmp_p3_100_idx3_tpPreserving n hn4 hn9 c1' hc2_1' hc3_1' hc4_1'
  let c2' := move (cup2System n hn4) c1' (cup2Idx3 n hn9)
  have hcN2_2' : (c2' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2Idx3] at hval
      omega
    rw [show c2' = move (cup2System n hn4) c1' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c1' (cup2Idx3 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2_1'
  have hcN1_2' : (c2' (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2Idx3] at hval
      omega
    rw [show c2' = move (cup2System n hn4) c1' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c1' (cup2Idx3 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1_1'
  have hc0_2' : (c2' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2Idx3] at hval
    rw [show c2' = move (cup2System n hn4) c1' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c1' (cup2Idx3 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0_1'
  have hc1_2' : (c2' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2Idx3] at hval
    rw [show c2' = move (cup2System n hn4) c1' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c1' (cup2Idx3 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1_1'
  have hc2_2' : (c2' (cup2BoundaryIdx2 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2Idx3 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2Idx3] at hval
    rw [show c2' = move (cup2System n hn4) c1' (cup2Idx3 n hn9) by rfl,
      move_apply_ne n hn4 c1' (cup2Idx3 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2_1'
  have hc3_2' : (c2' (cup2Idx3 n hn9)).1 = 1 := by
    rw [show c2' = move (cup2System n hn4) c1' (cup2Idx3 n hn9) by rfl,
      move_apply_self_val n hn4 c1' (cup2Idx3 n hn9)]
    have h0 : (cup2Idx3 n hn9).1 ≠ 0 := by simp [cup2Idx3]
    have h1 : (cup2Idx3 n hn9).1 ≠ 1 := by simp [cup2Idx3]
    have htop : (cup2Idx3 n hn9).1 + 1 ≠ n := by
      simp [cup2Idx3]
      omega
    have hhigh : (cup2Idx3 n hn9).1 + 2 ≠ n := by
      simp [cup2Idx3]
      omega
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop, if_neg hhigh]
    have hleft : (c1' (left (cup2Idx3 n hn9))).1 = 1 := by
      rw [left_cup2Idx3_eq_boundaryIdx2 n hn9]
      exact hc2_1'
    have hright : (c1' (right (cup2Idx3 n hn9))).1 = 0 := by
      rw [right_cup2Idx3_eq_idx4 n hn9]
      exact hc4_1'
    simpa [hleft, hc3_1', hright] using lookup_mid_100
  have hbad3 := p2_211_idx2_badStep n hn4 hn9 c2' hbad2.2.1
    hcN2_2' hcN1_2' hc0_2' hc1_2' hc2_2' hc3_2'
  have htp3 := p2_211_idx2_tpPreserving n hn4 hn9 c2' hc1_2' hc2_2' hc3_2'
  have hreach0 : cup2TpReachable n hn4 c c0' :=
    cup2TpReachable_step n hn4 ⟨hbad0, by simpa [cup2TpPreservingMove] using htp0⟩
  have hreach1 : cup2TpReachable n hn4 c c1' :=
    cup2TpReachable_trans n hn4 hreach0
      (cup2TpReachable_step n hn4 ⟨hbad1, by simpa [cup2TpPreservingMove] using htp1⟩)
  have hreach2 : cup2TpReachable n hn4 c c2' :=
    cup2TpReachable_trans n hn4 hreach1
      (cup2TpReachable_step n hn4 ⟨hbad2, by simpa [cup2TpPreservingMove] using htp2⟩)
  have hreach3 : cup2TpReachable n hn4 c
      (move (cup2System n hn4) c2' (cup2BoundaryIdx2 n hn9)) :=
    cup2TpReachable_trans n hn4 hreach2
      (cup2TpReachable_step n hn4 ⟨hbad3, by simpa [cup2TpPreservingMove] using htp3⟩)
  have hfc_gain :
      cup2Fc n hn4 (move (cup2System n hn4) c2' (cup2BoundaryIdx2 n hn9)) =
        cup2Fc n hn4 c + 2 := by
    have hfc0 := p0_112_idx0_fc_up_one n hn4 hn9 c hcN1 hc0 hc1
    have hfc1 := p4_022_idx4_fc_eq n hn4 hn9 c0' hc3_0' hc4_0' hc5_0'
    have hfc2 := p3_100_idx3_fc_eq n hn4 hn9 c1' hc2_1' hc3_1' hc4_1'
    have hfc3 := p2_211_idx2_fc_up_one n hn4 hn9 c2' hc1_2' hc2_2' hc3_2'
    calc
      cup2Fc n hn4 (move (cup2System n hn4) c2' (cup2BoundaryIdx2 n hn9)) =
          cup2Fc n hn4 c2' + 1 := hfc3
      _ = cup2Fc n hn4 c1' + 1 := by
        rw [show c2' = move (cup2System n hn4) c1' (cup2Idx3 n hn9) by rfl]
        rw [p3_100_idx3_fc_eq n hn4 hn9 c1' hc2_1' hc3_1' hc4_1']
      _ = cup2Fc n hn4 c0' + 1 := by
        rw [show c1' = move (cup2System n hn4) c0' (cup2Idx4 n hn9) by rfl]
        rw [p4_022_idx4_fc_eq n hn4 hn9 c0' hc3_0' hc4_0' hc5_0']
      _ = cup2Fc n hn4 c + 2 := by
        rw [show c0' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl]
        rw [p0_112_idx0_fc_up_one n hn4 hn9 c hcN1 hc0 hc1]
  calc
    cup2Fc n hn4 c + 2 =
        cup2Fc n hn4 (move (cup2System n hn4) c2' (cup2BoundaryIdx2 n hn9)) := by
      omega
    _ ≤ cup2PhiFull n hn4 (move (cup2System n hn4) c2' (cup2BoundaryIdx2 n hn9)) :=
      cup2Fc_le_cup2PhiFull n hn4 (move (cup2System n hn4) c2' (cup2BoundaryIdx2 n hn9))
    _ ≤ cup2PhiFull n hn4 c := cup2PhiFull_mono n hn4 hreach3

private theorem pn1_011_c1_two_c2_one_active_phi_lower
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1)
    (hactive : pn1_011_c1_two_c2_one_active n hn4 hn9 c) :
    cup2Fc n hn4 c + 2 ≤ cup2PhiFull n hn4 c := by
  rcases pn1_011_c1_two_c2_one_active_cases n hn4 hn9 c hactive with
    hc3_1 | h00 | h022
  · exact pn1_011_c1_two_c2_one_phi_lower_case3 n hn4 hn9 c
      hbadc hcN2 hcN1 hc0 hc1 hc2 hc3_1
  · exact pn1_011_c1_two_c2_one_phi_lower_case00 n hn4 hn9 c
      hbadc hcN2 hcN1 hc0 hc1 hc2 h00.1 h00.2
  · exact pn1_011_c1_two_c2_one_phi_lower_case022 n hn4 hn9 c
      hbadc hcN2 hcN1 hc0 hc1 hc2 h022.1 h022.2.1 h022.2.2

private theorem pn1_011_leftFrame_c2_zero_or_two_as_postmove
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (d : Config (cup2Spec n hn4))
    (hdN3 : (d (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hdN2 : (d (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hd1 : (d (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hd2 : (d (cup2BoundaryIdx2 n hn9)).1 = 0 ∨
      (d (cup2BoundaryIdx2 n hn9)).1 = 2) :
    ∃ src : Config (cup2Spec n hn4),
      (src (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
      (src (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      (src (cup2BoundaryIdxN1 n hn9)).1 = 1 ∧
      (src (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      (src (cup2BoundaryIdx1 n hn9)).1 = 2 ∧
      ((src (cup2BoundaryIdx2 n hn9)).1 = 0 ∨
        (src (cup2BoundaryIdx2 n hn9)).1 = 2) ∧
      d = move (cup2System n hn4) src (cup2BoundaryIdxN1 n hn9) := by
  let src : Config (cup2Spec n hn4) :=
    fun i =>
      if h : i = cup2BoundaryIdxN1 n hn9 then
        Fin.cast
          (by
            cases h
            have htop : (cup2BoundaryIdxN1 n hn9).1 + 1 = n := by
              simp [cup2BoundaryIdxN1]
              omega
            simpa [cup2Spec] using
              (cup2M_eq_two_of_endpoint (n := n) (i := cup2BoundaryIdxN1 n hn9)
                (Or.inr htop)).symm)
          (⟨1, by decide⟩ : Fin 2)
      else
        d i
  have hsrcN2 : (src (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    dsimp [src]
    split_ifs with h
    · have hval := congrArg Fin.val h
      simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
      omega
    · exact hdN2
  have hsrcN1 : (src (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    dsimp [src]
    split_ifs with h
    · rfl
    · contradiction
  have hsrc0 : (src (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    dsimp [src]
    split_ifs with h
    · have hval := congrArg Fin.val h
      simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
      omega
    · exact hd0
  have hsrcN3 : (src (cup2BoundaryIdxN3 n hn9)).1 = 2 := by
    dsimp [src]
    split_ifs with h
    · have hval := congrArg Fin.val h
      simp [cup2BoundaryIdxN3, cup2BoundaryIdxN1] at hval
      omega
    · exact hdN3
  have hsrc1 : (src (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    dsimp [src]
    split_ifs with h
    · have hval := congrArg Fin.val h
      simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
      omega
    · exact hd1
  have hsrc2 : (src (cup2BoundaryIdx2 n hn9)).1 = 0 ∨
      (src (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    dsimp [src]
    split_ifs with h
    · have hval := congrArg Fin.val h
      simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
      omega
    · exact hd2
  refine ⟨src, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsrcN3
  · exact hsrcN2
  · exact hsrcN1
  · exact hsrc0
  · exact hsrc1
  · exact hsrc2
  · apply funext
    intro i
    by_cases hi : i = cup2BoundaryIdxN1 n hn9
    · subst hi
      have hdv : (d (cup2BoundaryIdxN1 n hn9)).1 = 0 := hdN1
      have htop011 : TTopVal 0 1 1 = 0 := by native_decide
      apply Fin.eq_of_val_eq
      calc
        (d (cup2BoundaryIdxN1 n hn9)).1 = 0 := hdv
        _ = TTopVal 0 1 1 := by simpa using htop011.symm
        _ = cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (src (left (cup2BoundaryIdxN1 n hn9))).1
              (src (cup2BoundaryIdxN1 n hn9)).1
              (src (right (cup2BoundaryIdxN1 n hn9))).1 := by
          rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9,
            right_cup2BoundaryIdxN1 n hn9]
          simpa [hsrcN2, hsrcN1, hsrc0]
        _ = (move (cup2System n hn4) src (cup2BoundaryIdxN1 n hn9)
              (cup2BoundaryIdxN1 n hn9)).1 := by
          symm
          exact move_apply_self_val n hn4 src (cup2BoundaryIdxN1 n hn9)
    · rw [move_apply_ne n hn4 src (cup2BoundaryIdxN1 n hn9) i hi]
      simpa [src, hi]

private theorem pn1_011_leftFrame_c2_zero_or_two_tpReachable_fc_le
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (d0 : Config (cup2Spec n hn4))
    (hdN3 : (d0 (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hdN2 : (d0 (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hdN1 : (d0 (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hd0 : (d0 (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hd1 : (d0 (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hd2 : (d0 (cup2BoundaryIdx2 n hn9)).1 = 0 ∨
      (d0 (cup2BoundaryIdx2 n hn9)).1 = 2)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 d0 d) :
    cup2Fc n hn4 d ≤ cup2Fc n hn4 d0 := by
  rcases pn1_011_leftFrame_c2_zero_or_two_as_postmove n hn4 hn9 d0
      hdN3 hdN2 hdN1 hd0 hd1 hd2 with
    ⟨src, hsrcN3, hsrcN2, hsrcN1, hsrc0, hsrc1, hsrc2, rfl⟩
  exact pn1_011_c1_two_c2_zero_or_two_tpReachable_fc_le_core n hn4 hn9 src
    hsrcN3 hsrcN2 hsrcN1 hsrc0 hsrc1 hsrc2 hreach



private theorem pn1_011_c1_one_idx1_fc_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
      cup2Fc n hn4 c := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx1 n hn9)
        (c (left (cup2BoundaryIdx1 n hn9))).1
        (c (cup2BoundaryIdx1 n hn9)).1
        (c (right (cup2BoundaryIdx1 n hn9))).1 = 2 := by
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    have hlow112 : TLowVal 1 1 2 = 2 := lookup_low_112
    simpa [hc0, hc1, hc2] using hlow112
  rw [cup2Fc_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdx1 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
  rw [left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
  simp [localFcAfter, localFcBefore, frontierBitVal, hc0, hc1, hc2]

private theorem pn1_011_c1_one_idx1_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
        cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
      have hlow112 : TLowVal 1 1 2 = 2 := lookup_low_112
      simpa [hc0, hc1, hc2] using hlow112
    exact not_mem_goodCycle_of_cN2_zero_cN1_one_c0_one_c1_two n hn4 hn9 hN2' hN1' h0' h1'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    have hlow112 : TLowVal 1 1 2 = 2 := lookup_low_112
    simpa [hc0, hc1, hc2, hlow112] using (show (2 : Nat) ≠ 1 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx1 n hn9, hpriv, rfl⟩⟩

private theorem pn1_011_c1_one_idx1_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2TpPreservingMove n hn4 c (cup2BoundaryIdx1 n hn9) := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx1 n hn9)
        (c (left (cup2BoundaryIdx1 n hn9))).1
        (c (cup2BoundaryIdx1 n hn9)).1
        (c (right (cup2BoundaryIdx1 n hn9))).1 = 2 := by
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    have hlow112 : TLowVal 1 1 2 = 2 := lookup_low_112
    simpa [hc0, hc1, hc2] using hlow112
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1 2 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1 2
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    rw [localExp2After, localExp2Before, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Int21_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
    have hzero_left_before :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_left_after :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1 2 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_before :
        cup2Int21BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_after :
        cup2Int21BitVal n (cup2BoundaryIdx1 n hn9).1 2
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    rw [localInt21After, localInt21Before, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1 2 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1 2
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    rw [localExp2WeightAfter, localExp2WeightBefore,
      left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem pn1_011_c1_one_phi_lower
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
  let c1' := move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)
  have hbad1 :=
    pn1_011_c1_one_idx1_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1 hc2
  have htp1 :=
    pn1_011_c1_one_idx1_tpPreserving n hn4 hn9 c hc0 hc1 hc2
  have hcN1' : (c1' (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hcN2' : (c1' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hc0' : (c1' (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0
  have hc1' : (c1' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    have hlow112 : TLowVal 1 1 2 = 2 := lookup_low_112
    simpa [hc0, hc1, hc2] using hlow112
  have hbad2 :=
    p0_112_idx0_badStep n hn4 hn9 c1' hbad1.2.1 hcN2' hcN1' hc0' hc1'
  have htp2 :=
    p0_112_idx0_tpPreserving n hn4 hn9 c1' hcN1' hc0' hc1'
  have hreach1 : cup2TpReachable n hn4 c c1' :=
    cup2TpReachable_step n hn4 ⟨hbad1, by simpa [cup2TpPreservingMove] using htp1⟩
  have hreach2 : cup2TpReachable n hn4 c
      (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) :=
    cup2TpReachable_trans n hn4 hreach1
      (cup2TpReachable_step n hn4 ⟨hbad2, by simpa [cup2TpPreservingMove] using htp2⟩)
  have hfc_gain :
      cup2Fc n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) =
        cup2Fc n hn4 c + 1 := by
    have hfc1 := pn1_011_c1_one_idx1_fc_eq n hn4 hn9 c hc0 hc1 hc2
    have hfc2 := p0_112_idx0_fc_up_one n hn4 hn9 c1' hcN1' hc0' hc1'
    calc
      cup2Fc n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) =
          cup2Fc n hn4 c1' + 1 := hfc2
      _ = cup2Fc n hn4 c + 1 := by rw [hfc1]
  calc
    cup2Fc n hn4 c + 1 =
        cup2Fc n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) := by
      rw [hfc_gain]
    _ ≤ cup2PhiFull n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) :=
      cup2Fc_le_cup2PhiFull n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9))
    _ ≤ cup2PhiFull n hn4 c := cup2PhiFull_mono n hn4 hreach2

private def pn1_011_c1_one_srcBoundary : SixBoundary :=
  { c0 := (⟨1, by decide⟩ : Fin 2)
    c1 := (⟨1, by decide⟩ : Fin 3)
    c2 := (⟨2, by decide⟩ : Fin 3)
    cN3 := (⟨2, by decide⟩ : Fin 3)
    cN2 := (⟨0, by decide⟩ : Fin 3)
    cN1 := (⟨1, by decide⟩ : Fin 2) }

private def pn1_011_c1_one_dstA : SixBoundary :=
  boundarySuccPN1 pn1_011_c1_one_srcBoundary

private def pn1_011_c1_one_dstB : SixBoundary :=
  boundarySuccP1 pn1_011_c1_one_dstA

private theorem pn1_011_c1_one_source_boundary
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Boundary6 n hn4 hn9 c = pn1_011_c1_one_srcBoundary := by
  ext <;> simp [cup2Boundary6, pn1_011_c1_one_srcBoundary, hcN3, hcN2, hcN1, hc0, hc1, hc2]

private theorem pn1_011_c1_one_post_boundary
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
      pn1_011_c1_one_dstA := by
  rw [cup2Boundary6_move_eq_boundarySuccPN1 n hn4 hn9 c,
    pn1_011_c1_one_source_boundary n hn4 hn9 c hcN3 hcN2 hcN1 hc0 hc1 hc2]
  rfl

private theorem pn1_200_c1_zero_idx0_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    exact not_mem_goodCycle_of_cN2_two_cN1_zero n hn4 hn9 hN2' hN1'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot : TBotVal 0 0 0 = 1 := lookup_bot_000
    simpa [hcN1, hc0, hc1, hbot] using (show (1 : Nat) ≠ 0 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx0 n hn9, hpriv, rfl⟩⟩

private theorem pn1_200_c1_zero_idx0_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0) :
    cup2TpPreservingMove n hn4 c (cup2BoundaryIdx0 n hn9) := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx0 n hn9)
        (c (left (cup2BoundaryIdx0 n hn9))).1
        (c (cup2BoundaryIdx0 n hn9)).1
        (c (right (cup2BoundaryIdx0 n hn9))).1 = 1 := by
    rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot : TBotVal 0 0 0 = 1 := lookup_bot_000
    simpa [hcN1, hc0, hc1] using hbot
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
    rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simp [localExp2After, localExp2Before, cup2Exp2BitVal, hcN1, hc0, hc1]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Int21_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
    rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simp [localInt21After, localInt21Before, cup2Int21BitVal, hcN1, hc0, hc1]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2BoundaryIdx0 n hn9), hout]
    rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simp [localExp2WeightAfter, localExp2WeightBefore, cup2Exp2BitVal, hcN1, hc0, hc1]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem p0_001_c2_two_phi_lower
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
  let c1' := move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)
  have hbad1 :=
    p0_012_idx1_badStep n hn4 hn9 c hbadc hcN1 hc0 hc1 hc2
  have htp1 :=
    p0_012_idx1_tpPreserving n hn4 hn9 c hc0 hc1 hc2
  have hcN1' : (c1' (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc0' : (c1' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0
  have hc1' : (c1' (cup2BoundaryIdx1 n hn9)).1 = 0 := by
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2] using lookup_low_012
  have hc2' : (c1' (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx1] at hval
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hbad2 :=
    p0_000_c2_two_idx0_badStep n hn4 hn9 c1' hbad1.2.1 hcN1' hc0' hc1' hc2'
  have htp2 : cup2TpPreservingMove n hn4 c1' (cup2BoundaryIdx0 n hn9) := by
    exact pn1_200_c1_zero_idx0_tpPreserving n hn4 hn9 c1' hcN1' hc0' hc1'
  have hreach1 : cup2TpReachable n hn4 c c1' :=
    cup2TpReachable_step n hn4 ⟨hbad1, by simpa [cup2TpPreservingMove] using htp1⟩
  have hreach2 : cup2TpReachable n hn4 c
      (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) :=
    cup2TpReachable_trans n hn4 hreach1
      (cup2TpReachable_step n hn4 ⟨hbad2, by simpa [cup2TpPreservingMove] using htp2⟩)
  have hfc1 := p0_012_idx1_fc_down_one n hn4 hn9 c hc0 hc1 hc2
  have hfc2 := pn1_200_c1_zero_idx0_fc_gain n hn4 hn9 c1' hcN1' hc0' hc1'
  have hfc_gain :
      cup2Fc n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) =
        cup2Fc n hn4 c + 1 := by
    calc
      cup2Fc n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) =
          cup2Fc n hn4 c1' + 2 := hfc2
      _ = (cup2Fc n hn4 c1' + 1) + 1 := by omega
      _ = cup2Fc n hn4 c + 1 := by rw [hfc1]
  calc
    cup2Fc n hn4 c + 1 =
        cup2Fc n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) := by
      rw [hfc_gain]
    _ ≤ cup2PhiFull n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) :=
      cup2Fc_le_cup2PhiFull n hn4 (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9))
    _ ≤ cup2PhiFull n hn4 c := cup2PhiFull_mono n hn4 hreach2

private theorem pn1_200_c1_two_idx1_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    exact not_mem_goodCycle_of_cN2_two_cN1_zero n hn4 hn9 hN2' hN1'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    have hlow : TLowVal 0 2 2 = 0 := lookup_low_022
    simpa [hc0, hc1, hc2, hlow] using (show (0 : Nat) ≠ 2 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx1 n hn9, hpriv, rfl⟩⟩

private theorem pn1_200_c1_two_idx1_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2TpPreservingMove n hn4 c (cup2BoundaryIdx1 n hn9) := by
  have hout :
      cup2OutVal n (cup2BoundaryIdx1 n hn9)
        (c (left (cup2BoundaryIdx1 n hn9))).1
        (c (cup2BoundaryIdx1 n hn9)).1
        (c (right (cup2BoundaryIdx1 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2] using lookup_low_022
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        cup2Exp2Count n hn4 c := by
    rw [cup2Exp2_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1 0 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdx1 n hn9).1 0
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    rw [localExp2After, localExp2Before,
      left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9,
      hzero_left_after, hzero_left_before,
      hzero_right_after, hzero_right_before]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        cup2Int21Count n hn4 c := by
    rw [cup2Int21_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Int21_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
    have hzero_left_before :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_left_after :
        cup2Int21BitVal n (cup2BoundaryIdx0 n hn9).1
          (c (cup2BoundaryIdx0 n hn9)).1 0 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx0]
    have hzero_right_before :
        cup2Int21BitVal n (cup2BoundaryIdx1 n hn9).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    have hzero_right_after :
        cup2Int21BitVal n (cup2BoundaryIdx1 n hn9).1 0
          (c (cup2BoundaryIdx2 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_lt_two
      simp [cup2BoundaryIdx1]
    rw [localInt21After, localInt21Before,
      left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9,
      hzero_left_after, hzero_left_before,
      hzero_right_after, hzero_right_before]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    rw [cup2Exp2Weight_move_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2BoundaryIdx1 n hn9), hout]
    rw [left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simp [localExp2WeightAfter, localExp2WeightBefore, cup2Exp2BitVal, hc0, hc1, hc2]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem p0_022_idx1_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
      exact hcN2
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h2' :
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2BoundaryIdx1] at hval
      rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
      exact hc2
    exact not_mem_goodCycle_of_cN2_zero_cN1_one_c0_zero_c2_two n hn4 hn9 hN2' hN1' h0' h2'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2, lookup_low_022] using (show (0 : Nat) ≠ 2 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdx1 n hn9, hpriv, rfl⟩⟩

private theorem p0_022_idx1_tpStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2TpBadStepFwd n hn4 c
      (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) := by
  refine ⟨p0_022_idx1_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1 hc2, ?_⟩
  simpa [cup2TpPreservingMove] using pn1_200_c1_two_idx1_tpPreserving n hn4 hn9 c hc0 hc1 hc2

private theorem p0_002_idxN1_badStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    badStep (cup2System n hn4) (cup2GoodCycle n hn4)
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) c := by
  have hdest_bad :
      move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) ∉ (cup2GoodCycle n hn4).configs := by
    have hN1' :
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      rw [move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
        cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
      have htop010 : TTopVal 0 1 0 = 0 := by native_decide
      simpa [hcN2, hcN1, hc0] using htop010
    have h0' :
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc0
    have h2' :
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
        omega
      rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
      exact hc2
    exact not_mem_goodCycle_of_cN1_zero_c0_zero_c2_two n hn4 hn9 hN1' h0' h2'
  have hpriv : privileged (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) := by
    unfold privileged cup2System
    rw [Fin.ne_iff_vne, cup2Trans_val]
    rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    have htop010 : TTopVal 0 1 0 = 0 := by native_decide
    simpa [hcN2, hcN1, hc0, htop010] using (show (0 : Nat) ≠ 1 by decide)
  exact ⟨hbadc, hdest_bad, ⟨cup2BoundaryIdxN1 n hn9, hpriv, rfl⟩⟩

private theorem p0_002_idxN1_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0) :
    cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN1 n hn9) := by
  have hout :
      cup2OutVal n (cup2BoundaryIdxN1 n hn9)
        (c (left (cup2BoundaryIdxN1 n hn9))).1
        (c (cup2BoundaryIdxN1 n hn9)).1
        (c (right (cup2BoundaryIdxN1 n hn9))).1 = 0 := by
    rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    have htop010 : TTopVal 0 1 0 = 0 := by native_decide
    simpa [hcN2, hcN1, hc0] using htop010
  have hExp2 :
      cup2Exp2Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        cup2Exp2Count n hn4 c := by
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1 0 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1 0
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    rw [cup2Exp2_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Exp2_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Exp2_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9), hout]
    rw [localExp2After, localExp2Before, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hInt21 :
      cup2Int21Count n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        cup2Int21Count n hn4 c := by
    have hzero_left_before :
        cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_left_after :
        cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1 0 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_right_before :
        cup2Int21BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_after :
        cup2Int21BitVal n (cup2BoundaryIdxN1 n hn9).1 0
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Int21BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    rw [cup2Int21_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Int21_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Int21_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9), hout]
    rw [localInt21After, localInt21Before, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  have hWeight :
      cup2Exp2Weight n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        cup2Exp2Weight n hn4 c := by
    have hzero_left_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_left_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
          (c (cup2BoundaryIdxN2 n hn9)).1 0 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN2]
      omega
    have hzero_right_before :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    have hzero_right_after :
        cup2Exp2BitVal n (cup2BoundaryIdxN1 n hn9).1 0
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      apply cup2Exp2BitVal_eq_zero_of_ge_top
      simp [cup2BoundaryIdxN1]
      omega
    rw [cup2Exp2Weight_move_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Exp2Weight_split n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2Exp2Weight_rest_move_eq n hn4 c (cup2BoundaryIdxN1 n hn9), hout]
    rw [localExp2WeightAfter, localExp2WeightBefore,
      left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9,
      hzero_left_after, hzero_left_before, hzero_right_after, hzero_right_before]
  unfold cup2TpPreservingMove cup2TpInvariant
  simp [hExp2, hInt21, hWeight]

private theorem p0_002_idxN1_tpStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2TpBadStepFwd n hn4 c
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) := by
  refine ⟨p0_002_idxN1_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc2, ?_⟩
  simpa [cup2TpPreservingMove] using p0_002_idxN1_tpPreserving n hn4 hn9 c hcN2 hcN1 hc0

private theorem p0_002_right_two_step_tpReachable
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    let c1 := move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
    let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx0 n hn9)
    (c2 (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      (c2 (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
      (c2 (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      (c2 (cup2BoundaryIdx1 n hn9)).1 = 0 ∧
      (c2 (cup2BoundaryIdx2 n hn9)).1 = 2 ∧
      cup2TpReachable n hn4 c c2 := by
  let c1 := move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
  let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx0 n hn9)
  have hstep1 := p0_002_idxN1_tpStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc2
  have hc1N2 : (c1 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hc1N1 : (c1 (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    have htop010 : TTopVal 0 1 0 = 0 := by native_decide
    simpa [hcN2, hcN1, hc0] using htop010
  have hc10 : (c1 (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0
  have hc11 : (c1 (cup2BoundaryIdx1 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1
  have hc12 : (c1 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hbad2 := p0_000_c2_two_idx0_badStep n hn4 hn9 c1 hstep1.1.2.1 hc1N1 hc10 hc11 hc12
  have htp2 : cup2TpPreservingMove n hn4 c1 (cup2BoundaryIdx0 n hn9) := by
    exact pn1_200_c1_zero_idx0_tpPreserving n hn4 hn9 c1 hc1N1 hc10 hc11
  have hreach1 : cup2TpReachable n hn4 c c1 :=
    cup2TpReachable_step n hn4 hstep1
  have hreach2 : cup2TpReachable n hn4 c c2 :=
    cup2TpReachable_trans n hn4 hreach1
      (cup2TpReachable_step n hn4 ⟨hbad2, by simpa [cup2TpPreservingMove] using htp2⟩)
  have hc2N2 : (c2 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hc1N2
  have hc2N1 : (c2 (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc1N1
  have hc20 : (c2 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c1 (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hc1N1, hc10, hc11] using lookup_bot_000
  have hc21 : (c2 (cup2BoundaryIdx1 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc11
  have hc22 : (c2 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc12
  exact ⟨hc2N2, hc2N1, hc20, hc21, hc22, hreach2⟩

private theorem p1_112_idx1_tpStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2TpBadStepFwd n hn4 c
      (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) := by
  refine ⟨pn1_011_c1_one_idx1_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1 hc2, ?_⟩
  simpa [cup2TpPreservingMove] using pn1_011_c1_one_idx1_tpPreserving n hn4 hn9 c hc0 hc1 hc2

private theorem p1_122_idx0_tpStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2) :
    cup2TpBadStepFwd n hn4 c
      (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) := by
  refine ⟨p0_112_idx0_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1, ?_⟩
  simpa [cup2TpPreservingMove] using p0_112_idx0_tpPreserving n hn4 hn9 c hcN1 hc0 hc1

theorem p1_full_exact_four_step_tpReachable
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
    let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9)
    let c3 := move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9)
    let c4 := move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)
    cup2TpReachable n hn4 c c4 := by
  let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
  let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9)
  let c3 := move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9)
  let c4 := move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)
  have hstep1 : cup2TpBadStepFwd n hn4 c c1 := by
    simpa [c1] using p1_012_idx0_tpStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1
  have hc1N2 : (c1 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hc1N1 : (c1 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc10 : (c1 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
    simpa [hcN1, hc0, hc1] using hbot101
  have hc11 : (c1 (cup2BoundaryIdx1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1
  have hc12 : (c1 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hstep2 : cup2TpBadStepFwd n hn4 c1 c2 := by
    have hc1bad : c1 ∉ (cup2GoodCycle n hn4).configs := hstep1.1.2.1
    simpa [c2] using p1_112_idx1_tpStep n hn4 hn9 c1 hc1bad hc1N2 hc1N1 hc10 hc11 hc12
  have hc2N2 : (c2 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hc1N2
  have hc2N1 : (c2 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc1N1
  have hc20 : (c2 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc10
  have hc21 : (c2 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c1 (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc10, hc11, hc12] using lookup_low_112
  have hstep3 : cup2TpBadStepFwd n hn4 c2 c3 := by
    have hc2bad : c2 ∉ (cup2GoodCycle n hn4).configs := hstep2.1.2.1
    simpa [c3] using p1_122_idx0_tpStep n hn4 hn9 c2 hc2bad hc2N2 hc2N1 hc20 hc21
  have hc3N2 : (c3 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hc2N2
  have hc3N1 : (c3 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc2N1
  have hc30 : (c3 (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c2 (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hc2N1, hc20, hc21] using lookup_bot_112
  have hc31 : (c3 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc21
  have hc32 : (c3 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc12
  have hstep4 : cup2TpBadStepFwd n hn4 c3 c4 := by
    have hc3bad : c3 ∉ (cup2GoodCycle n hn4).configs := hstep3.1.2.1
    simpa [c4] using p0_022_idx1_tpStep n hn4 hn9 c3 hc3bad hc3N2 hc3N1 hc30 hc31 hc32
  exact cup2TpReachable_trans n hn4
    (cup2TpReachable_step n hn4 hstep1)
    (cup2TpReachable_trans n hn4
      (cup2TpReachable_step n hn4 hstep2)
      (cup2TpReachable_trans n hn4
        (cup2TpReachable_step n hn4 hstep3)
        (cup2TpReachable_step n hn4 hstep4)))

theorem p1_full_exact_four_step_fc_down_one
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
    let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9)
    let c3 := move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9)
    let c4 := move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)
    cup2Fc n hn4 c4 + 1 = cup2Fc n hn4 c := by
  let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
  let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9)
  let c3 := move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9)
  let c4 := move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)
  have hc1N1 : (c1 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc10 : (c1 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
    simpa [hcN1, hc0, hc1] using hbot101
  have hc11 : (c1 (cup2BoundaryIdx1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1
  have hc12 : (c1 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hc2N1 : (c2 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc1N1
  have hc20 : (c2 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc10
  have hc21 : (c2 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c1 (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc10, hc11, hc12] using lookup_low_112
  have hc3N1 : (c3 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc2N1
  have hc30 : (c3 (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c2 (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hc2N1, hc20, hc21] using lookup_bot_112
  have hc31 : (c3 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc21
  have hc32 : (c3 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc12
  have hfc0 := p1_012_idx0_fc_down_one n hn4 hn9 c hcN1 hc0 hc1
  have hfc1 := pn1_011_c1_one_idx1_fc_eq n hn4 hn9 c1 hc10 hc11 hc12
  have hfc2 := p0_112_idx0_fc_up_one n hn4 hn9 c2 hc2N1 hc20 hc21
  have hfc3 := pn1_200_c1_two_idx1_fc_eq n hn4 hn9 c3 hc30 hc31 hc32
  calc
    cup2Fc n hn4 c4 + 1 = cup2Fc n hn4 c3 + 1 := by
      rw [show c4 = move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9) by rfl]
      rw [hfc3]
    _ = cup2Fc n hn4 c2 + 2 := by
      rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl]
      rw [hfc2]
    _ = cup2Fc n hn4 c1 + 2 := by rw [hfc1]
    _ = cup2Fc n hn4 c := by
      rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl]
      exact p1_012_idx0_fc_down_one n hn4 hn9 c hcN1 hc0 hc1

private theorem p1_full_exact_four_step_endpoint_boundary
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 1)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
    let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9)
    let c3 := move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9)
    let c4 := move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)
    (c4 (cup2BoundaryIdxN3 n hn9)).1 = 1 ∧
      (c4 (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      (c4 (cup2BoundaryIdxN1 n hn9)).1 = 1 ∧
      (c4 (cup2BoundaryIdx0 n hn9)).1 = 0 ∧
      (c4 (cup2BoundaryIdx1 n hn9)).1 = 0 ∧
      (c4 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
  let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
  let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9)
  let c3 := move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9)
  let c4 := move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)
  have hc1N3 : (c1 (cup2BoundaryIdxN3 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN3, cup2BoundaryIdx0] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN3 n hn9) hne]
    exact hcN3
  have hc1N2 : (c1 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hc1N1 : (c1 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc10 : (c1 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
    simpa [hcN1, hc0, hc1] using hbot101
  have hc11 : (c1 (cup2BoundaryIdx1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1
  have hc12 : (c1 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hc2N3 : (c2 (cup2BoundaryIdxN3 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN3, cup2BoundaryIdx1] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN3 n hn9) hne]
    exact hc1N3
  have hc2N2 : (c2 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hc1N2
  have hc2N1 : (c2 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc1N1
  have hc20 : (c2 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc10
  have hc21 : (c2 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c1 (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc10, hc11, hc12] using lookup_low_112
  have hc22 : (c2 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx1] at hval
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc12
  have hc3N3 : (c3 (cup2BoundaryIdxN3 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN3, cup2BoundaryIdx0] at hval
      omega
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN3 n hn9) hne]
    exact hc2N3
  have hc3N2 : (c3 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hc2N2
  have hc3N1 : (c3 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc2N1
  have hc30 : (c3 (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c2 (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hc2N1, hc20, hc21] using lookup_bot_112
  have hc31 : (c3 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc21
  have hc32 : (c3 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc22
  have hc4N3 : (c4 (cup2BoundaryIdxN3 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN3, cup2BoundaryIdx1] at hval
      omega
    rw [show c4 = move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c3 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN3 n hn9) hne]
    exact hc3N3
  have hc4N2 : (c4 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
      omega
    rw [show c4 = move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c3 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hc3N2
  have hc4N1 : (c4 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [show c4 = move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c3 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc3N1
  have hc40 : (c4 (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [show c4 = move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c3 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc30
  have hc41 : (c4 (cup2BoundaryIdx1 n hn9)).1 = 0 := by
    rw [show c4 = move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c3 (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc30, hc31, hc32] using lookup_low_022
  have hc42 : (c4 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx1] at hval
    rw [show c4 = move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c3 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc32
  exact ⟨hc4N3, hc4N2, hc4N1, hc40, hc41, hc42⟩

/-

private theorem p1_full_exact_four_step_endpoint_eq_direct_idx1
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
    let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9)
    let c3 := move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9)
    let c4 := move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)
    c4 = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) := by
  let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
  let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9)
  let c3 := move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9)
  let c4 := move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)
  funext i
  by_cases hi0 : i = cup2BoundaryIdx0 n hn9
  · subst i
    have hc10 : (c1 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
        move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
        cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
      have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
      simpa [hcN1, hc0, hc1] using hbot101
    have hc11 : (c1 (cup2BoundaryIdx1 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
      rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
        move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    have hc12 : (c1 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
      have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
      rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
        move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
      exact hc2
    have hc20 : (c2 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
      rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
        move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
      exact hc10
    have hc21 : (c2 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
      rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
        move_apply_self_val n hn4 c1 (cup2BoundaryIdx1 n hn9),
        cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
      simpa [hc10, hc11, hc12] using lookup_low_112
    have hc2N1 : (c2 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
        omega
      rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
        move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have hc30 : (c3 (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
        move_apply_self_val n hn4 c2 (cup2BoundaryIdx0 n hn9),
        cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
      simpa [hc2N1, hc20, hc21] using lookup_bot_112
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    change (move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)) (cup2BoundaryIdx0 n hn9) =
      (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) (cup2BoundaryIdx0 n hn9)
    rw [move_apply_ne n hn4 c3 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    apply Fin.ext
    simpa [hc30, hc0]
  · by_cases hi1 : i = cup2BoundaryIdx1 n hn9
    · subst i
      have hc10 : (c1 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
        rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
          move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
          cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
        have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
        simpa [hcN1, hc0, hc1] using hbot101
      have hc11 : (c1 (cup2BoundaryIdx1 n hn9)).1 = 1 := by
        have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
        rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
          move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
        exact hc1
      have hc12 : (c1 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
        have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
        rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
          move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
        exact hc2
      have hc21 : (c2 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
        rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
          move_apply_self_val n hn4 c1 (cup2BoundaryIdx1 n hn9),
          cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
        simpa [hc10, hc11, hc12] using lookup_low_112
      have hc32 : (c3 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
        have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
        rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
          move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
        exact hc12
      change (move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)) (cup2BoundaryIdx1 n hn9) =
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) (cup2BoundaryIdx1 n hn9)
      rw [move_apply_self_val n hn4 c3 (cup2BoundaryIdx1 n hn9),
        cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9,
        show move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx1 n hn9) =
            ⟨0, by simp [cup2Spec, cup2M]⟩ by
          rw [move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
            cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
          simpa [hc0, hc1, hc2] using lookup_low_012]
      simp [lookup_low_022, hc32]
    · have hne1 : i ≠ cup2BoundaryIdx1 n hn9 := hi1
      change (move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)) i =
        (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) i
      rw [move_apply_ne n hn4 c3 (cup2BoundaryIdx1 n hn9) i hne1,
        move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) i hi0,
        move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) i hne1,
        move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) i hi0,
        move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) i hne1]

private theorem p1_full_exact_suffix_tpReachable
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
    cup2TpReachable n hn4 c1 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) := by
  let c1 := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
  let c2 := move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9)
  let c3 := move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9)
  let c4 := move (cup2System n hn4) c3 (cup2BoundaryIdx1 n hn9)
  have hstep1 : cup2TpBadStepFwd n hn4 c c1 := by
    simpa [c1] using p1_012_idx0_tpStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1
  have hc1bad : c1 ∉ (cup2GoodCycle n hn4).configs := hstep1.1.2.1
  have hc1N2 : (c1 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hc1N1 : (c1 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc10 : (c1 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    have hbot101 : TBotVal 1 0 1 = 1 := by native_decide
    simpa [hcN1, hc0, hc1] using hbot101
  have hc11 : (c1 (cup2BoundaryIdx1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc1
  have hc12 : (c1 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c1 = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hstep2 : cup2TpBadStepFwd n hn4 c1 c2 := by
    simpa [c2] using p1_112_idx1_tpStep n hn4 hn9 c1 hc1bad hc1N2 hc1N1 hc10 hc11 hc12
  have hc2bad : c2 ∉ (cup2GoodCycle n hn4).configs := hstep2.1.2.1
  have hc2N2 : (c2 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hc1N2
  have hc2N1 : (c2 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc1N1
  have hc20 : (c2 (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c1 (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc10
  have hc21 : (c2 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    rw [show c2 = move (cup2System n hn4) c1 (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c1 (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc10, hc11, hc12] using lookup_low_112
  have hstep3 : cup2TpBadStepFwd n hn4 c2 c3 := by
    simpa [c3] using p1_122_idx0_tpStep n hn4 hn9 c2 hc2bad hc2N2 hc2N1 hc20 hc21
  have hc3bad : c3 ∉ (cup2GoodCycle n hn4).configs := hstep3.1.2.1
  have hc3N2 : (c3 (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx0] at hval
      omega
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hc2N2
  have hc3N1 : (c3 (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
      omega
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hc2N1
  have hc30 : (c3 (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_self_val n hn4 c2 (cup2BoundaryIdx0 n hn9),
      cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
    simpa [hc2N1, hc20, hc21] using lookup_bot_112
  have hc31 : (c3 (cup2BoundaryIdx1 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
    exact hc21
  have hc32 : (c3 (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx0] at hval
    rw [show c3 = move (cup2System n hn4) c2 (cup2BoundaryIdx0 n hn9) by rfl,
      move_apply_ne n hn4 c2 (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc12
  have hstep4 : cup2TpBadStepFwd n hn4 c3 c4 := by
    simpa [c4] using p0_022_idx1_tpStep n hn4 hn9 c3 hc3bad hc3N2 hc3N1 hc30 hc31 hc32
  have hsuffix :
      cup2TpReachable n hn4 c1 c4 := by
    exact cup2TpReachable_trans n hn4
      (cup2TpReachable_step n hn4 hstep2)
      (cup2TpReachable_trans n hn4
        (cup2TpReachable_step n hn4 hstep3)
        (cup2TpReachable_step n hn4 hstep4))
  have hEq : c4 = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) := by
    exact p1_full_exact_four_step_endpoint_eq_direct_idx1 n hn4 hn9 c hcN1 hc0 hc1 hc2
  simpa [c1, c4, hEq] using hsuffix

-/

private theorem pn1_200_c1_zero_future_lower
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0) :
    cup2Fc n hn4 c + 2 ≤ cup2FutureFc n hn4 c := by
  have hbad0 :=
    pn1_200_c1_zero_idx0_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1
  have hgain :=
    pn1_200_c1_zero_idx0_fc_gain n hn4 hn9 c hcN1 hc0 hc1
  calc
    cup2Fc n hn4 c + 2 = cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) := by
      omega
    _ ≤ cup2FutureFc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) :=
      cup2Fc_le_cup2FutureFc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))
    _ ≤ cup2FutureFc n hn4 c := cup2FutureFc_mono n hn4 (cup2BadReachable_step n hn4 hbad0)

private theorem pn1_200_c1_two_future_lower
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Fc n hn4 c + 2 ≤ cup2FutureFc n hn4 c := by
  have hbad1 :=
    pn1_200_c1_two_idx1_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1 hc2
  let c1' := move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)
  have hcN2' : (c1' (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hcN1' : (c1' (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc0' : (c1' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0
  have hc1' : (c1' (cup2BoundaryIdx1 n hn9)).1 = 0 := by
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2] using lookup_low_022
  have hbad2 :=
    pn1_200_c1_zero_idx0_badStep n hn4 hn9 c1' hbad1.2.1 hcN2' hcN1' hc0' hc1'
  have hgain :=
    pn1_200_c1_two_idx1_then_idx0_fc_gain n hn4 hn9 c hcN1 hc0 hc1 hc2
  calc
    cup2Fc n hn4 c + 2 =
        cup2Fc n hn4
          (move (cup2System n hn4)
            (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
            (cup2BoundaryIdx0 n hn9)) := by
      omega
    _ ≤ cup2FutureFc n hn4
          (move (cup2System n hn4)
            (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
            (cup2BoundaryIdx0 n hn9)) :=
      cup2Fc_le_cup2FutureFc n hn4
        (move (cup2System n hn4)
          (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
          (cup2BoundaryIdx0 n hn9))
    _ ≤ cup2FutureFc n hn4 c :=
      cup2FutureFc_mono n hn4
        (cup2BadReachable_of_step n hn4 (cup2BadReachable_step n hn4 hbad1) hbad2)

private theorem pn1_200_c1_two_phi_lower
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hbadc : c ∉ (cup2GoodCycle n hn4).configs)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    cup2Fc n hn4 c + 2 ≤ cup2PhiFull n hn4 c := by
  have hbad1 :=
    pn1_200_c1_two_idx1_badStep n hn4 hn9 c hbadc hcN2 hcN1 hc0 hc1 hc2
  have htp1 :=
    pn1_200_c1_two_idx1_tpPreserving n hn4 hn9 c hc0 hc1 hc2
  let c1' := move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)
  have hcN2' : (c1' (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hcN1' : (c1' (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc0' : (c1' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0
  have hc1' : (c1' (cup2BoundaryIdx1 n hn9)).1 = 0 := by
    rw [show c1' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) by rfl,
      move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2] using lookup_low_022
  have hbad2 :=
    pn1_200_c1_zero_idx0_badStep n hn4 hn9 c1' hbad1.2.1 hcN2' hcN1' hc0' hc1'
  have htp2 : cup2TpPreservingMove n hn4 c1' (cup2BoundaryIdx0 n hn9) := by
    exact pn1_200_c1_zero_idx0_tpPreserving n hn4 hn9 c1' hcN1' hc0' hc1'
  have hreach1 : cup2TpReachable n hn4 c c1' :=
    cup2TpReachable_step n hn4 ⟨hbad1, by simpa [cup2TpPreservingMove] using htp1⟩
  have hreach2 : cup2TpReachable n hn4 c
      (move (cup2System n hn4) c1' (cup2BoundaryIdx0 n hn9)) :=
    cup2TpReachable_trans n hn4 hreach1
      (cup2TpReachable_step n hn4 ⟨hbad2, by simpa [cup2TpPreservingMove] using htp2⟩)
  have hfc_gain :=
    pn1_200_c1_two_idx1_then_idx0_fc_gain n hn4 hn9 c hcN1 hc0 hc1 hc2
  calc
    cup2Fc n hn4 c + 2 =
        cup2Fc n hn4
          (move (cup2System n hn4)
            (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
            (cup2BoundaryIdx0 n hn9)) := by
      omega
    _ ≤ cup2PhiFull n hn4
          (move (cup2System n hn4)
            (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
            (cup2BoundaryIdx0 n hn9)) :=
      cup2Fc_le_cup2PhiFull n hn4
        (move (cup2System n hn4)
          (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
          (cup2BoundaryIdx0 n hn9))
    _ ≤ cup2PhiFull n hn4 c := cup2PhiFull_mono n hn4 hreach2

private theorem cup2PhiFull_ge_of_tpReachable
    (n : Nat) (hn4 : 4 ≤ n)
    {c d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4 c d) :
    cup2Fc n hn4 d ≤ cup2PhiFull n hn4 c := by
  exact le_trans
    (cup2Fc_le_cup2PhiFull n hn4 d)
    (cup2PhiFull_mono n hn4 hreach)

private theorem pn1_200_postmove_badStepPos_is_B5
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {d c e : Config (cup2Spec n hn4)}
    (hpost : d = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hpos : cup2BadStepPos n hn4 e d) :
    ∃ i, e = move (cup2System n hn4) d i ∧ IsB5Config n hn4 d i := by
  have hdN2 : (d (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
    rw [hpost]
    have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
      omega
    rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
    exact hcN2
  have hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    rw [hpost, move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    have htop200 : TTopVal 2 0 0 = 1 := by native_decide
    simpa [hcN2, hcN1, hc0] using htop200
  have hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 0 := by
    rw [hpost]
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
      omega
    rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0
  rcases cup2BadStepPos_classified n hn4 hpos with ⟨i, hmove, hclass⟩
  rcases hclass with hB1 | hB2 | hB3 | hB4 | hB5
  · rcases hB1 with ⟨hi0, hL, _hS, _hR⟩
    have hi' : i = cup2BoundaryIdx0 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx0] using hi0
    have hL' : (d (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      calc
        (d (cup2BoundaryIdxN1 n hn9)).1 = (d (left i)).1 := by rw [hi', left_cup2BoundaryIdx0 n hn9]
        _ = 0 := hL
    rw [hdN1] at hL'
    omega
  · rcases hB2 with ⟨hi0, _hL, hS, _hR⟩
    have hi' : i = cup2BoundaryIdx0 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx0] using hi0
    have hS' : (d (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      calc
        (d (cup2BoundaryIdx0 n hn9)).1 = (d i).1 := by rw [hi']
        _ = 1 := hS
    rw [hd0] at hS'
    omega
  · rcases hB3 with ⟨hi, _hL, hS, _hR⟩
    have hi' : i = cup2BoundaryIdxN2 n hn9 := by
      apply Fin.ext
      simp [cup2BoundaryIdxN2]
      omega
    have hS' : (d (cup2BoundaryIdxN2 n hn9)).1 = 1 := by
      calc
        (d (cup2BoundaryIdxN2 n hn9)).1 = (d i).1 := by rw [hi']
        _ = 1 := hS
    rw [hdN2] at hS'
    omega
  · rcases hB4 with ⟨hi, _hL, hS, _hR⟩
    have hi' : i = cup2BoundaryIdxN1 n hn9 := by
      apply Fin.ext
      simp [cup2BoundaryIdxN1]
      omega
    have hS' : (d (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      calc
        (d (cup2BoundaryIdxN1 n hn9)).1 = (d i).1 := by rw [hi']
        _ = 0 := hS
    rw [hdN1] at hS'
    omega
  · exact ⟨i, hmove, hB5⟩

private theorem b5_deep_not_tpPreservingMove
    (n : Nat) (hn4 : 4 ≤ n)
    {c : Config (cup2Spec n hn4)} {i : Fin n}
    (hB5 : IsB5Config n hn4 c i)
    (h3 : 3 ≤ i.1) :
    ¬ cup2TpPreservingMove n hn4 c i := by
  intro htp
  rcases hB5 with ⟨_hi2, htop, hL, hS, hR⟩
  have h0 : i.1 ≠ 0 := by omega
  have h1 : i.1 ≠ 1 := by omega
  have htop' : i.1 + 1 ≠ n := by omega
  have hhigh : i.1 + 2 ≠ n := by omega
  have hout :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = 0 := by
    rw [cup2OutVal, if_neg h0, if_neg h1, if_neg htop', if_neg hhigh]
    simp [hL, hS, hR, TMidVal]
  obtain ⟨_hexp2, hi21, _hweight⟩ :=
    cup2TpPreserving_local_eqs n hn4 c i htp
  have hleftv : (left i).1 = i.1 - 1 := left_val_of_ne_zero h0
  have hleft_in : 2 ≤ (left i).1 := by
    rw [hleftv]
    omega
  have hleft_top : (left i).1 + 2 < n := by
    rw [hleftv]
    omega
  rw [localInt21After, localInt21Before, hout] at hi21
  rw [cup2Int21BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
    cup2Int21BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
    cup2Int21BitVal_eq_inner n i.1 _ _ (by omega) htop,
    cup2Int21BitVal_eq_inner n i.1 _ _ (by omega) htop] at hi21
  simp [hL, hS, hR] at hi21

/-- Destination-cap for Pn1:(2,0,0) c1=0: every TP-reachable config from c'
    has fc ≤ fc(c'). This implies PhiFull(c') = fc(c'), which combined with
    PhiFull(c) ≥ fc(c) + 2 contradicts PhiFull equality. -/
private theorem pn1_200_c1_zero_tpReachable_fc_le
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) d) :
    cup2Fc n hn4 d ≤
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) := by
  exact pn1_200_c1_zero_tpReachable_fc_le_core n hn4 hn9 c hcN2 hcN1 hc0 hc1 hreach

private theorem pn1_200_c1_zero_postmove_tp_nonpos
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0)
    {e : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) e) :
    cup2Fc n hn4 e ≤
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) := by
  by_cases hlt :
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) <
        cup2Fc n hn4 e
  · have hpos : cup2BadStepPos n hn4 e
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) :=
      ⟨hstep.1, hlt⟩
    rcases pn1_200_postmove_badStepPos_is_B5 n hn4 hn9 rfl hcN2 hcN1 hc0 hpos with
      ⟨i, hmove, hB5⟩
    rcases hB5 with ⟨hi2, htop, hL, hS, hR⟩
    by_cases hi_eq : i = cup2BoundaryIdx2 n hn9
    · have hd1 : (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
          (cup2BoundaryIdx1 n hn9)).1 = 0 := by
        have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
          omega
        rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9) hne]
        exact hc1
      subst hi_eq
      have hleft_zero : (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
          (left (cup2BoundaryIdx2 n hn9))).1 = 0 := by
        have hleft :
            (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
              (left (cup2BoundaryIdx2 n hn9))).1 =
              (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
                (cup2BoundaryIdx1 n hn9)).1 := by
          simpa using congrArg
            (fun j => (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) j).1)
            (left_cup2BoundaryIdx2 n hn9)
        rw [hleft]
        exact hd1
      rw [hL] at hleft_zero
      omega
    · have h3 : 3 ≤ i.1 := by
        have hi_ne_two : i.1 ≠ 2 := by
          intro hi_two
          apply hi_eq
          apply Fin.ext
          simpa [cup2BoundaryIdx2] using hi_two
        omega
      have htpMove : cup2TpPreservingMove n hn4
          (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) i := by
        simpa [cup2TpPreservingMove, hmove] using hstep.2
      exact False.elim <|
        (b5_deep_not_tpPreservingMove n hn4
          (c := move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
          (i := i) ⟨hi2, htop, hL, hS, hR⟩ h3) htpMove
  · exact le_of_not_gt hlt

private theorem pn1_200_c1_two_postmove_tp_nonpos
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    {e : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) e) :
    cup2Fc n hn4 e ≤
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) := by
  by_cases hlt :
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) <
        cup2Fc n hn4 e
  · have hpos : cup2BadStepPos n hn4 e
        (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) :=
      ⟨hstep.1, hlt⟩
    rcases pn1_200_postmove_badStepPos_is_B5 n hn4 hn9 rfl hcN2 hcN1 hc0 hpos with
      ⟨i, hmove, hB5⟩
    rcases hB5 with ⟨hi2, htop, hL, hS, hR⟩
    by_cases hi_eq : i = cup2BoundaryIdx2 n hn9
    · have hd2 : (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
          (cup2BoundaryIdx2 n hn9)).1 = 2 := by
        have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
          intro hEq
          have hval := congrArg Fin.val hEq
          simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
          omega
        rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
        exact hc2
      subst hi_eq
      rw [hS] at hd2
      omega
    · have h3 : 3 ≤ i.1 := by
        have hi_ne_two : i.1 ≠ 2 := by
          intro hi_two
          apply hi_eq
          apply Fin.ext
          simpa [cup2BoundaryIdx2] using hi_two
        omega
      have htpMove : cup2TpPreservingMove n hn4
          (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) i := by
        simpa [cup2TpPreservingMove, hmove] using hstep.2
      exact False.elim <|
        (b5_deep_not_tpPreservingMove n hn4
          (c := move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
          (i := i) ⟨hi2, htop, hL, hS, hR⟩ h3) htpMove
  · exact le_of_not_gt hlt

private theorem p0_001_postmove_tp_nonpos
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    {e : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4
      (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) e) :
    cup2Fc n hn4 e ≤
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) := by
  by_cases hlt :
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) <
        cup2Fc n hn4 e
  · have hpos : cup2BadStepPos n hn4 e
        (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) :=
      ⟨hstep.1, hlt⟩
    let d := move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)
    have hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
      have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdxN1, cup2BoundaryIdx0] at hval
        omega
      rw [show d = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
        move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
      exact hcN1
    have hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 1 := by
      rw [show d = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
        move_apply_self_val n hn4 c (cup2BoundaryIdx0 n hn9),
        cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
      have hbot001 : TBotVal 0 0 1 = 1 := by native_decide
      simpa [hcN1, hc0, hc1] using hbot001
    have hd1 : (d (cup2BoundaryIdx1 n hn9)).1 = 1 := by
      have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdx0 n hn9 := by
        intro hEq
        have hval := congrArg Fin.val hEq
        simp [cup2BoundaryIdx1, cup2BoundaryIdx0] at hval
      rw [show d = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) by rfl,
        move_apply_ne n hn4 c (cup2BoundaryIdx0 n hn9) (cup2BoundaryIdx1 n hn9) hne]
      exact hc1
    rcases cup2BadStepPos_classified n hn4 hpos with ⟨i, hmove, hclass⟩
    rcases hclass with hB1 | hB2 | hB3 | hB4 | hB5
    · rcases hB1 with ⟨hi0, _hL, hS, _hR⟩
      have hi' : i = cup2BoundaryIdx0 n hn9 := by
        apply Fin.ext
        simpa [cup2BoundaryIdx0] using hi0
      have hS' : (d (cup2BoundaryIdx0 n hn9)).1 = 0 := by
        calc
          (d (cup2BoundaryIdx0 n hn9)).1 = (d i).1 := by rw [hi']
          _ = 0 := hS
      rw [hd0] at hS'
      omega
    · rcases hB2 with ⟨hi0, hL, _hS, _hR⟩
      have hi' : i = cup2BoundaryIdx0 n hn9 := by
        apply Fin.ext
        simpa [cup2BoundaryIdx0] using hi0
      have hL' : (d (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
        calc
          (d (cup2BoundaryIdxN1 n hn9)).1 = (d (left i)).1 := by
            rw [hi', left_cup2BoundaryIdx0 n hn9]
          _ = 1 := hL
      rw [hdN1] at hL'
      omega
    · rcases hB3 with ⟨hi, _hL, _hS, hR⟩
      have hi' : i = cup2BoundaryIdxN2 n hn9 := by
        apply Fin.ext
        simp [cup2BoundaryIdxN2]
        omega
      have hR' : (d (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
        calc
          (d (cup2BoundaryIdxN1 n hn9)).1 = (d (right i)).1 := by
            rw [hi', right_cup2BoundaryIdxN2 n hn9]
          _ = 1 := hR
      rw [hdN1] at hR'
      omega
    · rcases hB4 with ⟨hi, _hL, _hS, hR⟩
      have hi' : i = cup2BoundaryIdxN1 n hn9 := by
        apply Fin.ext
        simp [cup2BoundaryIdxN1]
        omega
      have hR' : (d (cup2BoundaryIdx0 n hn9)).1 = 0 := by
        calc
          (d (cup2BoundaryIdx0 n hn9)).1 = (d (right i)).1 := by
            rw [hi', right_cup2BoundaryIdxN1 n hn9]
          _ = 0 := hR
      rw [hd0] at hR'
      omega
    · rcases hB5 with ⟨hi2, htop, hL, hS, hR⟩
      by_cases hi_eq : i = cup2BoundaryIdx2 n hn9
      · subst hi_eq
        have hleft_one : (d (left (cup2BoundaryIdx2 n hn9))).1 = 1 := by
          have hleft :
              (d (left (cup2BoundaryIdx2 n hn9))).1 =
                (d (cup2BoundaryIdx1 n hn9)).1 := by
            simpa using congrArg (fun j => (d j).1) (left_cup2BoundaryIdx2 n hn9)
          rw [hleft]
          exact hd1
        rw [hL] at hleft_one
        omega
      · have h3 : 3 ≤ i.1 := by
          have hi_ne_two : i.1 ≠ 2 := by
            intro hi_two
            apply hi_eq
            apply Fin.ext
            simpa [cup2BoundaryIdx2] using hi_two
          omega
        have htpMove : cup2TpPreservingMove n hn4 d i := by
          simpa [cup2TpPreservingMove, hmove, d] using hstep.2
        exact False.elim <|
          (b5_deep_not_tpPreservingMove n hn4 (c := d) (i := i)
            ⟨hi2, htop, hL, hS, hR⟩ h3) htpMove
  · exact le_of_not_gt hlt

private theorem pn1_011_postmove_tp_pos_is_idx2_B5
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {d c e : Config (cup2Spec n hn4)}
    (hpost : d = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hstep : cup2TpBadStepFwd n hn4 d e)
    (hpos : cup2BadStepPos n hn4 e d) :
    e = move (cup2System n hn4) d (cup2BoundaryIdx2 n hn9) ∧
      IsB5Config n hn4 d (cup2BoundaryIdx2 n hn9) := by
  have hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    rw [hpost, move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
      cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
    have htop011 : TTopVal 0 1 1 = 0 := by native_decide
    simpa [hcN2, hcN1, hc0] using htop011
  have hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    rw [hpost]
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
      omega
    rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0
  rcases cup2BadStepPos_classified n hn4 hpos with ⟨i, hmove, hclass⟩
  rcases hclass with hB1 | hB2 | hB3 | hB4 | hB5
  · rcases hB1 with ⟨hi0, _hL, hS, _hR⟩
    have hi' : i = cup2BoundaryIdx0 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx0] using hi0
    have hS' : (d (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      calc
        (d (cup2BoundaryIdx0 n hn9)).1 = (d i).1 := by rw [hi']
        _ = 0 := hS
    rw [hd0] at hS'
    omega
  · rcases hB2 with ⟨hi0, hL, _hS, _hR⟩
    have hi' : i = cup2BoundaryIdx0 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx0] using hi0
    have hL' : (d (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      calc
        (d (cup2BoundaryIdxN1 n hn9)).1 = (d (left i)).1 := by
          rw [hi', left_cup2BoundaryIdx0 n hn9]
        _ = 1 := hL
    rw [hdN1] at hL'
    omega
  · rcases hB3 with ⟨hi, _hL, _hS, hR⟩
    have hi' : i = cup2BoundaryIdxN2 n hn9 := by
      apply Fin.ext
      simp [cup2BoundaryIdxN2]
      omega
    have hR' : (d (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      calc
        (d (cup2BoundaryIdxN1 n hn9)).1 = (d (right i)).1 := by
          rw [hi', right_cup2BoundaryIdxN2 n hn9]
        _ = 1 := hR
    rw [hdN1] at hR'
    omega
  · rcases hB4 with ⟨hi, _hL, _hS, hR⟩
    have hi' : i = cup2BoundaryIdxN1 n hn9 := by
      apply Fin.ext
      simp [cup2BoundaryIdxN1]
      omega
    have hR' : (d (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      calc
        (d (cup2BoundaryIdx0 n hn9)).1 = (d (right i)).1 := by
          rw [hi', right_cup2BoundaryIdxN1 n hn9]
        _ = 0 := hR
    rw [hd0] at hR'
    omega
  · rcases hB5 with ⟨hi2, htop, hL, hS, hR⟩
    by_cases hi_eq : i = cup2BoundaryIdx2 n hn9
    · subst hi_eq
      exact ⟨hmove, ⟨by omega, htop, hL, hS, hR⟩⟩
    · have h3 : 3 ≤ i.1 := by
        have hi_ne_two : i.1 ≠ 2 := by
          intro hi_two
          apply hi_eq
          apply Fin.ext
          simpa [cup2BoundaryIdx2] using hi_two
        omega
      have htpMove : cup2TpPreservingMove n hn4 d i := by
        simpa [cup2TpPreservingMove, hmove] using hstep.2
      exact False.elim <|
        (b5_deep_not_tpPreservingMove n hn4 (c := d) (i := i)
          ⟨hi2, htop, hL, hS, hR⟩ h3) htpMove

private theorem pn1_011_leftFrame_tp_pos_is_idx2_B5
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {d e : Config (cup2Spec n hn4)}
    (hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hstep : cup2TpBadStepFwd n hn4 d e)
    (hpos : cup2BadStepPos n hn4 e d) :
    e = move (cup2System n hn4) d (cup2BoundaryIdx2 n hn9) ∧
      IsB5Config n hn4 d (cup2BoundaryIdx2 n hn9) := by
  rcases cup2BadStepPos_classified n hn4 hpos with ⟨i, hmove, hclass⟩
  rcases hclass with hB1 | hB2 | hB3 | hB4 | hB5
  · rcases hB1 with ⟨hi0, _hL, hS, _hR⟩
    have hi' : i = cup2BoundaryIdx0 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx0] using hi0
    have hS' : (d (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      calc
        (d (cup2BoundaryIdx0 n hn9)).1 = (d i).1 := by rw [hi']
        _ = 0 := hS
    rw [hd0] at hS'
    omega
  · rcases hB2 with ⟨hi0, hL, _hS, _hR⟩
    have hi' : i = cup2BoundaryIdx0 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx0] using hi0
    have hL' : (d (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      calc
        (d (cup2BoundaryIdxN1 n hn9)).1 = (d (left i)).1 := by
          rw [hi', left_cup2BoundaryIdx0 n hn9]
        _ = 1 := hL
    rw [hdN1] at hL'
    omega
  · rcases hB3 with ⟨hi, _hL, _hS, hR⟩
    have hi' : i = cup2BoundaryIdxN2 n hn9 := by
      apply Fin.ext
      simp [cup2BoundaryIdxN2]
      omega
    have hR' : (d (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
      calc
        (d (cup2BoundaryIdxN1 n hn9)).1 = (d (right i)).1 := by
          rw [hi', right_cup2BoundaryIdxN2 n hn9]
        _ = 1 := hR
    rw [hdN1] at hR'
    omega
  · rcases hB4 with ⟨hi, _hL, _hS, hR⟩
    have hi' : i = cup2BoundaryIdxN1 n hn9 := by
      apply Fin.ext
      simp [cup2BoundaryIdxN1]
      omega
    have hR' : (d (cup2BoundaryIdx0 n hn9)).1 = 0 := by
      calc
        (d (cup2BoundaryIdx0 n hn9)).1 = (d (right i)).1 := by
          rw [hi', right_cup2BoundaryIdxN1 n hn9]
        _ = 0 := hR
    rw [hd0] at hR'
    omega
  · rcases hB5 with ⟨hi2, htop, hL, hS, hR⟩
    by_cases hi_eq : i = cup2BoundaryIdx2 n hn9
    · subst hi_eq
      exact ⟨hmove, ⟨by omega, htop, hL, hS, hR⟩⟩
    · have h3 : 3 ≤ i.1 := by
        have hi_ne_two : i.1 ≠ 2 := by
          intro hi_two
          apply hi_eq
          apply Fin.ext
          simpa [cup2BoundaryIdx2] using hi_two
        omega
      have htpMove : cup2TpPreservingMove n hn4 d i := by
        simpa [cup2TpPreservingMove, hmove] using hstep.2
      exact False.elim <|
        (b5_deep_not_tpPreservingMove n hn4 (c := d) (i := i)
          ⟨hi2, htop, hL, hS, hR⟩ h3) htpMove

/- private theorem pn1_011_postLeftFrame_tp_pos_is_idx2_B5
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {d e : Config (cup2Spec n hn4)}
    (hdN2 : (d (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hstep : cup2TpBadStepFwd n hn4 d e)
    (hpos : cup2BadStepPos n hn4 e d) :
    e = move (cup2System n hn4) d (cup2BoundaryIdx2 n hn9) ∧
      IsB5Config n hn4 d (cup2BoundaryIdx2 n hn9) := by
  let src : Config (cup2Spec n hn4) :=
    fun i =>
      by
        by_cases h : i = cup2BoundaryIdxN1 n hn9
        · subst h
          have hself : 2 = (cup2Spec n hn4).m (cup2BoundaryIdxN1 n hn9) := by
            have htop : (cup2BoundaryIdxN1 n hn9).1 + 1 = n := by
              simp [cup2BoundaryIdxN1]
            simpa [cup2Spec] using
              (cup2M_eq_two_of_endpoint (n := n) (i := cup2BoundaryIdxN1 n hn9) (Or.inr htop)).symm
          exact Fin.cast hself (⟨1, by decide⟩ : Fin 2)
        · exact d i
  have hsrcN2 : (src (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    dsimp [src]
    split_ifs with h
    · have hval := congrArg Fin.val h
      simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
      omega
    · exact hdN2
  have hsrcN1 : (src (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    dsimp [src]
    split_ifs with h
    · rfl
    · contradiction
  have hsrc0 : (src (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    dsimp [src]
    split_ifs with h
    · have hval := congrArg Fin.val h
      simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
      omega
    · exact hd0
  have hpost : d = move (cup2System n hn4) src (cup2BoundaryIdxN1 n hn9) := by
    apply funext
    intro i
    by_cases hi : i = cup2BoundaryIdxN1 n hn9
    · subst hi
      have hdv : (d (cup2BoundaryIdxN1 n hn9)).1 = 0 := hdN1
      have htop011 : TTopVal 0 1 1 = 0 := by native_decide
      apply Fin.eq_of_val_eq
      calc
        (d (cup2BoundaryIdxN1 n hn9)).1 = 0 := hdv
        _ = TTopVal 0 1 1 := by simpa using htop011.symm
        _ = cup2OutVal n (cup2BoundaryIdxN1 n hn9)
              (src (left (cup2BoundaryIdxN1 n hn9))).1
              (src (cup2BoundaryIdxN1 n hn9)).1
              (src (right (cup2BoundaryIdxN1 n hn9))).1 := by
          rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9,
            right_cup2BoundaryIdxN1 n hn9]
          simpa [hsrcN2, hsrcN1, hsrc0]
        _ = (move (cup2System n hn4) src (cup2BoundaryIdxN1 n hn9)
              (cup2BoundaryIdxN1 n hn9)).1 := by
          symm
          exact move_apply_self_val n hn4 src (cup2BoundaryIdxN1 n hn9)
    · rw [move_apply_ne n hn4 src (cup2BoundaryIdxN1 n hn9) i hi]
      simpa [src, hi]
  exact pn1_011_postmove_tp_pos_is_idx2_B5 (d := d) (c := src)
    n hn4 hn9 hpost hsrcN2 hsrcN1 hsrc0 hstep hpos

-/

/- private theorem pn1_011_postLeftFrame_tp_pos_is_idx2_B5'
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {d e : Config (cup2Spec n hn4)}
    (hdN2 : (d (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hdN1 : (d (cup2BoundaryIdxN1 n hn9)).1 = 0)
    (hd0 : (d (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hstep : cup2TpBadStepFwd n hn4 d e)
    (hpos : cup2BadStepPos n hn4 e d) :
    e = move (cup2System n hn4) d (cup2BoundaryIdx2 n hn9) ∧
      IsB5Config n hn4 d (cup2BoundaryIdx2 n hn9) := by
  let src : Config (cup2Spec n hn4) :=
    fun i =>
      if h : i = cup2BoundaryIdxN1 n hn9 then
        Fin.cast
          (by
            cases h
            simp [cup2Spec, cup2BoundaryIdxN1])
          (⟨1, by decide⟩ : Fin 2)
      else
        d i
  have hsrcN2 : (src (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    dsimp [src]
    split_ifs with h
    · have hval := congrArg Fin.val h
      simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
      omega
    · exact hdN2
  have hsrcN1 : (src (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
    dsimp [src]
    split_ifs with h
    · rfl
    · contradiction
  have hsrc0 : (src (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    dsimp [src]
    split_ifs with h
    · have hval := congrArg Fin.val h
      simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
      omega
    · exact hd0
  have hpost : d = move (cup2System n hn4) src (cup2BoundaryIdxN1 n hn9) := by
    apply funext
    intro i
    by_cases hi : i = cup2BoundaryIdxN1 n hn9
    · subst hi
      apply Fin.eq_of_val_eq
      rw [move_apply_self_val n hn4 src (cup2BoundaryIdxN1 n hn9),
        cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
      have htop011 : TTopVal 0 1 1 = 0 := by native_decide
      simpa [hsrcN2, hsrcN1, hsrc0, hdN1] using htop011
    · rw [move_apply_ne n hn4 src (cup2BoundaryIdxN1 n hn9) i hi]
      dsimp [src]
      split_ifs with h
      · exact False.elim (hi h)
      · rfl
  exact pn1_011_postmove_tp_pos_is_idx2_B5 (d := d) (c := src)
    n hn4 hn9 hpost hsrcN2 hsrcN1 hsrc0 hstep hpos

-/


private abbrev p2TpLocal (L S R : Nat) : Prop :=
  let out := TMidVal L S R
  (if out = 2 ∧ R ≠ 2 then 1 else 0) = (if S = 2 ∧ R ≠ 2 then 1 else 0) ∧
    (if out = 2 ∧ R = 1 then 1 else 0) = (if S = 2 ∧ R = 1 then 1 else 0)

private abbrev pn3TpLocal (L S R : Nat) : Prop :=
  let out := TMidVal L S R
  (if L = 2 ∧ out ≠ 2 then 1 else 0) = (if L = 2 ∧ S ≠ 2 then 1 else 0) ∧
    (if out = 2 ∧ R ≠ 2 then 1 else 0) = (if S = 2 ∧ R ≠ 2 then 1 else 0) ∧
    ((if L = 2 ∧ out = 1 then 1 else 0) + (if out = 2 ∧ R = 1 then 1 else 0) =
      (if L = 2 ∧ S = 1 then 1 else 0) + (if S = 2 ∧ R = 1 then 1 else 0))

private abbrev pn2TpLocal (L S R : Nat) : Prop :=
  let out := THighVal L S R
  (if L = 2 ∧ out ≠ 2 then 1 else 0) = (if L = 2 ∧ S ≠ 2 then 1 else 0) ∧
    (if L = 2 ∧ out = 1 then 1 else 0) = (if L = 2 ∧ S = 1 then 1 else 0)

private theorem non617LocalClass_P2_of_notedge_tp
    (s : SixBoundary) (c3 : Fin 3)
    (htp : p2TpLocal s.c1.1 s.c2.1 c3.1)
    (hchange : (boundarySuccP2 s c3).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccP2 s c3).encode s.encode) :
    non617LocalClass P2 s.c1.1 s.c2.1 c3.1 := by
  have hclosed :
      ∀ (s : SixBoundary) (c3 : Fin 3),
        p2TpLocal s.c1.1 s.c2.1 c3.1 →
        (boundarySuccP2 s c3).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccP2 s c3).encode s.encode →
          ((s.c1.1 = 0 ∧ s.c2.1 = 1 ∧ c3.1 = 0) ∨
            (s.c1.1 = 0 ∧ s.c2.1 = 1 ∧ c3.1 = 2) ∨
            (s.c1.1 = 2 ∧ s.c2.1 = 0 ∧ c3.1 = 2) ∨
            (s.c1.1 = 2 ∧ s.c2.1 = 1 ∧ c3.1 = 2)) := by
    native_decide
  simpa [non617LocalClass, P2] using hclosed s c3 htp hchange hnotedge

private theorem non617LocalClass_PN3_of_notedge_tp
    (s : SixBoundary) (cn4 : Fin 3)
    (htp : pn3TpLocal cn4.1 s.cN3.1 s.cN2.1)
    (hchange : (boundarySuccPN3 s cn4).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN3 s cn4).encode s.encode) :
    non617LocalClass Pn3 cn4.1 s.cN3.1 s.cN2.1 := by
  have hclosed :
      ∀ (s : SixBoundary) (cn4 : Fin 3),
        pn3TpLocal cn4.1 s.cN3.1 s.cN2.1 →
        (boundarySuccPN3 s cn4).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN3 s cn4).encode s.encode →
          ((cn4.1 = 0 ∧ s.cN3.1 = 1 ∧ s.cN2.1 = 0) ∨
            (cn4.1 = 0 ∧ s.cN3.1 = 1 ∧ s.cN2.1 = 2) ∨
            (cn4.1 = 1 ∧ s.cN3.1 = 0 ∧ s.cN2.1 = 1) ∨
            (cn4.1 = 1 ∧ s.cN3.1 = 0 ∧ s.cN2.1 = 2)) := by
    native_decide
  simpa [non617LocalClass, Pn3] using hclosed s cn4 htp hchange hnotedge

private theorem non617LocalClass_PN2_of_notedge_tp
    (s : SixBoundary)
    (htp : pn2TpLocal s.cN3.1 s.cN2.1 s.cN1.1)
    (hchange : (boundarySuccPN2 s).encode ≠ s.encode)
    (hnotedge : ¬ sixTupleEdge (boundarySuccPN2 s).encode s.encode) :
    non617LocalClass Pn2 s.cN3.1 s.cN2.1 s.cN1.1 := by
  have hclosed :
      ∀ s : SixBoundary,
        pn2TpLocal s.cN3.1 s.cN2.1 s.cN1.1 →
        (boundarySuccPN2 s).encode ≠ s.encode →
        ¬ sixTupleEdge (boundarySuccPN2 s).encode s.encode →
          ((s.cN3.1 = 0 ∧ s.cN2.1 = 1 ∧ s.cN1.1 = 0) ∨
            (s.cN3.1 = 0 ∧ s.cN2.1 = 2 ∧ s.cN1.1 = 0) ∨
            (s.cN3.1 = 0 ∧ s.cN2.1 = 2 ∧ s.cN1.1 = 1) ∨
            (s.cN3.1 = 1 ∧ s.cN2.1 = 2 ∧ s.cN1.1 = 0)) := by
    native_decide
  simpa [non617LocalClass, Pn2] using hclosed s htp hchange hnotedge

private theorem p2TpLocal_of_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx2 n hn9)) :
    p2TpLocal (c (cup2BoundaryIdx1 n hn9)).1 (c (cup2BoundaryIdx2 n hn9)).1
      (c (right (cup2BoundaryIdx2 n hn9))).1 := by
  obtain ⟨hexp2, hi21, _hweight⟩ :=
    cup2TpPreserving_local_eqs n hn4 c (cup2BoundaryIdx2 n hn9) htp
  have hout :
      cup2OutVal n (cup2BoundaryIdx2 n hn9)
        (c (left (cup2BoundaryIdx2 n hn9))).1
        (c (cup2BoundaryIdx2 n hn9)).1
        (c (right (cup2BoundaryIdx2 n hn9))).1 =
          TMidVal (c (cup2BoundaryIdx1 n hn9)).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1 := by
    rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9]
  have h4 : 4 < n := by
    omega
  rw [hout] at hexp2 hi21
  constructor
  · rw [localExp2After, localExp2Before] at hexp2
    simpa [p2TpLocal, cup2Exp2BitVal, hout, left_cup2BoundaryIdx2 n hn9,
      cup2BoundaryIdx2, h4, Nat.mod_eq_of_lt (show 1 < n by omega)] using hexp2
  · rw [localInt21After, localInt21Before] at hi21
    simpa [p2TpLocal, cup2Int21BitVal, hout, left_cup2BoundaryIdx2 n hn9,
      cup2BoundaryIdx2, h4, Nat.mod_eq_of_lt (show 1 < n by omega)] using hi21

private theorem pn2TpLocal_of_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN2 n hn9)) :
    pn2TpLocal (c (cup2BoundaryIdxN3 n hn9)).1
      (c (cup2BoundaryIdxN2 n hn9)).1
      (c (cup2BoundaryIdxN1 n hn9)).1 := by
  obtain ⟨hexp2, hi21, _hweight⟩ :=
    cup2TpPreserving_local_eqs n hn4 c (cup2BoundaryIdxN2 n hn9) htp
  have hout :
      cup2OutVal n (cup2BoundaryIdxN2 n hn9)
        (c (left (cup2BoundaryIdxN2 n hn9))).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 =
          THighVal (c (cup2BoundaryIdxN3 n hn9)).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (cup2BoundaryIdxN1 n hn9)).1 := by
    rw [cup2OutVal_boundaryIdxN2 n hn9, left_cup2BoundaryIdxN2 n hn9,
      right_cup2BoundaryIdxN2 n hn9]
  have hzero_before_exp2 :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Exp2BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_after_exp2 :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Exp2BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_before_i21 :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Int21BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_before_exp2' :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_before_exp2
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hzero_after_exp2' :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_after_exp2
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hzero_before_i21' :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_before_i21
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hzero_after_i21 :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Int21BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_after_i21' :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_after_i21
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hinner_lo : 2 ≤ (cup2BoundaryIdxN3 n hn9).1 := by
    simp [cup2BoundaryIdxN3]
    omega
  have hinner_hi : (cup2BoundaryIdxN3 n hn9).1 + 2 < n := by
    simp [cup2BoundaryIdxN3]
    omega
  rw [localExp2After, localExp2Before] at hexp2
  rw [hout] at hexp2
  rw [left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9] at hexp2
  rw [hzero_after_exp2', hzero_before_exp2'] at hexp2
  rw [cup2Exp2BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi,
    cup2Exp2BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi] at hexp2
  rw [localInt21After, localInt21Before] at hi21
  rw [hout] at hi21
  rw [left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9] at hi21
  rw [hzero_after_i21', hzero_before_i21'] at hi21
  rw [cup2Int21BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi,
    cup2Int21BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi] at hi21
  simpa [pn2TpLocal] using And.intro hexp2 hi21

private theorem eq_bits_of_sum_and_weight_local
    {w a b c d : Nat}
    (hsum : a + b = c + d)
    (hweight : w * a + (w + 1) * b = w * c + (w + 1) * d) :
    a = c ∧ b = d := by
  have hbd : b = d := by
    nlinarith [hsum, hweight]
  have hac : a = c := by
    nlinarith [hsum, hbd]
  exact ⟨hac, hbd⟩

private theorem pn3TpLocal_of_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN3 n hn9)) :
    pn3TpLocal (c (left (cup2BoundaryIdxN3 n hn9))).1
      (c (cup2BoundaryIdxN3 n hn9)).1
      (c (cup2BoundaryIdxN2 n hn9)).1 := by
  let i := cup2BoundaryIdxN3 n hn9
  have hi_eq : i.1 = n - 3 := by
    change (cup2BoundaryIdxN3 n hn9).1 = n - 3
    simp [cup2BoundaryIdxN3]
  have h0 : i.1 ≠ 0 := by
    rw [hi_eq]
    omega
  have hleft_val : (left i).1 = n - 4 := by
    rw [left_val_of_ne_zero h0, hi_eq]
    omega
  have hi_succ : i.1 = (left i).1 + 1 := by
    rw [hleft_val]
    omega
  have hleft_in : 2 ≤ (left i).1 := by
    rw [hleft_val]
    omega
  have hleft_top : (left i).1 + 2 < n := by
    rw [hleft_val]
    omega
  have hi_in : 2 ≤ i.1 := by
    rw [hi_eq]
    omega
  have hi_top : i.1 + 2 < n := by
    rw [hi_eq]
    omega
  obtain ⟨hexp2, hi21, hweight⟩ := cup2TpPreserving_local_eqs n hn4 c i htp
  have hout :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 =
        TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 := by
    rw [cup2OutVal_boundaryIdxN3 n hn9, right_cup2BoundaryIdxN3 n hn9]
  have hexp2' :
      (if (c (left i)).1 = 2 ∧
            TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) +
        (if TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
            (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) =
      (if (c (left i)).1 = 2 ∧ (c i).1 ≠ 2 then 1 else 0) +
        (if (c i).1 = 2 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) := by
    rw [localExp2After, localExp2Before] at hexp2
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hexp2
    rw [cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ hi_in hi_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ hi_in hi_top] at hexp2
    exact hexp2
  have hweight' :
      (left i).1 *
          (if (c (left i)).1 = 2 ∧
                TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) +
        ((left i).1 + 1) *
          (if TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
              (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) =
      (left i).1 *
          (if (c (left i)).1 = 2 ∧ (c i).1 ≠ 2 then 1 else 0) +
        ((left i).1 + 1) *
          (if (c i).1 = 2 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) := by
    rw [localExp2WeightAfter, localExp2WeightBefore] at hweight
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hweight
    rw [cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ hi_in hi_top,
      cup2Exp2BitVal_eq_inner n i.1 _ _ hi_in hi_top] at hweight
    have htmp := hweight
    rw [hi_succ] at htmp
    exact htmp
  have hbits := eq_bits_of_sum_and_weight_local hexp2' hweight'
  have hi21' :
      (if (c (left i)).1 = 2 ∧
            TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) +
        (if TMidVal (c (left i)).1 (c i).1 (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
            (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) =
      (if (c (left i)).1 = 2 ∧ (c i).1 = 1 then 1 else 0) +
        (if (c i).1 = 2 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) := by
    rw [localInt21After, localInt21Before] at hi21
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hi21
    rw [cup2Int21BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n (left i).1 _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n i.1 _ _ hi_in hi_top,
      cup2Int21BitVal_eq_inner n i.1 _ _ hi_in hi_top] at hi21
    exact hi21
  simpa [pn3TpLocal] using And.intro hbits.1 (And.intro hbits.2 hi21')

private theorem p2TpLocal_c1_one_or_two_c2_two_implies_out_two
    (c1 c3 : Fin 3)
    (hc1 : c1.1 = 1 ∨ c1.1 = 2)
    (htp : p2TpLocal c1.1 2 c3.1) :
    TMidVal c1.1 2 c3.1 = 2 := by
  have h :
      ∀ (c1 c3 : Fin 3),
        (c1.1 = 1 ∨ c1.1 = 2) →
        p2TpLocal c1.1 2 c3.1 →
        TMidVal c1.1 2 c3.1 = 2 := by
    native_decide
  exact h c1 c3 hc1 htp

private theorem pn3TpLocal_cN3_two_cN2_zero_implies_out_two
    (cN4 : Fin 3)
    (htp : pn3TpLocal cN4.1 2 0) :
    TMidVal cN4.1 2 0 = 2 := by
  have h :
      ∀ cN4 : Fin 3,
        pn3TpLocal cN4.1 2 0 →
        TMidVal cN4.1 2 0 = 2 := by
    native_decide
  exact h cN4 htp

private theorem lookup_bot_012 : TBotVal 0 1 2 = 1 := by
  native_decide

private theorem pn2TpLocal_cN3_two_cN2_zero_cN1_zero_implies_out_zero
    (htp : pn2TpLocal 2 0 0) :
    THighVal 2 0 0 = 0 := by
  have h : pn2TpLocal 2 0 0 → THighVal 2 0 0 = 0 := by
    native_decide
  exact h htp

private theorem fc_noninc_of_boundary_fixed_tpStep
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hstep : cup2TpBadStepFwd n hn4 c c')
    (hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c) :
    cup2Fc n hn4 c' ≤ cup2Fc n hn4 c := by
  rcases hstep.1.2.2 with ⟨i, hpriv, hmove⟩
  subst c'
  have htpMove : cup2TpPreservingMove n hn4 c i := by
    simpa [cup2TpPreservingMove] using hstep.2
  have hdecode := congrArg (fun s : SixState => decodeSixBoundary s.1) hfixed
  have hfixed6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c i) =
        cup2Boundary6 n hn4 hn9 c := by
    simpa [cup2BoundaryState, decodeSixBoundary_encode] using hdecode
  have hnotboundary : ¬ (i.1 ≤ 2 ∨ n - 3 ≤ i.1) := by
    intro hboundary
    exact (cup2Boundary6_changed_of_boundary_move n hn4 hn9 c i hpriv hboundary) hfixed6
  have h3 : 3 ≤ i.1 := by omega
  have htop : i.1 + 2 < n := by omega
  have hcopy :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = (c (left i)).1 ∨
        cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = (c (right i)).1 := by
    exact cup2TpPreserving_mid_copyNeighbor_val n hn4 c i h3 htop htpMove hpriv
  rw [cup2Fc_move_split n hn4 c i, cup2Fc_split n hn4 c i, cup2Fc_rest_move_eq n hn4 c i]
  have hlocal :=
    localFcAfter_le_of_copyNeighbor
      (c (left i)).1 (c i).1 (c (right i)).1
      (cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1) hcopy
  omega

private theorem pn1_011_c1_one_boundary_dstA_values
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hA : cup2Boundary6 n hn4 hn9 c = pn1_011_c1_one_dstA) :
    (c (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
      (c (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      (c (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
      (c (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdx1 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdx2 n hn9)).1 = 2 := by
  have hN3 :
      (cup2Boundary6 n hn4 hn9 c).cN3 = (⟨2, by decide⟩ : Fin 3) := by
    simpa [pn1_011_c1_one_dstA, pn1_011_c1_one_srcBoundary, boundarySuccPN1] using
      congrArg SixBoundary.cN3 hA
  have hN2 :
      (cup2Boundary6 n hn4 hn9 c).cN2 = (⟨0, by decide⟩ : Fin 3) := by
    simpa [pn1_011_c1_one_dstA, pn1_011_c1_one_srcBoundary, boundarySuccPN1] using
      congrArg SixBoundary.cN2 hA
  have hN1 :
      (cup2Boundary6 n hn4 hn9 c).cN1 = (⟨0, by decide⟩ : Fin 2) := by
    simpa [pn1_011_c1_one_dstA, pn1_011_c1_one_srcBoundary, boundarySuccPN1] using
      congrArg SixBoundary.cN1 hA
  have h0 :
      (cup2Boundary6 n hn4 hn9 c).c0 = (⟨1, by decide⟩ : Fin 2) := by
    simpa [pn1_011_c1_one_dstA, pn1_011_c1_one_srcBoundary, boundarySuccPN1] using
      congrArg SixBoundary.c0 hA
  have h1 :
      (cup2Boundary6 n hn4 hn9 c).c1 = (⟨1, by decide⟩ : Fin 3) := by
    simpa [pn1_011_c1_one_dstA, pn1_011_c1_one_srcBoundary, boundarySuccPN1] using
      congrArg SixBoundary.c1 hA
  have h2 :
      (cup2Boundary6 n hn4 hn9 c).c2 = (⟨2, by decide⟩ : Fin 3) := by
    simpa [pn1_011_c1_one_dstA, pn1_011_c1_one_srcBoundary, boundarySuccPN1] using
      congrArg SixBoundary.c2 hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [cup2Boundary6] using congrArg Fin.val hN3
  · simpa [cup2Boundary6] using congrArg Fin.val hN2
  · simpa [cup2Boundary6] using congrArg Fin.val hN1
  · simpa [cup2Boundary6] using congrArg Fin.val h0
  · simpa [cup2Boundary6] using congrArg Fin.val h1
  · simpa [cup2Boundary6] using congrArg Fin.val h2

private theorem pn1_011_c1_one_boundary_dstB_values
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (hB : cup2Boundary6 n hn4 hn9 c = pn1_011_c1_one_dstB) :
    (c (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
      (c (cup2BoundaryIdxN2 n hn9)).1 = 0 ∧
      (c (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
      (c (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdx1 n hn9)).1 = 2 ∧
      (c (cup2BoundaryIdx2 n hn9)).1 = 2 := by
  have hN3 :
      (cup2Boundary6 n hn4 hn9 c).cN3 = (⟨2, by decide⟩ : Fin 3) := by
    simpa [pn1_011_c1_one_dstB, pn1_011_c1_one_dstA,
      pn1_011_c1_one_srcBoundary, boundarySuccPN1, boundarySuccP1] using
      congrArg SixBoundary.cN3 hB
  have hN2 :
      (cup2Boundary6 n hn4 hn9 c).cN2 = (⟨0, by decide⟩ : Fin 3) := by
    simpa [pn1_011_c1_one_dstB, pn1_011_c1_one_dstA,
      pn1_011_c1_one_srcBoundary, boundarySuccPN1, boundarySuccP1] using
      congrArg SixBoundary.cN2 hB
  have hN1 :
      (cup2Boundary6 n hn4 hn9 c).cN1 = (⟨0, by decide⟩ : Fin 2) := by
    simpa [pn1_011_c1_one_dstB, pn1_011_c1_one_dstA,
      pn1_011_c1_one_srcBoundary, boundarySuccPN1, boundarySuccP1] using
      congrArg SixBoundary.cN1 hB
  have h0 :
      (cup2Boundary6 n hn4 hn9 c).c0 = (⟨1, by decide⟩ : Fin 2) := by
    simpa [pn1_011_c1_one_dstB, pn1_011_c1_one_dstA,
      pn1_011_c1_one_srcBoundary, boundarySuccPN1, boundarySuccP1] using
      congrArg SixBoundary.c0 hB
  have h1 :
      (cup2Boundary6 n hn4 hn9 c).c1 = (⟨2, by decide⟩ : Fin 3) := by
    simpa [pn1_011_c1_one_dstB, pn1_011_c1_one_dstA,
      pn1_011_c1_one_srcBoundary, boundarySuccPN1, boundarySuccP1] using
      congrArg SixBoundary.c1 hB
  have h2 :
      (cup2Boundary6 n hn4 hn9 c).c2 = (⟨2, by decide⟩ : Fin 3) := by
    simpa [pn1_011_c1_one_dstB, pn1_011_c1_one_dstA,
      pn1_011_c1_one_srcBoundary, boundarySuccPN1, boundarySuccP1] using
      congrArg SixBoundary.c2 hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [cup2Boundary6] using congrArg Fin.val hN3
  · simpa [cup2Boundary6] using congrArg Fin.val hN2
  · simpa [cup2Boundary6] using congrArg Fin.val hN1
  · simpa [cup2Boundary6] using congrArg Fin.val h0
  · simpa [cup2Boundary6] using congrArg Fin.val h1
  · simpa [cup2Boundary6] using congrArg Fin.val h2

private theorem pn1_011_c1_one_postmove_step_noninc
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hshape :
      cup2Boundary6 n hn4 hn9 c = pn1_011_c1_one_dstA ∨
        cup2Boundary6 n hn4 hn9 c = pn1_011_c1_one_dstB)
    (hstep : cup2TpBadStepFwd n hn4 c c') :
    (cup2Boundary6 n hn4 hn9 c' = pn1_011_c1_one_dstA ∨
        cup2Boundary6 n hn4 hn9 c' = pn1_011_c1_one_dstB) ∧
      cup2Fc n hn4 c' ≤ cup2Fc n hn4 c := by
  by_cases hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c
  · have hdecode := congrArg (fun s : SixState => decodeSixBoundary s.1) hfixed
    have hb6 :
        cup2Boundary6 n hn4 hn9 c' = cup2Boundary6 n hn4 hn9 c := by
      simpa [cup2BoundaryState, decodeSixBoundary_encode] using hdecode
    constructor
    · rcases hshape with hA | hB
      · left
        exact hb6.trans hA
      · right
        exact hb6.trans hB
    · exact fc_noninc_of_boundary_fixed_tpStep n hn4 hn9 hstep hfixed
  · rcases hstep.1.2.2 with ⟨i, hpriv, hmove⟩
    subst c'
    have htpMove : cup2TpPreservingMove n hn4 c i := by
      simpa [cup2TpPreservingMove] using hstep.2
    have hbdry : i.1 ≤ 2 ∨ n - 3 ≤ i.1 :=
      cup2BoundaryState_changed_implies_boundary_index n hn4 hn9 c i hfixed
    rcases hshape with hA | hB
    · rcases pn1_011_c1_one_boundary_dstA_values n hn4 hn9 hA with
        ⟨hcN3, hcN2, hcN1, hc0, hc1, hc2⟩
      rcases hbdry with hsmall | hlarge
      · by_cases hi0 : i.1 = 0
        · have hi : i = cup2BoundaryIdx0 n hn9 := by
            apply Fin.ext
            simpa [cup2BoundaryIdx0] using hi0
          subst i
          have hout :
              cup2OutVal n (cup2BoundaryIdx0 n hn9)
                (c (left (cup2BoundaryIdx0 n hn9))).1
                (c (cup2BoundaryIdx0 n hn9)).1
                (c (right (cup2BoundaryIdx0 n hn9))).1 = 1 := by
            rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9,
              right_cup2BoundaryIdx0 n hn9]
            simpa [hcN1, hc0, hc1] using lookup_bot_011
          unfold privileged cup2System at hpriv
          rw [Fin.ne_iff_vne, cup2Trans_val, hout, hc0] at hpriv
          exact False.elim (hpriv rfl)
        · by_cases hi1 : i.1 = 1
          · have hi : i = cup2BoundaryIdx1 n hn9 := by
              apply Fin.ext
              simpa [cup2BoundaryIdx1] using hi1
            subst i
            constructor
            · right
              rw [cup2Boundary6_move_eq_boundarySuccP1 n hn4 hn9 c, hA]
              rfl
            · exact le_of_eq (pn1_011_c1_one_idx1_fc_eq n hn4 hn9 c hc0 hc1 hc2)
          · have hi2 : i.1 = 2 := by omega
            have hi : i = cup2BoundaryIdx2 n hn9 := by
              apply Fin.ext
              simpa [cup2BoundaryIdx2] using hi2
            subst i
            let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
            have htpLocal :
                p2TpLocal 1 2 c3.1 := by
              simpa [c3, stateAsFin3, hc1, hc2] using
                p2TpLocal_of_tpPreserving n hn4 hn9 c htpMove
            have hout :
                cup2OutVal n (cup2BoundaryIdx2 n hn9)
                  (c (left (cup2BoundaryIdx2 n hn9))).1
                  (c (cup2BoundaryIdx2 n hn9)).1
                  (c (right (cup2BoundaryIdx2 n hn9))).1 = 2 := by
              rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9]
              simpa [c3, stateAsFin3, hc1, hc2] using
                p2TpLocal_c1_one_or_two_c2_two_implies_out_two
                  (⟨1, by decide⟩ : Fin 3) c3 (Or.inl rfl) htpLocal
            unfold privileged cup2System at hpriv
            rw [Fin.ne_iff_vne, cup2Trans_val, hout, hc2] at hpriv
            exact False.elim (hpriv rfl)
      · by_cases hiN1 : i.1 + 1 = n
        · have hi : i = cup2BoundaryIdxN1 n hn9 := by
            have hi_val : i.1 = n - 1 := by omega
            apply Fin.ext
            simp [cup2BoundaryIdxN1, hi_val]
          subst i
          have hout :
              cup2OutVal n (cup2BoundaryIdxN1 n hn9)
                (c (left (cup2BoundaryIdxN1 n hn9))).1
                (c (cup2BoundaryIdxN1 n hn9)).1
                (c (right (cup2BoundaryIdxN1 n hn9))).1 = 0 := by
            rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9,
              right_cup2BoundaryIdxN1 n hn9]
            simpa [hcN2, hcN1, hc0] using lookup_top_001
          unfold privileged cup2System at hpriv
          rw [Fin.ne_iff_vne, cup2Trans_val, hout, hcN1] at hpriv
          exact False.elim (hpriv rfl)
        · by_cases hiN2 : i.1 + 2 = n
          · have hi : i = cup2BoundaryIdxN2 n hn9 := by
              have hi_val : i.1 = n - 2 := by omega
              apply Fin.ext
              simp [cup2BoundaryIdxN2, hi_val]
            subst i
            have htpLocal : pn2TpLocal 2 0 0 := by
              simpa [hcN3, hcN2, hcN1] using
                pn2TpLocal_of_tpPreserving n hn4 hn9 c htpMove
            have hout :
                cup2OutVal n (cup2BoundaryIdxN2 n hn9)
                  (c (left (cup2BoundaryIdxN2 n hn9))).1
                  (c (cup2BoundaryIdxN2 n hn9)).1
                  (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
              rw [cup2OutVal_boundaryIdxN2 n hn9, left_cup2BoundaryIdxN2 n hn9,
                right_cup2BoundaryIdxN2 n hn9]
              simpa [hcN3, hcN2, hcN1] using
                pn2TpLocal_cN3_two_cN2_zero_cN1_zero_implies_out_zero htpLocal
            unfold privileged cup2System at hpriv
            rw [Fin.ne_iff_vne, cup2Trans_val, hout, hcN2] at hpriv
            exact False.elim (hpriv rfl)
          · have hi_lt_n2 : i.1 < n - 2 := by
              by_contra hge
              have hge' : n - 2 ≤ i.1 := by omega
              have hi_le : i.1 ≤ n - 1 := Nat.le_pred_of_lt i.2
              have hi_eq : i.1 = n - 2 ∨ i.1 = n - 1 := by omega
              rcases hi_eq with hEq | hEq
              · apply hiN2
                omega
              · apply hiN1
                omega
            have hi_val : i.1 = n - 3 := by
              omega
            have hi : i = cup2BoundaryIdxN3 n hn9 := by
              apply Fin.ext
              simpa [cup2BoundaryIdxN3] using hi_val
            subst i
            let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
            have htpLocal : pn3TpLocal cn4.1 2 0 := by
              simpa [cn4, stateAsFin3, hcN3, hcN2] using
                pn3TpLocal_of_tpPreserving n hn4 hn9 c htpMove
            have hout :
                cup2OutVal n (cup2BoundaryIdxN3 n hn9)
                  (c (left (cup2BoundaryIdxN3 n hn9))).1
                  (c (cup2BoundaryIdxN3 n hn9)).1
                  (c (right (cup2BoundaryIdxN3 n hn9))).1 = 2 := by
              rw [cup2OutVal_boundaryIdxN3 n hn9, right_cup2BoundaryIdxN3 n hn9]
              simpa [cn4, stateAsFin3, hcN3, hcN2] using
                pn3TpLocal_cN3_two_cN2_zero_implies_out_two cn4 htpLocal
            unfold privileged cup2System at hpriv
            rw [Fin.ne_iff_vne, cup2Trans_val, hout, hcN3] at hpriv
            exact False.elim (hpriv rfl)
    · rcases pn1_011_c1_one_boundary_dstB_values n hn4 hn9 hB with
        ⟨hcN3, hcN2, hcN1, hc0, hc1, hc2⟩
      rcases hbdry with hsmall | hlarge
      · by_cases hi0 : i.1 = 0
        · have hi : i = cup2BoundaryIdx0 n hn9 := by
            apply Fin.ext
            simpa [cup2BoundaryIdx0] using hi0
          subst i
          have hout :
              cup2OutVal n (cup2BoundaryIdx0 n hn9)
                (c (left (cup2BoundaryIdx0 n hn9))).1
                (c (cup2BoundaryIdx0 n hn9)).1
                (c (right (cup2BoundaryIdx0 n hn9))).1 = 1 := by
            rw [cup2OutVal_boundaryIdx0 n hn9, left_cup2BoundaryIdx0 n hn9,
              right_cup2BoundaryIdx0 n hn9]
            simpa [hcN1, hc0, hc1] using lookup_bot_012
          unfold privileged cup2System at hpriv
          rw [Fin.ne_iff_vne, cup2Trans_val, hout, hc0] at hpriv
          exact False.elim (hpriv rfl)
        · by_cases hi1 : i.1 = 1
          · have hi : i = cup2BoundaryIdx1 n hn9 := by
              apply Fin.ext
              simpa [cup2BoundaryIdx1] using hi1
            subst i
            have hout :
                cup2OutVal n (cup2BoundaryIdx1 n hn9)
                  (c (left (cup2BoundaryIdx1 n hn9))).1
                  (c (cup2BoundaryIdx1 n hn9)).1
                  (c (right (cup2BoundaryIdx1 n hn9))).1 = 2 := by
              rw [cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9,
                right_cup2BoundaryIdx1 n hn9]
              simpa [hc0, hc1, hc2] using lookup_low_122
            unfold privileged cup2System at hpriv
            rw [Fin.ne_iff_vne, cup2Trans_val, hout, hc1] at hpriv
            exact False.elim (hpriv rfl)
          · have hi2 : i.1 = 2 := by omega
            have hi : i = cup2BoundaryIdx2 n hn9 := by
              apply Fin.ext
              simpa [cup2BoundaryIdx2] using hi2
            subst i
            let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
            have htpLocal :
                p2TpLocal 2 2 c3.1 := by
              simpa [c3, stateAsFin3, hc1, hc2] using
                p2TpLocal_of_tpPreserving n hn4 hn9 c htpMove
            have hout :
                cup2OutVal n (cup2BoundaryIdx2 n hn9)
                  (c (left (cup2BoundaryIdx2 n hn9))).1
                  (c (cup2BoundaryIdx2 n hn9)).1
                  (c (right (cup2BoundaryIdx2 n hn9))).1 = 2 := by
              rw [cup2OutVal_boundaryIdx2 n hn9, left_cup2BoundaryIdx2 n hn9]
              simpa [c3, stateAsFin3, hc1, hc2] using
                p2TpLocal_c1_one_or_two_c2_two_implies_out_two
                  (⟨2, by decide⟩ : Fin 3) c3 (Or.inr rfl) htpLocal
            unfold privileged cup2System at hpriv
            rw [Fin.ne_iff_vne, cup2Trans_val, hout, hc2] at hpriv
            exact False.elim (hpriv rfl)
      · by_cases hiN1 : i.1 + 1 = n
        · have hi : i = cup2BoundaryIdxN1 n hn9 := by
            have hi_val : i.1 = n - 1 := by omega
            apply Fin.ext
            simp [cup2BoundaryIdxN1, hi_val]
          subst i
          have hout :
              cup2OutVal n (cup2BoundaryIdxN1 n hn9)
                (c (left (cup2BoundaryIdxN1 n hn9))).1
                (c (cup2BoundaryIdxN1 n hn9)).1
                (c (right (cup2BoundaryIdxN1 n hn9))).1 = 0 := by
            rw [cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9,
              right_cup2BoundaryIdxN1 n hn9]
            simpa [hcN2, hcN1, hc0] using lookup_top_001
          unfold privileged cup2System at hpriv
          rw [Fin.ne_iff_vne, cup2Trans_val, hout, hcN1] at hpriv
          exact False.elim (hpriv rfl)
        · by_cases hiN2 : i.1 + 2 = n
          · have hi : i = cup2BoundaryIdxN2 n hn9 := by
              have hi_val : i.1 = n - 2 := by omega
              apply Fin.ext
              simp [cup2BoundaryIdxN2, hi_val]
            subst i
            have htpLocal : pn2TpLocal 2 0 0 := by
              simpa [hcN3, hcN2, hcN1] using
                pn2TpLocal_of_tpPreserving n hn4 hn9 c htpMove
            have hout :
                cup2OutVal n (cup2BoundaryIdxN2 n hn9)
                  (c (left (cup2BoundaryIdxN2 n hn9))).1
                  (c (cup2BoundaryIdxN2 n hn9)).1
                  (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
              rw [cup2OutVal_boundaryIdxN2 n hn9, left_cup2BoundaryIdxN2 n hn9,
                right_cup2BoundaryIdxN2 n hn9]
              simpa [hcN3, hcN2, hcN1] using
                pn2TpLocal_cN3_two_cN2_zero_cN1_zero_implies_out_zero htpLocal
            unfold privileged cup2System at hpriv
            rw [Fin.ne_iff_vne, cup2Trans_val, hout, hcN2] at hpriv
            exact False.elim (hpriv rfl)
          · have hi_lt_n2 : i.1 < n - 2 := by
              by_contra hge
              have hge' : n - 2 ≤ i.1 := by omega
              have hi_le : i.1 ≤ n - 1 := Nat.le_pred_of_lt i.2
              have hi_eq : i.1 = n - 2 ∨ i.1 = n - 1 := by omega
              rcases hi_eq with hEq | hEq
              · apply hiN2
                omega
              · apply hiN1
                omega
            have hi_val : i.1 = n - 3 := by
              omega
            have hi : i = cup2BoundaryIdxN3 n hn9 := by
              apply Fin.ext
              simpa [cup2BoundaryIdxN3] using hi_val
            subst i
            let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
            have htpLocal : pn3TpLocal cn4.1 2 0 := by
              simpa [cn4, stateAsFin3, hcN3, hcN2] using
                pn3TpLocal_of_tpPreserving n hn4 hn9 c htpMove
            have hout :
                cup2OutVal n (cup2BoundaryIdxN3 n hn9)
                  (c (left (cup2BoundaryIdxN3 n hn9))).1
                  (c (cup2BoundaryIdxN3 n hn9)).1
                  (c (right (cup2BoundaryIdxN3 n hn9))).1 = 2 := by
              rw [cup2OutVal_boundaryIdxN3 n hn9, right_cup2BoundaryIdxN3 n hn9]
              simpa [cn4, stateAsFin3, hcN3, hcN2] using
                pn3TpLocal_cN3_two_cN2_zero_implies_out_two cn4 htpLocal
            unfold privileged cup2System at hpriv
            rw [Fin.ne_iff_vne, cup2Trans_val, hout, hcN3] at hpriv
            exact False.elim (hpriv rfl)

private theorem pn1_011_c1_one_tpReachable_fc_le
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2)
    (hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0)
    (hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2)
    {d : Config (cup2Spec n hn4)}
    (hreach : cup2TpReachable n hn4
      (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) d) :
    cup2Fc n hn4 d ≤
      cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) := by
  let c' := move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)
  have hshape0 :
      cup2Boundary6 n hn4 hn9 c' = pn1_011_c1_one_dstA := by
    simpa [c'] using
      pn1_011_c1_one_post_boundary n hn4 hn9 c hcN3 hcN2 hcN1 hc0 hc1 hc2
  have hstrong :
      ∀ {x : Config (cup2Spec n hn4)},
        cup2TpReachable n hn4 c' x →
          (cup2Boundary6 n hn4 hn9 x = pn1_011_c1_one_dstA ∨
              cup2Boundary6 n hn4 hn9 x = pn1_011_c1_one_dstB) ∧
            cup2Fc n hn4 x ≤ cup2Fc n hn4 c' := by
    intro x hreach'
    induction hreach' with
    | refl =>
      exact ⟨Or.inl hshape0, le_rfl⟩
    | tail _ hstep ih =>
      rcases pn1_011_c1_one_postmove_step_noninc n hn4 hn9 ih.1 hstep with
        ⟨hshape', hfc_le⟩
      exact ⟨hshape', le_trans hfc_le ih.2⟩
  exact (hstrong hreach).2



private theorem eq_bits_of_sum_and_weight
    {w a b c d : Nat}
    (hsum : a + b = c + d)
    (hweight : w * a + (w + 1) * b = w * c + (w + 1) * d) :
    a = c ∧ b = d := by
  have hbd : b = d := by
    nlinarith [hsum, hweight]
  have hac : a = c := by
    nlinarith [hsum, hbd]
  exact ⟨hac, hbd⟩

/- private theorem pn3TpLocal_of_tpPreserving
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4))
    (htp : cup2TpPreservingMove n hn4 c (cup2BoundaryIdxN3 n hn9)) :
    pn3TpLocal (c (left (cup2BoundaryIdxN3 n hn9))).1
      (c (cup2BoundaryIdxN3 n hn9)).1
      (c (cup2BoundaryIdxN2 n hn9)).1 := by
  obtain ⟨hexp2, hi21, hweight⟩ :=
    cup2TpPreserving_local_eqs n hn4 c (cup2BoundaryIdxN3 n hn9) htp
  have hout :
      cup2OutVal n (cup2BoundaryIdxN3 n hn9)
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (right (cup2BoundaryIdxN3 n hn9))).1 =
          TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (cup2BoundaryIdxN2 n hn9)).1 := by
    rw [cup2OutVal_boundaryIdxN3 n hn9, right_cup2BoundaryIdxN3 n hn9]
  have hleft_ne0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
    simp [cup2BoundaryIdxN3]
    omega
  have hleft_val : (left (cup2BoundaryIdxN3 n hn9)).1 = n - 4 := by
    rw [left_val_of_ne_zero hleft_ne0, cup2BoundaryIdxN3]
    omega
  have hi_val : (cup2BoundaryIdxN3 n hn9).1 = n - 3 := by
    simp [cup2BoundaryIdxN3]
  have hleft_in : 2 ≤ n - 4 := by
    omega
  have hleft_top : n - 4 + 2 < n := by
    omega
  have hi_in : 2 ≤ n - 3 := by
    omega
  have hi_top : n - 3 + 2 < n := by
    omega
  have hexp2' :
      (if (c (left (cup2BoundaryIdxN3 n hn9))).1 = 2 ∧
            TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) +
        (if TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
            (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) =
      (if (c (left (cup2BoundaryIdxN3 n hn9))).1 = 2 ∧
            (c (cup2BoundaryIdxN3 n hn9)).1 ≠ 2 then 1 else 0) +
        (if (c (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
            (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) := by
    rw [localExp2After, localExp2Before] at hexp2
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hexp2
    rw [hleft_val, hi_val] at hexp2
    rw [cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (n - 3) _ _ hi_in hi_top,
      cup2Exp2BitVal_eq_inner n (n - 3) _ _ hi_in hi_top] at hexp2
    exact hexp2
  have hweight' :
      (n - 4) *
          (if (c (left (cup2BoundaryIdxN3 n hn9))).1 = 2 ∧
                TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
                  (c (cup2BoundaryIdxN3 n hn9)).1
                  (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) +
        (n - 3) *
          (if TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
                (c (cup2BoundaryIdxN3 n hn9)).1
                (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
              (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) =
      (n - 4) *
          (if (c (left (cup2BoundaryIdxN3 n hn9))).1 = 2 ∧
                (c (cup2BoundaryIdxN3 n hn9)).1 ≠ 2 then 1 else 0) +
        (n - 3) *
          (if (c (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
              (c (cup2BoundaryIdxN2 n hn9)).1 ≠ 2 then 1 else 0) := by
    rw [localExp2WeightAfter, localExp2WeightBefore] at hweight
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hweight
    rw [hleft_val, hi_val] at hweight
    rw [cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (n - 3) _ _ hi_in hi_top,
      cup2Exp2BitVal_eq_inner n (n - 3) _ _ hi_in hi_top] at hweight
    exact hweight
  have hbits := eq_bits_of_sum_and_weight hexp2' hweight'
  have hi21' :
      (if (c (left (cup2BoundaryIdxN3 n hn9))).1 = 2 ∧
            TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) +
        (if TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
              (c (cup2BoundaryIdxN3 n hn9)).1
              (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
            (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) =
      (if (c (left (cup2BoundaryIdxN3 n hn9))).1 = 2 ∧
            (c (cup2BoundaryIdxN3 n hn9)).1 = 1 then 1 else 0) +
        (if (c (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
            (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) := by
    rw [localInt21After, localInt21Before] at hi21
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hi21
    rw [hleft_val, hi_val] at hi21
    rw [cup2Int21BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n (n - 3) _ _ hi_in hi_top,
      cup2Int21BitVal_eq_inner n (n - 3) _ _ hi_in hi_top] at hi21
    exact hi21
  simpa [pn3TpLocal] using And.intro hbits.1 (And.intro hbits.2 hi21') -/

private theorem cphi_tpPreservingMove_of_move
    (n : Nat) (hn4 : 4 ≤ n)
    {c' c : Config (cup2Spec n hn4)} {i : Fin n}
    (h : cup2CPhiStep n hn4 c' c)
    (hmove : c' = move (cup2System n hn4) c i) :
    cup2TpPreservingMove n hn4 c i := by
  simpa [cup2TpPreservingMove, hmove] using h.2.1

private theorem cphi_boundary_non617_idx0_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    let s := cup2Boundary6 n hn4 hn9 c
    non617LocalClass P0 s.cN1.1 s.c0.1 s.c1.1 := by
  let s := cup2Boundary6 n hn4 hn9 c
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
        boundarySuccP0 s := by
    simpa [s] using cup2Boundary6_move_eq_boundarySuccP0 n hn4 hn9 c
  have hchange' : (boundarySuccP0 s).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccP0 s).encode s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hnotedge
  simpa [s] using non617LocalClass_P0_of_notedge s hchange' hnotedge'

private theorem cphi_boundary_non617_idx1_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    let s := cup2Boundary6 n hn4 hn9 c
    non617LocalClass P1 s.c0.1 s.c1.1 s.c2.1 := by
  let s := cup2Boundary6 n hn4 hn9 c
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        boundarySuccP1 s := by
    simpa [s] using cup2Boundary6_move_eq_boundarySuccP1 n hn4 hn9 c
  have hchange' : (boundarySuccP1 s).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccP1 s).encode s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hnotedge
  simpa [s] using non617LocalClass_P1_of_notedge s hchange' hnotedge'

private theorem cphi_boundary_non617_idx2_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    let s := cup2Boundary6 n hn4 hn9 c
    let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
    non617LocalClass P2 s.c1.1 s.c2.1 c3.1 := by
  let s := cup2Boundary6 n hn4 hn9 c
  let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9)) =
        boundarySuccP2 s c3 := by
    simpa [s, c3] using cup2Boundary6_move_eq_boundarySuccP2 n hn4 hn9 c
  have htp : p2TpLocal s.c1.1 s.c2.1 c3.1 := by
    simpa [s, c3] using
      p2TpLocal_of_tpPreserving n hn4 hn9 c (cphi_tpPreservingMove_of_move n hn4 h hmove)
  have hchange' : (boundarySuccP2 s c3).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, c3, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccP2 s c3).encode s.encode := by
    simpa [cup2BoundaryState, s, c3, hmove, hb6] using hnotedge
  simpa [s, c3] using non617LocalClass_P2_of_notedge_tp s c3 htp hchange' hnotedge'

private theorem cphi_boundary_non617_idxN1_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    let s := cup2Boundary6 n hn4 hn9 c
    non617LocalClass Pn1 s.cN2.1 s.cN1.1 s.c0.1 := by
  let s := cup2Boundary6 n hn4 hn9 c
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
        boundarySuccPN1 s := by
    simpa [s] using cup2Boundary6_move_eq_boundarySuccPN1 n hn4 hn9 c
  have hchange' : (boundarySuccPN1 s).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hnotedge
  simpa [s] using non617LocalClass_PN1_of_notedge s hchange' hnotedge'

private theorem cphi_boundary_non617_idxN2_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    let s := cup2Boundary6 n hn4 hn9 c
    non617LocalClass Pn2 s.cN3.1 s.cN2.1 s.cN1.1 := by
  let s := cup2Boundary6 n hn4 hn9 c
  have htpMove := cphi_tpPreservingMove_of_move n hn4 h hmove
  obtain ⟨hexp2, hi21, _hweight⟩ :=
    cup2TpPreserving_local_eqs n hn4 c (cup2BoundaryIdxN2 n hn9) htpMove
  have hout :
      cup2OutVal n (cup2BoundaryIdxN2 n hn9)
        (c (left (cup2BoundaryIdxN2 n hn9))).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 =
          THighVal (c (cup2BoundaryIdxN3 n hn9)).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (cup2BoundaryIdxN1 n hn9)).1 := by
    rw [cup2OutVal_boundaryIdxN2 n hn9, left_cup2BoundaryIdxN2 n hn9,
      right_cup2BoundaryIdxN2 n hn9]
  have hzero_before_exp2 :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Exp2BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_after_exp2 :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Exp2BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_before_i21 :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Int21BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_before_exp2' :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_before_exp2
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hzero_after_exp2' :
      cup2Exp2BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_after_exp2
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hzero_before_i21' :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_before_i21
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hzero_after_i21 :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (right (cup2BoundaryIdxN2 n hn9))).1 = 0 := by
    apply cup2Int21BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN2]
    omega
  have hzero_after_i21' :
      cup2Int21BitVal n (cup2BoundaryIdxN2 n hn9).1
        (THighVal (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (cup2BoundaryIdxN1 n hn9)).1)
        (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    have htmp := hzero_after_i21
    rw [right_cup2BoundaryIdxN2 n hn9] at htmp
    exact htmp
  have hinner_lo : 2 ≤ (cup2BoundaryIdxN3 n hn9).1 := by
    simp [cup2BoundaryIdxN3]
    omega
  have hinner_hi : (cup2BoundaryIdxN3 n hn9).1 + 2 < n := by
    simp [cup2BoundaryIdxN3]
    omega
  rw [localExp2After, localExp2Before] at hexp2
  rw [hout] at hexp2
  rw [left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9] at hexp2
  rw [hzero_after_exp2', hzero_before_exp2'] at hexp2
  rw [cup2Exp2BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi,
    cup2Exp2BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi] at hexp2
  rw [localInt21After, localInt21Before] at hi21
  rw [hout] at hi21
  rw [left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9] at hi21
  rw [hzero_after_i21', hzero_before_i21'] at hi21
  rw [cup2Int21BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi,
    cup2Int21BitVal_eq_inner n (cup2BoundaryIdxN3 n hn9).1 _ _ hinner_lo hinner_hi] at hi21
  have htpLocal : pn2TpLocal s.cN3.1 s.cN2.1 s.cN1.1 := by
    simpa [pn2TpLocal, s, cup2Boundary6] using And.intro hexp2 hi21
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9)) =
        boundarySuccPN2 s := by
    simpa [s] using cup2Boundary6_move_eq_boundarySuccPN2 n hn4 hn9 c
  have hchange' : (boundarySuccPN2 s).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccPN2 s).encode s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hnotedge
  simpa [s] using non617LocalClass_PN2_of_notedge_tp s htpLocal hchange' hnotedge'

/- private theorem cphi_boundary_non617_idxN3_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    let s := cup2Boundary6 n hn4 hn9 c
    let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
    non617LocalClass Pn3 cn4.1 s.cN3.1 s.cN2.1 := by
  let s := cup2Boundary6 n hn4 hn9 c
  let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
  have htpLocal : pn3TpLocal cn4.1 s.cN3.1 s.cN2.1 := by
    simpa [s, cn4, cup2Boundary6, stateAsFin3] using
      pn3TpLocal_of_tpPreserving n hn4 hn9 c (cphi_tpPreservingMove_of_move n hn4 h hmove)
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
        boundarySuccPN3 s cn4 := by
    simpa [s, cn4] using cup2Boundary6_move_eq_boundarySuccPN3 n hn4 hn9 c
  have hchange' : (boundarySuccPN3 s cn4).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, cn4, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccPN3 s cn4).encode s.encode := by
    simpa [cup2BoundaryState, s, cn4, hmove, hb6] using hnotedge
  simpa [s, cn4] using non617LocalClass_PN3_of_notedge_tp s cn4 htpLocal hchange' hnotedge' -/

/- private theorem cphi_boundary_non617_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass P0 s.cN1.1 s.c0.1 s.c1.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass P1 s.c0.1 s.c1.1 s.c2.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
       non617LocalClass P2 s.c1.1 s.c2.1 c3.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
       non617LocalClass Pn3 cn4.1 s.cN3.1 s.cN2.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass Pn2 s.cN3.1 s.cN2.1 s.cN1.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass Pn1 s.cN2.1 s.cN1.1 s.c0.1)) := by
  rcases cphi_boundary_non617_stateClass_or_hard n hn4 hn9 h hchange hnotedge with
    h0 | h1 | h2 | hN3 | hN2 | hN1
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h2))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hN3, cphi_boundary_non617_idxN3_stateClass n hn4 hn9 h hN3 hchange hnotedge⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hN2))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hN1)))) -/

/- private theorem cphi_boundary_non617_idxN3_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    let s := cup2Boundary6 n hn4 hn9 c
    let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
    non617LocalClass Pn3 cn4.1 s.cN3.1 s.cN2.1 := by
  let s := cup2Boundary6 n hn4 hn9 c
  let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
  have htpMove := cphi_tpPreservingMove_of_move n hn4 h hmove
  obtain ⟨hexp2, hi21, _hweight⟩ :=
    cup2TpPreserving_local_eqs n hn4 c (cup2BoundaryIdxN3 n hn9) htpMove
  have hout :
      cup2OutVal n (cup2BoundaryIdxN3 n hn9)
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (right (cup2BoundaryIdxN3 n hn9))).1 =
          TMidVal cn4.1 (c (cup2BoundaryIdxN3 n hn9)).1 (c (cup2BoundaryIdxN2 n hn9)).1 := by
    rw [cup2OutVal_boundaryIdxN3 n hn9, right_cup2BoundaryIdxN3 n hn9]
    simp [cn4, stateAsFin3]
  have hright_zero_exp2_before :
      cup2Exp2BitVal n (cup2BoundaryIdxN3 n hn9).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    apply cup2Exp2BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN3]
    omega
  have hright_zero_exp2_after :
      cup2Exp2BitVal n (cup2BoundaryIdxN3 n hn9).1
        (TMidVal cn4.1 (c (cup2BoundaryIdxN3 n hn9)).1 (c (cup2BoundaryIdxN2 n hn9)).1)
        (c (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    apply cup2Exp2BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN3]
    omega
  have hright_zero_i21_before :
      cup2Int21BitVal n (cup2BoundaryIdxN3 n hn9).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    apply cup2Int21BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN3]
    omega
  have hright_zero_i21_after :
      cup2Int21BitVal n (cup2BoundaryIdxN3 n hn9).1
        (TMidVal cn4.1 (c (cup2BoundaryIdxN3 n hn9)).1 (c (cup2BoundaryIdxN2 n hn9)).1)
        (c (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
    apply cup2Int21BitVal_eq_zero_of_ge_top
    simp [cup2BoundaryIdxN3]
    omega
  have hleft_val : (left (cup2BoundaryIdxN3 n hn9)).1 = n - 4 := by
    rw [left_val_of_ne_zero (by simp [cup2BoundaryIdxN3]; omega), cup2BoundaryIdxN3]
    omega
  have hleft_in : 2 ≤ n - 4 := by
    omega
  have hleft_top : n - 4 + 2 < n := by
    omega
  rw [localExp2After, localExp2Before] at hexp2
  rw [hout, right_cup2BoundaryIdxN3 n hn9] at hexp2
  rw [hright_zero_exp2_after, hright_zero_exp2_before] at hexp2
  rw [left_cup2BoundaryIdxN3, cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
    cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top] at hexp2
  have hi21left :
      (if cn4.1 = 2 ∧ TMidVal cn4.1 (c (cup2BoundaryIdxN3 n hn9)).1
            (c (cup2BoundaryIdxN2 n hn9)).1 = 1 then 1 else 0) =
        (if cn4.1 = 2 ∧ (c (cup2BoundaryIdxN3 n hn9)).1 = 1 then 1 else 0) := by
    rw [localInt21After, localInt21Before] at hi21
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hi21
    rw [hright_zero_i21_after, hright_zero_i21_before] at hi21
    rw [left_cup2BoundaryIdxN3, cup2Int21BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top] at hi21
    simpa [cn4, stateAsFin3, hleft_val] using hi21
  have htpLocal : pn3TpLocalActual cn4.1 s.cN3.1 s.cN2.1 := by
    simpa [pn3TpLocalActual, s, cn4, cup2Boundary6, hleft_val] using And.intro hexp2 hi21left
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
        boundarySuccPN3 s cn4 := by
    simpa [s, cn4] using cup2Boundary6_move_eq_boundarySuccPN3 n hn4 hn9 c
  have hchange' : (boundarySuccPN3 s cn4).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, cn4, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccPN3 s cn4).encode s.encode := by
    simpa [cup2BoundaryState, s, cn4, hmove, hb6] using hnotedge
  simpa [s, cn4] using non617LocalClass_PN3_of_notedge_tp_actual s cn4 htpLocal hchange' hnotedge' -/

/- private theorem cphi_boundary_non617_idxN3_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    let s := cup2Boundary6 n hn4 hn9 c
    let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
    non617LocalClass Pn3 cn4.1 s.cN3.1 s.cN2.1 := by
  let s := cup2Boundary6 n hn4 hn9 c
  let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
  have htpMove := cphi_tpPreservingMove_of_move n hn4 h hmove
  obtain ⟨hexp2, hi21, hweight⟩ :=
    cup2TpPreserving_local_eqs n hn4 c (cup2BoundaryIdxN3 n hn9) htpMove
  have hout :
      cup2OutVal n (cup2BoundaryIdxN3 n hn9)
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (right (cup2BoundaryIdxN3 n hn9))).1 =
          TMidVal cn4.1 (c (cup2BoundaryIdxN3 n hn9)).1 (c (cup2BoundaryIdxN2 n hn9)).1 := by
    rw [cup2OutVal_boundaryIdxN3 n hn9, right_cup2BoundaryIdxN3 n hn9]
    simp [cn4, stateAsFin3]
  have hleft_ne0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
    simp [cup2BoundaryIdxN3]
    omega
  have hleft_val : (left (cup2BoundaryIdxN3 n hn9)).1 = n - 4 := by
    rw [left_val_of_ne_zero hleft_ne0, cup2BoundaryIdxN3]
    omega
  have hi_val : (cup2BoundaryIdxN3 n hn9).1 = n - 3 := by
    simp [cup2BoundaryIdxN3]
  have hleft_in : 2 ≤ n - 4 := by
    omega
  have hleft_top : n - 4 + 2 < n := by
    omega
  have hi_in : 2 ≤ n - 3 := by
    omega
  have hi_top : n - 3 + 2 < n := by
    omega
  have hexp2' :
      (if cn4.1 = 2 ∧ TMidVal cn4.1 s.cN3.1 s.cN2.1 ≠ 2 then 1 else 0) +
        (if TMidVal cn4.1 s.cN3.1 s.cN2.1 = 2 ∧ s.cN2.1 ≠ 2 then 1 else 0) =
      (if cn4.1 = 2 ∧ s.cN3.1 ≠ 2 then 1 else 0) +
        (if s.cN3.1 = 2 ∧ s.cN2.1 ≠ 2 then 1 else 0) := by
    rw [localExp2After, localExp2Before] at hexp2
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hexp2
    rw [hleft_val, hi_val] at hexp2
    rw [cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (n - 3) _ _ hi_in hi_top,
      cup2Exp2BitVal_eq_inner n (n - 3) _ _ hi_in hi_top] at hexp2
    simpa [s, cn4, cup2Boundary6, stateAsFin3, hleft_val] using hexp2
  have hweight' :
      (n - 4) * (if cn4.1 = 2 ∧ TMidVal cn4.1 s.cN3.1 s.cN2.1 ≠ 2 then 1 else 0) +
        (n - 3) * (if TMidVal cn4.1 s.cN3.1 s.cN2.1 = 2 ∧ s.cN2.1 ≠ 2 then 1 else 0) =
      (n - 4) * (if cn4.1 = 2 ∧ s.cN3.1 ≠ 2 then 1 else 0) +
        (n - 3) * (if s.cN3.1 = 2 ∧ s.cN2.1 ≠ 2 then 1 else 0) := by
    rw [localExp2WeightAfter, localExp2WeightBefore] at hweight
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hweight
    rw [hleft_val, hi_val] at hweight
    rw [cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Exp2BitVal_eq_inner n (n - 3) _ _ hi_in hi_top,
      cup2Exp2BitVal_eq_inner n (n - 3) _ _ hi_in hi_top] at hweight
    simpa [s, cn4, cup2Boundary6, stateAsFin3, hleft_val] using hweight
  have hi21' :
      (if cn4.1 = 2 ∧ TMidVal cn4.1 s.cN3.1 s.cN2.1 = 1 then 1 else 0) +
        (if TMidVal cn4.1 s.cN3.1 s.cN2.1 = 2 ∧ s.cN2.1 = 1 then 1 else 0) =
      (if cn4.1 = 2 ∧ s.cN3.1 = 1 then 1 else 0) +
        (if s.cN3.1 = 2 ∧ s.cN2.1 = 1 then 1 else 0) := by
    rw [localInt21After, localInt21Before] at hi21
    rw [hout, right_cup2BoundaryIdxN3 n hn9] at hi21
    rw [hleft_val, hi_val] at hi21
    rw [cup2Int21BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n (n - 4) _ _ hleft_in hleft_top,
      cup2Int21BitVal_eq_inner n (n - 3) _ _ hi_in hi_top,
      cup2Int21BitVal_eq_inner n (n - 3) _ _ hi_in hi_top] at hi21
    simpa [s, cn4, cup2Boundary6, stateAsFin3, hleft_val] using hi21
  have hpriv_local : TMidVal cn4.1 s.cN3.1 s.cN2.1 ≠ s.cN3.1 := by
    intro hout_eq
    have hsame : boundarySuccPN3 s cn4 = s := by
      ext <;> simp [boundarySuccPN3, hout_eq]
    have henc : (boundarySuccPN3 s cn4).encode = s.encode := by
      simpa [hsame]
    have hb6 :
        cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
          boundarySuccPN3 s cn4 := by
      simpa [s, cn4] using cup2Boundary6_move_eq_boundarySuccPN3 n hn4 hn9 c
    have hchange' : (boundarySuccPN3 s cn4).encode ≠ s.encode := by
      simpa [cup2BoundaryState, s, cn4, hmove, hb6] using hchange
    exact hchange' henc
  have hcases := pn3_tp_local_cases n hn9 cn4 ⟨s.cN3.1, s.cN3.2⟩ ⟨s.cN2.1, s.cN2.2⟩
      hexp2' hweight' hi21' hpriv_local
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
        boundarySuccPN3 s cn4 := by
    simpa [s, cn4] using cup2Boundary6_move_eq_boundarySuccPN3 n hn4 hn9 c
  have hchange' : (boundarySuccPN3 s cn4).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, cn4, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccPN3 s cn4).encode s.encode := by
    simpa [cup2BoundaryState, s, cn4, hmove, hb6] using hnotedge
  simpa [s, cn4] using non617LocalClass_PN3_of_notedge_tp_cases s cn4 hcases hchange' hnotedge' -/

private theorem cphi_boundary_change_mover_cases
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c) :
    c' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) ∨
      c' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) ∨
      c' = move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) ∨
      c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9) ∨
      c' = move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9) ∨
      c' = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) := by
  rcases cphi_boundary_change_has_boundary_mover n hn4 hn9 h hchange with
    ⟨i, _hpriv, hmove, hbdry⟩
  have hvals :
      i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 ∨ i.1 = n - 3 ∨ i.1 = n - 2 ∨ i.1 = n - 1 := by
    rcases hbdry with hlo | hhi
    · omega
    · have hi_lt : i.1 < n := i.2
      omega
  rcases hvals with hi0 | hi1 | hi2 | hiN3 | hiN2 | hiN1
  · left
    have hi : i = cup2BoundaryIdx0 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx0] using hi0
    simpa [hi] using hmove
  · right; left
    have hi : i = cup2BoundaryIdx1 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx1] using hi1
    simpa [hi] using hmove
  · right; right; left
    have hi : i = cup2BoundaryIdx2 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdx2] using hi2
    simpa [hi] using hmove
  · right; right; right; left
    have hi : i = cup2BoundaryIdxN3 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdxN3] using hiN3
    simpa [hi] using hmove
  · right; right; right; right; left
    have hi : i = cup2BoundaryIdxN2 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdxN2] using hiN2
    simpa [hi] using hmove
  · right; right; right; right; right
    have hi : i = cup2BoundaryIdxN1 n hn9 := by
      apply Fin.ext
      simpa [cup2BoundaryIdxN1] using hiN1
    simpa [hi] using hmove

private theorem cphi_boundary_non617_stateClass_or_hard
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass P0 s.cN1.1 s.c0.1 s.c1.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass P1 s.c0.1 s.c1.1 s.c2.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
       non617LocalClass P2 s.c1.1 s.c2.1 c3.1)) ∨
    c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass Pn2 s.cN3.1 s.cN2.1 s.cN1.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass Pn1 s.cN2.1 s.cN1.1 s.c0.1)) := by
  rcases cphi_boundary_change_mover_cases n hn4 hn9 h hchange with
    h0 | h1 | h2 | hN3 | hN2 | hN1
  · left
    refine ⟨h0, ?_⟩
    exact cphi_boundary_non617_idx0_stateClass n hn4 hn9 h0 hchange hnotedge
  · right; left
    refine ⟨h1, ?_⟩
    exact cphi_boundary_non617_idx1_stateClass n hn4 hn9 h1 hchange hnotedge
  · right; right; left
    refine ⟨h2, ?_⟩
    exact cphi_boundary_non617_idx2_stateClass n hn4 hn9 h h2 hchange hnotedge
  · right; right; right; left
    exact hN3
  · right; right; right; right; left
    refine ⟨hN2, ?_⟩
    exact cphi_boundary_non617_idxN2_stateClass n hn4 hn9 h hN2 hchange hnotedge
  · right; right; right; right; right
    refine ⟨hN1, ?_⟩
    exact cphi_boundary_non617_idxN1_stateClass n hn4 hn9 hN1 hchange hnotedge

private theorem cphi_boundary_non617_idxN3_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    let s := cup2Boundary6 n hn4 hn9 c
    let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
    non617LocalClass Pn3 cn4.1 s.cN3.1 s.cN2.1 := by
  let s := cup2Boundary6 n hn4 hn9 c
  let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
  have htpLocal : pn3TpLocal cn4.1 s.cN3.1 s.cN2.1 := by
    simpa [s, cn4, cup2Boundary6, stateAsFin3] using
      pn3TpLocal_of_tpPreserving n hn4 hn9 c (cphi_tpPreservingMove_of_move n hn4 h hmove)
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9)) =
        boundarySuccPN3 s cn4 := by
    simpa [s, cn4] using cup2Boundary6_move_eq_boundarySuccPN3 n hn4 hn9 c
  have hchange' : (boundarySuccPN3 s cn4).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, cn4, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccPN3 s cn4).encode s.encode := by
    simpa [cup2BoundaryState, s, cn4, hmove, hb6] using hnotedge
  simpa [s, cn4] using non617LocalClass_PN3_of_notedge_tp s cn4 htpLocal hchange' hnotedge'

private theorem cphi_boundary_non617_stateClass
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass P0 s.cN1.1 s.c0.1 s.c1.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass P1 s.c0.1 s.c1.1 s.c2.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx2 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       let c3 := stateAsFin3 n hn4 c (right (cup2BoundaryIdx2 n hn9))
       non617LocalClass P2 s.c1.1 s.c2.1 c3.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       let cn4 := stateAsFin3 n hn4 c (left (cup2BoundaryIdxN3 n hn9))
       non617LocalClass Pn3 cn4.1 s.cN3.1 s.cN2.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN2 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass Pn2 s.cN3.1 s.cN2.1 s.cN1.1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       non617LocalClass Pn1 s.cN2.1 s.cN1.1 s.c0.1)) := by
  rcases cphi_boundary_non617_stateClass_or_hard n hn4 hn9 h hchange hnotedge with
    h0 | h1 | h2 | hN3 | hN2 | hN1
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h2))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hN3, cphi_boundary_non617_idxN3_stateClass n hn4 hn9 h hN3 hchange hnotedge⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hN2))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hN1))))

private theorem fc_drop_of_move_local_drop
    (n : Nat) (hn4 : 4 ≤ n)
    {c' c : Config (cup2Spec n hn4)} {i : Fin n} {out : Nat}
    (hmove : c' = move (cup2System n hn4) c i)
    (hout :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = out)
    (hlocal :
      localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 out <
        localFcBefore (c (left i)).1 (c i).1 (c (right i)).1) :
    cup2Fc n hn4 c' < cup2Fc n hn4 c := by
  rw [hmove, cup2Fc_move_split n hn4 c i, cup2Fc_split n hn4 c i,
    cup2Fc_rest_move_eq n hn4 c i, hout]
  omega

private theorem fc_nonneg_of_move_local_nonneg
    (n : Nat) (hn4 : 4 ≤ n)
    {c' c : Config (cup2Spec n hn4)} {i : Fin n} {out : Nat}
    (hmove : c' = move (cup2System n hn4) c i)
    (hout :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = out)
    (hlocal :
      localFcBefore (c (left i)).1 (c i).1 (c (right i)).1 ≤
        localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 out) :
    cup2Fc n hn4 c ≤ cup2Fc n hn4 c' := by
  rw [hmove, cup2Fc_move_split n hn4 c i, cup2Fc_split n hn4 c i,
    cup2Fc_rest_move_eq n hn4 c i, hout]
  omega

private theorem fc_drop_two_of_move_local_drop_two
    (n : Nat) (hn4 : 4 ≤ n)
    {c' c : Config (cup2Spec n hn4)} {i : Fin n} {out : Nat}
    (hmove : c' = move (cup2System n hn4) c i)
    (hout :
      cup2OutVal n i (c (left i)).1 (c i).1 (c (right i)).1 = out)
    (hlocal :
      localFcAfter (c (left i)).1 (c i).1 (c (right i)).1 out + 2 =
        localFcBefore (c (left i)).1 (c i).1 (c (right i)).1) :
    cup2Fc n hn4 c' + 2 = cup2Fc n hn4 c := by
  rw [hmove, cup2Fc_move_split n hn4 c i, cup2Fc_split n hn4 c i,
    cup2Fc_rest_move_eq n hn4 c i, hout]
  omega

private theorem cphi_boundary_non617_fc_drop_or_nonneg
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    cup2Fc n hn4 c' < cup2Fc n hn4 c ∨
      cup2BadStepNonneg n hn4 c' c := by
  rcases cphi_boundary_non617_stateClass n hn4 hn9 h hchange hnotedge with
    h0 | h1 | h2 | hN3 | hN2 | hN1
  · have hclass :
        non617LocalClass P0
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 := by
      rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
      simpa [cup2Boundary6] using h0.2
    have hcases := non617LocalClass_localFc_cases P0
      (c (left (cup2BoundaryIdx0 n hn9))).1
      (c (cup2BoundaryIdx0 n hn9)).1
      (c (right (cup2BoundaryIdx0 n hn9))).1 hclass
    have hout :
        cup2OutVal n (cup2BoundaryIdx0 n hn9)
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 =
        non617LocalOut P0
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 := by
      simpa [non617LocalOut, P0] using
        cup2OutVal_boundaryIdx0 n hn9
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1
    rcases hcases with hdrop | hnonneg | hexc
    · left
      exact fc_drop_of_move_local_drop n hn4 h0.1 hout hdrop
    · right
      exact ⟨h.1.1, fc_nonneg_of_move_local_nonneg n hn4 h0.1 hout hnonneg⟩
    · left
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 h0.1 hout hexc
      omega
  · have hclass :
        non617LocalClass P1
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 := by
      rw [left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
      simpa [cup2Boundary6] using h1.2
    have hcases := non617LocalClass_localFc_cases P1
      (c (left (cup2BoundaryIdx1 n hn9))).1
      (c (cup2BoundaryIdx1 n hn9)).1
      (c (right (cup2BoundaryIdx1 n hn9))).1 hclass
    have hout :
        cup2OutVal n (cup2BoundaryIdx1 n hn9)
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 =
        non617LocalOut P1
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 := by
      simpa [non617LocalOut, P1] using
        cup2OutVal_boundaryIdx1 n hn9
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1
    rcases hcases with hdrop | hnonneg | hexc
    · left
      exact fc_drop_of_move_local_drop n hn4 h1.1 hout hdrop
    · right
      exact ⟨h.1.1, fc_nonneg_of_move_local_nonneg n hn4 h1.1 hout hnonneg⟩
    · left
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 h1.1 hout hexc
      omega
  · have hclass :
        non617LocalClass P2
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 := by
      rw [left_cup2BoundaryIdx2 n hn9]
      simpa [cup2Boundary6, stateAsFin3] using h2.2
    have hcases := non617LocalClass_localFc_cases P2
      (c (left (cup2BoundaryIdx2 n hn9))).1
      (c (cup2BoundaryIdx2 n hn9)).1
      (c (right (cup2BoundaryIdx2 n hn9))).1 hclass
    have hout :
        cup2OutVal n (cup2BoundaryIdx2 n hn9)
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 =
        non617LocalOut P2
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 := by
      simpa [non617LocalOut, P2] using
        cup2OutVal_boundaryIdx2 n hn9
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1
    rcases hcases with hdrop | hnonneg | hexc
    · left
      exact fc_drop_of_move_local_drop n hn4 h2.1 hout hdrop
    · right
      exact ⟨h.1.1, fc_nonneg_of_move_local_nonneg n hn4 h2.1 hout hnonneg⟩
    · left
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 h2.1 hout hexc
      omega
  · have hclass :
        non617LocalClass Pn3
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 := by
      rw [right_cup2BoundaryIdxN3 n hn9]
      simpa [cup2Boundary6, stateAsFin3] using hN3.2
    have hcases := non617LocalClass_localFc_cases Pn3
      (c (left (cup2BoundaryIdxN3 n hn9))).1
      (c (cup2BoundaryIdxN3 n hn9)).1
      (c (right (cup2BoundaryIdxN3 n hn9))).1 hclass
    have hout :
        cup2OutVal n (cup2BoundaryIdxN3 n hn9)
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 =
        non617LocalOut Pn3
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 := by
      simpa [non617LocalOut, Pn3] using
        cup2OutVal_boundaryIdxN3 n hn9
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1
    rcases hcases with hdrop | hnonneg | hexc
    · left
      exact fc_drop_of_move_local_drop n hn4 hN3.1 hout hdrop
    · right
      exact ⟨h.1.1, fc_nonneg_of_move_local_nonneg n hn4 hN3.1 hout hnonneg⟩
    · left
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 hN3.1 hout hexc
      omega
  · have hclass :
        non617LocalClass Pn2
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 := by
      rw [left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9]
      simpa [cup2Boundary6] using hN2.2
    have hcases := non617LocalClass_localFc_cases Pn2
      (c (left (cup2BoundaryIdxN2 n hn9))).1
      (c (cup2BoundaryIdxN2 n hn9)).1
      (c (right (cup2BoundaryIdxN2 n hn9))).1 hclass
    have hout :
        cup2OutVal n (cup2BoundaryIdxN2 n hn9)
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 =
        non617LocalOut Pn2
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 := by
      simpa [non617LocalOut, Pn2] using
        cup2OutVal_boundaryIdxN2 n hn9
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1
    rcases hcases with hdrop | hnonneg | hexc
    · left
      exact fc_drop_of_move_local_drop n hn4 hN2.1 hout hdrop
    · right
      exact ⟨h.1.1, fc_nonneg_of_move_local_nonneg n hn4 hN2.1 hout hnonneg⟩
    · left
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 hN2.1 hout hexc
      omega
  · have hclass :
        non617LocalClass Pn1
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 := by
      rw [left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
      simpa [cup2Boundary6] using hN1.2
    have hcases := non617LocalClass_localFc_cases Pn1
      (c (left (cup2BoundaryIdxN1 n hn9))).1
      (c (cup2BoundaryIdxN1 n hn9)).1
      (c (right (cup2BoundaryIdxN1 n hn9))).1 hclass
    have hout :
        cup2OutVal n (cup2BoundaryIdxN1 n hn9)
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 =
        non617LocalOut Pn1
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 := by
      simpa [non617LocalOut, Pn1] using
        cup2OutVal_boundaryIdxN1 n hn9
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1
    rcases hcases with hdrop | hnonneg | hexc
    · left
      exact fc_drop_of_move_local_drop n hn4 hN1.1 hout hdrop
    · right
      exact ⟨h.1.1, fc_nonneg_of_move_local_nonneg n hn4 hN1.1 hout hnonneg⟩
    · left
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 hN1.1 hout hexc
      omega

private theorem cphi_boundary_non617_nonneg_cases
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c))
    (hnonneg : cup2BadStepNonneg n hn4 c' c) :
    (c' = move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       s.cN1.1 = 0 ∧ s.c0.1 = 0 ∧ s.c1.1 = 1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       s.cN2.1 = 0 ∧ s.cN1.1 = 1 ∧ s.c0.1 = 1)) ∨
    (c' = move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9) ∧
      (let s := cup2Boundary6 n hn4 hn9 c
       s.cN2.1 = 2 ∧ s.cN1.1 = 0 ∧ s.c0.1 = 0)) := by
  have hfc_nonneg : cup2Fc n hn4 c ≤ cup2Fc n hn4 c' := hnonneg.2
  rcases cphi_boundary_non617_stateClass n hn4 hn9 h hchange hnotedge with
    h0 | h1 | h2 | hN3 | hN2 | hN1
  · have hclass :
        non617LocalClass P0
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 := by
      rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9]
      simpa [cup2Boundary6] using h0.2
    rcases non617LocalClass_split P0
        (c (left (cup2BoundaryIdx0 n hn9))).1
        (c (cup2BoundaryIdx0 n hn9)).1
        (c (right (cup2BoundaryIdx0 n hn9))).1 hclass with heasy | hnonneg0 | hexc
    · cases heasy
    · left
      refine ⟨h0.1, ?_⟩
      rw [left_cup2BoundaryIdx0 n hn9, right_cup2BoundaryIdx0 n hn9] at hnonneg0
      show (c (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
          (c (cup2BoundaryIdx0 n hn9)).1 = 0 ∧
          (c (cup2BoundaryIdx1 n hn9)).1 = 1
      simpa [cup2Boundary6, non617NonnegClass, P0] using hnonneg0
    · have hout :
          cup2OutVal n (cup2BoundaryIdx0 n hn9)
            (c (left (cup2BoundaryIdx0 n hn9))).1
            (c (cup2BoundaryIdx0 n hn9)).1
            (c (right (cup2BoundaryIdx0 n hn9))).1 =
          non617LocalOut P0
            (c (left (cup2BoundaryIdx0 n hn9))).1
            (c (cup2BoundaryIdx0 n hn9)).1
            (c (right (cup2BoundaryIdx0 n hn9))).1 := by
        simp [non617LocalOut, P0]
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 h0.1 hout
        (non617ExceptionalClass_localFc_drop_two P0
          (c (left (cup2BoundaryIdx0 n hn9))).1
          (c (cup2BoundaryIdx0 n hn9)).1
          (c (right (cup2BoundaryIdx0 n hn9))).1 hexc)
      have : False := by omega
      exact this.elim
  · have hclass :
        non617LocalClass P1
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 := by
      rw [left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
      simpa [cup2Boundary6] using h1.2
    rcases non617LocalClass_split P1
        (c (left (cup2BoundaryIdx1 n hn9))).1
        (c (cup2BoundaryIdx1 n hn9)).1
        (c (right (cup2BoundaryIdx1 n hn9))).1 hclass with heasy | hnonneg1 | hexc
    · have hout :
          cup2OutVal n (cup2BoundaryIdx1 n hn9)
            (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1 =
          non617LocalOut P1
            (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1 := by
        simp [non617LocalOut, P1]
      have hdrop := fc_drop_of_move_local_drop n hn4 h1.1 hout
        (non617EasyClass_localFc_drop P1
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 heasy)
      have : False := by omega
      exact this.elim
    · cases hnonneg1
    · have hout :
          cup2OutVal n (cup2BoundaryIdx1 n hn9)
            (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1 =
          non617LocalOut P1
            (c (left (cup2BoundaryIdx1 n hn9))).1
            (c (cup2BoundaryIdx1 n hn9)).1
            (c (right (cup2BoundaryIdx1 n hn9))).1 := by
        simp [non617LocalOut, P1]
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 h1.1 hout
        (non617ExceptionalClass_localFc_drop_two P1
          (c (left (cup2BoundaryIdx1 n hn9))).1
          (c (cup2BoundaryIdx1 n hn9)).1
          (c (right (cup2BoundaryIdx1 n hn9))).1 hexc)
      have : False := by omega
      exact this.elim
  · have hclass :
        non617LocalClass P2
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 := by
      rw [left_cup2BoundaryIdx2 n hn9]
      simpa [cup2Boundary6, stateAsFin3] using h2.2
    rcases non617LocalClass_split P2
        (c (left (cup2BoundaryIdx2 n hn9))).1
        (c (cup2BoundaryIdx2 n hn9)).1
        (c (right (cup2BoundaryIdx2 n hn9))).1 hclass with heasy | hnonneg2 | hexc
    · have hout :
          cup2OutVal n (cup2BoundaryIdx2 n hn9)
            (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1 =
          non617LocalOut P2
            (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1 := by
        simp [non617LocalOut, P2]
      have hdrop := fc_drop_of_move_local_drop n hn4 h2.1 hout
        (non617EasyClass_localFc_drop P2
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 heasy)
      have : False := by omega
      exact this.elim
    · cases hnonneg2
    · have hout :
          cup2OutVal n (cup2BoundaryIdx2 n hn9)
            (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1 =
          non617LocalOut P2
            (c (left (cup2BoundaryIdx2 n hn9))).1
            (c (cup2BoundaryIdx2 n hn9)).1
            (c (right (cup2BoundaryIdx2 n hn9))).1 := by
        simp [non617LocalOut, P2]
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 h2.1 hout
        (non617ExceptionalClass_localFc_drop_two P2
          (c (left (cup2BoundaryIdx2 n hn9))).1
          (c (cup2BoundaryIdx2 n hn9)).1
          (c (right (cup2BoundaryIdx2 n hn9))).1 hexc)
      have : False := by omega
      exact this.elim
  · have hclass :
        non617LocalClass Pn3
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 := by
      rw [right_cup2BoundaryIdxN3 n hn9]
      simpa [cup2Boundary6, stateAsFin3] using hN3.2
    rcases non617LocalClass_split Pn3
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (right (cup2BoundaryIdxN3 n hn9))).1 hclass with heasy | hnonneg3 | hexc
    · have hout :
          cup2OutVal n (cup2BoundaryIdxN3 n hn9)
            (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1 =
          non617LocalOut Pn3
            (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1 := by
        simp [non617LocalOut, Pn3]
      have hdrop := fc_drop_of_move_local_drop n hn4 hN3.1 hout
        (non617EasyClass_localFc_drop Pn3
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 heasy)
      have : False := by omega
      exact this.elim
    · cases hnonneg3
    · have hout :
          cup2OutVal n (cup2BoundaryIdxN3 n hn9)
            (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1 =
          non617LocalOut Pn3
            (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (right (cup2BoundaryIdxN3 n hn9))).1 := by
        simp [non617LocalOut, Pn3]
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 hN3.1 hout
        (non617ExceptionalClass_localFc_drop_two Pn3
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (right (cup2BoundaryIdxN3 n hn9))).1 hexc)
      have : False := by omega
      exact this.elim
  · have hclass :
        non617LocalClass Pn2
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 := by
      rw [left_cup2BoundaryIdxN2 n hn9, right_cup2BoundaryIdxN2 n hn9]
      simpa [cup2Boundary6] using hN2.2
    rcases non617LocalClass_split Pn2
        (c (left (cup2BoundaryIdxN2 n hn9))).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (c (right (cup2BoundaryIdxN2 n hn9))).1 hclass with heasy | hnonneg4 | hexc
    · have hout :
          cup2OutVal n (cup2BoundaryIdxN2 n hn9)
            (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1 =
          non617LocalOut Pn2
            (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1 := by
        simp [non617LocalOut, Pn2]
      have hdrop := fc_drop_of_move_local_drop n hn4 hN2.1 hout
        (non617EasyClass_localFc_drop Pn2
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 heasy)
      have : False := by omega
      exact this.elim
    · cases hnonneg4
    · have hout :
          cup2OutVal n (cup2BoundaryIdxN2 n hn9)
            (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1 =
          non617LocalOut Pn2
            (c (left (cup2BoundaryIdxN2 n hn9))).1
            (c (cup2BoundaryIdxN2 n hn9)).1
            (c (right (cup2BoundaryIdxN2 n hn9))).1 := by
        simp [non617LocalOut, Pn2]
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 hN2.1 hout
        (non617ExceptionalClass_localFc_drop_two Pn2
          (c (left (cup2BoundaryIdxN2 n hn9))).1
          (c (cup2BoundaryIdxN2 n hn9)).1
          (c (right (cup2BoundaryIdxN2 n hn9))).1 hexc)
      have : False := by omega
      exact this.elim
  · have hclass :
        non617LocalClass Pn1
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 := by
      rw [left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9]
      simpa [cup2Boundary6] using hN1.2
    rcases non617LocalClass_split Pn1
        (c (left (cup2BoundaryIdxN1 n hn9))).1
        (c (cup2BoundaryIdxN1 n hn9)).1
        (c (right (cup2BoundaryIdxN1 n hn9))).1 hclass with heasy | hnonneg5 | hexc
    · have hout :
          cup2OutVal n (cup2BoundaryIdxN1 n hn9)
            (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1 =
          non617LocalOut Pn1
            (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1 := by
        simp [non617LocalOut, Pn1]
      have hdrop := fc_drop_of_move_local_drop n hn4 hN1.1 hout
        (non617EasyClass_localFc_drop Pn1
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 heasy)
      have : False := by omega
      exact this.elim
    · rcases hnonneg5 with h011 | h200
      · right; left
        refine ⟨hN1.1, ?_⟩
        rw [left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9] at h011
        simpa [cup2Boundary6] using h011
      · right; right
        refine ⟨hN1.1, ?_⟩
        rw [left_cup2BoundaryIdxN1 n hn9, right_cup2BoundaryIdxN1 n hn9] at h200
        show (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
            (c (cup2BoundaryIdxN1 n hn9)).1 = 0 ∧
            (c (cup2BoundaryIdx0 n hn9)).1 = 0
        simpa [cup2Boundary6] using h200
    · have hout :
          cup2OutVal n (cup2BoundaryIdxN1 n hn9)
            (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1 =
          non617LocalOut Pn1
            (c (left (cup2BoundaryIdxN1 n hn9))).1
            (c (cup2BoundaryIdxN1 n hn9)).1
            (c (right (cup2BoundaryIdxN1 n hn9))).1 := by
        simp [non617LocalOut, Pn1]
      have htwo := fc_drop_two_of_move_local_drop_two n hn4 hN1.1 hout
        (non617ExceptionalClass_localFc_drop_two Pn1
          (c (left (cup2BoundaryIdxN1 n hn9))).1
          (c (cup2BoundaryIdxN1 n hn9)).1
          (c (right (cup2BoundaryIdxN1 n hn9))).1 hexc)
      have : False := by omega
      exact this.elim

private theorem boundaryState_decode_of_val
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)} {k : Nat}
    (hk : (cup2BoundaryState n hn4 hn9 c).1 = k) :
    cup2Boundary6 n hn4 hn9 c = decodeSixBoundary k := by
  have hklt : k < 324 := by
    simpa [hk] using (cup2BoundaryState n hn4 hn9 c).2
  have hs : cup2BoundaryState n hn4 hn9 c = ⟨k, hklt⟩ := by
    apply Fin.eq_of_val_eq
    exact hk
  have hdec := congrArg (fun s : SixState => decodeSixBoundary s.1) hs
  simpa [cup2BoundaryState, decodeSixBoundary_encode] using hdec

private theorem boundaryState_239_fields
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (h239 : (cup2BoundaryState n hn4 hn9 c).1 = 239) :
    (c (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdx1 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdx2 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdxN3 n hn9)).1 = 0 ∧
      (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
      (c (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
  have hdec := boundaryState_decode_of_val n hn4 hn9 h239
  have h0 : ((cup2Boundary6 n hn4 hn9 c).c0).1 = ((decodeSixBoundary 239).c0).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.c0 hdec)
  have h1 : ((cup2Boundary6 n hn4 hn9 c).c1).1 = ((decodeSixBoundary 239).c1).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.c1 hdec)
  have h2 : ((cup2Boundary6 n hn4 hn9 c).c2).1 = ((decodeSixBoundary 239).c2).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.c2 hdec)
  have hN3 : ((cup2Boundary6 n hn4 hn9 c).cN3).1 = ((decodeSixBoundary 239).cN3).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.cN3 hdec)
  have hN2 : ((cup2Boundary6 n hn4 hn9 c).cN2).1 = ((decodeSixBoundary 239).cN2).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.cN2 hdec)
  have hN1 : ((cup2Boundary6 n hn4 hn9 c).cN1).1 = ((decodeSixBoundary 239).cN1).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.cN1 hdec)
  have h0' : ((decodeSixBoundary 239).c0).1 = 1 := by norm_num [decodeSixBoundary]
  have h1' : ((decodeSixBoundary 239).c1).1 = 1 := by norm_num [decodeSixBoundary]
  have h2' : ((decodeSixBoundary 239).c2).1 = 1 := by norm_num [decodeSixBoundary]
  have hN3' : ((decodeSixBoundary 239).cN3).1 = 0 := by norm_num [decodeSixBoundary]
  have hN2' : ((decodeSixBoundary 239).cN2).1 = 2 := by norm_num [decodeSixBoundary]
  have hN1' : ((decodeSixBoundary 239).cN1).1 = 1 := by norm_num [decodeSixBoundary]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h0.trans h0'
  · exact h1.trans h1'
  · exact h2.trans h2'
  · exact hN3.trans hN3'
  · exact hN2.trans hN2'
  · exact hN1.trans hN1'

private theorem boundaryState_245_fields
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (h245 : (cup2BoundaryState n hn4 hn9 c).1 = 245) :
    (c (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdx1 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdx2 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdxN3 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
      (c (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
  have hdec := boundaryState_decode_of_val n hn4 hn9 h245
  have h0 : ((cup2Boundary6 n hn4 hn9 c).c0).1 = ((decodeSixBoundary 245).c0).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.c0 hdec)
  have h1 : ((cup2Boundary6 n hn4 hn9 c).c1).1 = ((decodeSixBoundary 245).c1).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.c1 hdec)
  have h2 : ((cup2Boundary6 n hn4 hn9 c).c2).1 = ((decodeSixBoundary 245).c2).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.c2 hdec)
  have hN3 : ((cup2Boundary6 n hn4 hn9 c).cN3).1 = ((decodeSixBoundary 245).cN3).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.cN3 hdec)
  have hN2 : ((cup2Boundary6 n hn4 hn9 c).cN2).1 = ((decodeSixBoundary 245).cN2).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.cN2 hdec)
  have hN1 : ((cup2Boundary6 n hn4 hn9 c).cN1).1 = ((decodeSixBoundary 245).cN1).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.cN1 hdec)
  have h0' : ((decodeSixBoundary 245).c0).1 = 1 := by norm_num [decodeSixBoundary]
  have h1' : ((decodeSixBoundary 245).c1).1 = 1 := by norm_num [decodeSixBoundary]
  have h2' : ((decodeSixBoundary 245).c2).1 = 1 := by norm_num [decodeSixBoundary]
  have hN3' : ((decodeSixBoundary 245).cN3).1 = 1 := by norm_num [decodeSixBoundary]
  have hN2' : ((decodeSixBoundary 245).cN2).1 = 2 := by norm_num [decodeSixBoundary]
  have hN1' : ((decodeSixBoundary 245).cN1).1 = 1 := by norm_num [decodeSixBoundary]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h0.trans h0'
  · exact h1.trans h1'
  · exact h2.trans h2'
  · exact hN3.trans hN3'
  · exact hN2.trans hN2'
  · exact hN1.trans hN1'

private theorem boundaryState_251_fields
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c : Config (cup2Spec n hn4)}
    (h251 : (cup2BoundaryState n hn4 hn9 c).1 = 251) :
    (c (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdx1 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdx2 n hn9)).1 = 1 ∧
      (c (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧
      (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
      (c (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
  have hdec := boundaryState_decode_of_val n hn4 hn9 h251
  have h0 : ((cup2Boundary6 n hn4 hn9 c).c0).1 = ((decodeSixBoundary 251).c0).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.c0 hdec)
  have h1 : ((cup2Boundary6 n hn4 hn9 c).c1).1 = ((decodeSixBoundary 251).c1).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.c1 hdec)
  have h2 : ((cup2Boundary6 n hn4 hn9 c).c2).1 = ((decodeSixBoundary 251).c2).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.c2 hdec)
  have hN3 : ((cup2Boundary6 n hn4 hn9 c).cN3).1 = ((decodeSixBoundary 251).cN3).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.cN3 hdec)
  have hN2 : ((cup2Boundary6 n hn4 hn9 c).cN2).1 = ((decodeSixBoundary 251).cN2).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.cN2 hdec)
  have hN1 : ((cup2Boundary6 n hn4 hn9 c).cN1).1 = ((decodeSixBoundary 251).cN1).1 := by
    simpa using congrArg Fin.val (congrArg SixBoundary.cN1 hdec)
  have h0' : ((decodeSixBoundary 251).c0).1 = 1 := by norm_num [decodeSixBoundary]
  have h1' : ((decodeSixBoundary 251).c1).1 = 1 := by norm_num [decodeSixBoundary]
  have h2' : ((decodeSixBoundary 251).c2).1 = 1 := by norm_num [decodeSixBoundary]
  have hN3' : ((decodeSixBoundary 251).cN3).1 = 2 := by norm_num [decodeSixBoundary]
  have hN2' : ((decodeSixBoundary 251).cN2).1 = 2 := by norm_num [decodeSixBoundary]
  have hN1' : ((decodeSixBoundary 251).cN1).1 = 1 := by norm_num [decodeSixBoundary]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h0.trans h0'
  · exact h1.trans h1'
  · exact h2.trans h2'
  · exact hN3.trans hN3'
  · exact hN2.trans hN2'
  · exact hN1.trans hN1'

private theorem TMidVal_zero_two_eq_one_implies_left_one
    {L : Nat} (hL : L < 3) (hout : TMidVal L 0 2 = 1) : L = 1 := by
  interval_cases L <;> simp [TMidVal] at hout <;> omega

private theorem special239_245_local_shape
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hspecial : (cup2BoundaryState n hn4 hn9 c).1 = 239 ∧
      (cup2BoundaryState n hn4 hn9 c').1 = 245) :
    c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9) ∧
      (c (left (cup2BoundaryIdxN3 n hn9))).1 = 1 ∧
      (c (cup2BoundaryIdxN3 n hn9)).1 = 0 ∧
      (c (cup2BoundaryIdxN2 n hn9)).1 = 2 ∧
      (c' (cup2BoundaryIdxN3 n hn9)).1 = 1 := by
  rcases cphi_boundary_change_has_boundary_mover n hn4 hn9 h hchange with
    ⟨i, hpriv, hmove, _⟩
  rcases boundaryState_239_fields n hn4 hn9 hspecial.1 with
    ⟨_, _, _, hcN3, hcN2, _⟩
  rcases boundaryState_245_fields n hn4 hn9 hspecial.2 with
    ⟨_, _, _, hdN3, _, _⟩
  have hi : i = cup2BoundaryIdxN3 n hn9 := by
    by_contra hne
    have hne' : cup2BoundaryIdxN3 n hn9 ≠ i := by
      intro heq
      exact hne heq.symm
    have hsame :
        (c' (cup2BoundaryIdxN3 n hn9)).1 =
          (c (cup2BoundaryIdxN3 n hn9)).1 := by
      rw [hmove]
      simpa using congrArg Fin.val
        (move_apply_ne n hn4 c i (cup2BoundaryIdxN3 n hn9) hne')
    rw [hdN3, hcN3] at hsame
    omega
  subst hi
  have hLlt : (c (left (cup2BoundaryIdxN3 n hn9))).1 < 3 := by
    have h0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
      simp [cup2BoundaryIdxN3]
      omega
    have h1 : (cup2BoundaryIdxN3 n hn9).1 ≠ 1 := by
      simp [cup2BoundaryIdxN3]
      omega
    have htop : (cup2BoundaryIdxN3 n hn9).1 + 1 ≠ n := by
      simp [cup2BoundaryIdxN3]
      omega
    simpa [cup2Spec, cup2M_left_mid hn4 h0 h1 htop] using
      (c (left (cup2BoundaryIdxN3 n hn9))).2
  have hout : TMidVal (c (left (cup2BoundaryIdxN3 n hn9))).1
      (c (cup2BoundaryIdxN3 n hn9)).1 (c (cup2BoundaryIdxN2 n hn9)).1 = 1 := by
    rw [← hdN3, hmove, move_apply_self_val n hn4 c (cup2BoundaryIdxN3 n hn9),
      cup2OutVal_boundaryIdxN3 n hn9, right_cup2BoundaryIdxN3 n hn9]
  have hL : (c (left (cup2BoundaryIdxN3 n hn9))).1 = 1 := by
    apply TMidVal_zero_two_eq_one_implies_left_one hLlt
    simpa [hcN3, hcN2] using hout
  exact ⟨hmove, hL, hcN3, hcN2, hdN3⟩

private theorem special239_245_fc_drop
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hspecial : (cup2BoundaryState n hn4 hn9 c).1 = 239 ∧
      (cup2BoundaryState n hn4 hn9 c').1 = 245) :
    cup2Fc n hn4 c' < cup2Fc n hn4 c := by
  rcases special239_245_local_shape n hn4 hn9 h hchange hspecial with
    ⟨hmove, hL, hS, hR, _⟩
  rw [hmove, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN3 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdxN3 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN3 n hn9)]
  rw [right_cup2BoundaryIdxN3 n hn9]
  have hout :
      cup2OutVal n (cup2BoundaryIdxN3 n hn9)
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (cup2BoundaryIdxN2 n hn9)).1 = 1 := by
    simp [cup2OutVal_boundaryIdxN3, hL, hS, hR, TMidVal]
  rw [hout]
  simp [localFcAfter, localFcBefore, frontierBitVal, hL, hS, hR]

private theorem sccSubRank_239 :
    sccSubRank ((⟨239, by decide⟩ : SixState)) = 0 := by
  decide

private theorem sccSubRank_245 :
    sccSubRank ((⟨245, by decide⟩ : SixState)) = 2 := by
  decide

private theorem sccSubRank_251 :
    sccSubRank ((⟨251, by decide⟩ : SixState)) = 1 := by
  decide

private theorem condensationRank_239 :
    condensationRank ((⟨239, by decide⟩ : SixState)) = 7 := by
  decide

private theorem condensationRank_245 :
    condensationRank ((⟨245, by decide⟩ : SixState)) = 7 := by
  decide

private theorem condensationRank_251 :
    condensationRank ((⟨251, by decide⟩ : SixState)) = 7 := by
  decide

private theorem TMidVal_one_two_copyNeighbor
    {L : Nat} (hL : L < 3) :
    TMidVal L 1 2 = L ∨ TMidVal L 1 2 = 2 := by
  interval_cases L <;> simp [TMidVal]

private theorem TMidVal_two_two_copyNeighbor
    {L : Nat} (hL : L < 3) :
    TMidVal L 2 2 = L ∨ TMidVal L 2 2 = 2 := by
  interval_cases L <;> simp [TMidVal]

private theorem scc_cond_eq_scc_drop_mover_n3
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hs : (cup2BoundaryState n hn4 hn9 c).1 ∈ ({239, 245, 251} : Finset Nat))
    (hs' : (cup2BoundaryState n hn4 hn9 c').1 ∈ ({239, 245, 251} : Finset Nat)) :
    c' = move (cup2System n hn4) c (cup2BoundaryIdxN3 n hn9) := by
  rcases cphi_boundary_change_has_boundary_mover n hn4 hn9 h hchange with
    ⟨i, _, hmove, _⟩
  have hshared :=
    scc_shared_fields (cup2Boundary6 n hn4 hn9 c) (cup2Boundary6 n hn4 hn9 c')
      (by simpa [cup2BoundaryState] using hs) (by simpa [cup2BoundaryState] using hs')
  have hi : i = cup2BoundaryIdxN3 n hn9 := by
    by_contra hne
    have hne' : cup2BoundaryIdxN3 n hn9 ≠ i := by
      intro heq
      exact hne heq.symm
    have hcN3 :
        (cup2Boundary6 n hn4 hn9 c').cN3 = (cup2Boundary6 n hn4 hn9 c).cN3 := by
      rw [hmove]
      apply Fin.eq_of_val_eq
      simpa using congrArg Fin.val
        (move_apply_ne n hn4 c i (cup2BoundaryIdxN3 n hn9) hne')
    have hb6eq : cup2Boundary6 n hn4 hn9 c' = cup2Boundary6 n hn4 hn9 c := by
      rcases hshared with ⟨h0, h1, h2, hN2, hN1⟩
      exact SixBoundary.ext h0.symm h1.symm h2.symm hcN3 hN2.symm hN1.symm
    have hstateeq : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c := by
      simpa [cup2BoundaryState] using congrArg SixBoundary.encode hb6eq
    exact hchange hstateeq
  simpa [hi] using hmove

private theorem scc_cond_eq_scc_drop_fc_noninc
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hedge : sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c))
    (hcond : condensationRank (cup2BoundaryState n hn4 hn9 c') =
      condensationRank (cup2BoundaryState n hn4 hn9 c))
    (hscc : sccSubRank (cup2BoundaryState n hn4 hn9 c') <
      sccSubRank (cup2BoundaryState n hn4 hn9 c)) :
    cup2Fc n hn4 c' ≤ cup2Fc n hn4 c := by
  have hmemb :=
    scc_membership_of_edge_cond_eq_scc_drop
      (cup2BoundaryState n hn4 hn9 c') (cup2BoundaryState n hn4 hn9 c) hedge hcond hscc
  have hmove :=
    scc_cond_eq_scc_drop_mover_n3 n hn4 hn9 h hchange hmemb.1 hmemb.2
  rw [hmove, cup2Fc_move_split n hn4 c (cup2BoundaryIdxN3 n hn9),
    cup2Fc_split n hn4 c (cup2BoundaryIdxN3 n hn9),
    cup2Fc_rest_move_eq n hn4 c (cup2BoundaryIdxN3 n hn9),
    right_cup2BoundaryIdxN3 n hn9]
  have hLlt : (c (left (cup2BoundaryIdxN3 n hn9))).1 < 3 := by
    have h0 : (cup2BoundaryIdxN3 n hn9).1 ≠ 0 := by
      simp [cup2BoundaryIdxN3]
      omega
    have h1 : (cup2BoundaryIdxN3 n hn9).1 ≠ 1 := by
      simp [cup2BoundaryIdxN3]
      omega
    have htop : (cup2BoundaryIdxN3 n hn9).1 + 1 ≠ n := by
      simp [cup2BoundaryIdxN3]
      omega
    simpa [cup2Spec, cup2M_left_mid hn4 h0 h1 htop] using
      (c (left (cup2BoundaryIdxN3 n hn9))).2
  have hs_cases : (cup2BoundaryState n hn4 hn9 c).1 = 239 ∨
      (cup2BoundaryState n hn4 hn9 c).1 = 245 ∨
      (cup2BoundaryState n hn4 hn9 c).1 = 251 := by
    simpa using hmemb.1
  rcases hs_cases with h239 | h245 | h251
  · exfalso
    have hsEq : cup2BoundaryState n hn4 hn9 c = (⟨239, by decide⟩ : SixState) := by
      apply Fin.eq_of_val_eq
      exact h239
    rw [hsEq, sccSubRank_239] at hscc
    exact Nat.not_lt_zero _ hscc
  · rcases boundaryState_245_fields n hn4 hn9 h245 with
      ⟨_, _, _, hS, hR, _⟩
    have hcopy :
        cup2OutVal n (cup2BoundaryIdxN3 n hn9)
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1 =
            (c (left (cup2BoundaryIdxN3 n hn9))).1 ∨
          cup2OutVal n (cup2BoundaryIdxN3 n hn9)
            (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (cup2BoundaryIdxN2 n hn9)).1 =
              (c (cup2BoundaryIdxN2 n hn9)).1 := by
      rw [cup2OutVal_boundaryIdxN3 n hn9]
      rcases TMidVal_one_two_copyNeighbor hLlt with hleft | hright
      · left
        simpa [hS, hR] using hleft
      · right
        simpa [hS, hR] using hright
    have hlocal :=
      localFcAfter_le_of_copyNeighbor
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1)
        hcopy
    omega
  · rcases boundaryState_251_fields n hn4 hn9 h251 with
      ⟨_, _, _, hS, hR, _⟩
    have hcopy :
        cup2OutVal n (cup2BoundaryIdxN3 n hn9)
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1 =
            (c (left (cup2BoundaryIdxN3 n hn9))).1 ∨
          cup2OutVal n (cup2BoundaryIdxN3 n hn9)
            (c (left (cup2BoundaryIdxN3 n hn9))).1
            (c (cup2BoundaryIdxN3 n hn9)).1
            (c (cup2BoundaryIdxN2 n hn9)).1 =
              (c (cup2BoundaryIdxN2 n hn9)).1 := by
      rw [cup2OutVal_boundaryIdxN3 n hn9]
      rcases TMidVal_two_two_copyNeighbor hLlt with hleft | hright
      · left
        simpa [hS, hR] using hleft
      · right
        simpa [hS, hR] using hright
    have hlocal :=
      localFcAfter_le_of_copyNeighbor
        (c (left (cup2BoundaryIdxN3 n hn9))).1
        (c (cup2BoundaryIdxN3 n hn9)).1
        (c (cup2BoundaryIdxN2 n hn9)).1
        (cup2OutVal n (cup2BoundaryIdxN3 n hn9)
          (c (left (cup2BoundaryIdxN3 n hn9))).1
          (c (cup2BoundaryIdxN3 n hn9)).1
          (c (cup2BoundaryIdxN2 n hn9)).1)
        hcopy
    omega

/-- Boundary-only rank data from the precomputed 6-tuple automaton. -/
private def cphiBoundaryRank (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : Nat × Nat :=
  let s := cup2BoundaryState n hn4 hn9 c
  (condensationRank s, sccSubRank s)

/-- Direct `CΦ` lex measure. The boundary-changing branch is handled by the
    six-tuple DAG together with local `fc` control on the SCC, so the order is
    `(condensationRank, fc, sccSubRank, deepMidHopPotential)`. -/
private def cphiMeasure (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (c : Config (cup2Spec n hn4)) : Nat × Nat × Nat × Nat :=
  let br := cphiBoundaryRank n hn4 hn9 c
  (br.1, cup2Fc n hn4 c, br.2, deepMidHopPotential n hn4 c)

private def cphiLex : (Nat × Nat × Nat × Nat) → (Nat × Nat × Nat × Nat) → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))

private theorem cphiLex_wf : WellFounded cphiLex := by
  exact WellFounded.prod_lex Nat.lt_wfRel.wf
    (WellFounded.prod_lex Nat.lt_wfRel.wf
      (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf))

private theorem cphiBoundaryRank_eq_of_boundary_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hbdry : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c) :
    cphiBoundaryRank n hn4 hn9 c' = cphiBoundaryRank n hn4 hn9 c := by
  simp [cphiBoundaryRank, hbdry]

/-- Fixed-boundary `CΦ` steps already decrease the direct `cphiMeasure`.
    This is the completed inner half of the eventual direct `cup2CPhiStep_wf`
    proof. -/
private theorem boundaryFixed_cphiMeasure_drop
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2BoundaryFixedCPhiStep n hn4 hn9 c' c) :
    cphiLex (cphiMeasure n hn4 hn9 c') (cphiMeasure n hn4 hn9 c) := by
  have houter : cup2SyntheticOuterStep n hn4 c' c := by
    exact ⟨h.1.1.1, h.1.2.1⟩
  have hbrank :
      cphiBoundaryRank n hn4 hn9 c' = cphiBoundaryRank n hn4 hn9 c :=
    cphiBoundaryRank_eq_of_boundary_eq n hn4 hn9 h.2
  rcases fixed_boundary_fc_or_deep_drop n hn4 hn9 houter h.2 with hfc | ⟨hfc_eq, hdeep⟩
  · unfold cphiLex cphiMeasure
    simp [hbrank]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hfc)
  · unfold cphiLex cphiMeasure
    simp [hbrank, hfc_eq]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ hdeep))

private theorem cphiMeasure_drop_of_condRankDrop
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hcond :
      condensationRank (cup2BoundaryState n hn4 hn9 c') <
        condensationRank (cup2BoundaryState n hn4 hn9 c)) :
    cphiLex (cphiMeasure n hn4 hn9 c') (cphiMeasure n hn4 hn9 c) := by
  unfold cphiLex cphiMeasure cphiBoundaryRank
  simp
  exact Prod.Lex.left _ _ hcond

private theorem cphiMeasure_drop_of_fc_when_cond_eq
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hcond_eq :
      condensationRank (cup2BoundaryState n hn4 hn9 c') =
        condensationRank (cup2BoundaryState n hn4 hn9 c))
    (hfc : cup2Fc n hn4 c' < cup2Fc n hn4 c) :
    cphiLex (cphiMeasure n hn4 hn9 c') (cphiMeasure n hn4 hn9 c) := by
  unfold cphiLex cphiMeasure cphiBoundaryRank
  simp [hcond_eq]
  exact Prod.Lex.right _ (Prod.Lex.left _ _ hfc)

private theorem cphiMeasure_drop_of_sccRankDrop_fc_noninc
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hcond_eq :
      condensationRank (cup2BoundaryState n hn4 hn9 c') =
        condensationRank (cup2BoundaryState n hn4 hn9 c))
    (hfc_le : cup2Fc n hn4 c' ≤ cup2Fc n hn4 c)
    (hscc :
      sccSubRank (cup2BoundaryState n hn4 hn9 c') <
        sccSubRank (cup2BoundaryState n hn4 hn9 c)) :
    cphiLex (cphiMeasure n hn4 hn9 c') (cphiMeasure n hn4 hn9 c) := by
  rcases lt_or_eq_of_le hfc_le with hfc | hfc_eq
  · exact cphiMeasure_drop_of_fc_when_cond_eq n hn4 hn9 hcond_eq hfc
  · unfold cphiLex cphiMeasure cphiBoundaryRank
    simp [hcond_eq, hfc_eq]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ hscc))

private theorem cphiMeasure_drop_of_sixTupleEdge
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hedge : sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c)) :
    cphiLex (cphiMeasure n hn4 hn9 c') (cphiMeasure n hn4 hn9 c) := by
  have hdec := sixTuple_edge_lex_decrease hedge
  rcases hdec with hcond | hscc | hspecial
  · exact cphiMeasure_drop_of_condRankDrop n hn4 hn9 hcond
  · have hfc_le :=
      scc_cond_eq_scc_drop_fc_noninc n hn4 hn9 h hchange hedge hscc.1 hscc.2
    exact cphiMeasure_drop_of_sccRankDrop_fc_noninc n hn4 hn9 hscc.1 hfc_le hscc.2
  · have hcond_eq :
        condensationRank (cup2BoundaryState n hn4 hn9 c') =
          condensationRank (cup2BoundaryState n hn4 hn9 c) := by
      have hsrc : cup2BoundaryState n hn4 hn9 c = (⟨239, by decide⟩ : SixState) := by
        apply Fin.eq_of_val_eq
        exact hspecial.1
      have hdst : cup2BoundaryState n hn4 hn9 c' = (⟨245, by decide⟩ : SixState) := by
        apply Fin.eq_of_val_eq
        exact hspecial.2
      rw [hdst, hsrc, condensationRank_245, condensationRank_239]
    exact cphiMeasure_drop_of_fc_when_cond_eq n hn4 hn9 hcond_eq
      (special239_245_fc_drop n hn4 hn9 h hchange hspecial)

private theorem cphi_strict_p1_102_impossible
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hmove : c' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9))
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c)
    (hnotedge : ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c))
    (hfcdrop : cup2Fc n hn4 c' < cup2Fc n hn4 c)
    (hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1)
    (hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 0)
    (hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 2) :
    False := by
  let s := cup2Boundary6 n hn4 hn9 c
  have hb6 :
      cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9)) =
        boundarySuccP1 s := by
    simpa [s] using cup2Boundary6_move_eq_boundarySuccP1 n hn4 hn9 c
  have hchange' : (boundarySuccP1 s).encode ≠ s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hchange
  have hnotedge' : ¬ sixTupleEdge (boundarySuccP1 s).encode s.encode := by
    simpa [cup2BoundaryState, s, hmove, hb6] using hnotedge
  have hfamily := p1_102_non617_boundary_family s ⟨by simpa [s, cup2Boundary6] using hc0,
      by simpa [s, cup2Boundary6] using hc1,
      by simpa [s, cup2Boundary6] using hc2⟩ hchange' hnotedge'
  have hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    simpa [s, cup2Boundary6] using hfamily.1
  have hcN3N2 :
      ((c (cup2BoundaryIdxN3 n hn9)).1 = 0 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 = 1) ∨
        ((c (cup2BoundaryIdxN3 n hn9)).1 = 0 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 = 2) ∨
        ((c (cup2BoundaryIdxN3 n hn9)).1 = 1 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 = 2) ∨
        ((c (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 = 0) ∨
        ((c (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 = 1) ∨
        ((c (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧ (c (cup2BoundaryIdxN2 n hn9)).1 = 2) := by
    simpa [s, cup2Boundary6] using hfamily.2
  have hc'N1 : (c' (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
    rw [hmove]
    have hne : cup2BoundaryIdxN1 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN1, cup2BoundaryIdx1] at hval
      omega
    rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN1 n hn9) hne]
    exact hcN1
  have hc'0 : (c' (cup2BoundaryIdx0 n hn9)).1 = 1 := by
    rw [hmove]
    have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx0, cup2BoundaryIdx1] at hval
    rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
    exact hc0
  have hc'1 : (c' (cup2BoundaryIdx1 n hn9)).1 = 1 := by
    rw [hmove, move_apply_self_val n hn4 c (cup2BoundaryIdx1 n hn9),
      cup2OutVal_boundaryIdx1 n hn9, left_cup2BoundaryIdx1 n hn9, right_cup2BoundaryIdx1 n hn9]
    simpa [hc0, hc1, hc2] using lookup_low_102
  have hc'2 : (c' (cup2BoundaryIdx2 n hn9)).1 = 2 := by
    rw [hmove]
    have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdx2, cup2BoundaryIdx1] at hval
    rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
    exact hc2
  have hc'N3N2 :
      ((c' (cup2BoundaryIdxN3 n hn9)).1 = 0 ∧ (c' (cup2BoundaryIdxN2 n hn9)).1 = 1) ∨
        ((c' (cup2BoundaryIdxN3 n hn9)).1 = 0 ∧ (c' (cup2BoundaryIdxN2 n hn9)).1 = 2) ∨
        ((c' (cup2BoundaryIdxN3 n hn9)).1 = 1 ∧ (c' (cup2BoundaryIdxN2 n hn9)).1 = 2) ∨
        ((c' (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧ (c' (cup2BoundaryIdxN2 n hn9)).1 = 0) ∨
        ((c' (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧ (c' (cup2BoundaryIdxN2 n hn9)).1 = 1) ∨
        ((c' (cup2BoundaryIdxN3 n hn9)).1 = 2 ∧ (c' (cup2BoundaryIdxN2 n hn9)).1 = 2) := by
    rw [hmove]
    have hneN3 : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN3, cup2BoundaryIdx1] at hval
      omega
    have hneN2 : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdx1 n hn9 := by
      intro hEq
      have hval := congrArg Fin.val hEq
      simp [cup2BoundaryIdxN2, cup2BoundaryIdx1] at hval
      omega
    rw [move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN3 n hn9) hneN3,
      move_apply_ne n hn4 c (cup2BoundaryIdx1 n hn9) (cup2BoundaryIdxN2 n hn9) hneN2]
    exact hcN3N2
  have hsrc_eq_fc : cup2PhiFull n hn4 c = cup2Fc n hn4 c := by
    exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4 c
      (fun d hreach => p1_102_tpReachable_fc_le_core n hn4 hn9 c hcN1 hc0 hc1 hc2 hcN3N2 hreach)
  have hdst_eq_fc : cup2PhiFull n hn4 c' = cup2Fc n hn4 c' := by
    exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4 c'
      (fun d hreach => p1_112_tpReachable_fc_le_core n hn4 hn9 c' hc'N1 hc'0 hc'1 hc'2 hc'N3N2 hreach)
  have hphi_eq := h.2.2
  rw [hsrc_eq_fc, hdst_eq_fc] at hphi_eq
  omega

/-- Direct `CΦ` well-foundedness from the two exact boundary-changing bridge
    obligations suggested by the current exact scan:
    1. boundary-changing `CΦ` steps land in `sixTupleEdge`
    2. the special edge `239 -> 245` is impossible for `CΦ`

    Once these are proved, the old `psiRank` segment route can be deleted. -/
private theorem cup2CPhiStep_wf_of_sixTupleBridge
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    (h_bridge :
      ∀ {c' c : Config (cup2Spec n hn4)},
        cup2CPhiStep n hn4 c' c →
        cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c →
        sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
          (cup2BoundaryState n hn4 hn9 c)) :
    WellFounded (cup2CPhiStep n hn4) := by
  refine Subrelation.wf ?_ (InvImage.wf (cphiMeasure n hn4 hn9) cphiLex_wf)
  intro c' c h
  by_cases hfixed : cup2BoundaryState n hn4 hn9 c' = cup2BoundaryState n hn4 hn9 c
  · exact boundaryFixed_cphiMeasure_drop n hn4 hn9 ⟨h, hfixed⟩
  · exact cphiMeasure_drop_of_sixTupleEdge n hn4 hn9 h hfixed
      (h_bridge h hfixed)

/-! ### Active Bridge Target -/

/-- Exact no-drop contradiction theorem behind the remaining `CΦ` bridge.

    After reordering the direct measure to

    `(condensationRank, fc, sccSubRank, deepMidHopPotential)`,

    the special SCC edge `239 -> 245` is handled analytically by `fc` drop,
    and the SCC-subrank branch is handled by `fc` nonincrease plus
    `sccSubRank` drop. So the only remaining bridge debt is:

    - a boundary-changing `CΦ` step cannot be non-617

    This is now exactly the handoff target. -/
private theorem cphiBoundary_nodrop_non617_impossible
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n) :
    ∀ {c' c : Config (cup2Spec n hn4)},
      cup2CPhiStep n hn4 c' c →
      cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c →
      ¬ sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
        (cup2BoundaryState n hn4 hn9 c) →
      False := by
  intro c' c h hchange hnotedge
  rcases cphi_boundary_non617_fc_drop_or_nonneg n hn4 hn9 h hchange hnotedge with
    hfcdrop | hnonneg
  · have hbad : badStep (cup2System n hn4) (cup2GoodCycle n hn4) c' c := h.1.1
    have hfuture_eq : cup2FutureFc n hn4 c' = cup2FutureFc n hn4 c := h.1.2
    have hphi_eq : cup2PhiFull n hn4 c' = cup2PhiFull n hn4 c := h.2.2
    by_cases hp102 :
        c' = move (cup2System n hn4) c (cup2BoundaryIdx1 n hn9) ∧
          (c (cup2BoundaryIdx0 n hn9)).1 = 1 ∧
          (c (cup2BoundaryIdx1 n hn9)).1 = 0 ∧
          (c (cup2BoundaryIdx2 n hn9)).1 = 2
    · rcases hp102 with ⟨hmove, hc0, hc1, hc2⟩
      exact cphi_strict_p1_102_impossible n hn4 hn9 h hmove hchange hnotedge hfcdrop hc0 hc1 hc2
    · -- Remaining quantitative residue:
      -- strict local/global fc drop together with PhiFull equality on the
      -- classified non617 branch outside the handled `P1 : (1,0,2)` family.
      sorry
  · rcases hnonneg with ⟨hbad, hfc_nonneg⟩
    have hfuture_eq : cup2FutureFc n hn4 c' = cup2FutureFc n hn4 c := h.1.2
    have hphi_eq : cup2PhiFull n hn4 c' = cup2PhiFull n hn4 c := h.2.2
    rcases cphi_boundary_non617_nonneg_cases n hn4 hn9 h hchange hnotedge ⟨hbad, hfc_nonneg⟩ with
      h001 | h011 | h200
    · -- Remaining quantitative residue:
      -- mover `0`, local class `P0 : (0,0,1)` under
      -- `FutureFc` equality + `PhiFull` equality.
      let s := cup2Boundary6 n hn4 hn9 c
      have hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
        simpa [s, cup2Boundary6] using h001.2.1
      have hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
        have hs0 : c (cup2BoundaryIdx0 n hn9) = (⟨0, by omega⟩ : Fin 2) := by
          simpa [s] using h001.2.2.1
        exact congrArg Fin.val hs0
      have hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1 := by
        simpa [s, cup2Boundary6] using h001.2.2.2
      have hdst_eq :
          cup2Fc n hn4 c' = cup2Fc n hn4 c := by
        simpa [h001.1] using p0_001_idx0_fc_eq n hn4 hn9 c hcN1 hc0 hc1
      have hb6 :
          cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
            boundarySuccP0 s := by
        simpa [s] using cup2Boundary6_move_eq_boundarySuccP0 n hn4 hn9 c
      have hchange' : (boundarySuccP0 s).encode ≠ s.encode := by
        simpa [cup2BoundaryState, s, h001.1, hb6] using hchange
      have hnotedge' : ¬ sixTupleEdge (boundarySuccP0 s).encode s.encode := by
        simpa [cup2BoundaryState, s, h001.1, hb6] using hnotedge
      have hsrc_split : s.cN2.1 = 2 ∨ s.c2.1 = 2 := by
        simpa [s] using p0_001_cN2_two_or_c2_two s h001.2 hchange' hnotedge'
      have hpost_nonpos :
          ∀ {e : Config (cup2Spec n hn4)},
            cup2TpBadStepFwd n hn4 c' e → cup2Fc n hn4 e ≤ cup2Fc n hn4 c' := by
          intro e hstep
          have hstep' : cup2TpBadStepFwd n hn4
              (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) e := by
            simpa [h001.1] using hstep
          simpa [h001.1] using
            p0_001_postmove_tp_nonpos n hn4 hn9 c hcN1 hc0 hc1 hstep'
      rcases hsrc_split with hcN2 | hc2
      · -- Remaining quantitative residue:
        -- `P0 : (0,0,1)` with `c[n-2] = 2`.
        have hphi_src_lb :
            cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
          exact p0_001_cN2_two_phi_lower n hn4 hn9 c hbad.1 hcN2 hcN1 hc0 hc1
        have hphi_dst_lb :
            cup2Fc n hn4 c' + 1 ≤ cup2PhiFull n hn4 c' := by
          calc
            cup2Fc n hn4 c' + 1 = cup2Fc n hn4 c + 1 := by omega
            _ ≤ cup2PhiFull n hn4 c := hphi_src_lb
            _ = cup2PhiFull n hn4 c' := by simpa using hphi_eq.symm
        have hphi_eq_fc : cup2PhiFull n hn4 c' = cup2Fc n hn4 c' := by
          rw [h001.1]
          exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4
            (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))
            (fun d hreach => p0_001_cN2_two_tpReachable_fc_le_core n hn4 hn9 c
              hcN2 hcN1 hc0 hc1 hreach)
        omega
      · -- Remaining quantitative residue:
        -- `P0 : (0,0,1)` with `c[2] = 2`.
        have hphi_src_lb :
            cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
          exact p0_001_c2_two_phi_lower n hn4 hn9 c hbad.1 hcN1 hc0 hc1 hc2
        have hphi_dst_lb :
            cup2Fc n hn4 c' + 1 ≤ cup2PhiFull n hn4 c' := by
          calc
            cup2Fc n hn4 c' + 1 = cup2Fc n hn4 c + 1 := by omega
            _ ≤ cup2PhiFull n hn4 c := hphi_src_lb
            _ = cup2PhiFull n hn4 c' := by simpa using hphi_eq.symm
        have hphi_eq_fc : cup2PhiFull n hn4 c' = cup2Fc n hn4 c' := by
          rw [h001.1]
          exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4
            (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9))
            (fun d hreach => p0_001_c2_two_tpReachable_fc_le_core n hn4 hn9 c
              hcN1 hc0 hc1 hc2 hchange' hnotedge' hreach)
        omega
    · -- Remaining quantitative residue:
      -- mover `n-1`, local class `Pn1 : (0,1,1)` under
      -- `FutureFc` equality + `PhiFull` equality.
      let s := cup2Boundary6 n hn4 hn9 c
      have hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
        simpa [s, cup2Boundary6] using h011.2.1
      have hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
        simpa [s, cup2Boundary6] using h011.2.2.1
      have hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 1 := by
        simpa [s, cup2Boundary6] using h011.2.2.2
      have hdst_eq :
          cup2Fc n hn4 c' = cup2Fc n hn4 c := by
        simpa [h011.1] using pn1_011_idxN1_fc_eq n hn4 hn9 c hcN2 hcN1 hc0
      have hb6 :
          cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
            boundarySuccPN1 s := by
        simpa [s] using cup2Boundary6_move_eq_boundarySuccPN1 n hn4 hn9 c
      have hchange' : (boundarySuccPN1 s).encode ≠ s.encode := by
        simpa [cup2BoundaryState, s, h011.1, hb6] using hchange
      have hnotedge' : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode := by
        simpa [cup2BoundaryState, s, h011.1, hb6] using hnotedge
      have hc1_cases : s.c1.1 = 1 ∨ s.c1.1 = 2 := by
        simpa [s] using pn1_011_c1_one_or_two s h011.2 hchange' hnotedge'
      have hpost_pos :
          ∀ {e : Config (cup2Spec n hn4)},
            cup2TpBadStepFwd n hn4 c' e →
            cup2Fc n hn4 c' < cup2Fc n hn4 e →
            e = move (cup2System n hn4) c' (cup2BoundaryIdx2 n hn9) ∧
              IsB5Config n hn4 c' (cup2BoundaryIdx2 n hn9) := by
        intro e hstep hlt
        exact pn1_011_postmove_tp_pos_is_idx2_B5 (d := c') (c := c)
          n hn4 hn9 h011.1 hcN2 hcN1 hc0 hstep ⟨hstep.1, hlt⟩
      rcases hc1_cases with hc1_1 | hc1_2
      · have hc2 : s.c2.1 = 2 := pn1_011_c1_one_implies_c2_two s h011.2 hc1_1 hchange' hnotedge'
        have hcN3s : s.cN3.1 = 2 :=
          pn1_011_c1_one_implies_cN3_two s h011.2 hc1_1 hchange' hnotedge'
        have hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2 := by
          simpa [s, cup2Boundary6] using hcN3s
        have hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 1 := by
          simpa [s, cup2Boundary6] using hc1_1
        have hc2' : (c (cup2BoundaryIdx2 n hn9)).1 = 2 := by
          simpa [s, cup2Boundary6] using hc2
        have hphi_src_lb :
            cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
          exact pn1_011_c1_one_phi_lower n hn4 hn9 c hbad.1 hcN2 hcN1 hc0 hc1 hc2'
        have hphi_dst_lb :
            cup2Fc n hn4 c' + 1 ≤ cup2PhiFull n hn4 c' := by
          calc
            cup2Fc n hn4 c' + 1 = cup2Fc n hn4 c + 1 := by omega
            _ ≤ cup2PhiFull n hn4 c := hphi_src_lb
            _ = cup2PhiFull n hn4 c' := by simpa using hphi_eq.symm
        have hphi_eq_fc : cup2PhiFull n hn4 c' = cup2Fc n hn4 c' := by
          rw [h011.1]
          exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4
            (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
            (fun d hreach => pn1_011_c1_one_tpReachable_fc_le n hn4 hn9 c
              hcN3 hcN2 hcN1 hc0 hc1 hc2' hreach)
        omega
      · -- Remaining quantitative residue:
        -- `Pn1 : (0,1,1)` with `c1 = 2`.
        have hc2_cases : s.c2.1 = 0 ∨ s.c2.1 = 1 ∨ s.c2.1 = 2 := by
          omega
        rcases hc2_cases with hc2_0 | hc2_1 | hc2_2
        · have hc2_02 : s.c2.1 = 0 ∨ s.c2.1 = 2 := Or.inl hc2_0
          have hcN3s : s.cN3.1 = 2 :=
            pn1_011_c1_two_c2_zero_or_two_implies_cN3_two s h011.2 hc1_2 hc2_02 hchange' hnotedge'
          have hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2 := by
            simpa [s, cup2Boundary6] using hcN3s
          have hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2 := by
            simpa [s, cup2Boundary6] using hc1_2
          have hc2' : (c (cup2BoundaryIdx2 n hn9)).1 = 0 ∨
              (c (cup2BoundaryIdx2 n hn9)).1 = 2 := by
            simpa [s, cup2Boundary6] using hc2_02
          have hphi_src_lb :
              cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
            exact pn1_011_c1_two_phi_lower n hn4 hn9 c hbad.1 hcN2 hcN1 hc0 hc1
          have hphi_dst_lb :
              cup2Fc n hn4 c' + 1 ≤ cup2PhiFull n hn4 c' := by
            calc
              cup2Fc n hn4 c' + 1 = cup2Fc n hn4 c + 1 := by omega
              _ ≤ cup2PhiFull n hn4 c := hphi_src_lb
              _ = cup2PhiFull n hn4 c' := by simpa using hphi_eq.symm
          have hc'N3 : (c' (cup2BoundaryIdxN3 n hn9)).1 = 2 := by
            rw [h011.1]
            have hne : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdxN3, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN3 n hn9) hne]
            exact hcN3
          have hc'N2 : (c' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
            rw [h011.1]
            have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
            exact hcN2
          have hc'N1 : (c' (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
            rw [h011.1, move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
              cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9,
              right_cup2BoundaryIdxN1 n hn9]
            have htop011 : TTopVal 0 1 1 = 0 := by native_decide
            simpa [hcN2, hcN1, hc0] using htop011
          have hc'0 : (c' (cup2BoundaryIdx0 n hn9)).1 = 1 := by
            rw [h011.1]
            have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
            exact hc0
          have hc'1 : (c' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
            rw [h011.1]
            have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9) hne]
            exact hc1
          have hc'2 : (c' (cup2BoundaryIdx2 n hn9)).1 = 0 ∨
              (c' (cup2BoundaryIdx2 n hn9)).1 = 2 := by
            rw [h011.1]
            have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
            exact hc2'
          have hphi_eq_fc : cup2PhiFull n hn4 c' = cup2Fc n hn4 c' := by
            exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4
              c'
              (fun d hreach => pn1_011_leftFrame_c2_zero_or_two_tpReachable_fc_le n hn4 hn9 c'
                hc'N3 hc'N2 hc'N1 hc'0 hc'1 hc'2 hreach)
          omega
        · -- Remaining quantitative residue:
          -- `Pn1 : (0,1,1)` with `c1 = 2, c2 = 1`.
          have hcN3s : s.cN3.1 = 2 :=
            pn1_011_c1_two_c2_one_implies_cN3_two s h011.2 hc1_2 hc2_1 hchange' hnotedge'
          have hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2 := by
            simpa [s, cup2Boundary6] using hcN3s
          have hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2 := by
            simpa [s, cup2Boundary6] using hc1_2
          have hc2 : (c (cup2BoundaryIdx2 n hn9)).1 = 1 := by
            simpa [s, cup2Boundary6] using hc2_1
          have hc'N3 : (c' (cup2BoundaryIdxN3 n hn9)).1 = 2 := by
            rw [h011.1]
            have hne : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdxN3, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN3 n hn9) hne]
            exact hcN3
          have hc'N2 : (c' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
            rw [h011.1]
            have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
            exact hcN2
          have hc'N1 : (c' (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
            rw [h011.1, move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
              cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9,
              right_cup2BoundaryIdxN1 n hn9]
            have htop011 : TTopVal 0 1 1 = 0 := by native_decide
            simpa [hcN2, hcN1, hc0] using htop011
          have hc'0 : (c' (cup2BoundaryIdx0 n hn9)).1 = 1 := by
            rw [h011.1]
            have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
            exact hc0
          have hc'1 : (c' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
            rw [h011.1]
            have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9) hne]
            exact hc1
          have hc'2 : (c' (cup2BoundaryIdx2 n hn9)).1 = 1 := by
            rw [h011.1]
            have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
            exact hc2
          have hidx3 :
              (c' (cup2Idx3 n hn9)).1 = (c (cup2Idx3 n hn9)).1 := by
            rw [h011.1]
            have hne : cup2Idx3 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2Idx3, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx3 n hn9) hne]
          have hidx4 :
              (c' (cup2Idx4 n hn9)).1 = (c (cup2Idx4 n hn9)).1 := by
            rw [h011.1]
            have hne : cup2Idx4 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2Idx4, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx4 n hn9) hne]
          have hidx5 :
              (c' (cup2Idx5 n hn9)).1 = (c (cup2Idx5 n hn9)).1 := by
            rw [h011.1]
            have hne : cup2Idx5 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2Idx5, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2Idx5 n hn9) hne]
          by_cases hactive : pn1_011_c1_two_c2_one_active n hn4 hn9 c
          · have hphi_src_lb :
                cup2Fc n hn4 c + 2 ≤ cup2PhiFull n hn4 c := by
              exact pn1_011_c1_two_c2_one_active_phi_lower n hn4 hn9 c
                hbad.1 hcN2 hcN1 hc0 hc1 hc2 hactive
            have hphi_dst_lb :
                cup2Fc n hn4 c' + 2 ≤ cup2PhiFull n hn4 c' := by
              calc
                cup2Fc n hn4 c' + 2 = cup2Fc n hn4 c + 2 := by omega
                _ ≤ cup2PhiFull n hn4 c := hphi_src_lb
                _ = cup2PhiFull n hn4 c' := by simpa using hphi_eq.symm
            have hactive' : pn011c1two_c2one_activeWindow n hn4 hn9 c' := by
              have hactive0 : pn011c1two_c2one_activeWindow n hn4 hn9 c := by
                simpa [pn1_011_c1_two_c2_one_active, pn011c1two_c2one_activeWindow] using hactive
              rcases hactive0 with h3 | h00 | h022
              · left
                calc
                  (c' (cup2Idx3 n hn9)).1 = (c (cup2Idx3 n hn9)).1 := hidx3
                  _ = 1 := h3
              · right
                left
                constructor
                · calc
                    (c' (cup2Idx3 n hn9)).1 = (c (cup2Idx3 n hn9)).1 := hidx3
                    _ = 0 := h00.1
                · calc
                    (c' (cup2Idx4 n hn9)).1 = (c (cup2Idx4 n hn9)).1 := hidx4
                    _ = 0 := h00.2
              · right
                right
                constructor
                · calc
                    (c' (cup2Idx3 n hn9)).1 = (c (cup2Idx3 n hn9)).1 := hidx3
                    _ = 0 := h022.1
                constructor
                · calc
                    (c' (cup2Idx4 n hn9)).1 = (c (cup2Idx4 n hn9)).1 := hidx4
                    _ = 2 := h022.2.1
                · calc
                    (c' (cup2Idx5 n hn9)).1 = (c (cup2Idx5 n hn9)).1 := hidx5
                    _ = 2 := h022.2.2
            have hphi_dst_ub :
                cup2PhiFull n hn4 c' ≤ cup2Fc n hn4 c' + 1 := by
              rcases cup2PhiFull_attained n hn4 c' with ⟨d, hreach', hfc_eq⟩
              rw [← hfc_eq]
              exact pn1_011_c1_two_c2_one_tpReachable_fc_le_active n hn4 hn9 c'
                hc'N3 hc'N2 hc'N1 hc'0 hc'1 hc'2 hactive' hreach'
            omega
          · have hphi_src_lb :
                cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
              exact pn1_011_c1_two_phi_lower n hn4 hn9 c hbad.1 hcN2 hcN1 hc0 hc1
            have hphi_dst_lb :
                cup2Fc n hn4 c' + 1 ≤ cup2PhiFull n hn4 c' := by
              calc
                cup2Fc n hn4 c' + 1 = cup2Fc n hn4 c + 1 := by omega
                _ ≤ cup2PhiFull n hn4 c := hphi_src_lb
                _ = cup2PhiFull n hn4 c' := by simpa using hphi_eq.symm
            have hpassive' : ¬ pn011c1two_c2one_activeWindow n hn4 hn9 c' := by
              have hpassive0 : ¬ pn011c1two_c2one_activeWindow n hn4 hn9 c := by
                simpa [pn1_011_c1_two_c2_one_active, pn011c1two_c2one_activeWindow] using hactive
              intro hactive'
              apply hpassive0
              rcases hactive' with h3 | h00 | h022
              · left
                calc
                  (c (cup2Idx3 n hn9)).1 = (c' (cup2Idx3 n hn9)).1 := hidx3.symm
                  _ = 1 := h3
              · right
                left
                constructor
                · calc
                    (c (cup2Idx3 n hn9)).1 = (c' (cup2Idx3 n hn9)).1 := hidx3.symm
                    _ = 0 := h00.1
                · calc
                    (c (cup2Idx4 n hn9)).1 = (c' (cup2Idx4 n hn9)).1 := hidx4.symm
                    _ = 0 := h00.2
              · right
                right
                constructor
                · calc
                    (c (cup2Idx3 n hn9)).1 = (c' (cup2Idx3 n hn9)).1 := hidx3.symm
                    _ = 0 := h022.1
                constructor
                · calc
                    (c (cup2Idx4 n hn9)).1 = (c' (cup2Idx4 n hn9)).1 := hidx4.symm
                    _ = 2 := h022.2.1
                · calc
                    (c (cup2Idx5 n hn9)).1 = (c' (cup2Idx5 n hn9)).1 := hidx5.symm
                    _ = 2 := h022.2.2
            have hphi_eq_fc : cup2PhiFull n hn4 c' = cup2Fc n hn4 c' := by
              exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4
                c'
                (fun d hreach => pn1_011_c1_two_c2_one_tpReachable_fc_le_passive n hn4 hn9 c'
                  hc'N3 hc'N2 hc'N1 hc'0 hc'1 hc'2 hpassive' hreach)
            omega
        · have hc2_02 : s.c2.1 = 0 ∨ s.c2.1 = 2 := Or.inr hc2_2
          have hcN3s : s.cN3.1 = 2 :=
            pn1_011_c1_two_c2_zero_or_two_implies_cN3_two s h011.2 hc1_2 hc2_02 hchange' hnotedge'
          have hcN3 : (c (cup2BoundaryIdxN3 n hn9)).1 = 2 := by
            simpa [s, cup2Boundary6] using hcN3s
          have hc1 : (c (cup2BoundaryIdx1 n hn9)).1 = 2 := by
            simpa [s, cup2Boundary6] using hc1_2
          have hc2' : (c (cup2BoundaryIdx2 n hn9)).1 = 0 ∨
              (c (cup2BoundaryIdx2 n hn9)).1 = 2 := by
            simpa [s, cup2Boundary6] using hc2_02
          have hphi_src_lb :
              cup2Fc n hn4 c + 1 ≤ cup2PhiFull n hn4 c := by
            exact pn1_011_c1_two_phi_lower n hn4 hn9 c hbad.1 hcN2 hcN1 hc0 hc1
          have hphi_dst_lb :
              cup2Fc n hn4 c' + 1 ≤ cup2PhiFull n hn4 c' := by
            calc
              cup2Fc n hn4 c' + 1 = cup2Fc n hn4 c + 1 := by omega
              _ ≤ cup2PhiFull n hn4 c := hphi_src_lb
              _ = cup2PhiFull n hn4 c' := by simpa using hphi_eq.symm
          have hc'N3 : (c' (cup2BoundaryIdxN3 n hn9)).1 = 2 := by
            rw [h011.1]
            have hne : cup2BoundaryIdxN3 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdxN3, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN3 n hn9) hne]
            exact hcN3
          have hc'N2 : (c' (cup2BoundaryIdxN2 n hn9)).1 = 0 := by
            rw [h011.1]
            have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
            exact hcN2
          have hc'N1 : (c' (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
            rw [h011.1, move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
              cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9,
              right_cup2BoundaryIdxN1 n hn9]
            have htop011 : TTopVal 0 1 1 = 0 := by native_decide
            simpa [hcN2, hcN1, hc0] using htop011
          have hc'0 : (c' (cup2BoundaryIdx0 n hn9)).1 = 1 := by
            rw [h011.1]
            have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
            exact hc0
          have hc'1 : (c' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
            rw [h011.1]
            have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9) hne]
            exact hc1
          have hc'2 : (c' (cup2BoundaryIdx2 n hn9)).1 = 0 ∨
              (c' (cup2BoundaryIdx2 n hn9)).1 = 2 := by
            rw [h011.1]
            have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
              intro hEq
              have hval := congrArg Fin.val hEq
              simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
              omega
            rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
            exact hc2'
          have hphi_eq_fc : cup2PhiFull n hn4 c' = cup2Fc n hn4 c' := by
            exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4
              c'
              (fun d hreach => pn1_011_leftFrame_c2_zero_or_two_tpReachable_fc_le n hn4 hn9 c'
                hc'N3 hc'N2 hc'N1 hc'0 hc'1 hc'2 hreach)
          omega
    · -- Remaining quantitative residue:
      -- mover `n-1`, local class `Pn1 : (2,0,0)` under
      -- `FutureFc` equality + `PhiFull` equality.
      let s := cup2Boundary6 n hn4 hn9 c
      have hcN2 : (c (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
        simpa [s, cup2Boundary6] using h200.2.1
      have hcN1 : (c (cup2BoundaryIdxN1 n hn9)).1 = 0 := by
        simpa [s, cup2Boundary6] using h200.2.2.1
      have hc0 : (c (cup2BoundaryIdx0 n hn9)).1 = 0 := by
        have hs0 : c (cup2BoundaryIdx0 n hn9) = (⟨0, by omega⟩ : Fin 2) := by
          simpa [s] using h200.2.2.2
        exact congrArg Fin.val hs0
      have hb6 :
          cup2Boundary6 n hn4 hn9 (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) =
            boundarySuccPN1 s := by
        simpa [s] using cup2Boundary6_move_eq_boundarySuccPN1 n hn4 hn9 c
      have hchange' : (boundarySuccPN1 s).encode ≠ s.encode := by
        simpa [cup2BoundaryState, s, h200.1, hb6] using hchange
      have hnotedge' : ¬ sixTupleEdge (boundarySuccPN1 s).encode s.encode := by
        simpa [cup2BoundaryState, s, h200.1, hb6] using hnotedge
      have hdst_gain :
          cup2Fc n hn4 c' = cup2Fc n hn4 c + 1 := by
        simpa [h200.1] using pn1_200_idxN1_fc_up_one n hn4 hn9 c hcN2 hcN1 hc0
      have hc1_cases : s.c1.1 = 0 ∨ s.c1.1 = 2 := by
        simpa [s] using pn1_200_c1_zero_or_two s h200.2 hchange' hnotedge'
      rcases hc1_cases with hc1_0 | hc1_2
      · -- Remaining quantitative residue:
        -- `Pn1 : (2,0,0)` with `c1 = 0`.
        have hbad0 :=
          pn1_200_c1_zero_idx0_badStep n hn4 hn9 c hbad.1 hcN2 hcN1 hc0
            (by simpa [s, cup2Boundary6] using hc1_0)
        have hsrc_gain :
            cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) =
              cup2Fc n hn4 c + 2 := by
          simpa [s] using
            pn1_200_c1_zero_idx0_fc_gain n hn4 hn9 c h200.2.2.1 h200.2.2.2 hc1_0
        have htp0 : cup2TpPreservingMove n hn4 c (cup2BoundaryIdx0 n hn9) := by
          exact pn1_200_c1_zero_idx0_tpPreserving n hn4 hn9 c hcN1 hc0
            (by simpa [s, cup2Boundary6] using hc1_0)
        have hphi_src_lb :
            cup2Fc n hn4 c + 2 ≤ cup2PhiFull n hn4 c := by
          have hreach0 : cup2TpReachable n hn4 c
              (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) :=
            cup2TpReachable_step n hn4 ⟨hbad0, by simpa [cup2TpPreservingMove] using htp0⟩
          calc
            cup2Fc n hn4 c + 2 =
                cup2Fc n hn4 (move (cup2System n hn4) c (cup2BoundaryIdx0 n hn9)) := by
              omega
            _ ≤ cup2PhiFull n hn4 c := cup2PhiFull_ge_of_tpReachable n hn4 hreach0
        have hphi_dst_lb :
            cup2Fc n hn4 c' + 1 ≤ cup2PhiFull n hn4 c' := by
          calc
            cup2Fc n hn4 c' + 1 = cup2Fc n hn4 c + 2 := by omega
            _ ≤ cup2PhiFull n hn4 c := hphi_src_lb
            _ = cup2PhiFull n hn4 c' := by simpa using hphi_eq.symm
        have hpost_nonpos :
            ∀ {e : Config (cup2Spec n hn4)},
              cup2TpBadStepFwd n hn4 c' e → cup2Fc n hn4 e ≤ cup2Fc n hn4 c' := by
          intro e hstep
          have hstep' : cup2TpBadStepFwd n hn4
              (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) e := by
            simpa [h200.1] using hstep
          simpa [h200.1] using
            pn1_200_c1_zero_postmove_tp_nonpos n hn4 hn9 c hcN2 hcN1 hc0
              (by simpa [s, cup2Boundary6] using hc1_0) hstep'
        -- Use destination-cap to show PhiFull(c') = fc(c'), contradicting hphi_dst_lb.
        have hphi_eq_fc : cup2PhiFull n hn4 c' = cup2Fc n hn4 c' := by
          rw [h200.1]
          exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4
            (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9))
            (fun d hreach => pn1_200_c1_zero_tpReachable_fc_le n hn4 hn9 c
              hcN2 hcN1 hc0 (by simpa [s, cup2Boundary6] using hc1_0) hreach)
        omega
      · -- Remaining quantitative residue:
        -- `Pn1 : (2,0,0)` with `c1 = 2`.
        have hc2 : s.c2.1 = 2 := pn1_200_c1_two_implies_c2_two s h200.2 hc1_2 hchange' hnotedge'
        have hphi_src_lb :
            cup2Fc n hn4 c + 2 ≤ cup2PhiFull n hn4 c := by
          exact pn1_200_c1_two_phi_lower n hn4 hn9 c hbad.1 hcN2 hcN1 hc0
            (by simpa [s, cup2Boundary6] using hc1_2)
            (by simpa [s, cup2Boundary6] using hc2)
        have hphi_dst_lb :
            cup2Fc n hn4 c' + 1 ≤ cup2PhiFull n hn4 c' := by
          calc
            cup2Fc n hn4 c' + 1 = cup2Fc n hn4 c + 2 := by omega
            _ ≤ cup2PhiFull n hn4 c := hphi_src_lb
            _ = cup2PhiFull n hn4 c' := by simpa using hphi_eq.symm
        have hc'N2 : (c' (cup2BoundaryIdxN2 n hn9)).1 = 2 := by
          rw [h200.1]
          have hne : cup2BoundaryIdxN2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdxN2, cup2BoundaryIdxN1] at hval
            omega
          rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdxN2 n hn9) hne]
          exact hcN2
        have hc'N1 : (c' (cup2BoundaryIdxN1 n hn9)).1 = 1 := by
          rw [h200.1, move_apply_self_val n hn4 c (cup2BoundaryIdxN1 n hn9),
            cup2OutVal_boundaryIdxN1 n hn9, left_cup2BoundaryIdxN1 n hn9,
            right_cup2BoundaryIdxN1 n hn9]
          have htop200 : TTopVal 2 0 0 = 1 := by native_decide
          simpa [hcN2, hcN1, hc0] using htop200
        have hc'0 : (c' (cup2BoundaryIdx0 n hn9)).1 = 0 := by
          rw [h200.1]
          have hne : cup2BoundaryIdx0 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx0, cup2BoundaryIdxN1] at hval
            omega
          rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx0 n hn9) hne]
          exact hc0
        have hc'1 : (c' (cup2BoundaryIdx1 n hn9)).1 = 2 := by
          rw [h200.1]
          have hne : cup2BoundaryIdx1 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx1, cup2BoundaryIdxN1] at hval
            omega
          rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx1 n hn9) hne]
          simpa [s, cup2Boundary6] using hc1_2
        have hc'2 : (c' (cup2BoundaryIdx2 n hn9)).1 = 2 := by
          rw [h200.1]
          have hne : cup2BoundaryIdx2 n hn9 ≠ cup2BoundaryIdxN1 n hn9 := by
            intro hEq
            have hval := congrArg Fin.val hEq
            simp [cup2BoundaryIdx2, cup2BoundaryIdxN1] at hval
            omega
          rw [move_apply_ne n hn4 c (cup2BoundaryIdxN1 n hn9) (cup2BoundaryIdx2 n hn9) hne]
          simpa [s, cup2Boundary6] using hc2
        have hpost_nonpos :
            ∀ {e : Config (cup2Spec n hn4)},
              cup2TpBadStepFwd n hn4 c' e → cup2Fc n hn4 e ≤ cup2Fc n hn4 c' := by
          intro e hstep
          have hstep' : cup2TpBadStepFwd n hn4
              (move (cup2System n hn4) c (cup2BoundaryIdxN1 n hn9)) e := by
            simpa [h200.1] using hstep
          simpa [h200.1] using
            pn1_200_c1_two_postmove_tp_nonpos n hn4 hn9 c hcN2 hcN1 hc0
              (by simpa [s, cup2Boundary6] using hc2) hstep'
        have hphi_eq_fc : cup2PhiFull n hn4 c' = cup2Fc n hn4 c' := by
          exact cup2PhiFull_eq_fc_of_tpReachable_fc_le n hn4
            c'
            (fun d hreach => pn1_200_c1_two_tpReachable_fc_le_core n hn4 hn9 c'
              hc'N2 hc'N1 hc'0 hc'1 hc'2 hreach)
        omega

private theorem cphiBoundary_bridge_sixTupleEdge
    (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (h : cup2CPhiStep n hn4 c' c)
    (hchange : cup2BoundaryState n hn4 hn9 c' ≠ cup2BoundaryState n hn4 hn9 c) :
    sixTupleEdge (cup2BoundaryState n hn4 hn9 c')
      (cup2BoundaryState n hn4 hn9 c) := by
  by_contra hnotedge
  exact cphiBoundary_nodrop_non617_impossible n hn4 hn9 h hchange hnotedge

/-! ### Main well-foundedness results -/

theorem cup2CPhiStep_wf (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n) :
    WellFounded (cup2CPhiStep n hn4) := by
  refine cup2CPhiStep_wf_of_sixTupleBridge n hn4 hn9 ?_
  · intro c' c h hchange
    exact cphiBoundary_bridge_sixTupleEdge n hn4 hn9 h hchange

theorem cup2BadConstFutureStep_wf (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n) :
    WellFounded (cup2BadConstFutureStep n hn4) :=
  cup2BadConstFutureStep_wf_of_cphi n hn4 hn9 (cup2CPhiStep_wf n hn4 hn9)

end LeanMn
