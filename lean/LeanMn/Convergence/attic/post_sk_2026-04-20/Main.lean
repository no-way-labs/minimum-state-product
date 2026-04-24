/-
  Convergence/Main.lean — Full convergence proof for CUP-2 system (n ≥ 9)

  Two-level potential:
    Ψ(c) = FutureFc(c) · (R + 1) + rank(c)
  where R = 7n − 30 and rank is the DAG rank within the constant-FutureFc slice.

  Layer 1: FutureFc is non-increasing (PhiFull.lean).
           If FutureFc drops: Ψ drops by ≥ R + 1, dominating any rank change.
  Layer 2: At constant FutureFc: well-founded (ConstLayerDAG.lean).

  Combined: WellFounded (badStep (cup2System n hn) (cup2GoodCycle n hn))
  gives convergence for all n ≥ 9.
-/
import LeanMn.Convergence.ConstLayerDAG

namespace LeanMn

/-! ### General well-foundedness combinator for inner/segment decomposition -/

/-- If `inner` is WF and `segment` is WF, and inner steps compose into segments
    (i.e., an inner step from `a` to `b` followed by a segment from `b` to `c`
    yields a segment from `a` to `c`), then their union is well-founded.

    This is used to combine constant-FutureFc steps (inner) with
    FutureFc-dropping segments (segment). -/
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
    -- ih_seg : ∀ x, segment x a₀ → Acc (inner ∨ segment) x
    -- Build Acc by inner induction, carrying a "lift" function
    -- that composes inner steps to maintain segment reachability to a₀.
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
        -- Inner step: recurse, updating the lift function
        exact ih_inner x h_i (fun y hy => h_lift y (h_compose h_i hy))
      | inr h_s =>
        -- Segment step: use ih_seg with the lifted segment
        exact ih_seg x (h_lift x h_s)

/-! ### FutureFc is preserved along constant-FutureFc chains -/

private lemma futureFc_eq_of_constFutureChain (n : Nat) (hn4 : 4 ≤ n)
    {d c : Config (cup2Spec n hn4)}
    (hchain : Relation.ReflTransGen (cup2BadConstFutureStep n hn4) d c) :
    cup2FutureFc n hn4 d = cup2FutureFc n hn4 c := by
  induction hchain with
  | refl => rfl
  | tail _ hstep ih => rw [ih, hstep.2]

/-! ### Convergence for n ≥ 9 -/

/-- The segment relation: a chain of CF steps followed by a FutureFc-dropping step. -/
private def cup2DropSegment (n : Nat) (hn4 : 4 ≤ n)
    (c' c : Config (cup2Spec n hn4)) : Prop :=
  ∃ d, Relation.ReflTransGen (cup2BadConstFutureStep n hn4) d c ∧
    cup2BadDropFutureStep n hn4 c' d

/-- The segment relation is well-founded: FutureFc strictly drops across each segment. -/
private theorem cup2DropSegment_wf (n : Nat) (hn4 : 4 ≤ n) :
    WellFounded (cup2DropSegment n hn4) := by
  apply WellFounded.mono (InvImage.wf (cup2FutureFc n hn4) Nat.lt_wfRel.wf)
  intro c' c ⟨d, hchain, hdrop⟩
  -- FutureFc(d) = FutureFc(c) (chain preserves FutureFc)
  have heq := futureFc_eq_of_constFutureChain n hn4 hchain
  -- FutureFc(c') < FutureFc(d) (drop step)
  calc cup2FutureFc n hn4 c' < cup2FutureFc n hn4 d := hdrop.2
    _ = cup2FutureFc n hn4 c := heq

/-- An inner (CF) step followed by a segment step yields a segment step.
    This is because the CF step extends the CF chain in the segment. -/
private theorem cf_extends_segment (n : Nat) (hn4 : 4 ≤ n)
    {a b c : Config (cup2Spec n hn4)}
    (h_cf : cup2BadConstFutureStep n hn4 b a)
    (h_seg : cup2DropSegment n hn4 c b) :
    cup2DropSegment n hn4 c a := by
  rcases h_seg with ⟨d, hchain, hdrop⟩
  exact ⟨d, Relation.ReflTransGen.tail hchain h_cf, hdrop⟩

/-- Every bad step is either a CF step or a drop segment (with trivial CF chain). -/
private theorem badStep_cf_or_dropSegment (n : Nat) (hn4 : 4 ≤ n)
    {c' c : Config (cup2Spec n hn4)}
    (hbad : badStep (cup2System n hn4) (cup2GoodCycle n hn4) c' c) :
    cup2BadConstFutureStep n hn4 c' c ∨ cup2DropSegment n hn4 c' c := by
  rcases badStep_futureFc_split n hn4 hbad with hcf | hdrop
  · left; exact hcf
  · right; exact ⟨c, Relation.ReflTransGen.refl, hdrop⟩

/-- Every bad step either drops FutureFc or preserves it.
    Dropping is well-founded (bounded Nat).
    Constant-FutureFc is well-founded (ConstLayerDAG).
    Combined: badStep is well-founded. -/
theorem cup2Converges_ge9 (n : Nat) (hn4 : 4 ≤ n) (hn9 : 9 ≤ n) :
    converges (cup2System n hn4) (cup2GoodCycle n hn4) := by
  unfold converges
  -- badStep ⊆ CF ∪ DropSegment
  -- CF is WF (ConstLayerDAG)
  -- DropSegment is WF (FutureFc drops)
  -- CF step followed by DropSegment yields DropSegment (chain extension)
  -- Combined via wf_of_inner_segment
  have hwf_union := wf_of_inner_segment
    (cup2BadConstFutureStep_wf n hn4 hn9)
    (cup2DropSegment_wf n hn4)
    (cf_extends_segment n hn4)
  exact WellFounded.mono hwf_union (fun {c' c} hbad =>
    badStep_cf_or_dropSegment n hn4 hbad)

end LeanMn
