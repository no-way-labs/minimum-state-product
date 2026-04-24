/-
  LowerBound/SK/TwistCalculus.lean — Core twist-calculus objects.

  Frozen signature: docs/lean_docs/sk/sk_theorem_package_freeze_2026-04-19.md §0.
  Board-reset slate: docs/lean_docs/sk/sk_twist_calculus_slate_2026-04-19.md §§0, 2′.

  This file is standalone: it defines the algebraic layer used by
  DTNF-forward, CTCL, and the fusion defect classification. It does
  NOT depend on SinkKernel.lean or CloudsTheorem.lean, and it is NOT
  imported by them. Isolated twist-calculus frame.
-/
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sum
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LeanMn.SK.TwistCalculus

/-! ## Twist edges -/

/-- A twist edge is determined by its defect jump `(Δq, Δi)`,
    represented as nearest-representative signed integers. -/
structure TwistEdge where
  Δq : ℤ
  Δi : ℤ
  deriving DecidableEq, Repr

/-- **Twist charge.** The central invariant of CTCL. -/
def twistCharge (e : TwistEdge) : ℤ := e.Δi + 2 * e.Δq

@[simp] theorem twistCharge_def (e : TwistEdge) :
    twistCharge e = e.Δi + 2 * e.Δq := rfl

/-! ## Canonical generators -/

/-- Canonical generators for the twist alphabet:
    `R_k` (stretched retreat), `L_k` (stretched leap), `F_k` (fold). -/
inductive Generator
  | R (k : ℕ)
  | L (k : ℕ)
  | F (k : ℕ)
  deriving DecidableEq, Repr

/-- Embed a generator into a twist edge. -/
def Generator.toEdge : Generator → TwistEdge
  | .R k => ⟨-1,  (3 + (k : ℤ))⟩
  | .L k => ⟨ 2, -(3 + (k : ℤ))⟩
  | .F k => ⟨-2, -(3 + (k : ℤ))⟩

/-! ## Per-generator charges

`χ(R_k) = 1 + k`, `χ(L_k) = 1 − k`, `χ(F_k) = −7 − k`. -/

theorem twistCharge_R (k : ℕ) :
    twistCharge (Generator.R k).toEdge = 1 + (k : ℤ) := by
  simp [Generator.toEdge, twistCharge]
  ring

theorem twistCharge_L (k : ℕ) :
    twistCharge (Generator.L k).toEdge = 1 - (k : ℤ) := by
  simp [Generator.toEdge, twistCharge]
  ring

theorem twistCharge_F (k : ℕ) :
    twistCharge (Generator.F k).toEdge = -7 - (k : ℤ) := by
  simp [Generator.toEdge, twistCharge]
  ring

/-! ## Abstracted twist data for a min closed threading -/

/-- Abstracted view of the six twist edges of a min closed anchored
    threading (at n ≥ 6). We only care about the multiset of twist
    edges; the underlying threading / base cycle structure lives in
    other files. -/
structure TwistData where
  twists : Multiset TwistEdge
  card_six : Multiset.card twists = 6

/-- Total twist charge `Σ_e χ(e)`. -/
def TwistData.totalCharge (t : TwistData) : ℤ :=
  (t.twists.map twistCharge).sum

/-! ## Regime classification -/

/-- Is `e` of the form `R_k` for some `k`? -/
def isRedge (e : TwistEdge) : Prop := ∃ k : ℕ, (Generator.R k).toEdge = e

/-- Is `e` of the form `L_k` for some `k`? -/
def isLedge (e : TwistEdge) : Prop := ∃ k : ℕ, (Generator.L k).toEdge = e

/-- Is `e` of the form `F_k` for some `k`? -/
def isFedge (e : TwistEdge) : Prop := ∃ k : ℕ, (Generator.F k).toEdge = e

/-- An edge is canonical (R or L) if it sits in the dominant alphabet. -/
def isCanonical (e : TwistEdge) : Prop := isRedge e ∨ isLedge e

/-- **Dominant regime:** every twist edge is canonical (R or L). -/
def TwistData.isDominant (t : TwistData) : Prop :=
  ∀ e ∈ t.twists, isCanonical e

/-- **Fold regime:** contains at least one `F_k` edge. -/
def TwistData.isFold (t : TwistData) : Prop :=
  ∃ e ∈ t.twists, isFedge e

/-- **Fusion regime:** contains a non-canonical, non-fold edge. -/
def TwistData.isFusion (t : TwistData) : Prop :=
  (¬ t.isDominant) ∧ (¬ t.isFold)

end LeanMn.SK.TwistCalculus
