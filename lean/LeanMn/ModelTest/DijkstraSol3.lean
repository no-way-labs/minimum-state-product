/-
  ModelTest/DijkstraSol3.lean — Dijkstra's 1974 Solution 3 is valid in our model

  MODEL CORRECTNESS TEST: Dijkstra's original self-stabilizing token ring
  (1974) is accepted as `valid` by our formalization, confirming the model
  faithfully captures the standard central daemon model.

  Dijkstra's Solution 3 (n processors, K states each):
    Processor 0: if c[0] = c[n-1] then c[0] := (c[0] + 1) mod K
    Processor i (i > 0): if c[i] ≠ c[i-1] then c[i] := c[i-1]

  Unidirectional: ignores right neighbor. Instantiated at n=4, K=3.

  Reference: E.W. Dijkstra, "Self-stabilizing systems in spite of
  distributed control," CACM 17(11):643-644, 1974.
-/
import LeanMn.Dijkstra

namespace LeanMn

/-! ### System definition -/

private def dijk3M (_i : Fin 4) : Nat := 3

def dijk3Spec : RingSpec where
  n := 4
  n_ge_4 := by omega
  m := dijk3M
  m_pos := by intro i; simp [dijk3M]

-- Transition: explicit match table (same pattern as SmallN/Defs.lean)
-- P0: if L = S then (S+1)%3 else S
-- P1,P2,P3: if S ≠ L then L else S
-- R argument is ignored (unidirectional).
-- Transition function using Nat-level matching (same style as SmallN/Defs.lean).
-- P0: if L.val = S.val then (S.val + 1) % 3 else S.val
-- Pi (i>0): if S.val ≠ L.val then L.val else S.val
private def dijk3Raw (proc L S _R : Nat) : Nat :=
  match proc with
  | 0 => if L == S then (S + 1) % 3 else S
  | _ => if S != L then L else S

private theorem dijk3Raw_lt (i : Fin 4) (L : Fin (dijk3Spec.m (left i)))
    (S : Fin (dijk3Spec.m i)) (R : Fin (dijk3Spec.m (right i))) :
    dijk3Raw i.val L.val S.val R.val < dijk3Spec.m i := by
  fin_cases i <;> fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp_all [dijk3Raw, dijk3Spec, dijk3M]

private def dijk3F : TransFn dijk3Spec := by
  intro i L S R
  exact ⟨dijk3Raw i.val L.val S.val R.val, dijk3Raw_lt i L S R⟩

def dijk3System : System where
  rs := dijk3Spec
  f := dijk3F

/-! ### Good cycle (3n = 12 configs) -/

-- Encode: code = c0 + 3*c1 + 9*c2 + 27*c3
private def dijk3Decode (code : Nat) : Config dijk3Spec :=
  have h : ∀ k, k % 3 < 3 := fun k => Nat.mod_lt k (by omega)
  fun | ⟨0, _⟩ => ⟨(code / 1) % 3, h _⟩
      | ⟨1, _⟩ => ⟨(code / 3) % 3, h _⟩
      | ⟨2, _⟩ => ⟨(code / 9) % 3, h _⟩
      | ⟨3, _⟩ => ⟨(code / 27) % 3, h _⟩

private def dijk3Codes : List Nat :=
  [0, 1, 4, 13, 40, 41, 44, 53, 80, 78, 72, 54]

private def dijk3Configs : List (Config dijk3Spec) :=
  dijk3Codes.map dijk3Decode

private theorem dijk3_nonempty : dijk3Configs ≠ [] := by
  simp [dijk3Configs, dijk3Codes]

private theorem dijk3_unique_priv_aux :
    ∀ c ∈ dijk3Configs,
      ∃ i, privileged dijk3System c i ∧
        ∀ j, privileged dijk3System c j → j = i := by
  native_decide

private theorem dijk3_unique_priv :
    ∀ c ∈ dijk3Configs, ∃! i, privileged dijk3System c i := by
  intro c hc
  simpa [ExistsUnique] using dijk3_unique_priv_aux c hc

private theorem dijk3_closed :
    ∀ k : Fin dijk3Configs.length,
      ∃ i, privileged dijk3System (dijk3Configs.get k) i ∧
        dijk3Configs.get (nextIndex dijk3Configs k) =
          move dijk3System (dijk3Configs.get k) i := by
  native_decide

private theorem dijk3_distinct :
    ∀ j₁ j₂ : Fin dijk3Configs.length,
      dijk3Configs.get j₁ = dijk3Configs.get j₂ → j₁ = j₂ := by
  native_decide

private def dijk3GoodCycle : GoodCycle dijk3System where
  configs := dijk3Configs
  nonempty := dijk3_nonempty
  unique_privileged := dijk3_unique_priv
  closed := dijk3_closed
  distinct := dijk3_distinct

/-! ### Convergence -/

private def dijk3Rank (c : Config dijk3Spec) : Nat :=
  let code := (c ⟨0, by decide⟩).val + 3 * (c ⟨1, by decide⟩).val +
    9 * (c ⟨2, by decide⟩).val + 27 * (c ⟨3, by decide⟩).val
  match code with
  | 2 => 3 | 3 => 12 | 5 => 4 | 6 => 8 | 7 => 5 | 8 => 2
  | 9 => 10 | 10 => 9 | 11 => 6 | 12 => 11 | 14 => 3 | 15 => 14
  | 16 => 13 | 17 => 2 | 18 => 6 | 19 => 5 | 20 => 13 | 21 => 12
  | 22 => 3 | 23 => 9 | 24 => 7 | 25 => 4 | 26 => 1 | 27 => 1
  | 28 => 7 | 29 => 4 | 30 => 13 | 31 => 6 | 32 => 5 | 33 => 9
  | 34 => 12 | 35 => 3 | 36 => 2 | 37 => 8 | 38 => 5 | 39 => 3
  | 42 => 4 | 43 => 12 | 45 => 2 | 46 => 14 | 47 => 13
  | 48 => 6 | 49 => 10 | 50 => 9 | 51 => 3 | 52 => 11
  | 55 => 3 | 56 => 11 | 57 => 13 | 58 => 2 | 59 => 14
  | 60 => 9 | 61 => 6 | 62 => 10 | 63 => 3 | 64 => 9 | 65 => 12
  | 66 => 4 | 67 => 1 | 68 => 7 | 69 => 5 | 70 => 13 | 71 => 6
  | 73 => 4 | 74 => 12 | 75 => 5 | 76 => 2 | 77 => 8 | 79 => 3
  | _ => 0  -- good cycle configs map to 0

private theorem dijk3Rank_decreases_from
    (c : Config dijk3Spec)
    (hbad : c ∉ dijk3Configs)
    (i : Fin 4)
    (hpriv : privileged dijk3System c i)
    (hnext : move dijk3System c i ∉ dijk3Configs) :
    dijk3Rank (move dijk3System c i) < dijk3Rank c := by
  native_decide +revert

private theorem dijk3Rank_decreases :
    ∀ {c' c : Config dijk3Spec},
      badStep dijk3System dijk3GoodCycle c' c →
        dijk3Rank c' < dijk3Rank c := by
  intro c' c hstep
  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩
  exact dijk3Rank_decreases_from c hbad i hpriv hnext

private theorem dijk3_converges : converges dijk3System dijk3GoodCycle := by
  let f : Config dijk3Spec → Nat := dijk3Rank
  let r : Config dijk3Spec → Config dijk3Spec → Prop := InvImage Nat.lt f
  have hwf : WellFounded r := InvImage.wf f Nat.lt_wfRel.wf
  exact Subrelation.wf (fun hstep => dijk3Rank_decreases hstep) hwf

/-! ### Main theorem -/

/-- **Dijkstra's 1974 Solution 3 is valid in our model.**
    This confirms the model correctly captures the central daemon
    self-stabilization framework. -/
theorem dijk3_valid : valid dijk3System :=
  ⟨dijk3GoodCycle, dijk3_converges⟩

/-- State product = 81 = 3^4 (all ternary, n=4). -/
theorem dijk3_stateProduct : stateProduct dijk3Spec = 81 := by
  native_decide

end LeanMn
