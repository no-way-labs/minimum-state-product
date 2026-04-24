/-
  LowerBound/SK/Witness.lean — Witness wavefront empty SK (T4)

  Targets doc reference:
    docs/lean_docs/sk/sk_invariant_lean_targets_2026-04-14.md §2, §3 (T4)

  T4 handles the witness regime (k = 2 binary, n ≥ 9) where the tail
  skeleton theorem T2 does not apply because the system has only 2
  binary positions. The wavefront has a closed-form structure and the
  SK is empty by analytical induction on n.
-/
import LeanMn.LowerBound.SK.SinkKernel

namespace LeanMn.SK

/-- The CLB witness state vector at `n ≥ 9`: `ms = (2, 3, 3, …, 3, 2)`
    with binary endpoints and ternary interior. -/
def witnessMs (n : Nat) (_hn : 9 ≤ n) : Fin n → Nat :=
  fun i => if i.val = 0 ∨ i.val + 1 = n then 2 else 3

/-- The CLB witness ring spec for `n ≥ 9`. -/
def witnessSpec (n : Nat) (hn : 9 ≤ n) : RingSpec where
  n := n
  n_ge_4 := by omega
  m := witnessMs n hn
  m_pos := by
    intro i
    unfold witnessMs
    by_cases h : i.val = 0 ∨ i.val + 1 = n <;> simp [h]

/-- The 3-phase wavefront good cycle for the CLB witness at `n ≥ 9`.

    Has length `3n - 2` and per-position value distribution given by
    the closed form (targets doc §2):
    ```
    L_0(j) = n
    L_1(j) = 2(n - 2 - j)
    L_2(j) = 2(j + 1)
    ```
    for ternary positions `j = 0, …, n - 3`.

    Constructed symbolically — **not** as an enumerated list of configs
    (per §0.5 rule 2). The construction proves the cycle invariants
    (`unique_privileged`, `closed`, `distinct`, `fair`) from the
    closed form rather than verifying them per-config. -/
def witnessGoodCycle (n : Nat) (hn : 9 ≤ n)
    (sys : System) (hsys : sys.rs = witnessSpec n hn) :
    GoodCycle sys := by
  sorry

/-- T4: For the CLB witness at `n ≥ 9`, the sink-kernel of the
    wavefront good cycle is empty.

    Proof (see targets doc §3 T4): parametric induction on n.

    - **Base case n = 9**: proved analytically by case analysis on
      the wavefront's ternary-strip structure. **NOT** by `#eval`
      or `decide` on the cycle data — that would be the §0.5 rule 2
      trap. The closed-form wavefront table from §2 is the analytical
      object the proof works on.

    - **Step n → n+1**: the wavefront extends by one ternary position
      with value distribution inherited from the closed form. Show
      that every removal in the n+1 case either tracks a removal in
      the n case or is killed by the new column.

    Estimate: 400–700 lines. -/
theorem witness_wavefront_SK_empty
    (n : Nat) (hn : 9 ≤ n)
    (sys : System) (hsys : sys.rs = witnessSpec n hn) :
    SK (witnessGoodCycle n hn sys hsys) = ∅ := by
  sorry

end LeanMn.SK
