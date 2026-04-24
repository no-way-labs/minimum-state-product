/-
  ProcMinGap.lean — Entry conflict via processor-firing minimum gap

  For 3 consecutive binary {i, right i, right(right i)}, let p = right i.
  Among consecutive firing pairs of p, pick minimum gap b - a ≥ 2.
  Entry conflict at p: step a+1 (non-mover) vs step b (mover), if both
  binary neighbors fire even times in [a+1, b).
-/
import LeanMn.LowerBound.EntryConflict.ContextBridge

namespace LeanMn

variable {sys : System}

/-! ### Min-gap consecutive firing pair -/

/-- A consecutive firing pair of p with globally minimum gap. -/
structure MinFiringGap {sys : System} (gc : GoodCycle sys) (p : Fin sys.rs.n) where
  a : Fin gc.configs.length
  b : Fin gc.configs.length
  a_fires : gc.moverAt a = p
  b_fires : gc.moverAt b = p
  a_lt_b : a.val < b.val
  no_fire_between : ∀ k : Fin gc.configs.length,
    a.val < k.val → k.val < b.val → gc.moverAt k ≠ p
  is_min_gap : ∀ (a' b' : Fin gc.configs.length),
    gc.moverAt a' = p → gc.moverAt b' = p → a'.val < b'.val →
    (∀ k : Fin gc.configs.length, a'.val < k.val → k.val < b'.val → gc.moverAt k ≠ p) →
    b.val - a.val ≤ b'.val - a'.val

/-! ### Value preservation -/

/-- p's value at step a+1 equals its value at step b (p doesn't fire between). -/
theorem MinFiringGap.proc_value_preserved
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (ha1 : mg.a.val + 1 < gc.configs.length) :
    (gc.configs.get ⟨mg.a.val + 1, ha1⟩) p = (gc.configs.get mg.b) p := by
  have hab : mg.a.val + 1 ≤ mg.b.val := by
    have := mg.a_lt_b; omega
  exact configVal_eq_of_noFire_between gc p (mg.a.val + 1) mg.b.val
    hab mg.b.isLt
    (fun k hk1 hk2 => by
      have : mg.a.val < k.val := by omega
      exact mg.no_fire_between k this hk2)

/-- The mover at step a+1 is in {left p, p, right p}. -/
theorem MinFiringGap.next_mover_local
    {gc : GoodCycle sys} {p : Fin sys.rs.n} (mg : MinFiringGap gc p) :
    gc.moverAt (nextIndex gc.configs mg.a) = left p ∨
    gc.moverAt (nextIndex gc.configs mg.a) = p ∨
    gc.moverAt (nextIndex gc.configs mg.a) = right p := by
  have h := gc.next_mover_is_local mg.a
  rwa [mg.a_fires] at h

/-- With gap ≥ 2, the mover at step a+1 is NOT p. -/
theorem MinFiringGap.next_mover_ne_p
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (hgap2 : mg.b.val - mg.a.val ≥ 2) :
    gc.moverAt (nextIndex gc.configs mg.a) ≠ p := by
  intro hmov
  have ha1_lt : mg.a.val + 1 < gc.configs.length := by
    have := mg.b.isLt; omega
  have hnext_val : (nextIndex gc.configs mg.a).val = mg.a.val + 1 := by
    simp [nextIndex, Nat.mod_eq_of_lt ha1_lt]
  have hak : mg.a.val < (nextIndex gc.configs mg.a).val := by omega
  have hkb : (nextIndex gc.configs mg.a).val < mg.b.val := by omega
  exact mg.no_fire_between (nextIndex gc.configs mg.a) hak hkb hmov

/-- With gap ≥ 2, the mover at step a+1 is left p or right p. -/
theorem MinFiringGap.next_mover_left_or_right
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p) (hgap2 : mg.b.val - mg.a.val ≥ 2) :
    gc.moverAt (nextIndex gc.configs mg.a) = left p ∨
    gc.moverAt (nextIndex gc.configs mg.a) = right p := by
  rcases mg.next_mover_local with h | h | h
  · exact Or.inl h
  · exact absurd h (mg.next_mover_ne_p hgap2)
  · exact Or.inr h

/-! ### Entry conflict construction -/

/-- Entry conflict at p: step a+1 (non-mover) vs step b (mover). -/
theorem MinFiringGap.entry_conflict_of_neighbors_preserved
    {gc : GoodCycle sys} {p : Fin sys.rs.n}
    (mg : MinFiringGap gc p)
    (ha1 : mg.a.val + 1 < gc.configs.length)
    (_hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hL : (gc.configs.get ⟨mg.a.val + 1, ha1⟩) (left p) =
          (gc.configs.get mg.b) (left p))
    (hR : (gc.configs.get ⟨mg.a.val + 1, ha1⟩) (right p) =
          (gc.configs.get mg.b) (right p)) :
    hasEntryConflict gc := by
  have hS := mg.proc_value_preserved ha1
  have hak : mg.a.val < mg.a.val + 1 := Nat.lt_succ_self _
  have hkb : mg.a.val + 1 < mg.b.val := by omega
  have hmov_ne : gc.moverAt ⟨mg.a.val + 1, ha1⟩ ≠ p :=
    mg.no_fire_between ⟨mg.a.val + 1, ha1⟩ hak hkb
  exact ⟨mg.b, ⟨mg.a.val + 1, ha1⟩, p,
    mg.b_fires, hmov_ne,
    hL.symm, hS.symm, hR.symm⟩

/-! ### Binary value return -/

/-- A binary processor whose prefix fire count parity is the same at
    two times has the same value at both times. -/
theorem binary_config_eq_of_prefix_parity
    (gc : GoodCycle sys) (q : Fin sys.rs.n) (hbin : isBinary sys.rs q)
    {a b : Nat} (ha : a < gc.configs.length) (hb : b < gc.configs.length)
    (hparity : gc.prefixFireCount q a % 2 = gc.prefixFireCount q b % 2) :
    (gc.configs.get ⟨a, ha⟩) q = (gc.configs.get ⟨b, hb⟩) q := by
  have hfa := gc.binary_config_val_eq_initial_add_prefix q hbin ha
  have hfb := gc.binary_config_val_eq_initial_add_prefix q hbin hb
  apply Fin.ext
  rw [hfa, hfb]
  omega

/-! ### Assembly: 3 consecutive binary → entry conflict -/

/-- Top-level: 3 consecutive binary → entry conflict, given a min-gap pair
    with gap ≥ 2 and even neighbor fires. -/
theorem procMinGap_hasEntryConflict
    {gc : GoodCycle sys} {i : Fin sys.rs.n}
    (h3bin : threeConsecutiveBinary sys.rs i)
    (mg : MinFiringGap gc (right i))
    (hgap2 : mg.b.val - mg.a.val ≥ 2)
    (hL_parity : gc.prefixFireCount i (mg.a.val + 1) % 2 =
                 gc.prefixFireCount i mg.b.val % 2)
    (hR_parity : gc.prefixFireCount (right (right i)) (mg.a.val + 1) % 2 =
                 gc.prefixFireCount (right (right i)) mg.b.val % 2) :
    hasEntryConflict gc := by
  have ha1_lt : mg.a.val + 1 < gc.configs.length := by
    have := mg.b.isLt; omega
  -- Binary neighbors return when prefix fire parity matches
  have hL := binary_config_eq_of_prefix_parity gc i h3bin.1
    ha1_lt mg.b.isLt hL_parity
  have hR := binary_config_eq_of_prefix_parity gc (right (right i)) h3bin.2.2
    ha1_lt mg.b.isLt hR_parity
  -- left(right i) = i
  have hli : left (right i) = i := by
    simp [left_right_eq_self]
  -- Rewrite hL from i to left(right i)
  have hL' : (gc.configs.get ⟨mg.a.val + 1, ha1_lt⟩) (left (right i)) =
             (gc.configs.get mg.b) (left (right i)) := by
    rw [hli]; exact hL
  exact mg.entry_conflict_of_neighbors_preserved ha1_lt hgap2 hL' hR

end LeanMn
