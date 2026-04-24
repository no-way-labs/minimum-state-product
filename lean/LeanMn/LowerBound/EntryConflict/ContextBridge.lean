/-
  ContextBridge.lean — Context preservation between paired edge crossings

  Bridge lemma: between adjacent opposite-direction crossings of edge
  (p, right p), any processor q that does NOT fire has its configuration
  value preserved.  Combined with the paired crossing lemma this lets us
  deduce that specific processors see identical (L, S, R) contexts at
  the CW non-mover step and the CCW mover step.
-/
import LeanMn.LowerBound.EntryConflict.PairedCrossing

namespace LeanMn

variable {sys : System}

/-! ### Value preservation when a processor does not fire -/

private theorem nextIndex_eq_natSucc'
    (gc : GoodCycle sys) {m : Nat} (hm : m + 1 < gc.configs.length) :
    nextIndex gc.configs ⟨m, lt_trans (Nat.lt_succ_self _) hm⟩ = ⟨m + 1, hm⟩ := by
  apply Fin.ext
  simp [nextIndex, Nat.mod_eq_of_lt hm]

/-- If processor `q` is not the mover at any step in `[a, b)`, then its
    configuration value at step `a` equals its value at step `b`.
    This is the public version of the induction used in the palindromic
    argument, made available for the paired-crossing bridge. -/
theorem configVal_eq_of_noFire_between
    (gc : GoodCycle sys) (q : Fin sys.rs.n) (a b : Nat)
    (hab : a ≤ b) (hb : b < gc.configs.length)
    (hno : ∀ k : Fin gc.configs.length,
      a ≤ k.val → k.val < b → gc.moverAt k ≠ q) :
    (gc.configs.get ⟨a, lt_of_le_of_lt hab hb⟩) q =
      (gc.configs.get ⟨b, hb⟩) q := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    have hb_lt : b < gc.configs.length := by omega
    have hprev :
        (gc.configs.get ⟨a, lt_of_le_of_lt hab hb_lt⟩) q =
          (gc.configs.get ⟨b, hb_lt⟩) q := by
      simpa using ih hb_lt (fun k hk1 hk2 => hno k hk1 (by omega))
    have hstay :
        (gc.configs.get ⟨b, hb_lt⟩) q =
          (gc.configs.get ⟨b + 1, hb⟩) q := by
      have hq_ne : q ≠ gc.moverAt ⟨b, hb_lt⟩ := by
        intro hq
        exact hno ⟨b, hb_lt⟩ hab (by simp [Nat.lt_succ_self b]) hq.symm
      have hstep := gc.state_eq_of_ne_moverAt ⟨b, hb_lt⟩ q hq_ne
      simpa [nextIndex_eq_natSucc' gc hb] using hstep.symm
    exact hprev.trans hstay

/-- **Context Bridge Lemma.** If processor `q` does not fire at any step
    in `[a, b)`, its configuration value at step `a` equals its value at
    step `b`.  This is the `Fin`-indexed wrapper around
    `configVal_eq_of_noFire_between`, designed for use with the output of
    `exists_paired_edge_crossing`.

    Typical application: for the entry conflict at `right p` between
    paired crossings at edge (p, right p), we need L = value at `p`,
    S = value at `right p`, R = value at `right (right p)` to match at
    steps `a` and `b`.  Each follows from this lemma once the relevant
    processor is shown not to fire in the interval. -/
theorem context_preserved_between_paired_crossings
    (gc : GoodCycle sys)
    (a b : Fin gc.configs.length)
    (hlt : a.val < b.val)
    (q : Fin sys.rs.n)
    (hno : ∀ k : Fin gc.configs.length,
      a.val ≤ k.val → k.val < b.val → gc.moverAt k ≠ q) :
    (gc.configs.get a) q = (gc.configs.get b) q := by
  have := configVal_eq_of_noFire_between gc q a.val b.val
    (Nat.le_of_lt hlt) b.isLt hno
  simpa using this

/-- **Local Context Bridge.** If none of `left q`, `q`, `right q` fires
    in `[a, b)` between paired crossings, then the full (L, S, R) context
    at `q` is preserved from step `a` to step `b`. -/
theorem localContext_preserved_between_paired_crossings
    (gc : GoodCycle sys)
    (a b : Fin gc.configs.length)
    (hlt : a.val < b.val)
    (q : Fin sys.rs.n)
    (hno : ∀ k : Fin gc.configs.length,
      a.val ≤ k.val → k.val < b.val →
        gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ q ∧ gc.moverAt k ≠ right q) :
    (gc.configs.get a) (left q) = (gc.configs.get b) (left q) ∧
    (gc.configs.get a) q = (gc.configs.get b) q ∧
    (gc.configs.get a) (right q) = (gc.configs.get b) (right q) :=
  ⟨context_preserved_between_paired_crossings gc a b hlt (left q)
      (fun k h1 h2 => (hno k h1 h2).1),
   context_preserved_between_paired_crossings gc a b hlt q
      (fun k h1 h2 => (hno k h1 h2).2.1),
   context_preserved_between_paired_crossings gc a b hlt (right q)
      (fun k h1 h2 => (hno k h1 h2).2.2)⟩

end LeanMn
