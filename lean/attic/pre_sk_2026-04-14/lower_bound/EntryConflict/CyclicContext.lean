/-
  CyclicContext.lean — Cyclic context preservation helpers

  These lemmas are the wrap-aware analogues of the linear `ContextBridge` /
  `BinaryParity` utilities. They are intended for the small set of lower-bound
  arguments where the useful EC witness crosses the cycle boundary.
-/
import LeanMn.LowerBound.EntryConflict.PhaseExtractionBase
import LeanMn.LowerBound.EntryConflict.BinaryParity

namespace LeanMn

variable {sys : System}

/-- If processor `q` does not fire on the cyclic interval `[b, L) ∪ [0, a)`,
then its configuration value at step `b` equals its value at step `a`. -/
theorem configVal_eq_of_cyclic_noFire
    (gc : GoodCycle sys) (q : Fin sys.rs.n) (a b : Nat)
    (ha : a < gc.configs.length) (hb : b < gc.configs.length)
    (hab : a ≤ b)
    (hnofire_tail : ∀ k : Fin gc.configs.length,
      b ≤ k.val → gc.moverAt k ≠ q)
    (hnofire_head : ∀ k : Fin gc.configs.length,
      k.val < a → gc.moverAt k ≠ q) :
    (gc.configs.get ⟨b, hb⟩) q = (gc.configs.get ⟨a, ha⟩) q := by
  have hL_pos := gc.configs_length_pos
  have hL1_lt : gc.configs.length - 1 < gc.configs.length := by omega
  have hb_le_L1 : b ≤ gc.configs.length - 1 := by omega
  have h_tail : (gc.configs.get ⟨b, hb⟩) q =
      (gc.configs.get ⟨gc.configs.length - 1, hL1_lt⟩) q := by
    by_cases hb_last : b = gc.configs.length - 1
    · rw [show (⟨b, hb⟩ : Fin gc.configs.length) =
        ⟨gc.configs.length - 1, hL1_lt⟩ from Fin.ext hb_last]
    · exact configVal_eq_of_noFire_between gc q b (gc.configs.length - 1)
        hb_le_L1 hL1_lt (fun k hk1 hk2 => hnofire_tail k (by omega))
  have hq_ne_last : q ≠ gc.moverAt ⟨gc.configs.length - 1, hL1_lt⟩ :=
    fun heq => hnofire_tail ⟨gc.configs.length - 1, hL1_lt⟩ hb_le_L1 heq.symm
  have h_wrap_idx :
      nextIndex gc.configs ⟨gc.configs.length - 1, hL1_lt⟩ = ⟨0, hL_pos⟩ :=
    Fin.ext (by
      simp [nextIndex, show gc.configs.length - 1 + 1 = gc.configs.length by omega,
        Nat.mod_self])
  have h_wrap : (gc.configs.get ⟨gc.configs.length - 1, hL1_lt⟩) q =
      (gc.configs.get ⟨0, hL_pos⟩) q := by
    have := gc.state_eq_of_ne_moverAt ⟨gc.configs.length - 1, hL1_lt⟩ q hq_ne_last
    rw [h_wrap_idx] at this
    exact this.symm
  have h_head : (gc.configs.get ⟨0, hL_pos⟩) q =
      (gc.configs.get ⟨a, ha⟩) q := by
    by_cases ha0 : a = 0
    · rw [show (⟨0, hL_pos⟩ : Fin gc.configs.length) = ⟨a, ha⟩ from Fin.ext ha0.symm]
    · exact configVal_eq_of_noFire_between gc q 0 a (Nat.zero_le _) ha
        (fun k _ hk2 => hnofire_head k hk2)
  exact h_tail.trans (h_wrap.trans h_head)

/-- Binary parity across the cycle boundary: if a binary processor fires an
even number of times on the cyclic interval `[b, L) ∪ [0, a)`, then its value
at step `b` equals its value at step `a`. -/
theorem binary_config_eq_of_cyclic_even_fire
    (gc : GoodCycle sys) (p : Fin sys.rs.n) (hbin : sys.rs.m p = 2)
    (a b : Nat) (ha : a < gc.configs.length) (hb : b < gc.configs.length)
    (hab : a ≤ b)
    (heven : Even (gc.intervalFireCount p b gc.configs.length +
      gc.intervalFireCount p 0 a)) :
    (gc.configs.get ⟨b, hb⟩) p = (gc.configs.get ⟨a, ha⟩) p := by
  have hfc_even : Even (gc.fireCount p) := gc.binary_fireCount_even p hbin
  have hfull :
      gc.fireCount p =
        gc.intervalFireCount p 0 a +
        gc.intervalFireCount p a b +
        gc.intervalFireCount p b gc.configs.length := by
    have hfc_full := fireCount_eq_intervalFireCount_full gc p
    have h1 := intervalFireCount_split gc p (Nat.zero_le a)
      (show a ≤ gc.configs.length from Nat.le_of_lt ha)
    have h2 := intervalFireCount_split gc p hab
      (show b ≤ gc.configs.length from Nat.le_of_lt hb)
    rw [hfc_full, h1, h2]
    ring
  have hmid_even : Even (gc.intervalFireCount p a b) := by
    obtain ⟨u, hu⟩ := hfc_even
    obtain ⟨v, hv⟩ := heven
    rw [hfull] at hu
    have : gc.intervalFireCount p a b % 2 = 0 := by
      omega
    exact Nat.even_iff.mpr this
  have hcfg :=
    binary_config_eq_of_even_intervalFireCount gc p hbin a b hab hb hmid_even
  exact hcfg.symm

/-- If both binary neighbors have even cyclic wrap contribution between the
last linear `t`-fire `s_max` and the first one `s_min`, and the wrap gap is
nonempty, then the triple at `t` matches between the first step after `s_max`
and the mover step `s_min`, yielding EC at `t`. -/
theorem cyclic_wrap_bothEven_ec
    (gc : GoodCycle sys) (t : Fin sys.rs.n)
    (hbL : sys.rs.m (left t) = 2) (hbR : sys.rs.m (right t) = 2)
    (s_min s_max : Fin gc.configs.length)
    (hs_lt : s_min.val < s_max.val)
    (hs_min_fire : gc.moverAt s_min = t)
    (hno_t_before : ∀ k : Fin gc.configs.length, k.val < s_min.val → gc.moverAt k ≠ t)
    (hno_t_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ t)
    (hwrapL_even : Even (gc.intervalFireCount (left t) 0 s_min.val +
      gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length))
    (hwrapR_even : Even (gc.intervalFireCount (right t) 0 s_min.val +
      gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length))
    (hwrap_nonempty : nextIndex gc.configs s_max ≠ s_min) :
    hasEntryConflict gc := by
  have hL_pos := gc.configs_length_pos
  by_cases hlast : s_max.val + 1 = gc.configs.length
  · have hw0 : nextIndex gc.configs s_max = ⟨0, hL_pos⟩ := by
      apply Fin.ext
      simp [nextIndex, hlast]
    have hs_min_ne0 : s_min ≠ ⟨0, hL_pos⟩ := by
      intro hs0
      exact hwrap_nonempty (by simpa [hw0] using hs0.symm)
    have hs_min_pos : 0 < s_min.val := by
      by_contra h
      have hs_min_val0 : s_min.val = 0 := by omega
      have hs0 : s_min = ⟨0, hL_pos⟩ := by
        exact Fin.ext hs_min_val0
      exact hs_min_ne0 hs0
    have hzero_nonmover : gc.moverAt ⟨0, hL_pos⟩ ≠ t :=
      hno_t_before ⟨0, hL_pos⟩ hs_min_pos
    have htailL0 :
        gc.intervalFireCount (left t) (s_max.val + 1) gc.configs.length = 0 := by
      rw [hlast]
      simp [GoodCycle.intervalFireCount]
    have htailR0 :
        gc.intervalFireCount (right t) (s_max.val + 1) gc.configs.length = 0 := by
      rw [hlast]
      simp [GoodCycle.intervalFireCount]
    have hheadL_even : Even (gc.intervalFireCount (left t) 0 s_min.val) := by
      simpa [htailL0] using hwrapL_even
    have hheadR_even : Even (gc.intervalFireCount (right t) 0 s_min.val) := by
      simpa [htailR0] using hwrapR_even
    have hctx_L :
        (gc.configs.get s_min) (left t) = (gc.configs.get ⟨0, hL_pos⟩) (left t) := by
      exact (binary_config_eq_of_even_intervalFireCount gc (left t) hbL 0 s_min.val
        (Nat.zero_le _) s_min.isLt hheadL_even).symm
    have hctx_t :
        (gc.configs.get s_min) t = (gc.configs.get ⟨0, hL_pos⟩) t := by
      exact (configVal_eq_of_noFire_between gc t 0 s_min.val
        (Nat.zero_le _) s_min.isLt (fun k _ hk2 => hno_t_before k hk2)).symm
    have hctx_R :
        (gc.configs.get s_min) (right t) = (gc.configs.get ⟨0, hL_pos⟩) (right t) := by
      exact (binary_config_eq_of_even_intervalFireCount gc (right t) hbR 0 s_min.val
        (Nat.zero_le _) s_min.isLt hheadR_even).symm
    exact ⟨s_min, ⟨0, hL_pos⟩, t, hs_min_fire, hzero_nonmover, hctx_L, hctx_t, hctx_R⟩
  · have hs1_lt : s_max.val + 1 < gc.configs.length := by omega
    let w : Fin gc.configs.length := ⟨s_max.val + 1, hs1_lt⟩
    have hw_eq : nextIndex gc.configs s_max = w := by
      apply Fin.ext
      simp [nextIndex, w]
      exact Nat.mod_eq_of_lt hs1_lt
    have hw_nonmover : gc.moverAt w ≠ t := by
      exact hno_t_after w (by
        dsimp [w]
        omega)
    have hctx_L :
        (gc.configs.get w) (left t) = (gc.configs.get s_min) (left t) := by
      have hwrapL_even' : Even (gc.intervalFireCount (left t) w.val gc.configs.length +
          gc.intervalFireCount (left t) 0 s_min.val) := by
        simpa [w, Nat.add_comm] using hwrapL_even
      exact binary_config_eq_of_cyclic_even_fire gc (left t) hbL
        s_min.val w.val s_min.isLt w.isLt (by
          dsimp [w]
          omega) hwrapL_even'
    have hctx_t :
        (gc.configs.get w) t = (gc.configs.get s_min) t := by
      exact configVal_eq_of_cyclic_noFire gc t s_min.val w.val
        s_min.isLt w.isLt (by
          dsimp [w]
          omega)
        (fun k hk_ge => hno_t_after k (by
          dsimp [w] at hk_ge
          omega))
        (fun k hk_lt => hno_t_before k hk_lt)
    have hctx_R :
        (gc.configs.get w) (right t) = (gc.configs.get s_min) (right t) := by
      have hwrapR_even' : Even (gc.intervalFireCount (right t) w.val gc.configs.length +
          gc.intervalFireCount (right t) 0 s_min.val) := by
        simpa [w, Nat.add_comm] using hwrapR_even
      exact binary_config_eq_of_cyclic_even_fire gc (right t) hbR
        s_min.val w.val s_min.isLt w.isLt (by
          dsimp [w]
          omega) hwrapR_even'
    exact ⟨s_min, w, t, hs_min_fire, hw_nonmover, hctx_L.symm, hctx_t.symm, hctx_R.symm⟩

/-- Wrap-aware analogue of `general_step_pair_ec`.

If `i` fires at step `a`, does not fire on the cyclic interval from the step
after `s_max` through the step before `a`, and one neighbor is binary-even
while the other is silent on that cyclic interval, then `gc` has an entry
conflict at `i`. -/
theorem general_wrapping_step_pair_ec
    (gc : GoodCycle sys)
    (i : Fin sys.rs.n)
    (a s_max : Fin gc.configs.length)
    (ha_lt_s : a.val < s_max.val)
    (ha_fire : gc.moverAt a = i)
    (hno_i_before : ∀ k : Fin gc.configs.length, k.val < a.val → gc.moverAt k ≠ i)
    (hno_i_after : ∀ k : Fin gc.configs.length, s_max.val < k.val → gc.moverAt k ≠ i)
    (hwrap_nonempty : nextIndex gc.configs s_max ≠ a)
    (hprovider :
      ((∀ j : Fin gc.configs.length, s_max.val < j.val → gc.moverAt j ≠ left i) ∧
        (∀ j : Fin gc.configs.length, j.val < a.val → gc.moverAt j ≠ left i) ∧
        isBinary sys.rs (right i) ∧
        Even (gc.intervalFireCount (right i) (s_max.val + 1) gc.configs.length +
          gc.intervalFireCount (right i) 0 a.val))
      ∨
      (isBinary sys.rs (left i) ∧
        Even (gc.intervalFireCount (left i) (s_max.val + 1) gc.configs.length +
          gc.intervalFireCount (left i) 0 a.val) ∧
        (∀ j : Fin gc.configs.length, s_max.val < j.val → gc.moverAt j ≠ right i) ∧
        (∀ j : Fin gc.configs.length, j.val < a.val → gc.moverAt j ≠ right i))) :
    hasEntryConflict gc := by
  have hL_pos := gc.configs_length_pos
  rcases hprovider with
    ⟨hleft_tail, hleft_head, hbin_r, heven_r⟩ |
    ⟨hbin_l, heven_l, hright_tail, hright_head⟩
  · by_cases hlast : s_max.val + 1 = gc.configs.length
    · have hw0 : nextIndex gc.configs s_max = ⟨0, hL_pos⟩ := by
        apply Fin.ext
        simp [nextIndex, hlast]
      have ha_ne0 : a ≠ ⟨0, hL_pos⟩ := by
        intro ha0
        exact hwrap_nonempty (by simpa [hw0] using ha0.symm)
      have ha_pos : 0 < a.val := by
        by_contra h
        have ha0_val : a.val = 0 := by omega
        have ha0 : a = ⟨0, hL_pos⟩ := Fin.ext ha0_val
        exact ha_ne0 ha0
      have hzero_nonmover : gc.moverAt ⟨0, hL_pos⟩ ≠ i :=
        hno_i_before ⟨0, hL_pos⟩ ha_pos
      have htail0 :
          gc.intervalFireCount (right i) (s_max.val + 1) gc.configs.length = 0 := by
        rw [hlast]
        simp [GoodCycle.intervalFireCount]
      have hhead_even : Even (gc.intervalFireCount (right i) 0 a.val) := by
        simpa [htail0] using heven_r
      have hctx_L :
          (gc.configs.get a) (left i) = (gc.configs.get ⟨0, hL_pos⟩) (left i) := by
        exact (configVal_eq_of_noFire_between gc (left i) 0 a.val
          (Nat.zero_le _) a.isLt (fun k _ hk2 => hleft_head k hk2)).symm
      have hctx_S :
          (gc.configs.get a) i = (gc.configs.get ⟨0, hL_pos⟩) i := by
        exact (configVal_eq_of_noFire_between gc i 0 a.val
          (Nat.zero_le _) a.isLt (fun k _ hk2 => hno_i_before k hk2)).symm
      have hctx_R :
          (gc.configs.get a) (right i) = (gc.configs.get ⟨0, hL_pos⟩) (right i) := by
        exact (binary_config_eq_of_even_intervalFireCount gc (right i) hbin_r 0 a.val
          (Nat.zero_le _) a.isLt hhead_even).symm
      exact ⟨a, ⟨0, hL_pos⟩, i, ha_fire, hzero_nonmover, hctx_L, hctx_S, hctx_R⟩
    · have hs1_lt : s_max.val + 1 < gc.configs.length := by omega
      let w : Fin gc.configs.length := ⟨s_max.val + 1, hs1_lt⟩
      have hw_eq : nextIndex gc.configs s_max = w := by
        apply Fin.ext
        simp [nextIndex, w]
        exact Nat.mod_eq_of_lt hs1_lt
      have hw_nonmover : gc.moverAt w ≠ i := by
        exact hno_i_after w (by
          dsimp [w]
          omega)
      have hctx_L :
          (gc.configs.get w) (left i) = (gc.configs.get a) (left i) := by
        exact configVal_eq_of_cyclic_noFire gc (left i) a.val w.val
          a.isLt w.isLt (by
            dsimp [w]
            omega)
          (fun k hk_ge => hleft_tail k (by
            dsimp [w] at hk_ge
            omega))
          (fun k hk_lt => hleft_head k hk_lt)
      have hctx_S :
          (gc.configs.get w) i = (gc.configs.get a) i := by
        exact configVal_eq_of_cyclic_noFire gc i a.val w.val
          a.isLt w.isLt (by
            dsimp [w]
            omega)
          (fun k hk_ge => hno_i_after k (by
            dsimp [w] at hk_ge
            omega))
          (fun k hk_lt => hno_i_before k hk_lt)
      have hctx_R :
          (gc.configs.get w) (right i) = (gc.configs.get a) (right i) := by
        exact binary_config_eq_of_cyclic_even_fire gc (right i) hbin_r
          a.val w.val a.isLt w.isLt (by
            dsimp [w]
            omega) (by
            simpa [w, Nat.add_comm] using heven_r)
      exact ⟨a, w, i, ha_fire, hw_nonmover, hctx_L.symm, hctx_S.symm, hctx_R.symm⟩
  · by_cases hlast : s_max.val + 1 = gc.configs.length
    · have hw0 : nextIndex gc.configs s_max = ⟨0, hL_pos⟩ := by
        apply Fin.ext
        simp [nextIndex, hlast]
      have ha_ne0 : a ≠ ⟨0, hL_pos⟩ := by
        intro ha0
        exact hwrap_nonempty (by simpa [hw0] using ha0.symm)
      have ha_pos : 0 < a.val := by
        by_contra h
        have ha0_val : a.val = 0 := by omega
        have ha0 : a = ⟨0, hL_pos⟩ := Fin.ext ha0_val
        exact ha_ne0 ha0
      have hzero_nonmover : gc.moverAt ⟨0, hL_pos⟩ ≠ i :=
        hno_i_before ⟨0, hL_pos⟩ ha_pos
      have htail0 :
          gc.intervalFireCount (left i) (s_max.val + 1) gc.configs.length = 0 := by
        rw [hlast]
        simp [GoodCycle.intervalFireCount]
      have hhead_even : Even (gc.intervalFireCount (left i) 0 a.val) := by
        simpa [htail0] using heven_l
      have hctx_L :
          (gc.configs.get a) (left i) = (gc.configs.get ⟨0, hL_pos⟩) (left i) := by
        exact (binary_config_eq_of_even_intervalFireCount gc (left i) hbin_l 0 a.val
          (Nat.zero_le _) a.isLt hhead_even).symm
      have hctx_S :
          (gc.configs.get a) i = (gc.configs.get ⟨0, hL_pos⟩) i := by
        exact (configVal_eq_of_noFire_between gc i 0 a.val
          (Nat.zero_le _) a.isLt (fun k _ hk2 => hno_i_before k hk2)).symm
      have hctx_R :
          (gc.configs.get a) (right i) = (gc.configs.get ⟨0, hL_pos⟩) (right i) := by
        exact (configVal_eq_of_noFire_between gc (right i) 0 a.val
          (Nat.zero_le _) a.isLt (fun k _ hk2 => hright_head k hk2)).symm
      exact ⟨a, ⟨0, hL_pos⟩, i, ha_fire, hzero_nonmover, hctx_L, hctx_S, hctx_R⟩
    · have hs1_lt : s_max.val + 1 < gc.configs.length := by omega
      let w : Fin gc.configs.length := ⟨s_max.val + 1, hs1_lt⟩
      have hw_eq : nextIndex gc.configs s_max = w := by
        apply Fin.ext
        simp [nextIndex, w]
        exact Nat.mod_eq_of_lt hs1_lt
      have hw_nonmover : gc.moverAt w ≠ i := by
        exact hno_i_after w (by
          dsimp [w]
          omega)
      have hctx_L :
          (gc.configs.get w) (left i) = (gc.configs.get a) (left i) := by
        exact binary_config_eq_of_cyclic_even_fire gc (left i) hbin_l
          a.val w.val a.isLt w.isLt (by
            dsimp [w]
            omega) (by
            simpa [w, Nat.add_comm] using heven_l)
      have hctx_S :
          (gc.configs.get w) i = (gc.configs.get a) i := by
        exact configVal_eq_of_cyclic_noFire gc i a.val w.val
          a.isLt w.isLt (by
            dsimp [w]
            omega)
          (fun k hk_ge => hno_i_after k (by
            dsimp [w] at hk_ge
            omega))
          (fun k hk_lt => hno_i_before k hk_lt)
      have hctx_R :
          (gc.configs.get w) (right i) = (gc.configs.get a) (right i) := by
        exact configVal_eq_of_cyclic_noFire gc (right i) a.val w.val
          a.isLt w.isLt (by
            dsimp [w]
            omega)
          (fun k hk_ge => hright_tail k (by
            dsimp [w] at hk_ge
            omega))
          (fun k hk_lt => hright_head k hk_lt)
      exact ⟨a, w, i, ha_fire, hw_nonmover, hctx_L.symm, hctx_S.symm, hctx_R.symm⟩

end LeanMn
