import LeanMn.LowerBound.CycleTypes

namespace LeanMn

variable {sys : System}

private def nonbinaryFinset (rs : RingSpec) : Finset (Fin rs.n) :=
  Finset.univ.filter fun i : Fin rs.n => rs.m i ≠ 2

private theorem left_ne_self_of_n_eq_six
    (rs : RingSpec) (hn : rs.n = 6) (i : Fin rs.n) :
    left i ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  have hval' : (i.val + 6 - 1) % 6 = i.val := by
    simpa [left_val, hn] using hval
  have hi : i.val < 6 := by simpa [hn] using i.isLt
  omega

private theorem right_ne_self_of_n_eq_six
    (rs : RingSpec) (hn : rs.n = 6) (i : Fin rs.n) :
    right i ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  have hval' : (i.val + 1) % 6 = i.val := by
    simpa [right_val, hn] using hval
  have hi : i.val < 6 := by simpa [hn] using i.isLt
  omega

theorem left3_eq_right3_of_n_eq_six
    (rs : RingSpec) (hn : rs.n = 6) (t : Fin rs.n) :
    left (left (left t)) = right (right (right t)) := by
  apply Fin.ext
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, right_val, hn]
  omega

theorem left4_eq_right2_of_n_eq_six
    (rs : RingSpec) (hn : rs.n = 6) (t : Fin rs.n) :
    left (left (left (left t))) = right (right t) := by
  apply Fin.ext
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, right_val, hn]
  omega

theorem right4_eq_left2_of_n_eq_six
    (rs : RingSpec) (hn : rs.n = 6) (t : Fin rs.n) :
    right (right (right (right t))) = left (left t) := by
  apply Fin.ext
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  simp [left_val, right_val, hn]
  omega

theorem eq_left3_of_not_local5_of_n_eq_six
    (rs : RingSpec) (hn : rs.n = 6) (q t : Fin rs.n)
    (hqt : q ≠ t)
    (hqL : q ≠ left t)
    (hqLL : q ≠ left (left t))
    (hqR : q ≠ right t)
    (hqRR : q ≠ right (right t)) :
    q = left (left (left t)) := by
  apply Fin.ext
  have hq : q.val < 6 := by simpa [hn] using q.isLt
  have ht : t.val < 6 := by simpa [hn] using t.isLt
  let d : Nat := (q.val + 6 - t.val) % 6
  have hd_lt : d < 6 := by
    dsimp [d]
    exact Nat.mod_lt _ (by omega)
  have hd0 : d ≠ 0 := by
    intro hd
    apply hqt
    apply Fin.ext
    dsimp [d] at hd
    omega
  have hd1 : d ≠ 1 := by
    intro hd
    apply hqR
    apply Fin.ext
    dsimp [d] at hd
    simp [right_val, hn]
    omega
  have hd2 : d ≠ 2 := by
    intro hd
    apply hqRR
    apply Fin.ext
    dsimp [d] at hd
    simp [right_val, hn]
    omega
  have hd4 : d ≠ 4 := by
    intro hd
    apply hqLL
    apply Fin.ext
    dsimp [d] at hd
    simp [left_val, hn]
    omega
  have hd5 : d ≠ 5 := by
    intro hd
    apply hqL
    apply Fin.ext
    dsimp [d] at hd
    simp [left_val, hn]
    omega
  have hd3 : d = 3 := by
    omega
  dsimp [d] at hd3
  simp [left_val, hn]
  omega

theorem binaryCount_le_six_of_n_eq_six
    (rs : RingSpec) (hn : rs.n = 6) :
    binaryCount rs ≤ 6 := by
  unfold binaryCount
  simpa [Finset.card_univ, hn] using
    (Finset.card_filter_le (s := (Finset.univ : Finset (Fin rs.n)))
      (p := fun i : Fin rs.n => rs.m i = 2))

theorem existsUnique_nonbinary_of_binaryCount_five
    (rs : RingSpec) (hn : rs.n = 6)
    (hcount : binaryCount rs = 5) :
    ∃! t : Fin rs.n, ¬ isBinary rs t := by
  classical
  have hcard_one : (nonbinaryFinset rs).card = 1 := by
    have hsplit :
        binaryCount rs + (nonbinaryFinset rs).card = 6 := by
      simpa [binaryCount, nonbinaryFinset, hn] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin rs.n)))
          (p := fun i : Fin rs.n => rs.m i = 2))
    rw [hcount] at hsplit
    omega
  rcases Finset.card_eq_one.mp hcard_one with ⟨t, ht⟩
  refine ⟨t, ?_, ?_⟩
  · have htmem : t ∈ nonbinaryFinset rs := by simpa [ht]
    simpa [nonbinaryFinset, isBinary] using htmem
  · intro s hs
    have hsmem : s ∈ nonbinaryFinset rs := by
      simpa [nonbinaryFinset, isBinary] using hs
    simpa [ht] using hsmem

theorem exists_pivot_of_binaryCount_five
    (rs : RingSpec) (hn : rs.n = 6)
    (hcount : binaryCount rs = 5) :
    ∃ t : Fin rs.n, rs.m t ≠ 2 ∧ rs.m (left t) = 2 ∧ rs.m (right t) = 2 := by
  rcases existsUnique_nonbinary_of_binaryCount_five rs hn hcount with ⟨t, ht, huniq⟩
  have hL : isBinary rs (left t) := by
    by_contra hnb
    have hEq : left t = t := huniq (left t) hnb
    exact (left_ne_self_of_n_eq_six rs hn t) hEq
  have hR : isBinary rs (right t) := by
    by_contra hnb
    have hEq : right t = t := huniq (right t) hnb
    exact (right_ne_self_of_n_eq_six rs hn t) hEq
  exact ⟨t, ht, hL, hR⟩

theorem exists_ternary_pivot_of_binaryCount_five
    (rs : RingSpec) (hn : rs.n = 6)
    (hcount : binaryCount rs = 5) :
    ∃ t : Fin rs.n, rs.m t ≥ 3 ∧ rs.m (left t) = 2 ∧ rs.m (right t) = 2 := by
  rcases exists_pivot_of_binaryCount_five rs hn hcount with ⟨t, ht, hL, hR⟩
  have hpos := rs.m_pos t
  refine ⟨t, ?_, hL, hR⟩
  omega

theorem all_binary_of_binaryCount_six
    (rs : RingSpec) (hn : rs.n = 6)
    (hcount : binaryCount rs = 6) :
    ∀ i : Fin rs.n, isBinary rs i := by
  classical
  have hcard_zero : (nonbinaryFinset rs).card = 0 := by
    have hsplit :
        binaryCount rs + (nonbinaryFinset rs).card = 6 := by
      simpa [binaryCount, nonbinaryFinset, hn] using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin rs.n)))
          (p := fun i : Fin rs.n => rs.m i = 2))
    rw [hcount] at hsplit
    omega
  have hempty : nonbinaryFinset rs = ∅ := Finset.card_eq_zero.mp hcard_zero
  intro i
  by_contra hnb
  have himem : i ∈ nonbinaryFinset rs := by
    simpa [nonbinaryFinset, isBinary] using hnb
  simpa [hempty] using himem

theorem exists_ternary_pivot_or_all_binary_of_binaryCount_ge_five
    (rs : RingSpec) (hn : rs.n = 6)
    (hcount : 5 ≤ binaryCount rs) :
    (∃ t : Fin rs.n, rs.m t ≥ 3 ∧ rs.m (left t) = 2 ∧ rs.m (right t) = 2) ∨
    (∀ i : Fin rs.n, isBinary rs i) := by
  have hle : binaryCount rs ≤ 6 := binaryCount_le_six_of_n_eq_six rs hn
  have hcases : binaryCount rs = 5 ∨ binaryCount rs = 6 := by
    omega
  cases hcases with
  | inl h5 =>
      left
      exact exists_ternary_pivot_of_binaryCount_five rs hn h5
  | inr h6 =>
      right
      exact all_binary_of_binaryCount_six rs hn h6

theorem fireCount_pos_of_goodCycle
    (gc : GoodCycle sys) (p : Fin sys.rs.n) :
    0 < gc.fireCount p := by
  obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair p
  have hmov : gc.moverAt k = p := by
    rw [← hj]
    exact (gc.moverAt_unique k j hpriv).symm
  rw [gc.fireCount_eq_sum_moverAt p]
  have h2 := Finset.single_le_sum
    (f := fun i : Fin gc.configs.length =>
      if gc.moverAt i = p then (1 : Nat) else 0)
    (by
      intro i _
      by_cases h : gc.moverAt i = p <;> simp [h])
    (Finset.mem_univ k)
  have h2' :
      1 ≤ ∑ i : Fin gc.configs.length,
        (if gc.moverAt i = p then (1 : Nat) else 0) := by
    simpa [hmov] using h2
  omega

theorem exists_active_binary_sandwich_of_binaryCount_ge_five
    (gc : GoodCycle sys) (hn : sys.rs.n = 6)
    (hcount : 5 ≤ binaryCount sys.rs) :
    ∃ t : Fin sys.rs.n,
      sys.rs.m (left t) = 2 ∧
      sys.rs.m (right t) = 2 ∧
      0 < gc.fireCount t := by
  rcases exists_ternary_pivot_or_all_binary_of_binaryCount_ge_five sys.rs hn hcount with
    hpivot | hall
  · rcases hpivot with ⟨t, _, hL, hR⟩
    exact ⟨t, hL, hR, fireCount_pos_of_goodCycle gc t⟩
  · refine ⟨⟨0, by omega⟩, hall _, hall _, ?_⟩
    exact fireCount_pos_of_goodCycle gc _

end LeanMn
