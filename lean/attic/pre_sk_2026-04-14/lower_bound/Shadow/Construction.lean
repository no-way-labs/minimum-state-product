/-
  Construction.lean — Shadow Cycle Construction (Phase 6, Claim 4.4.1)

  Defines the shadow configuration formula for uniform sweep cycles.
  Given a waterfall good cycle of length 2n, constructs 2n shadow configs
  using processor-dependent shifts d_i.

  Shadow formula: s_k[i] = v_i iff 1 ≤ ((k + d_i) mod 2n) ≤ n

  Shadow permutation σ (mover at shadow step k is proc σ(k mod n)):
    σ(0) = n-4, σ(1) = n-1, σ(2) = 0,
    σ(k) = k-2 for 3 ≤ k ≤ n-3,
    σ(n-2) = n-2, σ(n-1) = n-3
-/
import LeanMn.LowerBound.MNU

namespace LeanMn

variable {sys : System}

/-! ### Shadow shift vector -/

/-- The shadow shift d_i for processor i on a ring of size n.
    d_i = n-2-i for 0 ≤ i ≤ n-5,
    d_{n-4} = 0, d_{n-3} = n+1, d_{n-2} = 2, d_{n-1} = 2n-1.
    We encode this as a function Fin n → Nat (values mod 2n). -/
def shadowShift (n : Nat) (i : Fin n) : Nat :=
  if i.val ≤ n - 5 then n - 2 - i.val
  else if i.val = n - 4 then 0
  else if i.val = n - 3 then n + 1
  else if i.val = n - 2 then 2
  else 2 * n - 1  -- i = n-1

/-- The shadow permutation σ on {0, ..., n-1}.
    σ(0) = n-4, σ(1) = n-1, σ(2) = 0,
    σ(k) = k-2 for 3 ≤ k ≤ n-3,
    σ(n-2) = n-2, σ(n-1) = n-3. -/
def shadowPerm (n : Nat) (hn : 5 ≤ n) (k : Fin n) : Fin n :=
  if k.val = 0 then ⟨n - 4, by omega⟩
  else if k.val = 1 then ⟨n - 1, by omega⟩
  else if k.val = 2 then ⟨0, by omega⟩
  else if k.val ≤ n - 3 then ⟨k.val - 2, by omega⟩
  else if k.val = n - 2 then ⟨n - 2, by omega⟩
  else ⟨n - 3, by omega⟩  -- k = n-1

@[simp] theorem shadowShift_linear (n : Nat) (hn : 5 ≤ n) (i : Nat)
    (hi : i ≤ n - 5) :
    shadowShift n ⟨i, by omega⟩ = n - 2 - i := by
  unfold shadowShift
  simp [hi]

@[simp] theorem shadowShift_n_sub_four (n : Nat) (hn : 5 ≤ n) :
    shadowShift n ⟨n - 4, by omega⟩ = 0 := by
  unfold shadowShift
  have hlin : ¬(n - 4 ≤ n - 5) := by omega
  simp [hlin]

@[simp] theorem shadowShift_n_sub_three (n : Nat) (hn : 5 ≤ n) :
    shadowShift n ⟨n - 3, by omega⟩ = n + 1 := by
  unfold shadowShift
  have hlin : ¬(n - 3 ≤ n - 5) := by omega
  have hn4 : n - 3 ≠ n - 4 := by omega
  simp [hlin, hn4]

@[simp] theorem shadowShift_n_sub_two (n : Nat) (hn : 5 ≤ n) :
    shadowShift n ⟨n - 2, by omega⟩ = 2 := by
  unfold shadowShift
  have hlin : ¬(n - 2 ≤ n - 5) := by omega
  have hn4 : n - 2 ≠ n - 4 := by omega
  have hn3 : n - 2 ≠ n - 3 := by omega
  simp [hlin, hn4, hn3]

@[simp] theorem shadowShift_n_sub_one (n : Nat) (hn : 5 ≤ n) :
    shadowShift n ⟨n - 1, by omega⟩ = 2 * n - 1 := by
  unfold shadowShift
  have hlin : ¬(n - 1 ≤ n - 5) := by omega
  have hn4 : n - 1 ≠ n - 4 := by omega
  have hn3 : n - 1 ≠ n - 3 := by omega
  have hn2 : n - 1 ≠ n - 2 := by omega
  simp [hlin, hn4, hn3, hn2]

@[simp] theorem shadowPerm_zero (n : Nat) (hn : 5 ≤ n) :
    shadowPerm n hn ⟨0, by omega⟩ = ⟨n - 4, by omega⟩ := by
  unfold shadowPerm
  simp

@[simp] theorem shadowPerm_one (n : Nat) (hn : 5 ≤ n) :
    shadowPerm n hn ⟨1, by omega⟩ = ⟨n - 1, by omega⟩ := by
  unfold shadowPerm
  simp

@[simp] theorem shadowPerm_two (n : Nat) (hn : 5 ≤ n) :
    shadowPerm n hn ⟨2, by omega⟩ = ⟨0, by omega⟩ := by
  unfold shadowPerm
  simp

@[simp] theorem shadowPerm_mid (n : Nat) (hn : 5 ≤ n) (k : Nat)
    (hk_lo : 3 ≤ k) (hk_hi : k ≤ n - 3) :
    shadowPerm n hn ⟨k, by omega⟩ = ⟨k - 2, by omega⟩ := by
  unfold shadowPerm
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  have h2 : k ≠ 2 := by omega
  simp [h0, h1, h2, hk_hi]

@[simp] theorem shadowPerm_n_sub_two (n : Nat) (hn : 5 ≤ n) :
    shadowPerm n hn ⟨n - 2, by omega⟩ = ⟨n - 2, by omega⟩ := by
  unfold shadowPerm
  have h0 : n - 2 ≠ 0 := by omega
  have h1 : n - 2 ≠ 1 := by omega
  have h2 : n - 2 ≠ 2 := by omega
  have hmid : ¬(n - 2 ≤ n - 3) := by omega
  simp [h0, h1, h2, hmid]

@[simp] theorem shadowPerm_n_sub_one (n : Nat) (hn : 5 ≤ n) :
    shadowPerm n hn ⟨n - 1, by omega⟩ = ⟨n - 3, by omega⟩ := by
  unfold shadowPerm
  have h0 : n - 1 ≠ 0 := by omega
  have h1 : n - 1 ≠ 1 := by omega
  have h2 : n - 1 ≠ 2 := by omega
  have hmid : ¬(n - 1 ≤ n - 3) := by omega
  have hn2 : n - 1 ≠ n - 2 := by omega
  simp [h0, h1, h2, hmid, hn2]

private lemma lt_two_mul_decompose_mod (n k : Nat) (_hn : 0 < n) (hk : k < 2 * n) :
    k = k % n ∨ k = k % n + n := by
  by_cases hkn : k < n
  · left
    symm
    exact Nat.mod_eq_of_lt hkn
  · right
    have hge : n ≤ k := by omega
    have hlt : k - n < n := by omega
    have hmod : k % n = k - n := by
      rw [Nat.mod_eq_sub_mod hge]
      simpa [Nat.mod_eq_of_lt hlt]
    omega

private lemma mod_two_period_boundary (n k : Nat) (hn : 0 < n) (hk : k < 2 * n) :
    (k < n ∧ k = k % n) ∨ (n ≤ k ∧ k = k % n + n) := by
  rcases lt_two_mul_decompose_mod n k hn hk with hkmod | hkmod
  · exact Or.inl ⟨by
      rw [hkmod]
      exact Nat.mod_lt _ hn, hkmod⟩
  · exact Or.inr ⟨by omega, hkmod⟩

private lemma mod_add_period (n a : Nat) (hn : 0 < n) (ha : a < n) :
    (a + n) % n = a := by
  rw [show a + n = a + 1 * n from by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]

private theorem shadowPerm_first_half_boundary (n : Nat) (hn : 5 ≤ n) (r : Nat)
    (hr : r < n) :
    let p := shadowPerm n hn ⟨r, hr⟩
    (r + shadowShift n p) % (2 * n) = 0 ∨
      (r + shadowShift n p) % (2 * n) = n := by
  dsimp
  by_cases h0 : r = 0
  · subst h0
    left
    rw [shadowPerm_zero n hn, shadowShift_n_sub_four n hn]
    simp
  · by_cases h1 : r = 1
    · subst h1
      left
      have hsum : 1 + (2 * n - 1) = 2 * n := by omega
      rw [shadowPerm_one n hn, shadowShift_n_sub_one n hn, hsum, Nat.mod_self]
    · by_cases h2 : r = 2
      · subst h2
        right
        have hshift0 : shadowShift n ⟨0, by omega⟩ = n - 2 := by
          simpa using shadowShift_linear n hn 0 (by omega)
        have hsum : 2 + (n - 2) = n := by omega
        rw [shadowPerm_two n hn, hshift0, hsum,
          Nat.mod_eq_of_lt (by omega)]
      · by_cases hmid : r ≤ n - 3
        · have h3 : 3 ≤ r := by omega
          right
          have hsum : r + (n - 2 - (r - 2)) = n := by omega
          rw [shadowPerm_mid n hn r h3 hmid,
            shadowShift_linear n hn (r - 2) (by omega), hsum,
            Nat.mod_eq_of_lt (by omega)]
        · by_cases hn2 : r = n - 2
          · subst hn2
            right
            have hsum : n - 2 + 2 = n := by omega
            rw [shadowPerm_n_sub_two n hn, shadowShift_n_sub_two n hn, hsum,
              Nat.mod_eq_of_lt (by omega)]
          · have hlast : r = n - 1 := by omega
            subst hlast
            left
            have hsum : n - 1 + (n + 1) = 2 * n := by omega
            rw [shadowPerm_n_sub_one n hn, shadowShift_n_sub_three n hn, hsum, Nat.mod_self]

private theorem shadowShift_linear_first_half_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (r i : Nat)
    (hr : r < n) (hi : i ≤ n - 5) :
    (((r + shadowShift n ⟨i, by omega⟩) % (2 * n) = 0) ∨
      ((r + shadowShift n ⟨i, by omega⟩) % (2 * n) = n)) ↔
      r = i + 2 := by
  have hsumlt : r + shadowShift n ⟨i, by omega⟩ < 2 * n := by
    rw [shadowShift_linear n hn i hi]
    omega
  have hsumlt' : r + (n - 2 - i) < 2 * n := by
    omega
  rw [shadowShift_linear n hn i hi]
  rw [Nat.mod_eq_of_lt hsumlt']
  constructor
  · intro h
    omega
  · intro h
    right
    omega

private theorem shadowShift_n4_first_half_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (r : Nat)
    (hr : r < n) :
    (((r + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) = 0) ∨
      ((r + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) = n)) ↔
      r = 0 := by
  have hsumlt : r + shadowShift n ⟨n - 4, by omega⟩ < 2 * n := by
    rw [shadowShift_n_sub_four n hn]
    omega
  have hsumlt' : r + 0 < 2 * n := by omega
  rw [shadowShift_n_sub_four n hn]
  rw [Nat.mod_eq_of_lt hsumlt']
  constructor
  · intro h
    omega
  · intro h
    left
    omega

private theorem shadowShift_n3_first_half_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (r : Nat)
    (hr : r < n) :
    (((r + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) = 0) ∨
      ((r + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) = n)) ↔
      r = n - 1 := by
  rw [shadowShift_n_sub_three n hn]
  constructor
  · intro h
    by_cases hlast : r = n - 1
    · exact hlast
    have hsumlt : r + (n + 1) < 2 * n := by omega
    rw [Nat.mod_eq_of_lt hsumlt] at h
    omega
  · intro h
    subst h
    left
    have hsum : n - 1 + (n + 1) = 2 * n := by omega
    rw [hsum, Nat.mod_self]

private theorem shadowShift_n2_first_half_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (r : Nat)
    (hr : r < n) :
    (((r + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) = 0) ∨
      ((r + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) = n)) ↔
      r = n - 2 := by
  have hsumlt : r + shadowShift n ⟨n - 2, by omega⟩ < 2 * n := by
    rw [shadowShift_n_sub_two n hn]
    omega
  have hsumlt' : r + 2 < 2 * n := by omega
  rw [shadowShift_n_sub_two n hn]
  rw [Nat.mod_eq_of_lt hsumlt']
  constructor
  · intro h
    omega
  · intro h
    right
    omega

private theorem shadowShift_n1_first_half_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (r : Nat)
    (hr : r < n) :
    (((r + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) = 0) ∨
      ((r + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) = n)) ↔
      r = 1 := by
  rw [shadowShift_n_sub_one n hn]
  constructor
  · intro h
    by_cases h0 : r = 0
    · subst h0
      simp at h
      omega
    have hge : 1 ≤ r := by omega
    have hmod :
        (r + (2 * n - 1)) % (2 * n) = r - 1 := by
      rw [show r + (2 * n - 1) = (r - 1) + 1 * (2 * n) from by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at h
    omega
  · intro h
    subst h
    left
    have hsum : 1 + (2 * n - 1) = 2 * n := by omega
    rw [hsum, Nat.mod_self]

private theorem residue_boundary_add_n_iff
    (n r : Nat) (hn : 0 < n) (hr : r < 2 * n) :
    (r = 0 ∨ r = n) ↔
      (((r + n) % (2 * n) = 0) ∨ ((r + n) % (2 * n) = n)) := by
  constructor
  · intro h
    rcases h with h0 | hn0
    · right
      rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    · left
      rw [hn0, show n + n = 2 * n by omega, Nat.mod_self]
  · intro h
    by_cases hlt : r < n
    · have hsumlt : r + n < 2 * n := by omega
      rw [Nat.mod_eq_of_lt hsumlt] at h
      omega
    · have hge : n ≤ r := by omega
      have hmod : (r + n) % (2 * n) = r - n := by
        rw [show r + n = (r - n) + 1 * (2 * n) from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod] at h
      omega

private theorem boundary_add_n_iff (n x : Nat) (hn : 0 < n) :
    (((x % (2 * n)) = 0) ∨ ((x % (2 * n)) = n)) ↔
      ((((x + n) % (2 * n)) = 0) ∨ (((x + n) % (2 * n)) = n)) := by
  let r := x % (2 * n)
  have h2n : 0 < 2 * n := by omega
  have hr : r < 2 * n := by
    dsimp [r]
    exact Nat.mod_lt _ h2n
  have hmod : (x + n) % (2 * n) = (r + n) % (2 * n) := by
    dsimp [r]
    have hx := Nat.mod_add_div x (2 * n)
    calc
      (x + n) % (2 * n)
          = ((x % (2 * n) + (2 * n) * (x / (2 * n))) + n) % (2 * n) := by
              rw [hx]
      _ = ((x % (2 * n) + n) + (x / (2 * n)) * (2 * n)) % (2 * n) := by
            ac_rfl
      _ = (x % (2 * n) + n) % (2 * n) := by
            rw [Nat.add_mul_mod_self_right]
  constructor
  · intro h
    rw [hmod]
    have hrb : r = 0 ∨ r = n := by
      simpa [r] using h
    exact (residue_boundary_add_n_iff n r hn hr).mp hrb
  · intro h
    rw [hmod] at h
    have hrb : r = 0 ∨ r = n :=
      (residue_boundary_add_n_iff n r hn hr).mpr h
    simpa [r] using hrb

private theorem shadowShift_linear_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (k i : Nat)
    (hk : k < 2 * n) (hi : i ≤ n - 5) :
    (((k + shadowShift n ⟨i, by omega⟩) % (2 * n) = 0) ∨
      ((k + shadowShift n ⟨i, by omega⟩) % (2 * n) = n)) ↔
      k % n = i + 2 := by
  rcases mod_two_period_boundary n k (by omega) hk with ⟨_, hk_eq⟩ | ⟨_, hk_eq⟩
  · rw [hk_eq]
    have hkmod : (k % n) % n = k % n := Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
    rw [hkmod]
    exact shadowShift_linear_first_half_boundary_iff n hn (k % n) i
      (Nat.mod_lt _ (by omega)) hi
  · have hstep :
        (((k % n + n + shadowShift n ⟨i, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + n + shadowShift n ⟨i, by omega⟩) % (2 * n) = n)) ↔
        (((k % n + shadowShift n ⟨i, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + shadowShift n ⟨i, by omega⟩) % (2 * n) = n)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (boundary_add_n_iff n (k % n + shadowShift n ⟨i, by omega⟩) (by omega)).symm
    have hkmod : (k % n + n) % n = k % n := mod_add_period n (k % n) (by omega)
      (Nat.mod_lt _ (by omega))
    rw [hk_eq, hkmod]
    exact hstep.trans <|
      shadowShift_linear_first_half_boundary_iff n hn (k % n) i
        (Nat.mod_lt _ (by omega)) hi

private theorem shadowShift_n4_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (k : Nat)
    (hk : k < 2 * n) :
    (((k + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) = 0) ∨
      ((k + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) = n)) ↔
      k % n = 0 := by
  rcases mod_two_period_boundary n k (by omega) hk with ⟨_, hk_eq⟩ | ⟨_, hk_eq⟩
  · rw [hk_eq]
    have hkmod : (k % n) % n = k % n := Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
    rw [hkmod]
    exact shadowShift_n4_first_half_boundary_iff n hn (k % n)
      (Nat.mod_lt _ (by omega))
  · have hstep :
        (((k % n + n + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + n + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) = n)) ↔
        (((k % n + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) = n)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (boundary_add_n_iff n (k % n + shadowShift n ⟨n - 4, by omega⟩) (by omega)).symm
    have hkmod : (k % n + n) % n = k % n := mod_add_period n (k % n) (by omega)
      (Nat.mod_lt _ (by omega))
    rw [hk_eq, hkmod]
    exact hstep.trans <|
      shadowShift_n4_first_half_boundary_iff n hn (k % n)
        (Nat.mod_lt _ (by omega))

private theorem shadowShift_n3_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (k : Nat)
    (hk : k < 2 * n) :
    (((k + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) = 0) ∨
      ((k + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) = n)) ↔
      k % n = n - 1 := by
  rcases mod_two_period_boundary n k (by omega) hk with ⟨_, hk_eq⟩ | ⟨_, hk_eq⟩
  · rw [hk_eq]
    have hkmod : (k % n) % n = k % n := Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
    rw [hkmod]
    exact shadowShift_n3_first_half_boundary_iff n hn (k % n)
      (Nat.mod_lt _ (by omega))
  · have hstep :
        (((k % n + n + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + n + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) = n)) ↔
        (((k % n + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) = n)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (boundary_add_n_iff n (k % n + shadowShift n ⟨n - 3, by omega⟩) (by omega)).symm
    have hkmod : (k % n + n) % n = k % n := mod_add_period n (k % n) (by omega)
      (Nat.mod_lt _ (by omega))
    rw [hk_eq, hkmod]
    exact hstep.trans <|
      shadowShift_n3_first_half_boundary_iff n hn (k % n)
        (Nat.mod_lt _ (by omega))

private theorem shadowShift_n2_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (k : Nat)
    (hk : k < 2 * n) :
    (((k + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) = 0) ∨
      ((k + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) = n)) ↔
      k % n = n - 2 := by
  rcases mod_two_period_boundary n k (by omega) hk with ⟨_, hk_eq⟩ | ⟨_, hk_eq⟩
  · rw [hk_eq]
    have hkmod : (k % n) % n = k % n := Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
    rw [hkmod]
    exact shadowShift_n2_first_half_boundary_iff n hn (k % n)
      (Nat.mod_lt _ (by omega))
  · have hstep :
        (((k % n + n + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + n + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) = n)) ↔
        (((k % n + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) = n)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (boundary_add_n_iff n (k % n + shadowShift n ⟨n - 2, by omega⟩) (by omega)).symm
    have hkmod : (k % n + n) % n = k % n := mod_add_period n (k % n) (by omega)
      (Nat.mod_lt _ (by omega))
    rw [hk_eq, hkmod]
    exact hstep.trans <|
      shadowShift_n2_first_half_boundary_iff n hn (k % n)
        (Nat.mod_lt _ (by omega))

private theorem shadowShift_n1_boundary_iff
    (n : Nat) (hn : 5 ≤ n) (k : Nat)
    (hk : k < 2 * n) :
    (((k + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) = 0) ∨
      ((k + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) = n)) ↔
      k % n = 1 := by
  rcases mod_two_period_boundary n k (by omega) hk with ⟨_, hk_eq⟩ | ⟨_, hk_eq⟩
  · rw [hk_eq]
    have hkmod : (k % n) % n = k % n := Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
    rw [hkmod]
    exact shadowShift_n1_first_half_boundary_iff n hn (k % n)
      (Nat.mod_lt _ (by omega))
  · have hstep :
        (((k % n + n + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + n + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) = n)) ↔
        (((k % n + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) = 0) ∨
          ((k % n + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) = n)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (boundary_add_n_iff n (k % n + shadowShift n ⟨n - 1, by omega⟩) (by omega)).symm
    have hkmod : (k % n + n) % n = k % n := mod_add_period n (k % n) (by omega)
      (Nat.mod_lt _ (by omega))
    rw [hk_eq, hkmod]
    exact hstep.trans <|
      shadowShift_n1_first_half_boundary_iff n hn (k % n)
        (Nat.mod_lt _ (by omega))

theorem shadow_boundary_imp_perm
    (n : Nat) (hn : 5 ≤ n) (k : Nat) (hk : k < 2 * n) (i : Fin n)
    (hboundary : (((k + shadowShift n i) % (2 * n) = 0) ∨
      ((k + shadowShift n i) % (2 * n) = n))) :
    i = shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩ := by
  have hboundary' : (((k + shadowShift n ⟨i.val, by omega⟩) % (2 * n) = 0) ∨
      ((k + shadowShift n ⟨i.val, by omega⟩) % (2 * n) = n)) := by
    simpa using hboundary
  by_cases hi_lin : i.val ≤ n - 5
  · have hkmod : k % n = i.val + 2 :=
      (shadowShift_linear_boundary_iff n hn k i.val hk hi_lin).mp hboundary'
    by_cases hi0 : i.val = 0
    · have hperm :
          shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩ = ⟨0, by omega⟩ := by
        have hk2 : k % n = 2 := by omega
        simpa [hk2] using
          (shadowPerm_two n hn :
            shadowPerm n hn ⟨2, by omega⟩ = ⟨0, by omega⟩)
      apply Fin.ext
      simpa [hi0] using congrArg Fin.val hperm.symm
    · have hmid :
          shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩ = ⟨i.val, by omega⟩ := by
        have hlo : 3 ≤ i.val + 2 := by omega
        have hhi : i.val + 2 ≤ n - 3 := by omega
        simpa [hkmod] using shadowPerm_mid n hn (i.val + 2) hlo hhi
      apply Fin.ext
      simpa using congrArg Fin.val hmid.symm
  · by_cases hi_n4 : i.val = n - 4
    · have hperm :
          shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩ = ⟨n - 4, by omega⟩ := by
        have hkmod : k % n = 0 :=
          (shadowShift_n4_boundary_iff n hn k hk).mp (by simpa [hi_n4] using hboundary')
        simpa [hkmod] using shadowPerm_zero n hn
      apply Fin.ext
      simpa [hi_n4] using congrArg Fin.val hperm.symm
    · by_cases hi_n3 : i.val = n - 3
      · have hperm :
            shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩ = ⟨n - 3, by omega⟩ := by
          have hkmod : k % n = n - 1 :=
            (shadowShift_n3_boundary_iff n hn k hk).mp (by simpa [hi_n3] using hboundary')
          simpa [hkmod] using shadowPerm_n_sub_one n hn
        apply Fin.ext
        simpa [hi_n3] using congrArg Fin.val hperm.symm
      · by_cases hi_n2 : i.val = n - 2
        · have hperm :
              shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩ = ⟨n - 2, by omega⟩ := by
            have hkmod : k % n = n - 2 :=
              (shadowShift_n2_boundary_iff n hn k hk).mp (by simpa [hi_n2] using hboundary')
            simpa [hkmod] using shadowPerm_n_sub_two n hn
          apply Fin.ext
          simpa [hi_n2] using congrArg Fin.val hperm.symm
        · have hi_last : i.val = n - 1 := by
            have hi_lt := i.isLt
            omega
          have hperm :
              shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩ = ⟨n - 1, by omega⟩ := by
            have hkmod : k % n = 1 :=
              (shadowShift_n1_boundary_iff n hn k hk).mp (by simpa [hi_last] using hboundary')
            simpa [hkmod] using shadowPerm_one n hn
          apply Fin.ext
          simpa [hi_last] using congrArg Fin.val hperm.symm

theorem shadow_off_boundary_of_ne_perm
    (n : Nat) (hn : 5 ≤ n) (k : Nat) (hk : k < 2 * n) (i : Fin n)
    (hi : i ≠ shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩) :
    (k + shadowShift n i) % (2 * n) ≠ 0 ∧
      (k + shadowShift n i) % (2 * n) ≠ n := by
  constructor
  · intro h0
    exact hi (shadow_boundary_imp_perm n hn k hk i (Or.inl h0))
  · intro hn0
    exact hi (shadow_boundary_imp_perm n hn k hk i (Or.inr hn0))

theorem shadow_boundary_at_perm
    (n : Nat) (hn : 5 ≤ n) (k : Nat) (hk : k < 2 * n) :
    let p : Fin n := shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩
    (((k + shadowShift n p) % (2 * n) = 0) ∨
      ((k + shadowShift n p) % (2 * n) = n)) := by
  dsimp
  rcases mod_two_period_boundary n k (by omega) hk with ⟨_, hk_eq⟩ | ⟨_, hk_eq⟩
  · rw [hk_eq]
    have hkmod : (k % n) % n = k % n := Nat.mod_eq_of_lt (Nat.mod_lt _ (by omega))
    simpa [hkmod] using shadowPerm_first_half_boundary n hn (k % n)
      (Nat.mod_lt _ (by omega))
  · have hstep :
        (((k % n + n + shadowShift n
            (shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩)) % (2 * n) = 0) ∨
          ((k % n + n + shadowShift n
            (shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩)) % (2 * n) = n)) ↔
        (((k % n + shadowShift n
            (shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩)) % (2 * n) = 0) ∨
          ((k % n + shadowShift n
            (shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩)) % (2 * n) = n)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (boundary_add_n_iff n
          (k % n + shadowShift n (shadowPerm n hn ⟨k % n, Nat.mod_lt _ (by omega)⟩))
          (by omega)).symm
    have hkmod : (k % n + n) % n = k % n := mod_add_period n (k % n) (by omega)
      (Nat.mod_lt _ (by omega))
    rw [hk_eq]
    simpa [hkmod] using hstep.mpr
      (shadowPerm_first_half_boundary n hn (k % n) (Nat.mod_lt _ (by omega)))

/-! ### Shadow configuration construction -/

/-- A shadow config s_k is defined by:
    s_k[i] = v_i  if 1 ≤ ((k + d_i) mod 2n) ≤ n
    s_k[i] = 0    otherwise

    This is the waterfall indicator with processor-dependent shift d_i.
    The shift breaks the alignment with the good cycle, producing
    configurations not in the good cycle. -/
structure ShadowConstruction (wc : WaterfallCycle sys) where
  /-- Number of shadow configs (= 2n) -/
  len : Nat
  len_eq : len = 2 * sys.rs.n
  /-- The shadow configurations -/
  configs : Fin len → Config sys.rs
  /-- Shadow formula: value at position i in shadow config k -/
  formula : ∀ (k : Fin len) (i : Fin sys.rs.n),
    let d := shadowShift sys.rs.n i
    let idx := (k.val + d) % (2 * sys.rs.n)
    if 1 ≤ idx ∧ idx ≤ sys.rs.n
    then configs k i = wc.highVal i
    else configs k i = ⟨0, by have := sys.rs.m_pos i; omega⟩

/-- The detection set D = {0} ∪ {2,...,n-2} ∪ {n+1} ∪ {2n-1}.
    Used for the distinctness proof: D^c has only three maximal runs,
    and shifting by n maps each run into D. -/
def detectionSet (n : Nat) (j : Fin (2 * n)) : Bool :=
  j.val = 0 ∨ (2 ≤ j.val ∧ j.val ≤ n - 2) ∨ j.val = n + 1 ∨ j.val = 2 * n - 1

/-! ### Shadow shift properties -/

theorem shadowShift_lt (n : Nat) (hn : 5 ≤ n) (i : Fin n) :
    shadowShift n i < 2 * n := by
  unfold shadowShift
  have := i.isLt
  split_ifs with h1 h2 h3 h4 <;> omega

private lemma two_n_mod_self (n : Nat) : 2 * n % (2 * n) = 0 := Nat.mod_self _

/-! ### Shadow active interval -/

/-- Active interval membership: j is in the active interval of shift d
    iff 1 ≤ (j + d) % (2n) ≤ n. -/
def shadowActive (n : Nat) (j d : Nat) : Prop :=
  1 ≤ (j + d) % (2 * n) ∧ (j + d) % (2 * n) ≤ n

instance (n j d : Nat) : Decidable (shadowActive n j d) := by
  unfold shadowActive; exact instDecidableAnd

/-- For j ∈ [2, n-2] and i ∈ [0, n-5], the linear shift d = n-2-i gives:
    shadowActive n j d ↔ j ≤ i + 2. -/
theorem linear_shift_lower (n j i : Nat) (hn : 5 ≤ n)
    (hj_lo : 2 ≤ j) (hj_hi : j ≤ n - 2) (hi : i ≤ n - 5) :
    shadowActive n j (shadowShift n ⟨i, by omega⟩) ↔ (j ≤ i + 2) := by
  unfold shadowActive shadowShift
  simp only [show (⟨i, _⟩ : Fin n).val = i from rfl, show i ≤ n - 5 from hi, ite_true]
  rw [Nat.mod_eq_of_lt (by omega : j + (n - 2 - i) < 2 * n)]
  constructor
  · intro ⟨_, hub⟩; omega
  · intro h; constructor <;> omega

/-- For j ∈ [n+2, 2n-2] and i ∈ [0, n-5], the linear shift d = n-2-i gives:
    shadowActive n j d ↔ n + 3 + i ≤ j. -/
theorem linear_shift_upper (n j i : Nat) (hn : 5 ≤ n)
    (hj_lo : n + 2 ≤ j) (hj_hi : j ≤ 2 * n - 2) (hi : i ≤ n - 5) :
    shadowActive n j (shadowShift n ⟨i, by omega⟩) ↔ (n + 3 + i ≤ j) := by
  unfold shadowActive shadowShift
  simp only [show (⟨i, _⟩ : Fin n).val = i from rfl, show i ≤ n - 5 from hi, ite_true]
  constructor
  · intro ⟨h_lb, h_ub⟩
    by_cases hlt : j + (n - 2 - i) < 2 * n
    · rw [Nat.mod_eq_of_lt hlt] at h_ub; omega
    · by_cases heq : j + (n - 2 - i) = 2 * n
      · rw [heq, two_n_mod_self] at h_lb; omega
      · have hgt : j + (n - 2 - i) > 2 * n := by omega
        have hval : j + (n - 2 - i) - 2 * n < 2 * n := by omega
        rw [show j + (n - 2 - i) = (j + (n - 2 - i) - 2 * n) + 1 * (2 * n) from by omega,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hval] at h_lb h_ub
        omega
  · intro hge
    have hval : j - (n + 2 + i) < 2 * n := by omega
    rw [show j + (n - 2 - i) = (j - (n + 2 + i)) + 1 * (2 * n) from by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hval]
    constructor <;> omega

/-! ### Shadow-waterfall disjointness infrastructure -/

/-- Shadow active at position n-4 (shift 0): active iff 1 ≤ k ≤ n. -/
theorem shadow_n4_active (n k : Nat) (hn : 5 ≤ n) (hk : k < 2 * n) :
    (1 ≤ (k + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) ∧
     (k + shadowShift n ⟨n - 4, by omega⟩) % (2 * n) ≤ n) ↔ (1 ≤ k ∧ k ≤ n) := by
  unfold shadowShift
  have : ¬(n - 4 ≤ n - 5) := by omega
  simp [this, Nat.mod_eq_of_lt hk]

/-- Shadow active at position n-3 (shift n+1): active iff n ≤ k. -/
theorem shadow_n3_active (n k : Nat) (hn : 5 ≤ n) (hk : k < 2 * n) :
    (1 ≤ (k + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) ∧
     (k + shadowShift n ⟨n - 3, by omega⟩) % (2 * n) ≤ n) ↔ (n ≤ k) := by
  unfold shadowShift
  have h1 : ¬(n - 3 ≤ n - 5) := by omega
  have h2 : ¬(n - 3 = n - 4) := by omega
  simp [h1, h2]
  constructor
  · intro ⟨h_lb, h_ub⟩
    by_contra h_lt; push_neg at h_lt
    by_cases h_eq : k + (n + 1) = 2 * n
    · rw [h_eq, two_n_mod_self] at h_lb; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h_ub; omega
  · intro hge
    rw [show k + (n + 1) = (k - n + 1) + 1 * (2 * n) from by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega

/-- Shadow active at position n-2 (shift 2): active iff k ≤ n-2 or k = 2n-1. -/
theorem shadow_n2_active (n k : Nat) (hn : 5 ≤ n) (hk : k < 2 * n) :
    (1 ≤ (k + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) ∧
     (k + shadowShift n ⟨n - 2, by omega⟩) % (2 * n) ≤ n) ↔ (k ≤ n - 2 ∨ k = 2 * n - 1) := by
  unfold shadowShift
  have h1 : ¬(n - 2 ≤ n - 5) := by omega
  have h2 : ¬(n - 2 = n - 4) := by omega
  have h3 : ¬(n - 2 = n - 3) := by omega
  simp [h1, h2, h3]
  constructor
  · intro ⟨h_lb, h_ub⟩
    by_cases hlt : k + 2 < 2 * n
    · rw [Nat.mod_eq_of_lt hlt] at h_lb h_ub; left; omega
    · by_cases heq : k + 2 = 2 * n
      · rw [heq, two_n_mod_self] at h_lb; omega
      · rw [show k + 2 = (k + 2 - 2 * n) + 1 * (2 * n) from by omega,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at h_lb h_ub
        right; omega
  · intro h
    rcases h with h | h
    · rw [Nat.mod_eq_of_lt (by omega : k + 2 < 2 * n)]; constructor <;> omega
    · subst h
      rw [show 2 * n - 1 + 2 = 1 + 1 * (2 * n) from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      constructor <;> omega

/-- Shadow active at position n-1 (shift 2n-1): active iff 2 ≤ k ≤ n+1. -/
theorem shadow_n1_active (n k : Nat) (hn : 5 ≤ n) (hk : k < 2 * n) :
    (1 ≤ (k + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) ∧
     (k + shadowShift n ⟨n - 1, by omega⟩) % (2 * n) ≤ n) ↔ (2 ≤ k ∧ k ≤ n + 1) := by
  unfold shadowShift
  have h1 : ¬(n - 1 ≤ n - 5) := by omega
  have h2 : ¬(n - 1 = n - 4) := by omega
  have h3 : ¬(n - 1 = n - 3) := by omega
  have h4 : ¬(n - 1 = n - 2) := by omega
  simp [h1, h2, h3, h4]
  constructor
  · intro ⟨h_lb, h_ub⟩
    by_cases hk1 : k ≤ 1
    · interval_cases k
      · rw [Nat.mod_eq_of_lt (by omega : 0 + (2 * n - 1) < 2 * n)] at h_ub; omega
      · rw [show 1 + (2 * n - 1) = 2 * n from by omega, two_n_mod_self] at h_lb; omega
    · push_neg at hk1
      rw [show k + (2 * n - 1) = (k - 1) + 1 * (2 * n) from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at h_lb h_ub
      omega
  · intro ⟨hge2, hle⟩
    rw [show k + (2 * n - 1) = (k - 1) + 1 * (2 * n) from by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega

/-- Waterfall active at position i: active iff i+1 ≤ j ≤ i+n. -/
theorem waterfall_active_iff (n j iv : Nat) (hn : 5 ≤ n)
    (hj : j < 2 * n) (hi : iv < n) :
    (1 ≤ (j + 2 * n - iv) % (2 * n) ∧ (j + 2 * n - iv) % (2 * n) ≤ n) ↔
    (iv + 1 ≤ j ∧ j ≤ iv + n) := by
  constructor
  · intro ⟨h_lb, h_ub⟩
    by_cases hjlt : j < iv
    · rw [Nat.mod_eq_of_lt (by omega : j + 2 * n - iv < 2 * n)] at h_ub; omega
    · by_cases hjeq : j = iv
      · subst hjeq
        have : j + 2 * n - j = 2 * n := by omega
        rw [this, two_n_mod_self] at h_lb; omega
      · rw [show j + 2 * n - iv = (j - iv) + 1 * (2 * n) from by omega,
            Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at h_lb h_ub
        omega
  · intro ⟨hge, hle⟩
    rw [show j + 2 * n - iv = (j - iv) + 1 * (2 * n) from by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega

private theorem active_add_n_iff_not (n x : Nat) (hn : 0 < n) :
    (1 ≤ ((x + n) % (2 * n)) ∧ ((x + n) % (2 * n) ≤ n)) ↔
      ¬ (1 ≤ x % (2 * n) ∧ x % (2 * n) ≤ n) := by
  set r := x % (2 * n)
  have h2n : 0 < 2 * n := by omega
  have hr : r < 2 * n := by
    dsimp [r]
    exact Nat.mod_lt _ h2n
  have hmod :
      (x + n) % (2 * n) = (r + n) % (2 * n) := by
    dsimp [r]
    have hx := Nat.mod_add_div x (2 * n)
    calc
      (x + n) % (2 * n)
          = ((x % (2 * n) + (2 * n) * (x / (2 * n))) + n) % (2 * n) := by
              rw [hx]
      _ = ((x % (2 * n) + n) + (x / (2 * n)) * (2 * n)) % (2 * n) := by
            ac_rfl
      _ = (x % (2 * n) + n) % (2 * n) := by
            rw [Nat.add_mul_mod_self_right]
  rw [hmod]
  change
    (1 ≤ (r + n) % (2 * n) ∧ (r + n) % (2 * n) ≤ n) ↔
      ¬ (1 ≤ r ∧ r ≤ n)
  by_cases hr0 : r = 0
  · rw [hr0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    constructor <;> intro h <;> omega
  · by_cases hrlt : r < n
    · have hrpos : 1 ≤ r := by omega
      rw [Nat.mod_eq_of_lt (by omega : r + n < 2 * n)]
      constructor <;> intro h <;> omega
    · by_cases hrn : r = n
      · rw [hrn, show n + n = 2 * n by omega, Nat.mod_self]
        constructor <;> intro h <;> omega
      · have hrgt : n < r := by omega
        rw [show r + n = (r - n) + 1 * (2 * n) from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        constructor <;> intro h <;> omega

theorem shadowActive_add_n_iff_not (n k d : Nat) (hn : 0 < n) :
    shadowActive n (k + n) d ↔ ¬ shadowActive n k d := by
  unfold shadowActive
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (active_add_n_iff_not n (k + d) hn)


/-- The 4-position pattern incompatibility: the shadow 4-tuple at positions
    (n-4, n-3, n-2, n-1) is always different from the waterfall 4-tuple.
    Shadow patterns: {FFTF, TFTF, TFTT, TFFT, TTFT, FTFT, FTFF, FTTF}.
    Waterfall patterns: {FFFF, TFFF, TTFF, TTTF, TTTT, FTTT, FFTT, FFFT}.
    These sets are disjoint. -/
private theorem shadow_waterfall_incompatible (n : Nat) (hn : 5 ≤ n)
    (k j : Nat) (hk : k < 2 * n) (hj : j < 2 * n)
    (h4 : (1 ≤ k ∧ k ≤ n) ↔ (n - 3 ≤ j ∧ j ≤ 2 * n - 4))
    (h3 : n ≤ k ↔ (n - 2 ≤ j ∧ j ≤ 2 * n - 3))
    (h2 : (k ≤ n - 2 ∨ k = 2 * n - 1) ↔ (n - 1 ≤ j ∧ j ≤ 2 * n - 2))
    (h1 : (2 ≤ k ∧ k ≤ n + 1) ↔ (n ≤ j ∧ j ≤ 2 * n - 1)) :
    False := by
  by_cases hkn : n ≤ k
  · have hj3 : n - 2 ≤ j ∧ j ≤ 2 * n - 3 := h3.mp hkn
    by_cases hk2n : k = 2 * n - 1
    · have hj2 : n - 1 ≤ j ∧ j ≤ 2 * n - 2 := h2.mp (Or.inr hk2n)
      have : ¬(n ≤ j ∧ j ≤ 2 * n - 1) := by rw [← h1]; push_neg; omega
      omega
    · have : ¬(n - 1 ≤ j ∧ j ≤ 2 * n - 2) := by rw [← h2]; push_neg; omega
      have hjeq : j = n - 2 := by omega
      subst hjeq
      have : ¬(2 ≤ k ∧ k ≤ n + 1) := by rw [h1]; omega
      have : 1 ≤ k ∧ k ≤ n ↔ (n - 3 ≤ n - 2 ∧ n - 2 ≤ 2 * n - 4) := h4
      omega
  · push_neg at hkn
    have hj3_false : ¬(n - 2 ≤ j ∧ j ≤ 2 * n - 3) := by rw [← h3]; omega
    by_cases hkn2 : k ≤ n - 2
    · have hj2 : n - 1 ≤ j ∧ j ≤ 2 * n - 2 := h2.mp (Or.inl hkn2)
      have hjeq : j = 2 * n - 2 := by omega
      subst hjeq
      have : ¬(1 ≤ k ∧ k ≤ n) := by rw [h4]; omega
      have : (2 ≤ k ∧ k ≤ n + 1) ↔ (n ≤ 2 * n - 2 ∧ 2 * n - 2 ≤ 2 * n - 1) := h1
      omega
    · have hkeq : k = n - 1 := by omega
      subst hkeq
      have : ¬(n - 1 ≤ n - 2 ∨ n - 1 = 2 * n - 1) := by omega
      have hj2_false : ¬(n - 1 ≤ j ∧ j ≤ 2 * n - 2) := by rw [← h2]; exact this
      have hj1 : n ≤ j ∧ j ≤ 2 * n - 1 := h1.mp (by omega)
      have hjeq : j = 2 * n - 1 := by omega
      subst hjeq
      have : 1 ≤ n - 1 ∧ n - 1 ≤ n ↔ (n - 3 ≤ 2 * n - 1 ∧ 2 * n - 1 ≤ 2 * n - 4) := h4
      omega

/-! ### Shadow shift separates -/

set_option maxHeartbeats 3200000 in
/-- The key separation lemma for distinctness:
    For any j₁ ≠ j₂ with j₁, j₂ < 2n and n ≥ 5,
    there exists a processor i such that exactly one of
    j₁, j₂ is in the active interval at shift d_i.

    Proof: use 4 special positions to separate most pairs,
    then linear shifts for interior elements.
    The 4 shifts (0, n+1, 2, 2n-1) at positions (n-4, n-3, n-2, n-1)
    separate all singleton classes. The remaining multi-element classes
    [2,n-2] and [n+2,2n-2] are separated by linear shifts d = n-2-i
    for i ∈ [0, n-5]. -/
theorem shadow_shift_separates (n : Nat) (hn5 : 5 ≤ n)
    (j₁ j₂ : Nat) (hj₁ : j₁ < 2 * n) (hj₂ : j₂ < 2 * n) (hne : j₁ ≠ j₂) :
    ∃ i : Fin n, ¬(shadowActive n j₁ (shadowShift n i) ↔
                    shadowActive n j₂ (shadowShift n i)) := by
  by_cases hsep0 : shadowActive n j₁ (shadowShift n ⟨n - 4, by omega⟩) ↔
                    shadowActive n j₂ (shadowShift n ⟨n - 4, by omega⟩)
  · by_cases hsep1 : shadowActive n j₁ (shadowShift n ⟨n - 1, by omega⟩) ↔
                      shadowActive n j₂ (shadowShift n ⟨n - 1, by omega⟩)
    · by_cases hsep2 : shadowActive n j₁ (shadowShift n ⟨n - 2, by omega⟩) ↔
                        shadowActive n j₂ (shadowShift n ⟨n - 2, by omega⟩)
      · by_cases hsep3 : shadowActive n j₁ (shadowShift n ⟨n - 3, by omega⟩) ↔
                          shadowActive n j₂ (shadowShift n ⟨n - 3, by omega⟩)
        · -- All 4 special positions agree → j₁, j₂ in same multi-element class.
          -- Reduce to non-mod conditions.
          unfold shadowActive at hsep0 hsep1 hsep2 hsep3
          rw [shadow_n4_active n j₁ hn5 hj₁, shadow_n4_active n j₂ hn5 hj₂] at hsep0
          rw [shadow_n1_active n j₁ hn5 hj₁, shadow_n1_active n j₂ hn5 hj₂] at hsep1
          rw [shadow_n2_active n j₁ hn5 hj₁, shadow_n2_active n j₂ hn5 hj₂] at hsep2
          rw [shadow_n3_active n j₁ hn5 hj₁, shadow_n3_active n j₂ hn5 hj₂] at hsep3
          -- Determine the class using case analysis.
          by_cases hj1_lo : j₁ < n
          · -- j₁ < n. By hsep3: j₂ < n.
            have hj2_lo : j₂ < n := by
              by_contra h; push_neg at h; exact absurd (hsep3.mpr h) (by omega)
            -- Both < n. Singleton classes {0},{1},{n-1} separated by hsep0/hsep1/hsep2.
            -- Multi-element class [2, n-2].
            by_cases hj1_ge2 : 2 ≤ j₁
            · by_cases hj1_le : j₁ ≤ n - 2
              · -- j₁ ∈ [2, n-2]. By hsep1/hsep2, j₂ ∈ [2, n-2].
                have hj2_ge2 : 2 ≤ j₂ := by
                  by_contra h; push_neg at h
                  exact absurd (hsep1.mp ⟨by omega, by omega⟩) (by omega)
                have hj2_le : j₂ ≤ n - 2 := by
                  by_contra h; push_neg at h
                  have : j₂ = n - 1 := by omega
                  exact absurd (hsep2.mp (Or.inl hj1_le)) (by omega)
                -- Both in [2, n-2]. Use linear shift.
                by_cases hlt : j₁ < j₂
                · exact ⟨⟨j₁ - 2, by omega⟩, by
                    rw [linear_shift_lower n j₁ (j₁ - 2) hn5 hj1_ge2 hj1_le (by omega),
                        linear_shift_lower n j₂ (j₁ - 2) hn5 hj2_ge2 hj2_le (by omega)]
                    simp only [not_iff]; omega⟩
                · exact ⟨⟨j₂ - 2, by omega⟩, by
                    rw [linear_shift_lower n j₁ (j₂ - 2) hn5 hj1_ge2 hj1_le (by omega),
                        linear_shift_lower n j₂ (j₂ - 2) hn5 hj2_ge2 hj2_le (by omega)]
                    simp only [not_iff]; omega⟩
              · -- j₁ = n-1. Singleton. j₂ = n-1 by hsep2. Contradicts hne.
                have : ¬(j₁ ≤ n - 2 ∨ j₁ = 2 * n - 1) := by omega
                have : ¬(j₂ ≤ n - 2 ∨ j₂ = 2 * n - 1) := fun h => absurd (hsep2.mpr h) this
                omega
            · -- j₁ ≤ 1. j₂ ≤ 1 by hsep1. Then hsep0 forces j₁ = j₂. Contradicts hne.
              have hj2_small : j₂ ≤ 1 := by
                by_contra h; push_neg at h
                exact absurd (hsep1.mpr ⟨by omega, by omega⟩) (by omega)
              -- j₁, j₂ ∈ {0,1}, j₁ ≠ j₂. hsep0: (1≤j₁∧j₁≤n) ↔ (1≤j₂∧j₂≤n).
              -- j₁=0,j₂=1: False↔True. j₁=1,j₂=0: True↔False. Both contradictions.
              interval_cases j₁ <;> interval_cases j₂ <;> simp_all
          · -- j₁ ≥ n (upper half). By hsep3: j₂ ≥ n.
            push_neg at hj1_lo
            have hj2_hi : n ≤ j₂ := hsep3.mp hj1_lo
            -- Singleton classes {n},{n+1},{2n-1}. Multi-element [n+2, 2n-2].
            by_cases hj1_le_n1 : j₁ ≤ n + 1
            · -- j₁ ∈ {n, n+1}. j₂ ∈ {n, n+1} by hsep1.
              have hj2_le_n1 : j₂ ≤ n + 1 := by
                have := hsep1.mp ⟨by omega, hj1_le_n1⟩; omega
              -- hsep0 forces j₁ = j₂. Contradicts hne.
              by_cases h : j₁ = n
              · have := hsep0.mp ⟨by omega, by omega⟩; omega
              · have : j₁ = n + 1 := by omega
                have : ¬(1 ≤ j₂ ∧ j₂ ≤ n) := by rw [← hsep0]; omega
                omega
            · push_neg at hj1_le_n1
              have hj2_ge : j₂ ≥ n + 2 := by
                by_contra h; push_neg at h
                exact absurd (hsep1.mpr ⟨by omega, by omega⟩) (by omega)
              -- hsep2: j₁ = 2n-1 ↔ j₂ = 2n-1 (since both > n-2).
              by_cases hj1_eq : j₁ = 2 * n - 1
              · have : j₂ ≤ n - 2 ∨ j₂ = 2 * n - 1 := hsep2.mp (Or.inr hj1_eq)
                omega -- j₂ = 2n-1 = j₁, contradicts hne
              · have hj1_hi : j₁ ≤ 2 * n - 2 := by omega
                have hj2_ne : j₂ ≠ 2 * n - 1 := by
                  intro h; exact absurd (hsep2.mpr (Or.inr h)) (by omega)
                have hj2_hi : j₂ ≤ 2 * n - 2 := by omega
                -- Both in [n+2, 2n-2]. Use linear shift.
                by_cases hlt : j₁ < j₂
                · exact ⟨⟨j₁ - n - 2, by omega⟩, by
                    rw [linear_shift_upper n j₁ (j₁ - n - 2) hn5 (by omega) hj1_hi (by omega),
                        linear_shift_upper n j₂ (j₁ - n - 2) hn5 (by omega) hj2_hi (by omega)]
                    simp only [not_iff]; omega⟩
                · exact ⟨⟨j₂ - n - 2, by omega⟩, by
                    rw [linear_shift_upper n j₁ (j₂ - n - 2) hn5 (by omega) hj1_hi (by omega),
                        linear_shift_upper n j₂ (j₂ - n - 2) hn5 (by omega) hj2_hi (by omega)]
                    simp only [not_iff]; omega⟩
        · exact ⟨⟨n - 3, by omega⟩, hsep3⟩
      · exact ⟨⟨n - 2, by omega⟩, hsep2⟩
    · exact ⟨⟨n - 1, by omega⟩, hsep1⟩
  · exact ⟨⟨n - 4, by omega⟩, hsep0⟩

/-! ### Shadow Cycle Mirror Theorem components -/

theorem shadow_len_pos {wc : WaterfallCycle sys}
    (sc : ShadowConstruction wc) : 0 < sc.len := by
  rw [sc.len_eq]; have := sys.rs.n_ge_4; omega

/-- The canonical shadow configuration at step `k`, given directly by the
    shift formula. -/
def canonicalShadowConfig (wc : WaterfallCycle sys) (k : Fin (2 * sys.rs.n)) :
    Config sys.rs :=
  fun i =>
    if shadowActive sys.rs.n k.val (shadowShift sys.rs.n i) then
      wc.highVal i
    else
      ⟨0, by have := sys.rs.m_pos i; omega⟩

/-- The canonical shadow construction packaged as a `ShadowConstruction`. -/
def canonicalShadowConstruction (wc : WaterfallCycle sys) : ShadowConstruction wc where
  len := 2 * sys.rs.n
  len_eq := rfl
  configs := canonicalShadowConfig wc
  formula := by
    intro k i
    by_cases h :
        1 ≤ (k.val + shadowShift sys.rs.n i) % (2 * sys.rs.n) ∧
          (k.val + shadowShift sys.rs.n i) % (2 * sys.rs.n) ≤ sys.rs.n
    · simp [canonicalShadowConfig, shadowActive, h]
    · simp [canonicalShadowConfig, shadowActive, h]

/-- Property (i): Closure — the mover entry at s_k transitions to s_{k+1 mod 2n}.
    The proof uses the 6-case analysis of the shadow permutation σ
    to show that firing processor σ(k mod n) at config s_k produces s_{k+1}. -/
def shadowClosure {wc : WaterfallCycle sys} (sc : ShadowConstruction wc) : Prop :=
  ∀ (k : Fin sc.len),
    ∃ p : Fin sys.rs.n,
      privileged sys (sc.configs k) p ∧
      sc.configs ⟨(k.val + 1) % sc.len, Nat.mod_lt _ (shadow_len_pos sc)⟩ =
        move sys (sc.configs k) p

/-- Property (ii): Movers — the mover at step k is processor σ(k mod n). -/
def shadowMovers {wc : WaterfallCycle sys} (sc : ShadowConstruction wc)
    (hn : 5 ≤ sys.rs.n) : Prop :=
  ∀ (k : Fin sc.len),
    let kmod : Fin sys.rs.n := ⟨k.val % sys.rs.n, Nat.mod_lt _ (by omega)⟩
    privileged sys (sc.configs k) (shadowPerm sys.rs.n hn kmod)

/-- Property (iii): Distinctness — all 2n shadow configs are distinct.
    Proved via the detection set D: D^c has three maximal runs of lengths
    1, 1, 1. Shifting by n maps each run into D, so no two shadow configs
    can agree at all positions. -/
def shadowDistinct {wc : WaterfallCycle sys} (sc : ShadowConstruction wc) : Prop :=
  ∀ (j₁ j₂ : Fin sc.len), sc.configs j₁ = sc.configs j₂ → j₁ = j₂

/-- Property (iv): Disjointness — no shadow config is a good config.
    Proved by examining positions n-4, n-3, n-2, n-1: good configs have
    staircase patterns while shadow configs have non-staircase patterns. -/
def shadowDisjoint {wc : WaterfallCycle sys} (sc : ShadowConstruction wc) : Prop :=
  ∀ (k : Fin sc.len), sc.configs k ∉ wc.configs

/-- Property (v): Each shadow config has a unique privileged processor. -/
def shadowSinglePriv {wc : WaterfallCycle sys} (sc : ShadowConstruction wc) : Prop :=
  ∀ (k : Fin sc.len), singlePrivileged sys (sc.configs k)

/-! ### Shadow-waterfall disjointness proof -/

set_option maxHeartbeats 1600000 in
/-- No shadow config can equal any waterfall (good cycle) config.
    Proved by showing the 4-position active patterns at (n-4, n-3, n-2, n-1)
    are disjoint between shadow and waterfall. -/
theorem shadow_not_waterfall (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n)
    (k : Nat) (hk : k < 2 * sys.rs.n)
    (j : Fin wc.configs.length)
    (heq : ∀ i : Fin sys.rs.n,
      (let d := shadowShift sys.rs.n i
       let idx := (k + d) % (2 * sys.rs.n)
       if 1 ≤ idx ∧ idx ≤ sys.rs.n
       then wc.highVal i
       else ⟨0, by have := sys.rs.m_pos i; omega⟩) =
      (wc.configs.get j) i) :
    False := by
  set n := sys.rs.n with hn_def
  have hlen := wc.len_eq
  have hjlt : j.val < 2 * n := hn_def ▸ hlen ▸ j.isLt
  have hn5 : 5 ≤ n := hn_def ▸ hn
  have hk2 : k < 2 * n := hn_def ▸ hk
  suffices derive_iff : ∀ i : Fin n,
      (1 ≤ (k + shadowShift n i) % (2 * n) ∧ (k + shadowShift n i) % (2 * n) ≤ n) ↔
      (1 ≤ (j.val + 2 * n - i.val) % (2 * n) ∧ (j.val + 2 * n - i.val) % (2 * n) ≤ n) by
    have h_iff4 := derive_iff ⟨n - 4, by omega⟩
    have h_iff3 := derive_iff ⟨n - 3, by omega⟩
    have h_iff2 := derive_iff ⟨n - 2, by omega⟩
    have h_iff1 := derive_iff ⟨n - 1, by omega⟩
    rw [shadow_n4_active n k hn5 hk2,
        waterfall_active_iff n j.val (n - 4) hn5 hjlt (by omega)] at h_iff4
    rw [shadow_n3_active n k hn5 hk2,
        waterfall_active_iff n j.val (n - 3) hn5 hjlt (by omega)] at h_iff3
    rw [shadow_n2_active n k hn5 hk2,
        waterfall_active_iff n j.val (n - 2) hn5 hjlt (by omega)] at h_iff2
    rw [shadow_n1_active n k hn5 hk2,
        waterfall_active_iff n j.val (n - 1) hn5 hjlt (by omega)] at h_iff1
    exact shadow_waterfall_incompatible n hn5 k j.val hk2 hjlt
      (by convert h_iff4 using 2 <;> omega)
      (by convert h_iff3 using 2 <;> omega)
      (by convert h_iff2 using 2 <;> omega)
      (by convert h_iff1 using 2 <;> omega)
  intro i
  have heqi := heq (hn_def ▸ i)
  have hwi := wc.waterfall j (hn_def ▸ i)
  simp only [] at heqi hwi
  split_ifs at heqi with hshad
  · split_ifs at hwi with hwat
    · exact ⟨fun _ => hwat, fun _ => hshad⟩
    · exfalso; rw [hwi] at heqi
      exact wc.highVal_pos (hn_def ▸ i) (congrArg Fin.val heqi)
  · split_ifs at hwi with hwat
    · exfalso; rw [hwi] at heqi
      exact wc.highVal_pos (hn_def ▸ i) (congrArg Fin.val heqi.symm)
    · exact ⟨fun h => absurd h hshad, fun h => absurd h hwat⟩

/-- The canonical shadow configurations are pairwise distinct. -/
theorem canonicalShadowDistinct (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) :
    shadowDistinct (canonicalShadowConstruction wc) := by
  intro j₁ j₂ heq
  by_cases h : j₁ = j₂
  · exact h
  · have hval : j₁.val ≠ j₂.val := fun hEq => h (Fin.ext hEq)
    obtain ⟨i, hsep⟩ := shadow_shift_separates sys.rs.n hn j₁.val j₂.val
      (by simpa [canonicalShadowConstruction] using j₁.isLt)
      (by simpa [canonicalShadowConstruction] using j₂.isLt) hval
    have heqi :
        (canonicalShadowConstruction wc).configs j₁ i =
          (canonicalShadowConstruction wc).configs j₂ i := congrFun heq i
    let A := shadowActive sys.rs.n j₁.val (shadowShift sys.rs.n i)
    let B := shadowActive sys.rs.n j₂.val (shadowShift sys.rs.n i)
    have hsep' : ¬(A ↔ B) := by
      simpa [A, B] using hsep
    by_cases hA : A <;> by_cases hB : B
    · exfalso
      exact hsep' (by simp [hA, hB])
    · exfalso
      simp [canonicalShadowConstruction, canonicalShadowConfig, A, B, hA, hB] at heqi
      exact wc.highVal_pos i (congrArg Fin.val heqi)
    · exfalso
      simp [canonicalShadowConstruction, canonicalShadowConfig, A, B, hA, hB] at heqi
      exact wc.highVal_pos i (congrArg Fin.val heqi.symm)
    · exfalso
      exact hsep' (by simp [hA, hB])

/-- No canonical shadow configuration is a good configuration from the
    waterfall cycle. -/
theorem canonicalShadowDisjoint (wc : WaterfallCycle sys) (hn : 5 ≤ sys.rs.n) :
    shadowDisjoint (canonicalShadowConstruction wc) := by
  intro k hk
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hk
  exact shadow_not_waterfall wc hn k.val
    (by simpa [canonicalShadowConstruction] using k.isLt)
    j
    (by
      intro i
      have hi := congrFun hj.symm i
      simpa [canonicalShadowConstruction, canonicalShadowConfig, shadowActive] using hi)

end LeanMn
