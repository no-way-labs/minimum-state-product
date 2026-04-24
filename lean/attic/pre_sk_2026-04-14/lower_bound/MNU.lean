/-
  MNU.lean — Mover Neighborhood Uniqueness and Universal Escape (Phase 5)

  Defines: waterfall structure, active intervals, MNU property,
  Universal Escape, shadow trap structure, and the master shadow invalidity theorem.

  The shadow invalidity theorem is the key structural lemma: if there exist
  2n non-good configurations forming a closed cycle under forced entries,
  no valid system exists.
-/
import LeanMn.LowerBound.GoodCycleBasics

namespace LeanMn

variable {sys : System}

/-! ### Active interval on Z_{2n} -/

/-- Active interval I_i = {i+1, i+2, ..., i+n} (mod 2n).
    j ∈ I_i iff 1 ≤ (j - i) mod 2n ≤ n.
    We use (j + 2n - i) % (2n) to avoid negative subtraction. -/
def inActiveInterval (n : Nat) (_hn : 0 < n) (i j : Fin (2 * n)) : Bool :=
  let d := (j.val + 2 * n - i.val) % (2 * n)
  1 ≤ d && d ≤ n

/-! ### Waterfall structure for uniform sweep cycles -/

/-- A uniform sweep cycle of length 2n in waterfall form.
    This captures the structural properties needed for MNU and shadow proofs. -/
structure WaterfallCycle (sys : System) extends GoodCycle sys where
  len_eq : configs.length = 2 * sys.rs.n
  /-- The "active" value for each processor (v_i).
      For binary: v_i = 1. For ternary: v_i can be 1 or 2. -/
  highVal : (i : Fin sys.rs.n) → Fin (sys.rs.m i)
  /-- The high value is nonzero. -/
  highVal_pos : ∀ i, (highVal i).val ≠ 0
  /-- Waterfall form: g_j[i] = v_i if j ∈ I_i, else g_j[i] = 0.
      I_i = {i+1, ..., i+n} mod 2n. Membership: 1 ≤ (j-i) mod 2n ≤ n. -/
  waterfall : ∀ (j : Fin configs.length) (i : Fin sys.rs.n),
    let d := (j.val + 2 * sys.rs.n - i.val) % (2 * sys.rs.n)
    if 1 ≤ d ∧ d ≤ sys.rs.n
    then (configs.get j) i = highVal i
    else (configs.get j) i = ⟨0, by have := sys.rs.m_pos i; omega⟩

/-! ### MNU (Mover Neighborhood Uniqueness) -/

/-- MNU property: for any mover step, the post-move triple (L, S', R) at the
    mover's three positions uniquely identifies which good config matches.
    Formally: if two good configs agree at the mover's neighborhood in the
    post-move config, they are the same config. -/
def hasMNU (gc : GoodCycle sys) : Prop :=
  ∀ (k : Fin gc.configs.length) (j₁ j₂ : Fin gc.configs.length),
    let p := gc.moverAt k
    let c' := move sys (gc.configs.get k) p
    (gc.configs.get j₁) (left p) = c' (left p) →
    (gc.configs.get j₁) p = c' p →
    (gc.configs.get j₁) (right p) = c' (right p) →
    (gc.configs.get j₂) (left p) = c' (left p) →
    (gc.configs.get j₂) p = c' p →
    (gc.configs.get j₂) (right p) = c' (right p) →
    j₁ = j₂

/-- Core arithmetic: the displacement d = (j - p) mod 2n is uniquely determined
    by three interval-membership constraints (same I_{p-1}, opposite I_p, same I_{p+1}).
    This is the heart of the MNU argument. -/
private lemma mnu_displacement_unique (n : Nat) (hn : n ≥ 4)
    (dk d1 d2 : Nat) (hdk : dk < 2 * n) (hd1 : d1 < 2 * n) (hd2 : d2 < 2 * n)
    -- d1 satisfies: same I_{p-1} as dk, opposite I_p, same I_{p+1}
    (h1L : (d1 ≤ n - 1) ↔ (dk ≤ n - 1))
    (h1S : (1 ≤ d1 ∧ d1 ≤ n) ↔ ¬(1 ≤ dk ∧ dk ≤ n))
    (h1R : (2 ≤ d1 ∧ d1 ≤ n + 1) ↔ (2 ≤ dk ∧ dk ≤ n + 1))
    -- d2 satisfies the same constraints
    (h2L : (d2 ≤ n - 1) ↔ (dk ≤ n - 1))
    (h2S : (1 ≤ d2 ∧ d2 ≤ n) ↔ ¬(1 ≤ dk ∧ dk ≤ n))
    (h2R : (2 ≤ d2 ∧ d2 ≤ n + 1) ↔ (2 ≤ dk ∧ dk ≤ n + 1)) :
    d1 = d2 := by
  omega

/-- Helper: move doesn't change non-mover positions. -/
private lemma move_ne (sys : System) (c : Config sys.rs) (p q : Fin sys.rs.n)
    (hne : q ≠ p) : move sys c p q = c q := by
  unfold move; simp [hne]

/-- Helper: left p ≠ p for n ≥ 4. -/
private lemma left_ne_self (n : Nat) (hn : 4 ≤ n) (p : Fin n) : left p ≠ p := by
  intro h; exact absurd (congrArg Fin.val h) (by
    simp only [left_val]
    have hp := p.isLt
    by_cases hp0 : p.val = 0
    · rw [hp0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [show p.val + n - 1 = (p.val - 1) + n from by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]; omega)

/-- Helper: right p ≠ p for n ≥ 4. -/
private lemma right_ne_self (n : Nat) (hn : 4 ≤ n) (p : Fin n) : right p ≠ p := by
  intro h; exact absurd (congrArg Fin.val h) (by
    simp only [right_val]
    have hp := p.isLt
    by_cases hp1 : p.val + 1 < n
    · rw [Nat.mod_eq_of_lt hp1]; omega
    · rw [show p.val + 1 = n from by omega, Nat.mod_self]; omega)

/-- Helper: waterfall value equality implies same active-interval membership. -/
private lemma waterfall_mem_iff (wc : WaterfallCycle sys)
    (j₁ j₂ : Fin wc.configs.length) (i : Fin sys.rs.n)
    (heq : (wc.configs.get j₁) i = (wc.configs.get j₂) i) :
    let n := sys.rs.n
    let d₁ := (j₁.val + 2 * n - i.val) % (2 * n)
    let d₂ := (j₂.val + 2 * n - i.val) % (2 * n)
    (1 ≤ d₁ ∧ d₁ ≤ n) ↔ (1 ≤ d₂ ∧ d₂ ≤ n) := by
  simp only []
  have hw₁ := wc.waterfall j₁ i
  have hw₂ := wc.waterfall j₂ i
  dsimp only at hw₁ hw₂
  split_ifs at hw₁ with h₁ <;> split_ifs at hw₂ with h₂
  · exact ⟨fun _ => h₂, fun _ => h₁⟩
  · exfalso; rw [hw₁, hw₂] at heq
    exact wc.highVal_pos i (congrArg Fin.val heq)
  · exfalso; rw [hw₁, hw₂] at heq
    exact wc.highVal_pos i (congrArg Fin.val heq.symm)
  · exact ⟨fun h => absurd h h₁, fun h => absurd h h₂⟩

/-- Helper: waterfall values gj[p] ≠ gk[p] implies opposite active-interval membership. -/
private lemma waterfall_ne_mem (wc : WaterfallCycle sys)
    (j k : Fin wc.configs.length) (i : Fin sys.rs.n)
    (hne : (wc.configs.get j) i ≠ (wc.configs.get k) i) :
    let n := sys.rs.n
    let dj := (j.val + 2 * n - i.val) % (2 * n)
    let dk := (k.val + 2 * n - i.val) % (2 * n)
    (1 ≤ dj ∧ dj ≤ n) ↔ ¬(1 ≤ dk ∧ dk ≤ n) := by
  simp only []
  have hwj := wc.waterfall j i
  have hwk := wc.waterfall k i
  dsimp only at hwj hwk
  split_ifs at hwj with hj <;> split_ifs at hwk with hk
  · exfalso; exact hne (hwj ▸ hwk ▸ rfl)
  · exact ⟨fun _ => hk, fun _ => hj⟩
  · exact ⟨fun h => absurd h hj, fun h => absurd hk h⟩
  · exfalso; exact hne (hwj ▸ hwk ▸ rfl)

set_option maxHeartbeats 1600000 in
/-- MNU index uniqueness: if a and b have opposite I_p membership to k,
    and same I_{left p} and I_{right p} membership as k, then a = b.
    Bridges from waterfall membership conditions to mnu_displacement_unique. -/
private lemma mnu_index_unique (n : Nat) (hn4 : 4 ≤ n)
    (a b kv pv lv rv : Nat)
    (ha : a < 2 * n) (hb : b < 2 * n) (hkv : kv < 2 * n)
    (hpv : pv < n) (hlv : lv < n) (hrv : rv < n)
    -- a: same at left p, opposite at p, same at right p (relative to k)
    (hSa : (1 ≤ (a + 2 * n - pv) % (2 * n) ∧ (a + 2 * n - pv) % (2 * n) ≤ n) ↔
           ¬(1 ≤ (kv + 2 * n - pv) % (2 * n) ∧ (kv + 2 * n - pv) % (2 * n) ≤ n))
    (hLa : (1 ≤ (a + 2 * n - lv) % (2 * n) ∧ (a + 2 * n - lv) % (2 * n) ≤ n) ↔
           (1 ≤ (kv + 2 * n - lv) % (2 * n) ∧ (kv + 2 * n - lv) % (2 * n) ≤ n))
    (hRa : (1 ≤ (a + 2 * n - rv) % (2 * n) ∧ (a + 2 * n - rv) % (2 * n) ≤ n) ↔
           (1 ≤ (kv + 2 * n - rv) % (2 * n) ∧ (kv + 2 * n - rv) % (2 * n) ≤ n))
    -- b: same constraints
    (hSb : (1 ≤ (b + 2 * n - pv) % (2 * n) ∧ (b + 2 * n - pv) % (2 * n) ≤ n) ↔
           ¬(1 ≤ (kv + 2 * n - pv) % (2 * n) ∧ (kv + 2 * n - pv) % (2 * n) ≤ n))
    (hLb : (1 ≤ (b + 2 * n - lv) % (2 * n) ∧ (b + 2 * n - lv) % (2 * n) ≤ n) ↔
           (1 ≤ (kv + 2 * n - lv) % (2 * n) ∧ (kv + 2 * n - lv) % (2 * n) ≤ n))
    (hRb : (1 ≤ (b + 2 * n - rv) % (2 * n) ∧ (b + 2 * n - rv) % (2 * n) ≤ n) ↔
           (1 ≤ (kv + 2 * n - rv) % (2 * n) ∧ (kv + 2 * n - rv) % (2 * n) ≤ n))
    (hlv_adj : lv = pv - 1 ∨ (pv = 0 ∧ lv = n - 1))
    (hrv_adj : rv = pv + 1 ∨ (pv + 1 = n ∧ rv = 0)) :
    a = b := by
  -- Eliminate all % by case splitting on j < q for each (j,q) pair
  have elim : ∀ j q, j < 2 * n → q < n →
      (j + 2 * n - q) % (2 * n) = if j < q then j + 2 * n - q else j - q := by
    intro j q hj hq; split
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [show j + 2 * n - q = (j - q) + 1 * (2 * n) from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  -- Rewrite each hypothesis: a-terms in hSa/hLa/hRa, b-terms in hSb/hLb/hRb, k-terms in all
  rw [elim _ _ ha hpv, elim _ _ hkv hpv] at hSa
  rw [elim _ _ ha hlv, elim _ _ hkv hlv] at hLa
  rw [elim _ _ ha hrv, elim _ _ hkv hrv] at hRa
  rw [elim _ _ hb hpv, elim _ _ hkv hpv] at hSb
  rw [elim _ _ hb hlv, elim _ _ hkv hlv] at hLb
  rw [elim _ _ hb hrv, elim _ _ hkv hrv] at hRb
  rcases hlv_adj with hlv_eq | ⟨hp0, hlv_eq⟩ <;> rcases hrv_adj with hrv_eq | ⟨hpn, hrv_eq⟩ <;>
  subst_vars <;> split_ifs at hSa hSb hLa hLb hRa hRb <;> omega

theorem waterfallCycle_hasMNU (wc : WaterfallCycle sys) : hasMNU wc.toGoodCycle := by
  unfold hasMNU
  intro k j₁ j₂
  -- After ∀-vars, the goal has let p, let c', then 6 →'s
  simp only []
  intro hj₁L hj₁S hj₁R hj₂L hj₂S hj₂R
  -- gj₁ and gj₂ both match c' at left p, p, right p
  -- c' = move sys gk p, so c' agrees with gk at non-p positions
  set p := wc.toGoodCycle.moverAt k
  -- c'[q] = gk[q] for q ≠ p
  have hc'L : (move sys (wc.configs.get k) p) (left p) = (wc.configs.get k) (left p) :=
    move_ne sys (wc.configs.get k) p (left p) (left_ne_self sys.rs.n sys.rs.n_ge_4 p)
  have hc'R : (move sys (wc.configs.get k) p) (right p) = (wc.configs.get k) (right p) :=
    move_ne sys (wc.configs.get k) p (right p) (right_ne_self sys.rs.n sys.rs.n_ge_4 p)
  -- gj₁ and gj₂ agree with gk at left p and right p
  have heqL₁ : (wc.configs.get j₁) (left p) = (wc.configs.get k) (left p) := by
    rw [hj₁L, hc'L]
  have heqR₁ : (wc.configs.get j₁) (right p) = (wc.configs.get k) (right p) := by
    rw [hj₁R, hc'R]
  have heqL₂ : (wc.configs.get j₂) (left p) = (wc.configs.get k) (left p) := by
    rw [hj₂L, hc'L]
  have heqR₂ : (wc.configs.get j₂) (right p) = (wc.configs.get k) (right p) := by
    rw [hj₂R, hc'R]
  -- gj₁[p] ≠ gk[p] and gj₂[p] ≠ gk[p] (from move + privileged)
  have hpriv : privileged sys (wc.configs.get k) p := wc.toGoodCycle.moverAt_privileged k
  have hne_move : (move sys (wc.configs.get k) p) p ≠ (wc.configs.get k) p := by
    unfold move privileged at *; simp at *; exact hpriv
  have hne₁ : (wc.configs.get j₁) p ≠ (wc.configs.get k) p := by
    intro h; rw [h] at hj₁S; exact hne_move hj₁S.symm
  have hne₂ : (wc.configs.get j₂) p ≠ (wc.configs.get k) p := by
    intro h; rw [h] at hj₂S; exact hne_move hj₂S.symm
  -- Waterfall membership: same class at left p, right p; opposite at p
  have hmemL₁ := waterfall_mem_iff wc j₁ k (left p) heqL₁
  have hmemR₁ := waterfall_mem_iff wc j₁ k (right p) heqR₁
  have hmemL₂ := waterfall_mem_iff wc j₂ k (left p) heqL₂
  have hmemR₂ := waterfall_mem_iff wc j₂ k (right p) heqR₂
  have hmemS₁ := waterfall_ne_mem wc j₁ k p hne₁
  have hmemS₂ := waterfall_ne_mem wc j₂ k p hne₂
  -- hmemL₁: I_{left p} membership of j₁ ↔ I_{left p} membership of k
  -- hmemS₁: I_p membership of j₁ ↔ ¬(I_p membership of k)
  -- hmemR₁: I_{right p} membership of j₁ ↔ I_{right p} membership of k
  -- Same for j₂
  -- Strategy: j₁ and j₂ have identical membership at left p, right p,
  -- and identical opposite-to-k membership at p. These 3 constraints
  -- uniquely determine j mod 2n, so j₁ = j₂.
  have hn4 : 4 ≤ sys.rs.n := sys.rs.n_ge_4
  have hlen : wc.configs.length = 2 * sys.rs.n := wc.len_eq
  have hj₁lt : j₁.val < 2 * sys.rs.n := hlen ▸ j₁.isLt
  have hj₂lt : j₂.val < 2 * sys.rs.n := hlen ▸ j₂.isLt
  have hplt : p.val < sys.rs.n := p.isLt
  -- Apply mnu_index_unique to conclude j₁ = j₂
  apply Fin.ext
  simp only [left_val, right_val] at hmemL₁ hmemL₂ hmemR₁ hmemR₂
  exact mnu_index_unique sys.rs.n hn4 j₁.val j₂.val k.val p.val
    ((p.val + sys.rs.n - 1) % sys.rs.n) ((p.val + 1) % sys.rs.n)
    hj₁lt hj₂lt (hlen ▸ k.isLt)
    hplt (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    hmemS₁ hmemL₁ hmemR₁ hmemS₂ hmemL₂ hmemR₂
    (by -- left p adjacency
      by_cases hp0 : p.val = 0
      · right; refine ⟨hp0, ?_⟩
        rw [hp0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      · left; rw [show p.val + sys.rs.n - 1 = (p.val - 1) + 1 * sys.rs.n from by omega,
                   Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)])
    (by -- right p adjacency
      by_cases hpn : p.val + 1 = sys.rs.n
      · right; exact ⟨hpn, by rw [hpn, Nat.mod_self]⟩
      · left; rw [Nat.mod_eq_of_lt (by omega)])

/-! ### Waterfall mover schedule -/

/-- Helper: the GoodCycle.closed field gives us the transition identity.
    At step k, the next config equals move(g_k, moverAt k). -/
private lemma gc_step_eq (gc : GoodCycle sys) (k : Fin gc.configs.length) :
    gc.configs.get (nextIndex gc.configs k) = move sys (gc.configs.get k) (gc.moverAt k) := by
  obtain ⟨i, hpriv, hstep⟩ := gc.closed k
  have : i = gc.moverAt k := gc.moverAt_unique k i hpriv
  rw [this] at hstep
  exact hstep

set_option maxHeartbeats 1600000 in
/-- **Waterfall mover schedule**: for a waterfall cycle, the mover at step k is
    processor (k mod n).

    Proof: at step k, the waterfall formula gives g_k[p] for p = k mod n.
    At the next step, g_{k+1}[p] has a different value (entry phase: 0 → highVal,
    exit phase: highVal → 0). Since move only changes the mover position,
    and g_k[p] ≠ g_{k+1}[p], processor p must be the mover. -/
theorem waterfall_moverAt_eq (wc : WaterfallCycle sys) (k : Fin wc.configs.length) :
    wc.toGoodCycle.moverAt k =
      ⟨k.val % sys.rs.n, Nat.mod_lt _ (by have := sys.rs.n_ge_4; omega)⟩ := by
  set n := sys.rs.n with hn_def
  have hn4 : 4 ≤ n := sys.rs.n_ge_4
  have hlen : wc.configs.length = 2 * n := wc.len_eq
  have hklt : k.val < 2 * n := hlen ▸ k.isLt
  -- Define p = k mod n
  set p : Fin n := ⟨k.val % n, Nat.mod_lt _ (by omega)⟩ with hp_def
  -- Strategy: show g_k[p] ≠ g_{next}[p], then since move only changes the mover,
  -- p must be the mover. Use moverAt_unique to conclude.
  suffices h_ne : (wc.configs.get k) p ≠
      (wc.configs.get (nextIndex wc.configs k)) p by
    -- From closed, ∃ i privileged with g_{next} = move(g_k, i)
    obtain ⟨i, hpriv_i, hstep_i⟩ := wc.toGoodCycle.closed k
    have hi_eq : i = wc.toGoodCycle.moverAt k := wc.toGoodCycle.moverAt_unique k i hpriv_i
    -- g_{next}[p] = move(g_k, i)[p]
    have hstep_p : (wc.configs.get (nextIndex wc.configs k)) p =
        (move sys (wc.configs.get k) i) p := congr_fun hstep_i p
    -- If p ≠ i, move doesn't change p, so g_{next}[p] = g_k[p], contradicting h_ne
    by_cases hpi : p = i
    · -- p = i = moverAt k, done
      rw [← hi_eq, ← hpi]
    · -- p ≠ i, so move(g_k, i)[p] = g_k[p], contradiction
      exfalso; apply h_ne
      rw [hstep_p, move_ne sys (wc.configs.get k) i p hpi]
  -- Now prove g_k[p] ≠ g_{next}[p] using the waterfall formula.
  -- Step 1: compute displacement d_k = (k + 2n - p) % 2n for g_k at position p.
  have hw_k := wc.waterfall k p
  -- Step 2: compute displacement for g_{next} at position p.
  have hw_next := wc.waterfall (nextIndex wc.configs k) p
  -- Simplify the if-then-else in hw_k and hw_next.
  dsimp only at hw_k hw_next
  -- d_k = (k.val + 2*n - (k.val % n)) % (2*n)
  -- Case split: k < n (entry phase) vs k ≥ n (exit phase)
  by_cases hk_lo : k.val < n
  · -- Entry phase: k < n, so p = k % n = k.
    have hp_eq : p.val = k.val := by simp [hp_def, Nat.mod_eq_of_lt hk_lo]
    -- d_k = (k + 2n - k) % 2n = 2n % 2n = 0
    have hd_k : (k.val + 2 * n - p.val) % (2 * n) = 0 := by
      rw [hp_eq, show k.val + 2 * n - k.val = 2 * n from by omega, Nat.mod_self]
    -- 0 is NOT in [1,n], so g_k[p] = 0
    have hcond_k : ¬(1 ≤ (k.val + 2 * n - p.val) % (2 * n) ∧
        (k.val + 2 * n - p.val) % (2 * n) ≤ n) := by rw [hd_k]; omega
    rw [if_neg hcond_k] at hw_k
    -- next = (k+1) % 2n. Since k < n < 2n, next = k+1.
    have hnext_val : (nextIndex wc.configs k).val = k.val + 1 := by
      unfold nextIndex; simp only []
      exact Nat.mod_eq_of_lt (by omega)
    -- d_next = (k+1 + 2n - k) % 2n = (2n+1) % 2n = 1
    have hd_next : ((nextIndex wc.configs k).val + 2 * n - p.val) % (2 * n) = 1 := by
      rw [hnext_val, hp_eq,
          show k.val + 1 + 2 * n - k.val = 1 + 2 * n from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 1 < 2 * n)]
    -- 1 is in [1,n], so g_{next}[p] = highVal p
    have hcond_next : 1 ≤ ((nextIndex wc.configs k).val + 2 * n - p.val) % (2 * n) ∧
        ((nextIndex wc.configs k).val + 2 * n - p.val) % (2 * n) ≤ n := by
      rw [hd_next]; omega
    rw [if_pos hcond_next] at hw_next
    -- g_k[p] = 0, g_{next}[p] = highVal p. These differ by highVal_pos.
    rw [hw_k, hw_next]
    intro h
    exact wc.highVal_pos p (congrArg Fin.val h.symm)
  · -- Exit phase: k ≥ n.
    push_neg at hk_lo
    -- p = k % n = k - n
    have hp_eq : p.val = k.val - n := by
      show k.val % n = k.val - n
      conv_lhs => rw [show k.val = (k.val - n) + n from by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : k.val - n < n)]
    -- d_k = (k + 2n - (k-n)) % 2n = (k + 2n - k + n) % 2n = 3n % 2n = n
    have hd_k : (k.val + 2 * n - p.val) % (2 * n) = n := by
      rw [hp_eq, show k.val + 2 * n - (k.val - n) = n + 2 * n from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : n < 2 * n)]
    -- n is in [1,n], so g_k[p] = highVal p
    have hcond_k : 1 ≤ (k.val + 2 * n - p.val) % (2 * n) ∧
        (k.val + 2 * n - p.val) % (2 * n) ≤ n := by rw [hd_k]; omega
    rw [if_pos hcond_k] at hw_k
    -- next = (k+1) % 2n.
    -- Case split on whether k = 2n-1 (wrap-around) or not.
    by_cases hk_last : k.val = 2 * n - 1
    · -- k = 2n-1, next = 0
      have hnext_val : (nextIndex wc.configs k).val = 0 := by
        simp [nextIndex]
        rw [show k.val + 1 = 2 * n from by omega, hlen, Nat.mod_self]
      -- p = k - n = 2n-1-n = n-1
      have hp_eq2 : p.val = n - 1 := by rw [hp_eq, hk_last]; omega
      -- d_next = (0 + 2n - (n-1)) % 2n = (n+1) % 2n = n+1
      have hd_next : ((nextIndex wc.configs k).val + 2 * n - p.val) % (2 * n) = n + 1 := by
        rw [hnext_val, hp_eq2]
        rw [Nat.mod_eq_of_lt (by omega : 0 + 2 * n - (n - 1) < 2 * n)]
        omega
      -- n+1 > n, so NOT in [1,n]
      have hcond_next : ¬(1 ≤ ((nextIndex wc.configs k).val + 2 * n - p.val) % (2 * n) ∧
          ((nextIndex wc.configs k).val + 2 * n - p.val) % (2 * n) ≤ n) := by
        rw [hd_next]; omega
      rw [if_neg hcond_next] at hw_next
      -- g_k[p] = highVal p, g_{next}[p] = 0. Differ by highVal_pos.
      rw [hw_k, hw_next]
      intro h
      exact wc.highVal_pos p (congrArg Fin.val h)
    · -- k ≥ n and k < 2n-1, so next = k+1
      have hnext_val : (nextIndex wc.configs k).val = k.val + 1 := by
        unfold nextIndex; simp only []
        exact Nat.mod_eq_of_lt (by omega)
      -- d_next = (k+1 + 2n - (k-n)) % 2n = (3n+1) % 2n = n+1
      have hd_next : ((nextIndex wc.configs k).val + 2 * n - p.val) % (2 * n) = n + 1 := by
        rw [hnext_val, hp_eq,
            show k.val + 1 + 2 * n - (k.val - n) = (n + 1) + 2 * n from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : n + 1 < 2 * n)]
      -- n+1 > n, so NOT in [1,n]
      have hcond_next : ¬(1 ≤ ((nextIndex wc.configs k).val + 2 * n - p.val) % (2 * n) ∧
          ((nextIndex wc.configs k).val + 2 * n - p.val) % (2 * n) ≤ n) := by
        rw [hd_next]; omega
      rw [if_neg hcond_next] at hw_next
      -- g_k[p] = highVal p, g_{next}[p] = 0. Differ by highVal_pos.
      rw [hw_k, hw_next]
      intro h
      exact wc.highVal_pos p (congrArg Fin.val h)

/-! ### Universal Escape -/

/-- Universal Escape: no forced move at any non-good configuration can enter
    the good cycle. -/
def hasEscape (gc : GoodCycle sys) : Prop :=
  ∀ (c : Config sys.rs) (p : Fin sys.rs.n),
    c ∉ gc.configs →
    privileged sys c p →
    move sys c p ∉ gc.configs

/- Waterfall cycles have Universal Escape.

    NOTE: This theorem as currently stated (for arbitrary WaterfallCycle
    without constraints on the transition function at non-good configs) is
    NOT provable in general. Counterexample: at n=4 with all binary procs,
    the config c = (0, v₁, v₂, 0) is not good, privileged at proc 0 if
    f₀(0,0,v₁) = v₀ ≠ 0, and move(c,0) = g₃ ∈ good. The transition
    f₀(0,0,v₁) is unconstrained by the good cycle (context (0,0,v₁) never
    appears at proc 0 in any good config).

    The shadow cycle mirror theorem (shadow_cycle_mirror_theorem) does NOT
    depend on this theorem — it constructs the shadow trap directly from
    the shadow construction properties (closure, distinctness, disjointness,
    single-priv). The escape property is therefore not needed for the main
    lower bound result.

    If escape is needed for other purposes, the WaterfallCycle definition
    should be strengthened with a constraint on the transition function,
    e.g., requiring that f maps non-waterfall values to non-waterfall
    values at every (L,R) context appearing in the good cycle.

    This statement is intentionally left unimplemented because it is false for
    arbitrary `WaterfallCycle` under the current definition, and it is also
    unused by the present lower-bound development. -/

/-! ### Shadow Trap -/

/-- A shadow trap: a set of non-good configurations forming a closed cycle
    under forced transitions. The adversary can loop through these forever,
    preventing convergence. -/
structure ShadowTrap (sys : System) (gc : GoodCycle sys) where
  /-- The shadow configurations. -/
  configs : List (Config sys.rs)
  /-- The shadow configs are nonempty. -/
  nonempty : configs ≠ []
  /-- Every shadow config is NOT a good config. -/
  disjoint : ∀ c ∈ configs, c ∉ gc.configs
  /-- The shadow cycle is closed: firing the privileged processor goes to
      the next shadow config. -/
  closed : ∀ (k : Fin configs.length),
    ∃ i, privileged sys (configs.get k) i ∧
      configs.get (nextIndex configs k) = move sys (configs.get k) i
  /-- All shadow configs are distinct. -/
  distinct : configs.Nodup

/-- Every shadow config has a badStep to the next shadow config. -/
private theorem shadowTrap_badStep (gc : GoodCycle sys) (st : ShadowTrap sys gc)
    (k : Fin st.configs.length) :
    badStep sys gc
      (st.configs.get (nextIndex st.configs k))
      (st.configs.get k) := by
  refine ⟨st.disjoint _ (List.get_mem _ _), st.disjoint _ (List.get_mem _ _), ?_⟩
  obtain ⟨i, hpriv, hstep⟩ := st.closed k
  exact ⟨i, hpriv, hstep⟩

/-- If a configuration lies in the shadow trap and is Acc for badStep,
    then so is the next config (and the next, and the next...).
    By cycling back to the start with a strictly smaller Acc proof,
    we get a contradiction. -/
private theorem shadowTrap_acc_false (gc : GoodCycle sys) (st : ShadowTrap sys gc)
    (c : Config sys.rs) (hacc : Acc (badStep sys gc) c)
    (hmem : ∃ k : Fin st.configs.length, st.configs.get k = c) : False := by
  induction hacc with
  | intro x _ ih =>
    obtain ⟨k, hk⟩ := hmem
    have hbad := shadowTrap_badStep gc st k
    rw [hk] at hbad
    exact ih _ hbad ⟨nextIndex st.configs k, rfl⟩

theorem shadowTrap_not_converges (gc : GoodCycle sys) (st : ShadowTrap sys gc) :
    ¬converges sys gc := by
  intro hconv
  have hlen_pos : 0 < st.configs.length := by
    cases h : st.configs with
    | nil => exact absurd h st.nonempty
    | cons _ _ => simp
  exact shadowTrap_acc_false gc st _ (hconv.apply _) ⟨⟨0, hlen_pos⟩, rfl⟩

/-! ### Counting Lemma (Case 1) -/

/-- Counting Lemma (Claim 4.2.1): if at most 2 processors are binary,
    the product is ≥ 4·3^(n-2). -/
private theorem pow_mul_pow_ge (b n : Nat) (hn : 4 ≤ n) (hb : b ≤ 2) (hbn : b ≤ n) :
    2 ^ b * 3 ^ (n - b) ≥ 4 * 3 ^ (n - 2) := by
  interval_cases b
  · -- b=0: 3^n ≥ 4·3^(n-2). Since 3^n = 9·3^(n-2) and 9 ≥ 4.
    simp
    calc 3 ^ n = 3 ^ ((n - 2) + 2) := by congr 1; omega
      _ = 3 ^ (n - 2) * 3 ^ 2 := pow_add 3 (n - 2) 2
      _ = 9 * 3 ^ (n - 2) := by ring
      _ ≥ 4 * 3 ^ (n - 2) := Nat.mul_le_mul_right _ (by omega)
  · -- b=1: 2·3^(n-1) ≥ 4·3^(n-2). Since 2·3^(n-1) = 6·3^(n-2).
    simp
    calc 2 * 3 ^ (n - 1) = 2 * 3 ^ ((n - 2) + 1) := by congr 2; omega
      _ = 2 * (3 ^ (n - 2) * 3) := by rw [pow_succ]
      _ = 6 * 3 ^ (n - 2) := by ring
      _ ≥ 4 * 3 ^ (n - 2) := Nat.mul_le_mul_right _ (by omega)
  · -- b=2: 4·3^(n-2) ≥ 4·3^(n-2). Exact.
    simp

theorem counting_lemma (rs : RingSpec) (h : binaryCount rs ≤ 2) :
    stateProduct rs ≥ 4 * 3 ^ (rs.n - 2) := by
  unfold stateProduct
  -- Lower bound: each m_i ≥ 3 for non-binary, ≥ 2 for binary
  -- So ∏ m_i ≥ ∏ (if binary then 2 else 3) = 2^b * 3^(n-b)
  have hprod : ∏ i : Fin rs.n, rs.m i ≥
      ∏ i : Fin rs.n, if rs.m i = 2 then 2 else 3 := by
    apply Finset.prod_le_prod'
    intro i _
    split_ifs with h
    · exact h ▸ le_refl _
    · have := rs.m_pos i; omega
  have hmid : (∏ i : Fin rs.n, (if rs.m i = 2 then 2 else 3)) ≥
      2 ^ (binaryCount rs) * 3 ^ (rs.n - binaryCount rs) := by
    -- Product splitting: ∏ (if binary then 2 else 3) = 2^b * 3^(n-b)
    suffices heq : (∏ i : Fin rs.n, (if rs.m i = 2 then (2 : ℕ) else 3)) =
        2 ^ binaryCount rs * 3 ^ (rs.n - binaryCount rs) by omega
    have h1 : (∏ i : Fin rs.n, (if rs.m i = 2 then (2 : ℕ) else 3)) =
        2 ^ (Finset.univ.filter (fun i : Fin rs.n => rs.m i = 2)).card *
        3 ^ (Finset.univ.filter (fun i : Fin rs.n => ¬rs.m i = 2)).card := by
      simp only [Finset.prod_ite, Finset.prod_const]
    rw [h1]
    unfold binaryCount
    have hcf := @Finset.card_filter_add_card_filter_not (Fin rs.n)
      (Finset.univ) (fun i => rs.m i = 2) _ _
    simp only [Finset.card_univ, Fintype.card_fin] at hcf
    congr 1; congr 1; omega
  have hfin := pow_mul_pow_ge (binaryCount rs) rs.n rs.n_ge_4 h (by
    unfold binaryCount
    exact le_trans (Finset.card_filter_le _ _) (by simp))
  exact le_trans hfin (le_trans hmid hprod)

/-- Contrapositive: sub-threshold implies ≥ 3 binary processors. -/
theorem subThreshold_ge3_binary (rs : RingSpec) (h : subThreshold rs) :
    hasGe3Binary rs := by
  by_contra hlt
  unfold hasGe3Binary at hlt
  push_neg at hlt
  have : binaryCount rs ≤ 2 := by omega
  have := counting_lemma rs this
  unfold subThreshold at h
  omega

end LeanMn
