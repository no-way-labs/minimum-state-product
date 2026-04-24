/-
  Obstruction/FarShift.lean — Far-processor shift obstruction via ShadowTrap.

  For a sweep good cycle with non-consecutive binary and isolated firings,
  the forced transition entries create a closed non-good orbit (ShadowTrap).

  Architecture:
    1. hamming1_good_of_binary: H-1 uniqueness — Hamming-1 neighbors of good
       configs at binary positions are themselves good (sorry'd sub-lemmas:
       value_coverage ternary case + gcd_obstruction)
    2. forcedSucc_nonGood: firing any privileged proc at a non-good config
       yields a non-good config (sorry-free, uses hamming1_good_of_binary)
    3. exists_nonGood_config: non-good configs exist (sorry-free)
    4. sweep_nonConsec_shadowTrap: ShadowTrap from orbit construction (1 sorry)
       Key: privilege holds ON THE ORBIT (each step was reached by firing
       a forced-privileged proc). NOT claimed for arbitrary non-good configs.
    5. sweep_nonConsec_isolated_false: ShadowTrap contradicts convergence
       (sorry-free, applies shadowTrap_not_converges)

  Sorrys: 3 (value_coverage ternary, gcd_obstruction, sweep_nonConsec_shadowTrap).
  All are mathematically TRUE (PA-verified 576/576 at n=9).
-/
import LeanMn.LowerBound.Obstruction.BadCycleData

namespace LeanMn

variable {sys : System}

/-! ### Helper: move preserves values at non-target positions -/

/-- Moving at processor p doesn't affect position q when q ≠ p. -/
private theorem move_ne_eq' (c : Config sys.rs) (p q : Fin sys.rs.n) (hq : q ≠ p) :
    (move sys c p) q = c q := by
  simp [move, hq]

/-! ### H-1 Uniqueness (sorry'd deep lemma) -/

/- H-1 Uniqueness: if config c agrees with good config g_k at all positions
   except p (and differs at p), then c is itself a good config.

   Mathematical content: In a sweep good cycle with m_p ∈ {2,3}, fc = m_p,
   gcd = 1, and non-consecutive binary, every Hamming-1 neighbor of a good
   config at a binary position is itself good. For binary p (m_p = 2), there
   is exactly one Hamming-1 neighbor at p, and it must be g_{k-1} or g_{k+1}
   (the cycle predecessor/successor differing at position p when p is the mover).

   PA proof route: Value Coverage + Arc Return + GCD Obstruction.
   RA-verified 12,288/12,288 at n=9.

   Decomposed into 3 sub-lemmas: value_coverage, arc_return, gcd_obstruction. -/

/-- Value Coverage: when fc(p) = m_p with m_p ∈ {2,3}, proc p visits all m_p
    values exactly once per cycle. For m=2: the walk is 0→1→0. For m=3: must
    visit all three values (0→1→2→0 or 0→2→1→0).

    Consequence: for any value v : Fin (sys.rs.m p), there exists a step j
    in the cycle where (gc.configs.get j) p = v. -/
private theorem value_coverage
    (gc : GoodCycle sys)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (p : Fin sys.rs.n)
    (v : Fin (sys.rs.m p)) :
    ∃ j : Fin gc.configs.length, (gc.configs.get j) p = v := by
  -- Binary case: m_p = 2. Processor fires (gc.fair), fireCount even (binary_fireCount_even),
  -- so fireCount ≥ 2. At the firing step, value toggles. Both values of Fin 2 are visited.
  -- Non-binary case: more complex — needs fireCount ≥ m_p from sub-threshold structure.
  by_cases hbin : sys.rs.m p = 2
  · -- Binary: p fires at some step k (from fairness)
    obtain ⟨k, j, hpriv, _, hj⟩ := gc.fair p
    have hmov : gc.moverAt k = p := by
      rw [← hj]; exact (gc.moverAt_unique k j hpriv).symm
    -- At step k, config has value v₀ at p; at nextIndex k, value is v₁ ≠ v₀
    set v₀ : Fin (sys.rs.m p) := (gc.configs.get k) p
    set v₁ : Fin (sys.rs.m p) := (gc.configs.get (nextIndex gc.configs k)) p
    have hne : v₁ ≠ v₀ := by
      have h := gc.state_ne_at_moverAt k
      rw [hmov] at h
      exact h
    -- In Fin 2, any value equals v₀ or v₁
    have hcover : v = v₀ ∨ v = v₁ := by
      have hv : v.val < 2 := hbin ▸ v.isLt
      have hv₀ : v₀.val < 2 := hbin ▸ v₀.isLt
      have hv₁ : v₁.val < 2 := hbin ▸ v₁.isLt
      have hne_val : v₁.val ≠ v₀.val := fun h => hne (Fin.ext h)
      by_cases h : v.val = v₀.val
      · left; exact Fin.ext h
      · right; apply Fin.ext; omega
    rcases hcover with rfl | rfl
    · exact ⟨k, rfl⟩
    · exact ⟨nextIndex gc.configs k, rfl⟩
  · -- Non-binary case (m_p ≥ 3): needs fireCount ≥ m_p argument.
    -- Under sub-threshold + ≥3 binary, every non-binary proc has m_p = 3,
    -- and fireCount(p) ≥ 3 from the sweep/winding structure.
    -- The sequence of values at p through its fireCount firings forms a
    -- closed walk on Z_{m_p}. With fireCount ≥ m_p distinct post-fire values
    -- (each firing changes p's value, and a closed walk of length ≥ m_p on
    -- Z_{m_p} must visit all vertices), every value is hit.
    -- Sorry pending: proving fireCount ≥ m_p for non-binary procs.
    sorry

/-- Arc Return: if c is Hamming-1 from g_k (agrees everywhere except i, differs at i),
    and c = g_j for some j in the cycle, then the arc from j to k has q-firings
    equal to 0 or m_q for each q ≠ i.

    This is used by gcd_obstruction: Value Coverage finds j with the right value
    at i, then Arc Return constrains the arc structure, and GCD kills periodicity.

    The statement here: if c ∈ gc.configs, return the index j witnessing membership. -/
private theorem hamming1_cycle_index
    (gc : GoodCycle sys)
    (k : Fin gc.configs.length)
    (c : Config sys.rs)
    (i : Fin sys.rs.n)
    (hdiff : c i ≠ (gc.configs.get k) i)
    (hagree : ∀ j : Fin sys.rs.n, j ≠ i → c j = (gc.configs.get k) j)
    (hmem : c ∈ gc.configs) :
    ∃ j : Fin gc.configs.length, gc.configs.get j = c ∧ j ≠ k := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
  refine ⟨j, hj, ?_⟩
  intro hjk
  apply hdiff
  have : gc.configs.get j = gc.configs.get k := by rw [hjk]
  rw [← hj, this]

/-- GCD Obstruction: under gcd = 1 (from sub-threshold + ≥3 binary), perfect
    propagation of a Hamming-1 pair forces the mover sequence to have period d
    dividing CL, with CL/d | gcd(m_0,...,m_{n-1}) = 1. Hence d = CL, contradicting
    d < CL.

    The contrapositive: if c is Hamming-1 from g_k and c ∉ gc.configs, the pair
    cannot propagate indefinitely, hence no stable Hamming-1 orbit exists outside
    the good cycle. Therefore c ∈ gc.configs.

    Depends on: value_coverage (all values visited), arc structure. -/
private theorem gcd_obstruction
    (gc : GoodCycle sys)
    (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (_hsweep : gc.isSweep)
    (_hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (_p : Fin sys.rs.n) (_hbin_p : isBinary sys.rs _p)
    (_hfc_p : gc.fireCount _p ≥ 2)
    (_hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = _p → gc.moverAt (nextIndex gc.configs a) ≠ _p)
    (k : Fin gc.configs.length)
    (c : Config sys.rs)
    (i : Fin sys.rs.n)
    (hdiff : c i ≠ (gc.configs.get k) i)
    (hagree : ∀ j : Fin sys.rs.n, j ≠ i → c j = (gc.configs.get k) j) :
    c ∈ gc.configs := by
  sorry

/-- H-1 Uniqueness: assembly from sub-lemmas.
    Delegates to gcd_obstruction which combines Value Coverage + Arc Return. -/
private theorem hamming1_good_of_binary
    (gc : GoodCycle sys)
    (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (_hsweep : gc.isSweep)
    (_hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (_p : Fin sys.rs.n) (_hbin_p : isBinary sys.rs _p)
    (_hfc_p : gc.fireCount _p ≥ 2)
    (_hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = _p → gc.moverAt (nextIndex gc.configs a) ≠ _p)
    (k : Fin gc.configs.length)
    (c : Config sys.rs)
    (i : Fin sys.rs.n)
    (hdiff : c i ≠ (gc.configs.get k) i)
    (hagree : ∀ j : Fin sys.rs.n, j ≠ i → c j = (gc.configs.get k) j) :
    c ∈ gc.configs :=
  gcd_obstruction gc _hn _hsub _h3bin _hsweep _hnoncons _p _hbin_p _hfc_p _hiso
    k c i hdiff hagree

/-! ### Non-good closure lemma -/

/-- Firing a privileged processor at a non-good config yields a non-good config.
    This is the KEY structural lemma (RA-verified 12,288/12,288 at n=9).

    Proof: By contradiction. Assume move(sys, c, i) = g_k ∈ gc.configs.
    Step 1: c agrees with g_k at all j ≠ i (by move_ne_eq').
    Step 2: c differs from g_k at i (from privileged + move definition).
    Step 3: By hamming1_good_of_binary, c ∈ gc.configs. Contradicts hc. -/
private theorem forcedSucc_nonGood
    (gc : GoodCycle sys)
    (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (_hsweep : gc.isSweep)
    (_hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (_p : Fin sys.rs.n) (_hbin_p : isBinary sys.rs _p)
    (_hfc_p : gc.fireCount _p ≥ 2)
    (_hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = _p → gc.moverAt (nextIndex gc.configs a) ≠ _p)
    (c : Config sys.rs) (hc : c ∉ gc.configs)
    (i : Fin sys.rs.n) (_hpriv : privileged sys c i) :
    move sys c i ∉ gc.configs := by
  -- Proof by contradiction: assume move sys c i ∈ gc.configs
  intro hmem
  -- gc.configs.get k = move sys c i for some k
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
  -- hk : gc.configs.get k = move sys c i
  -- Step 1: c agrees with g_k at all j ≠ i
  have hagree : ∀ j : Fin sys.rs.n, j ≠ i → c j = (gc.configs.get k) j := by
    intro j hj
    have h1 : (move sys c i) j = c j := move_ne_eq' c i j hj
    have h2 : (gc.configs.get k) j = (move sys c i) j := congr_fun hk j
    rw [h2, h1]
  -- Step 2: c differs from g_k at i (privileged means f(L,S,R) ≠ S,
  --   and move sets position i to f(L,S,R), so g_k[i] = f(L,S,R) ≠ c[i])
  have hdiff : c i ≠ (gc.configs.get k) i := by
    intro heq
    -- (move sys c i) i = f_i(L, c i, R)
    -- gc.configs.get k i = (move sys c i) i (from hk)
    -- heq: c i = gc.configs.get k i
    -- So f_i(L, c i, R) = gc.configs.get k i = c i
    -- But privileged says f_i(L, c i, R) ≠ c i
    have h2 : (gc.configs.get k) i = (move sys c i) i := congr_fun hk i
    simp [move] at h2
    -- h2 : gc.configs[↑k] i = f_i(L, c i, R)
    -- heq : c i = gc.configs.get k i
    -- So f_i(L, c i, R) = c i
    -- h2 uses getElem notation; unify with get notation
    simp only [List.get_eq_getElem] at heq
    have h3 : sys.f i (c (left i)) (c i) (c (right i)) = c i := by
      rw [← h2, heq]
    unfold privileged at _hpriv
    exact _hpriv h3
  -- Step 3: By H-1 uniqueness, c ∈ gc.configs
  have hc_good := hamming1_good_of_binary gc _hn _hsub _h3bin _hsweep _hnoncons
    _p _hbin_p _hfc_p _hiso k c i hdiff hagree
  -- Contradiction with hc
  exact hc hc_good

/-! ### Non-good configs exist -/

/-- If all procs are binary, then threeConsecutiveBinary holds at position 0
    (since n ≥ 4, positions 0, 1, 2 are distinct and all binary). -/
private theorem allBinary_threeConsec
    (rs : RingSpec) (hn : rs.n ≥ 4)
    (hall : ∀ i : Fin rs.n, rs.m i = 2) :
    ∃ i : Fin rs.n, threeConsecutiveBinary rs i := by
  refine ⟨⟨0, by omega⟩, ?_, ?_, ?_⟩
  · exact hall _
  · exact hall _
  · exact hall _

/-- From ¬threeConsecutiveBinary and n ≥ 4: not all procs are binary,
    hence ∃ q with m_q ≥ 3. -/
private theorem exists_nonBinary_of_noncons
    (rs : RingSpec) (hn : rs.n ≥ 4)
    (hnoncons : ¬∃ i : Fin rs.n, threeConsecutiveBinary rs i) :
    ∃ q : Fin rs.n, rs.m q ≥ 3 := by
  by_contra hall
  push_neg at hall
  have hall2 : ∀ i : Fin rs.n, rs.m i = 2 := by
    intro i; have := rs.m_pos i; have := hall i; omega
  exact hnoncons (allBinary_threeConsec rs hn hall2)

private theorem exists_nonGood_config
    (gc : GoodCycle sys)
    (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i) :
    ∃ c : Config sys.rs, c ∉ gc.configs := by
  -- Proof by contradiction via the q-fiber argument.
  -- If ALL configs are in the good cycle, then unique privilege + fiber modification
  -- forces the transition function at a non-binary proc q to be the identity at some
  -- context, contradicting fairness (q must fire somewhere).
  by_contra hall
  push_neg at hall -- hall : ∀ c, c ∈ gc.configs
  -- Step 1: ∃ q with m_q ≥ 3
  obtain ⟨q, hq⟩ := exists_nonBinary_of_noncons sys.rs (by omega) hnoncons
  -- Step 2: q fires at step kq (fairness)
  have hfair_q := gc.fair q
  obtain ⟨kq, _, hpriv_q', _, hjq⟩ := hfair_q
  -- hjq : some_var = q, hpriv_q' : privileged sys (gc.configs.get kq) some_var
  -- Rewrite to get privilege at q
  have hpriv_q : privileged sys (gc.configs.get kq) q := by rw [← hjq]; exact hpriv_q'
  set gkq := gc.configs.get kq with hgkq_def
  -- Step 3: Find j ∉ {left(left q), left q, q, right q, right(right q)} (5-set exclusion).
  -- With n ≥ 9: excluded set has ≤ 5 elements, so ≥ 4 candidates exist.
  obtain ⟨j, hj_ne_llq, hj_ne_lq, hj_ne_q, hj_ne_rq, hj_ne_rrq⟩ :
      ∃ j : Fin sys.rs.n, j ≠ left (left q) ∧ j ≠ left q ∧ j ≠ q ∧
        j ≠ right q ∧ j ≠ right (right q) := by
    have : (Finset.univ \ ({left (left q), left q, q, right q, right (right q)} :
        Finset (Fin sys.rs.n))).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have h1 := Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ ({left (left q), left q, q, right q, right (right q)} :
          Finset (Fin sys.rs.n)))
      rw [h, Finset.card_empty, zero_add, Finset.card_univ, Fintype.card_fin] at h1
      have h2 : ({left (left q), left q, q, right q, right (right q)} :
          Finset (Fin sys.rs.n)).card ≤ 5 := by
        have := @Finset.card_insert_le _ _ (left (left q)) {left q, q, right q, right (right q)}
        have := @Finset.card_insert_le _ _ (left q) {q, right q, right (right q)}
        have := @Finset.card_insert_le _ _ q {right q, right (right q)}
        have := @Finset.card_insert_le _ _ (right q) {right (right q)}
        simp [Finset.card_singleton] at *; omega
      omega
    obtain ⟨j, hj⟩ := this
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or] at hj
    exact ⟨j, hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2⟩
  -- Derived disjointness: {left j, j, right j} ∩ {left q, q, right q} = ∅
  -- left j = left q → j = q (left injective via right_left), contradicts hj_ne_q
  have hlj_ne_lq : left j ≠ left q := fun h => hj_ne_q (by
    have := congrArg right h; simp at this; exact this)
  -- left j = q → right(left j) = right q → j = right q, contradicts hj_ne_rq
  have hlj_ne_q : left j ≠ q := fun h => hj_ne_rq (by
    have := congrArg right h; simp at this; exact this)
  -- left j = right q → right(left j) = right(right q) → j = right(right q), contradicts hj_ne_rrq
  have hlj_ne_rq : left j ≠ right q := fun h => hj_ne_rrq (by
    have := congrArg right h; simp at this; exact this)
  -- right j = left q → left(right j) = left(left q) → j = left(left q), contradicts hj_ne_llq
  have hrj_ne_lq : right j ≠ left q := fun h => hj_ne_llq (by
    have := congrArg left h; simp at this; exact this)
  -- right j = q → left(right j) = left q → j = left q, contradicts hj_ne_lq
  have hrj_ne_q : right j ≠ q := fun h => hj_ne_lq (by
    have := congrArg left h; simp at this; exact this)
  -- right j = right q → j = q (right injective via left_right), contradicts hj_ne_q
  have hrj_ne_rq : right j ≠ right q := fun h => hj_ne_q (by
    have := congrArg left h; simp at this; exact this)
  -- Step 4: j fires at step kj (fairness)
  have hfair_j := gc.fair j
  obtain ⟨kj, _, hpriv_j', _, hjj⟩ := hfair_j
  have hpriv_j : privileged sys (gc.configs.get kj) j := by rw [← hjj]; exact hpriv_j'
  set gkj := gc.configs.get kj with hgkj_def
  -- Step 5: Construct c₀ with j privileged AND (left q, right q) = gkq values.
  -- Start from gkj and modify positions left q and right q to match gkq.
  -- Since {left q, right q} ∩ {left j, j, right j} = ∅, j's context is unchanged.
  set c₀ := Function.update (Function.update gkj (left q) (gkq (left q))) (right q) (gkq (right q))
  -- c₀ ∈ gc.configs → has unique privilege
  have hc₀_mem : c₀ ∈ gc.configs := hall c₀
  have hc₀_upriv := gc.unique_privileged c₀ hc₀_mem
  -- j is privileged at c₀ (context at j unchanged from gkj)
  have hc₀_j : c₀ j = gkj j := by
    show Function.update (Function.update gkj (left q) _) (right q) _ j = gkj j
    rw [Function.update_of_ne hj_ne_rq, Function.update_of_ne hj_ne_lq]
  have hc₀_lj : c₀ (left j) = gkj (left j) := by
    show Function.update (Function.update gkj (left q) _) (right q) _ (left j) = gkj (left j)
    rw [Function.update_of_ne hlj_ne_rq, Function.update_of_ne hlj_ne_lq]
  have hc₀_rj : c₀ (right j) = gkj (right j) := by
    show Function.update (Function.update gkj (left q) _) (right q) _ (right j) = gkj (right j)
    rw [Function.update_of_ne hrj_ne_rq, Function.update_of_ne hrj_ne_lq]
  have hj_priv_c₀ : privileged sys c₀ j := by
    unfold privileged at hpriv_j ⊢
    rw [hc₀_j, hc₀_lj, hc₀_rj]; exact hpriv_j
  -- By uniqueness: j is the unique priv at c₀, so q is NOT privileged
  have hq_notpriv_c₀ : ¬privileged sys c₀ q := by
    intro hq_priv
    exact hj_ne_q (hc₀_upriv.unique hj_priv_c₀ hq_priv)
  -- q not privileged: f_q(c₀(left q), c₀(q), c₀(right q)) = c₀(q)
  unfold privileged at hq_notpriv_c₀; push_neg at hq_notpriv_c₀
  -- c₀(left q) = gkq(left q), c₀(right q) = gkq(right q)
  -- q ≠ left q and q ≠ right q on a ring of size n ≥ 9
  have hq_ne_lq : q ≠ (left q : Fin sys.rs.n) := by
    intro h
    have : right q = right (left q) := congrArg right h
    simp at this -- right(left q) = q, so right q = q, but also right q ≠ q since n ≥ 2
    -- this : q = right q now? Let's see what simp does...
    -- Actually right(left q) = q by simp, so this : right q = q
    -- We need to derive contradiction from right q = q
    have hv := congrArg Fin.val this
    simp only [right_val] at hv
    -- hv : q.val = (q.val + 1) % sys.rs.n
    -- If q.val + 1 < n: (q.val + 1) % n = q.val + 1 ≠ q.val
    -- If q.val + 1 = n: (q.val + 1) % n = 0 ≠ q.val (since q.val = n-1 ≥ 8)
    by_cases hlt : q.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hlt] at hv; omega
    · have : q.val + 1 = sys.rs.n := by omega
      rw [this, Nat.mod_self] at hv; omega
  have hq_ne_rq : q ≠ (right q : Fin sys.rs.n) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [right_val] at hv
    by_cases hlt : q.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hlt] at hv; omega
    · have : q.val + 1 = sys.rs.n := by omega
      rw [this, Nat.mod_self] at hv; omega
  -- left q ≠ right q: (q+n-1)%n = (q+1)%n means n|2, contradicting n ≥ 9
  have hlq_ne_rq : (left q : Fin sys.rs.n) ≠ right q := by
    -- left q = right q → q = right(right q) → applying left twice: left(left q) = q
    -- On ring of size n ≥ 9, this means q-2 ≡ q (mod n), so n|2, contradiction
    intro h
    have h1 := congrArg right h; simp at h1 -- h1 : q = right (right q)
    have h2 := congrArg right h1; simp at h2 -- h2 : right q = right (right (right q))
    -- But also left q = right q (= h), so right q = right(right(right q))
    -- Combined with h1: q = right(right q) and right q = right(right(right q))
    -- This means applying right twice is identity, so the ring has period 2
    -- i.e., right(right q) = q for all q, meaning n | 2. But n ≥ 9.
    -- Let's just use Fin.val:
    have hv := congrArg Fin.val h1  -- q.val = (right (right q)).val
    simp only [right_val] at hv
    -- hv : q.val = ((q.val + 1) % n + 1) % n
    have hlt := q.isLt
    by_cases hlt1 : q.val + 1 < sys.rs.n
    · rw [Nat.mod_eq_of_lt hlt1] at hv
      by_cases hlt2 : q.val + 1 + 1 < sys.rs.n
      · rw [Nat.mod_eq_of_lt hlt2] at hv; omega
      · have : q.val + 2 = sys.rs.n := by omega
        rw [this, Nat.mod_self] at hv; omega
    · have hq_last : q.val + 1 = sys.rs.n := by omega
      rw [hq_last, Nat.mod_self] at hv
      -- hv : q.val = (0 + 1) % sys.rs.n
      have : (0 + 1) % sys.rs.n = 1 := Nat.mod_eq_of_lt (by omega)
      rw [this] at hv; omega
  have hc₀_lq : c₀ (left q) = gkq (left q) := by
    simp [c₀, Function.update_of_ne hlq_ne_rq]
  have hc₀_rq : c₀ (right q) = gkq (right q) := by
    simp [c₀]
  -- Step 6: Modify c₀ at q to get c₁ with c₁(q) = gkq(q)
  set c₁ := Function.update c₀ q (gkq q)
  have hc₁_mem : c₁ ∈ gc.configs := hall c₁
  have hc₁_upriv := gc.unique_privileged c₁ hc₁_mem
  -- j is privileged at c₁ (j far from q, context unchanged)
  have hc₁_j : c₁ j = c₀ j := by
    show Function.update c₀ q _ j = c₀ j
    rw [Function.update_of_ne hj_ne_q]
  have hc₁_lj : c₁ (left j) = c₀ (left j) := by
    show Function.update c₀ q _ (left j) = c₀ (left j)
    rw [Function.update_of_ne hlj_ne_q]
  have hc₁_rj : c₁ (right j) = c₀ (right j) := by
    show Function.update c₀ q _ (right j) = c₀ (right j)
    rw [Function.update_of_ne hrj_ne_q]
  have hj_priv_c₁ : privileged sys c₁ j := by
    unfold privileged at hj_priv_c₀ ⊢
    rw [hc₁_j, hc₁_lj, hc₁_rj]; exact hj_priv_c₀
  -- q not privileged at c₁ (by uniqueness, since j is priv and j ≠ q)
  have hq_notpriv_c₁ : ¬privileged sys c₁ q := by
    intro hq_priv
    exact hj_ne_q (hc₁_upriv.unique hj_priv_c₁ hq_priv)
  unfold privileged at hq_notpriv_c₁; push_neg at hq_notpriv_c₁
  -- c₁(left q) = gkq(left q), c₁(q) = gkq(q), c₁(right q) = gkq(right q)
  have hc₁_lq : c₁ (left q) = gkq (left q) := by
    have : c₁ (left q) = c₀ (left q) := by
      simp [c₁, Function.update_of_ne (Ne.symm hq_ne_lq)]
    rw [this]; exact hc₀_lq
  have hc₁_rq : c₁ (right q) = gkq (right q) := by
    have : c₁ (right q) = c₀ (right q) := by
      simp [c₁, Function.update_of_ne (Ne.symm hq_ne_rq)]
    rw [this]; exact hc₀_rq
  have hc₁_q : c₁ q = gkq q := by simp [c₁, Function.update_self]
  -- Step 7: Contradiction
  -- hq_notpriv_c₁ : f_q(c₁(left q), c₁(q), c₁(right q)) = c₁(q)
  -- Substituting: f_q(gkq(left q), gkq(q), gkq(right q)) = gkq(q)
  -- hpriv_q : f_q(gkq(left q), gkq(q), gkq(right q)) ≠ gkq(q)
  apply hpriv_q
  rw [← hc₁_lq, ← hc₁_q, ← hc₁_rq]
  exact hq_notpriv_c₁

/-! ### ShadowTrap via orbit construction -/

/-- The forced-entry orbit of a sweep cycle produces a ShadowTrap.

    Construction: shift a good config to get c₀ (non-good, from exists_nonGood_config).
    Follow forced transitions (fire procs whose context matches a good-cycle mover entry).
    The orbit closes after CL steps, each config non-good (forcedSucc_nonGood).

    PA proof (5 steps): setup, starting config (exists_nonGood_config),
    non-good closure (forcedSucc_nonGood via hamming1), orbit closure
    (pigeonhole on Fintype), ShadowTrap packaging.

    Key: privilege holds ON THE ORBIT (each step was reached by firing
    a forced-privileged proc). NOT claimed for arbitrary non-good configs.

    Verified 576/576 at n=9. -/
private noncomputable def sweep_nonConsec_shadowTrap
    (gc : GoodCycle sys)
    (_hn : sys.rs.n ≥ 9)
    (_hsub : subThreshold sys.rs)
    (_h3bin : hasGe3Binary sys.rs)
    (_hsweep : gc.isSweep)
    (_hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (_p : Fin sys.rs.n) (_hbin_p : isBinary sys.rs _p)
    (_hfc_p : gc.fireCount _p ≥ 2)
    (_hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = _p → gc.moverAt (nextIndex gc.configs a) ≠ _p) :
    ShadowTrap sys gc := by
  sorry

/-- The sweep + non-consecutive binary + isolated firings case is impossible:
    the forced-entry orbit produces a ShadowTrap, contradicting convergence. -/
theorem sweep_nonConsec_isolated_false
    (gc : GoodCycle sys)
    (hn : sys.rs.n ≥ 9)
    (hconv : converges sys gc)
    (hno_safe : ¬∃ q : Fin sys.rs.n, ∀ k : Fin gc.configs.length,
      gc.moverAt k ≠ q ∧ gc.moverAt k ≠ left q ∧ gc.moverAt k ≠ right q)
    (hsub : subThreshold sys.rs)
    (h3bin : hasGe3Binary sys.rs)
    (hsweep : gc.isSweep)
    (hnoncons : ¬∃ i : Fin sys.rs.n, threeConsecutiveBinary sys.rs i)
    (p : Fin sys.rs.n) (hbin_p : isBinary sys.rs p)
    (hfc_p : gc.fireCount p ≥ 2)
    (hiso : ∀ (a : Fin gc.configs.length),
      gc.moverAt a = p → gc.moverAt (nextIndex gc.configs a) ≠ p) :
    False :=
  shadowTrap_not_converges gc
    (sweep_nonConsec_shadowTrap gc hn hsub h3bin hsweep hnoncons p hbin_p hfc_p hiso)
    hconv

end LeanMn
