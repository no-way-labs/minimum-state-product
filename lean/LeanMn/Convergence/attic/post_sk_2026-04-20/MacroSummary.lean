import LeanMn.Convergence.SixTuple

namespace LeanMn

structure TwelveBoundary where
  c0 : Fin 2
  c1 : Fin 3
  c2 : Fin 3
  c3 : Fin 3
  c4 : Fin 3
  c5 : Fin 3
  cN6 : Fin 3
  cN5 : Fin 3
  cN4 : Fin 3
  cN3 : Fin 3
  cN2 : Fin 3
  cN1 : Fin 2
deriving DecidableEq, Repr

@[ext] theorem TwelveBoundary.ext {s t : TwelveBoundary}
    (h0 : s.c0 = t.c0) (h1 : s.c1 = t.c1) (h2 : s.c2 = t.c2)
    (h3 : s.c3 = t.c3) (h4 : s.c4 = t.c4) (h5 : s.c5 = t.c5)
    (hN6 : s.cN6 = t.cN6) (hN5 : s.cN5 = t.cN5) (hN4 : s.cN4 = t.cN4)
    (hN3 : s.cN3 = t.cN3) (hN2 : s.cN2 = t.cN2) (hN1 : s.cN1 = t.cN1) :
    s = t := by
  cases s
  cases t
  cases h0
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases hN6
  cases hN5
  cases hN4
  cases hN3
  cases hN2
  cases hN1
  rfl

def encodeOptFin3 : Option (Fin 3) → Nat
  | none => 0
  | some x => x.1 + 1

lemma encodeOptFin3_lt (x : Option (Fin 3)) : encodeOptFin3 x < 4 := by
  cases x with
  | none => decide
  | some x =>
    have hx : x.1 < 3 := x.2
    omega

def TwelveBoundary.encode (s : TwelveBoundary) : Nat :=
  ((((((((((((s.c0.1 * 3 + s.c1.1) * 3 + s.c2.1) * 3 + s.c3.1) * 3 + s.c4.1) * 3 + s.c5.1)
      * 3 + s.cN6.1) * 3 + s.cN5.1) * 3 + s.cN4.1) * 3 + s.cN3.1) * 3 + s.cN2.1) * 2 + s.cN1.1)

lemma TwelveBoundary.encode_lt (s : TwelveBoundary) : s.encode < 2 * 3^10 * 2 := by
  have h0 : s.c0.1 < 2 := s.c0.2
  have h1 : s.c1.1 < 3 := s.c1.2
  have h2 : s.c2.1 < 3 := s.c2.2
  have h3 : s.c3.1 < 3 := s.c3.2
  have h4 : s.c4.1 < 3 := s.c4.2
  have h5 : s.c5.1 < 3 := s.c5.2
  have hN6 : s.cN6.1 < 3 := s.cN6.2
  have hN5 : s.cN5.1 < 3 := s.cN5.2
  have hN4 : s.cN4.1 < 3 := s.cN4.2
  have hN3 : s.cN3.1 < 3 := s.cN3.2
  have hN2 : s.cN2.1 < 3 := s.cN2.2
  have hN1 : s.cN1.1 < 2 := s.cN1.2
  unfold TwelveBoundary.encode
  omega

def cup2BoundaryIdx3 (n : Nat) (hn : 12 ≤ n) : Fin n :=
  ⟨3, by omega⟩

def cup2BoundaryIdx4 (n : Nat) (hn : 12 ≤ n) : Fin n :=
  ⟨4, by omega⟩

def cup2BoundaryIdx5 (n : Nat) (hn : 12 ≤ n) : Fin n :=
  ⟨5, by omega⟩

def cup2BoundaryIdxN6 (n : Nat) (hn : 12 ≤ n) : Fin n :=
  ⟨n - 6, by omega⟩

def cup2BoundaryIdxN5 (n : Nat) (hn : 12 ≤ n) : Fin n :=
  ⟨n - 5, by omega⟩

def cup2BoundaryIdxN4 (n : Nat) (hn : 12 ≤ n) : Fin n :=
  ⟨n - 4, by omega⟩

def cup2Boundary12 (n : Nat) (hn4 : 4 ≤ n) (hn12 : 12 ≤ n)
    (c : Config (cup2Spec n hn4)) : TwelveBoundary where
  c0 := by
    show Fin 2
    simpa [cup2Spec, cup2M_eq_two_of_endpoint (n := n) (i := cup2BoundaryIdx0 n (by omega)) (Or.inl rfl)] using
      c (cup2BoundaryIdx0 n (by omega))
  c1 := by
    show Fin 3
    simpa [cup2Spec, cup2M_self_low hn4 (i := cup2BoundaryIdx1 n (by omega)) rfl] using
      c (cup2BoundaryIdx1 n (by omega))
  c2 := by
    have h0 : (cup2BoundaryIdx2 n (by omega)).1 ≠ 0 := by simp [cup2BoundaryIdx2]
    have htop : (cup2BoundaryIdx2 n (by omega)).1 + 1 ≠ n := by simp [cup2BoundaryIdx2]; omega
    show Fin 3
    simpa [cup2Spec, cup2M_self_mid hn4 (i := cup2BoundaryIdx2 n (by omega)) h0 htop] using
      c (cup2BoundaryIdx2 n (by omega))
  c3 := by
    have h0 : (cup2BoundaryIdx3 n hn12).1 ≠ 0 := by simp [cup2BoundaryIdx3]
    have htop : (cup2BoundaryIdx3 n hn12).1 + 1 ≠ n := by simp [cup2BoundaryIdx3]; omega
    show Fin 3
    simpa [cup2Spec, cup2M_self_mid hn4 (i := cup2BoundaryIdx3 n hn12) h0 htop] using
      c (cup2BoundaryIdx3 n hn12)
  c4 := by
    have h0 : (cup2BoundaryIdx4 n hn12).1 ≠ 0 := by simp [cup2BoundaryIdx4]
    have htop : (cup2BoundaryIdx4 n hn12).1 + 1 ≠ n := by simp [cup2BoundaryIdx4]; omega
    show Fin 3
    simpa [cup2Spec, cup2M_self_mid hn4 (i := cup2BoundaryIdx4 n hn12) h0 htop] using
      c (cup2BoundaryIdx4 n hn12)
  c5 := by
    have h0 : (cup2BoundaryIdx5 n hn12).1 ≠ 0 := by simp [cup2BoundaryIdx5]
    have htop : (cup2BoundaryIdx5 n hn12).1 + 1 ≠ n := by simp [cup2BoundaryIdx5]; omega
    show Fin 3
    simpa [cup2Spec, cup2M_self_mid hn4 (i := cup2BoundaryIdx5 n hn12) h0 htop] using
      c (cup2BoundaryIdx5 n hn12)
  cN6 := by
    have h0 : (cup2BoundaryIdxN6 n hn12).1 ≠ 0 := by simp [cup2BoundaryIdxN6]; omega
    have htop : (cup2BoundaryIdxN6 n hn12).1 + 1 ≠ n := by simp [cup2BoundaryIdxN6]; omega
    show Fin 3
    simpa [cup2Spec, cup2M_self_mid hn4 (i := cup2BoundaryIdxN6 n hn12) h0 htop] using
      c (cup2BoundaryIdxN6 n hn12)
  cN5 := by
    have h0 : (cup2BoundaryIdxN5 n hn12).1 ≠ 0 := by simp [cup2BoundaryIdxN5]; omega
    have htop : (cup2BoundaryIdxN5 n hn12).1 + 1 ≠ n := by simp [cup2BoundaryIdxN5]; omega
    show Fin 3
    simpa [cup2Spec, cup2M_self_mid hn4 (i := cup2BoundaryIdxN5 n hn12) h0 htop] using
      c (cup2BoundaryIdxN5 n hn12)
  cN4 := by
    have h0 : (cup2BoundaryIdxN4 n hn12).1 ≠ 0 := by simp [cup2BoundaryIdxN4]; omega
    have htop : (cup2BoundaryIdxN4 n hn12).1 + 1 ≠ n := by simp [cup2BoundaryIdxN4]; omega
    show Fin 3
    simpa [cup2Spec, cup2M_self_mid hn4 (i := cup2BoundaryIdxN4 n hn12) h0 htop] using
      c (cup2BoundaryIdxN4 n hn12)
  cN3 := by
    have h0 : (cup2BoundaryIdxN3 n (by omega)).1 ≠ 0 := by simp [cup2BoundaryIdxN3]; omega
    have htop : (cup2BoundaryIdxN3 n (by omega)).1 + 1 ≠ n := by simp [cup2BoundaryIdxN3]; omega
    show Fin 3
    simpa [cup2Spec, cup2M_self_mid hn4 (i := cup2BoundaryIdxN3 n (by omega)) h0 htop] using
      c (cup2BoundaryIdxN3 n (by omega))
  cN2 := by
    have hhigh : (cup2BoundaryIdxN2 n (by omega)).1 + 2 = n := by
      simp [cup2BoundaryIdxN2]
      omega
    show Fin 3
    simpa [cup2Spec, cup2M_self_high hn4 (i := cup2BoundaryIdxN2 n (by omega)) hhigh] using
      c (cup2BoundaryIdxN2 n (by omega))
  cN1 := by
    have htop : (cup2BoundaryIdxN1 n (by omega)).1 + 1 = n := by
      simp [cup2BoundaryIdxN1]
      omega
    show Fin 2
    simpa [cup2Spec, cup2M_eq_two_of_endpoint (n := n) (i := cup2BoundaryIdxN1 n (by omega)) (Or.inr htop)] using
      c (cup2BoundaryIdxN1 n (by omega))


def cup2MiddlePositions (n : Nat) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun i => 6 ≤ i.1 ∧ i.1 + 6 < n

lemma mem_cup2MiddlePositions_iff {n : Nat} (i : Fin n) :
    i ∈ cup2MiddlePositions n ↔ 6 ≤ i.1 ∧ i.1 + 6 < n := by
  simp [cup2MiddlePositions]

def cup2MiddleMonoTag (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) : Option (Fin 3) :=
  if hEmpty : cup2MiddlePositions n = ∅ then
    none
  else if h0 : ∀ i ∈ cup2MiddlePositions n, (c i).1 = 0 then
    some ⟨0, by decide⟩
  else if h1 : ∀ i ∈ cup2MiddlePositions n, (c i).1 = 1 then
    some ⟨1, by decide⟩
  else if h2 : ∀ i ∈ cup2MiddlePositions n, (c i).1 = 2 then
    some ⟨2, by decide⟩
  else
    none

def cup2MacroSummary (n : Nat) (hn4 : 4 ≤ n) (hn12 : 12 ≤ n)
    (c : Config (cup2Spec n hn4)) : TwelveBoundary × Option (Fin 3) :=
  (cup2Boundary12 n hn4 hn12 c, cup2MiddleMonoTag n hn4 c)

def cup2MiddlePrefix (k : Nat) (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) (j : Fin k) : Option (Fin 3) :=
  if h : 6 + j.1 + 6 < n then
    let i : Fin n := ⟨6 + j.1, by omega⟩
    some <| by
      have hi : i.1 = 6 + j.1 := rfl
      have h0 : i.1 ≠ 0 := by omega
      have hmid : i.1 + 6 < n := by
        simpa [hi, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      have htop : i.1 + 1 ≠ n := by omega
      show Fin 3
      simpa [cup2Spec, cup2M_self_mid hn4 h0 htop] using c i
  else
    none


def cup2MiddleRestPositions (k : Nat) (n : Nat) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter fun i => 6 + k ≤ i.1 ∧ i.1 + 6 < n

lemma mem_cup2MiddleRestPositions_iff {k n : Nat} (i : Fin n) :
    i ∈ cup2MiddleRestPositions k n ↔ 6 + k ≤ i.1 ∧ i.1 + 6 < n := by
  simp [cup2MiddleRestPositions]

def cup2MiddleRestMonoTag (k : Nat) (n : Nat) (hn4 : 4 ≤ n)
    (c : Config (cup2Spec n hn4)) : Option (Fin 3) :=
  if hEmpty : cup2MiddleRestPositions k n = ∅ then
    none
  else if h0 : ∀ i ∈ cup2MiddleRestPositions k n, (c i).1 = 0 then
    some ⟨0, by decide⟩
  else if h1 : ∀ i ∈ cup2MiddleRestPositions k n, (c i).1 = 1 then
    some ⟨1, by decide⟩
  else if h2 : ∀ i ∈ cup2MiddleRestPositions k n, (c i).1 = 2 then
    some ⟨2, by decide⟩
  else
    none

def cup2MacroSummaryK (k : Nat) (n : Nat) (hn4 : 4 ≤ n) (hn12 : 12 ≤ n)
    (c : Config (cup2Spec n hn4)) :
    TwelveBoundary × (Fin k → Option (Fin 3)) × Option (Fin 3) :=
  (cup2Boundary12 n hn4 hn12 c, cup2MiddlePrefix k n hn4 c, cup2MiddleRestMonoTag k n hn4 c)

abbrev Cup2MacroPrefix (k : Nat) := Fin k → Option (Fin 3)

abbrev Cup2MacroState (k : Nat) := TwelveBoundary × Cup2MacroPrefix k × Option (Fin 3)

/-- Current MVP candidate state from the plateau probes: 12 boundary cells,
    the first 2 omitted-core symbols, and a monochromatic tag for the rest. -/
abbrev Cup2MacroState2 := Cup2MacroState 2

def cup2MacroSummary2 (n : Nat) (hn4 : 4 ≤ n) (hn12 : 12 ≤ n)
    (c : Config (cup2Spec n hn4)) : Cup2MacroState2 :=
  cup2MacroSummaryK 2 n hn4 hn12 c

def Cup2MacroState2.encode : Cup2MacroState2 → Nat
  | (bdry, pref, tag) =>
      (((bdry.encode * 4 + encodeOptFin3 (pref ⟨0, by decide⟩)) * 4 +
        encodeOptFin3 (pref ⟨1, by decide⟩)) * 4 + encodeOptFin3 tag)
