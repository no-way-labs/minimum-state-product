/-
  LowerBound/SK/Forcing.lean — Determined dictionary + forced graph

  Defines:
  - `DetDict`: partial transition table extracted from a candidate cycle
  - `detOf`: extract a `DetDict` from a `GoodCycle`
  - `NonGood`: predicate "config not in the cycle"
  - `forcedNeighbors`: forced out-edges from a config under a `DetDict`
-/
import LeanMn.Dijkstra
import LeanMn.LowerBound.GoodCycleBasics

namespace LeanMn.SK

variable {sys : System}

/-- A determined dictionary maps each local context `(i, L, S, R)` to
    either a forced output value or `none` (no constraint).

    Built from a candidate good cycle: an entry is forced to `v` iff
    some cycle step has processor `i` producing value `v` from local
    context `(L, S, R)`. -/
def DetDict (sys : System) : Type :=
  (i : Fin sys.rs.n) →
    Fin (sys.rs.m (left i)) →
    Fin (sys.rs.m i) →
    Fin (sys.rs.m (right i)) →
    Option (Fin (sys.rs.m i))

/-- The empty det: no constraints. -/
def DetDict.empty (sys : System) : DetDict sys :=
  fun _ _ _ _ => none

/-- Insert an entry into the det. If the key already exists, keep the
    existing value (the cycle's consistency guarantees it matches). -/
def DetDict.insert (D : DetDict sys) (i : Fin sys.rs.n)
    (l : Fin (sys.rs.m (left i))) (s : Fin (sys.rs.m i))
    (r : Fin (sys.rs.m (right i))) (v : Fin (sys.rs.m i)) :
    DetDict sys :=
  fun i' l' s' r' =>
    if h : i' = i then
      let l'' := Fin.cast (by rw [show left i' = left i by rw [h]] ) l'
      let s'' := Fin.cast (by rw [h]) s'
      let r'' := Fin.cast (by rw [show right i' = right i by rw [h]]) r'
      if l'' = l ∧ s'' = s ∧ r'' = r then
        match D i' l' s' r' with
        | some existing => some existing
        | none => some (Fin.cast (by rw [h]) v)
      else D i' l' s' r'
    else D i' l' s' r'

/-- Extract the determined dictionary from a good cycle.

    For each position i and context (l, s, r): find the first cycle
    step k where config k has this context at position i. Return the
    value at position i in the NEXT config (c_{k+1}[i]).

    If i is the mover at step k: c_{k+1}[i] = sys.f i l s r (a move).
    If i is not the mover: c_{k+1}[i] = c_k[i] = s (a stay).

    This declarative definition is equivalent to the foldl version but
    easier to reason about. -/
noncomputable def detOf (gc : GoodCycle sys) : DetDict sys :=
  fun i l s r =>
    match (List.finRange gc.configs.length).find?
      (fun k => (gc.configs.get k (left i) == l) &&
                (gc.configs.get k i == s) &&
                (gc.configs.get k (right i) == r)) with
    | none => none
    | some k => some (gc.configs.get (nextIndex gc.configs k) i)

/-- A configuration is non-good iff it does not appear in the cycle. -/
def NonGood (gc : GoodCycle sys) (c : Config sys.rs) : Prop :=
  c ∉ gc.configs

instance (gc : GoodCycle sys) (c : Config sys.rs) : Decidable (NonGood gc c) := by
  unfold NonGood
  infer_instance

/-- Look up the forced output for processor i at config c. Returns
    `some v` if the det has an entry and v ≠ c[i] (a move), or
    `none` if no entry or the entry equals c[i] (stay/undefined). -/
def forcedOutput (D : DetDict sys) (c : Config sys.rs)
    (i : Fin sys.rs.n) : Option (Fin (sys.rs.m i)) :=
  match D i (c (left i)) (c i) (c (right i)) with
  | some v => if v = c i then none else some v  -- only moves, not stays
  | none => none

/-- Apply a forced move at position i: produce the new config with
    c[i] replaced by v, everything else unchanged. -/
def applyMove (c : Config sys.rs) (i : Fin sys.rs.n)
    (v : Fin (sys.rs.m i)) : Config sys.rs :=
  fun j => if h : j = i then Fin.cast (by rw [h]) v else c j

/-- The forced out-neighbors of a config c under a determined
    dictionary D: for each position i with a forced move to value v,
    the moved configuration (c with c[i] → v). -/
def forcedNeighbors (D : DetDict sys) (c : Config sys.rs) :
    List (Config sys.rs) :=
  (List.finRange sys.rs.n).filterMap fun i =>
    match forcedOutput D c i with
    | some v => some (applyMove c i v)
    | none => none

/-- Whether a config has any forced neighbor within a given set. -/
def hasForcedNeighborIn (D : DetDict sys) (c : Config sys.rs)
    (S : Finset (Config sys.rs)) : Bool :=
  (forcedNeighbors D c).any (· ∈ S)

end LeanMn.SK
