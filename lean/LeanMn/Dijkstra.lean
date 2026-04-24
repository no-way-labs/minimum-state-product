import LeanMn.Ring

namespace LeanMn

def privileged (sys : System) (c : Config sys.rs) (i : Fin sys.rs.n) : Prop :=
  sys.f i (c (left i)) (c i) (c (right i)) ≠ c i

instance (sys : System) (c : Config sys.rs) (i : Fin sys.rs.n) :
    Decidable (privileged sys c i) := by
  unfold privileged
  infer_instance

def move (sys : System) (c : Config sys.rs) (i : Fin sys.rs.n) : Config sys.rs :=
  fun j =>
    if h : j = i then
      Fin.cast (by cases h; rfl) (sys.f i (c (left i)) (c i) (c (right i)))
    else
      c j

def step (sys : System) (c c' : Config sys.rs) : Prop :=
  ∃ i, privileged sys c i ∧ c' = move sys c i

instance (sys : System) (c c' : Config sys.rs) : Decidable (step sys c c') := by
  unfold step
  infer_instance

def singlePrivileged (sys : System) (c : Config sys.rs) : Prop :=
  ∃! i, privileged sys c i

noncomputable instance (sys : System) (c : Config sys.rs) : Decidable (singlePrivileged sys c) := by
  classical
  unfold singlePrivileged
  infer_instance

def nextIndex {α : Type} (xs : List α) (k : Fin xs.length) : Fin xs.length :=
  ⟨(k.1 + 1) % xs.length, by
    have hlen : 0 < xs.length := by
      exact lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.succ_le_of_lt k.2)
    exact Nat.mod_lt _ hlen⟩

structure GoodCycle (sys : System) where
  configs : List (Config sys.rs)
  nonempty : configs ≠ []
  unique_privileged : ∀ c ∈ configs, ∃! i, privileged sys c i
  closed :
    ∀ k : Fin configs.length,
      ∃ i,
        privileged sys (configs.get k) i ∧
          configs.get (nextIndex configs k) = move sys (configs.get k) i
  /-- All configs in the good cycle are pairwise distinct.
      This is part of the mathematical definition: a good cycle is a minimal
      closed orbit under the deterministic single-privileged dynamics. Any
      periodic sub-cycle would itself be a valid cycle, so the minimal one
      has distinct configs. -/
  distinct :
    ∀ j₁ j₂ : Fin configs.length,
      configs.get j₁ = configs.get j₂ → j₁ = j₂
  /-- Fairness (Dijkstra Property 5): every processor fires at least once
      in the good cycle. No processor starves. -/
  fair :
    ∀ i : Fin sys.rs.n,
      ∃ k : Fin configs.length,
        ∃ j, privileged sys (configs.get k) j ∧
          configs.get (nextIndex configs k) = move sys (configs.get k) j ∧ j = i

def badStep (sys : System) (gc : GoodCycle sys) (c' c : Config sys.rs) : Prop :=
  c ∉ gc.configs ∧ c' ∉ gc.configs ∧ step sys c c'

instance (sys : System) (gc : GoodCycle sys) (c' c : Config sys.rs) :
    Decidable (badStep sys gc c' c) := by
  unfold badStep
  infer_instance

def converges (sys : System) (gc : GoodCycle sys) : Prop :=
  WellFounded (badStep sys gc)

def valid (sys : System) : Prop :=
  ∃ gc : GoodCycle sys, converges sys gc

end LeanMn
