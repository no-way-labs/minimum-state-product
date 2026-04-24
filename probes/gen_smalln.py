#!/usr/bin/env python3
"""Generate Lean 4 witness definitions and finite validity certificates.

Reads the Python witness data and outputs SmallN/Defs.lean with:
  - RingSpec definitions
  - Transition function definitions (flat Nat match + TransFn wrapper)
  - System definitions
  - State product theorems
  - Explicit good-cycle certificates
  - Explicit bad-rank certificates proving convergence
"""

import sys
from itertools import product as cartesian

sys.path.insert(0, '../docs')
from verify_witnesses import witness_n4, witness_n5, witness_n6, witness_n7, witness_n8


def gen_outval(name, n, ms, rules):
    """Generate the flat Nat transition function for a witness."""
    lines = []
    # Per-processor functions
    for proc in range(n):
        table = rules[proc]
        pname = f"{name}P{proc}"
        lines.append(f"private def {pname} (L S R : Nat) : Nat :=")
        lines.append(f"  match L, S, R with")
        entries = sorted(table.items())
        for (L, S, R), out in entries:
            lines.append(f"  | {L}, {S}, {R} => {out}")
        lines.append(f"  | _, _, _ => 0")
        lines.append("")

    # Combined function
    lines.append(f"def {name}OutVal (i L S R : Nat) : Nat :=")
    lines.append(f"  match i with")
    for proc in range(n):
        pname = f"{name}P{proc}"
        if proc < n - 1:
            lines.append(f"  | {proc} => {pname} L S R")
        else:
            lines.append(f"  | _ => {pname} L S R")
    lines.append("")
    return "\n".join(lines)


def gen_m_function(name, n, ms):
    """Generate the state-count function."""
    lines = []
    lines.append(f"def {name}M (i : Fin {n}) : Nat :=")
    lines.append(f"  match i.val with")
    for i in range(n):
        if i < n - 1:
            lines.append(f"  | {i} => {ms[i]}")
        else:
            lines.append(f"  | _ => {ms[i]}")
    lines.append("")
    return "\n".join(lines)


def gen_spec(name, n, ms):
    """Generate the RingSpec definition."""
    return f"""def {name}Spec : RingSpec where
  n := {n}
  n_ge_4 := by omega
  m := {name}M
  m_pos := by intro i; fin_cases i <;> simp [{name}M]
"""


def gen_left_right_m_lemmas(name, n, ms):
    """Generate lemmas about m (left i) and m (right i) for bound proofs."""
    lines = []
    for i in range(n):
        li = (i + n - 1) % n
        ri = (i + 1) % n
        lines.append(f"private lemma {name}_m_left_{i} : {name}M (left (n := {n}) ⟨{i}, by omega⟩) = {ms[li]} := by")
        lines.append(f"  simp [left, {name}M]; omega")
        lines.append(f"private lemma {name}_m_right_{i} : {name}M (right (n := {n}) ⟨{i}, by omega⟩) = {ms[ri]} := by")
        lines.append(f"  simp [right, {name}M]; omega")
        lines.append(f"private lemma {name}_m_self_{i} : {name}M (⟨{i}, by omega⟩ : Fin {n}) = {ms[i]} := by")
        lines.append(f"  simp [{name}M]")
        lines.append("")
    return "\n".join(lines)


def gen_outval_bound(name, n, ms, rules):
    """Generate the bound proof for the transition function output.
    Uses fin_cases on all variables + simp_all to fully reduce."""
    pnames = ", ".join(f"{name}P{p}" for p in range(n))
    return f"""private lemma {name}OutVal_lt (i : Fin {n})
    (L : Fin ({name}Spec.m (left i)))
    (S : Fin ({name}Spec.m i))
    (R : Fin ({name}Spec.m (right i))) :
    {name}OutVal i.val L.val S.val R.val < {name}Spec.m i := by
  fin_cases i <;> fin_cases L <;> fin_cases S <;> fin_cases R <;>
    simp_all [{name}OutVal, {pnames}, {name}Spec, {name}M]
"""


def gen_trans_and_system(name, n, ms):
    """Generate the TransFn and System definitions."""
    return f"""def {name}Trans : TransFn {name}Spec := by
  intro i L S R
  exact ⟨{name}OutVal i.val L.val S.val R.val, {name}OutVal_lt i L S R⟩

def {name}System : System where
  rs := {name}Spec
  f := {name}Trans
"""


def gen_product_theorem(name, n, ms):
    """Generate the state product theorem."""
    product = 1
    for m in ms:
        product *= m
    return f"""theorem {name}_stateProduct : stateProduct {name}Spec = {product} := by
  simp [stateProduct, {name}Spec, {name}M, Fin.prod_univ_succ]
"""


def mixed_radix_code(ms, cfg):
    code = 0
    mult = 1
    for i, v in enumerate(cfg):
        code += v * mult
        mult *= ms[i]
    return code


def compute_cycle_and_rank(ms, rules):
    n = len(ms)
    configs = list(cartesian(*(range(m) for m in ms)))

    def privileged(cfg):
        out = []
        for i in range(n):
            L = cfg[(i - 1) % n]
            S = cfg[i]
            R = cfg[(i + 1) % n]
            if rules[i][(L, S, R)] != S:
                out.append(i)
        return out

    def move(cfg, proc):
        L = cfg[(proc - 1) % n]
        S = cfg[proc]
        R = cfg[(proc + 1) % n]
        lst = list(cfg)
        lst[proc] = rules[proc][(L, S, R)]
        return tuple(lst)

    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            single_priv[cfg] = (move(cfg, priv[0]), priv[0])

    good_cycle = None
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []
        visited = set()
        cur = start
        while cur in single_priv and cur not in visited:
            visited.add(cur)
            visited_global.add(cur)
            path.append(cur)
            cur = single_priv[cur][0]
        if cur == start and path:
            good_cycle = path
            break

    if good_cycle is None:
        raise RuntimeError("no good cycle found")

    cycle_set = set(good_cycle)
    cycle_codes = [mixed_radix_code(ms, cfg) for cfg in good_cycle]

    bad_set = {cfg for cfg in configs if cfg not in cycle_set}
    rank = {}
    layer = 1
    while bad_set:
        removable = []
        for cfg in list(bad_set):
            priv = privileged(cfg)
            if all(move(cfg, proc) not in bad_set for proc in priv):
                removable.append(cfg)
        if not removable:
            raise RuntimeError("bad-step graph still contains a cycle")
        for cfg in removable:
            rank[cfg] = layer
            bad_set.remove(cfg)
        layer += 1

    total = 1
    for m in ms:
        total *= m
    rank_vals = [0] * total
    for cfg in configs:
        rank_vals[mixed_radix_code(ms, cfg)] = rank.get(cfg, 0)

    return cycle_codes, rank_vals


def gen_cfg_constructor(name, n, ms):
    params = " ".join(f"(x{i} : Fin {m})" for i, m in enumerate(ms))
    lines = []
    lines.append(f"def {name}Cfg {params} : Config {name}Spec")
    for i in range(n):
        lines.append(f"  | ⟨{i}, _⟩ => x{i}")
    lines.append("")
    return "\n".join(lines)


def gen_cfg_code(name, n, ms):
    expr = f"(c ⟨{n - 1}, by decide⟩).1"
    for i in reversed(range(n - 1)):
        expr = f"(c ⟨{i}, by decide⟩).1 + {ms[i]} * ({expr})"
    return f"""def {name}CfgCode (c : Config {name}Spec) : Nat :=
  {expr}
"""


def gen_cfg_of_code(name, n, ms):
    lines = []
    lines.append(f"def {name}CfgOfCode (k : Nat) : Config {name}Spec :=")
    lines.append(f"  {name}Cfg")
    mult = 1
    for m in ms:
        lines.append(f"    ⟨(k / {mult}) % {m}, by omega⟩")
        mult *= m
    lines.append("")
    return "\n".join(lines)


def gen_validity_certificate(name, n, ms, rules):
    cycle_codes, rank_vals = compute_cycle_and_rank(ms, rules)
    cycle_codes_str = ", ".join(str(k) for k in cycle_codes)
    rank_vals_str = ", ".join(str(k) for k in rank_vals)
    return f"""def {name}GoodCycleCodes : List Nat := [{cycle_codes_str}]

def {name}GoodCycleConfigs : List (Config {name}Spec) :=
  {name}GoodCycleCodes.map {name}CfgOfCode

def {name}RankVals : List Nat := [{rank_vals_str}]

def {name}BadRank (c : Config {name}Spec) : Nat :=
  {name}RankVals.getD ({name}CfgCode c) 0

theorem {name}GoodCycle_nonempty : {name}GoodCycleConfigs ≠ [] := by
  decide

theorem {name}GoodCycle_unique_privileged_aux :
    ∀ c ∈ {name}GoodCycleConfigs,
      ∃ i, privileged {name}System c i ∧
        ∀ j, privileged {name}System c j → j = i := by
  native_decide

theorem {name}GoodCycle_unique_privileged :
    ∀ c ∈ {name}GoodCycleConfigs, ∃! i, privileged {name}System c i := by
  intro c hc
  simpa [ExistsUnique] using {name}GoodCycle_unique_privileged_aux c hc

theorem {name}GoodCycle_closed :
    ∀ k : Fin {name}GoodCycleConfigs.length,
      ∃ i,
        privileged {name}System ({name}GoodCycleConfigs.get k) i ∧
          {name}GoodCycleConfigs.get (nextIndex {name}GoodCycleConfigs k) =
            move {name}System ({name}GoodCycleConfigs.get k) i := by
  native_decide

theorem {name}GoodCycle_distinct :
    ∀ j₁ j₂ : Fin {name}GoodCycleConfigs.length,
      {name}GoodCycleConfigs.get j₁ = {name}GoodCycleConfigs.get j₂ → j₁ = j₂ := by
  native_decide

def {name}GoodCycle : GoodCycle {name}System where
  configs := {name}GoodCycleConfigs
  nonempty := {name}GoodCycle_nonempty
  unique_privileged := {name}GoodCycle_unique_privileged
  closed := {name}GoodCycle_closed
  distinct := {name}GoodCycle_distinct

theorem {name}BadRank_decreases_from
    (c : Config {name}Spec)
    (hbad : c ∉ {name}GoodCycleConfigs)
    (i : Fin {n})
    (hpriv : privileged {name}System c i)
    (hnext : move {name}System c i ∉ {name}GoodCycleConfigs) :
    {name}BadRank (move {name}System c i) < {name}BadRank c := by
  native_decide +revert

theorem {name}BadRank_decreases :
    ∀ {{c' c : Config {name}Spec}},
      badStep {name}System {name}GoodCycle c' c → {name}BadRank c' < {name}BadRank c := by
  intro c' c hstep
  rcases hstep with ⟨hbad, hnext, ⟨i, hpriv, rfl⟩⟩
  exact {name}BadRank_decreases_from c hbad i hpriv hnext

theorem {name}_converges : converges {name}System {name}GoodCycle := by
  let f : Config {name}Spec → Nat := {name}BadRank
  let r : Config {name}Spec → Config {name}Spec → Prop := InvImage Nat.lt f
  have hwf : WellFounded r := by
    simpa [r] using (InvImage.wf f Nat.lt_wfRel.wf)
  refine Subrelation.wf (r := r) ?_ hwf
  intro c' c hstep
  exact {name}BadRank_decreases hstep

theorem {name}_valid : valid {name}System := by
  exact ⟨{name}GoodCycle, {name}_converges⟩
"""


def gen_witness(name, n, ms, rules):
    """Generate all Lean code for one witness."""
    parts = []
    product = 1
    for m in ms:
        product *= m
    parts.append(f"/-! ### Witness n={n}, ms={ms}, product={product} -/\n")
    parts.append(gen_m_function(name, n, ms))
    parts.append(gen_spec(name, n, ms))
    parts.append(gen_outval(name, n, ms, rules))
    parts.append(gen_outval_bound(name, n, ms, rules))
    parts.append(gen_trans_and_system(name, n, ms))
    parts.append(gen_product_theorem(name, n, ms))
    parts.append(gen_cfg_constructor(name, n, ms))
    parts.append(gen_cfg_code(name, n, ms))
    parts.append(gen_cfg_of_code(name, n, ms))
    parts.append(gen_validity_certificate(name, n, ms, rules))
    return "\n".join(parts)


def main():
    witnesses = [
        ("w4", *witness_n4()),
        ("w5", *witness_n5()),
        ("w6", *witness_n6()),
        ("w7", *witness_n7()),
        ("w8", *witness_n8()),
    ]

    header = """/-
  SmallN/Defs.lean — Witness system definitions for n = 4..8 (Phase 11)

  For each n ∈ {4,5,6,7,8}, defines the explicit witness system that achieves
  the minimum state product M_n = 32 · 3^(n-4).

  Each witness consists of:
    - State counts m_i for each processor
    - Transition function f_i(L, S, R) for each processor
    - Proof that stateProduct = M_n

  Validity is proved by explicit finite certificates:
    - the concrete good cycle
    - a concrete bad-rank function that strictly decreases on every bad step
-/
import LeanMn.Dijkstra

namespace LeanMn

"""

    footer = """
end LeanMn
"""

    body_parts = []
    for name, ms, rules in witnesses:
        n = len(ms)
        body_parts.append(gen_witness(name, n, ms, rules))

    print(header + "\n".join(body_parts) + footer)


if __name__ == "__main__":
    main()
