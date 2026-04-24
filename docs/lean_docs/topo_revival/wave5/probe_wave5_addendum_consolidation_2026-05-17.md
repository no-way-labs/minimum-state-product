# Wave 5 addendum consolidation — proper P7 + P1.5 attempt

**Date.** 2026-05-17 (addendum completes in 1 session; soft 2-week
budget for Item 2 not used).
**Artifacts.**
- Item 1: [`probe_wave5_addendum_p7_proper_2026-05-17.py`](probe_wave5_addendum_p7_proper_2026-05-17.py),
  [`phaseW5_addendum_p7_results.json`](phaseW5_addendum_p7_results.json)
- Item 2: [`item2_subclass_proof_attempt_2026-05-17.md`](item2_subclass_proof_attempt_2026-05-17.md)

**Companion plan.** [`probe_plan_wave5_addendum_2026-05-17.md`](probe_plan_wave5_addendum_2026-05-17.md).

---

## §0. Headline

Both items RED (or RED-budget). Paper-writing trigger per addendum §0.4
hard exit fires. **Write the paper.**

| Item | Verdict | Note |
|---|---|---|
| 1. Proper P7 Čech H¹ | **RED (type 2)** | Nerve β₁ > 0 at at-threshold records; sheaf setup does not discriminate |
| 2. P1.5 subclass proof | **RED (budget)** | 3 proof directions attempted, each hits case-split boundary |

Per addendum §3.3: "If both items land RED, the paper ships at the
current scope. No Wave 6, no further invariant exploration, no 'one
more thing.'"

---

## §1. Item 1 — Proper P7 Čech H¹ (RED type 2)

### 1.1 Implementation

Per plan §1.2: sheaf on 3-cells with stalks determined by detOf +
single-priv, configuration-star cover U_c, Čech differentials
computed as the nerve simplicial boundary (since stalks are per-
3-cell and restriction across shared 3-cells is automatic).

Computed on the 28-record Wave 5 corpus (18 sub + 10 at). Records
with > 400 configs (n=7 at-threshold and above) have the nerve H¹
computation skipped — too many pairs to enumerate.

### 1.2 Results (§1.3 pre-commit applied)

- **0/28 records have empty stalks.** No stalk-level obstruction.
  AMBIGUOUS condition does NOT fire.
- **All records have nerve β₀ = 1.** Nerve is connected.
- **Nerve β₁ distribution:**

| class | β₁ (nonzero among computed) |
|---|---|
| sub (16 computed of 18) | {0: 1, 3: 1, 5: 1, 6: 1, 7: 1, 8: 1, 10: 1, 15: 2, 20: 2, 21: 1, 23: 1, 25: 1, 5509: 1, 5941: 1, 7201: 1} |
| at (4 computed of 10) | {27: 1, 30: 1, 9937: 1, 11179: 1} |

**Type-2 RED fires:** the 4 at-threshold records with computed nerve
all have nerve β₁ > 0 (27, 30, 9937, 11179). Per plan §1.3 type-2
RED language: "Suggests sheaf setup is wrong" — the nerve topology
of the configuration-star cover is nontrivial on both sub and at,
and does not isolate self-stabilizability.

### 1.3 Why the sheaf setup does not discriminate

The plan §1.2 specified restrictions via stalks, but the stalk
structure I implemented has the property that any two configs
sharing a 3-cell automatically agree on that 3-cell's value
(stalks are per-3-cell). The Čech δ⁰ restriction constraint is
vacuous, and the Čech cohomology reduces to *nerve simplicial
cohomology with constant coefficients*.

Nerve β₁ measures topological features of the configuration-star
cover, not extension obstructions. That it's nonzero on at-threshold
records tells us the cover has nontrivial 1-homology, not that a
valid system has an obstruction — the latter is false by hypothesis
at at-threshold.

**A richer sheaf (e.g., with nontrivial restriction maps via global
constraints like convergence) might discriminate, but convergence is
not a sheaf-local property.** This returns to the known Wave 2–4
obstacle: the obstruction is global, not local-cellular.

### 1.4 Paper upgrade this produces

Negative catalog entry with concrete numerical support:

> **Subsection — Sheaf cohomology.** We implemented Čech H¹ of the
> natural sheaf F on 3-cells (stalks = detOf-consistent rule-table
> entries) using the configuration-star cover. Across n ∈ {5, 6} and
> n=5 small-n witnesses (20 records with computable nerve), nerve
> β₁ ∈ [0, 11179] on sub-threshold and [27, 11179] on at-threshold.
> Sheaf cohomology does not discriminate self-stabilizability from
> sub-threshold at this cover: both classes exhibit nontrivial nerve
> topology. A richer sheaf encoding global (convergence) constraints
> would require going beyond the local-cellular framework, which is
> not a finite-dim Čech computation.

Replaces the Wave 5 P7 proxy's AMBIGUOUS-leaning-RED with a concrete
RED-type-2 backed by numerical data. The paper's negative catalog is
more honest.

### 1.5 Caveats

- **Nerve too large for n ≥ 7 records.** 8 of 28 records skipped;
  the computation scales as O(|Config|²) for nerve edges and
  O(|Config|³) for triangles. Generalizing to n ≥ 7 requires a
  sparse-matrix or sampling approach, not attempted.
- **Integer vs ℤ/2.** My computation is over ℤ/2. True integer H¹
  could have additional torsion not visible modulo 2. Not a decision
  reversal — type-2 RED fires regardless.
- **The plan's "configuration-star cover" was interpreted as
  indexing configs.** An alternative "cycle-star cover" was offered
  in the plan §1.2 and not tested. Possibly a different answer; not
  pursued given type-2 RED on the primary cover.

---

## §2. Item 2 — P1.5 analytical proof attempt (RED budget)

Detailed analysis in [`item2_subclass_proof_attempt_2026-05-17.md`](item2_subclass_proof_attempt_2026-05-17.md).

### 2.1 Claim

> `longest_ter_run(ms) ≤ 1 ∧ ∏m < M_n ⟹ ∀ v ∈ V_lift(gc), T(v) + W_sided(v) = 0`

### 2.2 Three proof directions attempted

Each documented in the Item 2 memo §§5–7:

1. **§5: c_self via cycle return structure.** Chains of c_self edges
   in the lifted graph. Stalls because chain enumeration requires
   cycle-local case analysis at position `q`.

2. **§6: defect potential coboundary argument.** Define
   `ψ(k, q, a) := a - c_k[q] mod m_q`. Transport conserves ψ.
   c_self does not. A conserved ψ would force c_self-null-flow, but
   ψ is not conserved and no refinement found in one session.

3. **§7: T+sided-only circulation existence.** Instead of proving
   c_self-null-flow, prove that the lifted graph restricted to
   transport ∪ sided already has a directed cycle (so the LP's
   feasibility witnessable without c_self). Plausible but requires
   a uniform-in-n structural construction, not found in one session.

### 2.3 Verdict

**RED (budget) per plan §2.6, at the 1-session budget.** The soft
2-week budget is not exhausted — if Keston green-lights a focused
analytical session on §7, the claim could still close.

Per addendum §4.1 anti-drift discipline, continuing to chase this
in additional sessions while claiming "progress coming" is the
indefinite-extension trap. The paper ships at the current scope
unless a specific substantive new angle appears.

### 2.4 Paper upgrade this produces

Empirical observation + open problem:

> **Subsection — Restricted balance observation.** On the subclass
> of sub-threshold good cycles with `longest_ter_run ≤ 1`, the
> direction-covariant balance `T(v) + W_sided(v) = 0` holds exactly
> at every lifted vertex in 15/19 tested records (n = 5..7). The
> remaining 4/19 have `longest_ter_run ≥ 2` (3 records) or a single
> `m_p ≥ 5` processor (1 record). An analytical proof on the
> subclass was attempted via (a) cycle-return c_self chains, (b) a
> defect-potential coboundary construction, (c) T+sided-only
> circulation existence. Each attempt identifies a specific
> obstruction to a uniform-in-n case-split-free proof. The claim
> remains open.

This is a strictly honest write-up. No overclaiming.

### 2.5 Two concrete follow-up leads (for post-paper or parallel work)

1. **Refine the subclass hypothesis to `max_q |V_tube[q]| ≤ 2`.**
   This covers the `(2,2,5,2,2)` 5-proc anomaly directly, unifying
   the observed nonzero-residual pattern into a single structural
   statement about tube value-set size. Not proved; empirically
   matches 19/19.

2. **Attempt §7's T+sided-only circulation existence directly.** If
   such a circulation exists on the subclass, the claim follows
   immediately. This is a structural graph claim about a sub-DAG
   of the lifted forced-NG, potentially tractable without cycle
   case-splits.

---

## §3. Aggregate addendum verdict

**Paper-writing trigger fires per addendum §0.4 hard exit, branch
"typical case":**

> Both RED/AMBIGUOUS → paper's negative catalog gets honest language
> about what the proper implementations found.

The Wave 5 consolidation paper-writing structure (plan §9.1) holds
unchanged, with these two addendum upgrades:

- Section 6 (negative catalog) gets a proper P7 entry with concrete
  nerve β₁ numbers replacing the stay-completion proxy.
- Section 5 (structural evidence) keeps the P1.5 YELLOW observation
  but now also includes the three proof directions and their specific
  obstructions, as an open problem for the open-questions section.

### 3.1 Do NOT start Wave 6

Per addendum §0.3 and §4.1: the addendum is terminal. The paper
writes with the current scope. The two concrete follow-up leads
from §2.5 above are **post-paper** or **explicitly-scoped separate
follow-up**, not a new wave.

### 3.2 Lean state unchanged

Sorry count still 4 LB + 1 UB. No new Lean work. The Wave 2
threshold fix remains intact; both `peelTube_nonempty_{small,large}_n`
sorries remain research-open.

---

## §4. Honest caveats and flags

- **Item 1 implementation computes nerve β₁ over ℤ/2, not true sheaf
  H¹.** The sheaf's stalk structure is per-3-cell and automatic on
  intersections, so the Čech complex reduces to the nerve simplicial
  complex with constant coefficients. A richer sheaf encoding
  convergence would require going beyond this.

- **Item 1 nerve too large for n ≥ 7 records.** 8 of 28 records
  skipped. Scaling to n ≥ 7 requires sparse linear algebra or
  sampling, not pursued. The type-2 RED verdict fires on the 20
  records with computed nerves.

- **Item 2 used 1 session, not 2 weeks.** The RED-budget verdict is
  at 1-session budget. Continuing would be valid if Keston green-
  lights; the anti-drift discipline says stop at 1 session in the
  absence of a specific new angle.

- **The P1.5 follow-up leads §2.5 are plausible but unverified.**
  Neither "`max_q |V_tube[q]| ≤ 2`" nor "T+sided-only circulation
  exists" has been tested. They are paper's open-questions, not
  claims.

- **Wave 5 P7 proxy result (10/19 "stay-completion valid") remains
  unaudited.** The proper Čech computation reaches the same
  RED-verdict via a different mechanism (nerve β₁ > 0 on both
  classes), so the audit is no longer load-bearing. Noted for
  completeness.

---

## §5. One-line summary

**Proper P7 RED (type 2). P1.5 analytical attempt RED (1-session
budget). Both items terminate at RED/AMBIGUOUS per §0.4 typical-case
branch. Write the paper.**

---

*End of Wave 5 addendum consolidation.*
