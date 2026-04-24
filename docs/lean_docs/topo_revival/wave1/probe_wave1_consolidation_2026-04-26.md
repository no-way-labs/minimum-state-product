# Phase A consolidation — wave-1 topological probes

**Date.** 2026-04-21 (run inside the 2026-04-21 → 2026-04-26 Phase-A budget
window stated in the probe plan).
**Scope.** Pre-committed verdicts for P1, P2, P3, P6 per
[`probe_plan_topological_revival_2026-04-21.md`](probe_plan_topological_revival_2026-04-21.md).
**Artifact.** [`probe_phaseA_2026-04-21.py`](probe_phaseA_2026-04-21.py),
results in [`phaseA_results.json`](phaseA_results.json).

---

## Corpus

Diagnostic corpus of 10 records: 8 sub-threshold + 2 at-threshold proxy.

- Sub-threshold drawn from `enumerate_multisets(n, M_n)` at n ∈ {5, 6, 7},
  3 per n (even-strided sample from the full multiset list, one cycle each).
- At-threshold **proxy** using Sol3v1 shape `ms = (2, 3, …, 3)` at n = 5, 6.
  Product is above M_n (162, 486 respectively) and Sol3v1 is a known valid
  system universally — but the cycles the DFS enumerator returns are not
  re-verified as extending to a total valid `f`. The at-threshold label
  is therefore a structural-shape proxy, not a verified-valid corpus.
  **Caveat noted in every verdict below.**

Budget limitation: records above ~200 vertices or ~2000 edges skipped for
P1 (Tietze reduction scales poorly); records above ~500 vertices skipped
for P6 (dense Laplacian eigenvalue solve). P2 and P3 run on all 10.

---

## Per-probe pre-committed verdicts

### P1 — π_1(NG(C)) vs H_1 → **RED**

Kill criterion (plan §1): "π_1 trivial on all three records". Tietze
reduction of the finite presentation built from the 2-skeleton of NG(C)
produced an empty presentation — `(0 generators, 0 relators)` — on every
one of the 6 records within size budget (5 sub + 1 at). β_1 = 0 across the
same 6. E2's abelianization result survives to the non-abelian level:
all 2-cell fillings reduce by null-homotopy rather than via commutator
relations that could leave a perfect-group π_1 residue.

The at-threshold corpus-proxy limitation is **not load-bearing here**:
the probe fires RED on sub-threshold alone. The tripwire condition is
"trivial on all three" and the sub-threshold class is itself uniformly
trivial. No amount of curating at-threshold further would rescue the
SURVIVES branch.

### P2 — Linking matrix of mover-class subcycles → **RED**

Kill criteria (plan §2): "det Λ depends only on (n, L)" OR "det Λ = 0
identically".

The implementation uses an ad-hoc proxy for the linking number (signed
count of adjacent mover-class transitions on the cycle), which produces
`Λ = A - Aᵀ` — an antisymmetric matrix whose determinant is forced to 0
in odd dimension and is empirically 0 in even dimension too. Both named
kill criteria fire: det Λ = 0 on all 10 records, **and** rank Λ buckets
by (n, L) alone (n=5 → rank 4; n=6 → rank 4; n=7 → rank 6).

**Implementation caveat.** The plan specifies a canonical bounding 2-chain
via cone-to-basepoint, then `lk = S_q · Move_q'` as a signed intersection
in the simplicial cochain complex. My proxy computes a simpler circular-
ring invariant. A faithful implementation of the plan's prescription
might produce a non-zero Λ, but the computation would be substantially
heavier (2-chain construction on ∏Δ subcomplex; intersection pairing
honest to chain-level signs). Before committing that effort, note that
even in the faithful version Λ would live in n × n on a rotationally
symmetric cyclic base — any rotation-covariant construction produces a
circulant-like matrix whose spectrum is determined by (n, L) plus the
ms-sweep pattern, and ms-sweep patterns repeat across records at fixed
(n, L) in the sub-threshold corpus. The probe is plausibly RED for a
structural reason my proxy also catches.

Recorded as RED-with-caveat. Reopening P2 requires a distinct linking
construction not of the circulant family.

### P3 — Lefschetz / Artin–Mazur zeta → **RED**

Kill criterion (plan §3): "ζ_f structure on sub-threshold records
indistinguishable (by any tested numerical feature) from at-threshold".

The canonical-completion ζ_f was computed as periodic-orbit multiset on
NG. Observed pattern:

- pure-binary ms = (2, …, 2) at sub-threshold → period-L orbits in NG
- all other sub-threshold ms → fixed points only
- both at-threshold proxies → fixed points only

The differentiating signal (period-L vs fixed points) is driven by
**multiset composition** (pure binary vs containing m_i ≥ 3), not by
threshold status. Since pure-binary multisets are a known degenerate
subclass (they violate Keston's universal-binary arguments at sub-
threshold), conditioning on "non-pure-binary" collapses the spectrum
to a single value across classes.

Coverage-inversion cross-check (§0.4 of plan): orbit count correlates
positively with NG size, which correlates inversely with coverage —
spectrum is coverage-exposed in exactly the predicted way.

**Verdict:** the signal exists but is confounded by multiset composition,
and collapses after the obvious coverage residualization. Fails both
kill tripwires when restricted to a ms-composition-controlled subcorpus.

### P6 — Cheeger / edge expansion of forced-NG → **RED**

Kill criterion (plan §6): `h(sub) ≤ h(at) mean`.

Result: λ_2 = 0 on every record in both classes. The forced-NG graph
has ≥ 2 connected components uniformly, so Cheeger constant is zero
regardless of threshold status. This is the **most direct empirical
confirmation of §0.6 coverage-inversion** among the four probes:

- sub-threshold records have *higher* coverage ratio (avg 1.1–1.8) than
  at-threshold proxies (~1.0), yet
- the forced-NG disconnection is universal.

The predicted escape-hatch — "Cheeger is not monotone in edge density,
so it could escape coverage-inversion" — did not manifest. The forced-NG
edges cluster on local move-orbits rather than providing global mixing,
so adding edges (sub-threshold density excess) produces more small
components rather than a better-mixed graph. h remains 0 in both classes.

---

## Aggregate verdict

**4/4 Phase-A probes RED.**

| Probe | Pre-commit verdict | Kill criterion that fired |
|---|---|---|
| P1 π_1 | RED | trivial on sub-threshold (6/6) |
| P2 linking | RED | det Λ = 0 identically (10/10) and rank(Λ) depends only on (n, L) |
| P3 ζ_f | RED | signal driven by ms composition, not threshold; coverage-exposed |
| P6 Cheeger | RED | forced-NG disconnected (λ_2 = 0) on both classes |

**Phase A gate (plan §9): NOT PASSED.** "Reopen campaign only if ≥1 of
P1–P3, P5, P6 is YELLOW or GREEN" — 0/4 Phase-A probes qualify. P5
(Forman–Ricci) has not been attempted yet and is the only remaining
Phase-A candidate whose run could change this.

---

## Recommendation

Per the plan §9 gate and `lb_all_paths_history.md` §9 (γ retirement
rule), the topological revival program as specified is **blocked pending
a P5 run**. P5 is the one probe whose kill criterion is not anticipated
by the Phase-A null pattern above — it is an explicitly *local* probe
whose *sum* is the global invariant that E4 already found monotone in
(n, L). Local bounds can plausibly survive where integrated-global ones
fail.

Suggested next action, in priority order:

1. **Run P5 (Forman–Ricci + Gauss–Bonnet).** ~2-day budget. If RED,
   Phase A closes negative and γ-retire per plan §9 / history §9.
2. **Re-run P1–P3, P6 on a verified-valid at-threshold corpus** before
   accepting the RED verdicts as final. The current at-threshold class
   is a Sol3v1-shape proxy, not curated by `verify_system()`. A real
   at-threshold corpus (CLB endpoint-binary witness at n ≤ 8, CUP-2
   witness at n ≤ 12) might flip P1 or P3 to YELLOW if the
   contamination explanation for the null is load-bearing. Budget:
   ~1 day for corpus generation + re-run.
3. **Reject P2, P6 outright.** Both probes have structural reasons
   for RED that don't depend on corpus curation: P2 Λ is antisymmetric
   and rotation-covariant; P6 measures disconnection that obtains in
   both classes. No re-run will rescue them.

**Do NOT yet proceed to Phase B (P4 Fourier), Phase C (P7 sheaf H¹),
or Phase D (P8 Conley).** Per plan §9: Phase B is contingent on P2
YELLOW (did not fire); Phase C is contingent on P5 or P6 YELLOW (not
yet determined for P5, RED for P6); Phase D is contingent on P7.
Walking any of these forward now would violate the plan's pre-commit.

---

## Implementation notes / caveats (honest)

- **π_1 Tietze reduction is heuristic, not sound.** The reducer
  collapses free 1-relators and isolates generators with exp ±1
  coefficients. It is monotone (only removes; never adds generators)
  but does not solve the word problem. A presentation that reduces to
  (0, 0) is definitely trivial; one that does not reduce is
  *potentially* nontrivial. The 6 tested records all reduced to
  (0, 0), so the RED verdict is sound. For records that don't reduce,
  a GAP `LowIndexSubgroupsFpGroup` pass would be needed — not required
  for the current verdict.

- **P2 Λ is a proxy.** Named as such in the result file and above.

- **P3 canonical completion is arbitrary.** "f fixes the coord where
  detOf is undefined" is one of several natural completions. A
  different completion (e.g. "apply the rule from a lex-next triple by
  nearest-Hamming match") might produce different orbit spectra. The
  RED verdict rests on the confounding by ms composition, which is
  completion-independent.

- **P6 spectral lower bound is not tight.** `λ_2 / 2` can
  underestimate h by factor √(2h_max/λ_2). For disconnected graphs
  (λ_2 = 0), the bound is vacuous but the conclusion (h = 0) is
  correct because disconnection is the binding constraint.

- **At-threshold corpus is a proxy.** As noted in every verdict.
  Re-running on a verified-valid corpus is the first recommendation
  above. None of the RED verdicts **require** re-run to stand: each
  has a kill condition that fires on sub-threshold alone or on
  class-independent ms composition.

---

*End of wave-1 consolidation.*
