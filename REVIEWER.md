# Reviewer's map — theorems, observations, and conjectures to single reproduction commands

This file is the contract between the paper and the repo. For every
named claim in the paper, the table below gives *one* reproduction
command and the files it touches. A claim is considered reproduced
when its command exits 0 and produces the documented output.

Quick summary of the verification stack:

| Backing | What reproduces it |
|---|---|
| Lean 4 / Mathlib      | `cd lean && lake build`       (0 sorrys at top level) |
| Exhaustive search     | `cd probes/exhaustive_search && python3 driver.py` |
| Rule-table enumeration (deterministic parts, C1 + C2) | `cd probes/exhaustive_search && python3 multiset_enum.py --all` |
| CLB witness (n ≤ 18)  | `cd probes && python3 clb_witness_8748.py`  (n = 9)<br>`cd probes && python3 clb_inherent_cycles.py`  (general) |
| SMT (m5rel / Axis C)  | `cd docs/m5rel && python3 smt_relaxed_n5_n6.py`<br>`cd docs/axisc && python3 probe_cycle_smt.py` |
| LP post-check         | `cd docs/topo_revival && python3 exact_check.py --self-test`<br>`cd docs/topo_revival && python3 farkas_verify.py farkas_certificates.json` |

Set up the Python side once:

```
python3 -m venv .venv && . .venv/bin/activate
pip install -r requirements.txt
```

Set up the Lean side once:

```
cd lean && lake exe cache get
```

Toolchain pins are in `requirements.txt` (Python / z3) and in
`lean/lean-toolchain` + `lean/lakefile.lean` (Lean / Mathlib). The
expected end-state of `cd lean && lake build` is **0 sorrys** at the
shipping surface; the research tree (`LeanMn.Research` umbrella)
carries 5 open sorrys, all of which are declared sorrys, none load-
bearing for any shipped claim.

---

## Map, paper order

### §3 — Main results

**`thm:exact-values`** — *Exact values of $M_n$ for $n = 3, \ldots, 9$.*

The seven rows combine three components:

| $n$ | Upper bound (Lean) | Lower bound |
|---|---|---|
| 3 | trivial | trivial (3-cycle enumeration) |
| 4 | `LeanMn.SmallN.Theorem.M_4_upper` | `LeanMn.SmallN.Theorem.M_4_lower` |
| 5 | `LeanMn.UpperBound.Theorem.upper_bound_small` | exhaustive search (certificate stream) |
| 6 | idem | idem |
| 7 | idem | idem |
| 8 | idem | idem |
| 9 | `LeanMn.UpperBound.Theorem.upper_bound_cert` + `probes/clb_witness_8748.py` | exhaustive search (certificate stream; see `thm:non-extension`) |

*Reproduction.* All seven rows together:

```
cd lean && lake build LeanMn.SmallN.Theorem LeanMn.UpperBound.Theorem
cd ../probes && python3 clb_witness_8748.py
cd exhaustive_search && python3 driver.py          # C1+C2 summary + replay
cd exhaustive_search && make && ./exhaustive --n 5 --orient 2,2,2,2,3  # example C3+C4+C5 per orient
```

The Python driver emits `coverage_manifest.json` (hash cited in the
paper) and the per-certificate rejection stream under
`artifacts/rejections/` for the shipped `(n, orientation)` pairs.
The shipped bundle is full at `n ∈ {3,4}` and the all-binary
orientation at `n = 5`; aggregate counts for the remaining `n = 5`
orientations; and a regenerable recipe (via the C worker
`exhaustive.c`) for any orientation at `n ∈ {5, ..., 9}`. Full rules
of the ship-state and regeneration commands are in
`probes/exhaustive_search/REJECTION_STREAM.md`.

---

**`thm:M4-eq-24`** — *$M_4 = 24$ in the connected model.*

Lean: `LeanMn.SmallN.Theorem.M_4_eq_24`, combining
`M_4_upper` (explicit witness) and `M_4_lower` (case analysis).

```
cd lean && lake build LeanMn.SmallN.Theorem
```

The construction witness is `ms = (2, 2, 2, 3)`, product 24.

---

**`thm:upper-bound-small`** — *$M_n \le 32 \cdot 3^{n-4}$ for $n \in \{5, \ldots, 8\}$, Lean-checked.*

Lean: `LeanMn.UpperBound.Theorem.upper_bound_small`.

```
cd lean && lake build LeanMn.UpperBound.Theorem
```

---

**`thm:upper-bound-cert`** — *$M_n \le 4 \cdot 3^{n-2}$ via CUP-2 for $n \in \{4, \ldots, 10\}$, Lean-checked.*

Lean: `LeanMn.UpperBound.Theorem.upper_bound_cert`, which chains
through `LeanMn.SmallN.Cup2Convergence.cup2Converges4` ... `cup2Converges10`.

```
cd lean && lake build LeanMn.UpperBound.Theorem LeanMn.SmallN.Cup2Convergence
```

The Python mirror of the rule tables (for referee sanity-checking) is
`probes/cup2_theorem.py`; the per-$n$ rank tables are emitted by
`probes/gen_cup2_ranks.py`.

---

**`thm:m5rel`** — *$M_5^{\mathrm{rel}} = 96$ in the relaxed-connectedness convention, SMT-certified.*

```
cd docs/m5rel && python3 smt_relaxed_n5_n6.py
```

The script emits `smt_relaxed_findings.md`-matching output: every
product-$< 96$ state-count on 5 processors is UNSAT under the $\S1.7$
relaxed-model encoding, and $96$ has an explicit witness. The z3
pin is in `requirements.txt`.

---

**`thm:non-extension`** — *Neither small-$n$ absorber nor ternary-strip family realizes $M_n$ past $n = 9$; the three $7776$ multisets at $n = 9$ have no valid rule table.*

The two parts:

1. $n = 9$, product $= 7776$: the three multisets $\{2^3, 3^5, 4\}$,
   $\{2^4, 3^4, 6\}$, $\{2^5, 3^3, 9\}$ of Table~7 are each eliminated
   by the exhaustive search. Per-orientation rejection streams are
   regenerable via the C worker; see
   `probes/exhaustive_search/REJECTION_STREAM.md` for the ship-state
   rules at $n = 9$.
2. The ternary-strip product $4 \cdot 3^{n-2}$ is sharp at $n = 9$
   and realized at $n \in \{4, \ldots, 10\}$ via CUP-2; at $n \le 8$
   it is strictly above $M_n$ by $9/8$ (arithmetic).

```
cd probes/exhaustive_search && make && \
  ./exhaustive --n 9 --ms 2,2,2,3,3,3,3,3,4 --orient <...>  # part 1, per orient
cd lean && lake build LeanMn.UpperBound.Theorem                # part 2
```

---

**`obs:ratio-crossover`** — *$M_5/M_4 = 4$, $M_n/M_{n-1} = 3$ for $n \in \{6, 7, 8\}$, $M_9/M_8 = 27/8$.*

Arithmetic consequence of `thm:exact-values`. No separate command;
verify by inspection of the table in `thm:exact-values`.

---

**`conj:ub-allN`** — *$M_n \le 4 \cdot 3^{n-2}$ for all $n \ge 9$.*

Status is *Lean-checked* for $n \in \{4, \ldots, 10\}$ via CUP-2
(`thm:upper-bound-cert`) and *Python-verified* for $n \in \{5, \ldots, 18\}$
via the CLB construction. For $n \ge 19$ only Dijkstra's classical
$M_n \le 3^n$ is available. Repro:

```
cd lean && lake build LeanMn.UpperBound.Theorem       # n = 4..10
cd probes && python3 clb_inherent_cycles.py           # n = 5..18, emits ms + verify_system verdict per n
```

---

**`conj:lb-allN`** — *$M_n \ge 4 \cdot 3^{n-2}$ for all $n \ge 9$.*

Tiered reproduction:

| $n$ | Status | Command |
|---|---|---|
| $9$ | established by exhaustive search | `cd probes/exhaustive_search && python3 driver.py` |
| $10, 11$ | Axis-C-supported, not proved | `cd docs/axisc && python3 probe_axisc_n10_sweep.py`<br>and `python3 probe_cycle_smt.py` |
| $\ge 12$ | conjecture; detector separation on stored corpus | `cd docs/topo_revival && python3 farkas_verify.py farkas_certificates.json`<br>(feeds `obs:currency-null`) |

Axis-C sweep outputs are archived as
`docs/axisc/axc_n10_sweep_results.json`,
`docs/axisc/axc_n10_smt_sweep_results.json`,
`docs/axisc/axc_n11_sweep_results.json`,
`docs/axisc/axc_n11_smt_sweep_results.json`; the human-readable
summary is `docs/axisc/axisc_n10_n11_findings.md`.

---

**`cor:asymptotic`** — *If `conj:ub-allN` and `conj:lb-allN` both hold then $M_n = 4 \cdot 3^{n-2}$ for $n \ge 9$, so $M_n^{1/n} \to 3$.*

No separate repro (conditional consequence of the two conjectures above).

---

### §4 — Detector and corpus

**`obs:locus`** — *The LP detector's feasibility locus matches the
sub-threshold / at-threshold boundary on the stored corpus.*

Backing data: `corpus.json` (41028fd8ba34839337b78793f241a21afe0d291ee812d8c23cf6576968828c89),
`corpus_canonical.json` (paper-cited prefix `f4b017b1f57687cc`; the
canonical superset per §1.7 corpus reconciliation).

```
cd docs/topo_revival && python3 farkas_verify.py farkas_certificates.json
cd docs/topo_revival && python3 exact_check.py --self-test
```

The Farkas verifier re-checks infeasibility certificates for the 14
at-threshold witnesses without an LP solver; `exact_check.py` is the
exact rational post-check for the complementary (feasible, sub-threshold)
side (see §4 on exactness).

---

**`obs:currency-null`** — *The Wave-2 circulation LP null-separates
the paper's verified witnesses from sub-threshold counterexamples.*

```
cd docs/topo_revival && python3 longest_ter_run_restricted_check.py
```

The Wave-1..6 raw verdicts live under `docs/lean_docs/topo_revival/wave{2..6}/phase*_results.json`.

---

**`conj:tsided`** — *T+sided directed cycle on the verified corpus.*

Conjecture. Empirical support:
`docs/lean_docs/topo_revival/wave6/phaseW6_t2_results.json`
(Wave-6 T2 upgrade of the P1.5 probe).

---

**`conj:axis-c`** — *Axis C is uniformly fired by the sink-kernel monotonicity certificate on every sub-threshold $n \ge 10$ multiset.*

Empirical support: 320/320 tested probes at $n = 10$, 585/585 at $n = 11$
(one UNKNOWN SMT verdict).

```
cd docs/axisc && python3 probe_axisc_n10_sweep.py
cd docs/axisc && python3 probe_cycle_smt.py
```

See `docs/axisc/axisc_n10_n11_findings.md` for the summary.

---

### §A (Appendices)

**`prop:hoffman`** — *Hoffman circulation duality (standard).*

Paper-internal statement of a textbook result; no separate repro.

---

**`lem:quasi-uni`** — *Quasi-unidirectionality (non-proof-critical optimization).*

Explicitly flagged non-proof-critical in §A.2 (`app:exhaust-sound`):
the final verifier rejects every candidate with 4+ cyclically
consecutive binary processors independently, so the lower-bound
certificate does not depend on this lemma. No separate repro.

---

**`lem:state-label-bijection`** — *State-label renaming is validity-preserving.*

Paper has the proof sketch; the clause-by-clause proof is
`docs/state_label_renaming_proof.md` (six properties checked, full
template-follow of `enumi:orbit-red`).

---

### ARG 1985 LCM bound (§1.3)

The 1985 LCM bound does *not* induce the $n = 9$ phase transition
(witnesses adjacent-binary + insensitivity theorem):

```
cd docs/arg_lcm && python3 arg_lcm_finite_checks.py
```

See also `docs/arg_lcm/paper.md` for the dispatch writeup.

---

### §A lean-encoding audit

Python ↔ Lean `IsValid` parity runner (§A.1 Strengthening #3):

```
cd docs/parity && python3 parity_runner.py
```

Emits `parity_report.json` next to the runner. All stored small-$n$
witnesses must show `pass=True` on both the Python and Lean sides.

---

## Troubleshooting reproduction failures

* **`lake build` emits more than the expected 5 sorrys.** Confirm you
  are on the release tag: `git describe --tags` should match the paper's
  release. The 5 expected sorrys are all in `LeanMn.Research` umbrella
  and are enumerated in §7 / App~K.

* **`driver.py` complains about `multiset_enum`.** It expects its CWD
  to be `probes/exhaustive_search/`. Cd there first, or pass the
  corpus path explicitly.

* **`exact_check.py --self-test` fails.** Confirm `python3 --version` is
  3.11 or newer and `pip install -r requirements.txt` succeeded (numpy,
  scipy, z3-solver pins are load-bearing).

* **Any `*.py` reports `ImportError: verifier`.** Python scripts under
  `probes/` assume `probes/` is on `sys.path`; scripts under `docs/`
  that depend on the verifier either `sys.path.insert` to `probes/`
  themselves or ship a local copy. Running from the repo root should
  work; if not, set `PYTHONPATH=probes:$PYTHONPATH`.

---

## Contact

Keston Aquino-Michaels — <kestonamichaels@gmail.com>.

Issues reproducing any row of this table are the single best form of
referee feedback. Please open a GitHub issue (or email directly)
quoting the command you ran, the expected output per this file, and
the actual output.
