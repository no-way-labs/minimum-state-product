# SK Small-n Discovery — Sub-M_n Probe Findings — 2026-04-15

Companion to `sk_invariant_findings_2026-04-14.md`,
`sk_witness_template_findings_2026-04-15.md`, and
`sk_invariant_lean_targets_2026-04-14.md`. Reports the result of
`probe_sk_sub_mn_smalln_2026-04-15.py`, which tested whether the SK
invariant detects invalidity at the **sharp `M_n` threshold** for
`n = 5..8` (where `M_n = 32·3^(n-4)` is strictly less than `4·3^(n-2)`).

**TL;DR**: Hypothesis 2 is empirically confirmed for sweep + bounce
candidate cycles across **5,548 sub-M_n multisets at n=5..8**, with
**zero escapes**. SK at the sharp small-n threshold appears to give the
LB at small n — modulo the (genuine) caveat that the probe only tests
two cycle families, not all candidate cycles. A surprising secondary
finding: `|SK|` is **constant per n** across every multiset tested,
regardless of binary count or value structure. This is a much stronger
invariance than the previously-noted "binary-count invariance".

---

## The probe

For each `n ∈ {5, 6, 7, 8}`:
1. Enumerate every state vector `(m_0, …, m_{n-1})` with `m_i ≥ 2` and
   `product < M_n = 32·3^(n-4)`.
2. For each multiset, search for sweep candidate cycles
   (`mover_seq = [0,1,…,n-1,0,1,…,n-1]`) and bounce candidate cycles
   (`mover_seq = [0,1,…,n-1,n-2,…,1]`) via DFS, max 3 cycles per type.
3. For each found cycle, compute `det(C)`, the forced graph on
   non-good configs, and the sink-kernel `SK`.
4. Record whether **any** found cycle had `|SK| = 0` (which would
   indicate a possibly-valid system at sub-M_n product).

Source: `probes/probe_sk_sub_mn_smalln_2026-04-15.py`.

## Coverage

| n | M_n | multisets enumerated | cycles found in all | empty-SK cases |
|---|---|---|---|---|
| 5 | 96   | 26   | 26/26 | **0** |
| 6 | 288  | 147  | 147/147 | **0** |
| 7 | 864  | 820  | 820/820 | **0** |
| 8 | 2592 | 4555 | 4555/4555 | **0** |
| **total** | — | **5,548** | **5,548/5,548** | **0** |

Every sub-M_n multiset at n=5..8 had at least one sweep candidate cycle
**and** at least one bounce candidate cycle, and **every** found cycle
had non-empty SK.

## Verdict on hypothesis 2

> **Hypothesis 2 partial-confirmed**: SK at the sharp `M_n` threshold
> detects invalidity for sweep + bounce candidate cycles at `n = 5..8`,
> across all enumerated sub-M_n multisets.

"Partial" because the probe only tests two cycle families. The
following questions remain open:

- Do any sub-M_n multisets admit a candidate good cycle with a
  **non-sweep, non-bounce mover sequence** that has `|SK| = 0`? The
  M_5..M_8 witnesses themselves use such cycles (they fall in the gap
  zone `[M_n, 4·3^(n-2))`, not below M_n), so the question is whether
  similar non-sweep cycles exist at sub-M_n products.
- Does the iterative sweep DFS find every sweep candidate cycle, or
  only the "first 3" per starting config? The probe limits to
  `max_found = 3` per mover sequence per multiset.

Both can be addressed by follow-up probes. Neither blocks moving
forward.

## The surprise: per-n |SK| invariance

Every multiset tested at a given n had the **same** |SK| across all
its sweep+bounce candidate cycles, and that |SK| was the **same** for
**every multiset** at that n:

| n | |SK| (constant across all sub-M_n multisets) |
|---|---|
| 5 | **20**  |
| 6 | **52**  |
| 7 | **112** |
| 8 | **240** |
| 9 | **492** (from `probe_sk_n9_witness_2026-04-14.py`) |

Sequence: 20, 52, 112, 240, 492, …

This is a much stronger invariance than the previously-noted
"binary-count invariance" (which said `|SK|` depended only on `(n, k)`
at fixed binary count `k`). The new finding: `|SK|` depends on `n`
**only**, regardless of binary count, ternary count, presence of
quaternary, etc.

Specific examples at n=5 (all yielding `|SK| = 20`):
- `(2,2,2,2,2)` — 5 binary, total state 32
- `(2,2,2,2,3)` — 4 binary, total 48
- `(2,2,2,2,5)` — 4 binary + quinary, total 80
- `(2,2,2,3,3)` — 3 consecutive binary, total 72
- `(2,2,2,3,4)` is *above* M_5 so not in the probe, but earlier work
  showed `|SK| = 20` for sweep cycles there too

The cycles found have different lengths and different `det(C)`
contents across these multisets. Yet the resulting SK has identical
size. This is a non-trivial combinatorial invariant that probably has
a clean structural explanation (cycle length × forced-graph density?
A topological invariant of the forced graph?).

**Open question**: what is the closed form for `|SK|(n)`?

| n | |SK| | difference |
|---|---|---|
| 5 | 20  | — |
| 6 | 52  | 32 |
| 7 | 112 | 60 |
| 8 | 240 | 128 |
| 9 | 492 | 252 |

Differences: 32, 60, 128, 252 — almost doubling but not quite. Second
differences: 28, 68, 124 — also not clean. No obvious closed form yet.
Likely related to the ratio of "non-good configs in the {0,1}
sub-region" to the cycle length, but needs more thought.

## Implications for the SK formalization

The `Theorem.lean` stub currently states T6 with `n ≥ 9` and threshold
`4·3^(n-2)`. The probe data **suggests** (but does not prove) that a
sharper variant is true:

> **For `n ≥ 5` and any sub-`M_n(n)` system with at least one
> sweep-or-bounce candidate cycle, SK is non-empty.**

If we could prove this analytically:
- For `n = 5..8`, this would give us `M_n ≥ 32·3^(n-4)` — sharp.
- For `n ≥ 9`, this would coincide with the current SK claim.
- M_5..M_8 would land as theorems instead of being out-of-scope.

Whether to pursue this depends on:
1. Whether the |SK| invariance has an analytical proof (probably yes,
   but needs investigation).
2. Whether the "for any sweep-or-bounce cycle" hypothesis can be
   strengthened to "for any candidate cycle". This is the harder
   question and is the same one that exists at n ≥ 9 too.

**Conservative recommendation**: leave the SK formalization at `n ≥ 9`
for now, but add a `theorem M_n_lower_smalln` stub in `Theorem.lean`
for `n = 5..8` with a comment pointing at this findings doc. The
proof author can attempt it after T1–T6 land at n ≥ 9.

**Aggressive recommendation**: investigate the |SK| invariance and the
sharper threshold first. If both pan out, restate T6 with `n ≥ 5` and
the per-n M_n threshold (computed from `if n ≤ 8 then 32·3^(n-4) else
4·3^(n-2)`).

## Hypothesis 3: the quaternary investigation

The user explicitly asked about the structural role of the quaternary
in the M_5..M_8 witnesses. Three concrete questions worth probing:

### Q1. What does the M_5 witness's actual good cycle look like?

The M_5 witness is `ms = (2,2,2,3,4)` with a specific TransFn (encoded
somewhere in the existing codebase — try `probes/m5_lower_bound.py`,
`lean/LeanMn/SmallN/Defs.lean` for `w5System`, or
`verifier.py`'s `verify_dijkstra_solution1`). Extract its actual good
cycle and report:

- Cycle length
- Mover sequence (does it look anything like sweep or bounce?)
- Per-position value distribution: does the quaternary visit all 4
  states uniformly, or is one state "hidden"?
- Is there a closed form analogous to `L_0(j)=n, L_1(j)=2(n-2-j),
  L_2(j)=2(j+1)` from the n ≥ 9 wavefront?

### Q2. Does SK detect the M_5 witness's good cycle as valid?

If we run SK on the M_5 witness's actual good cycle (not a sweep), do
we get `|SK| = 0`? This would confirm that:
- (a) the cycle is genuinely the witness's good cycle
- (b) SK is consistent with validity

If `|SK| > 0` for the M_5 witness's actual cycle, something is very
wrong with the SK definition or the probe.

### Q3. Comparison with CLB witness

The CLB witness for n ≥ 9 has `ms = (2, 3^(n-2), 2)` and a 3-phase
wavefront cycle. The M_5..M_8 witnesses have a quaternary instead of
the second binary endpoint. Compare:

- Cycle length: CLB is `3n - 2`; M_5..M_8 cycle length?
- Value distribution structure: CLB has `L_0 = n, L_1 + L_2 = 2n - 2`
  uniform across ternary positions; M_5..M_8 distribution at the
  quaternary?
- Is there a "phase" the quaternary uses that the ternary endpoint
  cannot?

A concrete answer would either:
- Reveal a generalization of the wavefront that subsumes both regimes
  (in which case T4 in the targets doc generalizes nicely)
- Show that the quaternary is doing something fundamentally different
  that requires a separate small-n theorem

### Suggested probe script

`probe_sk_small_n_witness_2026-04-15.py` (not yet written):
1. For each n ∈ {5..8}, find the M_n witness's TransFn (search the
   existing scripts).
2. Extract its actual good cycle.
3. Report cycle length, mover sequence, per-position value
   distribution.
4. Compute SK on the witness's actual cycle. Verify `|SK| = 0`.
5. Compute the binary-cube projection of the witness's good cycle.
6. Compare to the CLB witness wavefront for n=9..11.

This is **discovery only** (§0.5 rule (d)) — it never enters Lean. The
output informs whether hypothesis 3 has structural content or whether
small-n is genuinely "different".

## What this changes for the proof author

The kickoff prompt at `sk_proof_author_kickoff_2026-04-15.md` currently
scopes the work to `n ≥ 9`. This findings doc does **not** change that
recommendation — it just reveals that there might be a path to extend
SK to small n later. The proof author should still focus on `n ≥ 9`
first and treat M_5..M_8 as a possible follow-up.

The new `M_n_lower_smalln` stub theorem in `Theorem.lean` (if added)
would be sorry'd with a comment pointing at this doc.

## Caveats and what we did NOT establish

- The probe tests **sweep + bounce** cycle families only. Other cycle
  types (wiggle, mixed, exotic mover sequences) were not tested. The
  M_n witnesses for n=5..8 may use exotic cycles not in either family.
- The probe finds at most 3 cycles per mover sequence per multiset.
  More cycles may exist with different starting configurations.
- The |SK| invariance is observed empirically across 5,548 cases but
  has no proof. Could be a coincidence at the sample sizes tested,
  though unlikely given the consistency.
- The probe runs on **sub-M_n** products only. We did not test
  exactly-M_n ms with k ≥ 3 binary at small n exhaustively (the
  earlier `probe_sk_threshold_check_2026-04-15.py` covered a few
  representative cases).

These caveats should be addressed by follow-up probes if we decide to
extend SK to small n.

## Files

- `probes/probe_sk_sub_mn_smalln_2026-04-15.py` — the probe
- `probes/probe_sk_threshold_check_2026-04-15.py` —
  earlier probe at exactly-M_n products
- `lean/docs/sk/sk_invariant_lean_targets_2026-04-14.md` —
  T6 (currently `n ≥ 9` only)
- `lean/docs/sk/sk_witness_template_findings_2026-04-15.md` —
  girth-2k templates at n=5..9 (consecutive 3CB)
- `lean/docs/sk/sk_invariant_findings_2026-04-14.md` —
  original empirical SK story
