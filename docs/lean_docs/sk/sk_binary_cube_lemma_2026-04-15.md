# The `|SK|(n)` Closed Form — Analytical Proof Sketch — 2026-04-15

Companion to `sk_small_n_followup_2026-04-15.md` §Probe 3. Records the
analytical proof of the `|SK|(n)` closed form, the structural
characterization of SK for all-binary multisets, and the bijection
conjecture explaining invariance across non-binary multisets.

Verification: `probes/probe_sk_binary_cube_lemma_2026-04-15.py`.

---

## Setup

Fix `n ≥ 5` and a state vector `ms = (m_0, …, m_{n-1})` with each
`m_i ≥ 2`. Let `C` be a sweep cycle on `ms` — i.e., a closed cycle of
length `2n` whose mover sequence is `[0, 1, …, n-1, 0, 1, …, n-1]`
and whose `det`-tracked configurations satisfy unique-privilege and
closure.

Notation:

- `det(C)` = dictionary `(i, L, S, R) ↦ v` recording, at each cycle
  step, the mover's output and every non-mover's "no change"
  commitment.
- `NG(C) = Config(ms) \ C` = the set of non-good configurations.
- `G(C)` = the forced graph on `NG(C)` with an edge `c → c'` at
  position `p` iff `(p, c[p-1], c[p], c[p+1]) ∈ det(C)` and
  `det(C)[…] ≠ c[p]`, where `c'` is `c` with position `p` replaced by
  `det(C)[…]`.
- `SK(C)` = sink kernel of `G(C)`, i.e., the largest subset with no
  sinks under repeated trimming.

Empirical data from probes 3 and 4:

> **`|SK(C)| = 2^n − 2n − ε(n)`** with `ε(n) = 2` for odd `n`, `0` for
> even `n`, **for every sweep cycle `C` on every multiset `ms` with
> `m_i ≥ 2`**, for `n = 5..10`.

Numeric verification:

| n | 2^n − 2n − ε(n) | verified at ms |
|---|---|---|
| 5 | 20 | 7 distinct multisets, all 20 sweep cycles per ms |
| 6 | 52 | 4 distinct multisets, all 30 sweep cycles per ms |
| 7 | 112 | all-binary at n=7 |
| 8 | 240 | all-binary at n=8 |
| 9 | 492 | all-binary at n=9 (from prior probe) |
| 10 | 1004 | all-binary at n=10 |

The closed form holds identically across *every* sweep cycle tested,
even though the *structural content* of SK varies between cycles
(binary cycles have `SK ⊂ {0,1}^n`; cycles that visit value 2 at a
ternary proc have `SK` containing configs with that position equal
to 2).

---

## Lemma A: the binary sweep cycle's SK

The **binary sweep cycle** is the sweep cycle obtained by, at every
mover step, flipping the mover's value between `0` and `1` (skipping
higher values even at ternary/quaternary procs). Such a cycle exists
for any `ms` with `m_i ≥ 2` because the DFS at each step can always
pick `new_val = 1` (if `S = 0`) or `new_val = 0` (if `S = 1`) — the
`det` consistency constraint is satisfied since these are the only
commitments made.

Call this cycle `C*(ms)`. It has `2n` distinct configs, all in
`{0,1}^n`, and `det(C*(ms))` is identical to
`det(C*((2,2,…,2)))` restricted to keys `(i, L, S, R)` with
`L, S, R ∈ {0,1}`.

**Lemma A**. `SK(C*(ms)) = {0,1}^n \ C*(ms) \ Alt(n)` where
`Alt(n) = {(0,1,0,1,…), (1,0,1,0,…)}` if `n` is odd, else `∅`.

**Proof sketch**. Two claims.

**A1. The forced graph `G(C*(ms))` restricted to non-binary configs
is empty.**

If `c` has `c_i = v ≥ 2` for some `i`, then every potential forced
edge at position `p` requires `(p, c[p-1], c[p], c[p+1]) ∈ det`. The
binary cycle only commits keys with `S ∈ {0,1}` and with
`L, R ∈ {0,1}`. Hence:

- At `p = i`: `S = v ≥ 2`, key not in `det`, no edge.
- At `p = i ± 1`: `L` or `R` equals `v ≥ 2`, key not in `det`, no edge.
- At `p` non-adjacent to `i`: key *is* in `det` (since `c[p-1], c[p],
  c[p+1]` are all binary), so there may be an edge, but such edges
  change `c[p]` and leave `c[i]` fixed. The sub-graph restricted to
  configs with `c_i = v` is closed.

The restricted sub-graph on `{c : c_i = v}` with `v ≥ 2` is
isomorphic (by removing position `i`, since `i` contributes no edges
and no non-edges either once its neighbors are fixed) to the forced
graph of the binary sweep on `(m_0, …, m_{i-1}, m_{i+1}, …, m_{n-1})`
with the fixed-value `c_i = v` essentially severing the ring at `i`.
Actually, the closer description: the restricted graph has the
topology of the `{0,1}^(n-3)` subcube at the positions not in
`{i-1, i, i+1}`, since positions `i-1` and `i+1` cannot fire (their
contexts require the neighbor at `i` to be in `{0,1}`, which it
isn't). That subcube has `n − 3 ≥ 2` "free" binary positions.

The forced graph on a 2-or-more dimensional binary subcube under the
sweep-`det` rules of a *shorter* ring might or might not have a
sink-kernel. Empirically, it is always empty for non-binary
starting positions — every config with some `c_i ≥ 2` is eventually
trimmed. The rigorous argument is:

> The sub-forced-graph is a proper subgraph of the `{0,1}^{n-3}`
> subcube with edges at `n − 3` positions only, and is easily seen to
> be acyclic (each edge strictly changes the Hamming weight modulo
> some known pattern). The full argument is a descent on Hamming
> weight + the binary sweep cycle's structure.

**A2. The forced graph `G(C*(ms))` restricted to `{0,1}^n` has SK =
`{0,1}^n \ C* \ Alt(n)`.**

The `det` on a binary sweep cycle is entirely in `{0,1}`, so the
forced graph restricted to `{0,1}^n` is exactly the same graph as for
`ms = (2,…,2)` (the binary cube). The good cycle `C*` is the
"Gray-code-like" cycle of length `2n` through the block configs
`0^n, 1 0^{n-1}, 1 1 0^{n-2}, …, 1^n, 0 1^{n-1}, 0 0 1^{n-2}, …, 0^n`.
The non-good binary configs are `{0,1}^n \ C*`, a set of size
`2^n − 2n`.

Direct analysis of the binary cube forced graph (probe 3 computes it
explicitly):

- The sink-kernel iteratively trims configs with no out-edge in the
  remaining set.
- For `n` even, every non-`C*` binary config is part of a cycle in
  the forced graph, so SK = non-`C*` binary configs, size `2^n − 2n`.
- For `n` odd, the exact alternations `(01)^(⌊n/2⌋)·0` and
  `(10)^(⌊n/2⌋)·1` have a "parity mismatch" on the ring (the last
  bit conflicts with the first under the sweep's ring-wrap) that
  breaks the forced-edge cycle; they are trimmed in the first
  sink-kernel round. All other non-`C*` binary configs remain, giving
  SK of size `2^n − 2n − 2`.

The case split in A2 is verified computationally at `n = 5..10` in
`probe_sk_cardinality_analysis_2026-04-15.py` and the structural
content (which configs are in / out of SK) is recorded there.

Combining A1 and A2: `SK(C*(ms)) = {0,1}^n \ C* \ Alt(n)` and
`|SK(C*(ms))| = 2^n − 2n − 2·[n odd]`. ∎

---

## Conjecture B: cycle invariance

**Conjecture B**. For every sweep cycle `C` on `ms`,
`|SK(C)| = |SK(C*(ms))| = 2^n − 2n − 2·[n odd]`.

**Evidence**. At `n = 5, 6`, across every sub-`M_n` multiset probed
in probe 3, across all 20..30 distinct sweep cycles per multiset,
`|SK(C)|` is constant. Non-binary cycles have non-binary SK content
that varies per-cycle, but total size is always `2^n − 2n − ε(n)`.

**Proof sketch (bijection)**. Let `C` be a non-binary sweep cycle on
`ms`. For each processor `p` with `m_p ≥ 3`, `P_p` fires exactly
twice in `C`; let `{0, a_p}` be the two values `P_p` takes during
`C` (both fires return `P_p` to `0`, so one is `0 → a_p` and the
other is `a_p → 0`). Define the value-restriction map

> `φ: Config(ms) ⇀ {0,1}^n`

by `φ(c)_p = 0` if `c_p = 0`, `1` if `c_p = a_p`, and undefined
otherwise. `φ` is defined exactly on configs in
`∏_p {0, a_p} ⊂ Config(ms)`; its image is `{0,1}^n`.

**Claim**: `φ` restricted to its domain is a forced-graph
isomorphism from `G(C)` (restricted to `dom(φ)`) to `G(C*(ms))`.

- `φ(C) = C*(ms)` (the binary cycle).
- `φ` sends edges to edges: a forced edge at `p` from `c` to `c'` in
  `G(C)` with `c, c' ∈ dom(φ)` corresponds to the same abstract
  transition `(p, L, S, R) → S'` in both cycles, with
  `L, S, R, S' ∈ {0, a_*}` mapping to `{0,1}`.
- `φ` is bijective on its domain.

Hence `|SK(C) ∩ dom(φ)| = |SK(C*)|`.

It remains to show `|SK(C) \ dom(φ)| = 0`. This is the core gap: it
requires that every config NOT in `dom(φ)` (i.e., with some
`c_p ∉ {0, a_p}`) is trimmed during sink-kernel iteration.

For `n = 5, 6` this is verified by exhaustive computation across all
cycles and all sub-`M_n` multisets (probe 3 data; see also the
probe_sk_binary_cube_lemma run below). For `n ≥ 7` it is conjectured.

**Why the claim should hold**: a config `c ∉ dom(φ)` has some
`c_p = b ∉ {0, a_p}`. The cycle's `det` commits no keys with
`S = b` at position `p`, so no edges at `p`. Configs in `c`'s
forced-graph orbit all have `c_p = b` (position `p` fixed). The
orbit is then restricted to `n − 1` "free" positions, which by
Lemma A's proof on the `(n-1)`-proc system is easily shown to be
acyclic once the "frozen" position blocks its neighbors.

---

## Computational verification

Script `probe_sk_binary_cube_lemma_2026-04-15.py` tests Conjecture B
at `n = 5, 6, 7` by enumerating up to 30 sweep cycles per sub-`M_n`
multiset (non-binary multisets only, since the all-binary case is
Lemma A). For each cycle, it computes `|SK|` and checks equality
with `2^n − 2n − ε(n)`. Zero violations observed.

The earlier claim in probe 4's initial run ("non-binary in SK → SK
not contained in `{0,1}^n`") is corrected here: the original claim
that `SK ⊆ {0,1}^n` was specific to the *binary* sweep cycle (Lemma
A). Non-binary sweep cycles do have non-binary SK content, but the
*total count* still matches the formula.

### Exhaustive verification at ms = (2,…,2) — step 1

`probe_sk_exhaustive_binary_2026-04-15.py` enumerates **every** fair
simple closed cycle on the all-binary multiset at `n = 5..9`. The
empirical result:

| n | distinct cycles (up to rotation) | cycle length | `\|SK\|` | match |
|---|---|---|---|---|
| 5 | 320 | 10 | 20 | ✓ |
| 6 | 768 | 12 | 52 | ✓ |
| 7 | 1792 | 14 | 112 | ✓ |
| 8 | 4096 | 16 | 240 | ✓ |
| 9 | 9216 | 18 | 492 | ✓ |

**16,192 total cycles, zero violations.** The count formula is
`c(n) = 2n · 2^n`, a striking combinatorial identity for the number
of fair length-`2n` simple closed cycles in the binary hypercube
under the det-consistency constraint.

**Critical observation**: every cycle has length **exactly** `2n`.
The DFS was permitted to enumerate cycles up to length `4n`, but no
longer simple cycles exist on the binary multiset. This is because:

- Each processor must fire at least twice (fairness + closure at
  `m = 2`).
- Each processor firing `2k ≥ 4` times would require at least two
  distinct mover contexts `(p, L, 0, R)` and `(p, L', 0, R')` for
  the fires from 0, which by det consistency can commit to different
  outputs (both `→ 1`). This is consistent locally, but the global
  coupling of positions (each cycle config has `n − 1` non-mover
  commitments) tightens so aggressively that no length-`> 2n` simple
  cycle exists.
- Empirically verified: DFS reaches `L_max = 4n` and finds **zero**
  cycles of length `> 2n`.

This makes the binary-ms case of Lemma A **exhaustively computable**
at each finite `n`: 16,192 cycles checked at `n = 5..9`, all match.

### From exhaustive verification to a Lean-ready statement

The natural Lean theorem (at each specific `n` in `{5, 6, 7, 8}`):

> `∀ C : SimpleClosedCycle binary_5, fair C → |SK(C)| = 20`

and similarly for `n = 6, 7, 8`. The proof can be structured as:

1. Enumerate the finite set of simple closed cycles (up to
   rotation) in `{0,1}^n` that satisfy the det-consistency
   constraint and fairness. There are 320, 768, 1792, 4096 of them
   at `n = 5, 6, 7, 8`.
2. For each cycle, compute `|SK|` directly and check equality with
   `2^n − 2n − ε(n)`.

Option (a): **`decide` / `fin_cases`** — the cycle set is finite,
the SK computation is a finite forced-graph computation, so a
`decide`-style proof is theoretically available. Problem: at
`n = 8`, 4096 cycles × forced-graph computation per cycle is at the
edge of `decide`'s feasibility, and at `n = 9` probably infeasible.
Also, §0.5 rule 1 forbids `native_decide` on theorem content.

Option (b): **Parametric structural argument**. Prove a single
theorem working for all `n` without case-splitting on cycle shape.
This is what the `{0,1}^n \ goodcycle \ alt[odd n]` characterization
enables — if we can show that the sink-kernel process ALWAYS
produces this set (up to the particular cycle rotation), then |SK|
is constant by construction.

Option (c): **Symmetry argument**. Show the cycles form one orbit
under a group action (rotation + complement + reflection), and SK
is invariant under this group. Then it suffices to compute |SK|
for one canonical cycle. (Attempted above but the orbit count
doesn't cleanly match the symmetry group size — `c(n) = 2n · 2^n`
and `|rotation × complement × reflection| = 4n` means `c(n)/|G|
= 2^(n-2)`, so there are `2^(n-2)` orbits, not a single one.
Symmetry alone does not suffice.)

**The cleanest Lean target**: formalize Lemma A at each specific
`n ∈ {5, 6, 7, 8}` via option (a) (`fin_cases` + explicit finite
enumeration), bounded by the 16,192-cycle total. Each `n` is a
separate finite theorem. A parametric proof (option b) is a
research target, not an immediate formalization target.

---

## Lean target (if pursued)

**T-binary-cube** (Lean). For the all-binary multiset
`ms = (2,2,…,2)` at `n ≥ 5`, `|SK(sweep_cycle)| = 2^n − 2n − 2·[n odd]`.

This is proved via Lemma A: the binary subcube structure is
finite-state and amenable to `fin_cases`-style analysis at each `n`,
or to a parametric proof via the Gray-code characterization of the
sweep cycle.

**T-cycle-invariance** (conjecture). For any `ms` with `m_i ≥ 2` and
any sweep cycle `C` on `ms`, `|SK(C)| = 2^n − 2n − 2·[n odd]`.

This is the harder target, requiring the value-restriction bijection
and the "orbit-acyclicity" sub-claim from Conjecture B's proof sketch.

The conservative path is to formalize T-binary-cube only and leave
T-cycle-invariance as a research conjecture with empirical evidence.

## Caveats and what's NOT proven

- The analytical proof of Lemma A glosses over the case-by-case
  trimming argument for odd `n` alternating configs. A fully
  rigorous version would enumerate the sink-kernel trimming rounds
  on the binary cube and show the alternating configs are trimmed
  in round 1.
- Conjecture B's "orbit-acyclicity" sub-claim is only verified at
  `n ≤ 6` exhaustively; `n = 7` and beyond rely on template coverage
  from probe 2, which is sparse.
- The per-multiset invariance `|SK|(n)` constant across `ms`
  shape-variants is empirically tight but not yet a theorem beyond
  Lemma A's all-binary case.

## Files

- `probes/probe_sk_binary_cube_lemma_2026-04-15.py`
  — initial empirical check (revealed the "binary sweep" scoping
  issue). Caveat: this first run flags non-binary cycles as
  "violations" of the SK ⊆ `{0,1}^n` claim; these are Conjecture-B
  cases, not actual violations of the `|SK|` closed form.
- `probes/probe_sk_cardinality_analysis_2026-04-15.py`
  — the formula verification at `n = 5..10`.
- `sk_small_n_followup_2026-04-15.md` — companion doc with probes
  1, 2, 3 findings.
- `sk_invariant_findings_2026-04-14.md` — the original empirical SK
  story (which is where the `|SK|(n) = 2^n − 2n − ε(n)` formula was
  first pinned).
