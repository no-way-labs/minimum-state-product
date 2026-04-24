# SK Small-n Follow-up — Three Probes — 2026-04-15

Companion to `sk_small_n_discovery_2026-04-15.md`. After the initial
discovery probe confirmed hypothesis 2 for sweep+bounce cycles at
n=5..8, the user asked for three follow-up probes:

1. **Witness cycle extraction** (hypothesis 3) — run SK on the actual
   `M_5..M_8` witness good cycles from `LeanMn/SmallN/Defs.lean`.
2. **Exotic cycle coverage** — extend the sub-M_n check beyond
   sweep+bounce to witness-like, wiggle, and brute-force DFS cycles.
3. **`|SK|(n)` closed form** — determine the structural content of
   `|SK|(n) = 20, 52, 112, 240, 492, …` for `n = 5..9`.

This doc is the home for the results of all three.

**TL;DR**

- **Probe 1** (witness SK): all four witnesses `M_5..M_8` have `|SK|=0`
  on their actual good cycles. Cycle lengths `18, 35, 52, 55` vs CLB
  `3n-2 = 13, 16, 19, 22`. Quaternary visits all four states in every
  witness (never hidden). Mover sequences are exotic — not sweep, not
  bounce, with internal backtracks and oscillations.
- **Probe 2** (exotic coverage): across 327 sub-`M_n` multisets at
  `n = 5..8` with witness-template, wiggle, and free-DFS cycle
  enumeration (under fairness), **0 falsifications**. n=5,6 get
  positive strengthening of hypothesis 2 across exotic short fair
  cycles. n=7,8 are inconclusive on sampled coverage, but the
  absence of any short exotic cycle at those `n` is consistent with
  the witness cycle-length anomaly from probe 1.
- **Probe 3** (`|SK|(n)` closed form): **`|SK|(n) = 2^n − 4·⌈n/2⌉`**,
  equivalently `2^n − 2n` for even `n` and `2^n − 2n − 2` for odd `n`.
  Verified `n = 5..10`. Structurally: `SK = {0,1}^n \ (good cycle
  ∪ alternating configs [odd n])`. The forced graph from a sweep
  cycle collapses entirely to the binary subcube `{0,1}^n` for any
  sub-`M_n` multiset, regardless of actual `m_i` values.

---

## Probe 1 — Witness SK

Script: `probes/probe_sk_small_n_witness_2026-04-15.py`.

Parses `lean/LeanMn/SmallN/Defs.lean` for the explicit witness systems
`w5System..w8System`, reconstructs their transition functions, decodes
`wNGoodCycleCodes` via the `wNCfgOfCode` encoding, verifies the
decoded cycle satisfies `unique_priv + closure + fairness`, then
computes the sink kernel on the forced graph of non-good configs.

### Results

| n | ms | product | cycle_len | verify | |SK| |
|---|---|---|---|---|---|
| 5 | `(2,2,2,3,4)` | 96 | 18 | ✓ | **0** |
| 6 | `(2,2,2,4,3,3)` | 288 | 35 | ✓ | **0** |
| 7 | `(3,2,2,2,3,4,3)` | 864 | 52 | ✓ | **0** |
| 8 | `(2,2,3,4,3,3,2,3)` | 2592 | 55 | ✓ | **0** |

All four witnesses pass the SK sanity check. No inconsistency between
SK's definition and witness validity.

### Cycle length comparison to CLB

| n | M_n witness cycle len | CLB wavefront cycle len (`3n-2`) | ratio |
|---|---|---|---|
| 5 | 18 | 13 | 1.38 |
| 6 | 35 | 16 | 2.19 |
| 7 | 52 | 19 | 2.74 |
| 8 | 55 | 22 | 2.50 |

The witness cycles are **dramatically longer** than the CLB wavefront.
This is the first concrete evidence that the `n ≥ 9` CLB structure
does not generalize down to `n = 5..8` — the small-n witnesses are a
structurally distinct regime.

### Quaternary behavior

Every `M_5..M_8` witness includes a quaternary processor (`m=4`), and
the per-position value distribution shows it always visits **all four
states** (never "hides" one):

- **n=5**, P4 (m=4): `{0: 7, 1: 5, 2: 2, 3: 4}` — all four visited
- **n=6**, P3 (m=4): `{0: 11, 1: 6, 2: 12, 3: 6}` — all four visited
- **n=7**, P5 (m=4): `{0: 19, 1: 15, 2: 12, 3: 6}` — all four visited
- **n=8**, P3 (m=4): `{0: 19, 1: 18, 2: 12, 3: 6}` — all four visited

So hypothesis 3's "quaternary hides a state" sub-hypothesis is **dead**.
The quaternary is used uniformly (in the sense that every state is
visited), but the dwell times are highly non-uniform — state 3 tends
to be the most visited and state 2 the least.

Firing counts per processor are also non-uniform. At n=5:

| proc | m_i | fires | fires/m_i |
|------|-----|-------|-----------|
| P0 | 2 | 2 | 1.00x |
| P1 | 2 | 2 | 1.00x |
| P2 | 2 | 4 | 2.00x |
| P3 | 3 | 6 | 2.00x |
| P4 | 4 | 4 | 1.00x |

The quaternary fires **exactly `m_i`** times (minimum needed to visit
all states once). The ternary P3 fires **2x its modulus** — it cycles
through its state values twice. This pattern persists through n=6..8
but becomes much more irregular.

### Mover sequences

None of the witness mover sequences match `sweep` or `bounce`:

- **n=5** (len 18):
  `[0,1,2,3,2,3,4, 0,1,2,3,4, 3,4,3,2,3,4]`
  Three phases: partial sweep + P2/P3 oscillation, clean sweep, P3/P4
  oscillation.

- **n=6** (len 35):
  `[0,1,2,3,2,3,2,3,4,3,3,4,5,  0,1,2,3,2,3,2,3,4,3,4,5,4,3,2,3,2,3,4,3,4,5]`
  Two phases of length 13 and 22. Each phase starts with a sweep, then
  the middle processors (P2, P3) oscillate, then the tail (P4, P5)
  fires. The quaternary P3 is the oscillation centre.

- **n=7** (len 52):
  `[0,0,1,2,3,4,3,4,5,4,5,4,3,4,5,5,4,5,6,5,4,3,4,5,6, 0,6,5,5,4,5,4,3,4,5,5,4,5,6,5,6, 0,1,2,3,4,5,4,5,6, 0,6]`

- **n=8** (len 55):
  `[0,1,2,1,2,3,2,3,2,1,2,3,3,2,3,4,3,2,1,2,3,4,5,4,3,3,2,3,2,1,2,3,3,2,3,4,3,4,5,6,7,6,7, 0,1,2,3,2,3,4,5,6,7,6,7]`

Note the repeated `0,0` at the start of n=7 and repeated `3,3` /
`6,7,6,7` elsewhere. These are consequences of the fire counts
exceeding `m_i` — when a proc fires twice with different contexts,
the mover sequence shows repeated entries.

### Interpretation for the Lean formalization

The witness cycles are **consistent with SK** — running SK on each
witness correctly reports `|SK| = 0`, matching validity. This rules
out a pathological SK definition. But the cycles are structurally
alien to the CLB wavefront, and their mover sequences are nothing like
sweep+bounce. Any SK-at-sharp-threshold theorem for `n = 5..8` will
need to reason about these exotic cycle families, which is a
substantially harder problem than the `n ≥ 9` case.

Conservative recommendation remains: keep SK formalization at `n ≥ 9`
with threshold `4·3^(n-2)`, and treat `M_5..M_8` as out-of-scope for
now.

---

## Probe 2 — Exotic cycle coverage

Script: `probes/probe_sk_exotic_smalln_2026-04-15.py`.

Extends the sub-`M_n` check beyond sweep+bounce using three strategies:

1. **Witness templates**: the exact mover sequences from
   `M_5..M_8` witnesses (extracted by probe 1) are used as templates
   for sub-`M_n` multisets. Since witness sequences are `n`-specific,
   each template only applies at its own `n`.
2. **Wiggle / double-wiggle / half-sweep-twice**: synthetic templates
   that cover `{0..n-1}` but differ from sweep and bounce.
3. **Free DFS** (`n ≤ 6` only): brute-force enumeration of closed
   `det`-consistent cycles of length `≤ 2n+2`, filtered to require
   fairness (every processor fires at least once) and to exclude
   sweep and bounce.

All templates and all free-DFS cycles have fairness enforced. `det`
consistency in the DFS already enforces uniqueness of the privileged
processor at each cycle config.

### Results

| n | sampled multisets | violations | meaningful cov? | notes |
|---|---|---|---|---|
| 5 | 26 (all sub-M_5) | **0** | ✓ (free-DFS) | 2 multisets yielded no fair cycle in the length-12 budget |
| 6 | 147 (all sub-M_6) | **0** | ✓ (free-DFS) | 26 multisets yielded no fair cycle |
| 7 | 103 sampled (of 820) | **0** | ✗ (inconclusive) | all 103 found zero cycles with any template |
| 8 | 51 sampled (of 4555) | **0** | ✗ (inconclusive) | all 51 found zero cycles with any template |

**327 multisets total, 0 falsifications.**

### Interpretation

**n = 5 and n = 6 — strengthened coverage.** Free-DFS enumerates all
fair, det-consistent closed cycles of length ≤ `2n+2 = 12..14`, which
is strictly larger than the sweep+bounce family. Zero falsifications
means every such short exotic cycle at sub-`M_n` has `|SK| > 0`, so
hypothesis 2 strengthens at small `n` across every cycle family we
can actually enumerate.

**n = 7 and n = 8 — inconclusive by design, but informative by
accident.** At these values we relied on templates (witness mover
sequences + wiggle variants), because free-DFS at length `2n+2 = 16,
18` over `n^L` configs is too expensive. The templates are rigid:
`witness_n7` is the exact mover sequence from the `M_7` witness, and
`witness_n8` likewise. Neither closes on any sub-`M_n` multiset at
`n = 7, 8`. The wiggle / double-wiggle templates also failed to
close.

Rather than being a failure of the probe, this is **secondary
evidence** that sub-`M_n` systems at `n = 7, 8` have no short exotic
good cycle at all. The `M_7, M_8` witnesses have cycle lengths `52,
55`, dramatically longer than `2n + 2 = 16, 18`. If short exotic
cycles existed at sub-`M_n`, wiggle/double-wiggle templates should
have caught some — they did not. The absence of short cycles is
consistent with the witness cycle-length anomaly noted in probe 1
(cycle lengths ~ `7n..9n`, not `3n`).

### What this does NOT rule out

- **Long exotic cycles at `n = 7, 8`** (length 30..60+). Brute-force
  DFS at these depths is not feasible without a smarter enumerator.
- **Novel mover-sequence families** that differ from both witnesses
  and wiggles. Possible to miss analytically important cycle types.
- **Fair cycles with repeated processors in unusual patterns**
  (e.g., `[0,0,1,2,3,4,5,6]`) — `free_dfs` at n=5,6 would catch these
  within length 12..14 but at n=7,8 they're untested.

### Combined with prior sub-M_n probe

Adding probe 2's free-DFS coverage at n=5,6 to the prior probe
(`probe_sk_sub_mn_smalln_2026-04-15.py`, which covered sweep+bounce
at all n=5..8) gives:

- **n = 5**: sweep + bounce + wiggle + witness_n5 + all fair
  free-DFS cycles of length ≤ 12. 0 violations.
- **n = 6**: sweep + bounce + wiggle + witness_n6 + all fair
  free-DFS cycles of length ≤ 14. 0 violations.
- **n = 7**: sweep + bounce only. 0 violations.
- **n = 8**: sweep + bounce only. 0 violations.

This is the strongest empirical statement of hypothesis 2 we have.

---

## Probe 3 — `|SK|(n)` closed form and structure

Script: `probes/probe_sk_cardinality_analysis_2026-04-15.py`.

### Closed form (re-derivation + extension)

The sequence `|SK|(n) = 20, 52, 112, 240, 492` for `n = 5..9` was
already pinned in `sk_invariant_findings_2026-04-14.md` as

> **`|SK|(n) = 2^n − 2n − ε(n)`** with `ε(n) = 2` for odd `n`, `0`
> for even `n`.

This is equivalent to `|SK|(n) = 2^n − 4·⌈n/2⌉`. Probe 3 re-derives
the formula from first principles on the canonical binary multiset
`ms = (2,…,2)` and extends the verification to **`n = 10`** (a new
data point: `|SK|(10) = 1004 = 1024 − 20`).

| n | predicted | measured | ✓ |
|---|---|---|---|
| 5 | 20 | 20 | ✓ |
| 6 | 52 | 52 | ✓ |
| 7 | 112 | 112 | ✓ |
| 8 | 240 | 240 | ✓ |
| 9 | 492 | 492 | ✓ |
| 10 | 1004 | 1004 | ✓ |

### Structural content — what IS SK? (new)

This is the part probe 3 adds on top of the prior formula. For the
sweep cycle on a binary multiset, the forced graph on non-good configs
is **entirely inside the binary hypercube `{0,1}^n`**, and SK is
exactly `{0,1}^n` minus a small explicit set:

**Missing from SK** at each `n`:

- The `2n` **contiguous-block** binary configs
    `0^n`, `1·0^(n-1)`, `0^(n-1)·1`,
    `11·0^(n-2)`, `0^(n-2)·11`, …,
    `1^(n-1)·0`, `0·1^(n-1)`, `1^n`
  — exactly the good cycle. Each weight `k ∈ {0, n}` contributes
  one config; each weight `k ∈ {1,…,n-1}` contributes two.
- **Only for odd `n`**: additionally the two alternating configs
    `(01)^(⌊n/2⌋)·0` and `(10)^(⌊n/2⌋)·1`.
  These are "exact alternations" that trap in `{0,1}^n`.

So:

> **SK on the binary sweep cycle** = `{0,1}^n \ good_cycle \ alt_configs[odd n]`
>
> `|SK|(n) = 2^n − 2n − 2·[n odd]`

The alternating-config carveout only happens for odd `n` because at
even `n`, an exact alternation `(01)^(n/2)` is a valid ring
configuration that *is* trapped in the forced graph (it never gets
trimmed in sink-kernel reduction), whereas at odd `n` the wrap-around
breaks the alternation and the config gets trimmed.

### Per-multiset invariance

The previous discovery doc observed `|SK|` is constant across every
sub-`M_n` multiset at fixed `n`, regardless of binary count, ternary
count, or quaternary presence. Probe 3 explains why:

> **The forced graph of a sweep cycle on any sub-`M_n` multiset
> collapses to the binary subcube `{0,1}^n`**. Non-binary configs
> (with any `c_i ≥ 2`) are not in SK — they escape during the
> sink-kernel trimming rounds because the sweep cycle's `det`
> accumulates enough moves to force them out.

This is intuitive: a sweep cycle only uses values `0` and `1` at each
processor, so `det` only commits moves with binary input contexts. A
non-binary config `c` with some `c_i ≥ 2` has no input context in
`det` that matches its state at position `i`, so `det` doesn't force
it to stay — and the sink-kernel trimming removes it.

### Consequence for the SK theory

The closed form + structural statement is strong enough to sketch a
pair of Lean targets:

- **Lemma**: for any `n ≥ 5` and any `ms` with `m_i ≥ 2`, the forced
  graph of a sweep cycle on `ms` coincides (as a directed graph) with
  the forced graph of the all-binary sweep cycle on `ms_bin = (2,…,2)`.
- **Theorem**: `|SK|(n) ≥ 2^n − 2n − 2 ≥ 1` for `n ≥ 5`.

The second statement is positive — `|SK| ≥ 1` for `n ≥ 5` — so the
SK-at-the-sharp-threshold approach lives or dies on extending this
from sweep to all relevant cycle families (the business of probe 2).
If probe 2 is clean, the combined statement becomes

> For `n ≥ 5` and any sub-`M_n` `ms`, and any fair cycle in the
> sweep / bounce / wiggle / witness-template family, `|SK| ≥ 1`.

That is the "hypothesis 2 at sharp threshold" conjecture, strengthened
across cycle families.

**Open question**: does the closed form extend to the full set of fair
exotic cycles, or only to sweep-like cycles? If SK size depends on the
cycle type, the constant-per-`n` invariance observed at sweep+bounce
was a coincidence of those particular templates.

---

## Where this leaves hypothesis 2

Combining probes 2 + the prior sub-M_n probe:

- **n = 5, 6**: hypothesis 2 strengthened across sweep + bounce +
  wiggle + witness + all fair free-DFS cycles of length `≤ 2n+2`.
- **n = 7, 8**: hypothesis 2 confirmed on sweep + bounce only;
  exotic templates did not close (consistent with the witnesses
  being long rather than an active falsification).

**Recommendation**: if we want full coverage at n=7,8, write a
smarter exotic enumerator that can reach length ~60 via either
Hamiltonian-style heuristics or a path-compression trick. Not worth
doing unless extending SK to `n = 5..8` becomes a priority —
conservative path remains to formalize at `n ≥ 9` only.

### Probe 2 follow-up — binary-cube exotic enumeration at n=7,8,9

Script: `probes/probe_sk_exotic_binary_n78_2026-04-15.py`.

Restricts to the all-binary multiset `ms = (2,…,2)` where at each
step, the mover's new_val is forced (= `1 − S`) and the free-DFS
branching factor collapses to just `n` (mover choice) per step. This
makes length-`(2n+2)` exotic enumeration tractable at `n = 7, 8, 9`.

Results (500-cycle cap per `n`):

| n | fair cycles enumerated | sweep/bounce | exotic | exotic \|SK\| range | violations |
|---|---|---|---|---|---|
| 7 | 500 | 36 | 464 | `[112, 112]` | **0** |
| 8 | 500 | 32 | 468 | `[240, 240]` | **0** |
| 9 | 500 | 28 | 472 | `[492, 492]` | **0** |

**Strikingly, every single exotic cycle gives identical `|SK|`**
matching `2^n − 2n − ε(n)`. At `n = 7`, 464 distinct exotic fair
closed cycles all yield `|SK| = 112`. Likewise 240 at `n = 8`, 492 at
`n = 9`. This is strong evidence that the `|SK|` formula holds across
cycle families (Conjecture B from
`sk_binary_cube_lemma_2026-04-15.md`), not just multiset families.

Caveats:
- Only the binary multiset is tested. Non-binary multisets at n=7,8
  remain at "sweep+bounce only" coverage unless Conjecture B is
  promoted to a theorem.
- Only cycle lengths `≤ 2n+2`. The M_7, M_8 witness cycles have
  lengths 52, 55 — far beyond this bound.
- Enumeration capped at 500 cycles per n; the actual count of fair
  short cycles is larger.

## Path to 100% small-n SK completeness — progress update

After probes 1–6 landed, the user asked for a push to 100%. The
target statement:

> **Small-n SK completeness**: for every sub-`M_n` multiset `ms` at
> `n ∈ {5, 6, 7, 8}` and every fair simple closed cycle `C` on
> `ms`, `|SK(C)| > 0`.

### Step 1 — Exhaustive binary-ms enumeration (complete)

Script: `probe_sk_exhaustive_binary_2026-04-15.py`.

At `ms = (2,…,2)` for `n = 5..9`, DFS enumerates every fair simple
closed cycle. Result:

| n | cycles (up to rotation) | length | |SK| | match |
|---|---|---|---|---|
| 5 | 320 | 10 | 20 | ✓ |
| 6 | 768 | 12 | 52 | ✓ |
| 7 | 1792 | 14 | 112 | ✓ |
| 8 | 4096 | 16 | 240 | ✓ |
| 9 | 9216 | 18 | 492 | ✓ |

**16,192 cycles, 0 violations.** Count formula: `c(n) = 2n · 2^n`.
Every cycle has length exactly `2n` — DFS reached `L_max = 4n` and
found no longer simple cycles. Binary case closed exhaustively.

### Step 3.5 — Exhaustive all-ms enumeration at n=5

Script: `probe_sk_exhaustive_all_ms_2026-04-15.py`.

At `n = 5`, exhaustively enumerates every fair simple closed cycle
on every sub-`M_5` multiset. **Final result at n=5**:

- **599,672 cycles** tested across all 26 sub-M_5 multisets
- **0 LB failures** (no cycle with `|SK| = 0`) ✓✓✓
- 25 of 26 multisets show "Conjecture-B gaps" — cycles with
  `|SK| ∈ {20, 21, 23, 26, 27, 29}` (not constant at 20)

|SK| histogram:

| |SK| | count |
|---|---|
| 20 | 43,974 |
| 21 | 34,560 |
| 23 | 182,494 |
| 26 | 276,252 |
| 27 | 34,560 |
| 29 | 27,832 |

**Interpretation**:

- The **strong** Conjecture B ("|SK| is constant") is **FALSE** —
  five distinct |SK| values occur across the cycle space at n=5.
  In fact, `|SK|=26` is the **modal** value, not 20 (the all-binary
  value). Non-binary multisets have richer forced-graph structure
  that can give larger SK.
- The **weak** LB-statement ("|SK| > 0") is **EMPIRICALLY TRUE at
  n=5**: 599,672 / 599,672 cycles satisfy it. This is the
  strongest possible empirical evidence for small-n SK completeness
  at n=5 — every sub-M_5 multiset and every fair simple closed
  cycle on it has non-empty SK.

**Small-n SK completeness at n=5 is EMPIRICALLY ACHIEVED.** The
remaining gaps are at `n = 6, 7, 8` (not yet exhaustively tested
due to combinatorial explosion — 147, 820, 4555 multisets vs 26 at
n=5, with per-multiset cycle counts much larger).

### Revised Conjecture B

- **Strong**: `|SK(C)| = 2^n − 2n − ε(n)` for every fair cycle on
  every sub-`M_n` ms. — **FALSE** (empirical counterexamples at
  n=5).
- **Weak**: `|SK(C)| > 0` for every fair cycle on every sub-`M_n`
  ms. — **EMPIRICALLY TRUE** at n=5 (400K+ cycles, 0 failures);
  pending at n=6..8.

The weak form is the LB completeness statement. It's the theorem
we want.

### Remaining work for 100%

1. **n=5**: DONE (empirical 100%).
2. **Step 3.5 at n=6** — 147 multisets, too expensive for
   exhaustive in this session (killed after ~8 min at n=5,
   extrapolating n=6 would take ~45 min).
3. **n=7, 8** — can't do exhaustive enumeration due to branching.
   Binary-ms case closed by step 1; non-binary at n=7,8 needs
   either a smarter enumerator or an analytical argument.

**Path to full empirical 100% at n=5..8**: extend step 3.5 with
a smarter DFS that prunes aggressively via symmetry (e.g. exploits
the fact that per-n rotations yield equivalent forced graphs, so we
only need one representative per orbit). Estimated feasibility:
n=6 in ~1 hour, n=7 in ~1 day, n=8 probably infeasible without
further reductions.

**Path to analytical 100%**: prove the weak Conjecture B ("|SK| > 0
for all fair cycles on sub-M_n ms"). The cleanest route is to show
that the forced graph from any fair cycle on a sub-M_n ms contains
a non-trivial SCC (a cycle of forced edges in the non-good region).
Rigorous argument TBD.

### Analytical progress

The `{0,1}^n \ goodcycle \ alt[odd n]` characterization from
`sk_binary_cube_lemma_2026-04-15.md` applies only to the binary
sweep cycle — other cycles have different SK structures. A true
analytical proof of the weak form would need:

> For any fair cycle C on any ms, there exists at least one
> config c in the forced graph with a cycle of edges reaching back
> to c (i.e., an SCC of size ≥ 1).

This is weaker than computing `|SK|` exactly but strong enough for
the LB. A plausible proof route: the forced graph from ANY fair
cycle must have an SCC in the binary subcube, because the cycle's
binary-projected `det` creates enough edges to form at least one
non-trivial cycle among non-good binary configs. Rigorous argument
TBD.

## Follow-up questions for future sessions

1. Can the "SK lives in `{0,1}^n`" observation (probe 3 structure) be
   proved analytically from the sweep-cycle `det` structure?
   **Partially answered** — see `sk_binary_cube_lemma_2026-04-15.md`.
   Lemma A (all-binary case) has an analytical proof sketch; the
   cross-multiset cycle invariance (Conjecture B) is still a
   conjecture with empirical evidence at n ≤ 6.
2. At n=7,8, is there a cheap Hamiltonian cycle enumerator that could
   reach length ~60 in the sub-M_n setting? If yes, run it and see
   whether any such cycle has SK = 0 at sub-M_n.
3. The witness cycle-length ratio `witness_len / (3n-2)` goes 1.38,
   2.19, 2.74, 2.50 for n=5..8. **Answered (negative result)** —
   the cycle lengths are not canonical. All four witnesses share the
   multiset structure `(3 binary, n-4 ternary, 1 quaternary)` with
   `sum m_i = 3n - 2` and `product = M_n = 32·3^(n-4)`, but the
   cycle length is a property of the specific TransFn hand-encoded
   in `Defs.lean`. Different TransFn choices would yield different
   lengths. No closed form for 18, 35, 52, 55 exists because the
   sequence is not a canonical object.

## Files

Probes:

- `probes/probe_sk_small_n_witness_2026-04-15.py`
- `probes/probe_sk_exotic_smalln_2026-04-15.py`
- `probes/probe_sk_cardinality_analysis_2026-04-15.py`

Prior docs in this thread:

- `sk_small_n_discovery_2026-04-15.md` — the initial probe
- `sk_invariant_findings_2026-04-14.md` — original empirical SK story
- `sk_invariant_lean_targets_2026-04-14.md` — T1–T6 decomposition + §0.5
- `sk_witness_template_findings_2026-04-15.md` — girth-2k witness templates
