# Information-Theoretic Memo

Date: April 5, 2026

Scope: extract the strongest information-theoretic formulation currently visible
in the lower-bound problem, while explicitly separating dead ends from surviving
structure.

This memo follows the residue workflow recorded in
`info_theory/exploration_log.md`.

## Executive point

The threshold does **not** appear to live in:

- raw table capacity,
- good-cycle local-context counts,
- good-cycle local-context entropy,
- mover-bit decoding cost,
- or privileged-cylinder cover counts.

Those quantities are all far too loose on valid witnesses.

The only information-theoretic object that currently looks nontrivial is the
**distributed encoding of the bad-side descent ranking**. If an info-theoretic
proof exists, it should attack convergence as a distributed code/orientation
problem, not good-cycle existence as a capacity problem.

## 1. Good Cycle = Zero-Error Local Classification

Fix a good cycle `g_0, ..., g_{CL-1}` and define, for processor `i`:

- `C_i(k) = (g_k[i-1], g_k[i], g_k[i+1])`
- `R_i(k) = 1[moverAt(k) = i]`

Then entry-conflict freedom at processor `i` is exactly:

- mover support `supp(C_i | R_i = 1)` and non-mover support
  `supp(C_i | R_i = 0)` are disjoint.

Equivalently:

- `R_i` is zero-error decodable from `C_i` on the good cycle.

This is the cleanest information-theoretic translation of entry conflict.

### Why this is not enough

For `CUP-2(n=9)`:

- `CL = 25`, `product = 8748`
- binary endpoints use only `7` local contexts total
- boundary ternaries use `8`
- interior ternaries use `9`
- mover-bit entropy is only:
  - `0.402` bits at binary endpoints
  - `0.529` bits at ternaries

For `Sol3(n=9)`:

- `CL = 48`, `product = 19683`
- local supports are only `12` or `15`
- mover-bit entropy is only `0.337` or `0.544` bits

So a per-processor “how many bits are needed to know whether I move?” story
cannot explain the threshold. Valid systems already do that with tiny local
information.

## 2. Support/Entropy Bounds on the Good Cycle Are Loose

Let `s_i = |supp(C_i)|` on the good cycle.

By Shearer’s inequality, because each global coordinate appears in exactly three
local contexts,

`log CL <= (1/3) Σ_i log s_i`

hence

`CL <= (Π_i s_i)^(1/3) <= P`.

This is the right entropy-style inequality for the cycle side, but it is very
weak numerically.

Examples:

- `CUP-2(n=9)`: `CL = 25`, bound gives `CL <= 569.98`
- `Sol3(n=9)`: `CL = 48`, bound gives `CL <= 2908.49`

So even support-sensitive entropy bounds do not come close to the threshold.

## 3. Liveness = Privileged-Cylinder Cover

Let `P_i` be the set of privileged local contexts in processor `i`'s table, and
let `L_i = m_{i-1} m_i m_{i+1}`.

Each privileged local context lifts to a cylinder in the global configuration
space of relative measure `1 / L_i`.

Liveness therefore implies the exact cover inequality:

`Σ_i |P_i| / L_i >= 1`.

This is a valid information-theoretic/counting statement. It is just not tight.

Examples at `n=9`:

- `CUP-2`: `Σ_i |P_i| / L_i = 4.592593`
- `Sol3`: `4.444444`

The cover floor is satisfied with a lot of slack. So liveness-cover counting
does not locate the threshold either.

## 4. Good Set Is Not the Single-Privileged Set

This matters because many info-theoretic stories implicitly identify “one-hot
privilege” with “good.”

That is false.

For `CUP-2(n=9)`:

- total single-privileged configurations: `79`
- good configurations: `61`
- bad single-privileged configurations: `18`

So any information-theoretic model that only tracks one-hot privilege patterns
is incomplete. The distinction between “single-privileged” and “actually on the
closed legitimate set” is part of the hard problem.

## 5. The First Nontrivial Information Object: Bad-Side Rank

For a valid system, convergence is equivalent to the bad-config graph being a
DAG. That gives a canonical rank:

- `rank(c) =` longest bad-path length from `c` down to the good set.

This is global information.

The natural information-theoretic question is:

- how much of `rank(c)` is visible from local radius-1 observations?

### Measured answer

For `CUP-2(n=9)`:

- bad configs: `8687`
- `max_rank = 52`
- `H(rank) = 5.2733` bits
- but `I(C_i; rank)` for one processor lies only in `[0.1486, 0.4013]` bits
- `I(|Priv(c)|; rank) = 0.3763` bits
- even `I(Priv(c); rank) = 1.7838` bits

For `Sol3(n=9)`:

- bad configs: `19587`
- `max_rank = 108`
- `H(rank) = 6.3383` bits
- `I(C_i; rank)` lies only in `[0.2178, 0.3235]` bits
- `I(|Priv(c)|; rank) = 0.6897` bits
- `I(Priv(c); rank) = 2.7233` bits

This is the first place where the information-theoretic viewpoint looks
substantive rather than cosmetic:

- the descent certificate is genuinely distributed,
- no single local view sees much of it,
- and even the whole privileged-set identity sees only part of it.

## 6. Working Hypothesis

If an information-theoretic lower bound exists, it should look more like:

- a lower bound on the distributed information needed to encode an acyclic
  descent scheme on the bad-config graph,

than like:

- a lower bound on good-cycle local-context capacity.

In other words:

- the threshold likely lives in the **distributed encoding of convergence**,
  not in the **local encoding of legitimacy**.

## 7. Concrete Next Targets

These are the most promising next steps from an information-theory angle.

## 8. New Constructive Structure: Window Codes for Bad-Side Rank

The biggest new development is constructive, not just obstructive.

For the canonical bad-side rank `rank(c)`, we fit additive overlapping-window
models

`rank(c) ~= const + Σ_i g_i(window_i(c))`

where `window_i(c)` is a cyclic block of consecutive processor states.

### Raw hierarchy

For `CUP-2(n=9)`:

- width `3` / radius-1 style: `R^2 = 0.8787`
- width `4`: `0.9344`
- width `5`: `0.9662`
- width `6`: `0.9884`
- width `7 = n-2`: `0.9979`
- width `8 = n-1`: `0.99998`, exact after rounding

For `Sol3(n=9)`:

- width `3`: `0.7723`
- width `4`: `0.8698`
- width `5`: `0.9327`
- width `6`: `0.9739`
- width `7 = n-2`: `0.9954`
- width `8 = n-1`: `0.99997`

Across `CUP-2(n=5..12)`, width `n-1` is exact after rounding in every tested
case.

### Critical correction: null-model calibration

That top-width exactness is **not** by itself deep. The width-`n-1` model is so
expressive that even shuffled or random targets fit extremely well.

Example at `n=9`:

- `CUP-2`, width `8`:
  - actual `R^2 = 0.99998`
  - shuffled rank `0.99277`
  - random target `0.99265`

- `Sol3`, width `8`:
  - actual `0.99997`
  - shuffled `0.97704`
  - random `0.97503`

So width `n-1` exactness is partly a capacity artifact.

### The meaningful invariant: width `n-2`

One step below that ceiling, the story changes. Width `n-2` remains strongly
special for the true rank and clearly beats the null models.

For `CUP-2(n=9)`, width `7`:

- actual `R^2 = 0.99788`
- shuffled rank `0.66925`
- random target `0.66538`

For `Sol3(n=9)`, width `7`:

- actual `0.99537`
- shuffled `0.57161`
- random `0.57237`

Across `CUP-2(n=5..12)`, width `n-2` actual-vs-null behaves as:

- actual: `0.9684, 0.9839, 0.9906, 0.9953, 0.9979, 0.9989, 0.9994, 0.9997`
- shuffled/random: roughly `0.54` to `0.74`

This is currently the strongest nontrivial information-theoretic signal in the
entire exploration.

## 10. Even Stronger: Forbidden Interaction Energy

The regression view can be sharpened into exact harmonic analysis.

For the width-`n-2` model, the forbidden interaction supports are exactly the
subset interactions not contained in any length-`n-2` window. Equivalently,
their complements contain no adjacent pair. On the cycle, these are the
vertex-cover-type supports.

Using the exact ANOVA decomposition of the full-space extension

- `F(c) = 0` on good configs,
- `F(c) = rank(c) + 1` on bad configs,

we can ask how much `L^2` energy lies on those forbidden supports.

### What happens

For the true rank extension, that forbidden mass is tiny.

At `n=9`:

- `CUP-2`: forbidden fraction `0.000243`
- `Sol3`: `0.000496`

For shuffled labels:

- `CUP-2`: `0.037269`
- `Sol3`: `0.046499`

Across sizes the same decay appears.

`CUP-2(n=5..9)` actual vs shuffled:

- `0.017567 vs 0.156007`
- `0.004541 vs 0.102526`
- `0.001877 vs 0.078132`
- `0.000686 vs 0.055796`
- `0.000243 vs 0.038038`

`Sol3(n=4..9)` actual vs shuffled:

- `0.138680 vs 0.375847`
- `0.029677 vs 0.209676`
- `0.007265 vs 0.136740`
- `0.002989 vs 0.090565`
- `0.001230 vs 0.062552`
- `0.000496 vs 0.047618`

This is now the strongest invariant in the whole project:

- valid witness ranks have vanishing energy on the forbidden width-`n-2`
  interaction directions.

That statement is sharper than `R^2`, survives null-model calibration, and has
a clean representation-theoretic meaning.

## 11. Invalid / Subthreshold Comparison

To compare against genuinely invalid objects, I used the finite `n=5,6`
residual subthreshold families from the lower-bound project. There, a full
convergence rank does not exist because the forced mover-entry graph has a bad
kernel. So I used two canonical obstruction-side scalars instead:

- kernel indicator,
- sink-peeling depth with the kernel at the top level.

These have substantially larger forbidden width-`n-2` energy than valid
`CUP-2` witnesses at the same sizes.

Examples:

- residual `n=5` cycles:
  - kernel indicator about `0.078` to `0.088`
  - peel depth about `0.072` to `0.079`
  - valid `CUP-2(n=5)` rank extension: `0.017567`

- residual `n=6` cycles:
  - kernel indicator about `0.031` to `0.040`
  - peel depth about `0.021` to `0.025`
  - valid `CUP-2(n=6)` rank extension: `0.004541`

So the suppression gap is not just “valid vs random.” It is visible against
actual subthreshold obstruction families too.

## 12. Bridge to the Existing Convergence Proof

The project’s convergence proof uses a two-level potential:

- coarse layer: `FutureFc`,
- residual layer: rank within constant-`FutureFc` slices.

Measured at width `n-2` for `n=9`:

`CUP-2`
- `fc`: forbidden fraction `0.000265`
- `FutureFc`: `0.000255`
- slice rank `cf_rank`: `0.006709`

`Sol3`
- `fc`: `0.000126`
- `FutureFc`: `0.000170`
- slice rank `cf_rank`: `0.025427`

So the explanation is:

- frontier/FutureFc kills almost all forbidden interaction mass,
- the slice rank carries the residual nonlocal correction.

This is exactly the kind of explanation I was hoping for: the
information-theoretic invariant aligns with the actual proof architecture.

## 13. The Residual Is Smaller Than It Looks

The slice-rank residual is not a diffuse hidden object.

At `n=9`, starting from the proof107-style base features

- `(FutureFc, boundary6, exp2, int21, exp2_weight)`

the remaining slice-rank entropy closes with just three more simple features.

`CUP-2(n=9)`:

- base MI `3.1171 / 4.0036`
- add `interior_sum` -> `3.8701`
- add `weight_pair_01` -> `3.9847`
- add `weight_pair_02` -> `4.0036` (exact)

`Sol3(n=9)`:

- base MI `3.2201 / 4.2287`
- add `interior_sum` -> `4.1273`
- add `weight_pair_10` -> `4.2231`
- add `weight_pair_12` -> `4.2287` (exact)

So after factoring out the frontier layer, the residual convergence code is
still a tiny weighted-pair code.

### Cross-`n` scaffold

For `CUP-2`, the fixed feature scaffold

- `interior_sum`
- `weight_pair_01`
- `weight_pair_02`
- `even_val_sum`

already determines the slice rank exactly for `n = 5..10`, and remains
extremely close at `n = 11`.

So this is not just an `n=9` curiosity; it looks like the beginning of an
actual formula basis.

### Nested correction family

The first correction terms stay inside the same weighted-pair algebra.

Adding

- `weight_pair_22`
- `weight_pair_00`

extends exactness for `CUP-2` through `n = 11`, and remains very close at
`n = 12`.

So the residual code appears to lie in a tiny nested family of weighted
adjacent-pair statistics.

### Important caveat: the decoder is small but nonlinear

This small basis is **not** affine-linear.

Least-squares fits on the exact-information bases still have substantial error,
so the decoder is not a simple linear formula in these features.

It is also not a simple lexicographic order on the residual feature tuple at
`n = 9`.

So the right formula type, if there is one, is probably:

- a small lookup code,
- a tiny decision tree,
- or a piecewise combinatorial rule on a few weighted pair counts.

## 9. Updated Interpretation

The live object is no longer “can we derive the threshold from capacity?”

It is:

- valid systems seem to admit exceptionally compressible bad-side descent codes,
- that compressibility is invisible on the good side,
- its first genuinely nontrivial manifestation is the width-`n-2`
  overlapping-window factorization gap relative to null models,
- the strongest exact version of that statement is suppression of the
  forbidden vertex-cover interaction energy,
- that suppression aligns with the proof’s two-level decomposition and
  leaves only a tiny weighted-pair residual,
- and even that residual already sits on a small cross-`n` feature scaffold.

That is the right target for future proof attempts.

### Target A: Descent-Certificate Coding

Find a representation of `rank(c)` or of a monotone surrogate as a tuple of
local certificates/messages. Then ask whether sub-threshold systems have enough
distributed memory to realize such a code.

### Target B: Cylinder-Orientation Entropy

Model each privileged table entry as orienting a whole global cylinder. The bad
graph is then a union of cylinder moves. Seek an entropy or communication bound
for acyclic orientation of this cylinder system.

### Target C: Zero-Error Bad-Side Graph

The good-cycle confusability graph is too small. Build the analogous graph on
bad configurations or bad cylinders and ask whether graph entropy / theta-style
bounds see the threshold there.

### Target D: Width-`n-2` Residual

Treat the width-`n-2` window model as the calibrated “just-below-capacity”
subspace, and study the residual of the true rank from that subspace.

This is now the best candidate for a nontrivial information-theoretic invariant:

- small for valid witness ranks,
- large for shuffled/random labels,
- plausibly large or unavoidable for invalid sub-threshold candidate systems.

### Target E: Forbidden Vertex-Cover Modes

Interpret the width-`n-2` forbidden supports dynamically.

The strongest current conjecture is:

- valid convergence suppresses the vertex-cover interaction modes of the rank,
  and invalid or sub-threshold candidates cannot suppress them enough.

### Target F: Closed-Form Slice Code

Turn the `n=9` weighted-pair closure into an actual formula.

The next plausible theorem object is:

- after removing the frontier/FutureFc layer, the residual slice rank is
  determined by a tiny weighted-pair feature tuple across `n`,
  with a small nonlinear decoder.

## Addendum: Later Decoder Results

The exploration continued substantially beyond the first draft of this memo.
The most important later results are:

### 1. Exact tiny-code theorem target for `FutureFc`

`FutureFc` turned out to be the cleanest exact-code object in the whole program.

On the solved range, after conditioning on boundary + base invariants, it admits
tiny exact decoders:

- `CUP-2`:
  - `n=5,6,7`: basis size `1`
  - `n=8`: size `2`
  - `n=9,10`: size `3`
  - `n=11`: size `5`
- `Sol3`:
  - `n=4,5,6,7`: size `1`
  - `n=8,9`: size `2`
  - `n=10`: size `3`
  - `n=11`: size `5`

Two stable family bases emerged:

`CUP-2(n=9..11)`:

- `even_val_sum`
- `weight_pair_00`
- `weight_pair_02`
- `weight_pair_11`
- `weight_pair_22`

`Sol3(n=9..11)`:

- `even_val_sum`
- `weight_pair_00`
- `weight_pair_01`
- `weight_pair_02`
- `weight_pair_22`

At `CUP-2(n=12)`, the current adjacent-pair/count bank stops being exact, but a
single nonlocal `(1,1)` pair correction repairs it:

- `count_lag2_11`

### 2. Exact decoders are shallow trees

The exact decoders are not only tiny, but shallow multiway decision trees.

For `FutureFc`:

- `CUP-2(n=9)`: max depth `3`
- `CUP-2(n=10)`: `3`
- `CUP-2(n=11)`: `3`
- `CUP-2(n=12)` on the repaired basis with `count_lag2_11`: `4`
- `Sol3(n=9)`: `2`
- `Sol3(n=10)`: `2`
- `Sol3(n=11)`: `3`

For the solved exact slice-rank branch:

- `CUP-2(n=9)`: max depth `2`
- `CUP-2(n=10)`: `3`
- `CUP-2(n=11)`: `3`
- `Sol3(n=9)`: `3`
- `Sol3(n=10)`: `3`
- `Sol3(n=11)`: `4`

So the decoder side now has a very strong endpoint:

- exact family bases,
- shallow exact trees,
- for both the coarse `FutureFc` layer and the solved slice-rank layer.

### 3. Common exact slice basis on the solved range

One especially strong unification result is that the same 5-feature basis is
exact for the slice-rank residual on both witness families through the solved
cross-family range:

- `even_val_sum`
- `weight_pair_00`
- `weight_pair_01`
- `weight_pair_02`
- `weight_pair_22`

This basis is exact for:

- `CUP-2(n=9,10,11)`
- `Sol3(n=9,10,11)`

It is also shallow as a decoder, and its root splits are dominated by

- `even_val_sum`
- `weight_pair_01`

### 4. What remains

At this point the exploration phase is effectively complete. The remaining work
is not more target discovery, but proof work on:

1. exact tiny shallow-tree theorem for `FutureFc`,
2. exact tiny shallow-tree theorem for the solved common slice basis,
3. forbidden width-`n-2` interaction suppression,
4. and the two-level `FutureFc + slice-rank` suppression theorem.

## Files

- `info_theory/exploration_log.md`
- `info_theory/theorem_targets.md`
- `info_theory/feature_algebra_notes.md`
- `info_theory/feature_subspace_theorem.md`
- `info_theory/cycle_info_metrics.py`
- `info_theory/table_cover_metrics.py`
- `info_theory/rank_info_metrics.py`
- `info_theory/entry_rank_spread.py`
- `info_theory/additive_rank_fit.py`
- `info_theory/window_rank_fit.py`
- `info_theory/window_null_model.py`
- `info_theory/window_model_dimension.py`
- `info_theory/anova_interaction_spectrum.py`
- `info_theory/forced_kernel_spectrum.py`
- `info_theory/twolevel_spectrum.py`
- `info_theory/slice_rank_boundary.py`
- `info_theory/slice_feature_search.py`
- `info_theory/slice_scaffold_eval.py`
- `info_theory/slice_linear_fit.py`
- `info_theory/futurefc_subset_search.py`
- `info_theory/futurefc_compressed_subset_search.py`
- `info_theory/futurefc_collision_report.py`
- `info_theory/futurefc_nonlocal_pair_probe.py`
- `info_theory/futurefc_decision_tree_probe.py`
- `info_theory/futurefc_tree_extract.py`
- `info_theory/futurefc_basis_family_probe.py`
- `info_theory/slice_subset_search.py`
- `info_theory/slice_compressed_subset_search.py`
- `info_theory/slice_collision_report.py`
- `info_theory/slice_decision_tree_probe.py`
- `info_theory/slice_triple_correction_probe.py`
