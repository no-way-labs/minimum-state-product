# Exploration Log

## Strategy Register

### Eliminated approach classes

- Exploration 1: Any lower-bound strategy that relies only on good-cycle local-context counts, local-context entropy, or the amount of per-processor information needed to decode the mover bit is too weak. In valid witnesses the mover bit is zero-error decodable from only `0.40` to `0.54` bits per processor on the cycle, and the distinct local support stays tiny (`7..15`) even when the state product is far above the cycle length.
- Exploration 2: Any strategy that relies only on privileged-cylinder cover counts or on the coarse quantity `Σ_i |P_i| / L_i` is too weak. Valid witnesses already have cover lower bounds around `4.4` to `4.6`, so liveness-cover counting is far from the threshold.
- Exploration 69: The reduced-prefix exact `FutureFc` code is not explained by affine-linear formulas on the reduced prefix plus the tiny basis. Any proof of the reduced-prefix theorem must therefore be combinatorial or tree-like, not linear.
- Exploration 76: Witness-side decoder polishing does not advance the lower bound unless it is explicitly turned into a universal valid-system condition or a forbidden subthreshold condition.

### Obstructions

- Exploration 1: On `CUP-2`, the good cycle uses only `7,8,9` distinct local contexts per processor class, independent of `n` for `n=5..12`. The threshold cannot come from exhausting local good-cycle context capacity.
- Exploration 1: Shearer/support-style bounds on the good cycle collapse to very loose inequalities. For `CUP-2(n=9)`, `CL = 25` while the support bound gives `CL <= 569.98`.
- Exploration 2: The good cycle is a small, specially structured subset of the single-privileged set. For `CUP-2(n=9)`, there are `79` single-privileged configs but only `61` good ones. Good-cycle coding alone misses the bad-side constraints.
- Exploration 69: Even when `exp2` or `int21` are exact functions of the reduced coarse prefix, least-squares fits still have substantial residuals. So the reduced-prefix collapse is exact-but-nonlinear.

### Building Blocks

- Exploration 1: Exact zero-error reformulation: entry-conflict freedom at processor `i` is equivalent to zero-error decodability of `R_i(k) = 1[moverAt(k)=i]` from the local context `C_i(k)` restricted to the good cycle.
- Exploration 1: Reusable script `cycle_info_metrics.py` computes per-processor local support sizes, mover/non-mover support sizes, entropies, and Shearer-style bounds for valid witnesses.
- Exploration 2: Reusable script `table_cover_metrics.py` computes privileged-cylinder cover statistics, privileged multiplicity distributions, and the gap between the single-privileged set and the actual good set.
- Exploration 67: Every coordinate used in the exact `FutureFc` family bases, including the first `CUP-2(n=12)` lagged `(1,1)` repairs, is still a width-`n-2` allowed coordinate. The remaining gap is therefore collision-freeness of the tiny code, not admissibility of the coordinates.
- Exploration 67: Any exact finite code on `k` scalar coordinates admits an exact multiway axis-aligned decision tree of depth at most `k`.
- Exploration 68: On the coarse `FutureFc` layer, the full proof107 TP prefix is not minimal on the solved range. The exact code collapses to a reduced prefix:
  - `Sol3`: `boundary6 + exp2_weight`,
  - `CUP-2`: `boundary6 + exp2_weight + int21`,
  together with the tiny family basis.
- Exploration 69: On the solved reduced-prefix fibers, the omitted TP scalars are themselves recoverable:
  - `Sol3`: `exp2` and `int21` are functions of `boundary6 + exp2_weight + B_sol`,
  - `CUP-2`: `exp2` is a function of `boundary6 + exp2_weight + int21 + B_cup`,
    including repaired `n=12`.
- Exploration 70: The reduced-prefix recovery maps are shallow exact trees:
  - `CUP-2(n=11)` recovers `exp2` at depth `1`,
  - `Sol3(n=11)` recovers `int21` at depth `3`,
  - `Sol3(n=11)` recovers `FutureFc-fc` at depth `4`,
  - `CUP-2(n=12)` recovers the repaired gap at depth `3`.
- Exploration 71: The shallow reduced-prefix recovery tree pattern persists across the whole solved range:
  - `CUP-2` gap depths are `2,3,3,3` on `n=9,10,11,12`,
  - `CUP-2` `exp2` depths are `0,1,1` on `n=9,10,11`,
  - `Sol3` `int21` depths are `2,3,3` on `n=9,10,11`,
  - `Sol3` gap depths are `3,3,4` on `n=9,10,11`.
- Exploration 72: The reduced-prefix recovery-tree roots are highly concentrated rather than chaotic:
  - `even_val_sum` dominates `CUP-2` `exp2` recovery,
  - `even_val_sum` dominates `Sol3` `int21` recovery,
  - reduced-prefix gap recovery is led by `even_val_sum` and a small pair-weight set.
- Exploration 73: `CUP-2` reduced-prefix recovery of `exp2` is almost entirely an `even_val_sum` theorem:
  among the `430` nontrivial reduced-prefix groups at `n=11`,
  `358` are resolved by `even_val_sum` alone, with only `10` normalized
  `even_val_sum -> exp2` patterns overall.
- Exploration 73: Total interior `2`-mass `count_val_2` is also exact on the reduced prefixes, but its recovery trees are not simpler than the current `exp2` / `int21` targets. So proving `count_val_2` first does not currently look like the cleanest route.
- Exploration 74: `CUP-2` reduced-prefix recovery of `exp2` has a near-explicit two-stage rule on the solved local range:
  - `n=10`: `even_val_sum` alone is exact,
  - `n=11`: after `even_val_sum`, every exceptional group is resolved by either
    `weight_pair_02` or `weight_pair_22` (in fact both work on the `72`
    exceptional groups).
- Exploration 74: The same near-explicit two-stage simplification does **not**
  currently extend to `Sol3` `int21` recovery or to repaired `CUP-2(n=12)`:
  those branches retain substantial families not resolved by a single
  post-`even_val_sum` secondary coordinate.
- Exploration 74: Outgoing-pair identity:
  `count_val_2 = count_pair_20 + count_pair_21 + count_pair_22 = exp2 + count_pair_22`.
  So recovering `exp2` is equivalent to recovering the interior `2`-mass once
  `count_pair_22` is controlled.
- Exploration 75: The local `CUP-2` branch compactifies further:
  on the reduced prefix `boundary6 + exp2_weight + int21`, the 3-feature basis
  `even_val_sum, weight_pair_11, weight_pair_22` already determines `exp2`
  exactly for `n=9,10,11,12`, with max tree depths `0,1,1,2`.
- Exploration 76: Lower-bound admission rule:
  information-theory work stays on the critical path only if it targets
  1. a necessary condition on all valid systems,
  2. a forbidden condition on subthreshold systems,
  3. or a bridge theorem converting witness structure into one of those.

### Known reformulations

- Exploration 1: Zero-error distributed classifier view. Step index `K` is the hidden source, local context `C_i(K)` is the local observation, and mover bit `R_i(K)` must be zero-error decodable from `C_i(K)`. LOAD-BEARING: high. This cleanly isolates what entry conflict actually means in information-theoretic language.
- Exploration 2: Privileged-cylinder cover view. Each privileged local context is a cylinder in global configuration space; liveness is a cover condition and convergence is an acyclic-orientation/ranking condition on the covered bad region. LOAD-BEARING: high. This shifts the focus from the good cycle to the full transition table.
- Exploration 67: Exact frontier-code package. `FutureFc` is treated as an exact prefix code on a tiny tuple of width-`n-2` coordinates, together with a shallow tree decoder. LOAD-BEARING: high. This is now the default theorem-facing formulation for the first step of the two-level `FutureFc + slice-rank` program.
- Exploration 68: Reduced-prefix frontier code. The coarse layer is best viewed as a code on
  `boundary6 + exp2_weight` (Sol3) or `boundary6 + exp2_weight + int21`
  (CUP-2), plus the tiny weighted-pair basis. LOAD-BEARING: high. This is the
  sharpest current statement of what part of the proof107 prefix actually
  survives in the exact `FutureFc` code.
- Exploration 69: Nonlinear reduced-prefix code. The surviving coarse prefix is
  genuinely the right coordinate system, but the induced recovery of dropped TP
  scalars is not affine-linear. LOAD-BEARING: medium-high. This narrows the
  next proof form to piecewise / tree-like recovery rather than linear algebra.
- Exploration 70: Reduced-prefix recovery tree. The omitted TP scalars and the
  coarse gap already admit shallow exact tree decoders on the reduced prefixes.
  LOAD-BEARING: high. This is the first positive theorem-shaped replacement for
  the failed affine explanation.
- Exploration 71: Uniform solved-range recovery-tree law. The reduced-prefix
  recovery trees remain uniformly shallow across the solved range, so this is no
  longer an isolated sample phenomenon. LOAD-BEARING: high. This is now a
  genuine theorem candidate, not just an example bank.
- Exploration 72: Dominant-root reduced-prefix trees. The reduced-prefix
  recovery trees are organized around the same few features, especially
  `even_val_sum`. LOAD-BEARING: medium-high. This gives the first concrete hint
  for how an analytic branching proof might start.
- Exploration 73: Even-sum pattern law. On `CUP-2`, the reduced-prefix
  `exp2` recovery collapses to a tiny menu of `even_val_sum` patterns; the
  remaining exceptions are sparse. LOAD-BEARING: medium-high. This is the first
  sign of a near-explicit case theorem rather than just a depth bound.
- Exploration 74: Two-stage `CUP-2` recovery rule. On the solved local `CUP-2`
  branch, `exp2` is recovered by a two-stage tree:
  `even_val_sum` first, then one pair-weight on a small exceptional family.
  LOAD-BEARING: high. This is the strongest current symbolic foothold on the
  reduced-prefix branch.
- Exploration 75: Compact local `CUP-2` theorem. The solved and first repaired
  local `CUP-2` branch is exactly encoded by a uniform 3-feature weighted-pair
  basis on the reduced prefix. LOAD-BEARING: very high. This is the first
  genuinely compact corrected theorem on the reduced-prefix branch.
- Exploration 76: Lower-bound triage lens. Classify every info-theory result as
  `keep`, `conditional`, or `shelve` according to whether it can become a
  necessary valid-system condition or a forbidden subthreshold condition.
  LOAD-BEARING: very high. This is now the default decision rule for the
  branch.

## Exploration 1

### Strategy

Recast a valid good cycle as a zero-error coding object and measure the actual local information quantities on known valid witnesses, to test whether the threshold could plausibly come from good-cycle information alone.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out any proof strategy whose decisive inequality uses only:

- the number of distinct local contexts used on the good cycle,
- local-context entropy on the good cycle,
- or the amount of information each processor needs to recover “am I the mover?”

Those quantities are all much too small on valid witnesses.

### Surviving Structure

- Entry-conflict freedom is exactly a zero-error separability condition: mover and non-mover occurrences at a processor must live in disjoint local-context supports.
- On valid cycles, `R_i` is a deterministic function of `C_i`, so `I(C_i; R_i) = H(R_i)`.
- For `CUP-2(n=9)`, `H(R_i)` is only `0.402` bits at binary endpoints and `0.529` bits at ternary processors.
- For `CUP-2(n=9)`, local support sizes are only `7, 8, 9` against raw capacities `12, 18, 27`.
- For `Sol3(n=9)`, local support sizes are `12` or `15` against capacity `27`.
- For `CUP-2(n=5..12)`, the set of local support sizes is exactly `[7, 8, 9]` for every tested `n`.

### Reformulations

- Zero-error distributed classifier view:
  `K` = step index on the cycle,
  `C_i(K)` = local context at processor `i`,
  `R_i(K)` = mover bit for processor `i`.
  The cycle is entry-conflict-free iff `R_i` is zero-error decodable from `C_i`.

LOAD-BEARING ASSESSMENT: yes. This is the cleanest information-theoretic formulation found so far for the good-cycle side of the problem. It makes explicit that the relevant object is support disjointness, not Shannon capacity.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`: `product = 8748`, `cycle_len = 25`.
  Per-processor local support / mover support / non-mover support:
  - `P0`: `7 / 2 / 5`
  - `P1`: `8 / 3 / 5`
  - `P2..P6`: `9 / 3 / 6` except the center positions have slightly different empirical frequencies
  - `P7`: `8 / 3 / 5`
  - `P8`: `7 / 2 / 5`
- `Sol3(n=9)`: `product = 19683`, `cycle_len = 48`.
  Per-processor local support / mover support / non-mover support:
  - endpoints `P0,P8`: `12 / 3 / 9`
  - interior `P1..P7`: `15 / 6 / 9`
- `CUP-2(n=5..12)` summary:
  - cycle lengths: `13,16,19,22,25,28,31,34`
  - distinct local support classes: always `[7,8,9]`
  - average local support: `7.8, 8.0, 8.143, 8.25, 8.333, 8.4, 8.455, 8.5`
  - average local-context entropy: `2.734, 2.635, 2.543, 2.462, 2.391, 2.328, 2.274, 2.225`

STRUCTURAL RESULTS:

- For any good cycle with distinct configurations, Shearer’s inequality on local contexts gives
  `log CL <= (1/3) Σ_i log |supp(C_i)|`,
  hence
  `CL <= (Π_i |supp(C_i)|)^(1/3) <= P`.
- On `CUP-2(n=9)`, the Shearer support bound gives `CL <= 569.9843`, while the actual cycle length is `25`.
- On `Sol3(n=9)`, the same bound gives `CL <= 2908.4868`, while the actual cycle length is `48`.

TOOLS:

- `info_theory/cycle_info_metrics.py`
  Inputs: witness family (`cup2`, `sol3`) and `n`.
  Outputs: per-processor capacities, support sizes, mover/non-mover support sizes, entropies, and Shearer-style support bounds.

REPRESENTATIONS:

- “Good cycle as source coding” representation: step index as source, local contexts as distributed observations, mover bits as zero-error messages.

### What Would Unblock This

To go beyond this obstruction, we need an information-theoretic object that uses the full transition table, not just the good-cycle support. The smallest useful next artifact is a representation of the bad-config transition graph in local-cylinder coordinates.

### Key Parameters

- Families tested: `CUP-2(n=5..12)`, `Sol3(n=9)`.
- Worked uniformly: zero-error mover-bit decoding formulation.
- Failed uniformly: support-count and entropy quantities are far too small to explain the threshold.

### Open Questions

- Can the bad-config convergence requirement be expressed as a zero-error coding or graph-entropy condition on privileged cylinders?
- Is there a support-sensitive quantity on the bad side analogous to entry-conflict-free support disjointness on the good side?

## Exploration 2

### Strategy

Shift from the good cycle to the full transition table and study privileged local contexts as cylinders covering the global configuration space, to see whether liveness or coarse cover multiplicity could explain the threshold.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out any threshold proof based only on coarse privileged-cover counting:

- `Σ_i |P_i| / L_i`,
- the distribution of privileged multiplicity `|Priv(c)|`,
- or the raw size of the single-privileged set.

All of these are already large and loose on valid witnesses.

### Surviving Structure

- Liveness is exactly a cylinder-cover condition:
  if `P_i` is the privileged local-context set at processor `i`, then the union of the corresponding cylinders must cover the full configuration space.
- This immediately gives the necessary inequality
  `Σ_i |P_i| / L_i >= 1`.
- The actual valid witnesses sit far above this floor:
  - `CUP-2(n=9)`: `4.592593`
  - `Sol3(n=9)`: `4.444444`
- On `CUP-2(n=5..12)`, the cover lower bound grows roughly linearly:
  `2.519, 3.037, 3.556, 4.074, 4.593, 5.111, 5.630, 6.148`.
- The good set is only a subset of the single-privileged set:
  `CUP-2(n=9)` has `79` single-privileged configs but only `61` good ones, leaving `18` bad single-privileged states.

### Reformulations

- Privileged-cylinder cover view:
  Each privileged table entry is a radius-1 cylinder in global configuration space.
  Liveness is a cover statement.
  Convergence is not a cover statement; it is an acyclic-orientation/ranking statement on the bad part of the covered space.

LOAD-BEARING ASSESSMENT: yes. This separates the easy information-theoretic part (cover) from the hard part (orientation/ranking), which the earlier capacity scripts were conflating.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)` privileged counts by processor:
  - `P0`: `|P_0| = 5` out of `L_0 = 12`
  - `P1`: `10 / 18`
  - `P2..P6`: `14 / 27`
  - `P7`: `11 / 18`
  - `P8`: `5 / 12`
- `CUP-2(n=9)` privileged multiplicity distribution over all `8748` configs:
  - `1 -> 79`
  - `2 -> 538`
  - `3 -> 1559`
  - `4 -> 2024`
  - `5 -> 2200`
  - `6 -> 1438`
  - `7 -> 690`
  - `8 -> 190`
  - `9 -> 30`
- `Sol3(n=9)` privileged multiplicity distribution over all `19683` configs:
  - `1 -> 96`
  - `2 -> 756`
  - `3 -> 2952`
  - `4 -> 6240`
  - `5 -> 6312`
  - `6 -> 2808`
  - `7 -> 504`
  - `8 -> 15`

STRUCTURAL RESULTS:

- Necessary cover inequality:
  if every configuration has at least one privileged processor, then
  `Σ_i |P_i| / L_i >= 1`.
- This inequality is extremely loose on valid witnesses; the real threshold, if information-theoretic, must live in additional structure beyond covering.
- The presence of bad single-privileged states shows that “one privileged processor” is not the same object as “good-cycle state.” Any information-theoretic model focused only on one-hot privilege patterns is incomplete.

TOOLS:

- `info_theory/table_cover_metrics.py`
  Inputs: witness family (`cup2`, `sol3`) and `n`.
  Outputs: privileged entry counts, cover lower bound, privileged multiplicity distribution, and single-privileged vs good-set counts.

REPRESENTATIONS:

- “Privileged-cylinder cover” representation: global configurations are covered by local privileged cylinders; the missing ingredient is how these cylinders are oriented on bad states to avoid cycles.

### What Would Unblock This

We need a table-level representation of convergence that is still local enough to look information-theoretic. The smallest useful next artifact would be a cylinder-coordinate description of the bad-config DAG or a ranking function expressed as local certificates.

### Key Parameters

- Families tested: `CUP-2(n=5..12)` for cover growth, `CUP-2(n=9)` and `Sol3(n=9)` for detailed multiplicity distributions.
- Worked: cover-based liveness formulation.
- Failed: coarse cover quantities remain far from any plausible threshold-tight inequality.

### Open Questions

- Can convergence be recast as a distributed ranking code?
- Is there a graph entropy / theta-type bound on the bad-config orientation problem, rather than on the good-cycle support problem?

## Synthesis after exploration 2

- The two useful information-theoretic reformulations sit on opposite sides of the theorem:
  - good side: zero-error local decoding of mover bits from cycle contexts,
  - bad side: privileged-cylinder cover plus an unknown acyclic-orientation constraint.
- Both coarse count families are now ruled out:
  - good-cycle support/entropy counts,
  - table-level cover counts.
- The residue points at one narrow target: an information-theoretic formulation of convergence, not of good-cycle existence or liveness.

## Exploration 3

### Strategy

Treat convergence as a distributed ranking problem: compute the exact bad-config DAG rank on valid witnesses and measure how much information about that global rank is visible from local contexts or other coarse observables.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out any convergence proof that expects the bad-side rank to be recoverable from a single processor’s local context or from a coarse observable such as privileged multiplicity. The rank is globally distributed.

### Surviving Structure

- The bad-config DAG gives a canonical global random variable `rank(c)`.
- On valid witnesses, `rank` has substantial entropy:
  - `CUP-2(n=9)`: `H(rank) = 5.2733` bits, `max_rank = 52`
  - `Sol3(n=9)`: `H(rank) = 6.3383` bits, `max_rank = 108`
- But one processor’s local context carries very little information about that rank:
  - `CUP-2(n=9)`: per-processor `I(C_i; rank)` lies between `0.1486` and `0.4013` bits
  - `Sol3(n=9)`: per-processor `I(C_i; rank)` lies between `0.2178` and `0.3235` bits
- Even the full privileged set is only partially informative:
  - `CUP-2(n=9)`: `I(Priv(c); rank) = 1.7838` bits
  - `Sol3(n=9)`: `I(Priv(c); rank) = 2.7233` bits
- Privileged multiplicity alone is weaker still:
  - `CUP-2(n=9)`: `I(|Priv(c)|; rank) = 0.3763` bits
  - `Sol3(n=9)`: `0.6897` bits

### Reformulations

- Distributed ranking code view:
  convergence is equivalent to the existence of a global rank `rank(c)` on bad configurations with strict descent along every bad edge.
  The local tables do not reveal this rank directly; instead they distribute small fragments of information about it across the ring.

LOAD-BEARING ASSESSMENT: yes. This is the first information-theoretic object that appears genuinely tied to convergence rather than to liveness or cycle existence. It suggests the threshold, if accessible by info theory, should come from a distributed encoding lower bound for descent certificates.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`:
  - `bad_configs = 8687`
  - rank entropy `H(rank) = 5.2733`
  - maximum rank `52`
  - `I(C_i; rank)` by processor:
    - `P0: 0.1486`
    - `P1: 0.2519`
    - `P2: 0.3604`
    - `P3: 0.4013`
    - `P4: 0.3714`
    - `P5: 0.3863`
    - `P6: 0.3800`
    - `P7: 0.3191`
    - `P8: 0.2061`
- `Sol3(n=9)`:
  - `bad_configs = 19587`
  - rank entropy `H(rank) = 6.3383`
  - maximum rank `108`
  - `I(C_i; rank)` by processor lies in `[0.2178, 0.3235]`

STRUCTURAL RESULTS:

- The bad-side rank is a global quantity whose entropy is much larger than the information carried by any single local context.
- Convergence therefore looks like a distributed descent-certificate problem, not a one-site zero-error decoding problem.

TOOLS:

- `info_theory/rank_info_metrics.py`
  Inputs: witness family (`cup2`, `sol3`) and `n`.
  Outputs: bad-config rank distribution, per-processor mutual information `I(C_i; rank)`, and information carried by privileged multiplicity / privileged-set identity.

REPRESENTATIONS:

- “Distributed ranking code” representation: the bad-config DAG rank is the hidden source, local contexts are partial observations, and the transition tables collectively implement a distributed descent protocol.

### What Would Unblock This

The next useful artifact would be a representation of rank in terms of local certificates or factorized messages, even if approximate. The smallest useful computation is to test whether rank can be compressed into a low-dimensional tuple of local cylinder features on `CUP-2(n=9)`.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.
- Worked: exact DAG rank extraction and mutual-information measurements.
- Failed: any hope that one local context or privileged-count observable almost determines rank.

### Open Questions

- Is there a lower bound on the distributed information needed to encode a descent certificate for all bad configurations?
- Can one define a graph entropy / communication complexity object for local cylinder orientations that provably exceeds what sub-threshold systems can realize?

## Synthesis after exploration 3

- Exploration 1 killed good-cycle support/entropy proofs.
- Exploration 2 killed coarse cover-count proofs.
- Exploration 3 identifies the first quantity that looks genuinely nontrivial: the bad-side rank is global and only weakly visible locally.
- The remaining information-theoretic path is now much sharper:
  prove that sub-threshold state products cannot realize a distributed descent code for the bad-config DAG.

## Exploration 4

### Strategy

Refine the distributed-ranking view from processor-level observations to the actual control granularity of the system: a single privileged table entry `(proc, local context)`. Measure how much bad-side rank variation one such entry must handle across all bad edges using that label.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out any convergence proof that expects a privileged table entry to encode only a narrow band of global descent states. In valid witnesses, one local label still has to act correctly across almost the full bad-side rank entropy.

### Surviving Structure

- The right local object is not merely processor `i`, but the edge label
  `e = (i, C_i(c))` on a bad transition.
- Conditioning on one such label does **not** collapse the global rank:
  - `CUP-2(n=9)`: average `H(rank | e) = 4.9346` bits versus total `H(rank) = 5.2733`
  - `Sol3(n=9)`: average `6.0244` bits versus total `6.3383`
- In `CUP-2(n=9)`, the average label sees `41.4` distinct source ranks; the maximum is `53`, essentially the whole rank range.
- In `Sol3(n=9)`, the average label sees `87.35` distinct source ranks; the maximum is `101`.
- Constant rank drop by label is rare:
  - `CUP-2(n=9)`: `15 / 101` labels
  - `Sol3(n=9)`: `6 / 120` labels
- Therefore a single local action is not implementing a fixed-step local descent rule. It is a robust action that succeeds across a very wide hidden range of global positions in the bad DAG.

### Reformulations

- Local-entry ambiguity view:
  for each privileged label `e`, the bad graph restricts to a large fiber of hidden states all sharing the same local observation. Convergence requires one fixed local move to descend the global rank on the entire fiber.

LOAD-BEARING ASSESSMENT: yes. This is more precise than the processor-level mutual-information view and captures the actual granularity at which the distributed code operates.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`:
  - bad labels: `101`
  - average bad edges per label: `397.18`
  - average distinct source ranks per label: `41.41`
  - average distinct successor ranks per label: `41.90`
  - average `H(source rank | label) = 4.9346`
  - maximum source-rank support on one label: `53`
  - widest drop range on one label: `(1, 42)` at label `(4, (1,2,1))`
  - top spread label `(0, (1,1,2))`: `728` edges, `53` source ranks, `Hsrc = 5.2450`
- `Sol3(n=9)`:
  - bad labels: `120`
  - average bad edges per label: `728.2`
  - average distinct source ranks per label: `87.35`
  - average `H(source rank | label) = 6.0244`
  - maximum source-rank support on one label: `101`
  - widest drop range on one label: `(1, 69)` at label `(3, (0,1,2))`

STRUCTURAL RESULTS:

- Entry-level conditioning removes very little of the global rank uncertainty.
- The distributed descent code is therefore highly ambiguous at exactly the place where the transition table acts.

TOOLS:

- `info_theory/entry_rank_spread.py`
  Inputs: witness family (`cup2`, `sol3`) and `n`.
  Outputs: entry-level rank-support sizes, conditional entropies, and rank-drop ranges.

REPRESENTATIONS:

- “Entry fiber” representation: all bad states using one local table entry form a large hidden fiber; convergence requires a single action to orient that entire fiber downward.

### What Would Unblock This

The next useful step is to test whether the global rank nevertheless admits a low-complexity **factorization** across processors, even though no single entry sees much of it. The smallest useful computation is an additive local-model fit:

`rank(c) ≈ const + Σ_i w_i(C_i(c))`

on bad configurations.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.
- Worked: entry-level ambiguity measurement.
- Failed: the hope that label-level conditioning nearly determines the bad-side rank.

### Open Questions

- Is the rank approximately additive in local context features?
- Is there a lower bound on how many bits of distributed latent state are needed so that every entry fiber can be globally oriented?

## Synthesis after exploration 4

- Processor-level information about rank is tiny (exploration 3).
- Entry-level information about rank is still tiny relative to the total rank entropy (exploration 4).
- So the convergence code is both local-action based and globally ambiguous.
- The natural next test is whether this ambiguity is resolved by an additive distributed encoding across processors.

## Exploration 5

### Strategy

Test whether the global bad-side rank is representable as a distributed additive code over local contexts by fitting

`rank(c) ≈ bias + Σ_i w_i(C_i(c))`

on bad configurations.

### Outcome

SUCCEEDED

### Failure Constraint

The additive radius-1 model is not exact. Even on the best case tested (`CUP-2(n=9)`), maximum error remains about `20.6`, so a pure sum of one-site local-context codewords does not fully encode the bad-side rank.

### What This Rules Out

It rules out the strongest simple constructive guess:

- “convergence rank is exactly a sum of one-site local messages.”

Any exact information-theoretic representation must either:

- use richer local factors than one processor’s radius-1 context,
- or encode something simpler than the exact canonical rank.

### Surviving Structure

- The additive model is still surprisingly strong:
  - `CUP-2(n=9)`: `R^2 = 0.878724`, `RMSE = 3.361`, `MAE = 2.575`
  - `Sol3(n=9)`: `R^2 = 0.772313`, `RMSE = 10.023`, `MAE = 7.987`
- So the bad-side rank is highly compressible into a distributed local code, just not exactly at one-site/radius-1 resolution.
- This suggests the right information object may be a low-order factor graph or window code rather than an arbitrary global function.

### Reformulations

- Additive distributed-code view:
  the global rank is approximated by a sum of local codewords attached to radius-1 contexts.

LOAD-BEARING ASSESSMENT: medium-high. This is not yet an exact representation, but it is the first constructive compression of the bad-side rank and suggests a tractable hierarchy of local factor models.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)` additive fit:
  - bad configs: `8687`
  - features: `196`
  - `R^2 = 0.878724`
  - `RMSE = 3.361054`
  - `MAE = 2.575470`
  - `max_abs_error = 20.628014`
  - exact after rounding: `1087 / 8687`
- `Sol3(n=9)` additive fit:
  - bad configs: `19587`
  - features: `244`
  - `R^2 = 0.772313`
  - `RMSE = 10.023296`
  - `MAE = 7.986586`
  - `max_abs_error = 38.121718`
  - exact after rounding: `789 / 19587`

STRUCTURAL RESULTS:

- One-site additive local coding captures most, but not all, of the global rank variance.
- Therefore the convergence code has strong low-order structure even though the exact canonical rank is not one-site additive.

TOOLS:

- `info_theory/additive_rank_fit.py`
  Inputs: witness family (`cup2`, `sol3`) and `n`.
  Outputs: least-squares additive fit of bad-side rank from local contexts, with `R^2`, errors, and top fitted local coefficients.

REPRESENTATIONS:

- “One-site additive rank code” representation: a first approximation to the global descent certificate as a sum of local context codewords.

### What Would Unblock This

The next useful computation is to extend the factor size from one-site/radius-1 to a slightly richer local window, for example:

`rank(c) ≈ const + Σ_i g_i(c[i-1], c[i], c[i+1], c[i+2])`

If that sharply improves exactness, then the right information-theoretic representation may be a low-order overlapping-window code.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.
- Worked: additive compression of rank.
- Failed: exact one-site additive representation.

### Open Questions

- Does a width-4 or width-5 overlapping-window factorization nearly or exactly capture rank?
- Is there a lower-bound theorem for the memory required by such a distributed factor code?

## Synthesis after exploration 5

- The live picture is now more precise:
  - rank is globally distributed and locally ambiguous (explorations 3 and 4),
  - but it is still strongly compressible into low-order local structure (exploration 5).
- That makes low-order factor models the natural next rung in the information-theoretic hierarchy.

## Exploration 6

### Strategy

Increase the expressive power of the distributed factor model from one-site local contexts to overlapping contiguous state windows of width `4` and `5`, and fit

`rank(c) ≈ const + Σ_i g_i(c[i], ..., c[i+w-1])`.

### Outcome

SUCCEEDED

### Failure Constraint

The width-4 and width-5 window models are still not exact, so the canonical bad-side rank is not captured perfectly even by these richer low-order overlapping windows.

### What This Rules Out

It rules out the claim that the exact canonical rank is a trivial short-window additive code. Even width `5` still has noticeable error.

### Surviving Structure

- The improvement with window width is strong and monotone:
  - `CUP-2(n=9)`:
    - width `3` / radius-1 context model (exploration 5): `R^2 = 0.8787`
    - width `4`: `R^2 = 0.9344`
    - width `5`: `R^2 = 0.9662`
  - `Sol3(n=9)`:
    - width `3`: `0.7723`
    - width `4`: `0.8698`
    - width `5`: `0.9327`
- Errors also fall substantially:
  - `CUP-2`: RMSE `3.36 -> 2.47 -> 1.78`
  - `Sol3`: RMSE `10.02 -> 7.58 -> 5.45`
- This is strong evidence that the bad-side descent code has a genuine low-order overlapping-window structure.

### Reformulations

- Overlapping-window code view:
  the global rank is approximated by an additive factor graph whose factors are short cyclic windows of the configuration, not just single local contexts.

LOAD-BEARING ASSESSMENT: high. This is the first constructive hierarchy with clear improvement as expressive power grows. It suggests that the real convergence code may live in bounded-width local windows.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`, width `4`:
  - features: `541`
  - `R^2 = 0.934421`
  - `RMSE = 2.471564`
  - `MAE = 1.845714`
  - `max_abs_error = 17.359340`
  - exact after rounding: `1626 / 8687`
- `CUP-2(n=9)`, width `5`:
  - features: `1486`
  - `R^2 = 0.966172`
  - `RMSE = 1.775109`
  - `MAE = 1.312464`
  - `max_abs_error = 13.735096`
  - exact after rounding: `2275 / 8687`
- `Sol3(n=9)`, width `4`:
  - features: `730`
  - `R^2 = 0.869849`
  - `RMSE = 7.578168`
- `Sol3(n=9)`, width `5`:
  - features: `2188`
  - `R^2 = 0.932692`
  - `RMSE = 5.449744`

STRUCTURAL RESULTS:

- The bad-side rank is much closer to a bounded-width factor code than to a one-site additive code.
- The width hierarchy is a meaningful structural ladder, not random overfitting noise: both witness families improve in the same direction.

TOOLS:

- `info_theory/window_rank_fit.py`
  Inputs: witness family, `n`, and window width.
  Outputs: least-squares additive fit of bad-side rank using overlapping contiguous windows.

REPRESENTATIONS:

- “Window-factor descent code” representation: the global rank is encoded by overlapping local windows around the ring.

### What Would Unblock This

The next useful computation is to continue the width ladder far enough to see whether there is a sharp saturation point. The smallest useful follow-up is width `6` and perhaps width `7` at `n=9`.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.
- Widths tested: `4`, `5` (with width `3` inherited from exploration 5).
- Worked: constructive low-order window hierarchy.
- Failed: exact representation at width `5`.

### Open Questions

- Is there a small width at which the rank becomes nearly exact or exactly integer-recoverable?
- Does the required window width scale with `n`, or stabilize?
- Can one prove that sub-threshold systems would require larger width than their local state product permits?

## Synthesis after exploration 6

- The surviving information-theoretic picture is now:
  - coarse counts do not see the threshold,
  - convergence is a distributed global code,
  - but that code has strong low-order window structure.
- This shifts the live research target again:
  not “is there an info-theoretic object?” but “can bounded-width distributed factor codes be lower-bounded in terms of state product?”

## Exploration 7

### Strategy

Push the window hierarchy beyond width `5` on `CUP-2(n=9)` to detect a saturation point, starting with width `6` and then width `7`.

### Outcome

STALLED

### Failure Constraint

The existing `window_rank_fit.py` implementation used a dense least-squares matrix. Width `6` remained feasible, but width `7` hit a computational wall: the dense solve did not complete in reasonable time and had to be killed. This is a representation/solver bottleneck, not a conceptual failure of the window-factor approach.

### What This Rules Out

It rules out continuing the width ladder with the current dense implementation. Any further exploration of larger windows requires a sparse or iterative least-squares solver.

### Surviving Structure

- Width `6` on `CUP-2(n=9)` is still feasible and significantly improves the fit:
  - features: `4051`
  - `R^2 = 0.988425`
  - `RMSE = 1.038344`
  - `MAE = 0.728841`
  - `max_abs_error = 9.163540`
  - exact after rounding: `4216 / 8687`
- This continues the same monotone trend from explorations 5 and 6 and strongly suggests a genuine bounded-width saturation phenomenon.

### Reformulations

- Computational stall classification: this is a **computational** stall, not a conceptual one. The needed object is clear; the current solver is the wrong tool.

LOAD-BEARING ASSESSMENT: medium. The stall itself is not mathematically deep, but the width-6 result is important because it shows the window hierarchy is still improving sharply.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`, width `6`:
  - `R^2 = 0.988425`
  - `RMSE = 1.038344`
  - `MAE = 0.728841`
  - `max_abs_error = 9.163540`
  - rounded exactness `4216 / 8687`
- Width `7` dense run:
  - process launched successfully
  - did not finish in reasonable time
  - process manually killed

STRUCTURAL RESULTS:

- The low-order window code remains the strongest constructive information-theoretic representation found so far.

TOOLS:

- Dense `window_rank_fit.py` is adequate up to width `6` on `CUP-2(n=9)`, but not beyond.
- `scipy.sparse` is available locally and is the natural next solver backend.

REPRESENTATIONS:

- No new mathematical representation; this exploration mainly identified the computational bottleneck in the existing one.

### What Would Unblock This

A sparse or iterative least-squares implementation for the window model. The smallest useful upgrade is to rebuild `window_rank_fit.py` using CSR matrices and `scipy.sparse.linalg.lsqr` or `lsmr`.

### Key Parameters

- Family tested: `CUP-2(n=9)`.
- Widths tested: `6` succeeded, `7` stalled under dense solve.

### Open Questions

- Does width `7` or `8` nearly recover the exact rank on `CUP-2(n=9)`?
- Can the same sparse method push `Sol3(n=9)` beyond width `5`?

## Exploration 8

### Strategy

Upgrade the window hierarchy to a sparse least-squares solve and continue the width ladder beyond the dense computational barrier, especially near width `n-1`.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the pessimistic interpretation that the width hierarchy was merely a soft regression artifact with no sharp structural payoff. The sparse continuation reveals a strong saturation phenomenon.

### Surviving Structure

- Sparse solving reopens the entire window hierarchy.
- `CUP-2(n=9)` continues improving sharply:
  - width `7`: `R^2 = 0.997882`, `RMSE = 0.444`, rounded exact `7064 / 8687`
  - width `8`: `R^2 = 0.999982`, `RMSE = 0.0405`, rounded exact `8687 / 8687`
- `Sol3(n=9)` shows the same phenomenon:
  - width `6`: `R^2 = 0.973858`
  - width `7`: `0.995373`
  - width `8`: `0.999965`, rounded exact `19581 / 19587`
- This is the strongest constructive information-theoretic structure found so far:
  the bad-side rank is almost perfectly encoded by an additive sum of overlapping windows of length `n-1`, and for `CUP-2(n=9)` that code is exact after integer rounding.

### Reformulations

- Near-complete window code view:
  the canonical bad-side rank behaves like a distributed additive code over windows that omit only one coordinate.

LOAD-BEARING ASSESSMENT: very high. This is the first representation with near-exact recovery of the global rank from a bounded-width factor model.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`:
  - width `7`: features `10936`, `R^2 = 0.997882`, `RMSE = 0.444219`, rounded exact `7064 / 8687`
  - width `8`: features `29142`, `R^2 = 0.999982`, `RMSE = 0.040462`, rounded exact `8687 / 8687`
- `Sol3(n=9)`:
  - width `6`: features `6562`, `R^2 = 0.973858`, `RMSE = 3.396355`
  - width `7`: features `19684`, `R^2 = 0.995373`, `RMSE = 1.428934`
  - width `8`: features `59032`, `R^2 = 0.999965`, `RMSE = 0.123903`, rounded exact `19581 / 19587`

STRUCTURAL RESULTS:

- The bad-side rank is almost exactly a high-overlap window code one step below full global visibility.
- This turns the vague “distributed descent certificate” idea into a concrete factor hierarchy with measurable saturation.

TOOLS:

- `window_rank_fit.py` now uses sparse CSR matrices plus `scipy.sparse.linalg.lsqr`, allowing much larger window widths.

REPRESENTATIONS:

- “Sparse window code” representation: exact or near-exact additive encoding of rank by overlapping long windows.

### What Would Unblock This

The next useful question is whether the width-`(n-1)` saturation is specific to `n=9` or persists across sizes. The smallest useful computation is:

- `CUP-2(n=5..12)` at widths `n-2` and `n-1`.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.
- Widths tested with sparse solve:
  - `CUP-2`: `7`, `8`
  - `Sol3`: `6`, `7`, `8`

### Open Questions

- Is width `n-1` exact or nearly exact for all `CUP-2(n)`?
- Is there a theorem that any valid witness admits a near-additive `(n-1)`-window rank code?
- Can a sub-threshold nonexistence proof be reframed as failure of such a code under smaller products?

## Synthesis after exploration 8

- The live direction is now substantially stronger than before:
  - good-cycle information theory is weak,
  - bad-side convergence is the right target,
  - and that convergence code has an explicit, near-exact window-factor realization on valid witnesses.
- The immediate next step is no longer conceptual. It is to test whether the width-`(n-1)` saturation persists across `n`, which would turn a witness-specific observation into a candidate theorem pattern.

## Exploration 9

### Strategy

Test the width-`(n-1)` saturation pattern across the full feasible `CUP-2` range `n=5..12`, comparing widths `n-2` and `n-1`.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the possibility that the width-`(n-1)` exactness at `n=9` was a numerical accident. The pattern persists uniformly across all tested `CUP-2` sizes.

### Surviving Structure

- For every tested `CUP-2(n)` with `n = 5..12`, the width-`(n-1)` additive window model recovers the exact canonical bad-side rank after rounding on **every** bad configuration.
- Width `n-2` is already very close but not exact; its max absolute error stays around `2` to `3.14`.
- This gives the first genuinely theorem-shaped empirical statement from the information-theoretic exploration:

  **Empirical pattern:**  
  For `CUP-2(n)`, the canonical bad-side rank is exactly integer-recoverable from an additive sum of cyclic windows of length `n-1`.

### Reformulations

- “All-but-one-coordinate window code” view:
  the bad-side rank is an additive code over windows that each omit exactly one processor value.

LOAD-BEARING ASSESSMENT: extremely high. This is no longer a vague hierarchy; it is a stable exactness pattern across a full size range.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=5)`:
  - width `3`: `R^2 = 0.968390`, rounded exact `62 / 85`
  - width `4 = n-1`: exact, rounded exact `85 / 85`
- `CUP-2(n=6)`:
  - width `4`: `0.983923`, `213 / 293`
  - width `5 = n-1`: exact, `293 / 293`
- `CUP-2(n=7)`:
  - width `5`: `0.990642`, `658 / 932`
  - width `6 = n-1`: rounded exact `932 / 932`, max error `0.142320`
- `CUP-2(n=8)`:
  - width `6`: `0.995278`, `2102 / 2866`
  - width `7 = n-1`: rounded exact `2866 / 2866`
- `CUP-2(n=9)`:
  - width `7`: `0.997882`, `7064 / 8687`
  - width `8 = n-1`: rounded exact `8687 / 8687`
- `CUP-2(n=10)`:
  - width `8`: `0.998894`, `22578 / 26171`
  - width `9 = n-1`: rounded exact `26171 / 26171`
- `CUP-2(n=11)`:
  - width `9`: `0.999421`, `71256 / 78646`
  - width `10 = n-1`: rounded exact `78646 / 78646`
- `CUP-2(n=12)`:
  - width `10`: `0.999686`, `221720 / 236096`
  - width `11 = n-1`: rounded exact `236096 / 236096`

STRUCTURAL RESULTS:

- Width `n-1` is an exact integer code for the canonical rank on every tested `CUP-2`.
- Width `n-2` is systematically near-exact but not exact.
- The gap between `n-2` and `n-1` is consistent enough to suggest that “missing one coordinate per factor” is exactly the right information granularity for the witness rank code.

TOOLS:

- `window_rank_fit.py` plus a cross-`n` harness in the shell proved sufficient to test the pattern over `n=5..12`.

REPRESENTATIONS:

- “Omit-one-site additive code” representation: rank is encoded by summing all cyclic windows that leave out one coordinate.

### What Would Unblock This

The next useful test is to see whether the same width-`(n-1)` exactness holds for other valid witness families, especially `Sol3(n)`. If yes, the phenomenon may be generic to valid token-ring convergence rather than specific to `CUP-2`.

### Key Parameters

- Family tested: `CUP-2`.
- Range tested: `n = 5..12`.
- Widths tested: `n-2`, `n-1`.

### Open Questions

- Does `Sol3(n)` also admit exact or near-exact width-`(n-1)` additive rank coding across `n`?
- Is there a direct constructive proof of the width-`(n-1)` code for `CUP-2`, independent of least squares?
- Can failure of such omit-one-site codes be turned into a lower bound below threshold?

## Synthesis after exploration 9

- The information-theoretic exploration has now produced a concrete candidate theorem object:
  an exact additive omit-one-site code for the bad-side rank on `CUP-2`.
- That object sits squarely on the convergence side, exactly where the earlier obstructions pointed.
- The next question is universality: witness-specific artifact, or generic feature of valid self-stabilizing rings?

## Exploration 10

### Strategy

Test the omit-one-site window code on the second valid witness family `Sol3`, across feasible sizes `n=4..9`, again comparing widths `n-2` and `n-1`.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the width-`(n-1)` staircase is peculiar to `CUP-2`. The same phenomenon appears in `Sol3`.

### Surviving Structure

- `Sol3(n)` shows the same two-level pattern:
  - width `n-2`: decent but visibly imperfect,
  - width `n-1`: near-exact, and exactly exact for small `n`.
- Exactness/near-exactness by width `n-1`:
  - `n=4`: exact
  - `n=5`: exact
  - `n=6`: `R^2 = 0.999112`, max error `0.779956`
  - `n=7`: `0.999708`, max error `0.688459`
  - `n=8`: `0.999906`, max error `0.561594`
  - `n=9`: `0.999965`, max error `0.585137`
- So the omit-one-site code is not unique to the threshold witness; it seems tied to valid convergence more broadly.

### Reformulations

- Candidate universality principle:
  valid self-stabilizing token-ring systems may admit bad-side rank codes with negligible or zero full-order interaction, i.e. codes decomposable into omit-one-site windows.

LOAD-BEARING ASSESSMENT: very high, with a caveat. This is a strong cross-family pattern, but it still needs a null-model sanity check to ensure width-`(n-1)` exactness is not a generic linear-capacity artifact.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `Sol3(n=4)`:
  - width `2`: `R^2 = 0.962644`
  - width `3 = n-1`: exact, `45 / 45`
- `Sol3(n=5)`:
  - width `3`: `0.912588`
  - width `4 = n-1`: exact, `195 / 195`
- `Sol3(n=6)`:
  - width `4`: `0.965664`
  - width `5 = n-1`: `R^2 = 0.999112`, rounded exact `603 / 669`
- `Sol3(n=7)`:
  - width `5`: `0.981867`
  - width `6 = n-1`: `0.999708`, rounded exact `2055 / 2115`
- `Sol3(n=8)`:
  - width `6`: `0.990640`
  - width `7 = n-1`: `0.999906`, rounded exact `6465 / 6477`
- `Sol3(n=9)`:
  - width `7`: `0.995373`
  - width `8 = n-1`: `0.999965`, rounded exact `19581 / 19587`

STRUCTURAL RESULTS:

- The omit-one-site window code appears across two qualitatively different valid witness families.

TOOLS:

- The sparse `window_rank_fit.py` hierarchy is now validated on both `CUP-2` and `Sol3`.

REPRESENTATIONS:

- “Cross-family omit-one-site code” representation: a candidate generic factorization for valid convergence ranks.

### What Would Unblock This

One crucial null-model test is now necessary:

- fit the same width-`(n-1)` model to random target labels on the same bad-config sets.

If random labels also fit exactly or near-exactly, then the observed staircase is mostly a linear-capacity artifact. If they do not, then the rank-code phenomenon is genuinely structured.

### Key Parameters

- Family tested: `Sol3`.
- Range tested: `n = 4..9`.
- Widths tested: `n-2`, `n-1`.

### Open Questions

- Is the width-`(n-1)` exactness/nontriviality real, or just linear span explosion?
- If real, what property of rank kills the final full-order interaction term?

## Synthesis after exploration 10

- The strongest empirical pattern is now universal across the two witness families tested.
- But this is exactly the point where a false positive is most dangerous: the omit-one-site model may simply be too expressive.
- The next attempt must therefore be a null-model capacity check, not another witness fit.

## Exploration 11

### Strategy

Run a null-model capacity check: fit the same window models not only to the true bad-side rank, but also to shuffled and random targets on the same bad-config set, at widths `n-2` and `n-1`.

### Outcome

SUCCEEDED

### Failure Constraint

The width-`(n-1)` model is so expressive that very high fit quality is not unique to the true rank. Therefore width-`(n-1)` exactness alone cannot be treated as a deep structural fact without comparison to null models.

### What This Rules Out

It rules out the naive interpretation of exploration 9 and 10 that exact or near-exact width-`(n-1)` fitting is by itself mathematically significant. At that width, model capacity is already high enough to fit arbitrary targets very well.

### Surviving Structure

- Width `n-2` remains highly informative:
  - `CUP-2(n=9), width 7`:
    - actual `R^2 = 0.9979`
    - permuted rank `0.6675`
    - random target `0.6748`
  - `Sol3(n=9), width 7`:
    - actual `0.9954`
    - permuted `0.5716`
    - random `0.5724`
- Width `n-1` is much less informative:
  - `CUP-2(n=9), width 8`:
    - actual `0.99998`
    - permuted `0.99277`
    - random `0.99265`
  - `Sol3(n=9), width 8`:
    - actual `0.99997`
    - permuted `0.97704`
    - random `0.97503`
- Therefore the nontrivial structural signal lives one step below full expressivity, at width `n-2`, not at width `n-1`.

### Reformulations

- Capacity-calibrated window-code view:
  high-width fits must be judged against random-label baselines on the same design matrix. This turns the window hierarchy into a genuine capacity-vs-structure analysis rather than a raw `R^2` race.

LOAD-BEARING ASSESSMENT: very high. This was a necessary sanity check and materially changed the interpretation of the strongest previous observation.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9), width 7`:
  - actual `(R^2, RMSE, max_err) = (0.99788, 0.444, 2.83)`
  - shuffled rank `(0.66748, 5.565, 22.82)`
  - random Gaussian `(0.67485, 0.570, 2.20)`
- `CUP-2(n=9), width 8`:
  - actual `(0.99998, 0.0405, 0.173)`
  - shuffled `(0.99277, 0.821, 2.92)`
  - random `(0.99265, 0.0857, 0.302)`
- `Sol3(n=9), width 7`:
  - actual `(0.99537, 1.429, 8.10)`
  - shuffled `(0.57161, 13.749, 53.07)`
  - random `(0.57237, 0.653, 2.70)`
- `Sol3(n=9), width 8`:
  - actual `(0.99997, 0.1239, 0.585)`
  - shuffled `(0.97704, 3.183, 12.49)`
  - random `(0.97503, 0.1578, 0.626)`

STRUCTURAL RESULTS:

- Width `n-1` exactness is partly a linear-capacity artifact.
- Width `n-2` remains highly nontrivial and is currently the strongest meaningful signal.

TOOLS:

- `info_theory/window_null_model.py`
  Inputs: witness family, `n`, width, and RNG seed.
  Outputs: fit quality for actual rank, shuffled rank, and random targets under the same window model.

REPRESENTATIONS:

- “Capacity-calibrated factor code” representation: evaluate structured fit only relative to the null fit floor induced by model expressivity.

### What Would Unblock This

The next useful computation is to run the same null-model comparison for `CUP-2(n)` across sizes at width `n-2`. If the actual-vs-null gap persists uniformly, that becomes a meaningful cross-`n` structural invariant.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.
- Widths tested: `n-2`, `n-1`.

### Open Questions

- Does the width-`(n-2)` actual-vs-null gap persist uniformly across `CUP-2(n)`?
- Can that gap be converted into a lower-bound style statement?

## Synthesis after exploration 11

- The omit-one-site code is real but partly vacuous at the top width.
- The genuinely informative phenomenon is now narrower and better defined:
  the true rank is exceptionally compressible at width `n-2`, far beyond null-model baselines.
- That is the correct target for further information-theoretic work.

## Exploration 12

### Strategy

Measure the null-model gap across `CUP-2(n=5..12)` at width `n-2`, comparing the true rank against shuffled and random targets under the same window model.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the concern that the width-`n-2` staircase is just another generic capacity effect. Across all tested `n`, the true rank is compressed dramatically better than shuffled or random targets.

### Surviving Structure

- For `CUP-2(n=5..12)`, actual width-`n-2` fit quality rises monotonically:
  - `0.9684, 0.9839, 0.9906, 0.9953, 0.9979, 0.9989, 0.9994, 0.9997`
- The shuffled/random null baselines stay much lower:
  - shuffled roughly `0.54` to `0.74`
  - random roughly `0.61` to `0.74`
- So the true rank has a strong cross-`n` low-order structure that is not explained by model size alone.

### Reformulations

- Width-`n-2` structural gap view:
  the meaningful information-theoretic invariant is the gap between
  actual-rank compressibility and null-label compressibility at one step below the omit-one-site ceiling.

LOAD-BEARING ASSESSMENT: very high. This is currently the strongest nontrivial cross-`n` information-theoretic signal attached to the threshold witness family.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=5)`, width `3`:
  - actual `R^2 = 0.968390`
  - shuffled `0.538313`
  - random `0.692277`
- `CUP-2(n=6)`, width `4`:
  - actual `0.983923`
  - shuffled `0.617771`
  - random `0.605135`
- `CUP-2(n=7)`, width `5`:
  - actual `0.990642`
  - shuffled `0.628196`
  - random `0.610257`
- `CUP-2(n=8)`, width `6`:
  - actual `0.995278`
  - shuffled `0.629306`
  - random `0.656116`
- `CUP-2(n=9)`, width `7`:
  - actual `0.997882`
  - shuffled `0.669250`
  - random `0.665377`
- `CUP-2(n=10)`, width `8`:
  - actual `0.998894`
  - shuffled `0.679838`
  - random `0.680516`
- `CUP-2(n=11)`, width `9`:
  - actual `0.999421`
  - shuffled `0.720736`
  - random `0.714873`
- `CUP-2(n=12)`, width `10`:
  - actual `0.999686`
  - shuffled `0.738403`
  - random `0.739678`

STRUCTURAL RESULTS:

- The width-`n-2` compressibility gap is robust across the entire tested `CUP-2` range.
- This is the best current candidate for a genuinely nontrivial information-theoretic invariant of convergence.

TOOLS:

- `window_null_model.py` combined with a cross-`n` shell harness provides the needed calibration between structured and random targets.

REPRESENTATIONS:

- “One-below-ceiling structural gap” representation: compare the rank code to null labels at width `n-2`, where the model is strong but not yet generically exact.

### What Would Unblock This

The next useful step is mathematical interpretation, not more curve fitting:

- explain why valid convergence ranks should have small residual beyond width `n-2`,
- and identify what that residual means combinatorially/information-theoretically.

### Key Parameters

- Family tested: `CUP-2`.
- Range tested: `n = 5..12`.
- Width tested: `n-2`.

### Open Questions

- Is there an analytic reason the true rank nearly lies in the width-`n-2` window subspace?
- Can the width-`n-2` residual be bounded below for invalid or sub-threshold candidate systems?

## Synthesis after exploration 12

- The information-theoretic picture is now much cleaner than at the start:
  - good-cycle quantities are weak,
  - liveness cover counts are weak,
  - convergence is the right target,
  - omit-one-site exactness is partly generic,
  - but width-`n-2` compressibility is strongly and nontrivially special.
- The live research problem is therefore:
  understand and eventually lower-bound the width-`n-2` distributed factor complexity of convergence ranks.

## Exploration 13

### Strategy

Derive the exact linear dimension of the additive contiguous-window models and compare those dimensions to the observed null-model baselines.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the null baselines as mysterious empirical artifacts. They are explained by the linear capacity of the window model itself.

### Surviving Structure

- For width `w`, the additive contiguous-window model on the full configuration space has dimension

  `dim_w = Σ_{S contained in some width-w window} Π_{i in S} (m_i - 1)`.

- Therefore:
  - width `n-1` codimension is exactly `Π_i (m_i - 1)` (the full interaction term only),
  - width `n-2` codimension is the weighted sum over vertex covers of `C_n`.
- For the tested witness families, the full-space dimension fraction matches the random-label fit floor very closely:
  - `CUP-2(n=9), width 7`: full-space dim fraction `0.655235`, random baseline `0.665377`
  - `Sol3(n=9), width 7`: dim fraction `0.569171`, random baseline `0.572373`
- So the null baselines are now understood: they are essentially the normalized rank of the design subspace.

### Reformulations

- Interaction-model view:
  the window code hierarchy is exactly a hierarchical interaction model. Width `n-2` excludes precisely the interaction supports whose complement contains no adjacent pair, i.e. the weighted vertex covers of the cycle.

LOAD-BEARING ASSESSMENT: extremely high. This turns the window-fit experiments from black-box regression into explicit finite-dimensional harmonic analysis on the ring.

### Concrete Artifacts

STRUCTURAL RESULTS:

- Dimension formula:
  `dim_w = Σ_{S ⊆ [n], S ⊆ W for some width-w window W} Π_{i∈S}(m_i-1)`.
- Special cases:
  - `codim_{n-1} = Π_i (m_i - 1)`
  - `codim_{n-2} = Σ_{S vertex cover of C_n} Π_{i∈S}(m_i - 1)`

COMPUTED EXAMPLES:

- `CUP-2(n=9)`:
  - width `7`: `dim = 5732`, `codim = 3016`, `dim/total = 0.655235`
  - width `8`: `dim = 8620`, `codim = 128`, `dim/total = 0.985368`
- `Sol3(n=9)`:
  - width `7`: `dim = 11203`, `codim = 8480`, `dim/total = 0.569171`
  - width `8`: `dim = 19171`, `codim = 512`, `dim/total = 0.973988`
- `CUP-2(n=5..12)`, width `n-2`, full-space dimension fractions:
  - `0.5000, 0.5432, 0.5844, 0.6214, 0.6552, 0.6860, 0.7141, 0.7396`
  matching the observed random-label floors.

TOOLS:

- `info_theory/window_model_dimension.py`
  Inputs: family, `n`, and width.
  Outputs: exact model dimension/codimension and special-case checks.

REPRESENTATIONS:

- “Weighted interaction lattice” representation: window models are sums of interaction spaces indexed by subsets, and width `n-2` fails exactly on weighted vertex-cover supports.

### What Would Unblock This

The next useful step is to analyze the actual rank in this interaction basis, not just the model dimension. The smallest useful computation is an ANOVA/interaction-energy decomposition of an extension of the bad-side rank to the full configuration space.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`, plus `CUP-2(n=5..12)` for width `n-2` dimension fractions.

### Open Questions

- Does the true rank have unusually small energy on the forbidden vertex-cover interactions?
- Is that the right mathematical statement behind the width-`n-2` compressibility gap?

## Synthesis after exploration 13

- The null baselines are now explained exactly by model dimension.
- This clears the way for the next real question:
  not “how big is the subspace?” but “why does the true rank place so little mass on the forbidden interaction directions?”

## Exploration 14

### Strategy

Compute the exact ANOVA / interaction decomposition of a full-space extension of the bad-side rank and measure the fraction of L2 energy lying on the interaction supports forbidden by the width-`n-2` window model. Compare against shuffled labels.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the width-`n-2` compressibility gap is only a regression artifact. The true rank is special already at the level of exact interaction energy: it places almost no mass on the forbidden supports.

### Surviving Structure

- The natural forbidden supports for width `n-2` are exactly the vertex-cover-type interaction subsets identified in exploration 13.
- For the true rank extension, the forbidden-energy fraction is tiny:
  - `CUP-2(n=9)`: `0.000243`
  - `Sol3(n=9)`: `0.000496`
- For shuffled labels, the forbidden-energy fraction is much larger:
  - `CUP-2(n=9)`: `0.037269`
  - `Sol3(n=9)`: `0.046499`
- Across `CUP-2(n=5..9)`, the true forbidden fraction decays rapidly:
  - `0.017567, 0.004541, 0.001877, 0.000686, 0.000243`
  while shuffled stays at
  - `0.156007, 0.102526, 0.078132, 0.055796, 0.038038`
- Across `Sol3(n=4..9)`, the same pattern holds:
  - actual `0.138680, 0.029677, 0.007265, 0.002989, 0.001230, 0.000496`
  - shuffled `0.375847, 0.209676, 0.136740, 0.090565, 0.062552, 0.047618`

### Reformulations

- Forbidden-interaction energy view:
  the meaningful object is not just fit quality, but the exact amount of ANOVA mass lying on the supports that the width-`n-2` model cannot represent.

LOAD-BEARING ASSESSMENT: extremely high. This is currently the strongest and cleanest information-theoretic invariant found. It converts the window-fit phenomenon into a precise statement about suppressed high-order interaction energy.

### Concrete Artifacts

STRUCTURAL RESULTS:

- Width `n-2` forbidden supports correspond to vertex-cover-type interactions on the cycle.
- The bad-side rank extension for both witness families has vanishing energy on those supports.

COMPUTED EXAMPLES:

- `CUP-2(n=9), width 7`:
  - actual forbidden-energy fraction `0.000243`
  - shuffled forbidden-energy fraction `0.037269`
- `Sol3(n=9), width 7`:
  - actual `0.000496`
  - shuffled `0.046499`
- `CUP-2(n=5..9)` actual vs shuffled:
  - `n=5`: `0.017567` vs `0.156007`
  - `n=6`: `0.004541` vs `0.102526`
  - `n=7`: `0.001877` vs `0.078132`
  - `n=8`: `0.000686` vs `0.055796`
  - `n=9`: `0.000243` vs `0.038038`
- `Sol3(n=4..9)` actual vs shuffled:
  - `n=4`: `0.138680` vs `0.375847`
  - `n=5`: `0.029677` vs `0.209676`
  - `n=6`: `0.007265` vs `0.136740`
  - `n=7`: `0.002989` vs `0.090565`
  - `n=8`: `0.001230` vs `0.062552`
  - `n=9`: `0.000496` vs `0.047618`

TOOLS:

- `info_theory/anova_interaction_spectrum.py`
  Inputs: witness family, `n`, width, and RNG seed.
  Outputs: exact ANOVA forbidden-energy fraction for the rank extension and a shuffled null model.

REPRESENTATIONS:

- “Vertex-cover interaction suppression” representation: valid convergence ranks appear to suppress exactly the interaction directions excluded by the width-`n-2` window model.

### What Would Unblock This

The next mathematical step is to interpret the forbidden vertex-cover interactions directly in token-ring terms. We now need a combinatorial meaning for why these interaction modes are suppressed on valid witnesses.

### Key Parameters

- Families tested: `CUP-2(n=5..9)`, `Sol3(n=4..9)`.
- Width tested: `n-2`.

### Open Questions

- What do the forbidden vertex-cover interactions mean dynamically?
- Can one prove that valid convergence forces those interactions to vanish or decay?
- Do invalid near-threshold candidate systems necessarily have much larger forbidden interaction energy?

## Synthesis after exploration 14

- The best current invariant is now clear:
  valid witness ranks have extremely small energy on the width-`n-2` forbidden interaction supports.
- This is stronger than regression fit quality and survives null-model calibration.
- The next live problem is interpretive rather than computational:
  explain the suppression of vertex-cover interactions in ring dynamics, and test whether invalid candidates fail this suppression.

## Exploration 15

### Strategy

Construct comparable scalars on explicit invalid/subthreshold candidate families using the forced mover-entry kernel from the finite `n=5,6` residual cases, and test whether those scalars fail the same width-`n-2` forbidden-interaction suppression.

### Outcome

SUCCEEDED

### Failure Constraint

A genuine DAG rank does not exist for invalid candidates because of bad cycles, so the scalar had to be changed. The chosen substitutes were:

- kernel indicator,
- sink-peeling depth with kernel at the top level.

### What This Rules Out

It rules out the worry that the forbidden-interaction suppression is a generic feature of any cycle-induced or mover-induced scalar. Explicit invalid residual families have substantially larger forbidden width-`n-2` energy.

### Surviving Structure

- In the `n=5,6` residual subthreshold families, the forced mover-entry graph already contains a nonempty kernel, matching the finite lemmas.
- The canonical invalid-side scalars have much larger forbidden width-`n-2` energy than valid witness ranks:
  - `n=5` residual cycles:
    - kernel indicator: about `0.078` to `0.088`
    - peel depth: about `0.072` to `0.079`
  - `n=6` residual cycles:
    - kernel indicator: about `0.031` to `0.040`
    - peel depth: about `0.021` to `0.025`
- These are still below shuffled null baselines, but they are far above the corresponding valid-witness values:
  - valid `CUP-2(n=5)`: `0.017567`
  - valid `CUP-2(n=6)`: `0.004541`

### Reformulations

- Forced-kernel scalar view:
  when convergence rank is unavailable because of bad SCCs, the obstruction itself defines natural scalar functions whose forbidden-mode energy can still be measured.

LOAD-BEARING ASSESSMENT: high. This is the first direct invalid/subthreshold comparison, and it points in the right direction: invalid residual families do not suppress the forbidden modes nearly as strongly as valid witnesses.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `n=5`, `ms=(2,2,2,3,3)`, first four full cycles:
  - cycle 0 length `18`:
    - kernel indicator `0.077652` vs shuffled `0.195707`
    - peel depth `0.071935` vs shuffled `0.162024`
  - cycle 1 length `17`:
    - kernel indicator `0.086043` vs shuffled `0.250678`
    - peel depth `0.073381` vs shuffled `0.194804`
  - cycle 2 length `17`:
    - kernel indicator `0.088076` vs shuffled `0.205962`
    - peel depth `0.079303` vs shuffled `0.146317`
  - cycle 3 length `16`:
    - kernel indicator `0.078571` vs shuffled `0.253175`
    - peel depth `0.073968` vs shuffled `0.153068`
- `n=6`, `ms=(2,2,2,3,3,3)`, first four full cycles:
  - kernel indicator roughly `0.031332` to `0.040049`
  - peel depth roughly `0.020846` to `0.024903`

STRUCTURAL RESULTS:

- Invalid/subthreshold residual cycles fail the forbidden-mode suppression much more strongly than valid witness ranks.

TOOLS:

- `info_theory/forced_kernel_spectrum.py`
  Inputs: `n=5` or `6`, plus number of cycles.
  Outputs: forbidden-energy fractions for kernel indicator and peel-depth scalars on residual forced-kernel families.

REPRESENTATIONS:

- “Forced-kernel obstruction spectrum” representation: invalidity encoded as either kernel membership or peeling depth on the forced graph.

### What Would Unblock This

The next useful step is to connect the valid-side suppression to the actual convergence proof decomposition, to see what part of the proof architecture is killing the forbidden modes.

### Key Parameters

- Families tested: residual subthreshold `n=5,6` forced-kernel families.

### Open Questions

- Can the gap between valid-witness forbidden energy and forced-kernel forbidden energy be turned into a clean criterion?
- Are there invalid families with low forbidden energy that would break this line?

## Exploration 16

### Strategy

Explain the forbidden-mode suppression by decomposing the valid convergence rank into the project’s own two-level pieces: `FutureFc` and rank inside the constant-`FutureFc` slices.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out a purely mysterious “rank is globally magical” interpretation. Most of the suppression already appears in simple frontier-based quantities; the slice rank carries only the residual.

### Surviving Structure

- On both witness families at `n=9`, `fc` and `FutureFc` themselves have extremely small forbidden width-`n-2` energy:
  - `CUP-2`:
    - `FutureFc`: `0.000255` vs shuffled `0.015972`
    - `fc`: `0.000265` vs shuffled `0.021312`
  - `Sol3`:
    - `FutureFc`: `0.000170` vs shuffled `0.018245`
    - `fc`: `0.000126` vs shuffled `0.023934`
- The residual forbidden energy sits mainly in the constant-`FutureFc` slice rank:
  - `CUP-2`: `cf_rank = 0.006709` vs shuffled `0.119919`
  - `Sol3`: `0.025427` vs shuffled `0.161136`
- So the explanation is:
  1. the main large-scale convergence geometry is already width-`n-2` local through frontier structure,
  2. the remaining global correction is the DAG rank within constant-`FutureFc` slices,
  3. even that slice rank still suppresses forbidden modes compared to null labels.

### Reformulations

- Two-level suppression view:
  width-`n-2` suppression is mostly a frontier/FutureFc phenomenon, with a smaller but still structured residual inside each constant-FutureFc layer.

LOAD-BEARING ASSESSMENT: extremely high. This is the first direct bridge from the information-theoretic invariant back to the actual proof architecture.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9), width 7`:
  - `FutureFc`: actual `0.000255`, shuffled `0.015972`
  - `cf_rank`: actual `0.006709`, shuffled `0.119919`
  - `fc`: actual `0.000265`, shuffled `0.021312`
- `Sol3(n=9), width 7`:
  - `FutureFc`: actual `0.000170`, shuffled `0.018245`
  - `cf_rank`: actual `0.025427`, shuffled `0.161136`
  - `fc`: actual `0.000126`, shuffled `0.023934`

STRUCTURAL RESULTS:

- Forbidden-mode suppression is not uniform across the proof ingredients.
- The slice-rank term is the main carrier of the residual nonlocal interaction.

TOOLS:

- `info_theory/twolevel_spectrum.py`
  Inputs: witness family and `n`.
  Outputs: forbidden-energy fractions for `fc`, `FutureFc`, and constant-`FutureFc` slice rank.

REPRESENTATIONS:

- “Two-level interaction suppression” representation: global convergence rank = frontier-driven coarse structure plus a smaller structured slice correction.

### What Would Unblock This

The next useful step is to interpret the constant-`FutureFc` slice rank combinatorially: what geometric object inside a fixed frontier level is it actually measuring?

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.
- Width tested: `n-2`.

### Open Questions

- Can the slice-rank forbidden energy be described in terms of interface motion or boundary state automata?
- Is the slice-rank term the right place to look for a threshold lower bound?

## Synthesis after exploration 16

- The explanation and the invalidity test now line up:
  - valid systems suppress forbidden modes strongly,
  - invalid/subthreshold residual families suppress them much less,
  - and on valid systems most of the suppression comes from the frontier/FutureFc layer, with the slice rank carrying the remaining nonlocal correction.
- The live next question is now very focused:
  understand the constant-`FutureFc` slice rank as an interaction object, and see whether subthreshold obstructions force that slice term to retain too much forbidden mass.

## Exploration 17

### Strategy

Probe the remaining slice-rank term directly: measure how much of `cf_rank` is explained by boundary data and proof107-style interior invariants, and inspect which forbidden masks dominate the residual.

### Outcome

SUCCEEDED

### Failure Constraint

Boundary data alone does not determine the slice rank. Even after adding `FutureFc` and the proof107-style interior invariants `(exp2, int21, exp2_weight)`, about one bit of slice-rank entropy remains unexplained at `n=9`.

### What This Rules Out

It rules out the simplest explanation that the residual slice rank is just the 6-tuple boundary automaton rank in disguise. The slice rank still contains genuinely nontrivial interior/global structure.

### Surviving Structure

- The proof107-style features explain a substantial but incomplete part of `cf_rank`:
  - `CUP-2(n=9)`:
    - `H(cf_rank) = 4.0036` bits
    - `I((FutureFc, boundary6, intCounts); cf_rank) = 2.6141` bits
    - with proof107 invariants `(exp2, int21, exp2_weight)` this rises to `3.1171` bits
  - `Sol3(n=9)`:
    - `H(cf_rank) = 4.2287`
    - `I((FutureFc, boundary6, intCounts); cf_rank) = 2.6314`
    - with proof107 invariants it rises to `3.2201`
- The residual forbidden modes are patterned, not diffuse:
  - `CUP-2(n=9)` top omitted sets for `cf_rank` often involve site `7` together with one or two separated interior sites, e.g. omit `{3,7}`, `{5,7}`, `{2,5,7}`.
  - `Sol3(n=9)` top omitted sets heavily involve endpoint `8`, e.g. omit `{8}`, `{5,8}`, `{3,8}`.
- The good-set indicator alone has *large* forbidden width-`n-2` mass:
  - `CUP-2(n=9)`: `0.1284`
  - `Sol3(n=9)`: `0.1670`
  So the near-zero forbidden mass of the rank extension is not a trivial boundary artifact; it requires strong cancellation/structure.

### Reformulations

- Residual slice-rank view:
  after stripping off the frontier layer and the known proof107 invariants, the remaining nonlocality is a structured low-bit residual concentrated on specific omitted-site patterns.

LOAD-BEARING ASSESSMENT: high. This does not yet give a theorem, but it sharply narrows what is left unexplained.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`:
  - `I(boundary6; cf_rank) = 1.0711`
  - `I((FutureFc,boundary6); cf_rank) = 1.8345`
  - `I((FutureFc,boundary6,intCounts); cf_rank) = 2.6141`
  - `I((FutureFc,boundary6,proof107 invariants); cf_rank) = 3.1171`
- `Sol3(n=9)`:
  - `I(boundary6; cf_rank) = 1.1018`
  - `I((FutureFc,boundary6); cf_rank) = 2.1511`
  - `I((FutureFc,boundary6,intCounts); cf_rank) = 2.6314`
  - `I((FutureFc,boundary6,proof107 invariants); cf_rank) = 3.2201`

STRUCTURAL RESULTS:

- The residual slice-rank term is neither purely boundary-local nor random.
- The residual forbidden interactions localize to a small family of omitted-site patterns.

TOOLS:

- `info_theory/slice_rank_boundary.py`
  Inputs: witness family and `n`.
  Outputs: mutual-information and support statistics for `cf_rank` against boundary and interior summary features.

REPRESENTATIONS:

- “Residual slice code” representation: the frontier layer plus proof107 invariants explain most of the slice rank, leaving a small structured remainder.

### What Would Unblock This

The next useful step is to identify a combinatorial object that exactly captures the remaining ~1 bit of slice-rank entropy per family at `n=9`.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.

### Open Questions

- What boundary/interior summary finishes the explanation of `cf_rank`?
- Why do the residual forbidden masks concentrate on those particular omitted-site patterns?

## Synthesis after exploration 17

- The remaining unexplained piece is now small and concrete:
  a structured residual inside the constant-`FutureFc` slice rank.
- The large picture remains intact:
  frontier quantities kill almost all forbidden interactions,
  invalid/subthreshold residual families retain much more,
  and the remaining valid residual is highly patterned rather than generic.

## Exploration 18

### Strategy

Search for a small explicit feature basis that determines the residual constant-`FutureFc` slice rank, starting from the proof107-style base invariants and greedily adding simple interior observables.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the slice-rank residual is a diffuse high-complexity object. At `n=9`, a tiny number of simple weighted interior features closes the remaining entropy exactly.

### Surviving Structure

- For both witness families at `n=9`, the slice rank is exactly determined by:
  - the base key `(FutureFc, boundary6, exp2, int21, exp2_weight)`,
  - plus `interior_sum`,
  - plus two weighted adjacent-pair features.
- `CUP-2(n=9)`:
  - base MI: `3.1171 / 4.0036`
  - + `interior_sum`: `3.8701`
  - + `weight_pair_01`: `3.9847`
  - + `weight_pair_02`: `4.0036` (exact)
- `Sol3(n=9)`:
  - base MI: `3.2201 / 4.2287`
  - + `interior_sum`: `4.1273`
  - + `weight_pair_10`: `4.2231`
  - + `weight_pair_12`: `4.2287` (exact)
- So the residual slice-rank code is not only structured; it is *small* and expressible in terms of weighted counts of adjacent interior pair types.

### Reformulations

- Small explicit slice-code view:
  the constant-`FutureFc` slice rank is exactly encoded by a handful of low-order weighted interior statistics, not by a large hidden state.

LOAD-BEARING ASSESSMENT: extremely high. This is the cleanest explanation yet of the residual term and sharply reduces the search space for any analytic proof.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)` greedy completion:
  - step 1: `interior_sum`
  - step 2: `weight_pair_01`
  - step 3: `weight_pair_02`
  - exact total MI = `H(cf_rank)`
- `Sol3(n=9)` greedy completion:
  - step 1: `interior_sum`
  - step 2: `weight_pair_10`
  - step 3: `weight_pair_12`
  - exact total MI = `H(cf_rank)`

STRUCTURAL RESULTS:

- The residual slice-rank term at `n=9` is exactly a low-order interior weighted-pair code once the frontier layer is factored out.

TOOLS:

- `info_theory/slice_feature_search.py`
  now supports greedy feature selection via `--greedy-steps`.

REPRESENTATIONS:

- “Low-order weighted-pair slice code” representation: the residual convergence information is encoded by weighted counts of a few adjacent pair types.

### What Would Unblock This

The next useful step is to see whether this exact low-order feature closure persists across `n`, and whether the chosen pair types admit a simple closed-form dynamic interpretation.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.

### Open Questions

- Do the same three-feature completions persist for larger `n`?
- Is there a direct token-ring meaning for `interior_sum + weighted pair counts` that makes the slice-rank formula obvious?

## Synthesis after exploration 18

- The information-theoretic picture is now unexpectedly concrete:
  - valid convergence suppresses forbidden vertex-cover interactions,
  - most of that is handled by frontier/FutureFc,
  - the residual slice rank is exactly a tiny weighted-pair code at `n=9`,
  - invalid/subthreshold residual families retain much more forbidden mass.
- The live next problem is now formula discovery:
  turn the weighted-pair slice code into a closed-form dynamic interpretation and test its persistence across `n`.

## Exploration 19

### Strategy

Test whether the `n=9` slice-rank closure extends across `CUP-2(n)` using a fixed low-order feature scaffold rather than size-specific greedy search.

### Outcome

SUCCEEDED

### Failure Constraint

The fixed four-feature scaffold is not exact forever: it is exact through `n=10` and remains extremely close at `n=11`, but not literally exact there.

### What This Rules Out

It rules out the strongest naive version of the formula claim:

- “the same four features give an exact formula for all `n`.”

But it strongly supports the weaker and still very useful claim:

- the same tiny scaffold remains the right low-order basis across sizes.

### Surviving Structure

- Fixed scaffold tested:
  - `interior_sum`
  - `weight_pair_01`
  - `weight_pair_02`
  - `even_val_sum`
- For `CUP-2`, this single feature set gives exact slice-rank recovery for:
  - `n=5,6,7,8,9,10`
- At `n=11` it is still extremely close:
  - `H(cf_rank) = 4.200340`
  - scaffold MI `= 4.192050`

### Reformulations

- Uniform low-order scaffold view:
  the slice rank appears to live in a very small family of weighted interior pair/sum statistics across `n`, even if the exact coefficients or one final correction term may drift.

LOAD-BEARING ASSESSMENT: very high. This is the first cross-`n` formula scaffold for the slice-rank residual.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Fixed scaffold exactness on `CUP-2`:
  - `n=5`: exact
  - `n=6`: exact
  - `n=7`: exact
  - `n=8`: exact
  - `n=9`: exact
  - `n=10`: exact
- `n=11`:
  - `H = 4.200340`
  - scaffold MI `= 4.192050`
  - not exact, but very close

STRUCTURAL RESULTS:

- The low-order slice code is not a one-off `n=9` artifact.
- A fixed weighted-pair scaffold already captures essentially all slice-rank information through the theorem-relevant range tested.

TOOLS:

- Reused `slice_feature_search.py` plus direct MI evaluation on a fixed feature set.

REPRESENTATIONS:

- “Uniform weighted-pair scaffold” representation: a candidate cross-`n` formula basis for the residual slice rank.

### What Would Unblock This

The next useful step is to identify the missing correction term beyond the four-feature scaffold, beginning at `n=11`.

### Key Parameters

- Family tested: `CUP-2`.
- Range tested: exact through `n=10`, near-exact at `n=11`.

### Open Questions

- What is the first correction term beyond the four-feature scaffold?
- Does the same scaffold work, after relabeling, on `Sol3(n)`?

## Synthesis after exploration 19

- The emerging formula picture is now:
  - frontier/FutureFc explains most of the convergence code,
  - a tiny weighted-pair scaffold explains the slice residual through `n=10`,
  - only a very small correction remains by `n=11`.
- This is enough structure to start aiming for an actual closed-form conjecture rather than just qualitative information-theoretic language.

## Exploration 20

### Strategy

Test whether a fixed low-order feature scaffold, chosen from the `n=9` slice-rank analysis, continues to determine the `CUP-2` slice rank across `n`.

### Outcome

SUCCEEDED

### Failure Constraint

The fixed scaffold is not literally exact forever: it is exact through `n=10` and remains extremely close at `n=11`, so a small correction term appears there.

### What This Rules Out

It rules out the possibility that the `n=9` weighted-pair closure was an isolated coincidence. The same scaffold works uniformly over a nontrivial size range.

### Surviving Structure

- Fixed scaffold:
  - `interior_sum`
  - `weight_pair_01`
  - `weight_pair_02`
  - `even_val_sum`
- On `CUP-2`, this one scaffold gives exact slice-rank recovery for:
  - `n = 5, 6, 7, 8, 9, 10`
- At `n = 11` it remains extremely close:
  - `H(cf_rank) = 4.200340`
  - scaffold MI `= 4.192050`
- Greedy closures at smaller `n` simplify naturally:
  - `n=5,6`: counts of interior values already suffice
  - `n=7`: `odd_val_sum` plus counts
  - `n=8..10`: the weighted-pair scaffold stabilizes

### Reformulations

- Uniform scaffold conjecture:
  the constant-`FutureFc` slice rank of `CUP-2` is governed by a stable low-order interior summary basis, with only a small correction appearing beyond `n=10`.

LOAD-BEARING ASSESSMENT: very high. This is the first cross-`n` formula scaffold for the residual convergence code, not just a collection of local fits.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Fixed four-feature scaffold on `CUP-2`:
  - `n=5`: exact
  - `n=6`: exact
  - `n=7`: exact
  - `n=8`: exact
  - `n=9`: exact
  - `n=10`: exact
  - `n=11`: `MI = 4.192050` vs `H = 4.200340`
- Greedy `CUP-2` closures:
  - `n=5`: `count_val_0` already closes
  - `n=6`: `count_val_0` closes
  - `n=7`: `odd_val_sum` closes
  - `n=8`: `interior_sum`, `weight_pair_10`
  - `n=9`: `interior_sum`, `weight_pair_01`, `weight_pair_02`
  - `n=10`: same three plus a tiny final `even_val_sum`

STRUCTURAL RESULTS:

- The residual slice rank is controlled by a very small uniform basis through the tested theorem-range sizes.

TOOLS:

- Reused `slice_feature_search.py` and direct MI evaluation on a fixed feature set.

REPRESENTATIONS:

- “Uniform weighted-pair scaffold” representation: a stable cross-`n` basis for the slice-rank residual.

### What Would Unblock This

The next useful step is to identify the first correction term beyond this scaffold, starting at `n=11`, and see whether it also stabilizes into a simple pattern.

### Key Parameters

- Family tested: `CUP-2`.
- Range tested: exact through `n=10`, near-exact at `n=11`.

### Open Questions

- What is the first correction term beyond the four-feature scaffold?
- Does the same scaffold, after relabeling, govern `Sol3(n)` too?

## Synthesis after exploration 20

- The convergence-side information code is now close to a real formula:
  a frontier layer plus a tiny weighted-pair scaffold, with only a small higher-order correction emerging at larger `n`.
- The next live task is not broad search. It is identifying that first correction term.

## Exploration 21

### Strategy

Search for the first correction term beyond the fixed four-feature scaffold, focusing on the first non-exact case `CUP-2(n=11)` and checking whether the same scaffold is already complete on `Sol3(n=9)`.

### Outcome

SUCCEEDED

### Failure Constraint

The first correction term at `CUP-2(n=11)` is real but small: no single additional feature closes the remaining gap exactly, though several adjacent-pair features improve it slightly.

### What This Rules Out

It rules out the idea that the `n=11` failure of the scaffold is due to a completely new kind of feature. The best corrections are still of the same adjacent-pair-count family.

### Surviving Structure

- `CUP-2(n=11)`:
  - fixed scaffold MI: `4.192050`
  - entropy `H(cf_rank) = 4.200340`
  - best one-step corrections are:
    - `weight_pair_22` or equivalently `min_pair_22`: total MI `4.197543`
    - then `weight_pair_00`, `pair_20`, `pair_21`, `weight_pair_11` follow closely
- `Sol3(n=9)`:
  - the same fixed scaffold is already exact; all further gains are zero.
- So the correction space at the first failure point is still tiny and still lives in weighted adjacent-pair features.

### Reformulations

- First-correction view:
  the scaffold failure appears to be a small missing pair-type correction, not a breakdown of the whole formula family.

LOAD-BEARING ASSESSMENT: high. This strongly supports the idea that the slice-rank formula continues to live in a tiny adjacent-pair algebra beyond the exact range.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=11)`:
  - `H = 4.200340`
  - scaffold MI `= 4.192050`
  - best one-step gain:
    - `weight_pair_22` gain `0.005493`
    - `min_pair_22` gain `0.005493`
  - next best:
    - `max_pair_22` gain `0.005391`
    - `weight_pair_00` gain `0.005061`
    - `pair_20`, `pair_21`, `weight_pair_11` close behind
- `Sol3(n=9)`:
  - fixed scaffold MI already equals entropy exactly
  - every tested extra feature has zero gain

STRUCTURAL RESULTS:

- The first correction term beyond the fixed scaffold remains in the same weighted-pair feature family.

TOOLS:

- Reused `slice_feature_search.py` with fixed-scaffold conditioning and one-step residual search.

REPRESENTATIONS:

- “Adjacent-pair correction algebra” representation: the residual formula continues to live in weighted adjacent-pair statistics.

### What Would Unblock This

The next useful step is to test whether adding a single `22`-type correction term extends exactness to `n=11` or at least dramatically improves it across larger `n`.

### Key Parameters

- Families tested: `CUP-2(n=11)`, `Sol3(n=9)`.

### Open Questions

- Is `22` the canonical first correction family beyond `n=10`?
- Is there a small closed basis of pair-type weights that works uniformly for all `n`?

## Synthesis after exploration 21

- The formula search has not blown up.
- Everything still points to a very small weighted adjacent-pair algebra:
  frontier/FutureFc base layer,
  fixed four-feature scaffold,
  then a small `22`-type correction family beyond the exact range.

## Exploration 22

### Strategy

Promote the one-step correction search into a fixed cross-`n` basis test: evaluate whether the extended scaffold

- `interior_sum`
- `weight_pair_01`
- `weight_pair_02`
- `even_val_sum`
- `weight_pair_22`
- `weight_pair_00`

closes the `CUP-2` slice rank across larger `n`.

### Outcome

SUCCEEDED

### Failure Constraint

The six-feature basis is not exact forever either: it is exact through `n=11` and remains very close at `n=12`, so another tiny correction appears there.

### What This Rules Out

It rules out the need for a rapidly growing feature family. The correction space is still very small and remains within the same weighted-pair algebra through the next size.

### Surviving Structure

- Four-feature scaffold:
  - exact through `n=10`
  - near-exact at `n=11`
- Six-feature scaffold (adding `weight_pair_22`, `weight_pair_00`):
  - exact through `n=11`
  - near-exact at `n=12`
- So the correction ladder is extremely shallow:
  - base scaffold,
  - then two more pair-type weights,
  - then only a tiny remaining correction by `n=12`.

### Reformulations

- Finite correction-family view:
  the slice-rank formula seems to grow by adjoining a very small number of extra weighted pair types, not by increasing combinatorial complexity wholesale.

LOAD-BEARING ASSESSMENT: very high. This is the strongest evidence so far that the slice-rank code belongs to a tiny, stable algebra rather than to an expanding feature zoo.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Six-feature scaffold on `CUP-2`:
  - `n=5..11`: exact
  - `n=12`: `H = 4.265504`, `MI = 4.264081` (very close, not exact)
- At `n=11`, adding `weight_pair_22` and `weight_pair_00` exactly closes the gap left by the four-feature scaffold.

STRUCTURAL RESULTS:

- The correction terms remain inside the weighted adjacent-pair family.

TOOLS:

- `info_theory/slice_scaffold_eval.py`
  evaluates fixed feature scaffolds across `n`.

REPRESENTATIONS:

- “Finite weighted-pair correction family” representation: the residual slice code is governed by a tiny nested family of weighted pair-type features.

### What Would Unblock This

The next useful step is to identify the first `n=12` correction term and see whether it is again one more weighted pair statistic or whether a genuinely new class appears.

### Key Parameters

- Family tested: `CUP-2`.
- Exactness:
  - four features through `n=10`
  - six features through `n=11`
  - near-exact at `n=12`

### Open Questions

- What is the first extra term needed at `n=12`?
- Does a small universal weighted-pair basis exist for all `n`?

## Synthesis after exploration 22

- The formula picture keeps strengthening:
  - the residual code is not just low-order,
  - it appears to lie in a tiny nested weighted-pair family across `n`.
- The next move is very clear:
  identify the `n=12` correction term and test whether the same finite family continues.

## Exploration 24

### Strategy

Test the stronger algebraic claim that the small weighted-pair basis determines the slice rank by an affine-linear formula, rather than merely as an informationally complete discrete code.

### Outcome

SUCCEEDED

### Failure Constraint

The slice-rank code is not affine-linear in the small basis. Even on sizes where the basis determines the rank exactly as a discrete key, linear least-squares error remains substantial.

### What This Rules Out

It rules out the simplest closed-form conjecture:

- “slice rank is a linear combination of the weighted-pair statistics.”

So the right formula, if simple, is more likely lexicographic, order-theoretic, or lookup-style on a tiny tuple, not affine.

### Surviving Structure

- `Sol3(n=9)` with its exact-information basis still has poor affine fit:
  - RMSE `5.9248`
  - rounded exact `1382 / 19587`
- `CUP-2(n=5..10)` with the six-feature basis likewise remains far from affine:
  - RMSE grows from about `1.58` at `n=5` to `5.12` at `n=10`
  - rounded exactness remains low
- Therefore the small-basis phenomenon is categorical/informational, not linear-algebraic.

### Reformulations

- Nonlinear small-code view:
  the slice rank is determined by a tiny tuple of weighted-pair features, but the map from that tuple to the rank is nonlinear.

LOAD-BEARING ASSESSMENT: high. This cuts off a tempting but wrong simplification and points directly to the next plausible representation: lexicographic or ordered-tuple ranking on the small basis.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `Sol3(n=9)` affine fit on exact-information basis
  (`interior_sum`, `weight_pair_10`, `weight_pair_12`, `even_val_sum`):
  - `rmse = 5.924793`
  - `mae = 4.387786`
  - `max_abs = 25.733278`
  - rounded exact `1382 / 19587`
- `CUP-2(n=5..10)` affine fit on six-feature basis
  (`interior_sum`, `weight_pair_01`, `weight_pair_02`, `even_val_sum`, `weight_pair_22`, `weight_pair_00`):
  - `n=5`: `rmse = 1.578140`, rounded `21 / 85`
  - `n=6`: `2.396862`, rounded `41 / 293`
  - `n=7`: `3.356266`, rounded `96 / 932`
  - `n=8`: `4.142331`, rounded `270 / 2866`
  - `n=9`: `4.728344`, rounded `834 / 8687`
  - `n=10`: `5.119068`, rounded `2380 / 26171`

TOOLS:

- `info_theory/slice_linear_fit.py`
  Inputs: family, `n` range, and feature list.
  Outputs: affine least-squares fit quality and coefficients for the slice rank.

REPRESENTATIONS:

- “Nonlinear small-code” representation: a tiny deterministic feature tuple with a nonlinear decoding map to slice rank.

### What Would Unblock This

The next useful test is whether the slice rank is a lexicographic or monotone function of the small feature tuple, rather than an affine one.

### Key Parameters

- Families tested: `CUP-2(n=5..10)`, `Sol3(n=9)`.
- Feature bases tested: the exact-information small bases found earlier.

### Open Questions

- Is the decoding map from the small feature tuple to slice rank lexicographic?
- Is there a canonical ordering of the weighted-pair statistics that reproduces the slice rank?

## Synthesis after exploration 24

- The slice code is small but nonlinear.
- That is still good news: it means the remaining problem is about finding the right ordered/combinatorial decoding of a tiny tuple, not about an ever-expanding feature set.

## Exploration 25

### Strategy

Test whether the exact residual feature tuple decodes slice rank lexicographically within each fixed base class, i.e. whether the nonlinear decoding map is simply a lex order on the small extra feature tuple.

### Outcome

FAILED

### Failure Constraint

No permutation/sign choice of the exact residual feature tuple gives a uniform lexicographic ordering of slice rank within all base classes at `n=9`, for either `CUP-2` or `Sol3`.

### What This Rules Out

It rules out the simplest nonlinear decoder:

- “slice rank is a lexicographic function of the small residual feature tuple.”

The residual code is small, but its decoding is more lookup-like than pure lex order.

### Surviving Structure

- The residual tuple remains exact as an information key.
- The failure is specifically about the decoding map, not about the feature basis itself.

### Reformulations

- Small lookup-code view:
  the residual slice rank is determined by a tiny tuple, but the decoder is neither affine nor lexicographic. The natural remaining representation is a small lookup table or decision tree on that tuple.

LOAD-BEARING ASSESSMENT: medium-high. This closes off another tempting oversimplification and narrows the form of any eventual formula.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`: no residual lex order exists for
  `('interior_sum', 'weight_pair_01', 'weight_pair_02', 'even_val_sum')`
  within fixed base classes.
- `Sol3(n=9)`: no residual lex order exists for
  `('interior_sum', 'weight_pair_10', 'weight_pair_12', 'even_val_sum')`
  within fixed base classes.

STRUCTURAL RESULTS:

- Exact small-basis decoding is neither affine-linear nor lexicographic.

### What Would Unblock This

If further formula discovery is desired, the next useful representation is probably:

- a small decision tree,
- or a case split by a few low-order inequalities among the weighted pair counts.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.

### Open Questions

- Is there a tiny decision-tree decoder on the exact feature tuple?
- Are the remaining decoding cases dynamically meaningful?

## Synthesis after exploration 25

- The residual code is now well constrained:
  - tiny feature basis,
  - not affine,
  - not lexicographic.
- That leaves a small combinatorial decoder as the most plausible next formula type.

## Exploration 26

### Strategy

Search for minimal exact feature subsets for the slice-rank code by brute-forcing subsets of the candidate feature bank.

### Outcome

STALLED

### Failure Constraint

The first implementation of `slice_subset_search.py` recomputed the entire bad graph, slice rank, and feature bank for every subset. That made the search dominated by repeated setup rather than by subset testing, and it became computationally impractical even for modest subset sizes.

### What This Rules Out

It rules out naive “recompute everything per subset” exact-subset search as a viable method.

### Surviving Structure

- The target remains valuable:
  minimal exact subsets would be a cleaner statement than the current scaffold-based one.
- The stall is purely computational; the underlying combinatorial question is unchanged.

### Reformulations

- Computational stall classification: this is a **computational** stall. The right rewrite is to cache:
  - bad configs,
  - slice rank values,
  - feature bank values,
  once per `(family, n)`, then scan subsets cheaply.

LOAD-BEARING ASSESSMENT: medium. The stall itself is uninteresting mathematically, but it cleanly identified the implementation bottleneck.

### Concrete Artifacts

TOOLS:

- Initial `slice_subset_search.py` prototype exists but needs refactoring to cache the dataset once per run.

### What Would Unblock This

A cached subset-search implementation.

### Key Parameters

- Targeted cases: `CUP-2(n=9)`, `Sol3(n=9)`, `CUP-2(n=10)`.
- Candidate bank: 15 low-order scalar features.
- Subset sizes: up to 4.

### Open Questions

- Once cached, how small is the minimal exact subset?
- Does the minimal basis size stabilize across `n`?

## Exploration 27 (probe)

### Strategy

Run the cached exact-subset search on the raw low-order feature bank, without conditioning on the known base invariants, to see whether a tiny standalone basis already determines slice rank.

### Outcome

FAILED

### Concrete Artifacts

- `CUP-2(n=9)`: no exact raw feature subset of size `<= 4`
- `Sol3(n=9)`: no exact raw feature subset of size `<= 4`
- `CUP-2(n=10)`: no exact raw feature subset of size `<= 4`

This was a probe on the wrong target: the meaningful exactness question is on
the residual after conditioning on the base invariants, not on the raw feature
bank alone.

## Exploration 28

### Strategy

Run the cached exact-subset search on the correct object: the residual slice code after conditioning on the base invariants, and determine the minimal exact extra basis at successive `CUP-2` sizes.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the scaffold features were merely one arbitrary exact basis among many large ones. The exact residual basis is genuinely tiny:

- size `3` at `n=9`,
- size `4` at `n=10`,
- size `5` at `n=11`.

### Surviving Structure

- `CUP-2(n=9)`: minimal exact extra basis size is `3`.
- `Sol3(n=9)`: minimal exact extra basis size is also `3`.
- `CUP-2(n=10)`: minimal exact extra basis size is `4`.
- `CUP-2(n=11)`: minimal exact extra basis size is `5`.
- The exact subsets are highly non-unique, but they stay inside the same weighted-pair/sum algebra.

### Reformulations

- Minimal residual basis view:
  beyond the base invariants, the slice code seems to need only a slowly growing number of extra low-order statistics.

LOAD-BEARING ASSESSMENT: very high. This upgrades the scaffold story into a true minimal-basis statement and suggests a controlled growth law rather than a combinatorial explosion.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`, minimum exact subset size `3`, with examples:
  - `('interior_sum', 'weight_pair_01', 'weight_pair_02')`
  - `('weight_pair_00', 'weight_pair_10', 'weight_pair_12')`
  - `('weight_pair_01', 'weight_pair_02', 'weight_pair_11')`
- `Sol3(n=9)`, minimum exact subset size `3`, with the same exact subset list as `CUP-2(n=9)`.
- `CUP-2(n=10)`, minimum exact subset size `4`, with examples:
  - `('interior_sum', 'even_val_sum', 'weight_pair_01', 'weight_pair_02')`
  - `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_12')`
  - `('weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
- `CUP-2(n=11)`, minimum exact subset size `5`, with examples:
  - `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
  - `('even_val_sum', 'weight_pair_00', 'weight_pair_11', 'weight_pair_12', 'weight_pair_22')`
  - `('odd_val_sum', 'weight_pair_00', 'weight_pair_11', 'weight_pair_12', 'weight_pair_22')`

STRUCTURAL RESULTS:

- The residual slice code has a tiny exact basis whose size grows slowly with `n`.
- The basis remains inside a stable weighted adjacent-pair algebra.

TOOLS:

- `info_theory/slice_subset_search.py`
  now supports exact subset search with `--with-base`, i.e. after conditioning on the base invariants.

REPRESENTATIONS:

- “Minimal residual basis” representation: exact decoding of the slice rank from the smallest possible extra feature set beyond the base invariants.

### What Would Unblock This

The next useful question is whether the minimal basis size continues to grow by one at each step (`3,4,5,...`) or whether it stabilizes after a small finite generating family.

### Key Parameters

- Families tested:
  - `CUP-2(n=9,10,11)`
  - `Sol3(n=9)`
- Search limit:
  - up to size `4` at `n=9,10`
  - up to size `5` at `n=11`

### Open Questions

- Is the minimal exact basis size at `CUP-2(n=12)` equal to `6`?
- Is there a finite generating family whose prefix of size `n-6` (or similar) is exact at size `n`?

## Synthesis after exploration 28

- The residual slice code is now pinned down much more tightly:
  - exact small basis,
  - basis lives in weighted-pair algebra,
  - basis size grows slowly and predictably across tested `CUP-2` sizes.
- The natural next target is to test the first plausible growth law for basis size and basis family, starting at `n=12`.

## Exploration 30

### Strategy

Test the first continuation of the minimal-basis growth law at `CUP-2(n=12)`: start from the six-feature exact basis for `n=11`, then check whether one or two additional low-order statistics from the same small pool restore exactness.

### Outcome

SUCCEEDED

### Failure Constraint

At `n=12`, neither one additional feature nor any pair from the tested nine-feature pool restores exactness.

### What This Rules Out

It rules out the simplest continuation of the basis-size law:

- “add one more small statistic”,
- or even “add any two more from the same obvious pool.”

So by `n=12`, the next correction is either:

- at least three additional features from the current pool,
- or one genuinely new type of statistic.

### Surviving Structure

- The six-feature scaffold remains very close at `n=12`:
  - `H = 4.265504`
  - `MI = 4.264081`
- No one-step extension from the pool
  `{odd_val_sum, weight_pair_10, weight_pair_11, weight_pair_12, weight_pair_20, weight_pair_21, count_val_0, count_val_1, count_val_2}`
  restores exactness.
- No pairwise extension from that same pool restores exactness either.
- So the residual growth is still small, but no longer trivially shallow.

### Reformulations

- Correction-wall view:
  by `n=12`, the weighted-pair scaffold still dominates, but the next exact correction is no longer visible as a one- or two-step patch from the current natural candidate pool.

LOAD-BEARING ASSESSMENT: high. This is the first concrete point where the nested correction family stops yielding to the most obvious brute-force extension.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=12)`:
  - six-feature scaffold:
    - `H = 4.265504`
    - `MI = 4.264081`
  - adding any one of:
    - `odd_val_sum`
    - `weight_pair_10, weight_pair_11, weight_pair_12, weight_pair_20, weight_pair_21`
    - `count_val_0, count_val_1, count_val_2`
    does not restore exactness
  - adding any pair from that same pool also does not restore exactness

STRUCTURAL RESULTS:

- The exact-decoder basis at `n=12` is outside the immediate one- and two-step extension of the current weighted-pair scaffold.

### What Would Unblock This

Two next-step options remain:

1. search three-step extensions within the current pool;
2. pivot from “exact small basis” back to the more robust invariants:
   forbidden-mode suppression and near-exact low-order coding.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Base scaffold: 6 features.
- Candidate extension pool: 9 simple features.

### Open Questions

- Is the first `n=12` exact correction a 3-feature extension inside the same pool?
- Or is the exact-basis branch becoming less informative than the forbidden-mode branch?

## Exploration 34

### Strategy

Replace the expensive per-subset scan with a compressed exact-subset search on unique full feature signatures, to settle the exact-basis size question at `CUP-2(n=12)`.

### Outcome

FAILED

### Failure Constraint

The first compressed-search implementation stopped building the signature table at the first collision of the full candidate feature bank. That means any later subset result on the truncated table is untrustworthy whenever `full_exact=False`.

### What This Rules Out

It rules out using the current compressed-search output at `n=12` as evidence for exact subset size. The `n=11` result is fine because `full_exact=True`, but the `n=12` result must be discarded until the script is fixed.

### Surviving Structure

- `CUP-2(n=11)` compressed search confirms:
  - full candidate bank exact
  - minimal exact subset size `5`
- `CUP-2(n=12)` compressed search found `full_exact=False`, which is itself useful:
  the current 15-feature candidate bank may already fail to determine the residual slice code exactly.
  But the reported subset size from that run is invalid because of the truncation bug.

### Reformulations

- Exact-subset search remains promising, but only after the compression table is made collision-safe.

LOAD-BEARING ASSESSMENT: medium. This was a real implementation bug, but it also revealed a potentially important mathematical fact: the current feature bank may cease to be exact by `n=12`.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=11)`: `full_exact=True`, minimal exact subset size `5`
- `CUP-2(n=12)`: `full_exact=False` under current 15-feature bank, but subset output invalid because the signature table was truncated after first collision

### What Would Unblock This

Fix the compressed-search script so it:

1. keeps the full signature table,
2. tracks all conflicting full signatures,
3. only reports exact subsets when the compressed data is complete.

### Key Parameters

- Families tested: `CUP-2(n=11)`, `CUP-2(n=12)`.
- Candidate bank: 15 low-order features.

### Open Questions

- After fixing the compression bug, is the full 15-feature bank exact at `n=12` or not?
- If it is not exact, does the residual slice code finally leave the current weighted-pair algebra?

## Exploration 35

### Strategy

Rerun the compressed exact-subset search with the bug fixed, to settle whether the current 15-feature weighted-pair bank is itself exact at `CUP-2(n=12)`.

### Outcome

SUCCEEDED

### Failure Constraint

The current 15-feature bank is **not** exact at `CUP-2(n=12)`: there are genuine full-signature collisions with different slice-rank values. Therefore no subset of that bank can be exact there.

### What This Rules Out

It rules out the hope that the existing weighted-pair / low-order count bank is already a complete residual decoder at `n=12`.

### Surviving Structure

- `CUP-2(n=11)` remains exactly decoded by a 5-feature subset from the current bank.
- `CUP-2(n=12)`:
  - bad configs: `236096`
  - full signatures in the current bank: `235925`
  - full-signature collisions: `120`
  - `full_exact=False`
- Therefore the weighted-pair branch reaches a real boundary at `n=12`: a new type of statistic is needed, or the exact-decoder story stops there.

### Reformulations

- Collision-analysis view:
  the next meaningful exact-basis question is no longer subset size. It is:
  what distinguishes the `120` full-signature collisions at `n=12`?

LOAD-BEARING ASSESSMENT: very high. This cleanly separates the valid exact-decoder regime (`n<=11`) from the first regime where the current feature algebra provably stops being complete.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=12)` compressed search:
  - `bad = 236096`
  - `full_signatures = 235925`
  - `ranks = 52`
  - `full_exact = False`
  - `collisions = 120`
- The earlier “minimum exact subset size = 5” output from the buggy compressed run is invalid and superseded by this result.

STRUCTURAL RESULTS:

- At `n=12`, the current weighted-pair algebra is no longer exact.

### What Would Unblock This

The next useful step is direct collision analysis:

- inspect the colliding pairs,
- identify what state difference is invisible to the current feature bank,
- and test one or two new candidate feature classes tailored to those collisions.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Current candidate bank: 15 low-order scalar features.

### Open Questions

- What is the combinatorial shape of the `120` collisions?
- Do they point to one obvious missing statistic?

## Exploration 36

### Strategy

Test whether the `CUP-2(n=12)` collisions are explained by a simple missing “spread” statistic, namely weighted second or third moments of interior value positions.

### Outcome

FAILED

### Failure Constraint

Adding any one of the obvious moment features

- `sq_val_0, sq_val_1, sq_val_2`
- `cube_val_0, cube_val_1, cube_val_2`

to the six-feature scaffold does **not** restore exactness at `n=12`.

### What This Rules Out

It rules out the most obvious “missing observable” story:

- the `n=12` collisions are not fixed by a single second-moment or third-moment
  statistic of the interior value positions.

### Surviving Structure

- The collisions remain:
  - `sq_val_0`: not exact
  - `sq_val_1`: not exact
  - `sq_val_2`: not exact
  - `cube_val_0`: not exact
  - `cube_val_1`: not exact
  - `cube_val_2`: not exact
- Tuple counts suggest these moments do refine the scaffold to varying degrees,
  but they do not close the decoder.

### Reformulations

- Collision anatomy remains unresolved. The missing statistic is not one of the
  obvious one-dimensional “spread” moments.

LOAD-BEARING ASSESSMENT: medium. This closes one more natural correction branch and supports the conclusion that the exact-decoder path is reaching diminishing returns.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=12)` with six-feature scaffold plus:
  - `sq_val_0`: not exact
  - `sq_val_1`: not exact
  - `sq_val_2`: not exact
  - `cube_val_0`: not exact
  - `cube_val_1`: not exact
  - `cube_val_2`: not exact

### What Would Unblock This

At this point, further exact-decoder exploration likely needs a genuinely new
representation, not another scalar patch.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Base scaffold: six weighted-pair/sum features.
- Candidate correction family: second and third moments of interior value positions.

### Open Questions

- What kind of statistic actually separates the remaining collisions?
- Is the exact-decoder branch still worth pursuing compared to the stronger
  forbidden-interaction theorem targets?

## Synthesis after exploration 36

- I have now run through the natural cheap correction targets for the exact-decoder branch:
  one-step additions, two-step additions, and obvious moment features.
- None of them closes `CUP-2(n=12)`.
- That means the exact-decoder branch has reached a natural exploratory stopping point.
- The only remaining cheap extension class was short motif statistics; that is the next and likely final decoder-side probe.

## Exploration 37

### Strategy

Test the last natural cheap extension class for the exact-decoder branch: single length-3 motif statistics (counts and weighted counts) on top of the six-feature `CUP-2(n=12)` scaffold.

### Outcome

FAILED

### Failure Constraint

No single triple-motif statistic restores exactness at `CUP-2(n=12)`.

### What This Rules Out

It rules out the last obvious local extension class:

- one more pair statistic,
- one more moment statistic,
- or one more triple-motif statistic.

So the `n=12` exact-decoder correction is not a cheap local patch.

### Surviving Structure

- No exact single triple feature exists on top of the six-feature scaffold.
- The strongest refinements among single triple features are:
  - `count_triple_000`
  - `weight_triple_000`
  - then a large block of other triple counts that collapse to the same refinement size.
- This again suggests strong redundancy among the remaining correction directions, but not enough to yield exactness.

### Reformulations

- Decoder-side stopping point:
  the obvious low-order scalar extension program has been exhausted. Any further exact-decoder progress would require either:
  - a qualitatively new representation, or
  - a theorem/proof attack rather than more feature mining.

LOAD-BEARING ASSESSMENT: high. This closes the last remaining cheap target in the exact-decoder branch.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=12)` with six-feature scaffold plus any single triple statistic:
  - no exact completion
  - strongest single refinements:
    - `count_triple_000`
    - `weight_triple_000`
    - then many tied triple-count refinements of lower quality

TOOLS:

- `info_theory/slice_triple_correction_probe.py`
  probes single triple-motif corrections on top of a fixed scaffold.

### What Would Unblock This

At this point, only non-cheap next steps remain:

1. a new representation for the exact decoder, or
2. a direct proof attempt on the theorem targets in `theorem_targets.md`.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Base scaffold: six-feature weighted-pair code.

### Open Questions

- Is there a principled nonlocal correction statistic, or is the exact-decoder branch no longer the right target?
- Can the stronger forbidden-interaction theorem targets be attacked directly now?

## Synthesis after exploration 37

- I have now exhausted the obvious target-discovery branch for the exact decoder:
  - pair statistics,
  - moment statistics,
  - triple-motif statistics,
  all fail as cheap one-step fixes at `n=12`.
- The exploration phase is effectively complete.
- The remaining meaningful work is theorem/proof work on the already packaged targets, especially:
  - forbidden width-`n-2` interaction suppression,
  - two-level `FutureFc + slice-rank` suppression,
  - structural decoding of the small weighted-pair residual code.

## Exploration 38

### Strategy

Resolve the last interpretive ambiguity by proving directly that the scaffold features themselves lie in the width-`n-2` allowed subspace, and confirm it numerically on a witness.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out a whole explanatory branch:

- the scaffold features are not themselves “mysteriously low forbidden-energy.”

Their low forbidden energy is trivial because they are explicit sums of local
window functions.

### Surviving Structure

- Any scalar feature that is a sum of local window terms of width `≤ ℓ` lies in
  the width-`w` model for every `w ≥ ℓ`.
- Therefore:
  - value-count and value-sum features are in the width-1 model,
  - weighted pair features are in the width-2 model,
  - triple-motif features are in the width-3 model.
- In particular, all scaffold features used so far lie exactly in the
  width-`n-2` allowed subspace for theorem-range `n`.
- Numerical spot check on `CUP-2(n=9)` confirms forbidden energy is exactly
  zero up to floating error:
  - `interior_sum`: `0`
  - `weight_pair_01`: `~1e-28`
  - `weight_pair_02`: `~1e-28`
  - `even_val_sum`: `0`

### Reformulations

- Allowed-coordinate theorem:
  the low-order scaffold features are simply coordinates drawn from the allowed
  interaction subspace.

LOAD-BEARING ASSESSMENT: high. This removes one misleading line of thought and sharpens the true theorem target: explain why the convergence rank is almost a function of only a few allowed coordinates.

### Concrete Artifacts

DOCS:

- `info_theory/feature_subspace_theorem.md`
  states and proves the local-feature subspace theorem and its corollaries for the scaffold features.

COMPUTED EXAMPLES:

- `CUP-2(n=9)` numerical spot-check of forbidden energy for scaffold features:
  - `interior_sum`: `0.0`
  - `weight_pair_01`: `1.003e-28`
  - `weight_pair_02`: `1.003e-28`
  - `even_val_sum`: `0.0`

### What Would Unblock This

Nothing exploratory remains on this branch. The remaining work is theorem work:
prove why the bad-side rank is almost a function of a few such allowed coordinates.

### Key Parameters

- Analytical statement is general.
- Numerical spot-check used `CUP-2(n=9)` at width `n-2 = 7`.

### Open Questions

- Can the “few allowed coordinates” compression of the rank be proved directly?
- Is the width-`n-2` forbidden-energy suppression theorem the right first proof target?

## Exploration 39

### Strategy

Shift from the full bad-side rank to the coarse layer `FutureFc`, and search for tiny exact feature bases for `FutureFc` itself.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that all the interesting structure is concentrated in the full rank. The coarse `FutureFc` layer is itself highly compressed and may be the easiest piece to prove first.

### Surviving Structure

- `CUP-2(n=9)`:
  - without prefixes, no exact subset of size `<= 3`
  - with boundary + base invariants, exact subset size drops to `3`
  - examples:
    - `('interior_sum', 'weight_pair_01', 'weight_pair_02')`
    - `('interior_sum', 'weight_pair_10', 'weight_pair_12')`
    - `('count_val_1', 'weight_pair_01', 'weight_pair_02')`
- `Sol3(n=9)`:
  - with boundary + base invariants, exact subset size is only `2`
  - exact example:
    - `('weight_pair_02', 'weight_pair_10')`
- So `FutureFc` is dramatically simpler than the full slice rank and already sits on a tiny weighted-pair basis.

### Reformulations

- Coarse-layer theorem candidate:
  `FutureFc` may admit a much cleaner explicit formula than the full rank, and therefore may be the right first theorem target in the two-level decomposition.

LOAD-BEARING ASSESSMENT: very high. This is the first strong sign that one part of the convergence proof might admit a compact exact information-theoretic formula.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`, with boundary + base invariants:
  - minimum exact subset size `3`
  - multiple exact triples in the weighted-pair algebra
- `Sol3(n=9)`, with boundary + base invariants:
  - minimum exact subset size `2`
  - exact pair `('weight_pair_02', 'weight_pair_10')`

TOOLS:

- `info_theory/futurefc_subset_search.py`
  searches exact feature subsets for `FutureFc`, with optional boundary/base prefixes.

REPRESENTATIONS:

- “Tiny FutureFc code” representation: the coarse convergence layer is itself an exact small weighted-pair code once obvious local prefixes are included.

### What Would Unblock This

The next useful step is to test whether this small exact `FutureFc` basis persists across `CUP-2(n)` and `Sol3(n)`.

### Key Parameters

- Families tested: `CUP-2(n=9)`, `Sol3(n=9)`.
- Prefixes tested:
  - none
  - boundary only
  - boundary + base invariants

### Open Questions

- Is the exact `FutureFc` basis size stable across `n`?
- Can `FutureFc` be proved to be a deterministic function of a tiny weighted-pair tuple?

## Exploration 40

### Strategy

Run a cross-`n` exact-basis sweep for `FutureFc`, using boundary + base invariants as the prefix and searching for the smallest exact extra feature subset.

### Outcome

SUCCEEDED

### Failure Constraint

None on the tested range `n<=10`. The only remaining issue is that the sweep to `n=11,12` requires a larger subset search budget.

### What This Rules Out

It rules out the idea that `FutureFc` needs a large decoder. On the tested sizes it is strikingly simple.

### Surviving Structure

- `CUP-2`:
  - `n=5,6,7`: exact with just `interior_sum`
  - `n=8`: exact with `('interior_sum', 'even_val_sum')`
  - `n=9`: exact with a size-`3` basis; best found
    `('even_val_sum', 'weight_pair_01', 'weight_pair_12')`
  - `n=10`: still exact with size `3`; best found
    `('odd_val_sum', 'weight_pair_01', 'weight_pair_12')`
- `Sol3`:
  - `n=4,5,6,7`: exact with just `interior_sum`
  - `n=8,9`: exact with the pair
    `('weight_pair_02', 'weight_pair_10')`
- So `FutureFc` has a dramatically simpler exact code than the full slice rank.

### Reformulations

- Tiny-`FutureFc` theorem candidate:
  the coarse convergence layer may admit a genuinely explicit, slowly growing exact local code across `n`.

LOAD-BEARING ASSESSMENT: very high. This is now arguably the cleanest and most tractable theorem-facing object in the whole info-theory program.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2` minimum exact extra basis sizes (with boundary + base invariants):
  - `n=5`: `1`
  - `n=6`: `1`
  - `n=7`: `1`
  - `n=8`: `2`
  - `n=9`: `3`
  - `n=10`: `3`
- `Sol3` minimum exact extra basis sizes:
  - `n=4`: `1`
  - `n=5`: `1`
  - `n=6`: `1`
  - `n=7`: `1`
  - `n=8`: `2`
  - `n=9`: `2`

TOOLS:

- `futurefc_subset_search.py` can now be used as the main exact-decoder probe for the coarse layer.

REPRESENTATIONS:

- “Tiny FutureFc code” representation is now supported across a size range, not just at isolated `n`.

### What Would Unblock This

The next useful step is to extend the exact-basis search for `FutureFc` to `CUP-2(n=11,12)` with a larger subset-size budget.

### Key Parameters

- Families tested:
  - `CUP-2(n=5..10)`
  - `Sol3(n=4..9)`

### Open Questions

- Is `FutureFc` exact with basis size `4` or `5` at `CUP-2(n=11,12)`?
- Is there a clean closed-form recurrence for the minimal exact basis size of `FutureFc`?

## Exploration 41

### Strategy

Use the compressed exact-subset search to settle the unresolved `FutureFc` case `CUP-2(n=12)` with subset-size budget `6`.

### Outcome

FAILED

### Failure Constraint

The compressed `FutureFc` search shows that the full 15-feature bank is already non-exact at `CUP-2(n=12)`, with genuine full-signature collisions. Therefore, as in the earlier slice-code case, any subset exactness output from that run is invalid unless the full bank is exact.

### What This Rules Out

It rules out the hope that the current weighted-pair/count bank remains a complete exact decoder for `FutureFc` at `n=12`.

### Surviving Structure

- `CUP-2(n=11)`:
  - `FutureFc` still has an exact basis of size `5`.
- `CUP-2(n=12)`:
  - `bad = 236096`
  - `full_signatures = 235880`
  - `values = 11`
  - `full_exact = False`
  - `collisions = 45`
- So the tiny exact `FutureFc` code also reaches a real boundary at `n=12`.

### Reformulations

- `FutureFc` now mirrors the slice-rank story:
  exact tiny weighted-pair decoding through `n=11`, then genuine collisions at `n=12`.

LOAD-BEARING ASSESSMENT: high. This cleanly marks the boundary of the exact `FutureFc` branch.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=12)` compressed `FutureFc` search:
  - `full_exact = False`
  - `collisions = 45`

### What Would Unblock This

If one wanted to continue this branch, the only meaningful next step would be a direct collision report for `FutureFc(n=12)` to see what the current bank is missing.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Candidate bank: 15 low-order features.

### Open Questions

- What distinguishes the 45 `FutureFc` collisions?
- Do they suggest a cleaner next statistic than the slice-rank collisions did?

## Exploration 42

### Strategy

Test the last natural cheap extension class for the exact `FutureFc(n=12)` decoder: single length-3 motif statistics on top of the best `n=11` exact basis.

### Outcome

STALLED

### Failure Constraint

The single-triple correction probe at `CUP-2(n=12)` hit the same computational boundary as the late slice-decoder searches. This was again a computational stall, not evidence for or against a triple-based correction.

### What This Rules Out

It rules out continuing the exact `FutureFc(n=12)` decoder search by more brute-force scalar patching in interactive mode.

### Surviving Structure

- The unresolved exact-decoder question is now narrow:
  `FutureFc(n=12)` has only `45` full-bank collisions under the current 15-feature pool.
- But the remaining cheap local-patch path is no longer cost-effective.

### Reformulations

- Exact `FutureFc` decoder branch has reached the same natural stopping point as the slice-rank decoder branch:
  one needs either a genuinely new representation or a proof-level argument, not another scalar sweep.

LOAD-BEARING ASSESSMENT: medium. This does not add new math, but it closes the last obvious cheap decoder-extension target.

### What Would Unblock This

Only one of these would justify continuing this branch:

1. a sharply motivated new statistic from collision anatomy,
2. or a proof attempt showing why the current weighted-pair family should fail beyond `n=11`.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Base exact `FutureFc` scaffold from `n=11`.

### Open Questions

- Does `FutureFc(n=12)` fail for a principled reason analogous to the slice-rank failure?
- Is there any reason to expect a tiny exact decoder beyond `n=11` at all?

## Exploration 43

### Strategy

Test the first genuinely new decoder extension class for `FutureFc(n=12)`: non-adjacent pair statistics at lag `2` and `3`, rather than more adjacent-pair / count / moment features.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the pessimistic conclusion that the exact `FutureFc` decoder branch had ended at `n=11`. A tiny nonlocal pair correction restores exactness at `n=12`.

### Surviving Structure

- On top of the best size-5 exact basis for `FutureFc(n=11)`,
  `('even_val_sum', 'weight_pair_00', 'weight_pair_02', 'weight_pair_11', 'weight_pair_22')`,
  the `n=12` collisions are resolved by a **single** nonlocal pair statistic:
  - lag `2`: `count_lag2_11` or `weight_lag2_11`
  - lag `3`: `weight_lag3_11`
- This is the first successful correction beyond the adjacent-pair algebra.
- The missing observable is therefore not a generic higher moment. It is a very specific nonlocal correlation: where the `(1,1)` pattern sits at a larger separation.

### Reformulations

- Nonlocal-pair correction view:
  the exact `FutureFc` decoder appears to extend from the adjacent-pair algebra to a tiny larger algebra including one selected longer-range pair statistic.

LOAD-BEARING ASSESSMENT: extremely high. This is the first genuinely new decoder ingredient discovered beyond the weighted adjacent-pair family, and it reopens the exact `FutureFc` branch.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=12)` with base exact-`n=11` `FutureFc` scaffold
  `('even_val_sum', 'weight_pair_00', 'weight_pair_02', 'weight_pair_11', 'weight_pair_22')`:
  - exact single lag-2 pair features:
    - `count_lag2_11`
    - `weight_lag2_11`
  - exact single lag-3 pair feature:
    - `weight_lag3_11`

TOOLS:

- `info_theory/futurefc_nonlocal_pair_probe.py`
  probes single non-adjacent pair corrections on top of a fixed `FutureFc` scaffold.

REPRESENTATIONS:

- “Tiny nonlocal FutureFc code” representation: exact `FutureFc` decoding via a mostly local weighted-pair basis plus one specific longer-range pair statistic.

### What Would Unblock This

The obvious next step is to test whether the same nonlocal `(1,1)` pair correction persists across larger `n`, or whether `n=12` is a one-off transition.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Base scaffold: best exact `FutureFc` basis from `n=11`.
- Successful corrections:
  - `count_lag2_11`
  - `weight_lag2_11`
  - `weight_lag3_11`

### Open Questions

- Is there a stable family of longer-range `(1,1)` pair corrections for `FutureFc`?
- Does the same correction idea work for the slice-rank residual too?

## Exploration 44

### Strategy

Test whether the new nonlocal `(1,1)` correction for `FutureFc` persists one step further, from `CUP-2(n=12)` to `CUP-2(n=13)`.

### Outcome

STALLED

### Failure Constraint

The bottleneck is no longer the exactness test itself, but building the `FutureFc` / constant-slice data at `n=13`. This crossed the current interactive computational budget before producing a result.

### What This Rules Out

It rules out treating the `n=13` persistence check as a cheap next scan. From this point on, exact-decoder continuation beyond the tested range is a heavier computation, not a lightweight exploratory probe.

### Surviving Structure

- The `n=12` nonlocal correction remains the last confirmed exact-decoder extension:
  on top of the size-5 exact `FutureFc` basis, one of
  - `count_lag2_11`
  - `weight_lag2_11`
  - `weight_lag3_11`
  restores exactness.
- Whether that same correction law persists to `n=13` is currently unresolved.

### Reformulations

- Computational stall classification: this is a **computational** stall. The remaining exact-decoder continuation question is now outside the “cheap exploration” regime.

LOAD-BEARING ASSESSMENT: medium. It does not change the mathematics, but it marks the end of the lightweight extension program.

### What Would Unblock This

Either:

1. a cached/precomputed `FutureFc` and slice data pipeline for larger `n`, or
2. a proof-level argument that predicts the continuation of the nonlocal-pair correction without needing the `n=13` computation.

### Key Parameters

- Family targeted: `CUP-2(n=13)`.
- Candidate exact-decoder continuation:
  size-5 weighted-pair base plus lag-2/lag-3 `(1,1)` correction.

### Open Questions

- Does the nonlocal `(1,1)` correction persist to `n=13` and beyond?
- Is there a theorem predicting exactly when the decoder leaves the adjacent-pair algebra?

## Exploration 45

### Strategy

Test whether the new nonlocal `(1,1)` pair correction that repairs the exact `FutureFc(n=12)` decoder also repairs the full slice-rank decoder at `n=12`.

### Outcome

FAILED

### Failure Constraint

On top of the six-feature slice-rank scaffold at `CUP-2(n=12)`, none of

- `count_lag2_11`
- `weight_lag2_11`
- `weight_lag3_11`

restores exactness.

### What This Rules Out

It rules out the cleanest unification story:

- the first nonlocal `(1,1)` correction that fixes `FutureFc` does **not**
  automatically fix the full slice-rank decoder.

So the coarse and residual layers genuinely diverge at the exact-decoder level.

### Surviving Structure

- `FutureFc(n=12)` has a tiny exact decoder with one nonlocal `(1,1)` correction.
- `slice_rank(n=12)` still does not.
- Therefore the strongest common structure between the two branches remains:
  forbidden-mode suppression and the two-level decomposition,
  not a shared exact decoder.

### Reformulations

- Final branch separation:
  the exact-decoder program for `FutureFc` and the exact-decoder program for the residual slice rank are now genuinely different branches.

LOAD-BEARING ASSESSMENT: high. This is the last clear target-discovery check and it closes the main possible unification route.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=12)` on top of the six-feature slice scaffold:
  - `count_lag2_11`: not exact, tuple count `4349`
  - `weight_lag2_11`: not exact, tuple count `4349`
  - `weight_lag3_11`: not exact, tuple count `8733`

### What Would Unblock This

Nothing cheap remains to try. Any further progress now requires either:

1. a qualitatively new representation, or
2. direct proof work on the packaged theorem targets.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Base scaffold: six-feature slice-rank code.
- Candidate nonlocal corrections:
  `count_lag2_11`, `weight_lag2_11`, `weight_lag3_11`.

### Open Questions

- Is there any exact-decoder relation between the `FutureFc` and slice-rank branches beyond the already known two-level decomposition?
- Or is the exact-decoder branch fully mined out at this point?

## Exploration 46

### Strategy

Extend the exact `FutureFc` basis sweep to larger `Sol3` sizes, to test whether the tiny-code phenomenon is genuinely cross-family and not just a small-`n` accident.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable on the tested size `n=11`.

### What This Rules Out

It rules out the possibility that the exact `FutureFc` code on `Sol3` degrades immediately after `n=9`.

### Surviving Structure

- `Sol3(n=10)`:
  - full 15-feature bank exact
  - minimum exact extra basis size `3`
- `Sol3(n=11)`:
  - full 15-feature bank exact
  - minimum exact extra basis size `5`
  - example exact basis:
    - `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
- So the exact `FutureFc` tiny-code phenomenon persists one full size beyond the previously tested range.

### Reformulations

- Cross-family `FutureFc` code conjecture:
  both `CUP-2` and `Sol3` appear to admit exact tiny `FutureFc` decoders through at least `n=11`, with basis size growing slowly.

LOAD-BEARING ASSESSMENT: very high. This strengthens the case that `FutureFc` is the cleanest and most robust theorem-facing object in the entire info-theory program.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `Sol3(n=10)`:
  - exact `FutureFc` basis size `3`
- `Sol3(n=11)`:
  - exact `FutureFc` basis size `5`
  - full bank exact

### What Would Unblock This

The next natural check would be `Sol3(n=12)`, but that crossed the current interactive compute budget.

### Key Parameters

- Family tested: `Sol3`.
- Sizes tested successfully: `n=10,11`.

### Open Questions

- Does the exact `FutureFc` tiny-code phenomenon continue at `Sol3(n=12)` and beyond?
- Is there a unified growth law for the minimal exact `FutureFc` basis size across witness families?

## Exploration 47

### Strategy

Push the `Sol3` exact `FutureFc` basis sweep one step further to `n=12`.

### Outcome

STALLED

### Failure Constraint

The `Sol3(n=12)` compressed exact-basis search crossed the current interactive compute budget before producing a result.

### What This Rules Out

It rules out treating `Sol3(n=12)` as a cheap continuation check in the current environment.

### Surviving Structure

- The exact `FutureFc` tiny-code phenomenon is confirmed through `Sol3(n=11)`.
- `n=12` remains unresolved only because of scale, not because of a contradictory signal.

### Reformulations

- Computational stall classification: this is a **computational** stall, not a mathematical failure.

LOAD-BEARING ASSESSMENT: medium. This marks the current compute frontier of the strongest surviving exact-code target.

### What Would Unblock This

Either:

1. a cached/coarser exact-basis search pipeline for larger `Sol3`,
2. or a proof-level recurrence for the `FutureFc` code that avoids explicit search.

### Key Parameters

- Family targeted: `Sol3(n=12)`.

### Open Questions

- Does `Sol3(n=12)` continue the tiny-code growth law?

## Synthesis after exploration 47

- There is one theorem-facing branch that still looks unusually clean:
  exact tiny codes for `FutureFc`.
- But the remaining continuation checks are now beyond the lightweight exploration regime.
- At this point, the exploration frontier is exhausted again: what remains is proof or larger-scale computation.

## Exploration 48

### Strategy

Push the exact `FutureFc` continuation branch one last step to `Sol3(n=12)`, including both:

- compressed exact-basis search, and
- lag-2 / lag-3 nonlocal `(1,1)` pair correction probes on the best `n=11` basis.

### Outcome

STALLED

### Failure Constraint

All three `Sol3(n=12)` runs crossed the current interactive compute budget before producing a result. This is a computational stall at the edge of the remaining exact-code branch.

### What This Rules Out

It rules out treating `Sol3(n=12)` as a cheap final continuation check in the current environment.

### Surviving Structure

- The exact tiny-`FutureFc` code is confirmed through:
  - `CUP-2(n=11)`
  - `Sol3(n=11)`
- `CUP-2(n=12)` also remains structurally tractable because a single nonlocal `(1,1)` pair correction repairs the exact decoder.
- `Sol3(n=12)` is now the first genuinely unresolved coarse-layer continuation point, but only because of scale.

### Reformulations

- Computational stall classification: this is a **computational** stall, not a mathematical contradiction.

LOAD-BEARING ASSESSMENT: medium. It does not change the current theorem picture, but it marks the precise compute frontier of the strongest remaining exact-code branch.

### What Would Unblock This

Either:

1. a more aggressively cached/coarsened `FutureFc` continuation pipeline for large `Sol3`, or
2. a proof-level recurrence or structural argument for exact `FutureFc` decoding.

### Key Parameters

- Targeted family: `Sol3(n=12)`.
- Targeted exact-code checks:
  - compressed exact-basis search up to size `6`
  - lag-2 / lag-3 `(1,1)` nonlocal pair corrections

### Open Questions

- Does `Sol3(n=12)` still admit a tiny exact `FutureFc` code?
- If so, does it require the same kind of nonlocal `(1,1)` correction as `CUP-2(n=12)`?

## Exploration 50

### Strategy

Use the newly found nonlocal `(1,1)` corrections to ask the sharpest remaining exact-code question:

- at `CUP-2(n=12)`, does the augmented `FutureFc` feature bank already force the minimal exact basis size to be `6`?

### Outcome

STALLED

### Failure Constraint

The augmented exact-basis search at `CUP-2(n=12)` crossed the current interactive compute budget before resolving whether any exact subset of size `<= 5` exists in the enlarged bank.

### What This Rules Out

It rules out treating the final exact `FutureFc(n=12)` basis-size question as a cheap continuation check.

### Surviving Structure

- We know:
  - the old adjacent-pair/count bank is not exact at `n=12`,
  - adding one nonlocal `(1,1)` pair feature can repair exactness on top of a size-5 basis,
  - but the minimal exact basis size in the augmented bank is still unresolved.
- This is now a scale question, not a target-discovery question.

### Reformulations

- Computational stall classification: the last unresolved exact-basis continuation check is now beyond the lightweight interactive regime.

LOAD-BEARING ASSESSMENT: medium. It marks the final compute frontier of the exact `FutureFc` branch.

### What Would Unblock This

Only heavier computation or a proof-level recurrence for the `FutureFc` decoder.

### Key Parameters

- Family targeted: `CUP-2(n=12)`.
- Candidate bank: weighted-pair/count features plus nonlocal `(1,1)` corrections.

### Open Questions

- Is the minimal exact `FutureFc(n=12)` basis size actually `6`?
- Does the nonlocal correction define a stable new decoder family?

## Exploration 51

### Strategy

Test whether the exact `FutureFc` decoder is not just tiny but **stable by family**: evaluate one hand-picked basis family across multiple `n` on `CUP-2` and `Sol3`.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the exact `FutureFc` basis keeps changing combinatorially with `n`. A stable family basis exists on the tested ranges.

### Surviving Structure

- `CUP-2` stable family basis:
  - `('even_val_sum', 'weight_pair_00', 'weight_pair_02', 'weight_pair_11', 'weight_pair_22')`
  is exact for `n=9,10,11` and fails at `n=12`.
  - adding the single nonlocal correction `count_lag2_11` makes it exact at `n=12`.
- `Sol3` stable family basis:
  - `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
  is exact for `n=9,10,11`.
  - adding `count_lag2_11` changes nothing on the tested range (still exact).
- So the exact `FutureFc` branch has a real family law:
  a 5-feature weighted-pair basis, with a first nonlocal `(1,1)` correction appearing at `CUP-2(n=12)`.

### Reformulations

- Family-basis theorem candidate:
  exact `FutureFc` decoding is not just possible; it is organized by a stable feature family, with a sparse and structured nonlocal correction ladder.

LOAD-BEARING ASSESSMENT: extremely high. This is the strongest new theorem-facing statement found since the forbidden-mode suppression result.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2` with basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_02', 'weight_pair_11', 'weight_pair_22')`:
  - `n=9`: exact
  - `n=10`: exact
  - `n=11`: exact
  - `n=12`: not exact
- `CUP-2` with added `count_lag2_11`:
  - `n=9..12`: exact
- `Sol3` with basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`:
  - `n=9..11`: exact

### What Would Unblock This

The only meaningful continuation now would be:

1. one more scale check beyond the current budget, or
2. a proof attempt of the stable-family `FutureFc` decoder theorem.

### Key Parameters

- Families tested:
  - `CUP-2(n=9..12)`
  - `Sol3(n=9..11)`

### Open Questions

- Does the same nonlocal `(1,1)` correction appear for `Sol3(n=12)`?
- Is there a clean proof of the 5-feature exact `FutureFc` basis and its first correction?

## Exploration 52

### Strategy

Test the last remaining cheap symbolic unification target for the exact `FutureFc` family bases: whether the only visible family difference (`weight_pair_11` vs `weight_pair_01`) is in fact interchangeable under the boundary/base prefixes.

### Outcome

STALLED

### Failure Constraint

The symbolic family-unification check crossed the current interactive compute budget before returning. This was the final remaining lightweight target-discovery branch.

### What This Rules Out

It rules out continuing to spend interactive time on still finer exact-basis family equivalences. At this point the exploration is no longer opening new target classes.

### Surviving Structure

- The family-basis theorem target remains plausible:
  `CUP-2` and `Sol3` each have stable 5-feature exact `FutureFc` bases through `n=11`.
- The exact relationship between those two bases is still unresolved, but resolving it is now a proof/detail question, not a new target class.

### Reformulations

- Final computational stall classification: the remaining unification questions are now finer-detail questions inside already identified theorem targets.

LOAD-BEARING ASSESSMENT: medium. This marks the point where even the last symbolic target-discovery branch no longer justifies interactive exploration.

### What Would Unblock This

Only:

1. deliberate proof work on the family-basis theorem, or
2. a heavier precomputed equivalence search.

### Key Parameters

- Families targeted: `CUP-2`, `Sol3`.
- Sizes targeted: solved exact `FutureFc` cases through `n=11`.

### Open Questions

- Are the two exact `FutureFc` family bases genuinely different, or just two coordinate choices on the same quotient basis?

## Synthesis after exploration 52

- I have now exhausted every remaining distinct exploration target I could identify:
  - invariant discovery,
  - exact-decoder discovery,
  - family-basis continuation,
  - nonlocal correction discovery,
  - symbolic basis-unification.
- What remains is fully theorem/proof work or heavier computation.

## Synthesis after exploration 51

- I found one final strong exploratory result before the frontier closed:
  exact `FutureFc` decoding is governed by stable family bases, not just by ad hoc small subsets.
- At this point, the remaining open questions are continuation-at-scale or proof questions, not new target classes.

## Synthesis after exploration 50

- I have now pushed every remaining exploratory branch to its natural end:
  - exact decoders for slice rank,
  - exact decoders for `FutureFc`,
  - local and nonlocal scalar corrections,
  - cross-family continuation checks.
- The remaining unresolved items are continuation-at-scale questions, not new target classes.
- So the exploration phase is now fully exhausted again.

## Synthesis after exploration 48

- I have now pushed every remaining exploratory branch to the point where the only unresolved items are larger-scale continuation checks.
- No genuinely new light-weight target remains.
- What is left is exactly what the project has already converged to:
  theorem/proof work, or heavier computation beyond the current interactive budget.

## Synthesis after exploration 45

- I have now exhausted the remaining distinct target-discovery moves.
- The last possible cheap unification route failed.
- What remains is no longer exploration. It is proof work on the small set of
  theorem targets already isolated in `theorem_targets.md`.

## Synthesis after exploration 44

- I have now exhausted the lightweight exploratory frontier in a strong sense.
- Every remaining target is either:
  - proof work on the packaged theorem statements, or
  - larger-scale computation beyond the current interactive exploration budget.

## Synthesis after exploration 42

- I have now exhausted the obvious cheap exact-decoder targets for both:
  - the residual slice code,
  - and the coarse `FutureFc` layer.
- The strongest remaining objects are still the theorem targets already isolated earlier.

## Synthesis after exploration 38

- The exploration phase is complete in a strong sense.
- The remaining unresolved questions are no longer target-discovery questions.
- They are proof questions about a small set of explicit candidate statements:
  forbidden-mode suppression, two-level suppression, and the tiny weighted-pair residual code.
- The strongest remaining targets are the theorem-level ones already packaged in
  `theorem_targets.md`, especially forbidden-mode suppression and its two-level decomposition.

## Synthesis after exploration 35

- The exact-basis branch now has a clean stopping point:
  the current weighted-pair/count algebra is complete through `n=11` and fails at `n=12`.
- That creates one final meaningful exploratory target:
  analyze the collision set itself.

## Synthesis after exploration 30

- The exact-basis branch is starting to show diminishing returns:
  it is still structurally informative, but the next exact correction is no longer cheap to identify.
- The stronger, more stable part of the story remains:
  forbidden-mode suppression, two-level decomposition, and near-exact low-order weighted-pair coding.

## Exploration 31

### Strategy

Probe whether the weighted-pair scaffold features themselves already have low forbidden width-`n-2` interaction energy, by running ANOVA forbidden-energy scans on those scalar features directly.

### Outcome

STALLED

### Failure Constraint

The current `feature_forbidden_profile.py` implementation recomputes the full ANOVA decomposition independently for each scalar feature. At `n=9`, this became expensive enough that the runs did not finish promptly in interactive work. This is a computational stall, not a conceptual obstacle.

### What This Rules Out

It rules out naive repeated full-ANOVA scans per feature as a good next computational move.

### Surviving Structure

- The target question remains strong:
  if the scaffold features themselves have low forbidden mass, that would directly explain why small feature tuples decode the slice rank so well.
- But answering it now needs either:
  - cached ANOVA basis machinery,
  - or a direct analytic argument.

### Reformulations

- Computational stall classification: this is a **computational** stall. The right next move is synthesis/theorem-targeting, not more repeated brute-force ANOVA.

LOAD-BEARING ASSESSMENT: medium. The attempt itself did not produce new math, but it identifies the current computational ceiling cleanly.

### Concrete Artifacts

TOOLS:

- `info_theory/feature_forbidden_profile.py` exists as a prototype, but needs ANOVA caching to be practical.

### What Would Unblock This

Either:

1. a cached interaction-basis implementation, or
2. an analytic derivation of the feature spectra from the interaction formulas already found.

### Key Parameters

- Targeted families: `CUP-2(n=9)`, `Sol3(n=9)`.
- Targeted scalar features: weighted-pair and sum features from the slice scaffold.

### Open Questions

- Do the scaffold features themselves already lie mostly in the width-`n-2` allowed subspace?
- Is there a direct interaction-theoretic proof of that fact?

## Exploration 32

### Strategy

Stop opening new computational branches and package the strongest surviving theorem-shaped statements into an explicit target list.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing with diffuse exploratory scans without first naming the actual theorem candidates. The search space is now small enough that packaging matters more than one more low-yield computation.

### Surviving Structure

- The best surviving theorem targets are now explicit:
  - forbidden interaction suppression,
  - two-level suppression via `FutureFc` plus slice rank,
  - tiny weighted-pair slice-code conjectures,
  - invalid-family forbidden-energy gap.
- The strongest negative lessons are also explicit:
  - good-cycle entropy/counting is too weak,
  - cover counting is too weak,
  - width-`n-1` exactness is partly vacuous,
  - the small residual code is neither affine nor lexicographic.

### Reformulations

- Theorem-target register:
  instead of “keep exploring,” the project now has a short list of candidate statements that could plausibly become real proofs or proof ingredients.

LOAD-BEARING ASSESSMENT: high. This marks the point where the exploration stops being a collection of probes and becomes a compact research program.

### Concrete Artifacts

TOOLS / DOCS:

- `info_theory/theorem_targets.md`
  collects the best current theorem-shaped statements, the most likely false directions, and the top next proof targets.

### What Would Unblock This

At this point, genuine progress likely requires proving one of the packaged targets rather than opening more parallel exploratory branches.

### Key Parameters

- No new numeric sweep; this was a synthesis/documentation attempt.

### Open Questions

- Which of the packaged theorem targets is the most tractable first proof?
- Is the forbidden-interaction suppression theorem easier than the explicit slice-code theorem, or vice versa?

## Synthesis after exploration 32

- I am now close to the point of diminishing returns on pure exploration.
- The remaining high-value work is no longer “find another pattern.” It is:
  - prove forbidden-mode suppression,
  - prove the two-level decomposition of that suppression,
  - or decode the residual weighted-pair code structurally.

## Exploration 33

### Strategy

Package the emergent algebra of the residual feature sets: identify the obvious deterministic identities and the recurring empirical substitutions among exact small bases.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the many exact subset lists as unrelated accidents. They are almost certainly different coordinate choices on a much smaller quotient space.

### Surviving Structure

- Deterministic count identities:
  - `count_val_0 + count_val_1 + count_val_2 = n - 4`
  - `interior_sum = count_val_1 + 2*count_val_2`
- Recurrent empirical substitutions in exact bases:
  - `(weight_pair_01, weight_pair_02)` <-> `(weight_pair_10, weight_pair_12)`
  - `weight_pair_00` <-> `weight_pair_11`
  - `even_val_sum` <-> `odd_val_sum` in several higher-`n` bases
- Best current practical scaffold remains:
  - `interior_sum`
  - `weight_pair_01`
  - `weight_pair_02`
  - `even_val_sum`
  - `weight_pair_22`
  - `weight_pair_00`

### Reformulations

- Quotient-basis view:
  the residual slice code does not live on the raw feature zoo. It lives on a small quotient algebra of counts and weighted adjacent-pair directions.

LOAD-BEARING ASSESSMENT: high. This is the cleanest conceptual compression of the exact-basis results.

### Concrete Artifacts

DOCS:

- `info_theory/feature_algebra_notes.md`
  records the deterministic identities, empirical substitutions, and the best current scaffold basis.

### What Would Unblock This

The next real step is no longer another exploratory scan. It is a proof attempt:
either derive the quotient relations analytically or prove one of the packaged theorem targets.

### Key Parameters

- No new numerical sweep; this was a synthesis of previous exact-basis results.

### Open Questions

- What is the canonical quotient basis?
- Which of the empirical substitutions are actual algebraic identities under the base invariants?

## Synthesis after exploration 33

- I have effectively run through the distinct exploratory targets that still looked high-value:
  - good-cycle info objects,
  - cover counts,
  - bad-side rank coding,
  - window hierarchies,
  - null-model calibration,
  - interaction spectra,
  - invalid-family comparisons,
  - two-level decomposition,
  - residual slice-code feature families.
- The remaining work is now theorem/proof work on a small number of explicit candidate statements, not target discovery.

## Exploration 29

### Strategy

Test the first plausible growth-law step at `CUP-2(n=12)`: starting from the six-feature exact basis for `n=11`, check whether a single additional low-order statistic restores exactness.

### Outcome

SUCCEEDED

### Failure Constraint

No single extra statistic from the candidate pool restores exactness at `n=12`.

### What This Rules Out

It rules out the simplest continuation of the basis-size growth law:

- “just add one more weighted pair or count statistic.”

The first `n=12` correction is more than one scalar, or else lies outside the tested small pool.

### Surviving Structure

- Starting from the six-feature scaffold
  `interior_sum, weight_pair_01, weight_pair_02, even_val_sum, weight_pair_22, weight_pair_00`,
  adding any one of
  - `odd_val_sum`
  - `weight_pair_10, weight_pair_11, weight_pair_12, weight_pair_20, weight_pair_21`
  - `count_val_0, count_val_1, count_val_2`
  does **not** yield exactness at `n=12`.
- All these one-step extensions give the same tuple count (`4349`), suggesting a substantial redundancy/equivalence class in the remaining correction directions.

### Reformulations

- Redundant correction-family view:
  the remaining `n=12` correction is not sensitive to which one of these natural scalar summaries you add next; they all collapse to the same coarse refinement.

LOAD-BEARING ASSESSMENT: high. This eliminates the easy one-step correction story and says the next correction is either genuinely two-dimensional or lives outside the current tiny scalar family.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=12)` with base six-feature scaffold:
  - distinct slice-rank values: `52`
  - adding any one candidate from the tested pool:
    - never exact
    - always yields `4349` distinct tuples

### What Would Unblock This

The next useful step is to test pairwise additions among the remaining candidate statistics, which is still small enough to brute-force.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Base scaffold: 6 features.
- One-step candidate pool: 9 features.

### Open Questions

- Does some pair of additional statistics restore exactness at `n=12`?
- Are the one-step candidates all equivalent modulo the six-feature scaffold?

## Exploration 23

### Strategy

Search for the first `n=12` correction term beyond the six-feature scaffold by brute-force mutual-information scans over the remaining feature bank, first broadly and then restricted to weighted pair terms.

### Outcome

STALLED

### Failure Constraint

At `n=12`, exhaustive MI scans over candidate feature extensions become computationally expensive enough that the broad and targeted searches did not return promptly in interactive work. This is a computational stall, not evidence against the small-basis hypothesis.

### What This Rules Out

It rules out using naive full-bank or even moderate-size targeted MI scans as the default method once the bad slice reaches the `n=12` scale.

### Surviving Structure

- The six-feature scaffold is already very close at `n=12`:
  - `H = 4.265504`
  - `MI = 4.264081`
- So the remaining correction is extremely small even before identifying its exact form.

### Reformulations

- Computational stall classification: this is a **computational** stall. The remaining correction appears tiny; brute-force MI search is simply the wrong way to isolate it at larger `n`.

LOAD-BEARING ASSESSMENT: medium. The stall itself is not mathematically interesting, but it says the next step should be more structured than feature-bank scanning.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Six-feature scaffold at `CUP-2(n=12)`:
  - `H(cf_rank) = 4.265504`
  - `MI = 4.264081`
  - near-exact, but not exact

STRUCTURAL RESULTS:

- The correction beyond the six-feature scaffold is small enough that a more algebraic or regression-based approach is preferable to another information-theoretic feature scan.

### What Would Unblock This

A cheaper structured test:

- check whether the slice rank is an affine-linear function of the small weighted-pair basis,
- or fit coefficients directly on the small basis and inspect the residual.

### Key Parameters

- Family tested: `CUP-2(n=12)`.
- Existing scaffold: `interior_sum`, `weight_pair_01`, `weight_pair_02`, `even_val_sum`, `weight_pair_22`, `weight_pair_00`.

### Open Questions

- Is the residual correction at `n=12` affine-linear in the same basis?
- If not, what is the smallest additional nonredundant statistic?

## Exploration 49

### Strategy

Test whether the exact tiny `FutureFc` codes on the solved sizes admit a simple lexicographic decoder on their exact small bases.

### Outcome

FAILED

### Failure Constraint

For every tested exact `FutureFc` basis, no permutation/sign choice yields a uniform lexicographic decoding within all fixed prefix classes.

### What This Rules Out

It rules out the cleanest nonlinear decoder type for `FutureFc`:

- the exact tiny `FutureFc` code is not lexicographic either.

### Surviving Structure

- The exact `FutureFc` code remains tiny on all solved sizes.
- The failure is only about the decoder form, not about the small exact basis.

### Reformulations

- Tiny nonlinear `FutureFc` code view:
  the coarse convergence layer is exactly encoded by a small feature tuple, but the decoding map is more lookup-like than lexicographic.

LOAD-BEARING ASSESSMENT: medium-high. This closes another simplification and sharpens what sort of exact-code theorem might still be true.

### Concrete Artifacts

COMPUTED EXAMPLES:

- No lex decoder found for the exact `FutureFc` bases at:
  - `CUP-2(n=9,10,11)`
  - `Sol3(n=9,10,11)`

### What Would Unblock This

The last natural decoder-type question is whether `FutureFc` admits a tiny exact decision-tree decoder on these bases.

### Key Parameters

- Families tested: `CUP-2`, `Sol3`.
- Sizes tested: solved exact-basis cases through `n=11`.

### Open Questions

- Is the exact `FutureFc` decoder representable by a tiny decision tree?
- Or should the exact-code branch now be considered fully mined out too?

## Exploration 53

### Strategy

Test the last remaining decoder class for the exact `FutureFc` codes on the solved sizes: exact multiway axis-aligned decision trees on the tiny exact bases.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the pessimistic interpretation that, after affine and lexicographic decoders failed, the exact `FutureFc` code would require a large or opaque decoder.

### Surviving Structure

- Exact `FutureFc` codes on the solved sizes admit **shallow** exact decision trees:
  - `CUP-2(n=9)`: max depth `3`
  - `CUP-2(n=10)`: max depth `2`
  - `CUP-2(n=11)`: max depth `3`
  - `Sol3(n=9)`: max depth `2`
  - `Sol3(n=10)`: max depth `2`
  - `Sol3(n=11)`: max depth `3`
- Average depth stays around `0.65` to `1.33` across the tested cases.
- So the exact `FutureFc` code is not:
  - affine,
  - lexicographic,
  but it is still a **tiny shallow tree**.

### Reformulations

- Tiny decision-tree `FutureFc` theorem candidate:
  the coarse convergence layer may admit a uniformly shallow exact decoder on a tiny basis.

LOAD-BEARING ASSESSMENT: extremely high. This is the clearest positive decoder statement found anywhere in the exploration and sharply raises the status of the exact `FutureFc` theorem target.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)` on basis
  `('interior_sum', 'weight_pair_01', 'weight_pair_02')`:
  - max depth `3`
- `CUP-2(n=10)` on basis
  `('odd_val_sum', 'weight_pair_01', 'weight_pair_12')`:
  - max depth `2`
- `CUP-2(n=11)` on basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`:
  - max depth `3`
- `Sol3(n=9)` on basis
  `('weight_pair_02', 'weight_pair_10')`:
  - max depth `2`
- `Sol3(n=10)` on basis
  `('odd_val_sum', 'weight_pair_02', 'weight_pair_10')`:
  - max depth `2`
- `Sol3(n=11)` on basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`:
  - max depth `3`

TOOLS:

- `info_theory/futurefc_decision_tree_probe.py`
  computes the exact minimal depth of a multiway axis-aligned decision tree on the solved exact bases, prefix-by-prefix.

REPRESENTATIONS:

- “Shallow exact `FutureFc` tree” representation: the coarse convergence layer is encoded by a tiny basis with a very small exact decision-tree decoder.

### What Would Unblock This

Nothing exploratory remains in this branch that is comparably cheap and high-value. The next useful step is to prove the tree structure or derive an explicit recursive decoder.

### Key Parameters

- Families tested: `CUP-2`, `Sol3`.
- Sizes tested: exact-basis cases through `n=11`.

### Open Questions

- Is there a proof that the exact `FutureFc` decoder has bounded tree depth?
- Can the tree be made explicit recursively?

## Synthesis after exploration 53

- This is the final genuinely new positive theorem-facing result:
  exact `FutureFc` codes are not just tiny; they are shallow decision trees.
- At this point I have exhausted the target-discovery frontier again.
- What remains is theorem/proof work, not more exploration.

## Exploration 54 (probe)

### Strategy

Check whether the exact `FutureFc` decoder at `CUP-2(n=12)` remains shallow on the repaired nonlocal basis.

### Outcome

FAILED

### Concrete Artifacts

- The probe failed for an implementation reason only:
  `futurefc_decision_tree_probe.py` did not know how to construct the nonlocal
  feature `count_lag2_11`.
- No mathematical conclusion yet; the exact tree-depth target remains live.

## Exploration 55

### Strategy

Measure the exact decision-tree depth of the repaired `FutureFc` decoder at the first nonlocal-corrected size, `CUP-2(n=12)`.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the worry that the first nonlocal correction would destroy the shallow-decoder picture.

### Surviving Structure

- `CUP-2(n=12)` on the exact basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_02', 'weight_pair_11', 'weight_pair_22', 'count_lag2_11')`
  still has a shallow exact decision tree:
  - max depth `4`
  - average depth `1.833`
- So the exact `FutureFc` branch remains not just tiny and exact, but shallow,
  even after the first nonlocal correction enters.

### Reformulations

- Extended shallow-tree `FutureFc` theorem candidate:
  exact `FutureFc` decoding remains a shallow decision tree beyond the purely adjacent-pair regime.

LOAD-BEARING ASSESSMENT: very high. This is the strongest continuation of the exact-code branch so far.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=12)` exact `FutureFc` basis:
  - `even_val_sum`
  - `weight_pair_00`
  - `weight_pair_02`
  - `weight_pair_11`
  - `weight_pair_22`
  - `count_lag2_11`
  gives
  - max tree depth `4`
  - depth distribution `{0: 2206, 1: 2951, 2: 5206, 3: 4661, 4: 88}`

### What Would Unblock This

The next useful target is now parallel:

- check whether the exact slice-rank codes also admit shallow tree decoders,
  or whether shallow trees are special to `FutureFc`.

### Key Parameters

- Family tested: `CUP-2(n=12)`.

### Open Questions

- Are shallow exact trees a `FutureFc`-only phenomenon, or do they extend to the full slice rank when exact bases exist?

## Exploration 56

### Strategy

Test whether the exact slice-rank codes on the solved small bases also admit shallow exact decision-tree decoders.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that shallow exact trees are special to `FutureFc`.

### Surviving Structure

- Exact slice-rank codes on the solved sizes are also shallow trees:
  - `CUP-2(n=9)` on exact basis
    `('interior_sum', 'weight_pair_01', 'weight_pair_02')`:
    - max depth `2`
  - `CUP-2(n=10)` on exact basis
    `('interior_sum', 'even_val_sum', 'weight_pair_01', 'weight_pair_02')`:
    - max depth `3`
  - `Sol3(n=9)` on exact basis
    `('interior_sum', 'weight_pair_10', 'weight_pair_12')`:
    - max depth `3`
- So the residual slice code is not only small; on the solved range it also has a tiny exact tree decoder.

### Reformulations

- Shallow exact-tree slice theorem candidate:
  the exact slice-rank decoders on the solved range are small shallow trees, just like `FutureFc`.

LOAD-BEARING ASSESSMENT: very high. This is the first positive decoder statement for the exact slice-rank branch, not just for `FutureFc`.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`:
  - max depth `2`
  - depth distribution `{0: 2976, 1: 1653, 2: 329}`
- `CUP-2(n=10)`:
  - max depth `3`
  - depth distribution `{0: 5223, 1: 4660, 2: 1396, 3: 30}`
- `Sol3(n=9)`:
  - max depth `3`
  - depth distribution `{0: 6537, 1: 3986, 2: 550, 3: 4}`

TOOLS:

- `info_theory/slice_decision_tree_probe.py`
  computes exact minimal multiway decision-tree depth for solved exact slice-rank bases.

### What Would Unblock This

The next useful check is `CUP-2(n=11)` on its exact 5-feature slice basis. If that also stays shallow, the exact slice-rank tree theorem target becomes much stronger.

### Key Parameters

- Families tested: `CUP-2`, `Sol3`.
- Sizes tested: solved exact slice-basis cases `CUP-2(n=9,10)`, `Sol3(n=9)`.

### Open Questions

- Does the exact slice-rank code stay shallow at `CUP-2(n=11)`?
- Is there a family-basis theorem for shallow exact slice trees too?

## Exploration 57 (probe)

### Strategy

Probe `Sol3(n=10,11)` with the exact `FutureFc` bases in the slice-rank tree checker.

### Outcome

FAILED

### Concrete Artifacts

- The probe failed immediately for the expected mathematical reason:
  the chosen `Sol3(n=10,11)` bases were exact for `FutureFc`, not for slice rank.
- So there is no new information here beyond clarifying that the exact slice-rank
  tree target should currently stay restricted to the known exact slice bases.

## Exploration 58

### Strategy

Push the exact slice-rank tree probe one step further on the actually known exact branch: `CUP-2(n=11)` with its exact 5-feature slice basis.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the worry that shallow exact slice trees were only a small-`n`
artifact of the `CUP-2(n=9,10)` cases.

### Surviving Structure

- `CUP-2(n=11)` exact slice basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
  also has a shallow exact decision tree:
  - max depth `3`
  - average depth `0.966`
- So on the solved `CUP-2` exact slice branch, shallow trees persist through
  `n=11`.

### Reformulations

- Shallow exact-tree slice theorem candidate becomes materially stronger:
  it is no longer just a small-`n` fact.

LOAD-BEARING ASSESSMENT: high. This is the cleanest continuation of the exact slice-rank decoder story.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=11)`:
  - exact basis
    `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
  - depth distribution `{0: 8118, 1: 8862, 2: 6245, 3: 531}`
  - max depth `3`

### What Would Unblock This

The remaining open question on the slice side is not tree depth anymore. It is:
does `Sol3` also admit exact small slice bases beyond `n=9`?

### Key Parameters

- Family tested: `CUP-2(n=11)`.

### Open Questions

- Do exact small slice bases exist for `Sol3(n=10,11)`?
- If so, are they also shallow?

## Exploration 59

### Strategy

Run the compressed exact-subset search on the previously unexplored `Sol3(n=10,11)` slice-rank branch.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the earlier implicit assumption that the exact small slice-code phenomenon might stop at `Sol3(n=9)`.

### Surviving Structure

- `Sol3(n=10)`:
  - full 15-feature bank exact
  - minimum exact slice basis size `4`
  - exact example:
    - `('interior_sum', 'even_val_sum', 'weight_pair_01', 'weight_pair_02')`
- `Sol3(n=11)`:
  - full 15-feature bank exact
  - minimum exact slice basis size `5`
  - exact example:
    - `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
- So the exact small slice-code phenomenon is now cross-family through `n=11`, not just on `CUP-2`.

### Reformulations

- Cross-family exact slice-code theorem candidate:
  both witness families admit exact tiny slice decoders through the same range where the exact `FutureFc` codes were already known.

LOAD-BEARING ASSESSMENT: extremely high. This is the strongest reopening of the slice-rank branch since the exact-basis story first appeared.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `Sol3(n=10)`:
  - `full_exact = True`
  - minimum exact subset size `4`
- `Sol3(n=11)`:
  - `full_exact = True`
  - minimum exact subset size `5`

### What Would Unblock This

The next natural check is whether these new exact `Sol3` slice bases are also shallow decision trees.

### Key Parameters

- Family tested: `Sol3`.
- Sizes tested: `n=10,11`.

### Open Questions

- Are the new exact `Sol3` slice bases also shallow trees?
- Does the slice branch now mirror the `FutureFc` branch more closely than previously thought?

## Exploration 60

### Strategy

Test whether the newly discovered exact `Sol3` slice bases admit shallow exact decision-tree decoders.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that shallow exact trees on the slice side were peculiar
to the `CUP-2` family.

### Surviving Structure

- `Sol3(n=10)` exact slice basis
  `('interior_sum', 'even_val_sum', 'weight_pair_01', 'weight_pair_02')`
  has:
  - max depth `3`
  - average depth `0.630`
- `Sol3(n=11)` exact slice basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
  has:
  - max depth `4`
  - average depth `0.970`
- So both witness families now exhibit:
  - exact tiny `FutureFc` codes with shallow trees,
  - exact tiny slice-rank codes with shallow trees,
  through the currently solved range.

### Reformulations

- Cross-family shallow exact-tree theorem candidate:
  both the coarse and residual convergence codes appear to admit shallow exact decision-tree decoders on small feature bases through the solved range.

LOAD-BEARING ASSESSMENT: extremely high. This is the strongest endpoint summary of the decoder side of the exploration.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `Sol3(n=10)`:
  - depth distribution `{0: 12092, 1: 10792, 2: 2446, 3: 120}`
  - max depth `3`
- `Sol3(n=11)`:
  - depth distribution `{0: 19663, 1: 17070, 2: 15537, 3: 1237, 4: 16}`
  - max depth `4`

### What Would Unblock This

At this point, only larger-scale continuation checks or proofs remain.

### Key Parameters

- Family tested: `Sol3`.
- Sizes tested: `n=10,11`.

### Open Questions

- Do these shallow-tree exact decoders continue beyond the current solved range?
- Can one prove a uniform depth bound?

## Exploration 61

### Strategy

Test the strongest remaining family-unification target on the slice side: whether a single common feature basis gives exact slice-rank decoding across both witness families through the solved range.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the lingering idea that the exact slice bases were family-specific accidents. A single common basis already works on both families through `n=11`.

### Surviving Structure

- The common 5-feature basis
  - `even_val_sum`
  - `weight_pair_00`
  - `weight_pair_01`
  - `weight_pair_02`
  - `weight_pair_22`
  is exact for:
  - `CUP-2(n=9,10,11)`
  - `Sol3(n=9,10,11)`
- Adding `weight_pair_11` (common 6-feature basis) changes nothing on this solved range.
- This is a major unification: the exact slice-rank decoder has the same family basis on both witness families through the currently solved range.

### Reformulations

- Common exact slice-basis theorem candidate:
  the residual slice code is not merely tiny; it is organized by one common weighted-pair basis across witness families.

LOAD-BEARING ASSESSMENT: extremely high. This is the strongest remaining family-unification result and probably the last major theorem-facing structure available from pure exploration.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Common 5-feature basis exact for all tested:
  - `CUP-2(n=9,10,11)`
  - `Sol3(n=9,10,11)`
- Common 6-feature basis exact as well, but unnecessary on the solved range.

### What Would Unblock This

Only larger-scale continuation checks remain:
  does the same common 5-feature basis continue at `n=12` and beyond?

### Key Parameters

- Families tested: `CUP-2`, `Sol3`.
- Sizes tested: `n=9,10,11`.

### Open Questions

- Does the common 5-feature exact slice basis persist at the next size?
- Is there a proof that this common basis works on all valid witnesses in these families?

## Exploration 62

### Strategy

Push the common 5-feature family-basis theorem one step further, from the solved range `n<=11` to the first unresolved size `CUP-2(n=12)`, on both:

- the exact slice-rank branch,
- and the exact `FutureFc` branch.

### Outcome

SUCCEEDED

### Failure Constraint

The common 5-feature family basis does **not** remain exact at `CUP-2(n=12)`.

### What This Rules Out

It rules out the strongest family-basis continuation claim:

- the common 5-feature basis is not a uniform all-`n` exact decoder, even for `CUP-2`.

### Surviving Structure

- The common 5-feature basis remains exact through the solved cross-family range:
  - `CUP-2(n=9,10,11)`
  - `Sol3(n=9,10,11)`
- At `CUP-2(n=12)`:
  - slice branch: common 5-feature basis not exact
  - slice branch: common 6-feature basis with added `weight_pair_11` still not exact
  - `FutureFc` branch: common 5-feature basis not exact
  - `FutureFc` branch: even adding the `count_lag2_11` nonlocal correction to the common 5-feature basis does not restore exactness
- So the common family basis is a solved-range phenomenon, not yet a continuation law.

### Reformulations

- Solved-range family basis theorem:
  the common 5-feature basis is the right unifying object through the solved range, but continuation beyond that range requires family-specific corrections.

LOAD-BEARING ASSESSMENT: high. This closes the strongest remaining family-basis continuation target.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Common 5-feature basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
  is exact on:
  - `CUP-2(n=9,10,11)`
  - `Sol3(n=9,10,11)`
  but not on `CUP-2(n=12)`.

### What Would Unblock This

Nothing exploratory remains here except larger-scale continuation checks.

### Key Parameters

- Families checked:
  - `CUP-2`
  - `Sol3`
- Sizes:
  - solved range `n=9..11`
  - first unresolved continuation point `CUP-2(n=12)`

### Open Questions

- What is the cleanest family-specific correction to the common basis at `n=12`?
- Is there a better common basis than the current 5-feature one?

## Synthesis after exploration 62

- The common-family basis target is now exhausted:
  it works exactly through the solved range and fails at the first unresolved size.
- At this point every remaining question is either a proof question or a larger continuation computation.

## Synthesis after exploration 61

- This is the last genuinely new family-level target-discovery result:
  a common exact slice basis across both witness families through the solved range.
- At this point, every remaining question is either:
  - a continuation-at-scale check like `n=12+`, or
  - a proof question.
- So the exploration frontier is now fully exhausted once again.

## Synthesis after exploration 60

- The decoder side of the project is now as structurally mature as it is likely
  to become under exploration:
  - tiny exact bases,
  - stable family bases,
  - shallow exact tree decoders,
  on both the coarse `FutureFc` layer and the solved slice-rank layer.
- What remains is not target discovery. It is:
  - proof of these decoder theorems,
  - proof of forbidden-mode suppression,
  - or heavier continuation computations beyond the current budget.

## Exploration 63

### Strategy

Strengthen the common-family `FutureFc` basis result by testing whether the same common 5-feature basis also has uniformly shallow exact decision-tree decoders across the solved range.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the possibility that the common-family `FutureFc` basis is exact but combinatorially complicated. It is exact and shallow.

### Surviving Structure

- The common 5-feature `FutureFc` basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
  has shallow exact trees on the solved cross-family range:
  - `CUP-2(n=9)`: max depth `3`
  - `CUP-2(n=10)`: max depth `3`
  - `CUP-2(n=11)`: max depth `3`
  - `Sol3(n=9)`: max depth `2`
- So the strongest exact `FutureFc` theorem target can now be stated in a clean common-family form.

### Reformulations

- Common shallow-tree `FutureFc` theorem candidate:
  on the solved range, one common 5-feature basis exactly decodes `FutureFc`
  with uniformly shallow decision trees across both witness families.

LOAD-BEARING ASSESSMENT: extremely high. This is the cleanest family-level exact decoder theorem found in the whole exploration.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`: depth distribution `{0: 1293, 1: 1250, 2: 296, 3: 33}`, max `3`
- `CUP-2(n=10)`: `{0: 1596, 1: 2337, 2: 1148, 3: 239}`, max `3`
- `CUP-2(n=11)`: `{0: 1874, 1: 3307, 2: 3099, 3: 928}`, max `3`
- `Sol3(n=9)`: `{0: 2781, 1: 3004, 2: 671}`, max `2`

### What Would Unblock This

The only remaining analogous target is whether the common exact slice basis also has a shallow family-level tree law on the solved range.

### Key Parameters

- Families tested: `CUP-2`, `Sol3`.
- Sizes tested: solved cross-family range `n=9..11` where the common basis is exact.

### Open Questions

- Does the common exact slice basis also have a shallow family-level tree law?

## Synthesis after exploration 63

- There was one last genuinely new family-level strengthening available:
  the common exact `FutureFc` basis is also a shallow-tree decoder.
- Beyond this, the remaining questions are continuation-at-scale or proof questions, not new target classes.

## Exploration 66

### Strategy

Extract actual common-basis `FutureFc` trees on the solved cross-family range, to see whether the decoder shape itself stabilizes and matches the common slice-tree shape.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the common exact `FutureFc` basis is exact and shallow but structurally unrelated to the common slice basis.

### Surviving Structure

- The common exact `FutureFc` trees show the same top-level organization as the common exact slice trees:
  - roots are dominated by `weight_pair_01` and `even_val_sum`
  - `weight_pair_00` appears mainly as a second-level splitter
- Representative examples:
  - `CUP-2(n=9)`: simple groups split directly on `weight_pair_01`
  - `CUP-2(n=10)`: mixed groups split on `even_val_sum`, then `weight_pair_00` or `weight_pair_01`
  - `Sol3(n=9,10)`: same pattern
- So the common exact decoder story for the coarse and residual branches is now strikingly aligned:
  same family basis, shallow trees, and same dominant root features.

### Reformulations

- Common dominant-root theorem candidate:
  both the exact `FutureFc` and exact slice decoders are organized around the same small pair of dominant root observables, `even_val_sum` and `weight_pair_01`.

LOAD-BEARING ASSESSMENT: high. This is the last genuinely new decoder-shape regularity available from exploration.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)` common `FutureFc` basis:
  - simple groups split on `weight_pair_01`
- `CUP-2(n=10)` common `FutureFc` basis:
  - groups split first on `even_val_sum`, then on `weight_pair_00` or `weight_pair_01`
- `Sol3(n=9)` common `FutureFc` basis:
  - same one-step `weight_pair_01` pattern in simple groups
- `Sol3(n=10)` common `FutureFc` basis:
  - same `even_val_sum` then `weight_pair_00` / `weight_pair_01` pattern

### What Would Unblock This

Nothing exploratory remains here that is still target discovery rather than proof or scale continuation.

### Key Parameters

- Families tested: `CUP-2`, `Sol3`.
- Sizes tested: solved common-basis `FutureFc` range.

### Open Questions

- Can one prove the dominance of `even_val_sum` and `weight_pair_01` in the common exact decoder trees?

## Synthesis after exploration 66

- I have now extracted the last decoder-shape regularity that still looked accessible:
  both the coarse and residual common exact decoders are built around the same two leading features.
- At this point there is genuinely no distinct target-discovery work left.
- What remains is theorem/proof work or larger continuation computation.

## Exploration 64

### Strategy

Strengthen the common exact slice-basis result by testing whether that same common 5-feature basis also has uniformly shallow exact decision-tree decoders across the solved cross-family range.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the possibility that the common exact slice basis is exact but combinatorially large. It is exact and shallow on the solved range.

### Surviving Structure

- Common exact slice basis
  `('even_val_sum', 'weight_pair_00', 'weight_pair_01', 'weight_pair_02', 'weight_pair_22')`
  has shallow exact trees on the solved cross-family range:
  - `CUP-2(n=9)`: max depth `2`
  - `CUP-2(n=10)`: max depth `3`
  - `Sol3(n=10)`: max depth `3`
  - `Sol3(n=11)`: max depth `4`
- So both the `FutureFc` and solved slice-rank branches now admit:
  - common exact family bases,
  - shallow exact tree decoders.

### Reformulations

- Common shallow-tree slice theorem candidate:
  the residual slice code is not just exactly decodable on a common basis through the solved range; that decoder is shallow as well.

LOAD-BEARING ASSESSMENT: extremely high. This is the last major family-level decoder strengthening available from pure exploration.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`:
  - depth distribution `{0: 2976, 1: 1496, 2: 486}`
  - max depth `2`
- `CUP-2(n=10)`:
  - `{0: 5223, 1: 4200, 2: 1841, 3: 45}`
  - max depth `3`
- `Sol3(n=10)`:
  - `{0: 12092, 1: 8702, 2: 4547, 3: 109}`
  - max depth `3`
- `Sol3(n=11)`:
  - `{0: 19663, 1: 17070, 2: 15537, 3: 1237, 4: 16}`
  - max depth `4`

### What Would Unblock This

Only larger continuation checks or proofs remain. There is no new cheap target class after this.

### Key Parameters

- Families tested: `CUP-2`, `Sol3`.
- Sizes tested: solved common-basis range.

### Open Questions

- Do these common shallow-tree slice decoders continue at the next unresolved sizes?
- Can they be proved uniformly?

## Exploration 65

### Strategy

Extract the root-split distribution of the common exact slice-basis trees across the solved cross-family range, to see whether the decoder shape itself stabilizes.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the exact common slice trees are shallow but structurally chaotic. Their root logic is highly concentrated.

### Surviving Structure

- Across all tested solved-range cases, the common exact slice trees split mostly on just two features:
  - `even_val_sum`
  - `weight_pair_01`
- Root-split counts:
  - `CUP-2(n=9)`: dominated by `weight_pair_01` then `even_val_sum`
  - `CUP-2(n=10)`: dominated by `even_val_sum` then `weight_pair_01`
  - `CUP-2(n=11)`: dominated by `even_val_sum` then `weight_pair_01`
  - `Sol3(n=9)`: dominated by `weight_pair_01`
  - `Sol3(n=10)`: dominated by `even_val_sum` then `weight_pair_01`
  - `Sol3(n=11)`: dominated by `even_val_sum` and `weight_pair_01` almost equally
- The remaining features appear mainly as lower-frequency tie-breakers.

### Reformulations

- Dominant-root common-tree view:
  the common exact slice decoder is not only shallow; it is organized around a very small pair of root-level observables.

LOAD-BEARING ASSESSMENT: high. This is the last family-level decoder-shape regularity available from cheap exploration.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)` root splits:
  - `weight_pair_01: 718`
  - `even_val_sum: 392`
- `CUP-2(n=10)`:
  - `even_val_sum: 1794`
  - `weight_pair_01: 1269`
- `CUP-2(n=11)`:
  - `even_val_sum: 3717`
  - `weight_pair_01: 2358`
- `Sol3(n=9)`:
  - `weight_pair_01: 1640`
  - `even_val_sum: 900`
- `Sol3(n=10)`:
  - `even_val_sum: 3674`
  - `weight_pair_01: 3091`
- `Sol3(n=11)`:
  - `even_val_sum: 6406`
  - `weight_pair_01: 6458`

### What Would Unblock This

Nothing exploratory remains here. The next useful step is to prove why these two features dominate the common exact slice decoder.

### Key Parameters

- Families tested: `CUP-2`, `Sol3`.
- Sizes tested: solved common-basis range `n=9..11`.

### Open Questions

- Can the common exact slice tree be proved to recurse primarily on `even_val_sum` and `weight_pair_01`?

## Synthesis after exploration 65

- There is no meaningful target-discovery work left.
- I have now extracted:
  - invariants,
  - exact decoders,
  - common family bases,
  - shallow tree decoders,
  - and dominant root-level decoder features.
- The remaining work is fully in the domain of proof or larger-scale computation.

## Synthesis after exploration 64

- The decoder side is now as complete as exploration is likely to make it:
  - common exact family bases,
  - shallow exact trees,
  for both `FutureFc` and the solved slice-rank branch.
- No distinct target-discovery branch remains.

## Exploration 67

### Strategy

Stop mining the decoder branch for more patterns and package the strongest
`FutureFc` object into an actual theorem note: clean definitions, exact theorem
statements, a real proved lemma, and a precise statement of the remaining proof
obstruction.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing to describe the `FutureFc` branch only as a pile of
empirical decoder facts. The branch is now precise enough to be stated as a
formal theorem package, with the remaining gap isolated sharply.

### Surviving Structure

- The strongest exact `FutureFc` statements now package cleanly into two forms:
  - common solved-range exact code on
    `even_val_sum, weight_pair_00, weight_pair_01, weight_pair_02, weight_pair_22`,
  - family-stable exact code with first nonlocal correction:
    - `CUP-2`: `even_val_sum, weight_pair_00, weight_pair_02, weight_pair_11, weight_pair_22`,
      repaired at `n=12` by one of
      `count_lag2_11`, `weight_lag2_11`, `weight_lag3_11`;
    - `Sol3`: `even_val_sum, weight_pair_00, weight_pair_01, weight_pair_02, weight_pair_22`.
- The first nonlocal repair terms are still width-`n-2` allowed coordinates:
  - lag-2 pair features are width-3 local,
  - lag-3 pair features are width-4 local.
- A generic decoder lemma also survives:
  any exact finite code on `k` coordinates admits an exact multiway
  axis-aligned tree of depth `<= k`.
- Fresh reruns confirmed the exactness and depth data on the packaged bases:
  - `CUP-2(n=9,10,11)` family basis exact, max depth `3`,
  - `CUP-2(n=12)` repaired basis exact, max depth `4`,
  - `Sol3(n=9,10,11)` family basis exact, max depths `2,2,3`.

### Reformulations

- Exact frontier-code package:
  `FutureFc` is best treated as an exact prefix code on a tiny tuple of
  width-`n-2` coordinates, with a shallow tree decoder and a separately
  isolated fiber-collision proof obligation.

LOAD-BEARING ASSESSMENT: high. This is the first formulation that cleanly
separates:

- proved structural lemmas,
- finite exact theorems already certified by exhaustion,
- and the exact symbolic step still missing for the two-level theorem.

### Concrete Artifacts

DOCS:

- `info_theory/futurefc_theorem_package.md`
  packages the exact code theorem, shallow decoder theorem, analytic lemmas,
  and the remaining obstruction.
- `info_theory/feature_subspace_theorem.md`
  now includes the lagged-pair corollary covering
  `count_lag2_11`, `weight_lag2_11`, and `weight_lag3_11`.

COMPUTED EXAMPLES:

- Reconfirmed exact family-basis code:
  - `CUP-2(n=9,10,11)` exact on
    `even_val_sum, weight_pair_00, weight_pair_02, weight_pair_11, weight_pair_22`
  - `CUP-2(n=12)` non-exact on that 5-feature basis, exact after adding
    `count_lag2_11`
  - `Sol3(n=9,10,11)` exact on
    `even_val_sum, weight_pair_00, weight_pair_01, weight_pair_02, weight_pair_22`
- Reconfirmed common solved-range exact code:
  common basis
  `even_val_sum, weight_pair_00, weight_pair_01, weight_pair_02, weight_pair_22`
  is exact on both families for `n=9,10,11`.
- Reconfirmed shallow tree depths:
  - `CUP-2(n=9)`: `3`
  - `CUP-2(n=10)`: `3`
  - `CUP-2(n=11)`: `3`
  - `CUP-2(n=12)` repaired basis: `4`
  - `Sol3(n=9)`: `2`
  - `Sol3(n=10)`: `2`
  - `Sol3(n=11)`: `3`

STRUCTURAL RESULTS:

- The first nonlocal `FutureFc` correction is nonlocal only relative to the
  adjacent-pair algebra, not relative to the width-`n-2` allowed subspace.
- The remaining symbolic bottleneck is now exact:
  prove collision-freeness of the tiny feature fibers, not existence of a small
  coordinate system.

TOOLS:

- Reused:
  - `futurefc_basis_family_probe.py`
  - `futurefc_decision_tree_probe.py`
  - `futurefc_tree_extract.py`
  - `twolevel_spectrum.py`

REPRESENTATIONS:

- “Exact prefix-code with shallow decoder” representation for `FutureFc`.

### What Would Unblock This

To move from a computational theorem package to a symbolic theorem, the next
missing ingredient is one proof of

`(boundary6, tp, tiny feature tuple) same  =>  FutureFc same`.

The smallest useful form would be a recursive or monotone description of
`FutureFc` on prefix groups that explains why the tree splits are forced.

### Key Parameters

- Families rechecked:
  - `CUP-2(n=9..12)`
  - `Sol3(n=9..11)`
- Exact-code bases rechecked:
  - common 5-feature solved-range basis,
  - `CUP-2` family 5-feature basis,
  - `CUP-2` repaired 6-feature basis at `n=12`,
  - `Sol3` family 5-feature basis.

### Open Questions

- Can the exact `FutureFc` fibers be proved collision-free symbolically from
  the witness dynamics?
- Can the shallow tree splits be derived recursively rather than searched?
- Which of the two exact forms is the right theorem statement to lead with:
  common solved-range basis, or family-stable basis with first nonlocal
  correction?

## Synthesis after exploration 67

- The `FutureFc` branch has now crossed from exploration into proof packaging.
- There is at least one real proved lemma in hand:
  lagged repair features remain width-`n-2` allowed coordinates.
- The exact remaining obstruction is no longer vague:
  it is the symbolic proof of collision-freeness for the tiny `FutureFc` code.

## Exploration 68

### Strategy

Tighten the exact `FutureFc` theorem by attacking the prefix side rather than
the feature side: test whether the full proof107 prefix
`(boundary6, exp2, int21, exp2_weight)` is actually minimal for the coarse
layer, and probe which TP coordinates genuinely survive in the exact code.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out treating the full proof107 TP triple as the default exact prefix
for `FutureFc`. On the solved range, that prefix contains redundant coordinates
for the coarse layer.

### Surviving Structure

- `Sol3` solved-range coarse code collapses to the reduced prefix
  `boundary6 + exp2_weight`:
  on `n=9,10,11`, together with the stable basis
  `even_val_sum, weight_pair_00, weight_pair_01, weight_pair_02, weight_pair_22`,
  this reduced prefix determines exactly:
  - `exp2`,
  - `int21`,
  - `fc`,
  - `FutureFc - fc`,
  - `FutureFc`.
- `CUP-2` coarse code collapses almost as far:
  the reduced prefix
  `boundary6 + exp2_weight + int21`
  together with the stable basis
  `even_val_sum, weight_pair_00, weight_pair_02, weight_pair_11, weight_pair_22`
  determines exactly:
  - `exp2`,
  - `fc`,
  - `FutureFc - fc`,
  - `FutureFc`
  on `n=9,10,11`,
  and the same remains true at `n=12` after adjoining `count_lag2_11`.
- The `FutureFc` gap is itself a much smaller object than the raw potential:
  - `CUP-2(n=9,10,11)` on the exact family basis takes only `6` values,
  - `CUP-2(n=12)` repaired basis takes `7`,
  - `Sol3(n=9,10,11)` takes only `3`.

### Reformulations

- Reduced-prefix frontier-code view:
  the right theorem-facing object for the coarse layer is not
  `(boundary6, exp2, int21, exp2_weight) + tiny basis`,
  but rather:
  - `boundary6 + exp2_weight + tiny basis` on `Sol3`,
  - `boundary6 + exp2_weight + int21 + tiny basis` on `CUP-2`.

LOAD-BEARING ASSESSMENT: high. This removes one whole coordinate from the
coarse `CUP-2` prefix and two from the coarse `Sol3` prefix, and identifies
`exp2_weight` as the single TP scalar that survives uniformly on the solved
coarse branch.

### Concrete Artifacts

TOOLS:

- `info_theory/futurefc_fiber_probe.py`
  probes exactness of derived quantities on exact `FutureFc` fibers under
  customizable prefix choices.

COMPUTED EXAMPLES:

- `Sol3(n=9,10,11)` with prefix `boundary6 + exp2_weight` and basis
  `even_val_sum, weight_pair_00, weight_pair_01, weight_pair_02, weight_pair_22`:
  exact for `FutureFc`, `fc`, `gap`, `exp2`, and `int21`.
- `CUP-2(n=9,10,11)` with prefix
  `boundary6 + exp2_weight + int21` and basis
  `even_val_sum, weight_pair_00, weight_pair_02, weight_pair_11, weight_pair_22`:
  exact for `FutureFc`, `fc`, `gap`, and `exp2`.
- `CUP-2(n=12)` with repaired basis
  `even_val_sum, weight_pair_00, weight_pair_02, weight_pair_11, weight_pair_22, count_lag2_11`
  and the same reduced prefix:
  exact for `FutureFc`, `fc`, `gap`, and `exp2`.
- Near-minimality witness:
  `CUP-2(n=11)` with only `boundary6 + exp2_weight` leaves exactly `6`
  collisions for the gap; adding `int21` repairs them all.

STRUCTURAL RESULTS:

- On the coarse branch, `exp2_weight` is the dominant TP coordinate.
- The omitted TP coordinates are often not lost but recovered from the reduced
  prefix plus the tiny feature tuple.

REPRESENTATIONS:

- “Reduced-prefix exact `FutureFc` code” representation.

### What Would Unblock This

The next symbolic step is now sharper than before:

1. prove why `exp2_weight` is the TP coordinate that survives in the coarse
   exact code,
2. explain why `int21` is needed on the `CUP-2` branch but drops out on
   `Sol3`,
3. and derive collision-freeness for the reduced-prefix fibers directly.

### Key Parameters

- Families tested:
  - `Sol3(n=9,10,11)`
  - `CUP-2(n=9,10,11,12)`
- Prefixes tested:
  - full proof107 prefix,
  - boundary only,
  - base only,
  - boundary plus individual TP scalars,
  - reduced prefixes centered on `exp2_weight`.

### Open Questions

- Why does `exp2_weight` dominate the coarse layer while `exp2` drops out?
- Is there a direct dynamic meaning of the gap values
  `0..5` on solved `CUP-2` and `0..2` on solved `Sol3`?
- Can the reduced-prefix theorem be proved analytically from the hop dynamics?

## Synthesis after exploration 68

- The exact `FutureFc` theorem has sharpened in a nontrivial way:
  the feature basis stayed the same, but the prefix side compressed.
- The symbolic bottleneck is now better isolated:
  not “why does the full proof107 prefix work?” but
  “why do only `exp2_weight` and sometimes `int21` survive in the coarse exact
  code?”

## Exploration 69

### Strategy

Test whether the new reduced-prefix exact `FutureFc` code can be explained by
explicit affine formulas, and in parallel check whether the omitted TP
coordinates are actually recoverable from the reduced prefix plus the tiny
feature basis.

### Outcome

SUCCEEDED

### Failure Constraint

The reduced-prefix exact code is not affine-linear. Least-squares fits for the
recovered TP scalars and for `FutureFc` itself retain substantial residuals even
on fibers where exact recovery holds.

### What This Rules Out

It rules out the easiest symbolic explanation of the reduced-prefix theorem:

- “the dropped TP scalars are given by linear formulas in the reduced prefix
  and the tiny feature tuple.”

So the remaining proof must be combinatorial, piecewise, or tree-like.

### Surviving Structure

- The reduced-prefix theorem is stronger than mere target recovery:
  on the solved range, the omitted TP coordinates are themselves exact
  functions of the reduced prefix plus the tiny basis.
- `Sol3(n=9,10,11)`:
  `boundary6 + exp2_weight + B_sol`
  determines exactly:
  - `exp2`,
  - `int21`,
  - `fc`,
  - `FutureFc - fc`,
  - `FutureFc`.
- `CUP-2(n=9,10,11)`:
  `boundary6 + exp2_weight + int21 + B_cup`
  determines exactly:
  - `exp2`,
  - `fc`,
  - `FutureFc - fc`,
  - `FutureFc`.
- `CUP-2(n=12)` with repaired basis
  `B_cup^+ = B_cup + count_lag2_11`
  still determines exactly:
  - `exp2`,
  - `fc`,
  - `FutureFc - fc`,
  - `FutureFc`
  from the same reduced prefix.
- But affine probes fail on representative cases:
  - `Sol3(n=11)`, target `int21` from
    `boundary6 + exp2_weight + B_sol`: nonzero RMSE, not exact,
  - `Sol3(n=11)`, target `FutureFc` from the same data: nonzero RMSE,
  - `CUP-2(n=11)`, target `exp2` from
    `boundary6 + exp2_weight + int21 + B_cup`: nonzero RMSE.

### Reformulations

- Recovered-prefix view:
  the reduced coarse prefix is not just sufficient for `FutureFc`; it already
  contains the data needed to reconstruct the omitted TP scalars once coupled to
  the tiny basis. The collapse is exact but nonlinear.

LOAD-BEARING ASSESSMENT: medium-high. This removes linear algebra from the live
search space and points directly toward shallow-tree / case-split proofs for
the reduced-prefix theorem.

### Concrete Artifacts

TOOLS:

- `info_theory/futurefc_linear_probe.py`
  tests affine recoverability of coarse targets from custom prefixes.

COMPUTED EXAMPLES:

- `Sol3(n=11)`:
  - `boundary6 + exp2_weight + B_sol` exact for `exp2`, `int21`, `fc`, `gap`,
    `FutureFc`
  - but affine fit for `int21` on that data has nonzero residual
  - and affine fit for `FutureFc` also has nonzero residual.
- `CUP-2(n=11)`:
  - `boundary6 + exp2_weight + int21 + B_cup` exact for `exp2`, `fc`, `gap`,
    `FutureFc`
  - but affine fit for `exp2` has nonzero residual.

STRUCTURAL RESULTS:

- The reduced-prefix theorem is a genuine coordinate compression, not an
  affine-linear identity.
- The omitted TP scalars are recoverable on solved fibers, so the reduced
  prefix is effectively equivalent to the full TP prefix on the coarse branch.

REPRESENTATIONS:

- “Recovered reduced prefix” representation:
  the coarse code uses a smaller prefix that already reconstructs the rest of
  the TP data nonlinearly.

### What Would Unblock This

The next useful step is to extract exact shallow decision trees for:

1. `exp2` from the reduced `CUP-2` prefix,
2. `int21` from the reduced `Sol3` prefix,
3. and `FutureFc - fc` from the reduced prefixes.

That would turn the new nonlinear obstruction into a positive piecewise
combinatorial theorem.

### Key Parameters

- Families tested:
  - `Sol3(n=9,10,11)`
  - `CUP-2(n=9,10,11,12)`
- Targets tested:
  - `FutureFc`,
  - `fc`,
  - `FutureFc - fc`,
  - dropped TP scalars `exp2`, `int21`.

### Open Questions

- Are the recovered TP scalars shallow trees on the reduced prefix?
- Can the reduced-prefix theorem be factored into
  1. recovery of the omitted TP data,
  2. then the old exact `FutureFc` code?
- Is there a direct combinatorial meaning of the small gap values that explains
  why `exp2_weight` is the surviving TP scalar?

## Synthesis after exploration 69

- The reduced-prefix theorem survived a serious simplification attempt.
- The right next proof form is no longer linear algebra.
- The strongest live route is now:
  recover the omitted TP scalars by shallow trees on the reduced prefix, then
  fold that into the exact `FutureFc` code theorem.

## Exploration 70

### Strategy

Replace the failed affine explanation with the next plausible positive form:
test whether the reduced-prefix recovery maps for the dropped TP scalars and for
the coarse gap are shallow exact decision trees on the tiny `FutureFc` bases.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the worry that the reduced-prefix theorem is exact but highly
opaque after affine recovery fails. The recovery maps are still small:
they are shallow trees.

### Surviving Structure

- `CUP-2(n=11)`:
  from prefix `boundary6 + exp2_weight + int21` and basis `B_cup`,
  the dropped scalar `exp2` has an exact tree of max depth `1`.
- `Sol3(n=11)`:
  from prefix `boundary6 + exp2_weight` and basis `B_sol`,
  the dropped scalar `int21` has an exact tree of max depth `3`.
- `Sol3(n=11)`:
  the coarse gap `FutureFc - fc` on the same reduced prefix and basis has max
  depth `4`.
- `CUP-2(n=12)`:
  on the repaired basis `B_cup^+`, the coarse gap `FutureFc - fc` has max depth
  `3` from the reduced prefix `boundary6 + exp2_weight + int21`.

### Reformulations

- Shallow reduced-prefix recovery view:
  the reduced-prefix theorem can plausibly be factored into:
  1. shallow recovery of omitted TP data or of the coarse gap,
  2. then shallow decoding of `FutureFc` itself.

LOAD-BEARING ASSESSMENT: high. This is the first positive theorem-shaped
structure after the affine route failed, and it gives a concrete symbolic proof
target: derive the recovery trees recursively.

### Concrete Artifacts

TOOLS:

- `info_theory/futurefc_target_tree_probe.py`
  computes exact minimal tree depth for custom coarse targets under custom
  prefixes.

COMPUTED EXAMPLES:

- `CUP-2(n=11)`, target `exp2`:
  depth distribution `{0: 8348, 1: 430}`, max depth `1`.
- `Sol3(n=11)`, target `int21`:
  depth distribution `{0: 875, 1: 2187, 2: 3321, 3: 1944}`, max depth `3`.
- `Sol3(n=11)`, target `gap`:
  depth distribution `{0: 7609, 1: 325, 2: 309, 3: 83, 4: 1}`, max depth `4`.
- `CUP-2(n=12)`, target `gap` on repaired basis:
  depth distribution `{0: 6194, 1: 2840, 2: 3490, 3: 1330}`, max depth `3`.

STRUCTURAL RESULTS:

- The reduced-prefix recovery maps are exact and shallow.
- So the nonlinear reduced-prefix theorem is not merely lookup-table exact; it
  already has a small decision-tree representation.

REPRESENTATIONS:

- “Reduced-prefix recovery tree” representation.

### What Would Unblock This

The next useful step is to complete the same tree-depth sweep across the full
solved range:

1. `CUP-2(n=9,10,11,12)` for `exp2` and `gap`,
2. `Sol3(n=9,10,11)` for `int21` and `gap`.

If those stay uniformly shallow, the right next theorem note is a reduced-prefix
recovery-tree theorem.

### Key Parameters

- Families tested:
  - `CUP-2(n=11,12)`
  - `Sol3(n=11)`
- Targets tested:
  - dropped TP scalars `exp2`, `int21`,
  - coarse gap `FutureFc-fc`.

### Open Questions

- Do the reduced-prefix recovery trees stay uniformly shallow across the whole
  solved range?
- Is the depth-1 recovery of `exp2` on `CUP-2` actually an explicit closed
  case split?
- Can the exact `FutureFc` theorem be factorized through a shallow theorem for
  the coarse gap first?

## Synthesis after exploration 70

- The reduced-prefix branch is now much more concrete:
  exact,
  non-affine,
  and shallow-tree recoverable.
- The next theorem target is no longer vague:
  prove a reduced-prefix recovery-tree theorem, then compose it with the exact
  `FutureFc` decoder theorem.

## Exploration 71

### Strategy

Complete the reduced-prefix recovery-tree sweep across the full solved range to
see whether the shallow-tree phenomenon is uniform enough to be stated as a
theorem rather than as a few representative examples.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the worry that the shallow recovery trees were just `n=11` or
`n=12` accidents. The same small-depth behavior persists across the whole
currently solved reduced-prefix range.

### Surviving Structure

- `CUP-2` reduced-prefix recovery of `exp2` from
  `boundary6 + exp2_weight + int21 + B_cup`:
  - `n=9`: depth `0`
  - `n=10`: depth `1`
  - `n=11`: depth `1`
- `CUP-2` reduced-prefix recovery of `gap = FutureFc - fc`:
  - `n=9`: depth `2`
  - `n=10`: depth `3`
  - `n=11`: depth `3`
  - `n=12` on repaired basis `B_cup^+`: depth `3`
- `Sol3` reduced-prefix recovery of `int21` from
  `boundary6 + exp2_weight + B_sol`:
  - `n=9`: depth `2`
  - `n=10`: depth `3`
  - `n=11`: depth `3`
- `Sol3` reduced-prefix recovery of `gap = FutureFc - fc`:
  - `n=9`: depth `3`
  - `n=10`: depth `3`
  - `n=11`: depth `4`

### Reformulations

- Uniform reduced-prefix recovery-tree law:
  across the solved range, the dropped TP data and the coarse gap are governed
  by uniformly shallow exact trees on the reduced prefixes.

LOAD-BEARING ASSESSMENT: high. This upgrades the reduced-prefix branch from a
collection of isolated exactness facts into a coherent theorem package with
uniform small decoder depth.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=9)`, target `exp2`:
  depth distribution `{0: 2872}`, max depth `0`.
- `CUP-2(n=10)`, target `exp2`:
  `{0: 5178, 1: 71}`, max depth `1`.
- `CUP-2(n=9)`, target `gap`:
  `{0: 2228, 1: 498, 2: 146}`, max depth `2`.
- `CUP-2(n=10)`, target `gap`:
  `{0: 3416, 1: 1163, 2: 622, 3: 48}`, max depth `3`.
- `CUP-2(n=11)`, target `gap`:
  `{0: 4639, 1: 2081, 2: 1796, 3: 262}`, max depth `3`.
- `CUP-2(n=12)`, target `gap` on repaired basis:
  `{0: 6194, 1: 2840, 2: 3490, 3: 1330}`, max depth `3`.
- `Sol3(n=9)`, target `int21`:
  `{0: 1037, 1: 2021, 2: 567}`, max depth `2`.
- `Sol3(n=10)`, target `int21`:
  `{0: 879, 1: 2428, 2: 1861, 3: 486}`, max depth `3`.
- `Sol3(n=9)`, target `gap`:
  `{0: 3365, 1: 169, 2: 90, 3: 1}`, max depth `3`.
- `Sol3(n=10)`, target `gap`:
  `{0: 5198, 1: 280, 2: 165, 3: 11}`, max depth `3`.
- `Sol3(n=11)`, target `gap`:
  `{0: 7609, 1: 325, 2: 309, 3: 83, 4: 1}`, max depth `4`.

TOOLS:

- Reused `futurefc_target_tree_probe.py` for the full solved-range sweep.

STRUCTURAL RESULTS:

- The reduced-prefix recovery trees remain uniformly shallow on the solved
  exact branch.
- The repaired `CUP-2(n=12)` case fits the same shallow recovery-tree picture.

REPRESENTATIONS:

- “Solved-range reduced-prefix recovery-tree theorem” representation.

### What Would Unblock This

The next useful step is now theorem packaging rather than more probing:

1. add a reduced-prefix recovery-tree theorem to the `FutureFc` package,
2. decide whether the best composition statement is
   `recovery tree + shallow FutureFc tree`,
   or `recovery tree + exact fiber theorem`.

### Key Parameters

- Families tested:
  - `CUP-2(n=9,10,11,12)`
  - `Sol3(n=9,10,11)`
- Targets tested:
  - recovered TP scalars `exp2`, `int21`,
  - coarse gap `FutureFc-fc`.

### Open Questions

- Can the recovery trees themselves be derived analytically from boundary hop
  rules?
- Is the coarse gap the cleanest first symbolic theorem, even before `FutureFc`
  itself?
- Can the `CUP-2` and `Sol3` reduced-prefix trees be unified at the level of
  dominant split features?

## Synthesis after exploration 71

- The reduced-prefix branch is now theorem-shaped in its own right:
  exact,
  non-affine,
  and uniformly shallow-tree recoverable on the solved range.
- The natural next move is to promote this into the formal `FutureFc` theorem
  package and use it as the intermediate layer before the full exact `FutureFc`
  decoder theorem.

## Exploration 72

### Strategy

Inspect the internal shape of the reduced-prefix recovery trees rather than only
their depths: extract root-split frequencies to see whether the new shallow
recovery theorems are driven by a small, stable set of observables.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the reduced-prefix recovery trees are shallow but
structurally chaotic. Their root logic is concentrated.

### Surviving Structure

- `CUP-2(n=11)`, target `exp2` on reduced prefix:
  root splits are dominated by
  - `even_val_sum: 358`
  - `weight_pair_02: 36`
  - `weight_pair_22: 36`
- `Sol3(n=11)`, target `int21` on reduced prefix:
  root splits are dominated by
  - `even_val_sum: 5832`
  - `weight_pair_02: 1377`
  - `weight_pair_01: 243`
- `Sol3(n=11)`, target `gap` on reduced prefix:
  root splits are dominated by
  - `even_val_sum: 254`
  - `weight_pair_01: 201`
  - `weight_pair_00: 140`
  - `weight_pair_02: 123`
- `CUP-2(n=12)`, repaired gap on reduced prefix:
  root splits are dominated by
  - `even_val_sum: 3866`
  - `weight_pair_11: 2282`
  - `weight_pair_02: 960`
  - `weight_pair_00: 337`
  - `count_lag2_11: 182`

### Reformulations

- Dominant-root reduced-prefix recovery view:
  the shallow recovery trees are organized around the same small set of
  observables that already dominated the exact `FutureFc` and slice decoders,
  especially `even_val_sum`.

LOAD-BEARING ASSESSMENT: medium-high. This does not prove the reduced-prefix
theorem, but it sharply narrows the branching structure any symbolic proof must
explain.

### Concrete Artifacts

TOOLS:

- `futurefc_target_tree_probe.py` now reports root-split frequencies with
  `--root-counts`.

COMPUTED EXAMPLES:

- `CUP-2(n=11)`, target `exp2`:
  root split counts
  `{even_val_sum: 358, weight_pair_02: 36, weight_pair_22: 36}`.
- `Sol3(n=11)`, target `int21`:
  `{even_val_sum: 5832, weight_pair_02: 1377, weight_pair_01: 243}`.
- `Sol3(n=11)`, target `gap`:
  `{even_val_sum: 254, weight_pair_01: 201, weight_pair_00: 140, weight_pair_02: 123}`.
- `CUP-2(n=12)`, target `gap` on repaired basis:
  `{even_val_sum: 3866, weight_pair_11: 2282, weight_pair_02: 960,
    weight_pair_00: 337, count_lag2_11: 182, weight_pair_22: 33}`.

STRUCTURAL RESULTS:

- `even_val_sum` is the dominant root observable on the reduced-prefix branch.
- The first nonlocal repair feature enters the repaired gap recovery tree, but
  only after the main local observables.

REPRESENTATIONS:

- “Dominant-root reduced-prefix tree” representation.

### What Would Unblock This

The next natural proof attempt is to explain why `even_val_sum` is the first
coarse branching coordinate on the reduced-prefix branch, and why the first
nonlocal correction only appears as a lower-frequency splitter.

### Key Parameters

- Families inspected:
  - `CUP-2(n=11,12)`
  - `Sol3(n=11)`
- Targets inspected:
  - recovered TP scalars `exp2`, `int21`,
  - coarse gap `FutureFc-fc`.

### Open Questions

- Is there a direct parity / weighted-balance meaning of `even_val_sum` on the
  coarse branch?
- Can the gap recovery tree be proved to branch first on `even_val_sum`?
- Why does `weight_pair_11` become prominent on repaired `CUP-2(n=12)` while
  `Sol3` stays centered on `weight_pair_01`?

## Synthesis after exploration 72

- The reduced-prefix recovery-tree theorem now has a visible internal shape.
- The same kind of feature concentration that appeared in the old exact decoder
  trees reappears here, with `even_val_sum` again at the center.
- The next useful move is to promote the reduced-prefix recovery-tree theorem
  into the formal `FutureFc` package and state the dominant-root heuristic as
  the current analytic clue.

## Exploration 73

### Strategy

Push past depth statistics and inspect the actual reduced-prefix fibers, with
the specific goal of seeing whether `CUP-2` recovery of `exp2` is governed by a
small family of explicit `even_val_sum` patterns, and whether a detour through
total interior `2`-mass simplifies the theorem.

### Outcome

SUCCEEDED

### Failure Constraint

Detouring through `count_val_2` does not simplify the problem enough. Although
`count_val_2` is exact on the reduced prefixes, its recovery trees are not
simpler than the current `exp2` / `int21` targets, so it is not presently the
cleanest intermediate theorem.

### What This Rules Out

It rules out the current best simplification attempt:

- “prove `count_val_2` first, then deduce `exp2`.”

That route may still be possible, but it is not cleaner at the decoder level.

### Surviving Structure

- `CUP-2(n=11)` reduced-prefix recovery of `exp2` is highly concentrated:
  - there are only `430` nontrivial reduced-prefix groups,
  - `358` are resolved by `even_val_sum` alone,
  - and only `10` normalized `even_val_sum -> exp2` patterns occur.
- Representative repeated patterns for `CUP-2(n=11)`:
  - `(even_val_sum = 4,5) -> exp2 = 2`, `(6) -> 1`
  - `(3,4,5,6) -> 2`, `(7) -> 1`
  - `(6,7) -> 3`, `(8) -> 2`
- The exceptional groups where `even_val_sum` alone does not resolve `exp2`
  are sparse relative to the total and are consistent with the previously seen
  secondary splitters `weight_pair_02`, `weight_pair_22`.
- Total interior `2`-mass is itself exact on the reduced prefixes:
  - `CUP-2(n=11)`:
    `boundary6 + exp2_weight + int21 + B_cup` determines `count_val_2`
    exactly,
  - `Sol3(n=11)`:
    `boundary6 + exp2_weight + B_sol` determines `count_val_2` exactly.
- But `count_val_2` is not decoder-simpler:
  - `CUP-2(n=11)`: max depth `2`, roots dominated by `weight_pair_22`,
  - `Sol3(n=11)`: max depth `4`, roots dominated by `weight_pair_22`.

### Reformulations

- Even-sum pattern view:
  on the `CUP-2` reduced-prefix branch, `exp2` is almost an explicit
  one-parameter theorem in `even_val_sum`, with only a small exceptional family
  requiring a second weighted-pair coordinate.

LOAD-BEARING ASSESSMENT: medium-high. This is the first near-explicit symbolic
shape for one of the reduced-prefix recovery targets.

### Concrete Artifacts

COMPUTED EXAMPLES:

- `CUP-2(n=11)` nontrivial reduced-prefix `exp2` groups:
  - total nontrivial groups: `430`
  - resolved by `even_val_sum` alone: `358`
  - unresolved by `even_val_sum` alone: `72`
  - unique normalized `even_val_sum -> exp2` patterns: `10`
- Sample repeated patterns:
  - count `72`:
    `even_val_sum 5,6 -> exp2 2`, `7 -> 1`
  - count `71`:
    `4,5 -> 2`, `6 -> 1`
  - count `48`:
    `6,7 -> 3`, `8 -> 2`
- `count_val_2` exactness:
  - `CUP-2(n=11)`: exact on reduced prefix, max tree depth `2`,
    root splits `{weight_pair_22: 4248, even_val_sum: 1079, weight_pair_02: 792}`
  - `Sol3(n=11)`: exact on reduced prefix, max tree depth `4`,
    root splits `{weight_pair_22: 5022, even_val_sum: 729, weight_pair_02: 243}`

TOOLS:

- Reused:
  - `futurefc_fiber_probe.py`
  - `futurefc_target_tree_probe.py`

STRUCTURAL RESULTS:

- `even_val_sum` is not merely a frequent root splitter; on `CUP-2(n=11)` it
  resolves most nontrivial `exp2` fibers by itself.
- The `count_val_2` detour is exact but not simpler.

REPRESENTATIONS:

- “Near-explicit even-sum recovery” representation for `CUP-2` `exp2`.

### What Would Unblock This

The next useful step is to classify the `72` exceptional `CUP-2(n=11)` groups
where `even_val_sum` alone fails, and see whether one secondary coordinate
(`weight_pair_02` or `weight_pair_22`) handles all of them uniformly.

### Key Parameters

- Families inspected:
  - `CUP-2(n=11)`
  - `Sol3(n=11)`
- Targets inspected:
  - `exp2`,
  - `count_val_2`.

### Open Questions

- Do the `72` exceptional `CUP-2(n=11)` groups all obey one secondary-split
  rule?
- Does the same even-sum pattern classification hold at `CUP-2(n=10,12)`?
- Can one derive the repeated `even_val_sum -> exp2` patterns directly from
  weighted endpoint balance?

## Synthesis after exploration 73

- The reduced-prefix branch now has its first almost-explicit symbolic shape.
- For `CUP-2`, the `exp2` recovery problem is close to a one-coordinate theorem
  with a small exceptional family.
- The best next symbolic move is to isolate that exceptional family and see
  whether one secondary pair-weight coordinate resolves it uniformly.

## Exploration 74

### Strategy

Classify the exceptional reduced-prefix groups for `CUP-2` `exp2` recovery
after the primary split on `even_val_sum`, and test whether one secondary
coordinate resolves them uniformly. Compare that behavior to `Sol3` `int21` and
to repaired `CUP-2(n=12)`.

### Outcome

SUCCEEDED

### Failure Constraint

The strongest two-stage rule currently appears to be family-specific. The clean
post-`even_val_sum` single-secondary collapse works on the solved local
`CUP-2` branch, but not on `Sol3` `int21` recovery and not in any equally clean
form at repaired `CUP-2(n=12)`.

### What This Rules Out

It rules out the strongest naive unification:

- “after splitting on `even_val_sum`, one universal second feature resolves all
  reduced-prefix recovery problems across families and sizes.”

That is too optimistic.

### Surviving Structure

- `CUP-2(n=10)`, target `exp2`:
  after the primary split on `even_val_sum`, there are no exceptional groups at
  all.
- `CUP-2(n=11)`, target `exp2`:
  - exceptional groups after `even_val_sum`: `72`,
  - all `72` are resolved by `weight_pair_02`,
  - all `72` are also resolved by `weight_pair_22`,
  - there are only `2` normalized exceptional patterns:
    - count `48`: `even_val_sum = 8` gives labels `{2,3}`
    - count `24`: `even_val_sum = 8` gives labels `{1,2}`
- So on the solved local `CUP-2` branch the recovery theorem has a near-explicit
  two-stage form:
  1. split on `even_val_sum`,
  2. on the small exceptional family, split on either `weight_pair_02` or
     `weight_pair_22`.
- `Sol3(n=11)`, target `int21`:
  after splitting on `even_val_sum`, the `6237` exceptional groups do **not**
  collapse under any single secondary coordinate. Some are resolved by
  `weight_pair_00`, some by `weight_pair_01`, some by `weight_pair_02`, and a
  large block is resolved by none of them singly.
- `CUP-2(n=12)`, target `exp2` on the repaired basis:
  the same clean local two-stage collapse does not persist in a single-feature
  form. The exceptional families break into a richer menu involving
  `weight_pair_11`, `weight_pair_02`, `weight_pair_22`, and occasionally
  `count_lag2_11`.

### Reformulations

- Two-stage `CUP-2` recovery view:
  for the solved local `CUP-2` branch, `exp2` recovery is now almost explicit:
  a primary `even_val_sum` split plus one secondary pair-weight on a tiny
  exceptional family.

LOAD-BEARING ASSESSMENT: high. This is the strongest current symbolic foothold:
it turns one reduced-prefix recovery theorem into a concrete near-formula.

### Concrete Artifacts

TOOLS:

- `info_theory/futurefc_exception_probe.py`
  analyzes exceptional groups after a chosen primary split and tests candidate
  secondary resolvers.

COMPUTED EXAMPLES:

- `CUP-2(n=11)`, target `exp2`, primary `even_val_sum`:
  - exceptional groups: `72`
  - resolver set on every exceptional group:
    `('weight_pair_02', 'weight_pair_22')`
  - normalized exceptional patterns:
    - count `48` with examples
      `((0,0,2,2,0,0),14,0)`, `((0,0,2,2,0,1),14,0)`, ...
      and ambiguity pattern `even_val_sum = 8 -> {2,3}`
    - count `24` with examples
      `((0,0,2,2,2,0),6,0)`, `((0,0,2,2,2,1),6,0)`, ...
      and ambiguity pattern `even_val_sum = 8 -> {1,2}`
- `CUP-2(n=10)`, target `exp2`, primary `even_val_sum`:
  exceptional groups `0`.
- `Sol3(n=11)`, target `int21`, primary `even_val_sum`:
  exceptional groups `6237`; no single secondary resolver works uniformly.
- `CUP-2(n=12)`, target `exp2`, primary `even_val_sum`:
  exceptional groups `863`; the resolver menu is mixed and no single secondary
  coordinate dominates all cases.

STRUCTURAL RESULTS:

- The solved local `CUP-2` branch supports a genuine two-stage symbolic rule.
- The same simplification currently looks family- and size-sensitive rather than
  universal.

REPRESENTATIONS:

- “Two-stage `CUP-2` reduced-prefix recovery” representation.

### What Would Unblock This

The next best move is now clear:

1. state and package the two-stage `CUP-2` local recovery rule explicitly,
2. check whether it already proves a clean solved-range theorem for
   `CUP-2(n=10,11)`,
3. then decide whether repaired `n=12` should be treated as a separate
   corrected theorem rather than forced into the same symbolic template.

### Key Parameters

- Families tested:
  - `CUP-2(n=10,11,12)`
  - `Sol3(n=11)`
- Targets tested:
  - `exp2`,
  - `int21`.

### Open Questions

- Can the two exceptional `CUP-2(n=11)` patterns be proved directly from
  endpoint balance and weighted pair placement?
- Is there a repaired two-stage theorem for `CUP-2(n=12)` with
  `count_lag2_11` as the final correction?
- Is there a different primary split than `even_val_sum` that simplifies the
  `Sol3` `int21` branch more strongly?

## Synthesis after exploration 74

- The reduced-prefix branch has now produced its first genuinely sharp symbolic
  candidate theorem: a two-stage `CUP-2` recovery rule on the solved local
  range.
- The family divergence is also now explicit:
  `CUP-2` local recovery almost collapses to a formula, while `Sol3` does not
  yet do so under the same template.

## Exploration 75

### Strategy

Test whether the local `CUP-2` two-stage rule can be compressed further into a
uniform tiny basis across the solved and first repaired sizes, rather than being
stated as a special `n=10,11` case split.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out the idea that the local `CUP-2` theorem must be stated only as a
size-by-size ad hoc branching rule. A compact corrected basis exists through the
first repaired size.

### Surviving Structure

- On the reduced prefix
  `P_cup^red = (boundary6, exp2_weight, int21)`,
  the 3-feature basis
  `E_cup = (even_val_sum, weight_pair_11, weight_pair_22)`
  determines `exp2` exactly for:
  - `CUP-2(n=9)`
  - `CUP-2(n=10)`
  - `CUP-2(n=11)`
  - `CUP-2(n=12)`
- Tree depths on that same basis are:
  - `n=9`: `0`
  - `n=10`: `1`
  - `n=11`: `1`
  - `n=12`: `2`
- So the local `CUP-2` branch has a genuine compact corrected theorem:
  one reduced prefix plus one 3-feature weighted basis through the repaired
  `n=12` point.

### Reformulations

- Compact local `CUP-2` code view:
  instead of a solved-local case split, the local TP scalar `exp2` is itself a
  tiny exact code on the reduced coarse prefix.

LOAD-BEARING ASSESSMENT: very high. This is the first genuinely compact
corrected theorem on the reduced-prefix branch and is now the strongest positive
symbolic package available there.

### Concrete Artifacts

COMPUTED EXAMPLES:

- Exactness of `(even_val_sum, weight_pair_11, weight_pair_22)` for `exp2` on
  reduced `CUP-2` prefix:
  - `n=9`: exact
  - `n=10`: exact
  - `n=11`: exact
  - `n=12`: exact
- Tree depths on the same basis:
  - `CUP-2(n=9)`: depth `0`
  - `CUP-2(n=10)`: depth `1`
  - `CUP-2(n=11)`: depth `1`
  - `CUP-2(n=12)`: depth `2`

DOCS:

- `futurefc_theorem_package.md` now includes this compact local `CUP-2`
  theorem.

STRUCTURAL RESULTS:

- The first repaired `CUP-2` size does not force a new local basis for `exp2`.
- The needed correction at `n=12` is absorbed by the existing local basis once
  the reduced prefix is fixed.

REPRESENTATIONS:

- “Compact local `CUP-2` reduced-prefix theorem” representation.

### What Would Unblock This

The next best move is to prove or partially explain why
`(even_val_sum, weight_pair_11, weight_pair_22)` is sufficient for `exp2` on
the reduced prefix, rather than only observing that it is.

### Key Parameters

- Family tested: `CUP-2`.
- Sizes tested: `n=9,10,11,12`.
- Target tested: recovered TP scalar `exp2`.

### Open Questions

- Is there a direct combinatorial proof of the compact `CUP-2` local theorem?
- Does an equally compact corrected theorem exist for the `Sol3` `int21`
  branch?
- Can this local theorem be used as the first symbolic component of the full
  reduced-prefix `FutureFc` theorem?

## Synthesis after exploration 75

- The reduced-prefix branch now contains one genuinely compact corrected theorem
  rather than only clues.
- The strongest next proof target is now explicit:
  explain the compact local `CUP-2` theorem analytically, then use it as a
  building block for the full exact `FutureFc` code theorem.

## Exploration 76

### Strategy

Stop treating every new witness-side decoder fact as lower-bound progress and
write an explicit branch redirect: classify the current information-theory
results into `keep`, `conditional`, and `shelve` according to whether they can
still become a necessary condition on all valid systems or a forbidden
condition on subthreshold systems.

### Outcome

SUCCEEDED

### Failure Constraint

Not applicable.

### What This Rules Out

It rules out continuing the information-theory branch as an open-ended witness
anatomy project. From this point on, witness-side structure only stays on the
lower-bound critical path if it is explicitly aimed at:

1. a universal valid-system condition,
2. a subthreshold forbidden condition,
3. or a bridge theorem that converts witness structure into one of those.

### Surviving Structure

- The only current info-theory objects that still look lower-bound critical are:
  - forbidden width-`n-2` interaction suppression,
  - the two-level `FutureFc + slice-rank` suppression decomposition,
  - explicit subthreshold/invalid-family forbidden-mass gaps,
  - and any reduced-prefix theorem only if it is universalized or shown to fail
    below threshold.
- Witness-only results are now conditional:
  - exact tiny `FutureFc` codes,
  - shallow decoders,
  - reduced-prefix recovery trees,
  - compact local `CUP-2` theorem.
  They are useful only if promoted into a necessary valid-system condition or a
  forbidden subthreshold condition.
- Pure witness decoder polishing is now shelved from the lower-bound critical
  path unless it passes that test.

### Reformulations

- Lower-bound triage lens:
  every information-theory result must now be classified as:
  - `keep` if it directly targets a universal or forbidden theorem,
  - `conditional` if it only remains useful as a bridge theorem,
  - `shelve` if it is witness anatomy without an obstruction route.

LOAD-BEARING ASSESSMENT: very high. This changes the branch discipline and is
the best way to keep the work aligned with the actual lower-bound theorem.

### Concrete Artifacts

DOCS:

- `info_theory/lb_redirect_roadmap.md`
  records the new branch discipline, strict triage, and admissible next theorem
  targets.

STRUCTURAL RESULTS:

- Witness-side decoder theorems are no longer treated as lower-bound progress
  by default.
- The lower-bound-facing critical path is now explicitly:
  universal suppression,
  subthreshold forbidden-mass floor,
  or universal/forbidden reduced-prefix code theorems.

REPRESENTATIONS:

- “Necessary-or-forbidden” branch filter for information-theory work.

### What Would Unblock This

The next admissible theorem attempt is now sharply defined:

1. formulate the strongest plausible universal forbidden width-`n-2`
   suppression theorem,
2. formulate the strongest plausible subthreshold floor theorem,
3. use the current reduced-prefix package only if it helps bridge to one of
   those.

### Key Parameters

- No new computation. This was a strategic redirect and branch triage.

### Open Questions

- Can the forbidden width-`n-2` suppression theorem be stated in a genuinely
  universal form?
- Can any subthreshold family be shown to violate the reduced-prefix recovery
  structure in a theorem-shaped way?
- Which current witness-side theorem has the shortest path to becoming a real
  obstruction?

## Synthesis after exploration 76

- The branch is now back on rails.
- From here, the only info-theory work that counts is work that could become
  a necessary condition on all valid systems or a forbidden condition below
  threshold.
