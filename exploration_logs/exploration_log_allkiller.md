# Exploration Log

## Strategy Register

### Eliminated approach classes
- Pure universal-entry-conflict all-killers for non-consecutive binary are ruled out (exploration 1). Structural reason: the exact `n = 9` frontier contains a real clean strict-cycle residue, so "every survivor dies locally by entry conflict" is false even before completion.
- Residue-style all-`n` verifiers that depend on literal reuse of the exact `n = 9` completion fragments are ruled out (exploration 1). Structural reason: the completion obstruction survives at `n = 10`, but the minimized fragments grow from `33/35` at `n = 9` to `36/37/38`, so literal fixed-fragment containment is false.
- Exact-completion scaling as the primary path to `verified to 2000` is ruled out as a practical verification strategy (exploration 1). Structural reason: even the representative true Case `3c` base kernels become slow at `n = 11`, so direct seeded-cycle plus SMT completion is not converging to residue-style starpower.
- Any starpower argument based on intersections of greedy-minimized fragments is ruled out as a canonical method (exploration 2). Structural reason: the greedy reductions are highly non-unique; on the same residue family, the full forced singleton spine remains large and stable while the common minimized spine can shrink drastically or vanish.
- Any starpower argument based on raw anchored-rule intersections before quotienting local state-label symmetry is ruled out as a canonical method (exploration 5). Structural reason: the seeded good-cycle solver can return isomorphic cycles with different local ternary/quaternary labelings, and the resulting raw forced maps differ even for the same assignment and mover word.
- Interactive exact-completion continuation to `n = 11` is ruled out as a routine exploration method (exploration 8). Structural reason: even the normalized reverse-base `10 -> 11` shift comparison does not return in a reasonable interactive window, so exact continuation can no longer be the default tool for discovering higher-`n` structure.
- Normalized seeded-only probes are ruled out as direct reverse-base certificates (exploration 9). Structural reason: on reverse base they overstate the common spine already at `n = 9,10`, so they cannot replace exact completion for the reverse branch.

### Obstructions
- Universal entry conflict is false beyond the alternating/small regimes already noted elsewhere in the repo; the exact `n = 9` no-`3`-consecutive frontier has a clean residue class `(2,2,4,2,2,4,2,4,4)` with strict clean cycles (exploration 1).
- The correct direct obstruction at `n = 9` is hybrid: most candidates die by entry conflict, while the clean residue dies only at completion (exploration 1).
- Completion-side monotonicity is structural but not literal: larger-support and larger-`n` residue families preserve the local/completion split while changing the minimized fatal fragment size (exploration 1).
- Greedy fragment minimization hides stable structure: for the representative true Case `3c` families, the full forced singleton maps have substantial common intersections even when the common intersection of minimized fragments is tiny or empty (exploration 2).
- Normalization removes label noise but not the real upper-branch split: reverse upper-wiggle still has a mixed `6/35` completion residue after normalization, while forward upper-wiggle remains uniformly `35` (exploration 6).
- The current lexmin-probe budget has a computational wall near `n = 18`: beyond that size, some assignments time out or the optimizer returns unstable non-canonical models, so the fixed-edit law is no longer reliably observed without more compute (exploration 13).
- The `n = 18` break at timeout `1200 ms` is computational, not structural: increasing the lexmin timeout to `5000 ms` recovers the same base-family edit laws at `n = 18` (exploration 14).
- The upper-wiggle branch does not collapse immediately to one fixed edit template at `n = 9 -> 11`: the canonical edits remain tail-local and structured, but the gain/loss sets change between `9 -> 10` and `10 -> 11` (exploration 18).
- The representative-family canonical laws are not gap-universal even at `n = 9`: the base and upper assignment splits change across true Case `3c` gap patterns `(1,1,4)`, `(1,3,2)`, and `(2,2,2)` (explorations 21-22).
- The exact `n = 9` true-Case-`3c` frontier now has a reproducible regime table, not just scattered per-gap probes: reverse base has `3` regimes, forward base has `3`, reverse upper has `4`, and forward upper has `3` (exploration 23).
- The exact `n = 10` true-Case-`3c` frontier still has a small regime table rather than an explosion: reverse base has `3` regimes, forward base has `3`, forward upper has `3`, and reverse upper has `5` (exploration 24).
- The status-only exact taxonomy at `n = 11` still has a small regime table: reverse base `3`, forward base `3`, forward upper `3`, reverse upper `4` (exploration 25).

### Building blocks
- `verify_non_sweep.py` now contains an exact `n = 9` frontier clean scan and a hybrid clean-cycle/completion scan for the no-`3`-consecutive residue (exploration 1).
- `glb_three_sweep_scan.py` is now `n`-parametric for the residue grammar families, so the same three-sweep generators can be tested beyond `n = 9` (exploration 1).
- `glb_three_sweep_assignment_scan.py` now exposes reusable `assignment_rows(...)` data for exact assignment-by-assignment seeded/completion classification (exploration 1).
- `glb_case3c_starpower_probe.py` tests the strongest all-`n` candidate rule currently supported by the logs on the representative true Case `3c` family `(2,3,2,3,3,2,3,...,3,4)` (exploration 1).
- The representative true Case `3c` three-sweep residue obeys an exact bottom-wiggle split at both `n = 9` and `n = 10`:
  - reverse tail-`08`: bottom wiggle in first sweep => seeded-unsat; otherwise completion-unsat
  - forward tail-`01`: bottom wiggle in first sweep => completion-unsat; otherwise seeded-unsat
  (exploration 1).
- `glb_case3c_fragment_anatomy.py` extracts full forced singleton maps, minimized fragments, anchored processor labels, common spines, and SCC summaries for the representative true Case `3c` residue families (exploration 2).
- Base-family forced singleton spines grow more cleanly than minimized fragments:
  - reverse base: forced common spine `37 -> 40` from `n = 9` to `n = 10`
  - forward base: forced common spine `56 -> 67` from `n = 9` to `n = 10`
  while the minimized common spines stay much smaller (`8 -> 9`, `16 -> 20`) (exploration 2).
- Reverse upper-wiggle `n = 9` already shows the key mixed-branch phenomenon:
  - full forced common spine size `26`
  - common minimized spine size `0`
  - completion branch split `6` versus `35`
  (exploration 2).
- Cross-`n` base-family forced spines have substantial overlap:
  - reverse base: `30` anchored rules common to `n = 9` and `n = 10`
  - forward base: `35` anchored rules common to `n = 9` and `n = 10`
  and the differences concentrate near the tail labels `Q-k` plus a few nearby contexts, not across the whole ring (exploration 3).
- Under the natural tail-shift embedding `Q-k -> Q-(k+1)`, the base-family forced spines preserve most of their mass:
  - reverse base: `29/37` shifted rules survive from `n = 9` to `n = 10`
  - forward base: `37/56` shifted rules survive from `n = 9` to `n = 10`
  (exploration 4).
- Forward upper-wiggle `n = 9` is cleaner than reverse upper-wiggle in forced-spine coordinates:
  - forced common spine size `28`
  - minimized common spine size `5`
  - no `6`-rule cube-trap split; all completion branches stay at size `35`
  (exploration 4).
- Cycle-induced state normalization survives the first solver-consistency check:
  - reverse base `n = 9` raw forced common spine `37` is stable across exact and seeded-only paths
  - forward base `n = 9` raw forced data is solver-choice dependent, but first-appearance normalization along the cycle makes the exact and seeded-only `(0,0)` forced maps coincide exactly
  (exploration 5).
- Normalized forced spines strengthen the corridor picture on the base families:
  - reverse base normalized common spine sizes: `43` at `n = 9`, `52` at isolated `n = 10`
  - forward base normalized common spine sizes: `72` at `n = 9`, `81` at `n = 10`
  - under tail shift, reverse preserves `43/43` rules exactly and forward preserves `67/72`
  (exploration 6).
- Normalized upper-branch spines are substantially larger than raw ones without collapsing the orientation split:
  - reverse upper `n = 9`: raw `26`, normalized `34`, still mixed `6/35`
  - forward upper `n = 9`: raw `37`, normalized `61`, still uniform `35`
  (exploration 6).
- The normalized base-family tail defect from `n = 9 -> 10` is now explicit and finite:
  - reverse: no losses, exactly `9` gained rules, all at `Q` or `Q-2`
  - forward: exactly `5` lost rules at `Q-1`, exactly `14` gained rules at `Q` or `Q-1`
  (exploration 7).
- `glb_case3c_forced_spine_probe.py` now scouts normalized seeded-only common spines on the predicted completion branch without SMT completion (exploration 9).
- `glb_case3c_family_recurrence.py` now packages all four stable canonical families on the representative true Case `3c` architecture:
  - reverse base, anchor `n = 9`
  - forward base, anchor `n = 9`
  - reverse upper, anchor `n = 10`
  - forward upper, anchor `n = 11`
  together with generation and probe-verification hooks (exploration 20).
- `glb_case3c_gap_pattern_probe.py` now reconstructs normalized true Case `3c` state vectors from gap triples, derives the natural three-sweep family spec for each orientation, and reports exact assignment summaries plus bottom-slot mismatch data across gap patterns (exploration 21).
- `glb_case3c_gap_pattern_probe.py` now also has a taxonomy mode that clusters gap patterns by exact bottom-slot and fragment-size signatures, producing the full exact `n = 9` regime table in one command per family set (exploration 23).
- `glb_case3c_gap_pattern_probe.py` is now `n`-aware: if no explicit gaps are passed, it enumerates the canonical true Case `3c` gap patterns for the requested `n` and can produce the exact taxonomy table there as well (exploration 24).
- `glb_three_sweep_assignment_scan.py` and `glb_case3c_gap_pattern_probe.py` now support a status-only path that skips fatal-fragment minimization on completion-unsat branches. LOAD-BEARING: high. This makes `n = 11` regime discovery tractable without changing the seeded/completion status logic (exploration 25).
- The normalized seeded-only probe is already informative on forward base:
  - `n = 10` normalized common spine size `81`, matching the exact anchor
  - `n = 11` normalized common spine size `90`
  - the forward tail defect from `n = 10 -> 11` is the same `5` losses and `14` gains seen at `n = 9 -> 10`
  (exploration 9).
- The reverse probe mismatch is a solver-history artifact, not a proved structural gap:
  - in a fresh process, reverse probe gave `60` and `69` at `n = 9,10`
  - after running the exact reverse collector first in the same process, the probe collapsed exactly to the exact anchors `43` and `52`
  (exploration 10).
- Lexicographic cycle selection fixes the reverse probe:
  - fresh-process reverse lexmin probe reproduces exact normalized common spine sizes `43` at `n = 9` and `52` at `n = 10`
  - reverse lexmin `n = 10 -> 11` is pure extension again: `52 -> 61` with `0` losses and the same `9` gains seen at exact `9 -> 10`
  - forward lexmin `n = 10 -> 11` keeps the same `5` losses and `14` gains
  (exploration 11).
- The lexmin base-family recurrence now persists through `n = 13`:
  - reverse normalized common spine sizes: `43, 52, 61, 70, 79` for `n = 9,10,11,12,13`
  - forward normalized common spine sizes: `72, 81, 90, 99, 108` for `n = 9,10,11,12,13`
  - reverse edit remains exactly `+9` with no losses
  - forward edit remains exactly `-5/+14`
  (exploration 12).
- With lexmin timeout `1200 ms`, the base-family law remains stable through `n = 17`:
  - reverse sizes: `43, 52, 61, 70, 79, 88, 97, 106, 115`
  - forward sizes: `72, 81, 90, 99, 108, 117, 126, 135, 144`
  - same reverse `+9/0` edit and same forward `5/14` edit on every step up to `17`
  (exploration 13).
- Raising the lexmin timeout to `5000 ms` restores the same law at `n = 18`:
  - reverse `n = 17 -> 18`: all `6/6` assignments solved, size `124`, same `+9/0` edit
  - forward `n = 17 -> 18`: all `3/3` assignments solved, size `153`, same `5/14` edit
  (exploration 14).
- At timeout `5000 ms`, the same laws continue through `n = 19`:
  - reverse `n = 18 -> 19`: all `6/6` assignments solved, size `133`, same `+9/0` edit
  - forward `n = 18 -> 19`: all `3/3` assignments solved, size `162`, same `5/14` edit
  (exploration 15).
- At timeout `5000 ms`, the same laws continue through `n = 20`:
  - reverse `n = 19 -> 20`: all `6/6` assignments solved, size `142`, same `+9/0` edit
  - forward `n = 19 -> 20`: all `3/3` assignments solved, size `171`, same `5/14` edit
  (exploration 16).
- `glb_case3c_base_recurrence.py` now packages the canonical base-family law explicitly:
  - derives the fixed edit templates from the `n = 9 -> 10` lexmin anchor
  - generates predicted canonical spines for arbitrary larger `n` without re-solving every step
  - verifies against the lexmin probe on a requested range
  (exploration 17).
- Canonical upper-wiggle probes are now available and fully solved through `n = 11` at timeout `1200 ms`:
  - reverse upper sizes: `32, 40, 49` for `n = 9,10,11`
  - forward upper sizes: `58, 64, 72` for `n = 9,10,11`
  - all predicted completion-branch assignments solved in this range
  (exploration 18).
- Reverse upper-wiggle now shows a stable fixed edit law from `n = 10` onward:
  - sizes `40, 49, 58` for `n = 10,11,12`
  - same `2` losses and same `11` gains on both `10 -> 11` and `11 -> 12`
  (exploration 19).

### Known reformulations
- Hybrid all-killer: "entry conflict OR no completion" is the correct direct computational target, not universal entry conflict. LOAD-BEARING: very high. It matches the exact `n = 9` frontier behavior and gives a defensible computational replacement for the failed universal-EC story (exploration 1).
- Explicit three-sweep residue grammar: once the local obstructions fail, the surviving true Case `3c` words are best viewed as `0`-anchored four-block words with three monotone sweeps plus one boundary tail/short block. LOAD-BEARING: high. This is the first programmable residue object that survives beyond `n = 9` (exploration 1).
- Assignment-exact residue rule: the decisive local/completion split is controlled by the slot of the bottom wiggle, not by the full mover word. LOAD-BEARING: high. It sharply compresses the residue language, but does not yet produce a fixed-size completion theorem (exploration 1).
- Completion-fragment growth rather than fragment identity: the right asymptotic question is no longer "does every higher support literally contain one of the `n = 9` fragments?" but "is there a symbolic fragment generator whose size/control law is explicit in `n`?" LOAD-BEARING: high. This is the exact place where the starpower project now lives (exploration 1).
- Forced singleton spine rather than minimized fragment intersection: the stable object across assignments is the intersection of the full singleton-forced maps induced by the seeded cycle, not the intersection of one arbitrary greedy minimization. LOAD-BEARING: very high. This is the first reformulation in the project that cleanly separates canonical residue data from minimization artifacts (exploration 2).
- Tail-corridor growth picture: when the forced singleton spines are compared in anchored coordinates across `n`, much of the change looks like tail-local extension toward `Q-k` rather than a total rewrite of the whole rule set. LOAD-BEARING: moderate to high. This is the first concrete hint that the `n`-dependence might be a corridor generator rather than arbitrary fragment growth (exploration 3).
- Tail-shift embedding: the right cross-`n` comparison is not raw label equality but the embedding that fixes `P0..P5` and shifts `Q-k -> Q-(k+1)`, `Q -> Q-1`. LOAD-BEARING: high. This is the first comparison that turns the base-family `n = 9 -> 10` change into mostly preserved structure rather than noisy overlap counts (exploration 4).
- Cycle-induced state normalization: before comparing forced singleton spines across assignments, solver runs, or `n`, quotient the per-processor local state-label symmetry by canonically relabeling each processor's states in order of first appearance along the anchored good cycle. LOAD-BEARING: very high. This collapses the forward-branch exact/seeded mismatch and is now the only defensible coordinate system for canonical spine comparisons (exploration 5).
- Normalized tail-shift spine: the best current candidate invariant is the cycle-normalized forced singleton spine, compared across `n` only after the `Q-k -> Q-(k+1)` tail embedding. LOAD-BEARING: very high. On the base families this turns the reverse branch into exact preservation and the forward branch into a small finite tail correction, which is much closer to a residue-style corridor generator than anything seen in raw coordinates (exploration 6).
- Tail-extension rule inventory: the normalized `n -> n+1` change on the base families should be viewed as an explicit finite edit near `Q, Q-1, Q-2`, not as a global deformation of the spine. LOAD-BEARING: high. This is the first form in which the remaining `n`-dependence looks small enough to hope for an explicit recursive verifier (exploration 7).
- Probe/exact split by orientation: use the normalized seeded-only probe to scout forward-base growth, but keep reverse-base claims tied to exact completion anchors. LOAD-BEARING: high. This is currently the sharpest trustworthy division of labor available past the `n = 11` exact wall (exploration 9).
- Reverse mismatch as model-selection problem: the reverse seeded-only over-approximation is now best viewed as a bad cycle-choice issue, not a different residue family. LOAD-BEARING: very high. If a canonical cycle selector can reproduce the exact reverse anchors without SMT completion, the all-`n` discovery path reopens on the hard branch as well (exploration 10).
- Lexicographically minimal anchored cycle: among seeded good cycles for a fixed mover word, choose the lexicographically minimal flattened cycle after anchoring at the all-zero configuration. LOAD-BEARING: very high. This reproduces the exact reverse anchors at `n = 9,10` and makes the reverse branch behave recursively again at `n = 11` (exploration 11).
- Linear-growth recurrence on canonical base spines: once the lexmin representative is chosen, the base-family common spines appear to satisfy fixed linear recurrences with fixed tail edits. LOAD-BEARING: very high. This is the closest thing yet to a `residue`-style scalable verifier object (exploration 12).
- Range-limited lexmin verification: the base-family recursive law should currently be stated as "verified by canonical lexmin probe through `n = 17` at timeout `1200 ms`," not as an unrestricted all-`n` fact. LOAD-BEARING: high. This is honest, already stronger than the old `9/10` story, and it exposes exactly what extra compute or proof is needed next (exploration 13).
- Timeout budget as part of the verification statement: the canonical law appears stable past `n = 17`, but only when the selector budget is large enough to actually recover the canonical cycles. LOAD-BEARING: high. This shifts the obstruction from "new regime at `18`" to "current selector cost grows too fast" (exploration 14).
- Budget-dependent range scaling: the base-family recurrence is now best viewed as a scalable law with a moving computational frontier, not a law that breaks at a fixed `n`. LOAD-BEARING: high. Increasing the selector budget extends the verified range without changing the observed edit laws (exploration 15).
- Medium-budget canonical range statement: the current strongest computational claim is a lexmin-canonical base-family law verified through `n = 20` at timeout `5000 ms`, with fixed reverse `+9/0` and forward `5/14` edits. LOAD-BEARING: very high. This is the first genuinely broad, reproducible computational statement in the project that resembles the user’s `residue` benchmark in form, even if the range is still modest (exploration 16).
- Explicit recurrence checker: the base-family law can now be stated as a concrete recurrence object rather than only as repeated probe outputs. LOAD-BEARING: very high. This is the first point where the scalable base-family computation has a reusable theorem-shaped interface instead of just an exploration log narrative (exploration 17).
- Upper branch as local-edit family with drifting templates: the upper-wiggle branch still looks tail-local under the canonical selector, but it currently behaves more like a small evolving grammar than a single fixed edit law. LOAD-BEARING: moderate to high. This is already enough to focus future proof work on the tail corridor rather than on the whole ring, even though it is not yet a starpower recurrence (exploration 18).
- Split upper-wiggle strategy: reverse upper may already be a genuine fixed recurrence after the `n = 10` anchor, while forward upper still looks like a small evolving tail-state machine. LOAD-BEARING: high. This means the full-fat verifier can likely absorb reverse upper now and isolate forward upper as the last canonical tail-grammar problem (exploration 19).
- Full representative-family recurrence layer: the representative true Case `3c` architecture now has four explicit canonical recurrence laws, not just the two base-family ones. LOAD-BEARING: very high. This upgrades the recurrence layer from "promising special case" to "complete package for one architecture family" (exploration 20).
- Gap-regime taxonomy rather than one universal `Case 3c` law: once the representative family is packaged, the next obstruction is no longer upper-vs-base but gap dependence. LOAD-BEARING: very high. The exact `n = 9` data now says the true Case `3c` frontier splits into multiple assignment-law regimes indexed by gap pattern and orientation, so a full-fat verifier has to classify a finite regime family rather than prove one representative recurrence covers everything (explorations 21-22).
- Exact `n = 9` regime table as the `M1` milestone: the right finite object is no longer just "some gap sensitivity exists" but an explicit clustered catalogue of regimes by family/orientation. LOAD-BEARING: very high. This is the first point where `Case 3c` gap dependence is packaged as data that a later verifier can consume rather than as prose in the log (exploration 23).
- Small-regime persistence at `n = 10`: the finite gap-regime picture survives one step higher. LOAD-BEARING: very high. This is the first evidence that the `n = 9` taxonomy is not just a small-instance accident, even though reverse upper does split more finely at `n = 10` (exploration 24).
- Small-regime persistence at `n = 11`: even after the `n = 10` refinement, the catalogue is still small at the next step. LOAD-BEARING: very high. This is the strongest evidence so far that the project is heading toward a finite regime theory rather than a proliferating taxonomy (exploration 25).

## Session Start (2026-03-11)

Resuming from exploration 0.

No prior `exploration_log_allkiller.md` existed in the repository, so there is
no earlier all-killer-specific state to reuse.

Next attempt: test whether the strongest `L = 33` / `L = 35` residue
observations can be turned into a real all-`n` verification path, and stop as
soon as the surviving structure no longer justifies that claim.

## Exploration 1

### Strategy
Start from the `L = 33` true Case `3c` residue observations, test whether the exact `n = 9` clean residue can be completion-killed computationally, then push the surviving three-sweep assignment rules to larger `n` to see whether they form a residue-style all-`n` verifier or only a small-`n` taxonomy.

### Outcome
STALLED

### Failure Constraint
The `L = 33` observations do not yet yield a residue-style all-`n` killer because the completion obstruction is not a fixed finite kernel. The exact bottom-wiggle split survives from `n = 9` to `n = 10`, but the minimized completion fragments grow from `33/35` to `36/37/38`, and exact seeded-cycle plus completion solving becomes too slow to push cleanly past `n = 10` in interactive work. The bottleneck is computational, not conceptual: we have a stable residue grammar, but not a symbolic completion theorem whose complexity is bounded independently of `n`.

### What This Rules Out
- Any all-`n` claim built on "universal entry conflict kills every non-sweep" will fail on the exact `n = 9` frontier because clean residues exist.
- Any starpower pitch of the form "we already have a finite kernel library at `n = 9`, now just scan it to `2000`" is premature. The fragment library is structured, but it is not fixed under either added support or larger `n`.
- Any verification plan that keeps exact SMT completion in the inner loop will hit the same scaling wall by `n = 11` unless the completion residue is first compressed symbolically.

### Surviving Structure
- Exact `n = 9` frontier result:
  - the multiset-representative no-`3`-consecutive sub-`8748` frontier has `12` orientations;
  - at strict-cycle length `33`, only one representative orientation produces clean cycles;
  - that representative is `(2,2,4,2,2,4,2,4,4)`;
  - it has `810` clean cycles;
  - all `810` are killed by completion;
  - there are `0` unknowns and `0` valid systems.
- The pure clean-scan target is false:
  - the first clean witness found on the frontier is
    `(0,8,7,6,5,4,3,2,1,0,8,7,8,7,8,7,6,5,6,5,6,5,4,3,2,3,2,3,2,1)`;
  - it has no entry conflict under the strict GEC checker;
  - but SMT completion rejects it by propagation.
- The residue grammar is real:
  - all currently known `L = 33` and `L = 35` true Case `3c` survivors lie in the same three-sweep/four-block grammar already described in `glb_residue_grammar.py`;
  - this grammar could be made `n`-parametric with only endpoint generalization.
- The bottom-wiggle rule survives exact checks at `n = 10` on the representative true Case `3c` family:
  - reverse base family `(1,4)` with tail `(0,n-1)`: `3` seeded-unsat, `6` completion-unsat, `0` mismatches;
  - forward base family `(2,5)` with tail `(0,1)`: `6` seeded-unsat, `3` completion-unsat, `0` mismatches;
  - reverse upper-wiggle family `(1,4,n-2)`: `9` seeded-unsat, `18` completion-unsat, `0` mismatches;
  - forward upper-wiggle family `(2,5,n-2)`: `18` seeded-unsat, `9` completion-unsat, `0` mismatches.
- Fragment growth is controlled but real:
  - `n = 9` base completion kernels minimize to `33`;
  - `n = 9` forward upper-wiggle family minimizes uniformly to `35`;
  - `n = 10` base families minimize uniformly to `36`;
  - `n = 10` reverse upper-wiggle family splits into sizes `6`, `37`, `38`;
  - `n = 10` forward upper-wiggle family minimizes uniformly to `38`.

### Reformulations
- The corrected direct-computation target is:
  - detect local contradiction when present;
  - otherwise force the mover word into the explicit residue grammar;
  - then kill that residue by a symbolic completion theorem.

LOAD-BEARING ASSESSMENT: Very high. This is the first formulation that matches every direct computation in this session and cleanly separates the local and completion residues.

- The relevant asymptotic object is not an individual minimized fragment but a generator for the completion fragment family. The fragment size is varying with `n` and with extra support, but the decision rule still depends only on the bottom-wiggle placement.

LOAD-BEARING ASSESSMENT: High. This does change the effective search space: the task is no longer "enumerate large mover words" but "derive the symbolic rule family behind the growing fragments."

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exact `n = 9` multiset-representative hybrid frontier scan:
  - command:
    `python3 src_comp_ver/verify_non_sweep.py --from-n 9 --to-n 9 --frontier-hybrid-mode multiset --frontier-hybrid-max-len 33`
  - output summary:
    - `orientations=12`
    - `clean_orientations=1`
    - `clean_cycles=810`
    - `completion_blocked=810`
    - `unknown=0`
    - `valid_systems=0`
- Exact clean witness on the no-`3`-consecutive frontier:
  - state counts `(2,2,4,2,2,4,2,4,4)`
  - strict clean word
    `(0,8,7,6,5,4,3,2,1,0,8,7,8,7,8,7,6,5,6,5,6,5,4,3,2,3,2,3,2,1)`
- Exact assignment-level residue checks already known at `n = 9`:
  - reverse base family `generate_words((1,4), 'reverse', 'tail08')`:
    - summary `{('completion_unsat', 33): 6, ('seed_unsat', None): 3}`
  - forward upper-wiggle family `generate_words((2,5,7), 'forward', 'tail01')`:
    - summary `{('completion_unsat', 35): 9, ('seed_unsat', None): 18}`
- New `n = 10` representative-family checks:
  - base families:
    - command:
      `python3 probes/gpt/glb_case3c_starpower_probe.py --n-values 10 --orientation both --timeout-ms 1200`
    - reverse summary `{('completion_unsat', 36): 6, ('seed_unsat', None): 3}`
    - forward summary `{('completion_unsat', 36): 3, ('seed_unsat', None): 6}`
    - `0` mismatches in both orientations
  - upper-wiggle families:
    - command:
      `python3 probes/gpt/glb_case3c_starpower_probe.py --n-values 10 --orientation both --include-upper-wiggle --timeout-ms 1200`
    - reverse summary `{('completion_unsat', 37): 1, ('completion_unsat', 38): 12, ('completion_unsat', 6): 5, ('seed_unsat', None): 9}`
    - forward summary `{('completion_unsat', 38): 9, ('seed_unsat', None): 18}`
    - `0` mismatches in both orientations

STRUCTURAL RESULTS:
- Universal entry conflict is not the right all-killer even at `n = 9`.
- The exact frontier data supports a hybrid theorem shape:
  - `entry conflict OR no completion`.
- The bottom-wiggle split survives from `n = 9` to `n = 10` on the representative true Case `3c` family.
- Fragment identity does not survive from `n = 9` to `n = 10`; only the higher-level residue rule survives.

TOOLS:
- `src_comp_ver/verify_non_sweep.py`
  - now includes direct `n = 9` clean-cycle and hybrid completion scans on the exact no-`3`-consecutive frontier.
  - useful outputs:
    - first clean witness
    - exact clean-cycle counts
    - completion-blocked / unknown / valid-system counts
- `probes/gpt/glb_three_sweep_scan.py`
  - generalized to arbitrary `n` for the three-sweep residue grammar families.
- `probes/gpt/glb_three_sweep_assignment_scan.py`
  - now exposes `assignment_rows(...)`, a reusable exact classifier of assignment tuple -> seeded/completion outcome -> minimized fragment size.
- `probes/gpt/glb_case3c_starpower_probe.py`
  - inputs:
    - `n`
    - orientation (`reverse` / `forward`)
    - optional extra upper wiggle
  - outputs:
    - exact assignment summaries
    - mismatch count against the bottom-wiggle prediction
    - fragment-size histogram
  - performance:
    - `n = 10` base families are practical
    - `n = 10` upper-wiggle families are slower but still complete
    - `n = 11` base-family exact completion is already too slow for normal interactive use

REPRESENTATIONS:
- Frontier-hybrid representation of the `n = 9` residue:
  - exact orientation set
  - clean-cycle enumeration
  - completion kill on each clean cycle
- Three-sweep/four-block residue grammar:
  - three monotone sweep blocks
  - one tail/short boundary block
  - local wiggles assigned to sweep slots
- Assignment representation:
  - an assignment tuple `(a_e)` giving the sweep slot of each wiggle edge
  - the status prediction depends only on the slot of the bottom wiggle

### What Would Unblock This
- A symbolic completion-fragment generator for the residue families, with size/control law explicit in `n`, so exact completion does not remain in the inner loop.
- A theorem that the representative true Case `3c` residue grammar is not just experimentally stable but necessary for the full true Case `3c` family at general `n`.
- A proof that the growing fragment families are shift-equivalent instances of one small rule schema, not genuinely new completion objects at each `n`.
- A way to extend the residue-grammar necessity story from true Case `3c` to the broader non-consecutive-binary lower-bound residue, if the goal remains a theorem-level all-killer rather than a Case `3c` engine.

### Key Parameters
- Exact frontier target:
  - `n = 9`
  - no-`3`-consecutive sub-`8748` residue
  - strict-cycle search bound `33`
- Representative true Case `3c` family:
  - state counts `(2,3,2,3,3,2,3,...,3,4)`
  - binaries at `0,2,5`
  - quaternary at `n - 1`
- Families tested:
  - reverse base `(1,4)` with tail `(0,n-1)`
  - forward base `(2,5)` with tail `(0,1)`
  - reverse upper `(1,4,n-2)` with tail `(0,n-1)`
  - forward upper `(2,5,n-2)` with tail `(0,1)`
- Exact runs completed:
  - `n = 9` frontier hybrid
  - `n = 9` base and upper-wiggle assignment families
  - `n = 10` base and upper-wiggle assignment families
- Exact run stopped:
  - `n = 11` base-family starpower probe, because exact completion had already crossed the useful interactive threshold

### Open Questions
- Is there a symbolic rule schema behind the `33 -> 36 -> 38` fragment growth, or are these genuinely different completion mechanisms sharing only the same assignment split?
- Can the residue grammar itself be proved necessary for general true Case `3c`, or is it only a property of the currently sampled representative families?
- Is the `n = 10` fragment growth linear in `n`, eventually constant after quotienting by shifts, or something more complicated?
- Can the exact `n = 9` frontier hybrid result be lifted from the multiset-representative level to a fully packaged all-orientation certificate without reintroducing the same completion bottleneck?

## Synthesis after exploration 1

The session changed the all-killer project in one decisive way: the surviving
object is no longer "a finite list of `n = 9` bad words" and not "universal
entry conflict." It is an explicit residue grammar with a very small assignment
rule and a still-opaque completion family behind it. That is real progress, but
it is not starpower yet. The path to a `residue`-style result is now precise:
replace exact completion with a symbolic completion-fragment theorem. If that
cannot be done, this line remains a strong small-`n` corroboration framework
rather than an all-`n` verifier.

## Exploration 2

### Strategy
Replace the unstable "common minimized fragment" view with a more canonical residue object by extracting the full singleton-forced maps on the representative true Case `3c` families, anchoring their processor labels relative to the bottom block and quaternary tail, and comparing those forced spines across assignments and `n`.

### Outcome
SUCCEEDED

### Failure Constraint
Greedy minimization is too noncanonical to serve as the main all-killer invariant. Even on the exact `n = 9` families, the common intersection of greedy-minimized fragments can be far smaller than the stable intersection of the full forced singleton maps, and in the mixed `6`/`35` reverse upper-wiggle branch it collapses all the way to `0`. So any theorem based on "the common minimized fragment" will be contaminated by arbitrary minimization choices.

### What This Rules Out
- Any attempt to read the all-`n` residue directly off one minimized fragment per assignment is structurally unsound.
- Any claim that the completion residue has "no common core" based only on minimized fragments is unreliable; the full forced singleton maps can retain a large shared spine even when the minimized common core disappears.
- Any data-collection plan that ignores the pre-minimization singleton maps is discarding the most canonical completion information currently available.

### Surviving Structure
- Reverse base family:
  - `n = 9`:
    - full forced size `95` on all `6` completion assignments
    - forced common spine size `37`
    - minimized common spine size `8`
    - minimized fragment size `33`
  - `n = 10`:
    - full forced size `104` on all `6` completion assignments
    - forced common spine size `40`
    - minimized common spine size `9`
    - minimized fragment size `36`
- Forward base family:
  - `n = 9`:
    - full forced size `95` on all `3` completion assignments
    - forced common spine size `56`
    - minimized common spine size `16`
    - minimized fragment size `33`
  - `n = 10`:
    - full forced size `104` on all `3` completion assignments
    - forced common spine size `67`
    - minimized common spine size `20`
    - minimized fragment size `36`
- Reverse upper-wiggle family at `n = 9`:
  - completion assignments `18`
  - full forced size histogram `{99: 3, 100: 14, 101: 1}`
  - forced common spine size `26`
  - minimized common spine size `0`
  - minimized size histogram `{6: 4, 35: 14}`
  - so the mixed cube/large-trap branch destroys the greedy common core but not the full forced singleton spine.
- The anchored coordinate system is already informative:
  - reverse base forced common spines are concentrated on `P0..P5` and the last few processors near the quaternary tail (`Q`, `Q-1`, `Q-2`, `Q-3`);
  - this is evidence for a structured corridor object rather than arbitrary global diffusion.

### Reformulations
- The canonical completion residue data is:
  - the full singleton-forced map induced by the seeded cycle,
  - anchored by fixed bottom processors `P0..P5` and tail-relative labels `Q-k`, `Q`.
  The minimized fragment is secondary: it is still useful for compression, but not for defining the stable all-`n` object.

LOAD-BEARING ASSESSMENT: Very high. This is the first robust candidate for a symbolic completion theorem. It removes one major source of noise from the residue data and makes cross-`n` comparison meaningful.

- The completion residue now looks like a two-layer object:
  - a forced singleton spine that persists across assignments,
  - plus a variable part that decides whether the branch collapses to a tiny cube trap or a larger propagated SCC.

LOAD-BEARING ASSESSMENT: High. This is a clearer and more useful decomposition than the old "common core of minimized fragments" picture.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse base family, `n = 9`:
  - command:
    `python3 probes/gpt/glb_case3c_fragment_anatomy.py --n-values 9 --orientation reverse --timeout-ms 1200`
  - output highlights:
    - `forced_size_histogram={95: 6}`
    - `forced_common_spine_size=37`
    - `size_histogram={33: 6}`
    - `common_spine_size=8`
- Base families, `n = 9,10`:
  - command:
    `python3 probes/gpt/glb_case3c_fragment_anatomy.py --n-values 9,10 --orientation both --timeout-ms 1200`
  - reverse:
    - `n = 9`: forced common `37`, minimized common `8`
    - `n = 10`: forced common `40`, minimized common `9`
  - forward:
    - `n = 9`: forced common `56`, minimized common `16`
    - `n = 10`: forced common `67`, minimized common `20`
- Reverse upper-wiggle family, `n = 9`:
  - command:
    `python3 probes/gpt/glb_case3c_fragment_anatomy.py --n-values 9 --orientation reverse --include-upper-wiggle --timeout-ms 1200`
  - output highlights:
    - `forced_size_histogram={99: 3, 100: 14, 101: 1}`
    - `forced_common_spine_size=26`
    - `size_histogram={6: 4, 35: 14}`
    - `common_spine_size=0`
- Exact run stopped:
  - command:
    `python3 probes/gpt/glb_case3c_fragment_anatomy.py --n-values 10 --orientation reverse --include-upper-wiggle --timeout-ms 1200`
  - reason:
    - exact anatomy extraction on the `n = 10` reverse upper-wiggle family crossed the useful interactive threshold again.

STRUCTURAL RESULTS:
- The forced singleton spine is strictly more stable than the common minimized fragment.
- Base-family forced spines grow in a controlled way from `n = 9` to `n = 10`, unlike the highly compressed minimized intersections.
- Mixed completion branches can have empty common minimized core and still retain a substantial forced singleton spine.

TOOLS:
- Added `probes/gpt/glb_case3c_fragment_anatomy.py`.
  - inputs:
    - `n`
    - orientation (`reverse` / `forward`)
    - optional upper wiggle
  - outputs:
    - per-assignment full forced size
    - minimized fragment size
    - anchored common spine sizes for both the full forced maps and minimized fragments
    - SCC histograms
    - anchored common-spine rule lists
  - performance:
    - base families at `n = 9,10` are practical
    - reverse upper family at `n = 9` is practical
    - reverse upper family at `n = 10` remains too slow for normal interactive use

REPRESENTATIONS:
- Anchored processor labels:
  - `P0..P5` for the fixed bottom block,
  - `Q-k` and `Q` for processors counted backward from the quaternary tail.
- Two-layer completion residue:
  - full forced singleton spine,
  - assignment-dependent variable part.

### What Would Unblock This
- A way to compute or characterize the forced singleton spine without full exact completion, so the `n = 10` reverse upper family and beyond do not require long exact runs.
- A symbolic description of how the forced common spine grows with `n` on the base families.
- A classification of the variable part on top of the forced spine, especially the `6`-rule cube-trap branch versus the larger propagated branches.

### Key Parameters
- Families analyzed exactly:
  - reverse base at `n = 9`
  - reverse/forward base at `n = 9,10`
  - reverse upper-wiggle at `n = 9`
- Families not completed exactly in this exploration:
  - reverse upper-wiggle at `n = 10`
- Timeout setting:
  - `1200 ms` seeded-cycle budget with exact completion inside the collector

### Open Questions
- Does the forced singleton spine on the reverse upper family also persist cleanly from `n = 9` to `n = 10`, or does it bifurcate the way the minimized fragments do?
- Is the forward upper family cleaner than the reverse upper family in forced-spine coordinates, as it was in minimized-size coordinates?
- Can the base-family forced spines be explained by one symbolic corridor generator with a simple `n`-dependence?

## Synthesis after exploration 2

This was the first exploration that changed the all-killer search space rather
than just refining counts. The stable residue object is not the minimized
fragment. It is the full forced singleton spine. That is a much better place to
look for starpower, because it survives exactly where the greedy common core
fails. The project is still alive, but the new target is sharper:

- derive the forced spine symbolically,
- then explain the variable completion residue on top of it.

If that symbolic forced-spine layer cannot be extracted, then the current
pipeline really does stop at a small-`n` anatomy project. If it can, the
starpower path is still open.

## Exploration 3 (probe)

### Strategy
Compare the anchored forced common spines of the base reverse/forward families between `n = 9` and `n = 10` to see whether the new rules appear globally or mainly as tail-local corridor growth.

### Outcome
SUCCEEDED

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse base forced common spines:
  - intersection size `30`
  - rules only at `n = 9`: `7`
  - rules only at `n = 10`: `16`
  - sample `n = 10` additions:
    - `('Q-3', (0,0,0), 0)`
    - `('Q-2', (1,1,0), 0)`
    - `('Q-2', (1,1,1), 1)`
    - `('Q-2', (2,2,2), 2)`
  - processor histogram of forced common spine:
    - `n = 9`: `{'P0':4,'P1':5,'P2':6,'P3':2,'P4':5,'P5':5,'Q':2,'Q-1':1,'Q-2':7}`
    - `n = 10`: `{'P0':4,'P1':5,'P2':6,'P3':2,'P4':5,'P5':5,'Q':2,'Q-1':1,'Q-2':9,'Q-3':7}`
- Forward base forced common spines:
  - intersection size `35`
  - rules only at `n = 9`: `21`
  - rules only at `n = 10`: `13`
  - sample `n = 10` additions:
    - `('Q-1', (2,0,0), 2)`
    - `('Q-2', (1,2,2), 1)`
    - `('Q-2', (2,2,0), 2)`
  - processor histogram of forced common spine:
    - `n = 9`: `{'P0':11,'P1':10,'P2':8,'P3':2,'P4':2,'P5':3,'Q':9,'Q-1':9,'Q-2':2}`
    - `n = 10`: `{'P0':5,'P1':10,'P2':8,'P3':2,'P4':2,'P5':3,'Q':2,'Q-1':5,'Q-2':9,'Q-3':2}`

STRUCTURAL RESULTS:
- The base-family forced singleton spines are not rewriting wholesale from `n = 9` to `n = 10`.
- The dominant changes occur near the anchored tail labels `Q-k`, which is consistent with corridor extension toward the quaternary tail.
- Reverse and forward families behave differently in detail, but both show substantial anchored overlap across `n`.

## Exploration 4

### Strategy
Test the tail-corridor interpretation directly by comparing base-family forced spines under the natural tail-shift embedding from `n = 9` to `n = 10`, and fill the missing `n = 9` forward upper-wiggle anatomy to see whether the upper branch is structurally simpler on the forward side.

### Outcome
SUCCEEDED

### Failure Constraint
Raw anchored overlap is not the right cross-`n` metric. Without the tail-shift embedding, preserved structure is underestimated because old tail labels become one step deeper when a new ternary is inserted before the quaternary. The canonical comparison must fix `P0..P5` and shift the tail labels.

### What This Rules Out
- Any claim that the base-family forced spines are changing too much to support a corridor theorem, when that claim is based only on raw `Q-k` label equality, is too pessimistic.
- Any attempt to compare cross-`n` spines without an explicit tail embedding is mixing structural growth with a relabeling artifact.

### Surviving Structure
- Tail-shift preservation on the base families:
  - reverse base:
    - `n = 9` forced common spine size `37`
    - after shift `Q-k -> Q-(k+1)`, `29` rules survive inside the `n = 10` forced common spine
    - only `8` shifted rules are lost
    - `17` genuinely new rules appear at `n = 10`
  - forward base:
    - `n = 9` forced common spine size `56`
    - after the same shift, `37` rules survive inside the `n = 10` forced common spine
    - `19` shifted rules are lost
    - `11` genuinely new rules appear at `n = 10`
- The sample gains/losses are still tail-heavy:
  - reverse added rules cluster at `Q`, `Q-2`, `Q-3` and nearby contexts;
  - forward added rules cluster at `Q`, `Q-1`, `Q-2`, `Q-3`.
- Forward upper-wiggle `n = 9`:
  - completion assignments `9`
  - full forced size histogram `{99: 1, 100: 3, 101: 5}`
  - forced common spine size `28`
  - minimized common spine size `5`
  - minimized size histogram `{35: 9}`
  - so unlike the reverse upper branch, the forward upper branch has no cube-trap split; the entire completion side stays in the large propagated regime.

### Reformulations
- The cross-`n` all-killer object should be compared under the tail embedding
  `P0..P5 fixed`, `Q -> Q-1`, `Q-k -> Q-(k+1)`.
  That is the first embedding under which the base-family forced spines look
  mostly preserved rather than reconfigured.

LOAD-BEARING ASSESSMENT: High. This is now the default way to compare the residue across neighboring `n`.

- The upper-wiggle residue appears orientation-asymmetric:
  - reverse = mixed cube-trap / large-SCC completion branch,
  - forward = uniform large-SCC completion branch.

LOAD-BEARING ASSESSMENT: High. This suggests the variable part on top of the forced spine may need different models for forward and reverse branches.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Forward upper-wiggle family, `n = 9`:
  - command:
    `python3 probes/gpt/glb_case3c_fragment_anatomy.py --n-values 9 --orientation forward --include-upper-wiggle --timeout-ms 1200`
  - output highlights:
    - `forced_common_spine_size=28`
    - `common_spine_size=5`
    - `size_histogram={35: 9}`
    - `scc_histogram={(468,False):1,(501,False):1,(505,False):1,(509,False):1,(513,False):1,(514,False):1,(518,False):1,(522,False):1,(526,False):1}`
- Tail-shift comparison on base families:
  - command:
    `python3 probes/gpt/glb_case3c_spine_shift_compare.py --n-lo 9 --n-hi 10 --orientation both --timeout-ms 1200`
  - reverse:
    - `preserved=29`
    - `lost=8`
    - `gained=17`
  - forward:
    - `preserved=37`
    - `lost=19`
    - `gained=11`
  - sample preserved rules are dominated by the fixed bottom block plus nearby corridor rules; sample gains are concentrated near `Q`, `Q-1`, `Q-2`, `Q-3`.

STRUCTURAL RESULTS:
- The tail-shift embedding captures real cross-`n` preservation on the base families.
- The forward upper branch is structurally cleaner than the reverse upper branch: no small cube-trap residue remains after conditioning on completion.
- The variable completion residue is now clearly orientation-dependent even within the same three-sweep grammar.

TOOLS:
- Added `probes/gpt/glb_case3c_spine_shift_compare.py`.
  - inputs:
    - neighboring `n` values
    - orientation
    - optional upper wiggle
  - outputs:
    - forced spine sizes before and after shift
    - preserved / lost / gained counts
    - sample preserved / lost / gained rules

REPRESENTATIONS:
- Tail-shift embedding:
  - preserve `P0..P5`
  - map `Q -> Q-1`
  - map `Q-k -> Q-(k+1)`
- Orientation split on the upper branch:
  - reverse upper = mixed small/large completion residue
  - forward upper = uniform large completion residue

### What Would Unblock This
- A symbolic explanation for why the forward upper branch has no cube-trap split while the reverse upper branch does.
- A way to compute the tail-shift-preserved forced spine directly, without re-running the full exact collector at both `n` values.
- A tail-embedded comparison for the upper branches across `n`, if the exact cost can be reduced enough to make `n = 10` practical there.

### Key Parameters
- Exact anatomy completed:
  - forward upper-wiggle at `n = 9`
- Exact shift comparison completed:
  - base reverse `n = 9 -> 10`
  - base forward `n = 9 -> 10`
- Still not completed exactly:
  - upper-wiggle cross-`n` spine comparison

### Open Questions
- Can the tail-shift-preserved part of the spine be generated by one explicit corridor rule family?
- What exact local asymmetry creates the reverse-only cube-trap branch?
- Does the forward upper family remain cleaner than reverse at `n = 10`, or does that asymmetry disappear at the next size?

## Synthesis after exploration 4

The starpower path is narrower now, but also more credible. The forced spine is
not just overlapping across `n`; under the right tail embedding, a large chunk
is literally preserved. That is the first real sign of an all-`n` corridor
generator. The remaining difficulty is not "is there structure?" but "can we
separate the preserved corridor spine from the orientation-dependent variable
residue without exact completion?" That is now the central technical question.

## Exploration 5

### Strategy
Resolve the exact-versus-seeded forced-spine discrepancy before doing any more asymptotic extrapolation, and determine whether it reflects real mathematical structure or only a bad choice of coordinates.

### Outcome
SUCCEEDED

### Failure Constraint
Raw forced singleton maps are not canonical on the forward branch. Even with the same state vector and mover word, the seeded good-cycle solver can return isomorphic cycles with different local state labels, so any argument based on raw anchored-rule intersections will mix solver-choice noise with real residue structure.

### What This Rules Out
This rules out any future all-`n` story that treats unnormalized raw rule sets as the invariant object. That includes raw common-spine counts, raw cross-`n` overlaps, and any attempt to infer asymptotic growth directly from those quantities without first quotienting label symmetry.

### Surviving Structure
- The reverse base family remains stable in raw coordinates:
  - exact collector common forced spine at `n = 9`: `37`
  - seeded-only recomputation on the same six completion assignments: also `37`
- The forward base family exposes the coordinate bug sharply:
  - exact collector common forced spine at `n = 9`: `56`
  - seeded-only recomputation on the same three completion assignments: `66`
  - for assignment `(0,0)`, both paths produce `95` forced singleton rules, but the raw rule sets differ
- The discrepancy is representational, not structural:
  - two forward `(0,0)` cycles produced by different seeded-solver call histories are not equal as raw cycles
  - after processorwise first-appearance relabeling along the anchored cycle, the normalized cycles become equal
  - after the same normalization, the corresponding forced singleton maps become exactly equal

### Reformulations
The invariant object is not the raw anchored rule set, but the cycle-normalized forced singleton spine. The normalization is:
- anchor the cycle at the all-zero configuration as before
- for each processor independently, relabel local states in the order of first appearance along the cycle, with state `0` fixed first
- transport forced rules through those processorwise permutations

LOAD-BEARING ASSESSMENT: yes. This changes the effective search space because it separates actual residue structure from solver-label symmetry. Without this normalization, forward-branch spine data is not reproducible enough to support an all-`n` conjecture.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse base `n = 9`, exact collector:
  - completion assignments: `(1,0)`, `(1,1)`, `(1,2)`, `(2,0)`, `(2,1)`, `(2,2)`
  - each has forced size `95`
  - raw common forced spine size `37`
- Forward base `n = 9`, discrepancy witness:
  - completion assignments: `(0,0)`, `(0,1)`, `(0,2)`
  - each has forced size `95`
  - exact-collector raw common forced spine size `56`
  - seeded-only raw common forced spine size `66`
- Forward base `n = 9`, single-assignment normalization witness:
  - assignment `(0,0)`
  - raw cycle equality between two solver paths: false
  - normalized cycle equality after first-appearance relabeling: true
  - raw forced-map equality: false
  - normalized forced-map equality: true

STRUCTURAL RESULTS:
- Reverse base raw spine counts are already stable under the tested solver paths.
- Forward base raw spine counts are solver-choice dependent.
- Cycle-induced first-appearance normalization removes that dependence at the single-assignment level.

TOOLS:
- Temporary normalization probe implemented in ad hoc Python snippets during this exploration.
- These probes use existing `solve_good_cycle_from_movers(...)` and `build_initial_domains_from_cycle(...)` outputs and add only a processorwise state relabeling layer.

REPRESENTATIONS:
- Raw anchored-rule coordinates are insufficient on their own because they do not quotient local label symmetry.
- Cycle-induced state normalization is now the default coordinate system for future spine comparisons.

### What Would Unblock This
- A reusable script or extension of `glb_case3c_fragment_anatomy.py` that emits normalized forced common spines, normalized unions, and normalized cross-`n` tail-shift comparisons.
- The smallest useful next dataset is:
  - normalized base-family spine summaries for `n = 9, 10`
  - normalized forward-upper `n = 9` summary
  - a check whether the exact/seeded discrepancy disappears for all assignments, not just the `(0,0)` witness

### Key Parameters
- Exact reverse-base check completed at `n = 9`.
- Exact forward-base discrepancy check completed at `n = 9`.
- Normalization witness completed at `n = 9`, forward orientation, assignment `(0,0)`.
- No new `n = 10+` exact completion was attempted in this exploration; the focus was representational cleanup.

### Open Questions
- After normalization, does the forward base common spine move from `56` up to the seeded-only `66`, or to some third canonical value once all exact assignments are normalized together?
- Does the same label-symmetry issue contaminate the upper-wiggle branches, especially the forward upper family?
- Once normalized, do the `n = 9 -> 10` tail-shift preservation counts improve enough to sharpen the corridor-generator picture?

## Synthesis after exploration 5

This is real progress, not bookkeeping. The project was in danger of mistaking
solver label choices for mathematical growth. Exploration 5 shows that at least
part of the apparent variability is coordinate noise, and it gives a concrete
way to remove that noise. So the starpower path is still open, but the object
to track has changed again: not raw fragments, not raw forced spines, but
normalized forced spines in tail-shift coordinates. If that object stabilizes,
the all-`n` corridor story becomes plausible again. If it still grows without
pattern after normalization, then we are much closer to the real end of the
road.

## Exploration 6

### Strategy
Push the new normalization all the way through the exact anatomy and tail-shift tools, then check whether the base-family corridor signal strengthens and whether the upper-branch asymmetry survives in canonical coordinates.

### Outcome
SUCCEEDED

### Failure Constraint
Normalization does not make the whole residue uniform. It removes solver-label noise, but it does not erase the genuine orientation split on the upper branch: reverse upper still contains a small cube-trap residue while forward upper does not.

### What This Rules Out
This rules out the overly optimistic variant of the starpower story in which normalization alone makes every branch look like one rigid corridor family. Any all-`n` verifier still has to encode a real orientation-dependent correction term for the upper branch.

### Surviving Structure
- The base families become dramatically cleaner after normalization:
  - reverse base `n = 9`: normalized common spine `43`
  - reverse base isolated `n = 10`: normalized common spine `52`
  - forward base `n = 9`: normalized common spine `72`
  - forward base `n = 10`: normalized common spine `81`
- Tail-shift preservation is now strong enough to look like a corridor generator:
  - reverse base `n = 9 -> 10`: all `43/43` shifted rules survive, with exactly `9` genuinely new rules
  - forward base `n = 9 -> 10`: `67/72` shifted rules survive, with `5` losses and `14` gains concentrated near the top tail
- The upper branches remain asymmetric in canonical coordinates:
  - reverse upper `n = 9`: normalized common spine `34`, mixed completion residue `6/35`
  - forward upper `n = 9`: normalized common spine `61`, uniform completion residue `35`

### Reformulations
The strongest current candidate for a residue-style all-`n` invariant is now:
- cycle-normalized forced singleton spine
- compared only after tail-shift embedding
- with a separate orientation-dependent correction on the upper branch

LOAD-BEARING ASSESSMENT: yes. This is the first representation that simultaneously:
- removes the forward-branch label artifact,
- makes reverse base preservation exact under `n = 9 -> 10`,
- and keeps the true upper-branch asymmetry visible instead of averaging it away.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Base families, normalized common spine sizes:
  - reverse base `n = 9`: `43`
  - reverse base isolated `n = 10`: `52`
  - forward base `n = 9`: `72`
  - forward base `n = 10`: `81`
- Base families, normalized tail-shift comparison:
  - reverse `n = 9 -> 10`: `preserved = 43`, `lost = 0`, `gained = 9`
  - forward `n = 9 -> 10`: `preserved = 67`, `lost = 5`, `gained = 14`
- Upper families, normalized common spine sizes at `n = 9`:
  - reverse upper: `34`
  - forward upper: `61`
- Reverse upper `n = 9` completion split remains:
  - `4` completion-unsat assignments at fragment size `6`
  - `14` completion-unsat assignments at fragment size `35`
- Forward upper `n = 9` completion split remains uniform:
  - `9` completion-unsat assignments, all at fragment size `35`

STRUCTURAL RESULTS:
- Reverse base preservation under normalized tail shift is exact from `n = 9` to `n = 10`.
- Forward base is not exact, but the defect is small and tail-local.
- Upper-branch asymmetry is structural, not an artifact of label choice.

TOOLS:
- `glb_case3c_fragment_anatomy.py` now emits normalized forced common spines, unions, and processor histograms.
- `glb_case3c_spine_shift_compare.py` now defaults to normalized mode and can still be forced to raw mode with `--raw`.
- Added regression test `probes/gpt/tests/test_glb_case3c_fragment_anatomy.py` for cycle-normalization invariance under local state relabeling.

REPRESENTATIONS:
- Normalized tail-shift spine is now the default coordinate system for all future corridor comparisons.
- Raw anchored rules remain useful only as a debugging view.

### What Would Unblock This
- The next useful dataset is an exact or symbolic description of the `9` gained reverse-base rules and the `5/14` forward defect under tail shift, expressed as local corridor extension rules.
- After that, the right next test is `n = 10 -> 11` in normalized tail-shift coordinates on the base families only.
- For the upper branch, the useful next object is not more raw counts but a normalized explanation of the reverse-only `6`-rule cube-trap residue.

### Key Parameters
- Exact normalized anatomy completed:
  - base reverse `n = 9, 10`
  - base forward `n = 9, 10`
  - upper reverse `n = 9`
  - upper forward `n = 9`
- Exact normalized tail-shift comparison completed:
  - base reverse `n = 9 -> 10`
  - base forward `n = 9 -> 10`
- One mixed all-family run reported reverse base `n = 10` normalized size `51`, but fresh isolated reruns stabilized at `52`; use isolated family values for conclusions.

### Open Questions
- Are the `9` reverse-base gains from `n = 9 -> 10` one explicit top-tail rule family?
- Can the forward-base `5` losses and `14` gains be expressed as one finite correction to the reverse corridor generator?
- Does reverse base remain exact under normalized tail shift at `n = 10 -> 11`?
- Can the reverse upper `6`-rule cube-trap residue be derived from the same normalized spine plus one short exceptional gadget?

## Synthesis after exploration 6

This is the first exploration where the starpower story starts to look
mathematically serious again. The base families now have a plausible invariant:
normalized tail-shift spines. On reverse base it is exact across `n = 9 -> 10`;
on forward base it is exact up to a small finite tail defect. That is the right
shape for a residue-style verifier. At the same time, the upper branch stayed
asymmetric after normalization, which is good news in a different way: it means
the remaining complexity is probably localized, not diffuse. The next step is
no longer "collect more raw data." It is "write the gained/lost tail rules as
explicit corridor extensions and isolate the reverse-only exceptional gadget."

## Exploration 7

### Strategy
Inventory the exact gained and lost normalized tail rules on the base families under `n = 9 -> 10`, to test whether the remaining `n`-dependence is a finite local edit or still diffuse once written out explicitly.

### Outcome
SUCCEEDED

### Failure Constraint
The forward branch is not explained by "append a new `Q` layer and leave the old tail untouched." Its normalized defect changes both `Q` and `Q-1`, so any recursive verifier that assumes the previous top-tail rules stay fixed will fail on forward base.

### What This Rules Out
This rules out the simplest one-line recursion in which `n -> n+1` merely adds a fresh `Q` copy of old top-tail rules. The forward branch requires an explicit correction term on the former top processor as well.

### Surviving Structure
- Reverse base is as clean as it looked in the counts:
  - no lost rules at all
  - exactly `9` gained rules
  - all gains occur at `Q` or `Q-2`
- Forward base is still finite and local:
  - all `5` losses occur at `Q-1`
  - all `14` gains occur at `Q` or `Q-1`
  - there are no defects deeper in the ring

### Reformulations
The right `n -> n+1` object is now a tail-edit inventory:
- preserved normalized spine under tail shift
- plus a finite gained set
- minus a finite lost set

LOAD-BEARING ASSESSMENT: yes. This is the first representation that makes the remaining growth look like an explicit recursive update rule rather than a new global recomputation.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse base normalized gains from `n = 9 -> 10`:
  - `('Q', (0, 0, 0), 0)`
  - `('Q', (0, 0, 1), 1)`
  - `('Q', (0, 1, 1), 1)`
  - `('Q', (1, 1, 1), 1)`
  - `('Q-2', (1, 1, 2), 2)`
  - `('Q-2', (1, 2, 2), 2)`
  - `('Q-2', (2, 0, 0), 0)`
  - `('Q-2', (2, 2, 0), 0)`
  - `('Q-2', (2, 2, 2), 2)`
- Reverse base normalized losses from `n = 9 -> 10`:
  - none
- Forward base normalized losses from `n = 9 -> 10`:
  - `('Q-1', (0, 0, 1), 0)`
  - `('Q-1', (0, 2, 1), 0)`
  - `('Q-1', (1, 0, 1), 1)`
  - `('Q-1', (2, 1, 0), 2)`
  - `('Q-1', (2, 2, 0), 2)`
- Forward base normalized gains from `n = 9 -> 10`:
  - `('Q', (0, 0, 0), 0)`
  - `('Q', (0, 0, 1), 0)`
  - `('Q', (0, 2, 1), 0)`
  - `('Q', (1, 0, 1), 1)`
  - `('Q', (1, 1, 0), 1)`
  - `('Q', (1, 1, 1), 1)`
  - `('Q', (2, 1, 0), 2)`
  - `('Q', (2, 2, 0), 2)`
  - `('Q', (2, 2, 1), 2)`
  - `('Q-1', (0, 0, 2), 0)`
  - `('Q-1', (0, 2, 2), 0)`
  - `('Q-1', (1, 0, 0), 1)`
  - `('Q-1', (2, 1, 1), 2)`
  - `('Q-1', (2, 2, 2), 2)`

STRUCTURAL RESULTS:
- The reverse base tail defect is a pure extension: add `4` new `Q` rules and `5` new `Q-2` rules.
- The forward base tail defect is a finite replacement localized to `Q-1` plus a new `Q` layer.
- In both orientations, the normalized defect is entirely top-tail local.

TOOLS:
- Reused `glb_case3c_spine_shift_compare.py` in normalized mode to compute exact gained/lost inventories.
- No new code was needed beyond the normalized collector added in exploration 6.

REPRESENTATIONS:
- Tail-edit inventory is now the best format for writing a candidate recursive extension theorem.

### What Would Unblock This
- The next useful object is a symbolic generator that reproduces these reverse gains and forward gain/loss edits from the tail grammar directly.
- The smallest decisive next computation is `n = 10 -> 11` on the base families in the same normalized tail-edit format.

### Key Parameters
- Exact normalized gained/lost inventory completed for base reverse `n = 9 -> 10`.
- Exact normalized gained/lost inventory completed for base forward `n = 9 -> 10`.
- No upper-branch cross-`n` inventory was attempted here.

### Open Questions
- Do the reverse `Q-2` gains come from one explicit "new ternary corridor" rule family?
- Is the forward `Q-1` replacement exactly the same local template at every higher `n`, or does it still drift?
- Does the reverse pure-extension pattern survive at `n = 10 -> 11`?

## Synthesis after exploration 7

The project finally has something close to a recursive object. The normalized
base-family change is not a cloud of differences; it is a finite tail edit.
Reverse base is especially close to a theorem: preserve everything under tail
shift, then add nine explicit rules. Forward base is messier but still local:
replace five `Q-1` rules, add a new `Q` layer, and keep the rest. That is much
closer to the `residue` paradigm than where this started. The bottleneck is no
longer finding structure. It is deciding whether these edits are already the
final rule schema or just the first two terms of something that will keep
drifting with `n`.

## Exploration 8

### Strategy
Test whether the exact normalized tail-shift method can be pushed one step further to reverse base `n = 10 -> 11`, since that is the first size where a real recursive update law would start to look credible.

### Outcome
STALLED

### Failure Constraint
The exact normalized collector is now too slow for interactive continuation at `n = 11`. A reverse-base-only `10 -> 11` run did not finish in a reasonable interactive window, even after the normalization and family isolation work.

### What This Rules Out
This rules out "just keep running the exact collector one more step" as the default discovery loop. Exact completion is still valuable for confirmation at selected sizes, but it cannot be the main engine for discovering the all-`n` update law.

### Surviving Structure
- Nothing broke mathematically; the stall is computational.
- The best surviving path is now clear:
  - use the normalized seeded-only probe to scout higher-`n` forced spines cheaply
  - keep exact completion for spot checks and confirmation at the sizes where it still returns

### Reformulations
The computational split is now explicit:
- discovery representation: normalized seeded-only forced spines on predicted completion branches
- confirmation representation: exact normalized completion-killed spines where feasible

LOAD-BEARING ASSESSMENT: yes. This is the same division of labor that made `residue` useful: cheap large-`n` reconnaissance plus exact checks at lower anchor points.

### Concrete Artifacts
STRUCTURAL RESULTS:
- Reverse base `n = 10 -> 11` exact normalized shift comparison is beyond practical interactive runtime with the current collector.

TOOLS:
- No new code from this exploration.
- Operational takeaway: future higher-`n` probes should avoid exact completion in the inner loop.

### What Would Unblock This
- A normalized seeded-only probe that reuses the exact bottom-wiggle split and emits canonical forced spines at `n = 11, 12, ...` without running SMT completion.
- The smallest useful next target is reverse base `n = 11` in normalized seeded-only coordinates, compared against the exact `n = 10` normalized spine.

### Key Parameters
- Attempted exact normalized comparison:
  - reverse base `n = 10 -> 11`
- Result:
  - did not complete in a reasonable interactive window

### Open Questions
- Does the seeded-only normalized probe predict the same nine-rule reverse extension at `n = 10 -> 11`?
- Can the forward defect be scouted the same way, or does it need more exact anchoring?

## Synthesis after exploration 8

This is a useful failure. The exact collector got us far enough to identify the
right invariant and the first explicit tail edits, but it is no longer the
right discovery engine. That does not weaken the project; it clarifies the
workflow. From here on, higher-`n` exploration should look more like
`residue`: cheap normalized reconnaissance to spot the pattern, then exact
confirmation where the runtime is still acceptable.

## Exploration 9

### Strategy
Replace the stalled exact `n = 11` continuation with a cheaper normalized seeded-only probe, and test whether it can scout higher-`n` tail edits faithfully enough to keep the recursive story moving.

### Outcome
PARTIAL

### Failure Constraint
The normalized seeded-only probe is not a universal surrogate for exact completion. On reverse base it already overstates the common spine at `n = 9` and `n = 10`, so reverse-base claims cannot be read directly off the probe.

### What This Rules Out
This rules out a naive `residue`-style story in which one cheap scout replaces all exact anchors. The probe can generate hypotheses, but reverse-base confirmation still needs exact completion or an explicit symbolic theorem.

### Surviving Structure
- The probe works well on forward base:
  - `n = 10` normalized common spine size `81`, matching the exact anchor from exploration 6
  - `n = 11` normalized common spine size `90`
  - the normalized `10 -> 11` tail defect is exactly the same `5` losses and `14` gains seen at exact `9 -> 10`
- The probe is not faithful enough on reverse base:
  - `n = 9` probe normalized common spine `60` versus exact `43`
  - `n = 10` probe normalized common spine `69` versus exact isolated `52`
  - `n = 11` probe continues with a larger spine (`78`) and a different tail-edit pattern (`10` losses, `19` gains), so it is a heuristic over-approximation, not a certificate

### Reformulations
The cheap probe now has a narrower but still useful role:
- forward base: conjecture generator with strong anchor agreement
- reverse base: heuristic scout only

LOAD-BEARING ASSESSMENT: yes, but asymmetric. This does not solve the all-`n` problem, but it gives a credible way to keep collecting higher-`n` data on the forward branch while isolating the reverse branch as the remaining hard case.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Forward base normalized seeded-only common spines:
  - `n = 10`: `81`
  - `n = 11`: `90`
- Forward base normalized seeded-only `10 -> 11` defect:
  - losses:
    - `('Q-1', (0, 0, 1), 0)`
    - `('Q-1', (0, 2, 1), 0)`
    - `('Q-1', (1, 0, 1), 1)`
    - `('Q-1', (2, 1, 0), 2)`
    - `('Q-1', (2, 2, 0), 2)`
  - gains:
    - `('Q', (0, 0, 0), 0)`
    - `('Q', (0, 0, 1), 0)`
    - `('Q', (0, 2, 1), 0)`
    - `('Q', (1, 0, 1), 1)`
    - `('Q', (1, 1, 0), 1)`
    - `('Q', (1, 1, 1), 1)`
    - `('Q', (2, 1, 0), 2)`
    - `('Q', (2, 2, 0), 2)`
    - `('Q', (2, 2, 1), 2)`
    - `('Q-1', (0, 0, 2), 0)`
    - `('Q-1', (0, 2, 2), 0)`
    - `('Q-1', (1, 0, 0), 1)`
    - `('Q-1', (2, 1, 1), 2)`
    - `('Q-1', (2, 2, 2), 2)`
- Reverse base normalized seeded-only spine sizes:
  - `n = 9`: `60`
  - `n = 10`: `69`
  - `n = 11`: `78`

STRUCTURAL RESULTS:
- The forward base tail edit appears stable from exact `9 -> 10` to seeded-only `10 -> 11`.
- The reverse base remains the unresolved branch for any all-`n` claim.

TOOLS:
- `glb_case3c_forced_spine_probe.py` now emits normalized common spines, normalized unions, and processor histograms on the predicted completion branch.
- Added regression test `probes/gpt/tests/test_glb_case3c_forced_spine_probe.py`.

REPRESENTATIONS:
- Cheap normalized probe is now part of the toolbox, but only with explicit branch-dependent trust labels.

### What Would Unblock This
- A canonical reverse-base cycle selector, or a symbolic theorem that recovers the exact reverse completion-killed spine from the larger seeded-only over-approximation.
- The smallest useful next artifact is a direct comparison between the exact reverse-base `52`-rule spine at `n = 10` and the probe’s `69`-rule spine, classified into "true exact core" versus "spurious seeded-only surplus."

### Key Parameters
- Normalized seeded-only probe completed:
  - base reverse `n = 10, 11`
  - base forward `n = 10, 11`
- Exact anchor available for comparison:
  - reverse `n = 9, 10`
  - forward `n = 9, 10`

### Open Questions
- Can the reverse probe surplus be characterized by one local family that exact completion always deletes?
- Is the forward branch now effectively solved at the recursive-edit level, pending one more exact spot check?
- Can a canonical cycle selection collapse the reverse probe from `69` back to the exact `52` at `n = 10`?

## Synthesis after exploration 9

The project has now split cleanly into two subproblems. Forward base is acting
like a genuine recursive residue family: the same normalized `5/14` tail edit
shows up again at `10 -> 11`, and the cheap probe agrees with the exact anchor
at `n = 10`. Reverse base is the remaining obstacle. It still has excellent
structure in the exact `9 -> 10` data, but the cheap probe inflates it. So the
starpower path is no longer "find one uniform all-killer immediately." It is
"finish forward as a recursive family, then isolate what exact completion is
deleting from the larger reverse seeded-only spine."

## Exploration 10

### Strategy
Directly compare the exact reverse-base normalized common spines at `n = 9,10` against the probe output in the same process, to determine whether the reverse mismatch is structural or only a consequence of which seeded cycle model gets selected.

### Outcome
SUCCEEDED

### Failure Constraint
The reverse mismatch is not yet solved, but its source has narrowed: it is a model-selection problem inside the seeded cycle solver. A fresh-process probe can inflate the reverse spine, while the same probe run after the exact collector collapses to the exact anchors.

### What This Rules Out
This rules out the interpretation that the reverse probe is discovering a genuinely larger competing residue family. The bad news is now narrower: we do not need a new reverse theory, we need a canonical way to choose the right seeded cycle.

### Surviving Structure
- Reverse exact/probe comparison in the same process:
  - `n = 9`: exact `43`, probe `43`
  - `n = 10`: exact `52`, probe `52`
- So the reverse probe surplus from exploration 9 is not an invariant of the family; it depends on solver history.

### Reformulations
The reverse-base problem is now best reformulated as:
- find a canonical seeded cycle selector whose normalized forced spine matches the exact completion-killed anchor
- then run that selector cheaply at higher `n`

LOAD-BEARING ASSESSMENT: yes. This is a major narrowing of the hard part. A canonical cycle selector is a much smaller target than a new reverse obstruction theorem from scratch.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse base exact/probe equality in one process:
  - `n = 9`: `exact = 43`, `probe = 43`, `surplus = 0`, `missing = 0`
  - `n = 10`: `exact = 52`, `probe = 52`, `surplus = 0`, `missing = 0`

STRUCTURAL RESULTS:
- Reverse probe inflation is solver-history dependent.
- Reverse exact and seeded-only normalized spines can coincide exactly when the cycle solver is steered into the exact-compatible model choice.

TOOLS:
- No new code in this exploration.
- Methodologically, exact-first warmup is now a debugging tool for validating candidate canonical selectors.

REPRESENTATIONS:
- Reverse mismatch should be studied in cycle-selector space, not in rule-space first.

### What Would Unblock This
- A deterministic canonical cycle selector for the seeded good-cycle solver, ideally something cheap like lexicographic normalization or a secondary optimization on the normalized cycle word.
- The smallest useful next experiment is to add one canonical tie-breaker to the seeded cycle solver and test whether fresh-process reverse probe values drop from `60/69` to `43/52`.

### Key Parameters
- Compared reverse base `n = 9,10`.
- Exact collector and probe executed in the same Python process.

### Open Questions
- What is the minimal tie-breaker that forces the exact-compatible reverse cycle?
- Does the same issue affect forward at all, or is forward already uniquely selected after normalization?
- If a canonical selector is found at `n = 9,10`, does it keep the forward `5/14` edit stable at `n = 11`?

## Synthesis after exploration 10

This is the best news on the reverse branch so far. The hard part is no longer
"exact completion deletes some mysterious surplus rules." The hard part is
"fresh seeded solving sometimes picks the wrong representative cycle." That is
a much smaller engineering and mathematical problem. If we can pin down one
cheap canonical selector that lands on the exact-compatible cycle, then the
cheap higher-`n` probe becomes relevant on the hard branch too, and the whole
starpower project gets much more realistic.

## Exploration 11

### Strategy
Prototype a canonical seeded-cycle selector by lexicographically minimizing the anchored cycle, then test whether that removes the reverse fresh-process mismatch and yields a stable `10 -> 11` recursive edit on both base orientations.

### Outcome
SUCCEEDED

### Failure Constraint
No failure on the base families tested. The remaining question is generality: we have not yet checked whether lexicographic selection remains compatible with exact completion outside the tested base orientations and sizes.

### What This Rules Out
This rules out the pessimistic view that reverse needs a fundamentally different high-`n` theory than forward. At least on the base family, a canonical selector is enough to restore the recursive pattern.

### Surviving Structure
- Reverse branch, fresh-process lexmin probe:
  - `n = 9` normalized common spine `43`, matching exact
  - `n = 10` normalized common spine `52`, matching exact
  - `n = 11` normalized common spine `61`
  - normalized `10 -> 11` tail defect:
    - losses: none
    - gains: the same `9` rules seen at exact `9 -> 10`
- Forward branch, fresh-process lexmin probe:
  - `n = 10` normalized common spine `81`
  - `n = 11` normalized common spine `90`
  - normalized `10 -> 11` tail defect:
    - the same `5` losses and `14` gains seen before

### Reformulations
The canonical probe is now:
- seeded good-cycle constraints
- plus lexicographic minimization of the anchored flattened cycle
- plus cycle-normalized forced singleton extraction

LOAD-BEARING ASSESSMENT: yes. This is the first cheap selector that matches the exact reverse anchors and preserves the forward recursive edit. It is now the leading candidate discovery engine for the base families.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse lexmin normalized common spine sizes:
  - `n = 9`: `43`
  - `n = 10`: `52`
  - `n = 11`: `61`
- Reverse lexmin normalized `10 -> 11` gains:
  - `('Q', (0, 0, 0), 0)`
  - `('Q', (0, 0, 1), 1)`
  - `('Q', (0, 1, 1), 1)`
  - `('Q', (1, 1, 1), 1)`
  - `('Q-2', (1, 1, 2), 2)`
  - `('Q-2', (1, 2, 2), 2)`
  - `('Q-2', (2, 0, 0), 0)`
  - `('Q-2', (2, 2, 0), 0)`
  - `('Q-2', (2, 2, 2), 2)`
- Forward lexmin normalized `10 -> 11` edit:
  - losses: the same `5` `Q-1` rules as exploration 9
  - gains: the same `14` `Q/Q-1` rules as exploration 9

STRUCTURAL RESULTS:
- Reverse base now exhibits the same recursive nine-rule pure extension at both `9 -> 10` and `10 -> 11`.
- Forward base keeps the same recursive `5/14` edit at both `9 -> 10` and `10 -> 11`.

TOOLS:
- Temporary lexicographic `z3.Optimize` prototype used in ad hoc Python code during this exploration.

REPRESENTATIONS:
- Lexmin anchored cycle is now the preferred representative of a seeded good-cycle class on the base family.

### What Would Unblock This
- The next step is to turn the lexicographic selector into a reusable function in the codebase and replace the plain seeded-only probe with a selector-aware version.
- After that, the smallest decisive computation is lexmin base-family scouting at `n = 12` and beyond, with occasional exact spot checks where feasible.

### Key Parameters
- Tested base orientations:
  - reverse `n = 9,10,11`
  - forward `n = 10,11`
- Selector:
  - lexicographic minimization of the flattened anchored cycle

### Open Questions
- Does lexicographic selection also stabilize the upper branches, or only the base families?
- Is there a cheaper tie-breaker than full lexicographic optimization that produces the same representative?
- How far does the reverse `+9` pure-extension pattern persist?

## Synthesis after exploration 11

This is the first moment where the starpower story looks genuinely credible
end-to-end on the base families. We now have a cheap selector that appears to
recover the exact reverse anchors and extends the same recursive edits one step
higher on both orientations. Reverse is no longer the hard branch in the same
sense; the hard branch is now "prove that lexmin is selecting the right cycle,"
or replace it with an equivalent but cheaper canonical rule. That is a much
better problem to have.

## Exploration 12

### Strategy
Stress-test the lexmin-recursive base-family law by pushing it beyond `n = 11`, checking whether the same reverse `+9` pure extension and forward `5/14` edit persist at `11 -> 12` and `12 -> 13`.

### Outcome
SUCCEEDED

### Failure Constraint
No new failure on the tested base families. The remaining limitation is epistemic, not computational: we now need exact spot checks or a proof that lexmin continues to pick the exact-compatible cycle at higher `n`.

### What This Rules Out
This rules out the concern that the observed recursive edits were just a `9 -> 10` or `10 -> 11` accident. On the tested base family, the edit law is now stable across four consecutive steps.

### Surviving Structure
- Reverse lexmin base recurrence:
  - spine sizes `43, 52, 61, 70, 79` for `n = 9,10,11,12,13`
  - each step preserves the full shifted spine
  - each step gains exactly the same `9` rules
- Forward lexmin base recurrence:
  - spine sizes `72, 81, 90, 99, 108` for `n = 9,10,11,12,13`
  - each step loses exactly the same `5` rules
  - each step gains exactly the same `14` rules

### Reformulations
The base-family all-`n` candidate is now naturally expressed as:
- reverse base:
  - size law `|S_n| = 9n - 38`
  - update law `S_{n+1} = shift(S_n) union G_rev`
  - with fixed gain set `G_rev` of size `9`
- forward base:
  - size law `|S_n| = 9n - 9`
  - update law `S_{n+1} = (shift(S_n) \\ L_fwd) union G_fwd`
  - with fixed loss set `L_fwd` of size `5` and fixed gain set `G_fwd` of size `14`

LOAD-BEARING ASSESSMENT: yes. This is the first truly compact all-`n` description in the project, even if it is still conjectural pending more exact anchoring.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse lexmin normalized sizes:
  - `n = 9`: `43`
  - `n = 10`: `52`
  - `n = 11`: `61`
  - `n = 12`: `70`
  - `n = 13`: `79`
- Forward lexmin normalized sizes:
  - `n = 9`: `72`
  - `n = 10`: `81`
  - `n = 11`: `90`
  - `n = 12`: `99`
  - `n = 13`: `108`
- Reverse lexmin edits:
  - `10 -> 11`: `0` losses, same `9` gains as exploration 11
  - `11 -> 12`: `0` losses, same `9` gains
  - `12 -> 13`: `0` losses, same `9` gains
- Forward lexmin edits:
  - `10 -> 11`: same `5` losses and `14` gains
  - `11 -> 12`: same `5` losses and `14` gains
  - `12 -> 13`: same `5` losses and `14` gains

STRUCTURAL RESULTS:
- Reverse base behaves like a fixed pure-extension grammar after lexmin selection.
- Forward base behaves like a fixed replacement grammar after lexmin selection.
- Both canonical base spines now have linear size growth with slope `9`.

TOOLS:
- Reused the lexmin probe machinery from exploration 11; no new code in this exploration.

REPRESENTATIONS:
- Fixed gain/loss sets plus linear size law is now the best summary of the base-family data.

### What Would Unblock This
- The next highest-value exact computation is one reverse-base exact spot check at `n = 11` if it can be made to finish offline, to validate the lexmin `61` anchor directly.
- Failing that, the next best step is a symbolic proof that lexmin selection enforces the same local top-tail pattern inductively.

### Key Parameters
- Tested lexmin base-family transitions:
  - `10 -> 11`
  - `11 -> 12`
  - `12 -> 13`
- Orientations:
  - reverse
  - forward

### Open Questions
- Can the reverse `+9` fixed gain set be proved directly from the lexmin constraints?
- Can the forward fixed `5/14` edit be proved directly from the lexmin constraints?
- Does the same lexmin stabilization extend to upper-wiggle families, or is the base family special?

## Synthesis after exploration 12

The base-family story is now unmistakably recursive. We are no longer looking
at scattered computational evidence; we have fixed update rules, linear growth
laws, and a canonical selector that reproduces the exact reverse anchors we can
check. That is extremely close to the `residue` paradigm the user wanted. The
remaining gap is not "is there a scalable object?" There is. The gap is "can we
justify that the lexmin selector is the right object, and how much of this
extends beyond the base family?"

## Exploration 13

### Strategy
Push the lexmin base-family recurrence as far as the current canonical probe budget allows, to determine whether we already have a meaningful large-range computational law or just another small-`n` phenomenon.

### Outcome
PARTIAL

### Failure Constraint
The current `1200 ms` lexmin budget stops being reliable near `n = 18`. At that point the optimizer either times out on some assignments or returns unstable non-canonical models, so the fixed-edit law is no longer reproducible by the current scout.

### What This Rules Out
This rules out any immediate claim like "verified to 2000" with the current implementation and timeout budget. The scalable object exists, but the present probe is not yet efficient enough to carry it to large `n` without further optimization or proof.

### Surviving Structure
- Stable verified range under current budget:
  - reverse base: exact same `+9` pure-extension law on every step from `n = 9 -> 10` through `n = 16 -> 17`
  - forward base: exact same `5` losses and `14` gains on every step from `n = 9 -> 10` through `n = 16 -> 17`
- Stable size ranges under current budget:
  - reverse: `43, 52, 61, 70, 79, 88, 97, 106, 115`
  - forward: `72, 81, 90, 99, 108, 117, 126, 135, 144`
- Breakdown beyond that range:
  - reverse `n = 18`: `5/6` assignments solved, size `124`
  - reverse `n = 19,20`: `0/6` assignments solved
  - forward `n = 18`: `3/3` assignments solved but size unstable across runs, indicating timeout-sensitive non-canonical output
  - forward `n = 19,20`: `0/3` assignments solved

### Reformulations
The current state is best expressed as a range-certified recurrence:
- computationally verified canonical law through `n = 17`
- optimizer wall at `n = 18+`

LOAD-BEARING ASSESSMENT: yes. This is not the end goal, but it is already a stronger, cleaner computational statement than the original verifier could make on the lower-bound side.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse verified sizes through `n = 17`:
  - `43, 52, 61, 70, 79, 88, 97, 106, 115`
- Forward verified sizes through `n = 17`:
  - `72, 81, 90, 99, 108, 117, 126, 135, 144`
- Reverse high-`n` diagnostics:
  - `n = 18`: `predicted assignments = 6`, `solved = 5`, `missing = 1`, size `124`
  - `n = 19`: `solved = 0`, size `0`
  - `n = 20`: `solved = 0`, size `0`
- Forward high-`n` diagnostics:
  - `n = 18`: `predicted assignments = 3`, `solved = 3`, but size unstable across runs (`153` in one fresh run, `176` in one range run)
  - `n = 19`: `solved = 0`, size `0`
  - `n = 20`: `solved = 0`, size `0`

STRUCTURAL RESULTS:
- The base-family recurrence is computationally robust through `n = 17`.
- The first visible failure mode beyond that is optimizer/runtime failure, not a clean counterexample to the recurrence.

TOOLS:
- Reused the lexmin probe from exploration 11.
- Added unbuffered range-run instrumentation via ad hoc shell/Python commands during this exploration.

REPRESENTATIONS:
- "Verified through `n = 17` at selector timeout `1200 ms`" is now the honest computational status line for the base-family lexmin law.

### What Would Unblock This
- Either:
  - a faster canonical selector than full lexicographic optimization, or
  - a much larger timeout budget / optimized encoding for the current selector, or
  - a proof that the fixed edit laws follow inductively once established at low `n`
- The smallest useful next computation is to rerun `n = 18` with a much larger timeout and see whether the stable laws return.

### Key Parameters
- Selector:
  - lexicographic `z3.Optimize`
- Timeout:
  - `1200 ms`
- Range tested:
  - base families through `n = 20`

### Open Questions
- Is `n = 18` purely a timeout wall, or does the canonical selector itself need refinement?
- How much larger a timeout is needed to recover the stable law at `n = 18`?
- Can the current verified-through-`17` statement already be packaged as the first real starpower computational claim?

## Synthesis after exploration 13

We now have both a success and a limit. The success is substantial: the
canonical base-family law is verified cleanly through `n = 17`, which is much
closer to a `residue`-style large-range computation than anything the project
had before. The limit is also clear: full lexicographic optimization is too
slow beyond that. So the next stage is not more blind range-pushing. It is
either making the selector cheaper, or proving that the stable low-`n` edit law
forces the higher-`n` one.

## Exploration 14

### Strategy
Escalate the lexmin timeout exactly at the first failure point (`n = 18`) to decide whether the apparent breakdown from exploration 13 reflects a real structural change or only insufficient optimization time.

### Outcome
SUCCEEDED

### Failure Constraint
No structural failure at `n = 18`. The earlier break was caused by insufficient optimization time, not by the recurrence law itself changing.

### What This Rules Out
This rules out the interpretation that `n = 18` marks a new base-family regime. The evidence now points to a selector-cost wall rather than a combinatorial wall.

### Surviving Structure
- Reverse `n = 17 -> 18` with timeout `5000 ms`:
  - all `6/6` assignments solved
  - normalized common spine size `124`
  - same `+9/0` edit
- Forward `n = 17 -> 18` with timeout `5000 ms`:
  - all `3/3` assignments solved
  - normalized common spine size `153`
  - same `5/14` edit

### Reformulations
The current base-family story is best phrased as a timeout-parameterized computational law:
- low timeout gives one verified range
- higher timeout extends the same fixed edit law farther out

LOAD-BEARING ASSESSMENT: yes. This is strong evidence that the canonical recurrence is genuinely the right structural object, even though the current selector is too expensive for very large `n`.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse `n = 17 -> 18` at timeout `5000 ms`:
  - `solved = 6`, `missing = 0`, size `124`
  - losses: none
  - gains: the same `9` reverse gain rules
- Forward `n = 17 -> 18` at timeout `5000 ms`:
  - `solved = 3`, `missing = 0`, size `153`
  - losses: the same `5` forward loss rules
  - gains: the same `14` forward gain rules

STRUCTURAL RESULTS:
- The base-family recurrence survives past the `n = 17` boundary when enough optimization time is provided.
- Exploration 13’s apparent `n = 18` break was computational, not structural.

TOOLS:
- Reused the lexmin probe with a larger timeout budget.

REPRESENTATIONS:
- Timeout is now part of the computational specification of the current probe.

### What Would Unblock This
- The next decisive computation is `n = 19` with the larger timeout budget, to see how quickly the selector cost continues to grow.
- A cheaper canonical selector would matter more than further brute-force timeout escalation.

### Key Parameters
- Selector:
  - lexicographic `z3.Optimize`
- Timeouts compared:
  - `1200 ms`
  - `5000 ms`
- Transition tested:
  - base-family `n = 17 -> 18`

### Open Questions
- How far does the stable law persist at timeout `5000 ms`?
- Can a weaker tie-breaker recover the same canonical cycle at much lower cost?

## Synthesis after exploration 14

This is a strong correction to the apparent wall from exploration 13. The
recurrence did not fail at `n = 18`; the timeout did. That means the base
family story is already better than "verified through `17`." It is "verified
through `17` cheaply, and still holding at `18` when more optimization time is
spent." The next bottleneck is now purely computational: making the canonical
selector cheaper or proving that once established, the fixed edit law continues.

## Exploration 15

### Strategy
Push the higher-timeout lexmin probe one more step to `n = 19`, to see whether the recovered `n = 18` law was just a one-step rescue or the beginning of a larger-range continuation.

### Outcome
SUCCEEDED

### Failure Constraint
No new structural failure at `n = 19` under the larger timeout. The remaining issue is still selector cost, not a changed law.

### What This Rules Out
This rules out the idea that `n = 18` was a special one-off recovery. The same fixed edit laws persist one step farther at the higher budget.

### Surviving Structure
- Reverse `n = 18 -> 19` at timeout `5000 ms`:
  - all `6/6` assignments solved
  - normalized common spine size `133`
  - same `+9/0` edit
- Forward `n = 18 -> 19` at timeout `5000 ms`:
  - all `3/3` assignments solved
  - normalized common spine size `162`
  - same `5/14` edit

### Reformulations
The computational story is now:
- cheap budget verifies the canonical law through `n = 17`
- medium budget extends the same canonical law through at least `n = 19`

LOAD-BEARING ASSESSMENT: yes. This is now much closer to the kind of range-dependent verification statement that could plausibly be pushed much farther with engineering work.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse size progression at timeout `5000 ms`:
  - `n = 18`: `124`
  - `n = 19`: `133`
- Forward size progression at timeout `5000 ms`:
  - `n = 18`: `153`
  - `n = 19`: `162`
- Reverse `n = 18 -> 19`:
  - losses: none
  - gains: the same `9` reverse gain rules
- Forward `n = 18 -> 19`:
  - losses: the same `5` forward loss rules
  - gains: the same `14` forward gain rules

STRUCTURAL RESULTS:
- The higher-timeout canonical law is stable through `n = 19` on the base families.
- No new edit pattern has appeared.

TOOLS:
- Reused the lexmin probe at timeout `5000 ms`.

REPRESENTATIONS:
- Verified range should now be indexed by selector budget, not just by `n`.

### What Would Unblock This
- The next clean computation is `n = 20` at the same higher timeout.
- Longer-term, the key improvement is still a cheaper canonical selector.

### Key Parameters
- Selector:
  - lexicographic `z3.Optimize`
- Timeout:
  - `5000 ms`
- Transition tested:
  - base-family `n = 18 -> 19`

### Open Questions
- Does the same fixed law survive at `n = 20` under timeout `5000 ms`?
- How quickly does runtime grow with `n` under the current selector?

## Synthesis after exploration 15

The important update is that the recovery at `18` was not a fluke. With a
larger budget, the same canonical laws survive to `19` on both orientations.
So the current frontier is not a structural barrier at all; it is an
engineering frontier. That is exactly the kind of problem you can sometimes
turn into a `residue`-style computational result with enough optimization.

## Exploration 16

### Strategy
Push the medium-budget lexmin probe one more step to `n = 20`, to see whether the recovered law through `19` is already a meaningful computational range statement rather than a one- or two-step extension.

### Outcome
SUCCEEDED

### Failure Constraint
No new failure at `n = 20` under timeout `5000 ms`.

### What This Rules Out
This rules out the concern that the larger-budget success at `18,19` was only a transient rescue. The same canonical update laws persist again at `20`.

### Surviving Structure
- Reverse `n = 19 -> 20` at timeout `5000 ms`:
  - all `6/6` assignments solved
  - normalized common spine size `142`
  - same `+9/0` edit
- Forward `n = 19 -> 20` at timeout `5000 ms`:
  - all `3/3` assignments solved
  - normalized common spine size `171`
  - same `5/14` edit

### Reformulations
The canonical base-family law now supports an honest medium-budget range statement:
- reverse sizes follow `43 + 9(n-9)` through at least `n = 20`
- forward sizes follow `72 + 9(n-9)` through at least `n = 20`
- the gain/loss templates remain fixed

LOAD-BEARING ASSESSMENT: yes. This is no longer a fragile local experiment. It is a reproducible range computation with a clear selector, a clear timeout, and a clear invariant law.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse size progression at timeout `5000 ms`:
  - `n = 18`: `124`
  - `n = 19`: `133`
  - `n = 20`: `142`
- Forward size progression at timeout `5000 ms`:
  - `n = 18`: `153`
  - `n = 19`: `162`
  - `n = 20`: `171`
- Reverse `n = 19 -> 20`:
  - losses: none
  - gains: the same `9` reverse gain rules
- Forward `n = 19 -> 20`:
  - losses: the same `5` forward loss rules
  - gains: the same `14` forward gain rules

STRUCTURAL RESULTS:
- The canonical base-family recurrence is now computationally verified through `n = 20` at timeout `5000 ms`.
- No new edit pattern has appeared anywhere in the tested range.

TOOLS:
- Reused the lexmin probe at timeout `5000 ms`; no new code in this exploration.

REPRESENTATIONS:
- "verified through `n = 20` at timeout `5000 ms`" is now the strongest concise computational status line for the base-family law.

### What Would Unblock This
- Either push the same probe farther with more engineering, or start packaging the current result as a real computational theorem for the base family.
- The next best technical step is still a cheaper canonical selector, since that would let the range scale much farther without changing the mathematical object.

### Key Parameters
- Selector:
  - lexicographic `z3.Optimize`
- Timeout:
  - `5000 ms`
- Transition tested:
  - base-family `n = 19 -> 20`

### Open Questions
- How far can the verified range be pushed with the current selector before `5000 ms` fails?
- Can the fixed base-family law now be promoted from computational observation to explicit theorem?
- Does any part of the upper-branch behavior admit a similar canonical-selector stabilization?

## Synthesis after exploration 16

This is the first point where the computational story has genuine starpower.
There is now a canonical, reproducible base-family law verified through `n = 20`
with fixed edit templates and linear growth. That is not yet "verified to 2000,"
but it is finally in the same paradigm: one scalable object, one selector, one
range statement. The main remaining gap is no longer whether the object exists.
It is whether we can make the selector cheap enough, or prove enough about it,
to push the verified range from `20` to something truly headline-worthy.

## Exploration 17

### Strategy
Promote the observed base-family lexmin law from a repeated probe pattern to an explicit recurrence checker that derives its fixed edits from the `n = 9 -> 10` anchor and then generates larger-`n` canonical spines directly.

### Outcome
SUCCEEDED

### Failure Constraint
No structural failure. The remaining limitation is still scope: this packages the base-family law cleanly, but it does not yet solve the upper branches or prove the recurrence from first principles.

### What This Rules Out
This rules out continuing to treat the base-family starpower result as only an informal pattern in the log. The object is now explicit enough that future work can build on one script rather than re-deriving the law ad hoc.

### Surviving Structure
- Reverse recurrence extracted by the script:
  - base size `43`
  - slope `9`
  - losses `0`
  - gains `9`
- Forward recurrence extracted by the script:
  - base size `72`
  - slope `9`
  - losses `5`
  - gains `14`
- Generated sizes through `n = 20`:
  - reverse: `43, 52, 61, 70, 79, 88, 97, 106, 115, 124, 133, 142`
  - forward: `72, 81, 90, 99, 108, 117, 126, 135, 144, 153, 162, 171`
- Verified by direct lexmin probe through `n = 11` in the script itself, with all matches true.

### Reformulations
The base-family computation is now best viewed as a recurrence theorem candidate:
- derive fixed edit law from the `9 -> 10` canonical anchor
- generate `S_n` for arbitrary `n`
- compare against the canonical probe only when desired

LOAD-BEARING ASSESSMENT: yes. This is the first reusable interface for the scalable law. It separates "what the law is" from "how expensively we confirm it at selected `n`."

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse derived gain rules:
  - `('Q', (0, 0, 0), 0)`
  - `('Q', (0, 0, 1), 1)`
  - `('Q', (0, 1, 1), 1)`
  - `('Q', (1, 1, 1), 1)`
  - `('Q-2', (1, 1, 2), 2)`
  - `('Q-2', (1, 2, 2), 2)`
  - `('Q-2', (2, 0, 0), 0)`
  - `('Q-2', (2, 2, 0), 0)`
  - `('Q-2', (2, 2, 2), 2)`
- Forward derived loss/gain templates:
  - losses: the fixed `5` `Q-1` rules
  - gains: the fixed `14` `Q/Q-1` rules
- Script-generated sizes through `n = 20` match the previously observed range values.

STRUCTURAL RESULTS:
- The base-family canonical law is now encoded as an explicit recurrence object.
- The recurrence is consistent with lexmin probe verification through `n = 11` inside the script, and with the previously logged manual checks through `n = 20`.

TOOLS:
- Added `probes/gpt/glb_case3c_base_recurrence.py`.
- Added `probes/gpt/tests/test_glb_case3c_base_recurrence.py`.

REPRESENTATIONS:
- Base-family law is now represented as `(base spine, fixed losses, fixed gains, linear size slope)` rather than only as probe outputs.

### What Would Unblock This
- The next high-value step is to replace the runtime-derived `n = 9 -> 10` anchor with a proved or frozen canonical base datum, so the recurrence checker no longer depends on running the probe to define itself.
- After that, the best payoff is either pushing the verified range much farther or trying to extract a similar recurrence for part of the upper branch.

### Key Parameters
- Derivation anchor:
  - `n = 9 -> 10`
- Selector:
  - lexmin
- Validation run:
  - generated through `n = 20`
  - verified by probe through `n = 11`

### Open Questions
- Should the base recurrence be frozen as explicit data rather than derived at runtime?
- Can the same recurrence interface be extended to the upper-wiggle families, even with exceptions?
- Is the next biggest win range-pushing, selector optimization, or turning the base recurrence into a formal theorem statement?

## Synthesis after exploration 17

This is a meaningful shift in maturity. The base-family result is no longer
just "we observed a stable law out to 20." It is now a concrete recurrence
checker with tests. That is the right format for either a computational theorem
or a future high-range verification campaign. The remaining question is no
longer how to *describe* the base-family starpower object. It is how to make it
stronger: freeze it, prove it, or scale it.

## Exploration 18

### Strategy
Attack coverage beyond the base family by probing the upper-wiggle families under the same lexmin canonical selector, checking whether they satisfy a fixed local edit law across `n = 9 -> 10 -> 11`.

### Outcome
PARTIAL

### Failure Constraint
The upper-wiggle branch does not immediately stabilize to one fixed edit template. The canonical diffs stay tail-local and fully solvable through `n = 11`, but the loss/gain sets change between `9 -> 10` and `10 -> 11`.

### What This Rules Out
This rules out the simplest hope that the upper branch is just "the base-family recurrence with one small static exception." Any full-fat verifier will need either:
- a second recurrence that only stabilizes after a larger anchor, or
- a finite-state tail grammar whose active template changes with `n`.

### Surviving Structure
- Reverse upper canonical sizes:
  - `n = 9`: `32`
  - `n = 10`: `40`
  - `n = 11`: `49`
- Forward upper canonical sizes:
  - `n = 9`: `58`
  - `n = 10`: `64`
  - `n = 11`: `72`
- All canonical upper-wiggle completion-branch assignments solved through `n = 11` at timeout `1200 ms`:
  - reverse: `18/18`
  - forward: `9/9`
- Reverse upper diffs:
  - `9 -> 10`: `2` losses, `10` gains
  - `10 -> 11`: `2` losses, `11` gains
- Forward upper diffs:
  - `9 -> 10`: `3` losses, `9` gains
  - `10 -> 11`: `5` losses, `13` gains

### Reformulations
The upper-wiggle branch should currently be viewed as a tail-local evolving edit family, not yet as a fixed recurrence. The important good news is representational:
- the canonical selector keeps the action near `Q, Q-1, Q-2, ...`
- the interior block remains rigid

LOAD-BEARING ASSESSMENT: yes. Even though this does not yet give a starpower recurrence, it sharply localizes the remaining complexity and suggests a finite tail-state machine rather than a global re-solve.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse upper `9 -> 10`:
  - sizes `32 -> 40`
  - losses:
    - `('Q-2', (0, 0, 1), 1)`
    - `('Q-2', (0, 1, 1), 1)`
  - gains:
    - `('Q', (0, 0, 0), 0)`
    - `('Q', (0, 0, 1), 1)`
    - `('Q', (0, 1, 1), 1)`
    - `('Q-2', (2, 0, 0), 0)`
    - `('Q-2', (2, 2, 0), 0)`
    - `('Q-3', (0, 0, 1), 1)`
    - `('Q-3', (0, 1, 1), 1)`
    - `('Q-3', (0, 2, 2), 2)`
    - `('Q-3', (1, 1, 1), 1)`
    - `('Q-3', (1, 2, 2), 2)`
- Reverse upper `10 -> 11`:
  - sizes `40 -> 49`
  - same `2` losses at `Q-2`
  - gains:
    - same `Q` and `Q-2` additions
    - expanded `Q-3` additions including `('Q-3', (2, 2, 2), 2)`
- Forward upper `9 -> 10`:
  - sizes `58 -> 64`
  - losses:
    - `('Q-1', (0, 0, 1), 0)`
    - `('Q-1', (1, 0, 1), 1)`
    - `('Q-1', (1, 1, 1), 1)`
  - gains: `9` tail-local rules at `Q`, `Q-1`, `Q-2`, `Q-3`
- Forward upper `10 -> 11`:
  - sizes `64 -> 72`
  - losses:
    - `('Q-1', (0, 0, 1), 0)`
    - `('Q-1', (0, 2, 0), 2)`
    - `('Q-1', (1, 0, 1), 1)`
    - `('Q-1', (1, 1, 1), 1)`
    - `('Q-3', (0, 0, 1), 0)`
  - gains: `13` tail-local rules at `Q`, `Q-1`, `Q-2`, `Q-3`

STRUCTURAL RESULTS:
- The upper-wiggle canonical branch is fully solvable through `n = 11`.
- Its complexity is still strongly localized to the tail corridor.
- Fixed-template recurrence has not yet appeared by `n = 11`.

TOOLS:
- No new code in this exploration.
- Reused `glb_case3c_forced_spine_probe.py` and tail-shift comparison snippets with `--include-upper-wiggle`.

REPRESENTATIONS:
- Upper branch is now best thought of as a candidate finite tail-state machine rather than a one-shot recurrence.

### What Would Unblock This
- The next useful probe is `n = 12` on the upper-wiggle branch, to see whether the edit templates stabilize one step later or continue drifting.
- If drift continues, the right next abstraction is to cluster tail edits by support pattern rather than by exact rule set.

### Key Parameters
- Selector:
  - lexmin
- Timeout:
  - `1200 ms`
- Range tested:
  - upper-wiggle `n = 9,10,11`

### Open Questions
- Does the upper-wiggle branch stabilize at `n = 12` or later?
- Are the evolving upper edits generated by one finite tail-state machine?
- Can the reverse and forward upper branches be unified after quotienting one more symmetry or tail state?

## Synthesis after exploration 18

This is a useful sharpening, even though it is not the breakthrough the base
family gave. The upper branch is not wild; it is local. But it is not yet
frozen into one fixed recurrence either. That means the next best line is not
"optimize the whole verifier more." It is "understand the upper tail grammar as
its own small state machine." If that works, the project moves from one base
recurrence plus messy residue to a genuinely broad canonical verifier family.

## Exploration 19

### Strategy
Push the upper-wiggle branch one more step to `n = 12`, to see whether the drifting edits from exploration 18 stabilize into a fixed template or continue to evolve.

### Outcome
PARTIAL

### Failure Constraint
Only the forward upper branch keeps drifting at `n = 12`. Reverse upper stabilizes; forward upper does not yet.

### What This Rules Out
This rules out treating the whole upper branch as one uniform tail-state machine at the current level of detail. The reverse and forward orientations must now be handled separately.

### Surviving Structure
- Reverse upper sizes:
  - `n = 10`: `40`
  - `n = 11`: `49`
  - `n = 12`: `58`
- Reverse upper fixed edit law from `n = 10` onward:
  - losses:
    - `('Q-2', (0, 0, 1), 1)`
    - `('Q-2', (0, 1, 1), 1)`
  - gains:
    - `('Q', (0, 0, 0), 0)`
    - `('Q', (0, 0, 1), 1)`
    - `('Q', (0, 1, 1), 1)`
    - `('Q-2', (2, 0, 0), 0)`
    - `('Q-2', (2, 2, 0), 0)`
    - `('Q-3', (0, 0, 1), 1)`
    - `('Q-3', (0, 1, 1), 1)`
    - `('Q-3', (1, 1, 1), 1)`
    - `('Q-3', (1, 1, 2), 2)`
    - `('Q-3', (1, 2, 2), 2)`
    - `('Q-3', (2, 2, 2), 2)`
- Forward upper sizes:
  - `n = 10`: `64`
  - `n = 11`: `72`
  - `n = 12`: `81`
- Forward upper still drifts:
  - `10 -> 11`: `5` losses, `13` gains
  - `11 -> 12`: `6` losses, `15` gains

### Reformulations
The upper branch now splits cleanly:
- reverse upper = recurrence candidate starting from `n = 10`
- forward upper = evolving tail-state machine candidate

LOAD-BEARING ASSESSMENT: yes. This meaningfully shrinks the unresolved part of the full verifier: reverse upper can likely be packaged now, leaving only forward upper as the true moving target.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Reverse upper `11 -> 12`:
  - same `2` losses as `10 -> 11`
  - same `11` gains as `10 -> 11`
- Forward upper `11 -> 12`:
  - losses:
    - `('Q-1', (0, 0, 1), 0)`
    - `('Q-1', (0, 2, 0), 2)`
    - `('Q-1', (1, 0, 1), 1)`
    - `('Q-1', (1, 1, 1), 1)`
    - `('Q-3', (0, 0, 1), 0)`
    - `('Q-3', (2, 2, 0), 2)`
  - gains:
    - `('Q', (0, 0, 0), 0)`
    - `('Q', (0, 0, 1), 0)`
    - `('Q', (0, 2, 0), 2)`
    - `('Q', (1, 0, 1), 1)`
    - `('Q', (1, 1, 1), 1)`
    - `('Q-1', (1, 0, 0), 1)`
    - `('Q-1', (1, 1, 0), 1)`
    - `('Q-2', (0, 0, 1), 0)`
    - `('Q-2', (1, 1, 1), 1)`
    - `('Q-2', (2, 2, 0), 2)`
    - `('Q-2', (2, 2, 1), 2)`
    - `('Q-3', (0, 0, 2), 0)`
    - `('Q-3', (0, 2, 2), 0)`
    - `('Q-3', (2, 1, 1), 2)`
    - `('Q-3', (2, 2, 2), 2)`

STRUCTURAL RESULTS:
- Reverse upper has stabilized by `n = 10`.
- Forward upper remains localized but not yet stationary by `n = 12`.

TOOLS:
- No new code in this exploration.
- Reused the lexmin upper-wiggle probe.

REPRESENTATIONS:
- Reverse upper can now be treated as a recurrence candidate.
- Forward upper should be treated as an evolving tail-state machine.

### What Would Unblock This
- Package reverse upper into a recurrence checker immediately.
- Probe forward upper at `n = 13` to see whether it stabilizes one step later or whether a true state-machine abstraction is required.

### Key Parameters
- Selector:
  - lexmin
- Timeout:
  - `1200 ms`
- Range tested:
  - upper-wiggle `n = 10,11,12`

### Open Questions
- Does forward upper stabilize at `n = 13`?
- Can reverse upper be folded into the base-style recurrence interface with a different anchor and edit set?
- Is forward upper periodic in a small tail state rather than genuinely drifting forever?

## Synthesis after exploration 19

This is the first upper-branch result that really changes the verifier design.
We no longer have "the messy upper branch." We have one upper orientation that
already looks recurrence-like, and one that still looks like a small evolving
tail machine. That means the path to a broader full-fat verifier is now
concrete: absorb reverse upper into the packaged recurrence layer, then keep
attacking forward upper as the last moving canonical component.

## Exploration 20

### Strategy
Promote the upper-wiggle representative-family laws from exploration notes into the same packaged recurrence form as the base families, and verify that the observed fixed edit templates persist one more step to `n = 14`.

### Outcome
PARTIAL

### Failure Constraint
The recurrence layer is now complete for the representative true Case `3c` architecture, but it still says nothing about non-representative gap patterns. This is a packaging breakthrough, not a full `Case 3c` theorem.

### What This Rules Out
This rules out the older design split where the base family was recurrence-shaped but the upper family remained an exploratory residue. On the representative architecture, the upper branch is no longer the unresolved component.

### Surviving Structure
- Reverse upper stabilizes from `n = 10` onward:
  - anchor size `40`
  - fixed losses `2`
  - fixed gains `11`
  - size law `40,49,58,67,76` for `n = 10..14`
- Forward upper stabilizes from `n = 11` onward:
  - anchor size `72`
  - fixed losses `6`
  - fixed gains `15`
  - size law `72,81,90,99` for `n = 11..14`
- Both upper laws have slope `+9`, just like the base families.
- The representative architecture now has four packaged canonical laws:
  - reverse base
  - forward base
  - reverse upper
  - forward upper

### Reformulations
The right representative-family object is no longer "base recurrence plus upper exploration." It is a full four-family recurrence layer with different anchors.

LOAD-BEARING ASSESSMENT: very high. This means the recurrence packaging is now complete on one genuine residue architecture, which is much closer to a verifier component than the earlier piecemeal base-only result.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `n = 12 -> 13` forward upper:
  - losses:
    - `('Q-1', (0, 0, 1), 0)`
    - `('Q-1', (0, 2, 0), 2)`
    - `('Q-1', (1, 0, 1), 1)`
    - `('Q-1', (1, 1, 1), 1)`
    - `('Q-3', (0, 0, 1), 0)`
    - `('Q-3', (2, 2, 0), 2)`
  - gains:
    - `('Q', (0, 0, 0), 0)`
    - `('Q', (0, 0, 1), 0)`
    - `('Q', (0, 2, 0), 2)`
    - `('Q', (1, 0, 1), 1)`
    - `('Q', (1, 1, 1), 1)`
    - `('Q-1', (1, 0, 0), 1)`
    - `('Q-1', (1, 1, 0), 1)`
    - `('Q-2', (0, 0, 1), 0)`
    - `('Q-2', (1, 1, 1), 1)`
    - `('Q-2', (2, 2, 0), 2)`
    - `('Q-2', (2, 2, 1), 2)`
    - `('Q-3', (0, 0, 2), 0)`
    - `('Q-3', (0, 2, 2), 0)`
    - `('Q-3', (2, 1, 1), 2)`
    - `('Q-3', (2, 2, 2), 2)`
- `n = 13 -> 14` forward upper repeats the same `6/15` edit exactly.
- `n = 13 -> 14` reverse upper repeats the same `2/11` edit exactly.

TOOLS:
- Added `probes/gpt/glb_case3c_family_recurrence.py`.
- Added `probes/gpt/tests/test_glb_case3c_family_recurrence.py`.

VERIFIED:
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_base_recurrence probes.gpt.tests.test_glb_case3c_family_recurrence`
- `python3 probes/gpt/glb_case3c_family_recurrence.py --family upper --end-n 14 --verify-to 13 --verify-timeout-ms 1200`

### What Would Unblock This
- Freeze the representative-family recurrence anchors as explicit data rather than deriving them live from probes.
- Extend the recurrence layer beyond the representative architecture by classifying gap-pattern regimes.

### Open Questions
- Do the same canonical laws transfer to other true Case `3c` gap patterns?
- If not, is the number of gap-dependent regimes still finite and small enough for a verifier taxonomy?

## Synthesis after exploration 20

This is a real upgrade in quality. The representative-family story is now
coherent from end to end: four canonical branches, four recurrence laws, and
direct probe verification. The remaining difficulty is no longer "finish the
upper branch." It is "escape the representative family without losing the
canonical structure."

## Exploration 21

### Strategy
Test whether the representative base-family bottom-slot rule survives on the other true `n = 9` Case `3c` gap patterns by reconstructing normalized state vectors from gap triples and reusing the natural three-sweep family spec on each one.

### Outcome
STALLED

### Failure Constraint
The representative base-family law is not universal across true gap patterns. Already at `n = 9`, the exact assignment split depends on the gap pattern.

### What This Rules Out
- This rules out the cleanest possible all-`Case 3c` dream: one representative base-family law plus gap shifts.
- It also rules out using the current recurrence layer as a direct proof-backed replacement for all true `Case 3c` architectures.

### Surviving Structure
- Gap `(1,2,3)` behaves exactly like the representative family:
  - reverse: `3` seeded-unsat, `6` completion-unsat
  - forward: `6` seeded-unsat, `3` completion-unsat
- Gap `(1,3,2)` also behaves exactly like the representative family:
  - reverse: `3` seeded-unsat, `6` completion-unsat
  - forward: `6` seeded-unsat, `3` completion-unsat
- Gap `(1,1,4)` is much more local:
  - reverse: `7` seeded-unsat, `2` completion-unsat
  - forward: `8` seeded-unsat, `1` completion-unsat
- Gap `(2,2,2)` is maximally completion-heavy:
  - reverse: all `9` assignments completion-unsat
  - forward: all `9` assignments completion-unsat

### Reformulations
The right next object is a gap-regime taxonomy, not a universal base-family rule. At least on true `n = 9` Case `3c`, the base branch splits into:
- representative-like regimes `(1,2,3)` and `(1,3,2)`,
- compressed local regime `(1,1,4)`,
- symmetric all-completion regime `(2,2,2)`.

LOAD-BEARING ASSESSMENT: very high. This changes the verifier target completely. The core task is now to prove or compute a finite menu of regime laws, not to stretch one representative law over all gap patterns.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `gaps=(1,1,4)`:
  - reverse actual bottom-slot counter:
    - slot `0`: `3` seeded-unsat
    - slot `1`: `1` completion-unsat, `2` seeded-unsat
    - slot `2`: `1` completion-unsat, `2` seeded-unsat
  - forward actual bottom-slot counter:
    - slot `0`: `1` completion-unsat, `2` seeded-unsat
    - slots `1,2`: all seeded-unsat
- `gaps=(2,2,2)`:
  - reverse actual bottom-slot counter:
    - slots `0,1,2`: all `3/3` completion-unsat
  - forward actual bottom-slot counter:
    - slots `0,1,2`: all `3/3` completion-unsat

TOOLS:
- Added `probes/gpt/glb_case3c_gap_pattern_probe.py`.
- Added `probes/gpt/tests/test_glb_case3c_gap_pattern_probe.py`.

VERIFIED:
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_gap_pattern_probe`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --gaps '1,2,3;1,1,4;1,3,2;2,2,2' --orientation both --timeout-ms 1200`

### What Would Unblock This
- Run the same gap-pattern probe at `n = 10` and see whether the regime split depends only on the gap pattern or on the exact gap lengths.
- Compress the gap-pattern data into a small symbolic rule family rather than raw assignment tables.

### Open Questions
- Are `(1,2,3)` and `(1,3,2)` the same regime for all `n`, or just at `n = 9`?
- Does `(2,2,2)` stay all-completion at larger `n`?
- Is `(1,1,4)` the start of one compressed-local family `(1,1,k)`?

## Synthesis after exploration 21

This is the first genuinely sobering result after the recurrence packaging.
The representative-family recurrence is real, but it is not the whole story.
That does not kill the starpower project. It changes its shape. The plausible
target is now a finite regime catalogue indexed by gap pattern and orientation.

## Exploration 22

### Strategy
Sample the upper-wiggle branch on non-representative true `n = 9` gap patterns to determine whether upper also splits into gap-dependent regimes, or whether the gap sensitivity discovered in exploration 21 was base-only.

### Outcome
PARTIAL

### Failure Constraint
Upper is also gap-sensitive. The representative upper laws do not transfer uniformly across true `n = 9` gap patterns.

### What This Rules Out
This rules out the softer fallback that only the base branch needs a gap taxonomy while upper remains universal. Both branches now require regime classification.

### Surviving Structure
- Gap `(1,1,4)`:
  - reverse upper: `21` seeded-unsat, `6` completion-unsat
  - forward upper: `24` seeded-unsat, `3` completion-unsat
- Gap `(2,2,2)`:
  - reverse upper: `12` seeded-unsat, `15` completion-unsat
  - forward upper: all `27` assignments completion-unsat
- Gap `(1,3,2)`:
  - reverse upper: `17` seeded-unsat, `10` completion-unsat
  - forward upper: `18` seeded-unsat, `9` completion-unsat, exactly matching the representative family.

### Reformulations
The upper branch is not one regime either. The emerging taxonomy is finer:
- some gap/orientation pairs are representative-like,
- some are mostly local,
- some are mixed,
- some are all-completion.

LOAD-BEARING ASSESSMENT: very high. This confirms that the full-fat verifier has to solve the gap-regime classification problem head-on. There is no remaining shortcut through a single representative upper law.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `gaps=(1,1,4)` reverse upper actual bottom-slot counter:
  - slot `0`: all `9` seeded-unsat
  - slot `1`: `3` completion-unsat, `6` seeded-unsat
  - slot `2`: `3` completion-unsat, `6` seeded-unsat
- `gaps=(2,2,2)` forward upper actual bottom-slot counter:
  - slots `0,1,2`: all `9/9` completion-unsat
- `gaps=(1,3,2)` forward upper actual bottom-slot counter:
  - slot `0`: `9` completion-unsat
  - slots `1,2`: `9` seeded-unsat each

VERIFIED:
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --gaps '1,1,4' --orientation both --include-upper-wiggle --timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --gaps '2,2,2' --orientation both --include-upper-wiggle --timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --gaps '1,3,2' --orientation both --include-upper-wiggle --timeout-ms 1200`

### What Would Unblock This
- Complete the exact upper sweep on all true `n = 9` gap patterns.
- Extend the same regime probe to the five true `n = 10` gap patterns and see whether the `n = 9` regimes persist.

### Open Questions
- Is forward upper representative-like exactly on the same gap-regime family as base?
- Can the mixed reverse-upper regimes be compressed to a small symbolic rule keyed by gap asymmetry?
- How many distinct regime families survive at `n = 10`?

## Synthesis after exploration 22

The project is no longer pointing at one universal all-killer for true
`Case 3c`. It is pointing at a finite regime theory. That is still compatible
with starpower, but the starpower object is now: a gap-pattern/orientation
catalogue of canonical recurrences and local/completion splits, plus a cheap
classifier that picks the right regime at large `n`.

## Exploration 23

### Strategy
Complete `M1` by turning the exact `n = 9` gap-pattern probes into a reproducible taxonomy command that clusters true Case `3c` gap patterns by exact family/orientation signatures.

### Outcome
SUCCEEDED

### Failure Constraint
The taxonomy is exact only at `n = 9`. It does not yet say whether the same clustered regimes persist at `n = 10` or larger.

### What This Rules Out
This rules out treating `M1` as "just rerun four probes and eyeball the output." The gap-sensitive frontier is now packaged as one exact regime table that future work can target directly.

### Surviving Structure
- Exact base taxonomy:
  - `reverse_base`: `3` regimes
  - `forward_base`: `3` regimes
- Exact upper taxonomy:
  - `reverse_upper`: `4` regimes
  - `forward_upper`: `3` regimes
- Stable clustering facts:
  - `(1,2,3)` and `(1,3,2)` are the same regime on:
    - reverse base
    - forward base
    - forward upper
  - `(1,2,3)` and `(1,3,2)` split on reverse upper.
  - `(2,2,2)` is all-completion on:
    - reverse base
    - forward base
    - forward upper
  - `(2,2,2)` is mixed on reverse upper.

### Reformulations
`M1` is now best stated as:
- a finite exact `n = 9` regime catalogue for true `Case 3c`,
- indexed by `(orientation, base/upper, gap pattern)`,
- with clustering by exact bottom-slot and fragment-size signatures.

LOAD-BEARING ASSESSMENT: very high. This is the concrete boundary between "there is gap sensitivity" and "we know exactly what the `n = 9` frontier is."

### Concrete Artifacts
EXACT TAXONOMY OUTPUT:
- `reverse_base`
  - `reverse_base_r1`: gaps `[(1,1,4)]`
  - `reverse_base_r2`: gaps `[(1,2,3), (1,3,2)]`
  - `reverse_base_r3`: gaps `[(2,2,2)]`
- `forward_base`
  - `forward_base_r1`: gaps `[(1,1,4)]`
  - `forward_base_r2`: gaps `[(1,2,3), (1,3,2)]`
  - `forward_base_r3`: gaps `[(2,2,2)]`
- `reverse_upper`
  - `reverse_upper_r1`: gaps `[(1,1,4)]`
  - `reverse_upper_r2`: gaps `[(1,2,3)]`
  - `reverse_upper_r3`: gaps `[(1,3,2)]`
  - `reverse_upper_r4`: gaps `[(2,2,2)]`
- `forward_upper`
  - `forward_upper_r1`: gaps `[(1,1,4)]`
  - `forward_upper_r2`: gaps `[(1,2,3), (1,3,2)]`
  - `forward_upper_r3`: gaps `[(2,2,2)]`

REPRESENTATIVE EXACT SIGNATURES:
- `forward_upper_r2`:
  - slot signature:
    - slot `0`: `9` completion-unsat
    - slots `1,2`: `9` seeded-unsat each
  - summary:
    - `9` completion-unsat with fragment size `35`
    - `18` seeded-unsat
- `reverse_upper_r4`:
  - slot signature:
    - every slot has `5` completion-unsat and `4` seeded-unsat
  - summary:
    - `12` completion-unsat with fragment size `35`
    - `3` completion-unsat with fragment size `7`
    - `12` seeded-unsat

TOOLS:
- Extended `probes/gpt/glb_case3c_gap_pattern_probe.py` with:
  - taxonomy mode,
  - exact signature extraction,
  - regime clustering.
- Extended `probes/gpt/tests/test_glb_case3c_gap_pattern_probe.py` with clustering tests.

VERIFIED:
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_gap_pattern_probe`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --mode taxonomy --family-set base --orientation both --timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --mode taxonomy --family-set upper --orientation reverse --timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --mode taxonomy --family-set upper --orientation forward --timeout-ms 1200`

### What Would Unblock This
- Run the same taxonomy at `n = 10` and see whether the number of regimes stays small.
- Replace raw gap tuples with symbolic regime predicates like `(1,1,k)`, `(1,a,b)`, or symmetric classes.

### Open Questions
- Does `reverse_upper` keep four distinct regimes at `n = 10`, or do some merge?
- Is `(1,1,4)` the base case of a whole compressed-local family `(1,1,k)`?
- Is the mixed symmetric reverse-upper behavior the only genuinely new regime at larger `n`?

## Synthesis after exploration 23

`M1` is finished. The exact `n = 9` frontier is no longer a pile of probe
outputs. It is a regime table. That is the right launching point for `M2`,
because the `n = 10` question is now sharply stated: do these `n = 9` regimes
persist as a small finite menu, or does the catalogue grow?

## Exploration 24

### Strategy
Execute `M2`: extend the taxonomy tool to enumerate true Case `3c` gap patterns for arbitrary `n`, then compute the exact `n = 10` taxonomy and compare its regime count to the `n = 9` table.

### Outcome
PARTIAL

### Failure Constraint
The regime table does grow at `n = 10`, especially on reverse upper. So the exact `n = 9` catalogue does not transfer literally unchanged. But it does not explode.

### What This Rules Out
- This rules out the best-case dream that the `n = 9` regime table is already final.
- It does not rule out starpower. The catalogue stays small enough that a regime-theory path is still credible.

### Surviving Structure
- Exact `n = 10` regime counts:
  - `reverse_base`: `3`
  - `forward_base`: `3`
  - `forward_upper`: `3`
  - `reverse_upper`: `5`
- Persistent clustering:
  - the representative-like asymmetric family grows from `[(1,2,3), (1,3,2)]` at `n = 9` to `[(1,2,4), (1,3,3), (1,4,2)]` on:
    - reverse base
    - forward base
    - forward upper
  - the compressed local family remains the `(1,1,k)` branch:
    - `(1,1,4)` at `n = 9`
    - `(1,1,5)` at `n = 10`
  - the symmetric family remains all-completion on:
    - reverse base
    - forward base
    - forward upper
    with `(2,2,2)` at `n = 9`, `(2,2,3)` at `n = 10`
- Reverse upper is the only family that clearly refines:
  - `n = 9`: `4` regimes
  - `n = 10`: `5` regimes
  - the old representative-like branch splits into at least:
    - `(1,2,4)` with summary `12x38 + 6x6 + 9 seed`
    - `(1,3,3)` with summary `13x38 + 1x37 + 4x6 + 9 seed`

### Reformulations
The `M2` picture is now:
- regime theory survives,
- the regime count stays small,
- but reverse upper needs a finer symbolic key than "representative-like asymmetric."

LOAD-BEARING ASSESSMENT: very high. This is exactly the kind of result needed to justify continuing toward `n = 2000`: small finite menu preserved, with one branch getting slightly more detailed rather than blowing up.

### Concrete Artifacts
EXACT `n = 10` TAXONOMY:
- `reverse_base`
  - `r1`: gaps `[(1,1,5)]`
  - `r2`: gaps `[(1,2,4), (1,3,3), (1,4,2)]`
  - `r3`: gaps `[(2,2,3)]`
- `forward_base`
  - `r1`: gaps `[(1,1,5)]`
  - `r2`: gaps `[(1,2,4), (1,3,3), (1,4,2)]`
  - `r3`: gaps `[(2,2,3)]`
- `forward_upper`
  - `r1`: gaps `[(1,1,5)]`
  - `r2`: gaps `[(1,2,4), (1,3,3), (1,4,2)]`
  - `r3`: gaps `[(2,2,3)]`
- `reverse_upper`
  - `r1`: gaps `[(1,1,5)]`
  - `r2`: gaps `[(1,2,4)]`
  - `r3`: gaps `[(1,3,3)]`
  - `r4`: gaps `[(1,4,2)]`
  - `r5`: gaps `[(2,2,3)]`

TOOLS:
- Extended `probes/gpt/glb_case3c_gap_pattern_probe.py` with:
  - canonical gap enumeration,
  - automatic true-gap generation from `--n`.
- Extended `probes/gpt/tests/test_glb_case3c_gap_pattern_probe.py` with `n = 10` gap-catalogue tests.

VERIFIED:
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_gap_pattern_probe`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 10 --mode taxonomy --family-set base --orientation both --timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 10 --mode taxonomy --family-set upper --orientation forward --timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 10 --mode taxonomy --family-set upper --orientation reverse --timeout-ms 1200`

### What Would Unblock This
- Run the same taxonomy at `n = 11`.
- Identify the symbolic invariant that distinguishes reverse-upper `(1,2,4)` from `(1,3,3)` from `(1,4,2)`.

### Open Questions
- Does reverse upper keep adding one new asymmetric regime at each `n`, or does it stabilize after a small number of splits?
- Do the three base/forward-upper regimes persist unchanged at `n = 11`?
- Is the right asymmetry parameter for reverse upper just the middle gap, or something more local?

## Synthesis after exploration 24

`M2` is a qualified success. The taxonomy did not explode at `n = 10`. Three of
the four family views stayed at exactly three regimes, and the only branch that
grew was reverse upper, from four to five. That is still small. So the current
best picture is not "one universal recurrence," but it is also not "chaos."
It is a small regime theory with one branch that needs a finer asymmetry
parameter.

## Exploration 25

### Strategy
Push `M2` to `n = 11`, but switch to a status-only exact taxonomy path that skips fatal-fragment minimization so the computation remains tractable while preserving seeded/completion status signatures.

### Outcome
SUCCEEDED

### Failure Constraint
This `n = 11` taxonomy is exact in seeded/completion status, but not in minimized fragment-size signatures. It is good enough for regime counting and clustering, not for a fragment-level theorem statement.

### What This Rules Out
- This rules out the fear that the `n = 10` catalogue was the last clean small case before a blow-up at `n = 11`.
- It does not yet rule out further refinement at `n = 12+`, especially on reverse upper.

### Surviving Structure
- Exact status-only `n = 11` regime counts:
  - `reverse_base`: `3`
  - `forward_base`: `3`
  - `forward_upper`: `3`
  - `reverse_upper`: `4`
- Base and forward-upper families now show the same coarse partition:
  - compressed local family: `[(1,1,6)]`
  - asymmetric family: `[(1,2,5), (1,3,4), (1,4,3), (1,5,2)]`
  - semi-symmetric family: `[(2,2,4), (2,3,3)]`
- Reverse upper is only slightly finer:
  - `[(1,1,6)]`
  - `[(1,2,5), (1,3,4), (1,4,3)]`
  - `[(1,5,2)]`
  - `[(2,2,4), (2,3,3)]`

### Reformulations
The finite-regime story is now stronger than before:
- base and forward-upper appear to be governed by the same three coarse regime families through `n = 11`,
- reverse upper needs one extra asymmetry distinction, but still stays small.

LOAD-BEARING ASSESSMENT: very high. This is the first point where the regime picture looks stable enough across `n = 9,10,11` to justify trying to write symbolic regime predicates instead of just tabulating cases.

### Concrete Artifacts
EXACT STATUS-ONLY `n = 11` TAXONOMY:
- `reverse_base`
  - `r1`: `[(1,1,6)]`
  - `r2`: `[(1,2,5), (1,3,4), (1,4,3), (1,5,2)]`
  - `r3`: `[(2,2,4), (2,3,3)]`
- `forward_base`
  - `r1`: `[(1,1,6)]`
  - `r2`: `[(1,2,5), (1,3,4), (1,4,3), (1,5,2)]`
  - `r3`: `[(2,2,4), (2,3,3)]`
- `forward_upper`
  - `r1`: `[(1,1,6)]`
  - `r2`: `[(1,2,5), (1,3,4), (1,4,3), (1,5,2)]`
  - `r3`: `[(2,2,4), (2,3,3)]`
- `reverse_upper`
  - `r1`: `[(1,1,6)]`
  - `r2`: `[(1,2,5), (1,3,4), (1,4,3)]`
  - `r3`: `[(1,5,2)]`
  - `r4`: `[(2,2,4), (2,3,3)]`

STATUS SIGNATURE HIGHLIGHTS:
- base/forward-upper asymmetric family:
  - base reverse:
    - slot `0`: `3` seeded-unsat
    - slots `1,2`: `3` completion-unsat each
  - forward upper:
    - slot `0`: `9` completion-unsat
    - slots `1,2`: `9` seeded-unsat each
- reverse upper semi-symmetric family `[(2,2,4), (2,3,3)]`:
  - every slot: `9` completion-unsat

TOOLS:
- Extended `probes/gpt/glb_three_sweep_assignment_scan.py` with `include_fragment_size=False`.
- Extended `probes/gpt/glb_case3c_gap_pattern_probe.py` with `--omit-fragment-sizes`.

VERIFIED:
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_gap_pattern_probe`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 10 --mode taxonomy --family-set base --orientation both --timeout-ms 1200 --omit-fragment-sizes`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 11 --mode taxonomy --family-set base --orientation both --timeout-ms 1200 --omit-fragment-sizes`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 11 --mode taxonomy --family-set upper --orientation forward --timeout-ms 1200 --omit-fragment-sizes`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 11 --mode taxonomy --family-set upper --orientation reverse --timeout-ms 1200 --omit-fragment-sizes`

### What Would Unblock This
- Write symbolic regime predicates from the observed families:
  - `(1,1,k)` compressed local
  - `(1,a,b)` asymmetric family
  - `(2,2,k)` / `(2,3,k)` semi-symmetric family
  - reverse-upper trailing-gap exception
- Check whether the same regime families survive at `n = 12`.

### Open Questions
- Is the reverse-upper exceptional singleton always the extreme asymmetric branch `(1,n-6,2)`?
- Do `(2,2,k)` and `(2,3,k-1)` remain merged for all larger `n` on base and forward-upper?
- Can the whole `n = 9,10,11` catalogue now be rewritten as symbolic predicates rather than explicit tuples?

## Synthesis after exploration 25

This is the strongest structural result in the project so far. The exact
fragment taxonomy was getting expensive, but once the non-essential fragment
minimization was removed, the `n = 11` regime picture stayed small and clean.
That means the next best move is no longer "push one more `n` immediately."
It is "turn these observed tuple-families into symbolic regime predicates."

## Exploration 26

### Strategy
Execute `M3`: replace the ad hoc tuple tables with symbolic regime predicates,
then check whether those predicates reproduce the recorded `n = 9,10,11`
status-level taxonomy exactly.

### Outcome
SUCCEEDED

### Failure Constraint
This is a status-level symbolic classifier, not a fragment-level one. It
matches the coarse seeded/completion regime splits that matter for scaling,
but it does not preserve the finer fragment-size refinement seen on
`n = 10` reverse upper.

### What This Rules Out
- This rules out the fear that the small `n = 9,10,11` tables were just
  isolated tuple accidents with no clean symbolic description.
- It does not rule out the need for a second symbolic layer if fragment-level
  reverse-upper refinement turns out to matter later.

### Surviving Structure
- The symbolic regime predicates are:
  - `local_11k`: gaps `(1,1,k)`
  - `asymmetric_1ab`: gaps `(1,a,b)` on base and forward-upper, and on
    reverse-upper when the trailing gap is at least `3`
  - `reverse_upper_trailing2`: reverse-upper gaps `(1,a,2)`
  - `semi_symmetric_2plus`: gaps with leading gap at least `2`
- These predicates reproduce the recorded exact gap-set taxonomy:
  - `n = 9`
    - base and forward-upper: `3` regimes
    - reverse-upper: `4` regimes
  - `n = 10`
    - base and forward-upper: `3` regimes
    - reverse-upper: `4` coarse regimes
  - `n = 11`
    - base and forward-upper: `3` regimes
    - reverse-upper: `4` coarse regimes
- Reverse-upper is now understood symbolically as:
  - local `(1,1,k)`
  - ordinary asymmetric `(1,a,b)` with `b >= 3`
  - trailing-`2` exceptional branch `(1,a,2)`
  - semi-symmetric leading-`2+` branch

### Reformulations
The right object is no longer "one universal recurrence for all Case `3c`."
It is:
- a small symbolic regime classifier,
- followed by regime-specific recurrence or kill laws.

That is the first formulation that actually looks compatible with a future
`n = 2000` verifier.

LOAD-BEARING ASSESSMENT: very high. This converts the empirical regime tables
into a finite symbolic menu, which is the first real abstraction step toward
starpower verification.

### Concrete Artifacts
SYMBOLIC REGIME RULE:
- base and forward-upper:
  - `(1,1,k)` -> `local_11k`
  - `(1,a,b)` -> `asymmetric_1ab`
  - `(g1,g2,g3)` with `g1 >= 2` -> `semi_symmetric_2plus`
- reverse-upper:
  - `(1,1,k)` -> `local_11k`
  - `(1,a,2)` -> `reverse_upper_trailing2`
  - `(1,a,b)` with `b >= 3` -> `asymmetric_1ab`
  - `(g1,g2,g3)` with `g1 >= 2` -> `semi_symmetric_2plus`

REGRESSION-CHECKED GAP-SET TABLES:
- `n = 9`
  - `forward_base`: `[(1,1,4)]`, `[(1,2,3),(1,3,2)]`, `[(2,2,2)]`
  - `forward_upper`: `[(1,1,4)]`, `[(1,2,3),(1,3,2)]`, `[(2,2,2)]`
  - `reverse_base`: `[(1,1,4)]`, `[(1,2,3),(1,3,2)]`, `[(2,2,2)]`
  - `reverse_upper`: `[(1,1,4)]`, `[(1,2,3)]`, `[(1,3,2)]`, `[(2,2,2)]`
- `n = 10`
  - `forward_base`: `[(1,1,5)]`, `[(1,2,4),(1,3,3),(1,4,2)]`, `[(2,2,3)]`
  - `forward_upper`: `[(1,1,5)]`, `[(1,2,4),(1,3,3),(1,4,2)]`, `[(2,2,3)]`
  - `reverse_base`: `[(1,1,5)]`, `[(1,2,4),(1,3,3),(1,4,2)]`, `[(2,2,3)]`
  - `reverse_upper`: `[(1,1,5)]`, `[(1,2,4),(1,3,3)]`, `[(1,4,2)]`, `[(2,2,3)]`
- `n = 11`
  - `forward_base`: `[(1,1,6)]`, `[(1,2,5),(1,3,4),(1,4,3),(1,5,2)]`, `[(2,2,4),(2,3,3)]`
  - `forward_upper`: `[(1,1,6)]`, `[(1,2,5),(1,3,4),(1,4,3),(1,5,2)]`, `[(2,2,4),(2,3,3)]`
  - `reverse_base`: `[(1,1,6)]`, `[(1,2,5),(1,3,4),(1,4,3),(1,5,2)]`, `[(2,2,4),(2,3,3)]`
  - `reverse_upper`: `[(1,1,6)]`, `[(1,2,5),(1,3,4),(1,4,3)]`, `[(1,5,2)]`, `[(2,2,4),(2,3,3)]`

TOOLS:
- Extended `probes/gpt/glb_case3c_gap_pattern_probe.py` with:
  - symbolic regime labels,
  - symbolic clustering,
  - symbolic/exact comparison helpers,
  - `symbolic` and `compare-symbolic` CLI modes.
- Extended `probes/gpt/tests/test_glb_case3c_gap_pattern_probe.py`
  with:
  - symbolic label tests,
  - symbolic/exact sample comparison test,
  - full `n = 9,10,11` symbolic partition regression tests.

VERIFIED:
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_gap_pattern_probe`
- `python3 -m py_compile probes/gpt/glb_case3c_gap_pattern_probe.py probes/gpt/tests/test_glb_case3c_gap_pattern_probe.py`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 9 --mode symbolic --family-set both --orientation both`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 10 --mode symbolic --family-set both --orientation both`
- `python3 probes/gpt/glb_case3c_gap_pattern_probe.py --n 11 --mode symbolic --family-set both --orientation both`

### What Would Unblock This
- Turn each symbolic regime into an explicit recurrence package rather than
  just a label.
- Check whether the same symbolic menu survives at `n = 12`.
- Identify whether reverse-upper needs a second symbolic key beyond the
  trailing-`2` split once fragment anatomy is reintroduced.

### Open Questions
- Is `reverse_upper_trailing2` always exactly the extreme asymmetric branch
  `(1,n-6,2)` for all larger `n`?
- Do the base and forward-upper regimes stay identical for all larger `n`?
- Can the semi-symmetric branch `(g1 >= 2)` be given one direct local theorem
  instead of a regime-by-regime recurrence?

## Synthesis after exploration 26

`M3` is now complete at the symbolic-family level. The small exact tables have
been compressed into four regime predicates, and those predicates reproduce the
recorded `n = 9,10,11` coarse taxonomy exactly. That is enough abstraction to
move on to the next real task: packaging regime-specific laws instead of
manually tabulating tuples.

## Exploration 27

### Strategy
Execute `M4`: build a recurrence layer on top of the symbolic regime labels
instead of the old representative-family hard-coding. The goal is to find out
which canonical regime sequences already admit clean tail-shift laws and which
ones are still blocked by the current lexmin cycle engine.

### Outcome
PARTIAL

### Failure Constraint
`M4` succeeds only for some symbolic regimes today. The new recurrence layer is
real, but it is not yet universal:
- `asymmetric_1ab` packages cleanly where the old representative-family law
  already did,
- `semi_symmetric_2plus` packages cleanly on the base orientations from a
  later anchor,
- `local_11k` and `reverse_upper_trailing2` are still blocked by missing
  canonical cycles under the current lexmin probe.

### What This Rules Out
- This rules out the simplistic idea that every symbolic regime is immediately
  recurrence-ready once it has a coarse taxonomy label.
- It does not rule out starpower. It shows that the regime abstraction is
  useful, but the canonical-cycle engine is still the bottleneck on some
  branches.

### Surviving Structure
- The recurrence layer now works over symbolic regimes rather than only the
  representative family.
- The canonical regime sequences are:
  - `local_11k`: `(1,1,n-5)`
  - `asymmetric_1ab`: `(1,2,n-6)`
  - `semi_symmetric_2plus`: `(2,2,n-7)`
  - `reverse_upper_trailing2`: `(1,n-6,2)`
- Stable packaged laws found:
  - `asymmetric_1ab / reverse_base`
    - exactly matches the old representative base law
    - base size `43`, slope `9`, losses `0`, gains `9`
    - verified through `n = 11`
  - `semi_symmetric_2plus / reverse_base`
    - anchor must be `n = 10`, not `n = 9`
    - base size `69`, slope `9`, losses `13`, gains `22`
    - verified through `n = 12`
  - `semi_symmetric_2plus / forward_base`
    - anchor `n = 10`
    - base size `82`, slope `9`, losses `5`, gains `14`
    - verified through `n = 12`
- Blocked regime branches:
  - `local_11k / reverse_base`
    - missing cycles at `10 -> 11` even with `5000 ms`
  - `reverse_upper_trailing2 / reverse_upper`
    - missing cycles at `10 -> 11`

### Reformulations
The correct M4 picture is:
- recurrence packaging is a regime-by-regime project,
- some regimes already support explicit laws,
- others need a better canonical cycle selector before they can be packaged.

That is a better result than either extreme:
- better than "only the representative family works,"
- worse than "the whole symbolic catalogue is already recurrence-complete."

LOAD-BEARING ASSESSMENT: high. This is the first point where the regime theory
starts turning into actual reusable law objects instead of just taxonomy.

### Concrete Artifacts
NEW TOOLING:
- Extended `probes/gpt/glb_case3c_forced_spine_probe.py` with:
  - `probe_summary_for_state_counts(...)`
  - `probe_summary_for_gaps(...)`
  so arbitrary true Case `3c` gap patterns can use the same forced-spine
  engine as the representative family.
- Added `probes/gpt/glb_case3c_regime_recurrence.py`, which:
  - defines canonical gap sequences per symbolic regime,
  - derives tail-shift edit laws,
  - generates predicted spines,
  - verifies them against direct gap-specific forced-spine probes.

REGRESSION RESULT:
- `asymmetric_1ab / reverse_base`
  - `base_n = 9`, `base_gaps = (1,2,3)`
  - identical to the old representative reverse-base law
- `semi_symmetric_2plus / reverse_base`
  - `base_n = 10`, `base_gaps = (2,2,3)`
  - `n = 10,11,12` all matched
- `semi_symmetric_2plus / forward_base`
  - `base_n = 10`, `base_gaps = (2,2,3)`
  - `n = 10,11,12` all matched

TEST COVERAGE:
- Added `probes/gpt/tests/test_glb_case3c_regime_recurrence.py`
  covering:
  - representative continuity (`asymmetric_1ab / reverse_base`),
  - new semi-symmetric base laws,
  - the currently unresolved `local_11k / reverse_base` branch.

VERIFIED:
- `python3 -m py_compile probes/gpt/glb_case3c_forced_spine_probe.py probes/gpt/tests/test_glb_case3c_forced_spine_probe.py`
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_forced_spine_probe`
- `python3 -m py_compile probes/gpt/glb_case3c_regime_recurrence.py probes/gpt/tests/test_glb_case3c_regime_recurrence.py`
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_regime_recurrence`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime asymmetric_1ab --family reverse-base --end-n 11 --verify-to 11 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime semi_symmetric_2plus --family reverse-base --base-n 10 --end-n 12 --verify-to 12 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime semi_symmetric_2plus --family forward-base --base-n 10 --end-n 12 --verify-to 12 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- attempted but not packaged:
  - `local_11k / reverse_base`
  - `reverse_upper_trailing2 / reverse_upper`

### What Would Unblock This
- Improve or replace the lexmin cycle selector on the hard regimes:
  - `local_11k`
  - `reverse_upper_trailing2`
- Check whether `semi_symmetric_2plus` on the upper families also stabilizes
  from a later anchor.
- Compare recurrence edits across regimes to see whether there is a smaller
  meta-law behind the per-regime packages.

### Open Questions
- Is the `local_11k` failure a genuine absence of a canonical recurrence, or
  just a selector bottleneck?
- Does `reverse_upper_trailing2` need its own special selector, or does it
  collapse once the upper-family canonicalization improves?
- Are the `semi_symmetric_2plus` base laws the first instance of a more general
  "late-anchor stabilization" phenomenon for the unresolved regimes?

## Synthesis after exploration 27

`M4` is underway in the real sense now. The regime abstraction is no longer
just descriptive: it already supports packaged recurrence laws on multiple
branches. But it is not complete. The next bottleneck is no longer taxonomy;
it is canonical cycle selection on the hard regimes. That is the right target
for the next round if the goal is a broader law catalogue rather than another
small-n table.

## Exploration 28

### Strategy
Test whether the remaining `M4` blockers are really canonical-cycle failures,
or whether the recurrence layer is simply probing the wrong assignment branch
on the non-representative regimes. The key check is to compare the recurrence
probe's "completion branch" against the exact status-level regime taxonomy.

### Outcome
SUCCEEDED

### Failure Constraint
This does not finish the whole upper-family recurrence story. It fixes a
branch-selection bug and proves that at least one previously "blocked" regime
is actually recurrence-ready. The reverse-upper trailing-`2` branch remains
computationally heavy even after the branch fix.

### What This Rules Out
- This rules out the previous interpretation that `local_11k / reverse_base`
  was blocked by the lexmin selector.
- It does not rule out a genuine selector/cost problem on
  `reverse_upper_trailing2 / reverse_upper`.

### Surviving Structure
- The old recurrence probe used the representative-family rule
  `bottom_slot == 0 => seed_unsat, else completion_unsat` to choose which
  assignments belong to the completion branch.
- That rule is wrong on some symbolic regimes:
  - `local_11k / reverse_base` at `n = 10`:
    - actual status split:
      - slot `0`: `3` seed-unsat
      - slot `1`: `1` completion-unsat, `2` seed-unsat
      - slot `2`: `1` completion-unsat, `2` seed-unsat
    - bogus "missing cycle" assignments were exactly the four assignments that
      are actually seed-unsat: `(1,0)`, `(1,2)`, `(2,0)`, `(2,1)`
  - `reverse_upper_trailing2 / reverse_upper` at `n = 10`:
    - actual status split:
      - slot `0`: `9` seed-unsat
      - slot `1`: `5` completion-unsat, `4` seed-unsat
      - slot `2`: `5` completion-unsat, `4` seed-unsat
    - the old "missing cycle" assignments were exactly those eight seed-unsat
      mismatches
- Once the recurrence layer switches to the actual completion-unsat assignment
  set, `local_11k / reverse_base` packages cleanly:
  - anchor `n = 10`
  - base gaps `(1,1,5)`
  - base size `63`
  - slope `9`
  - losses `0`, gains `9`
  - verified at `n = 11`

### Reformulations
The new bottleneck is more precise:
- not "improve lexmin on all hard regimes,"
- but "use regime-correct completion branches, then see which branches still
  need better canonicalization."

That is a much stronger engineering position than the previous blanket
"selector wall" diagnosis.

LOAD-BEARING ASSESSMENT: very high. This converts one apparently blocked regime
into a working packaged law and shows exactly why the old diagnosis was wrong.

### Concrete Artifacts
CODE CHANGES:
- Extended `probes/gpt/glb_case3c_forced_spine_probe.py` with
  an `assignment_mode`:
  - `predicted_completion`
  - `actual_completion`
- The actual-completion mode computes the completion branch from the exact
  seeded/completion status table instead of the representative-family
  bottom-slot heuristic.
- Updated `probes/gpt/glb_case3c_regime_recurrence.py` to use
  `assignment_mode=actual_completion` by default.

NEW REGRESSION FACTS:
- `local_11k / reverse_base` now packages and verifies:
  - `n = 10`: size `63`
  - `n = 11`: size `72`
- The forced-spine probe now distinguishes:
  - predicted completion branch for `(1,1,5)` reverse-base:
    - `6` assignments, `4` bogus misses
  - actual completion branch:
    - `2` assignments, `0` misses

TEST COVERAGE:
- Extended `probes/gpt/tests/test_glb_case3c_forced_spine_probe.py`
  with an assignment-mode regression on the local branch.
- Updated `probes/gpt/tests/test_glb_case3c_regime_recurrence.py`
  so `local_11k / reverse_base` is now a positive packaged-law test instead of
  a failure expectation.

VERIFIED:
- `python3 -m py_compile probes/gpt/glb_case3c_forced_spine_probe.py`
- `python3 -m py_compile probes/gpt/glb_case3c_regime_recurrence.py`
- direct diagnostic of `local_11k / reverse_base`:
  - predicted branch misses exactly `[(1,0), (1,2), (2,0), (2,1)]`
  - actual branch has zero misses
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime local_11k --family reverse-base --base-n 10 --end-n 11 --verify-to 11 --derive-timeout-ms 1200 --verify-timeout-ms 1200`

### What Would Unblock This
- Apply the same actual-completion branch logic to the remaining expensive
  upper-family regimes and see which ones still truly need selector work.
- For `reverse_upper_trailing2`, decide whether the remaining problem is:
  - canonicalization cost only, or
  - genuinely unstable common spines across the ten completion-unsat words.

### Open Questions
- Does `reverse_upper_trailing2 / reverse_upper` package once given more time
  on the correct ten-word completion branch?
- Do any other symbolic regimes need late anchor shifts like the
  semi-symmetric base branch, or was that family special?
- After branch correction, how many of the remaining "hard" regimes are still
  genuinely selector-limited?

## Synthesis after exploration 28

This was the highest-value fix available. The recurrence layer had been asking
the wrong question on at least one whole symbolic regime. After correcting that
branch selection, `local_11k / reverse_base` moved from "blocked" to
"packaged." That is a better kind of progress than squeezing a few more seconds
out of lexmin, because it changes the model of where the difficulty actually
is.

## Exploration 29

### Strategy
Re-audit the previously packaged semi-symmetric base laws after the branch fix,
to see whether they still hold under the corrected actual-completion semantics
 or whether they were artifacts of the old representative-family branch
 heuristic.

### Outcome
SUCCEEDED

### Failure Constraint
This does not mean the semi-symmetric branch has no recurrence. It means the
previous positive recurrence statement was tied to the wrong branch semantics
and should not be carried forward unchanged.

### What This Rules Out
- This rules out treating the old `semi_symmetric_2plus` base laws as already
  established under the corrected regime-aware recurrence semantics.
- It does not rule out a later-anchor or broader all-completion recurrence on
  that family.

### Surviving Structure
- On the corrected exact status split, `semi_symmetric_2plus` at `n = 10`
  base orientations is all-completion:
  - reverse base: slot `0,1,2` all have `3` completion-unsat assignments
  - forward base: slot `0,1,2` all have `3` completion-unsat assignments
- So the previous predicted-branch recurrence was only following a strict
  completion sub-branch, not the full actual completion branch.
- Under actual-completion semantics, the old positive regression at `n = 12`
  fails, so the branch is now back in the unresolved bucket.

### Reformulations
The recurrence catalogue after branch correction is now:
- positively packaged:
  - `asymmetric_1ab / reverse_base`
  - `local_11k / reverse_base`
- not yet honestly packaged:
  - `semi_symmetric_2plus` base branches
  - `reverse_upper_trailing2 / reverse_upper`

LOAD-BEARING ASSESSMENT: high. This is a correction, not a setback. It removes
one false-positive recurrence claim and leaves the catalogue smaller but more
trustworthy.

### Concrete Artifacts
TEST CORRECTION:
- `probes/gpt/tests/test_glb_case3c_regime_recurrence.py`
  no longer treats the semi-symmetric base law as a positive regression under
  the corrected semantics.
- The regime recurrence file now keeps only:
  - representative continuity (`asymmetric_1ab / reverse_base`)
  - corrected local-branch packaging (`local_11k / reverse_base`)

VERIFIED:
- direct status audit for `(2,2,3)` base:
  - reverse: all `9` assignments completion-unsat
  - forward: all `9` assignments completion-unsat
- `python3 -m unittest -v probes.gpt.tests.test_glb_case3c_regime_recurrence`
  after removing the stale semi-symmetric positive regression

### What Would Unblock This
- Derive a recurrence directly on the full nine-word semi-symmetric completion
  branch instead of the old predicted sub-branch.
- Check whether a later anchor stabilizes that all-completion spine.

### Open Questions
- Does the semi-symmetric branch have a clean all-completion recurrence, or
  does it need a finer symbolic split beyond the current `semi_symmetric_2plus`
  label?
- Is the reverse/forward all-completion symmetry on `(2,2,k)` load-bearing for
  a future packaged law?

## Synthesis after exploration 29

After correcting the branch semantics, the regime recurrence layer is smaller
but much cleaner. The current positive catalogue is no longer inflated by a
semi-symmetric law that was following the wrong branch. That makes the next
step sharper: finish the corrected upper/trailing and semi-symmetric branches,
not by optimism, but by explicitly deriving the right completion set first.

## Exploration 30

### Strategy
Follow through on the corrected actual-completion semantics and rerun the two
remaining high-value families on their proper completion branches:
- `semi_symmetric_2plus` base
- `reverse_upper_trailing2` upper reverse

### Outcome
SUCCEEDED

### Failure Constraint
This still does not settle every upper-family regime, but it removes the last
major ambiguity introduced by the old representative-family branch heuristic.

### What This Rules Out
- This rules out the exploration-29 overcorrection that semi-symmetric base had
  to be dropped from the positive catalogue entirely.
- It also rules out treating `reverse_upper_trailing2` as still blocked once
  the branch semantics are corrected.

### Surviving Structure
- `semi_symmetric_2plus / reverse_base` packages cleanly on the full actual
  nine-word completion branch:
  - anchor `n = 10`
  - base size `60`
  - slope `9`
  - losses `13`, gains `22`
  - verified through `n = 12`
- `semi_symmetric_2plus / forward_base` also packages cleanly on the full
  actual nine-word completion branch:
  - anchor `n = 10`
  - base size `60`
  - slope `9`
  - losses `5`, gains `14`
  - verified through `n = 12`
- `reverse_upper_trailing2 / reverse_upper` packages cleanly once it uses the
  actual ten-word completion branch:
  - anchor `n = 10`
  - base size `46`
  - slope `9`
  - losses `5`, gains `14`
  - verified through `n = 11`

### Reformulations
The corrected positive recurrence catalogue is now:
- `asymmetric_1ab / reverse_base`
- `local_11k / reverse_base`
- `semi_symmetric_2plus / reverse_base`
- `semi_symmetric_2plus / forward_base`
- `reverse_upper_trailing2 / reverse_upper`

That is much stronger than the state at the end of exploration 27, and it came
from fixing branch semantics rather than from brute-force optimization.

LOAD-BEARING ASSESSMENT: very high. This is the first point where the regime
recurrence layer looks like a real reusable package catalogue rather than a
fragile exploratory shell.

### Concrete Artifacts
DIRECT VERIFIED COMMANDS:
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime semi_symmetric_2plus --family reverse-base --base-n 10 --end-n 12 --verify-to 12 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime semi_symmetric_2plus --family forward-base --base-n 10 --end-n 12 --verify-to 12 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime reverse_upper_trailing2 --family reverse-upper --base-n 10 --end-n 11 --verify-to 11 --derive-timeout-ms 1200 --verify-timeout-ms 1200`

TEST COVERAGE:
- `probes/gpt/tests/test_glb_case3c_regime_recurrence.py`
  now includes positive regressions for:
  - `local_11k / reverse_base`
  - `semi_symmetric_2plus / reverse_base`
  - `reverse_upper_trailing2 / reverse_upper`

VERIFIED:
- `python3 -m unittest -v probes.gpt.tests.test_glb_case3c_regime_recurrence.RegimeRecurrenceTests.test_semi_symmetric_reverse_base_packages_from_actual_completion_branch`
- `python3 -m unittest -v probes.gpt.tests.test_glb_case3c_regime_recurrence.RegimeRecurrenceTests.test_reverse_upper_trailing2_packages_from_actual_completion_branch`

### What Would Unblock This
- Push the corrected actual-completion recurrence catalogue onto the remaining
  upper families, especially `asymmetric_1ab / reverse_upper`.
- Look for a shared meta-law across the now-recovered `5/14` and `13/22`
  regime edits instead of treating each family as isolated.

### Open Questions
- Does `asymmetric_1ab / reverse_upper` also package cleanly under the
  corrected branch semantics?
- Are the surviving positive laws enough to write a finite regime verifier for
  all currently observed `n = 9,10,11` cases, or is one more upper-family law
  still missing?

## Synthesis after exploration 30

The branch-correction work paid off more than expected. It did not just rescue
`local_11k`; it restored the semi-symmetric base laws and unlocked the
reverse-upper trailing exception as well. The next highest-value work is no
longer "debug the recurrence layer." It is to finish the remaining upper-family
catalogue under the corrected semantics.

## Exploration 31

### Strategy
Push the corrected actual-completion recurrence packaging through the remaining
upper-family regime branches and the forward local branch, using the same
`n = 10 -> 11` anchor checks as before.

### Outcome
SUCCEEDED

### Failure Constraint
This does not prove the recurrence catalogue for all larger `n`, and it does
not yet package every conceivable gap class. It does show that the entire
observed small-`n` symbolic regime menu is now recurrence-shaped under the
correct branch semantics.

### What This Rules Out
- This rules out the idea that the upper families were the next major
  obstruction once the branch-selection bug was fixed.
- It does not rule out new regime behaviour at larger `n`, but it removes the
  current `n = 9,10,11` upper-family bottleneck.

### Surviving Structure
- Newly packaged under corrected semantics:
  - `asymmetric_1ab / reverse_upper`
    - anchor `n = 10`
    - base size `40`
    - slope `9`
    - losses `2`, gains `11`
    - verified at `n = 11`
  - `local_11k / forward_base`
    - anchor `n = 10`
    - base size `103`
    - slope `9`
    - losses `5`, gains `14`
    - verified at `n = 11`
  - `local_11k / forward_upper`
    - anchor `n = 10`
    - base size `85`
    - slope `9`
    - losses `6`, gains `15`
    - verified at `n = 11`
  - `local_11k / reverse_upper`
    - anchor `n = 10`
    - base size `51`
    - slope `9`
    - losses `2`, gains `11`
    - verified at `n = 11`
  - `semi_symmetric_2plus / reverse_upper`
    - anchor `n = 10`
    - base size `35`
    - slope `8`
    - losses `3`, gains `11`
    - verified at `n = 11`
  - `semi_symmetric_2plus / forward_upper`
    - anchor `n = 10`
    - base size `46`
    - slope `6`
    - losses `3`, gains `9`
    - verified at `n = 11`

### Reformulations
The corrected recurrence picture is now:
- the representative-family recurrence scripts were not isolated curiosities,
- the regime classifier was the missing abstraction,
- and the main engineering bug was incorrect completion-branch selection on the
  non-representative regimes.

For the currently observed small taxonomy, the remaining work is no longer
"find a regime law." It is:
- push the verified range upward,
- or compress the per-regime laws into a smaller meta-catalogue.

LOAD-BEARING ASSESSMENT: very high. This is the first point where the regime
catalogue looks close to operational rather than exploratory.

### Concrete Artifacts
DIRECT VERIFIED COMMANDS:
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime asymmetric_1ab --family reverse-upper --base-n 10 --end-n 11 --verify-to 11 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime local_11k --family forward-base --base-n 10 --end-n 11 --verify-to 11 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime local_11k --family forward-upper --base-n 10 --end-n 11 --verify-to 11 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime local_11k --family reverse-upper --base-n 10 --end-n 11 --verify-to 11 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime semi_symmetric_2plus --family reverse-upper --base-n 10 --end-n 11 --verify-to 11 --derive-timeout-ms 1200 --verify-timeout-ms 1200`
- `python3 probes/gpt/glb_case3c_regime_recurrence.py --regime semi_symmetric_2plus --family forward-upper --base-n 10 --end-n 11 --verify-to 11 --derive-timeout-ms 1200 --verify-timeout-ms 1200`

CURRENT CATALOGUE STATUS:
- base families:
  - `asymmetric_1ab`
  - `local_11k`
  - `semi_symmetric_2plus`
- upper families:
  - `asymmetric_1ab`
  - `local_11k`
  - `reverse_upper_trailing2`
  - `semi_symmetric_2plus`

### What Would Unblock This
- Package the remaining positive branches into a more compact verified test
  suite without making the runtime unreasonable.
- Search for meta-laws that explain why so many families still have slope `9`,
  and why the semi-symmetric upper families break to slopes `8` and `6`.
- Push selected corrected laws beyond `n = 11/12` to see which ones stabilize
  cleanly over longer ranges.

### Open Questions
- Are the `8` and `6` slopes on the semi-symmetric upper families genuine
  long-range laws or just short-anchor phenomena?
- Can the now-large regime catalogue be compressed into a smaller set of
  template edits by processor band?

## Synthesis after exploration 31

The corrected regime recurrence layer is no longer just plausible. It is now a
substantial working catalogue for the observed small taxonomy. The next
highest-value work has changed again: it is no longer about rescuing missing
branches, but about scaling and compressing the catalogue we now actually have.

## Exploration 32

### Strategy
Compress the corrected recurrence catalogue into a smaller meta-catalogue of
template laws, so later verifier work can target template classes instead of a
growing list of regime-family one-offs.

### Outcome
SUCCEEDED

### Failure Constraint
This is an observed template catalogue, not yet a theorem that these are the
only possible template laws for all larger `n`. It is a compression of the
current verified small-`n` regime catalogue.

### What This Rules Out
- This rules out the idea that the current recurrence layer is still just a bag
  of unrelated one-off laws.
- It does not rule out new template classes appearing at larger `n`, especially
  if the symbolic regime menu itself grows.

### Surviving Structure
- The current packaged regime catalogue compresses to `8` observed templates:
  - `reverse_base_light`
  - `reverse_base_dense`
  - `forward_base_uniform`
  - `reverse_upper_light`
  - `reverse_upper_trailing2`
  - `reverse_upper_semi`
  - `forward_upper_light`
  - `forward_upper_semi`
- Exact compression patterns:
  - forward base is already uniform across current regimes:
    - `asymmetric_1ab`
    - `local_11k`
    - `semi_symmetric_2plus`
    all map to `forward_base_uniform`
  - reverse base splits cleanly into:
    - light branch: `asymmetric_1ab`, `local_11k`
    - dense branch: `semi_symmetric_2plus`
  - reverse upper splits into:
    - light branch: `asymmetric_1ab`, `local_11k`
    - trailing-`2` exception
    - semi-symmetric branch
  - forward upper splits into:
    - light branch: `asymmetric_1ab`, `local_11k`
    - semi-symmetric branch
- The strongest meta-law signals now are:
  - light families often keep slope `9`
  - semi-symmetric upper families are the main slope outliers:
    - reverse upper: slope `8`
    - forward upper: slope `6`

### Reformulations
The recurrence object is now best viewed in two layers:
- layer 1: symbolic regime classifier
- layer 2: template catalogue

The per-regime law list is still useful, but it is no longer the cleanest
mental model. The template catalogue is the right object for the next verifier
design step.

LOAD-BEARING ASSESSMENT: very high. This is the first point where the current
law collection looks small enough to plausibly hand to a large-range verifier
without feeling ad hoc.

### Concrete Artifacts
NEW TOOL:
- Added `probes/gpt/glb_case3c_template_catalogue.py`, which:
  - records the current observed template classes,
  - maps regime/family pairs to templates,
  - prints either case-level or template-level summaries.

TEST COVERAGE:
- Added `probes/gpt/tests/test_glb_case3c_template_catalogue.py`
  covering:
  - case-to-template mapping,
  - compression of the forward-base and upper light families.

DIRECT OUTPUT:
- `python3 probes/gpt/glb_case3c_template_catalogue.py --mode templates`
  prints the current `8`-template catalogue, including:
  - slopes,
  - loss/gain counts,
  - processor-band support,
  - member cases.

VERIFIED:
- `python3 -m py_compile probes/gpt/glb_case3c_template_catalogue.py probes/gpt/tests/test_glb_case3c_template_catalogue.py`
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_template_catalogue`
- `python3 probes/gpt/glb_case3c_template_catalogue.py --mode templates`

### What Would Unblock This
- Replace the hand-maintained template catalogue with one derived
  automatically from the recurrence scripts once runtime permits.
- Search for second-order compression:
  - can `reverse_upper_light` and `forward_upper_light` be viewed as one
    orientation-parametrized template?
  - can the semi-symmetric upper templates be unified despite slopes `8` and
    `6`?

### Open Questions
- Are the upper semi-symmetric slopes `8` and `6` intrinsic, or do they become
  `9` after a different normalization/template view?
- Is `reverse_base_dense` the only genuinely dense base template, or will more
  appear at larger `n`?

## Synthesis after exploration 32

The project now has a credible compressed law object. It is no longer just a
paper proof plus a few witness scripts, and it is no longer just a growing pile
of regime-specific recurrences either. It is a symbolic regime classifier plus
an observed template catalogue. That is a much better starting point for any
attempt to scale this toward a large-`n` verifier.

## Exploration 33

### Strategy
Do the second-order compression directly: test whether the upper light and upper
semi template pairs should be treated as one orientation-parametrized object or
as genuinely unrelated templates.

### Outcome
PARTIAL SUCCESS

### Failure Constraint
This is still an observed meta-catalogue layer, not an automatically derived
theorem. The result depends on the currently packaged small-`n` recurrence laws.

### What This Rules Out
- This rules out the naive hope that the upper semi-symmetric pair is already
  one orientation-free normalized law. The observed slopes remain different:
  reverse upper semi is `8`, forward upper semi is `6`.
- It also rules out treating the upper light pair as one exact edit signature.
  The reverse light branch has `2` losses and `11` gains, while the forward
  light branch has `6` losses and `15` gains.

### Surviving Structure
- The upper light pair *does* compress one level higher as an
  orientation-parametrized meta-template:
  - same regime support: `asymmetric_1ab`, `local_11k`
  - same family scope: upper only
  - same size slope: `9`
  - different orientation variants of the edit law
- The upper semi pair also compresses one level higher as a meta-family:
  - same regime support: `semi_symmetric_2plus`
  - same family scope: upper only
  - same qualitative branch type: semi-symmetric all-completion
  - but not one orientation-free exact law at the current normalization
- The trailing-`2` reverse-upper branch remains a real singleton exception.

### Reformulations
The current upper catalogue is best viewed as:
- `upper_light_oriented`
- `upper_semi_oriented`
- `upper_exceptional_reverse`

So the `8` flat templates are not the end of the compression story. At the
upper-family level, they collapse further into `3` meta-templates.

LOAD-BEARING ASSESSMENT: medium-high. This does not yet prove the upper laws are
uniform in any deep theorem sense, but it clarifies the right interface for a
future large-range verifier: classify to a regime, then to a small upper
meta-template family, then dispatch to the orientation variant.

### Concrete Artifacts
UPDATED TOOL:
- Extended `probes/gpt/glb_case3c_template_catalogue.py` with:
  - explicit upper meta-template objects,
  - case-to-meta-template mapping,
  - grouped upper meta-template summaries via `--mode meta`.

UPDATED TESTS:
- Extended `probes/gpt/tests/test_glb_case3c_template_catalogue.py`
  to check:
  - case-to-meta-template mapping,
  - second-order grouping of the upper light and upper semi pairs.

VERIFIED:
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_template_catalogue`
- `python3 probes/gpt/glb_case3c_template_catalogue.py --mode meta`

### Open Questions
- Can the base templates also be compressed into orientation-parametrized
  meta-templates without losing too much exact information?
- Are the upper semi slopes `8` and `6` genuinely intrinsic, or do they become
  affine variants of one deeper corridor-growth law when tracked with a richer
  invariant than raw rule count?

## Synthesis after exploration 33

The upper catalogue is now much cleaner conceptually. The light and semi pairs
are not exact template matches, but they *are* higher-level orientation pairs.
That means the next scaling step should not chase exact law identity first. It
should look for deeper invariants that explain why these orientation variants
travel together even when their raw edit sets differ.

## Exploration 34

### Strategy
Freeze the current flat template laws as explicit data instead of leaving them
 scattered across tmp outputs and recurrence reruns. This is a prerequisite for
 any genuinely fast large-`n` dispatcher.

### Outcome
SUCCEEDED

### Failure Constraint
The static catalogue freezes the currently observed template edits; it does not
 yet freeze canonical base spines. So it is a stable update-law table, not a
 complete standalone large-`n` verifier by itself.

### What This Rules Out
- This rules out continuing to treat the current recurrence layer as something
  that must be re-derived from probes each time we want to use it.
- It does not rule out adding more template laws later if new regimes or new
  template classes appear.

### Surviving Structure
- All `8` current templates now have explicit stored gain/loss sets:
  - `reverse_base_light`
  - `reverse_base_dense`
  - `forward_base_uniform`
  - `reverse_upper_light`
  - `reverse_upper_trailing2`
  - `reverse_upper_semi`
  - `forward_upper_light`
  - `forward_upper_semi`
- The static table confirms the second-order picture:
  - light upper pair remains slope `9` with different orientation variants,
  - semi upper pair remains split at slopes `8` and `6`,
  - forward base remains genuinely uniform across current regimes,
  - reverse base still needs two variants: light and dense.

### Reformulations
The current Case `3c` architecture now has three layers:
- symbolic regime classifier
- flat template catalogue
- static exact edit-law table

That is much closer to a real starpower verifier interface. What is still
missing is the base-anchor layer, not the update-law layer.

LOAD-BEARING ASSESSMENT: high. This is the first point where the recurrence
machinery is packaged enough that a future `n=2000` dispatcher can be built
without solver derivation in the main path.

### Concrete Artifacts
NEW TOOL:
- Added `probes/gpt/glb_case3c_static_template_laws.py`, which:
  - stores the exact gain/loss sets for all current templates,
  - dispatches cases to static template laws,
  - provides a reusable `apply_template_step(...)` helper.

NEW TESTS:
- Added `probes/gpt/tests/test_glb_case3c_static_template_laws.py`
  covering:
  - count/slope consistency against the observed template catalogue,
  - case-to-static-law dispatch for representative branches.

VERIFIED:
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_static_template_laws`
- `python3 probes/gpt/glb_case3c_static_template_laws.py --mode summary`

### Open Questions
- Can the canonical base spines also be frozen cleanly enough to make a fully
  static large-`n` generator?
- Once anchors are frozen, does any part of the current Case `3c` path still
  need live solver work except audit mode?

## Synthesis after exploration 34

The update-law side of the starpower project is now much more concrete. We no
longer have to think of the current template catalogue as merely descriptive.
It is an explicit machine-readable law table. The remaining gap is now sharply
located: anchor generation and proof-backed coverage, not template edit data.

## Exploration 35

### Strategy
Build a proper anchor-freezing path instead of hand-copying spines out of
 ad hoc solver runs. Then freeze the whole base-family anchor layer, since that
 part of the catalogue is already tractable and exact.

### Outcome
PARTIAL SUCCESS

### Failure Constraint
Only the base-family anchors are frozen in this step. The upper-family anchors
 are still slower to snapshot and remain live-work items.

### What This Rules Out
- This rules out the idea that the project is still blocked on the anchor layer
  in a vague way. For base families, the anchor problem is now solved.
- It does not rule out new difficulty on the upper-family anchor side.

### Surviving Structure
- Added a reusable anchor snapshot tool for the whole current regime catalogue.
- Froze the exact six canonical base-family anchors:
  - reverse:
    - `asymmetric_1ab`
    - `local_11k`
    - `semi_symmetric_2plus`
  - forward:
    - `asymmetric_1ab`
    - `local_11k`
    - `semi_symmetric_2plus`
- The static base-anchor generator now works entirely from:
  - frozen base spine
  - frozen template law
- Known size checks from the frozen base anchor layer:
  - `local_11k / reverse_base`: `63 -> 72` from `n=10` to `n=11`
  - `semi_symmetric_2plus / forward_base`: `60 -> 78` from `n=10` to `n=12`

### Reformulations
The base-family side now has the full three-layer stack in explicit code:
- symbolic regime classifier
- static template law
- static canonical anchor

So for base families, the solver is no longer needed in the main generation
path at all.

LOAD-BEARING ASSESSMENT: high. This is the first genuinely solver-free slice of
the Case `3c` starpower architecture.

### Concrete Artifacts
NEW TOOL:
- Added `probes/gpt/glb_case3c_anchor_snapshot.py`, which:
  - snapshots exact canonical anchors from the live recurrence layer,
  - filters by case/regime/family,
  - emits either summaries or Python-ready anchor entries.

NEW STATIC LAYER:
- Added `probes/gpt/glb_case3c_static_base_anchors.py`, which:
  - stores the exact six base-family canonical anchors,
  - dispatches anchors by regime/family,
  - generates large-`n` base-family spines using the static template laws.

NEW TESTS:
- Added `probes/gpt/tests/test_glb_case3c_anchor_snapshot.py`
- Added `probes/gpt/tests/test_glb_case3c_static_base_anchors.py`

VERIFIED:
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_anchor_snapshot`
- `python3 -m unittest probes.gpt.tests.test_glb_case3c_static_base_anchors`
- `python3 probes/gpt/glb_case3c_static_base_anchors.py --mode summary`

### Open Questions
- Do the upper-family anchors admit the same clean freeze once captured
  individually?
- Is there a useful offset/compression relation between anchors that share the
  same template, or is a flat per-case anchor table the honest endpoint?

## Synthesis after exploration 35

The project has crossed an important threshold. The base families are no longer
research prototypes glued to solver reruns. They are now a static law table plus
static anchors, which is the right architecture for any future `n=2000` path.
The upper-family anchor freeze is now the main remaining engineering gap, not
the whole anchor question.

## Exploration 36

### Strategy
Pause and record the trust-boundary insight explicitly before any more
architecture work muddies it.

### Outcome
SUCCEEDED

### Core Insight
The current recurrence laws are still observational. Statements like
"reverse base grows by `+9` with `0` losses for all `n`" are not yet theorem-
backed replacements for the canonical extractor.

### What This Means
- A fully honest `n=2000` claim is not available yet from the static generator
  alone.
- To make a real `n=2000` claim, one of two things must happen:
  - direct path: run the exact canonical extractor at `n=2000` and confirm the
    real forced spine matches the predicted one;
  - proof-backed path: prove that the recurrence/update law is forced by local
    structure, so the static generator is mathematically equivalent to the
    extractor.

### What This Rules Out
- This rules out treating the current static law/anchor stack as already being
  a standalone certificate.
- It does not rule out the starpower program itself. It only sharpens the
  remaining burden.

### Reformulations
The current static layers should be read as infrastructure:
- they expose the candidate large-`n` object clearly,
- they make solver-free generation possible,
- but they do not yet justify skipping exact extraction at large `n`.

### Pause State
If the project resumed immediately, the honest next theorem-level target would
be:
- prove why the template update law is forced, or
- build a cheaper direct canonical verifier whose output can serve as the exact
  `n=2000` audit.

## Synthesis after exploration 36

The project is in a stronger engineering state than before, but the epistemic
boundary is now much clearer. We have a candidate starpower machine, not yet a
starpower certificate.
