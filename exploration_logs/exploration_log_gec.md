# Exploration Log

## Strategy Register

### Eliminated approach classes
- Loose entry-conflict scans that do not enforce cyclic mover adjacency at the wrap from the last mover back to the first are not reliable evidence for or against the GEC residue (exploration 1). Structural reason: the old non-consecutive anatomy script counts many locally closed words that fail the strict ring-adjacent condition used by the blocker pipeline, and those false positives can look “clean” even though every strict cycle still conflicts.
- Treating generic determinism clashes as a mover-vs-mover phenomenon is not the right lens for the normalized good-cycle search space (exploration 1). Structural reason: under the existing cycle normalization, every mover action is the canonical increment `S -> S+1 mod m`, so the observed strict conflicts are mover/nonmover overlaps, i.e. true entry conflicts, not competing mover outputs.
- Purely local “squeezed processor” theorems on the abstract `2 × m × 2` neighborhood graph are too weak to prove universal entry conflict (exploration 2). Structural reason: for `m = 3,4,5` there exist simple directed local cycles using left, center, and right moves with no mover/nonmover overlap at the center, so the real obstruction needs genuine ring-level constraints.
- The stronger `n <= 7` localization “some processor with two binary neighbors must conflict” is false in general (exploration 3). Structural reason: at `n = 8`, the strict cycle found in `(2,3,2,3,3,2,3,4)` keeps the unique two-binary-neighbor processor clean while forcing its only conflict at a processor with exactly one binary neighbor on a longer binary gap.
- The still-stronger boundary localization “some processor with at least one binary neighbor must conflict” is also false in general (exploration 4). Structural reason: the `n = 8` class `(2,3,3,2,3,3,2,4)` has a strict cycle with no entry conflicts anywhere on the ring.

### Obstructions
- Under the actual theorem hypothesis “pairwise non-adjacent binary + some `m_i >= 4` + product `< 4·3^(n-2)`”, there are no `n = 5` state vectors at all; the first live theorem-family case is `n = 6` (exploration 1).
- For the old `n = 5` mixed residue `(2,4,2,3,2)`, the apparent clean residue in `scripts/binscc_conflict_anatomy_nc.py` is an artifact of the loose cycle notion: there are `11110` loose cycles but only `3228` strict cycles, and all `3228` strict cycles have mover/nonmover overlap (exploration 1).
- In every exact or sampled strict mixed cycle checked so far, some processor with two binary neighbors already carries an entry conflict (exploration 1). Exact at `(2,4,2,3,2)`; sampled for the pairwise `n = 6,7` theorem families.
- Exact pairwise mixed theorem-family obstruction through `n = 7`: no strict cycle exists in which every processor with two binary neighbors is entry-conflict-free (exploration 2). Verified exactly for `(2,4,2,3,2,3)`, `(2,3,2,4,2,3,3)`, and `(2,3,3,2,4,2,3)`.
- The first `n = 8` boundary counterexample to the naive bn2 theorem occurs in `(2,3,2,3,3,2,3,4)` (exploration 3): there exists a strict cycle with the unique bn2 processor `P1` clean, and the sole conflict shifts to `P7`, which has one binary neighbor.
- Universal entry conflict is false for strict pairwise mixed cycles (exploration 4). Exact counterexample:
  - state counts `(2,3,3,2,3,3,2,4)`,
  - product `2592 < 4·3^6 = 2916`,
  - binaries at positions `0,3,6` (pairwise nonadjacent),
  - strict cycle word `(0,7,6,5,4,3,2,1,0,7,6,5,4,5,4,3,2,1,2,1,0,7,0,7)`,
  - no mover/nonmover or mover/mover entry conflict at any processor.

### Building blocks
- `scripts/gec_conflict_scan.py` (exploration 1): strict entry-conflict scanner for this residue. It
  enumerates dihedral state-vector classes under the `4·3^(n-2)` bound, streams ring-adjacent mover words, enforces the same strict cycle notion as the blocker scripts, and classifies conflicts as mover/nonmover overlap versus mover/mover clash.
- Streaming mover-word enumeration inside `scripts/gec_conflict_scan.py` (exploration 1): avoids materializing the full mover-word list before analysis, which is necessary for the slower `n = 7` theorem-family scans.
- Small-family enumerator inside `scripts/gec_conflict_scan.py` (exploration 1): exact dihedral class generation for the theorem hypothesis at fixed `n`, useful for separating the real pairwise-nonadjacent family from the older “no triple run” experiments.
- `find_bn_clean_cycle` inside `scripts/gec_conflict_scan.py` (exploration 2): DFS search for a strict cycle with no mover/nonmover overlap at processors having a specified number of binary neighbors. It prunes incrementally on local-context overlap and was strong enough to close the exact pairwise mixed families through `n = 7`.
- All-processor clean-cycle search via `find_bn_clean_cycle(..., min_neighbors=0)` (exploration 4): same DFS machinery, now targeting every processor. This was strong enough to sweep all 13 pairwise mixed `n = 8` classes and isolate the unique clean strict-cycle class.

### Known reformulations
- Strict entry-conflict lens: in the normalized good-cycle model, the only relevant cycle-level determinism obstruction is mover/nonmover overlap of the same `(proc, L, S, R)` entry. LOAD-BEARING: high. This removes mover/mover noise and makes the target statement exactly “some processor repeats a mover context as a nonmover context.”
- Squeezed-processor reformulation: the conflict mechanism appears to localize on processors sitting in binary-to-binary gaps, especially processors with two binary neighbors. LOAD-BEARING: promising. Exact for the `n = 5` mixed residue and present in every sampled pairwise `n = 6,7` theorem-family cycle; suggests replacing a global search for “some conflict somewhere” by a local theorem on binary-gap interfaces.
- Counterexample-as-clean-cycle reformulation: instead of cataloging where conflicts occur after enumeration, search directly for a strict cycle whose designated squeezed processors remain clean. LOAD-BEARING: high. This converts the localization claim into an incremental DFS invariant and closed the exact pairwise mixed theorem families through `n = 7`.
- Gap-end reformulation: the right local object is not just a processor with two binary neighbors, but the whole binary gap and in particular its entry/exit processors next to the binary endpoints. LOAD-BEARING: high. Exploration 3 shows the conflict can migrate from the squeezed center of a short gap to a one-binary-neighbor endpoint of a longer gap.
- Full-clean counterexample search: search directly for a strict cycle with no entry conflict at any processor. LOAD-BEARING: very high. Exploration 4 uses this to disprove the universal entry-conflict conjecture on the exact `n = 8` pairwise mixed frontier.

## Session Start (2026-03-10)

Resuming from exploration 0.

No prior `exploration_log_gec.md` existed in the repository, so there is no earlier GEC-specific state to reuse.

Next attempt: replace the loose non-consecutive conflict anatomy with a strict scanner using the same good-cycle notion as the blocker scripts, then use that cleaned-up view to localize where the forced entry conflicts actually occur in the mixed residue.

## Exploration 1

### Strategy
Build a strict conflict scanner matching the blocker pipeline, use it to remove artifacts from the loose anatomy script, and see whether the remaining conflicts localize to a smaller proof-facing part of the ring.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- Any argument that leans on the old `scripts/binscc_conflict_anatomy_nc.py` “valid cycle” counts without rechecking cyclic mover adjacency. The six apparent clean cycles in `(2,4,2,3,2)` are not real strict cycles.
- Any attempt to explain the residue through generic inconsistent mover outputs. In the normalized cycle space now in use, the observed strict conflicts are entry overlaps, not mover/mover branch points.

### Surviving Structure
- The strict conflict picture is much cleaner than the loose one: once the wrap-adjacency condition is enforced, the mixed `n = 5` residue `(2,4,2,3,2)` has zero clean cycles.
- The theorem-family enumeration is tiny at small `n`:
  - `n = 5`: no pairwise-nonadjacent mixed classes;
  - `n = 6`: one dihedral class `(2,3,2,3,2,4)`;
  - `n = 7`: two dihedral classes `(2,3,2,3,2,3,4)` and `(2,3,2,3,3,2,4)`.
- The conflict mass localizes strongly to squeezed processors between binary pairs:
  - exact for `(2,4,2,3,2)`: every strict cycle has a conflict at the quaternary `P1`, which has two binary neighbors;
  - sampled for the pairwise theorem families at `n = 6,7`: every sampled strict cycle has a conflict at some processor with two binary neighbors, while binary conflicts occur only in a minority of sampled cycles.

### Reformulations
- The right object is not “determinism conflict” in general but strict mover/nonmover overlap. For the normalized good-cycle search, mover/mover clashes are a red herring.

LOAD-BEARING ASSESSMENT: High. This reduces the residue to the exact statement the user wants: prove that some processor repeats a mover context as a nonmover context.

- The second useful reformulation is geometric: the overlap seems to live on squeezed processors in binary-to-binary gaps, not arbitrarily around the ring. For short gaps this is literally a processor with two binary neighbors; for longer gaps the right analogue is likely an endpoint or compressed local transducer on the arc.

LOAD-BEARING ASSESSMENT: Promising. It changes the search space from “all processors on the ring” to “binary-gap interfaces,” which is much smaller and more structured.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exact theorem-family dihedral classes under the real pairwise-nonadjacent mixed hypothesis:
  - `n = 5`: `[]`
  - `n = 6`: `[(2,3,2,3,2,4)]`
  - `n = 7`: `[(2,3,2,3,2,3,4), (2,3,2,3,3,2,4)]`
- Old loose-vs-strict discrepancy for `(2,4,2,3,2)`:
  - loose cycle count from `scripts/binscc_conflict_anatomy_nc.py`: `11110`
  - strict cycle count using the blocker notion: `3228`
- Exact strict conflict summary for `(2,4,2,3,2)`:
  - strict cycles: `3228`
  - clean strict cycles: `0`
  - cycle-level conflict kinds: `{'mover_nonmover': 3228}`
  - processors with two binary neighbors hit by conflict:
    - `P1`: `3228/3228` cycles
    - `P3`: `2820/3228` cycles
- Sampled strict conflict summaries in the actual pairwise theorem families:
  - `(2,4,2,3,2,3)`: in the first `200` strict cycles, all `200` have a conflict at some processor with two binary neighbors; binary processors conflict in `57/200`.
  - `(2,3,2,4,2,3,3)`: in the first `100` strict cycles, all `100` have a conflict at some processor with two binary neighbors; `P3` (the quaternary with two binary neighbors) is hit in all `100`, `P1` in `64`.
  - `(2,3,3,2,4,2,3)`: in the first `100` strict cycles, all `100` have a conflict at some processor with two binary neighbors; `P4` (the quaternary with two binary neighbors) is hit in all `100`, `P6` in `91`.

STRUCTURAL RESULTS:
- The apparent “clean” mixed residue at `n = 5` vanishes under the strict good-cycle notion.
- In the exact `n = 5` mixed residue, strict entry conflict is universal and already visible at a squeezed processor with two binary neighbors.
- In every sampled strict pairwise mixed cycle at `n = 6,7`, some squeezed processor with two binary neighbors already conflicts.

TOOLS:
- `scripts/gec_conflict_scan.py`
  - Inputs:
    - explicit state vectors via `--state-counts`
    - or all dihedral classes below `4·3^(n-2)` for selected `n` via `--n`
    - binary-spacing mode via `--binary-mode pairwise|no_triple_run`
  - Outputs:
    - strict cycle counts
    - mover/nonmover vs mover/mover conflict classification
    - conflict localization by processor and by number of binary neighbors
    - sample conflicting mover words

REPRESENTATIONS:
- Strict local-context conflict representation: each processor is tracked by the set of mover contexts and nonmover contexts it sees on the cycle; conflict means set overlap.
- Binary-gap localization: classify a processor by how many binary neighbors it has (`0,1,2`) and ask where the overlap actually lands.

### What Would Unblock This
- A local theorem for a squeezed processor or squeezed arc: given a processor in a binary-to-binary gap, prove that the local context walk must revisit some mover context as a nonmover context.
- For longer binary gaps, the smallest useful next artifact would be a compressed “arc transducer” model that replaces a length-`d` ternary/quaternary chain between binary endpoints by an effective local interface seen by the first processor next to one endpoint.
- Operationally, a faster sharded or progress-reporting strict word enumerator would make full `n = 7` theorem-family exhaustion practical inside this scanner rather than only sampled.

### Key Parameters
- Mixed residue checked exactly: `(2,4,2,3,2)` with `max_len = 21`.
- Pairwise theorem-family classes identified:
  - `n = 6`: `(2,3,2,3,2,4)` up to dihedral symmetry
  - `n = 7`: `(2,3,2,3,2,3,4)` and `(2,3,2,3,3,2,4)` up to dihedral symmetry
- Sample sizes on pairwise classes:
  - `n = 6`: first `200` strict cycles on `(2,4,2,3,2,3)`
  - `n = 7`: first `100` strict cycles on each of `(2,3,2,4,2,3,3)` and `(2,3,3,2,4,2,3)`

### Open Questions
- Is the “conflict at a processor with two binary neighbors” phenomenon exact for the full pairwise `n = 6,7` theorem families, or only overwhelmingly dominant?
- Can the squeezed-quaternary phenomenon be proved directly when the unique `m_i >= 4` processor lies between two binaries?
- What is the right replacement for “processor with two binary neighbors” when all binary gaps have length `>= 2`, which is the real `n >= 8` difficulty?

## Synthesis after exploration 1

The conflict residue is now cleaner and more local than it looked at the start of the session. The first cleanup is methodological: the loose anatomy script was mixing in non-cyclic words, which is why it seemed to leave a tiny clean residue in `(2,4,2,3,2)`. Once the strict good-cycle notion is restored, that residue disappears completely and the conflict is pure mover/nonmover overlap. The second cleanup is geometric: the overlap is not wandering randomly around the ring. In every exact or sampled mixed case I checked, some squeezed processor in a binary-to-binary gap already carries the contradiction, and in the exact `n = 5` mixed class the squeezed quaternary is universal. That points to the next proof move: do not try to prove “some processor conflicts” globally. Prove a local overlap theorem on a binary-gap interface, then generalize from a single squeezed processor to a compressed longer gap.

## Exploration 2

### Strategy
Test whether the “two binary neighbors” phenomenon can be made exact by searching directly for strict good cycles in which every such squeezed processor stays clean, and compare that ring-level search with the weaker purely local `2 × m × 2` neighborhood model.

### Outcome
SUCCEEDED

### Failure Constraint
The strongest local version fails: the isolated neighborhood graph already admits clean directed cycles. So any proof has to use ring-level movement constraints, not just the local availability of left/center/right transitions around one squeezed processor.

### What This Rules Out
- Any proof that only studies the induced dynamics on one squeezed processor and its two binary neighbors, without using how the rest of the ring forces returns to that neighborhood.
- Any attempt to derive universal conflict at the squeezed processor from local-state graph impossibility alone.

### Surviving Structure
- The ring-level clean-cycle reformulation is much stronger than the raw local graph:
  - the abstract local graph has clean cycles for `m = 3,4,5`;
  - nevertheless, the exact pairwise mixed theorem families through `n = 7` have no strict cycle in which all two-binary-neighbor processors stay clean.
- The new pruned DFS is unexpectedly sharp:
  - `(2,4,2,3,2)` closes with `20311` search nodes;
  - `(2,4,2,3,2,3)` closes with `9114` nodes;
  - `(2,3,2,4,2,3,3)` and `(2,3,3,2,4,2,3)` both close with `1603419` nodes.
- So the exact localization statement now holds for all live pairwise mixed classes below `4·3^(n-2)` up to `n = 7`.

### Reformulations
- “Look for a clean counterexample, not for all conflicts.” The designated clean set is the processors with two binary neighbors, and the DFS prunes as soon as one of them repeats a mover context as a nonmover context.

LOAD-BEARING ASSESSMENT: High. This makes the localization statement itself a search invariant, not a post-processing statistic.

- The failed local-graph probe clarifies the needed theorem shape: the obstruction is not a forbidden local cycle on the squeezed neighborhood, but a forbidden embedding of such a local cycle into a full fair ring-adjacent global cycle.

LOAD-BEARING ASSESSMENT: High. It cleanly separates what the local picture can and cannot prove.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Clean local cycles on the abstract squeezed-processor graph:
  - `m = 3`: a length-9 simple directed cycle exists using labels `L,S,L,S,L,R,L,S,R`.
  - `m = 4`: a length-12 simple directed cycle exists using labels `L,S,L,S,L,S,L,R,L,S,L,R`.
  - `m = 5`: a length-13 simple directed cycle exists using labels `L,S,L,S,L,S,L,S,L,R,L,S,R`.
- Exact ring-level bn-clean searches:
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,4,2,3,2 --search-bn-clean --binary-mode no_triple_run`
    reports `target_procs=[1,3]`, `nodes=20311`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,4,2,3,2,3 --search-bn-clean`
    reports `target_procs=[1,3,5]`, `nodes=9114`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,2,4,2,3,3 --search-bn-clean`
    reports `target_procs=[1,3]`, `nodes=1603419`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,3,2,4,2,3 --search-bn-clean`
    reports `target_procs=[4,6]`, `nodes=1603419`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.

STRUCTURAL RESULTS:
- The abstract squeezed-neighborhood graph does not forbid clean center behavior by itself.
- Despite that, every exact pairwise mixed theorem-family search through `n = 7` forces an entry conflict at a processor with two binary neighbors before a strict cycle can close.

TOOLS:
- Extended `scripts/gec_conflict_scan.py` with:
  - `target_binary_neighbor_procs`
  - `context_index_map`
  - `find_bn_clean_cycle`
  - CLI flag `--search-bn-clean`

REPRESENTATIONS:
- Clean-cycle counterexample representation: a putative counterexample is a strict mover word together with incremental mover/nonmover context masks that stay disjoint on the designated squeezed processors.
- Local squeezed-neighborhood graph on states `(L,S,R) in {0,1} × Z_m × {0,1}` with move labels `L`, `S`, `R`; useful mainly as a negative control now that clean local cycles are known to exist.

### What Would Unblock This
- A paper-style structural explanation for why the clean local cycles on `2 × m × 2` cannot embed into a fair ring-adjacent global cycle once there are at least three pairwise nonadjacent binaries.
- For the `n >= 8` regime, the next useful compressed object is a binary-gap transducer that tracks not just the squeezed processor but how a local clean pattern would have to be entered and exited through the surrounding arc.
- If another exact computation is needed, the natural next target is `n = 8` pairwise mixed families below `4·3^(n-2)`, but that should probably use the bn-clean DFS directly rather than the older post-hoc scanner.

### Key Parameters
- Local negative-control graph checked for `m = 3,4,5`.
- Exact ring-level clean-cycle searches run on:
  - `(2,4,2,3,2)`
  - `(2,4,2,3,2,3)`
  - `(2,3,2,4,2,3,3)`
  - `(2,3,3,2,4,2,3)`
- Target processors were exactly those with two binary neighbors.

### Open Questions
- What global feature forbids embedding the clean local squeezed cycles into the full ring?
- Can the bn-clean DFS invariant be rephrased as a finite “gap interface” lemma rather than a search procedure?
- At `n >= 8`, when every binary gap can be longer than one, what is the correct replacement for the two-binary-neighbor target set?

## Synthesis after exploration 2

The search space split is now much sharper. The pure local picture is officially not enough: one squeezed processor with two binary neighbors can support a clean local cycle on its own. So the entry-conflict theorem is genuinely about how that local pattern interacts with the rest of the ring. But that interaction is already strong enough to close the exact pairwise mixed families through `n = 7` by direct search. In other words, the right theorem shape is not “the squeezed processor cannot cycle cleanly,” but “a clean squeezed cycle cannot be embedded in a fair ring-adjacent global cycle when three pairwise nonadjacent binaries are present.” That is the structural gap to attack next.

## Exploration 3

### Strategy
Push the clean-cycle search to the first `n = 8` pairwise mixed classes to see whether the exact `n <= 7` bn2 localization survives once 4-binary classes and longer binary gaps appear.

### Outcome
SUCCEEDED

### Failure Constraint
The bn2 localization is not stable beyond `n = 7`. In an `n = 8` class with one short gap and one longer gap, a strict cycle can keep the unique two-binary-neighbor processor clean while shifting the conflict to an endpoint processor on the longer gap.

### What This Rules Out
- Any theorem whose conclusion is specifically “some processor with two binary neighbors conflicts” for all pairwise mixed systems.
- Any proof architecture that treats the squeezed center of the shortest gap as the only possible conflict location.

### Surviving Structure
- The bn-clean DFS still kills some representative `n = 8` classes immediately:
  - alternating 4-binary class `(2,3,2,3,2,3,2,4)` closes with no bn-clean strict cycle;
  - mixed 4-binary class `(2,3,2,4,2,3,2,4)` also closes with no bn-clean strict cycle.
- But the 3-binary class `(2,3,2,3,3,2,3,4)` is different:
  - target set `{P1}` (the only processor with two binary neighbors) stays clean on a strict cycle of length `24`;
  - the unique conflict moves to `P7` with context `(2,2,0) -> 3`, and `P7` has exactly one binary neighbor.
- So the right proof object has to see at least one whole longer binary gap, not just its squeezed center.

### Reformulations
- Replace “two-binary-neighbor processor” by “binary-gap interface.” The found `n = 8` cycle suggests the real invariant should track how a clean short-gap center couples to the entry/exit behavior on an adjacent longer gap, where the actual conflict may appear.

LOAD-BEARING ASSESSMENT: High. This is the first concrete evidence about how the conflict can move while remaining tied to the binary-gap geometry.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Representative `n = 8` bn-clean searches:
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,2,3,2,3,2,4 --search-bn-clean`
    reports `target_procs=[1,3,5,7]`, `nodes=23992`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,2,4,2,3,2,4 --search-bn-clean`
    reports `target_procs=[1,3,5,7]`, `nodes=68136`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,2,3,3,2,3,4 --search-bn-clean`
    reports `target_procs=[1]`, `nodes=6750`, `strict_bn_clean_cycles_checked=1`, and finds the strict cycle
    `(0,7,6,5,4,3,2,1,0,7,6,5,4,3,4,3,2,1,0,1,0,7,6,7)`.
- Conflict anatomy of that found `n = 8` cycle:
  - exact strict cycle length: `24`
  - number of conflicts: `1`
  - sole conflict:
    `ConflictRecord(proc=7, ctx=(2, 2, 0), kind='mover_nonmover', outputs=(3,), binary_neighbors=1, is_binary=False)`

STRUCTURAL RESULTS:
- The exact bn2 theorem survives through `n = 7` but fails already at `n = 8`.
- The first failure mode does not remove conflict; it relocates it to a one-binary-neighbor endpoint of a longer binary gap.

TOOLS:
- Reused `scripts/gec_conflict_scan.py --search-bn-clean` on the first representative `n = 8` classes and reused `analyze_cycle` to inspect the resulting counterexample.

REPRESENTATIONS:
- Binary-gap endpoint view: in the `n = 8` counterexample class, the clean short-gap center is compatible with a unique conflict at the far endpoint of a longer wrap gap.

### What Would Unblock This
- A generalized clean-cycle search over processors with at least one binary neighbor, not just exactly two, to test whether the conflict always remains on the binary-gap boundary.
- A compressed representation of a binary gap by its endpoint transducers, so the `n = 8` counterexample can be understood as a statement about clean internal transport versus forced conflict at one exit.

### Key Parameters
- `n = 8` pairwise mixed representative classes tested:
  - `(2,3,2,3,2,3,2,4)`
  - `(2,3,2,4,2,3,2,4)`
  - `(2,3,2,3,3,2,3,4)`
- In the counterexample class, binary positions are `0,2,5`; the bn2-clean target set is `{1}`.

### Open Questions
- Is “some processor adjacent to a binary conflicts” the right global replacement for the failed bn2 theorem?
- Can the `n = 8` counterexample be decomposed into a clean short-gap gadget feeding a forced-conflict long-gap endpoint gadget?
- Among the remaining `n = 8` classes, does every bn-clean witness still force a conflict on the union of one-binary-neighbor and two-binary-neighbor processors?

## Synthesis after exploration 3

The localization story just got more precise. Through `n = 7`, “watch the squeezed processors with two binary neighbors” was not just a good heuristic; it was exact on the full pairwise mixed family. At `n = 8`, that exact statement breaks, but in a very informative way: the conflict does not disappear into the interior of the ring. It slides to a processor with one binary neighbor at the endpoint of a longer binary gap. So the right invariant is still binary-gap-local, but not center-local. The next proof move should target the whole gap boundary, probably by searching for cycles that keep every binary-adjacent processor clean and seeing whether that stronger statement survives.

## Exploration 4

### Strategy
Test the stronger binary-boundary hypothesis by searching for strict cycles that keep every processor with at least one binary neighbor clean, and if that fails, push all the way to a full clean-cycle search over every processor on the exact `n = 8` pairwise mixed frontier.

### Outcome
SUCCEEDED

### Failure Constraint
The binary-boundary hypothesis is false. In the exact `n = 8` pairwise mixed frontier, one class admits a strict cycle with no entry conflict anywhere, so universal entry conflict is not the right theorem beyond `n = 7`.

### What This Rules Out
- The original GEC mission as stated: universal entry conflict for all pairwise mixed systems with at least three nonadjacent binaries.
- Any proof strategy that tries to close the remaining theorem solely by proving every candidate good cycle already contains an entry conflict.

### Surviving Structure
- The counterexample is very sparse on the exact `n = 8` frontier:
  - among all `13` pairwise mixed `n = 8` dihedral classes below `4·3^(n-2)`,
    only one class produced a fully clean strict cycle under the current search.
- The previous boundary counterexample class `(2,3,2,3,3,2,3,4)` does **not** admit a fully clean strict cycle; it only defeats the narrower bn2 and binary-boundary localizations.
- So the clean phenomenon is real but not ubiquitous. It may belong to a narrow subfamily rather than a generic `n = 8` effect.

### Reformulations
- The clean-cycle question should now be treated as a classification problem, not a proof target: which mixed pairwise classes admit a fully clean strict cycle, and what structural feature distinguishes them from the classes that do not?

LOAD-BEARING ASSESSMENT: Very high. The conjectured universal obstruction is false, so the productive path is to understand the counterexample family and pivot the proof architecture accordingly.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Binary-boundary test on the earlier `n = 8` bn2 counterexample class:
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,2,3,3,2,3,4 --search-bn-clean --min-binary-neighbors 1`
    reports `target_procs=[1,3,4,6,7]`, `nodes=442205`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.
- Full clean-cycle confirmation for the exact counterexample class:
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,3,2,3,3,2,4 --search-bn-clean --min-binary-neighbors 0`
    reports `target_procs=[0,1,2,3,4,5,6,7]`, `nodes=222`, `strict_bn_clean_cycles_checked=1`,
    and finds the clean strict cycle
    `(0,7,6,5,4,3,2,1,0,7,6,5,4,5,4,3,2,1,2,1,0,7,0,7)`.
- Exact full-clean sweep over all pairwise mixed `n = 8` classes:
  - `python3 -u scripts/gec_conflict_scan.py --n 8 --search-bn-clean --min-binary-neighbors 0`
    found a clean strict cycle in exactly one class:
    `(2,3,3,2,3,3,2,4)`.
  - The other `12` classes returned `no bn-clean strict cycle found` with node counts between `20748` and `118513`.
- Cross-checks on the clean cycle for `(2,3,3,2,3,3,2,4)`:
  - `analyze_cycle(...)` returns `[]` (no conflicts).
  - `get_determined_entries(...)` succeeds with `70` determined entries.
  - `check_mnu(...)` fails: example violation `(19, 1, 0, 0, 0, 3, [0,20,23])`.
  - `check_escape(...)` fails with `2` failures out of `3288` checked forced moves.
  - `find_shadow(...)` returns `None` on that cycle.

STRUCTURAL RESULTS:
- Entry conflict is not universal.
- The first exact clean strict-cycle counterexample appears at `n = 8` in the class `(2,3,3,2,3,3,2,4)`.
- The counterexample is still blocked by other obstructions already in play here, specifically MNU and Escape.

TOOLS:
- Reused `find_bn_clean_cycle` with `--min-binary-neighbors 0` as an all-processor clean-cycle search.

REPRESENTATIONS:
- Exact `n = 8` frontier classification by clean strict-cycle existence:
  - `12` classes: no clean strict cycle found.
  - `1` class: clean strict cycle found, namely `(2,3,3,2,3,3,2,4)`.

### What Would Unblock This
- A structural explanation for why `(2,3,3,2,3,3,2,4)` admits a clean cycle while the other `12` exact `n = 8` classes do not.
- A pivot from entry conflict to a hybrid obstruction: classify the clean-cycle classes, then show they are all killed by MNU, Escape, or another ring-level mechanism.
- If the clean class extends to larger `n`, the smallest useful next artifact is a family description of its mover-word/gap pattern, not another universal-conflict search.

### Key Parameters
- Exact search domain: all `13` pairwise mixed `n = 8` dihedral classes below `4·3^(n-2)`.
- Unique clean strict-cycle class found:
  - state counts `(2,3,3,2,3,3,2,4)`
  - mover word length `24`

### Open Questions
- Is `(2,3,3,2,3,3,2,4)` the first member of an infinite clean-cycle family?
- What geometric feature distinguishes the unique clean class from the other `12` exact `n = 8` classes?
- After abandoning universal entry conflict, what is the cleanest theorem statement that still closes the remaining lower-bound program?

## Synthesis after exploration 4

The residue has changed character completely. Up through `n = 7`, entry conflict looked like it might be the missing universal obstruction. Exploration 4 shows that it is not: the exact `n = 8` frontier already contains a fully clean strict cycle. But the disproof is highly structured, not chaotic. The clean class is unique among the 13 exact pairwise mixed `n = 8` classes, and even that class is still killed by MNU and Escape. So the right next move is not to keep chasing a false universality claim. It is to understand the clean class as a geometric family and then fold it into a hybrid obstruction theorem: entry conflict handles most classes, while MNU/Escape (or a refined gap mechanism) handles the exceptional clean family.

## Exploration 5 (probe)

### Strategy
Test whether the unique clean `n = 8` class extends to the most obvious nearby `n = 9` one-quaternary, three-binary classes obtained by inserting one extra ternary or shifting the quaternary locally.

### Outcome
FAILED

### Concrete Artifacts
- Full-clean `n = 9` probes, all negative:
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,3,2,3,3,2,3,4 --search-bn-clean --min-binary-neighbors 0`
    reports `nodes=344464`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,3,2,3,3,3,2,4 --search-bn-clean --min-binary-neighbors 0`
    reports `nodes=388484`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.
  - `python3 -u scripts/gec_conflict_scan.py --state-counts 2,3,3,2,3,3,2,4,3 --search-bn-clean --min-binary-neighbors 0`
    reports `nodes=344464`, `strict_bn_clean_cycles_checked=0`, `no bn-clean strict cycle found`.

## Exploration 6

### Strategy
Classify the exact pairwise mixed frontiers at `n = 8` and `n = 9` by full clean strict-cycle existence, to determine whether the `n = 8` counterexample is isolated or extends into the next frontier.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The idea that the clean strict-cycle counterexample is already a broad `n >= 8` family visible on the exact `n = 9` frontier.
- The idea that the `n = 8` clean class is common among nearby pairwise mixed classes.

### Surviving Structure
- The clean phenomenon is extremely sparse:
  - exact `n = 8` frontier: `13` pairwise mixed classes, exactly `1` clean class;
  - exact `n = 9` frontier: `35` pairwise mixed classes, `0` clean classes.
- So the current evidence points to an isolated `n = 8` exceptional class, not an obvious monotone family.

### Reformulations
- Clean-class classification by frontier, not by anecdote: treat each exact mixed frontier as a finite family and ask for the subset admitting fully clean strict cycles.

LOAD-BEARING ASSESSMENT: High. This turns the exception from a vague worry into a sharply bounded residue: unique at `n = 8`, absent at `n = 9` on the exact frontier.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exact `n = 8` pairwise mixed frontier:
  - `13` dihedral classes total.
  - full-clean sweep via
    `python3 -u scripts/gec_conflict_scan.py --n 8 --search-bn-clean --min-binary-neighbors 0`
    finds a clean strict cycle in exactly one class:
    `(2,3,3,2,3,3,2,4)`.
- Exact `n = 9` pairwise mixed frontier:
  - `35` dihedral classes total.
  - bin-count split: `{3: 10, 4: 25}`.
  - product split: `{5184: 3, 6480: 3, 6912: 6, 7776: 13, 8640: 10}`.
  - full-clean sweep via
    `python3 -u scripts/gec_conflict_scan.py --n 9 --search-bn-clean --min-binary-neighbors 0`
    finds no clean strict cycle in any of the `35` classes.

STRUCTURAL RESULTS:
- The exact clean-class counts are:
  - `n = 8`: `1 / 13`
  - `n = 9`: `0 / 35`
- Therefore the clean strict-cycle exception is not already propagating to the next exact frontier.

TOOLS:
- Reused `scripts/gec_conflict_scan.py --search-bn-clean --min-binary-neighbors 0` as a frontier-wide clean-cycle classifier.

REPRESENTATIONS:
- Frontier classification table:
  - each dihedral state-count class is marked `clean` or `non-clean` according to the existence of a fully clean strict cycle under the current search model.

### What Would Unblock This
- Exact enumeration of all clean strict cycles inside the unique `n = 8` clean class, so we can test whether MNU/Escape kills the entire clean residue or only the first witness.
- A structural description of what makes `(2,3,3,2,3,3,2,4)` special among the 13 exact `n = 8` classes.

### Key Parameters
- Exact frontiers classified:
  - `n = 8`: `13` classes
  - `n = 9`: `35` classes

### Open Questions
- Is the unique clean `n = 8` class the only clean strict-cycle exception on all exact frontiers checked so far?
- Are all clean strict cycles in `(2,3,3,2,3,3,2,4)` killed by MNU/Escape, or only some?
- What structural feature disappears between the unique clean `n = 8` class and its nearby negative `n = 9` continuations?

## Synthesis after exploration 6

The frontier picture is now surprisingly favorable. The clean strict-cycle exception is real, so universal entry conflict is dead; but the exception is not proliferating. It is unique on the exact `n = 8` frontier and absent on the exact `n = 9` frontier. That sharply changes the replacement theorem problem: we do not need a giant new family theory unless the unique `n = 8` clean class hides many internal variants. The next productive move is to exhaust the clean cycles inside that one class and show they are all killed by MNU/Escape or by a still-finer hybrid obstruction.

## Exploration 7

### Strategy
Exhaust the full clean strict-cycle family inside the unique clean class `(2,3,3,2,3,3,2,4)`, then classify the resulting cycles by length, mover-count profile, and whether MNU/Escape/shadow survives on any member.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The idea that only the first clean witness is killed by MNU/Escape while other clean cycles in the same class survive.
- The idea that the clean class hides a large variety of cycle lengths or mover-distributions requiring many different case analyses.

### Surviving Structure
- The clean residue inside `(2,3,3,2,3,3,2,4)` is finite and highly rigid:
  - exactly `288` clean strict cycles were found (under the current enumeration model);
  - every one has length `24`;
  - the mover-count vector is always one of two profiles:
    - `(4,3,3,2,3,3,2,4)` on `144` cycles,
    - `(2,3,3,2,3,3,4,4)` on `144` cycles.
- Every clean strict cycle in this class is still killed by the global obstructions already present:
  - `288 / 288` fail MNU,
  - `288 / 288` fail Escape,
  - `288 / 288` exhibit no shadow witness under the current `find_shadow` test.

### Reformulations
- Replace “the clean class exists” with the much stronger finite statement:
  - the unique exact `n = 8` clean class contributes a rigid `24`-step clean family, and that entire family is globally obstructed by MNU and Escape.

LOAD-BEARING ASSESSMENT: High. This turns the `n = 8` exception from a single witness into a fully exhausted finite family and shows that the existing global obstructions already kill the whole family.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exhaustive clean-cycle enumeration for the unique clean class:
  - internal search over `(2,3,3,2,3,3,2,4)` returns `288` clean strict cycles.
- Exact family summary:
  - cycle length distribution: `{24: 288}`;
  - mover-count distribution:
    - `(4,3,3,2,3,3,2,4)`: `144`,
    - `(2,3,3,2,3,3,4,4)`: `144`.
- Global-obstruction classification over all `288` clean cycles:
  - `{'clean': 288, 'mnu_fail': 288, 'escape_fail': 288, 'no_shadow': 288}`.

STRUCTURAL RESULTS:
- Three short subword statistics already show strong rigidity:
  - occurrences of `0,7`: either `0`, `3`, or `4`;
  - occurrences of `2,1`: concentrated at `1` or `3`;
  - occurrences of `4,5,4`: present on `264 / 288` cycles, absent on only `24`.
- So the clean family appears to be a small grammar built from a few repeated local motifs, not a combinatorially wild set.

TOOLS:
- Reused `enumerate_bn_clean_cycles` from `scripts/gec_conflict_scan.py`.
- Evaluated each clean cycle with `check_mnu`, `check_escape`, and `find_shadow`.

REPRESENTATIONS:
- Family view of the unique clean class:
  - `(2,3,3,2,3,3,2,4)` supports a finite set of `288` clean length-`24` cycles, partitioned into two equal mover-count types.

### What Would Unblock This
- A conceptual explanation for why the two mover-count profiles are exactly the only possibilities.
- A proof that any clean cycle in this class must trigger MNU or Escape without exhaustive search.
- A comparison with the `12` negative `n = 8` classes to identify the structural feature that creates this one exceptional clean family.

### Key Parameters
- State counts: `(2,3,3,2,3,3,2,4)`
- Clean strict cycles: `288`
- Cycle length: `24`

### Open Questions
- Do the `288` cycles form a small number of dihedral/rotation orbits?
- Is there a simple symbolic template generating exactly the two observed mover-count profiles?
- Can the MNU/Escape failure in this class be proved directly from the mover word geometry?

## Synthesis after exploration 7

The `n = 8` exception is much better behaved than it first looked. It is not just unique as a state-count class on the exact frontier; internally it is also a rigid finite family. Every clean strict cycle has the same length, falls into one of two mover-count profiles, and is killed by both MNU and Escape. So the replacement theorem target is now sharper: entry conflict is not universal, but the clean residue seems both sparse and globally doomed. The real proof problem is to turn that empirical rigidity into a conceptual lemma rather than to keep searching for more exceptions.

## Exploration 8

### Strategy
Quotient the `288` clean strict cycles in `(2,3,3,2,3,3,2,4)` by dihedral symmetry of the mover word and inspect the canonical representatives, looking for a compact symbolic description of the clean family.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The idea that the `288` clean cycles are mostly redundant rotations of only one or two representatives.
- The idea that the clean family needs a large uncontrolled set of word shapes.

### Surviving Structure
- The clean family has exactly `12` dihedral mover-word orbits.
- Every orbit has size `24`, so the `288` cycles split evenly as `12 x 24`.
- The canonical representatives all exhibit the same coarse skeleton:
  - a forward sweep through `0,1,2,3,4,5,6,7`,
  - one duplicated local zig-zag on the left side (`0,1,2,1,2,3`),
  - one duplicated local zig-zag on the right side (`4,5,4,5` or an equivalent shifted placement),
  - one short binary/quaternary shuttle (`0,7,0,7` or `6,7,6,7`) inserted in one of a small number of slots.
- So the clean family is not merely finite; it is generated by a tiny combinatorial grammar of two local zig-zags plus one endpoint shuttle.

### Reformulations
- Treat the clean `n = 8` exception as a small orbit family of templated mover words rather than as `288` unrelated cycles.

LOAD-BEARING ASSESSMENT: Medium-high. This gives the first compact symbolic description of the unique clean family and suggests a direct route to proving MNU/Escape from mover-word geometry.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Dihedral orbit count for clean cycles in `(2,3,3,2,3,3,2,4)`:
  - `12` orbits total;
  - orbit-size distribution `{24: 12}`.
- Canonical representatives include:
  - `(0,1,2,1,2,3,4,5,4,5,6,7,0,1,2,3,4,5,6,7,0,7,0,7)`,
  - `(0,1,2,1,2,3,4,5,4,5,6,7,6,7,6,7,0,1,2,3,4,5,6,7)`,
  - `(0,1,2,1,2,3,4,5,6,7,0,7,0,7,0,1,2,3,4,5,4,5,6,7)`.

STRUCTURAL RESULTS:
- All orbit representatives are built from the same motifs, with only the location and handedness of the short shuttle changing.
- This sharply supports the view that the `n = 8` clean family is a geometric anomaly tied to a very specific binary/quaternary placement, not a broad mixed-system phenomenon.

TOOLS:
- Reused `enumerate_bn_clean_cycles` and added a local dihedral canonicalization pass over mover words.

REPRESENTATIONS:
- Orbit picture:
  - `288` clean cycles = `12` dihedral templates x `24` symmetries each.

### What Would Unblock This
- A proof that every word generated by this small template forces an MNU or Escape failure.
- A comparison between this template and the exact negative `n = 8` classes to identify which local arc pattern is indispensable.

### Key Parameters
- State counts: `(2,3,3,2,3,3,2,4)`
- Clean cycles: `288`
- Dihedral orbits: `12`
- Orbit sizes: all `24`

### Open Questions
- Is there a minimal normal form with only a few template parameters that generates exactly the `12` orbits?
- Which specific arc of the ring hosts the binary/quaternary shuttle in each orbit, and is that placement the source of the MNU/Escape obstruction?

## Synthesis after exploration 8

The unique clean class is now reduced to something close to a finite template theorem. Up to symmetry, there are only `12` mover-word shapes, and they all look like the same ring geometry with a small shuttle relocated. That is exactly the kind of structure that can plausibly be proved by hand. The search problem is no longer “what weird clean cycles might exist?” but “why does this single templated anomaly still force MNU/Escape?”

## Exploration 9

### Strategy
Inspect where the global obstructions hit inside the `12` clean orbit representatives, then verify on all `288` clean cycles whether MNU and Escape always fail at the same processors.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The idea that MNU/Escape kills the clean class in a diffuse, case-by-case way spread across many processors.
- The idea that a proof would need to analyze all eight processors symmetrically.

### Surviving Structure
- The global obstructions are sharply localized:
  - across all `12` clean dihedral orbit representatives, MNU and Escape failures occur only at processor `1` or processor `5`;
  - across all `288` clean cycles, the same localization persists.
- Geometrically, processors `1` and `5` are exactly the central ternaries of the two length-`2` ternary arcs between binary endpoints.
- So the clean class is globally obstructed not by its short binary-quaternary shuttle arc, but by the two symmetric long arcs it forces elsewhere.

### Reformulations
- The clean class can be reframed as:
  - local determinism survives everywhere,
  - but one of the two long squeezed ternary arcs inevitably violates MNU/Escape at its middle processor.

LOAD-BEARING ASSESSMENT: High. This is the first exact localization of the surviving obstruction in the clean class and suggests a concrete proof target on a single arc.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Orbit-level MNU/Escape classification over the `12` clean word templates:
  - only `8` distinct MNU signatures;
  - only `8` distinct Escape signatures.
- Full-family localization over all `288` clean cycles:
  - MNU violation processor counts: `{1: 192, 5: 192}`;
  - Escape failure processor counts: `{1: 864, 5: 864}`.

STRUCTURAL RESULTS:
- No MNU or Escape witness ever lands on:
  - a binary processor,
  - the quaternary processor `7`,
  - or the outer ternaries `2` and `4`.
- The obstruction lives exclusively at the inner processors of the two length-`2` arcs, exactly where the clean mover words exhibit their duplicated zig-zags.

TOOLS:
- Reused `check_mnu` and `check_escape` from `scripts/binscc_mixed_nonconsec_mnu.py`.
- Aggregated witnesses first by clean orbit representative and then across all `288` clean cycles.

REPRESENTATIONS:
- Localization summary for `(2,3,3,2,3,3,2,4)`:
  - clean cycles exist,
  - entry conflict is absent,
  - but MNU/Escape is forced on processor `1` or `5`.

### What Would Unblock This
- A direct combinatorial proof that any clean mover word on the `(3,3)` arc forces repeated post-move neighborhood at its middle ternary, hence MNU or Escape.
- A class comparison showing that the `12` negative `n = 8` classes fail earlier because the same arc geometry cannot even be completed without entry conflict.

### Key Parameters
- State counts: `(2,3,3,2,3,3,2,4)`
- Clean cycles: `288`
- MNU failure processors: `1`, `5`
- Escape failure processors: `1`, `5`

### Open Questions
- Is there a direct “length-2 ternary arc” lemma implying MNU/Escape once local entry conflict is absent?
- Can the two mover-count profiles be interpreted as which of processors `1` and `5` carries the forced obstruction?

## Synthesis after exploration 9

The clean exception now has a precise internal fault line. Entry conflict disappears globally, but the price is that one of the two long ternary arcs becomes overloaded at its middle processor and immediately triggers MNU/Escape. That is much closer to a theorem than the earlier brute-force picture: the remaining proof may boil down to an arc lemma, not a whole-ring classification.

## Exploration 10

### Strategy
Summarize the exact `n = 9` pairwise mixed frontier by binary-gap geometry, to see whether the unique clean `n = 8` arc pattern can even occur once the theorem range `n >= 9` begins.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The idea that the unique clean `n = 8` geometry automatically persists into the first theorem-range frontier.
- The idea that the `n = 9` clean-class absence is merely accidental rather than geometric.

### Surviving Structure
- The clean `n = 8` class has three binaries with gap multiset `(1,2,2)`.
- On the exact `n = 9` pairwise mixed frontier, the three-binary classes have only gap multisets:
  - `(1,1,4)`,
  - `(1,2,3)`,
  - `(2,2,2)`.
- Therefore the precise gap geometry of the `n = 8` clean exception is impossible already at `n = 9`.
- The remaining `n = 9` classes have four binaries with gap multiset `(1,1,1,2)`, which is even more constrained and still admits no clean strict cycle.

### Reformulations
- The `n = 8` clean anomaly is tied to the existence of a short length-`1` arc together with two length-`2` arcs. That geometry disappears as soon as the theorem range starts.

LOAD-BEARING ASSESSMENT: Medium-high. This does not prove the theorem, but it gives the first structural reason the `n = 8` clean family may be an isolated below-range exception.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exact `n = 9` pairwise mixed frontier geometry summary:
  - `3` three-binary classes with gaps `(1,1,4)`,
  - `6` three-binary classes with gaps `(1,2,3)`,
  - `1` three-binary class with gaps `(2,2,2)`,
  - `25` four-binary classes with gaps `(1,1,1,2)`.

STRUCTURAL RESULTS:
- No exact `n = 9` class realizes the clean `n = 8` gap multiset `(1,2,2)`.
- Hence any theorem for `n >= 9` can plausibly separate the isolated `n = 8` anomaly from the actual residue by gap geometry alone.

TOOLS:
- Reused `enumerate_classes(..., pairwise_nonadjacent_binary)` and summarized each class by cyclic distances between consecutive binary processors.

REPRESENTATIONS:
- Gap-multiset view of the theorem-range frontier.

### What Would Unblock This
- An analogous `n = 10` geometry summary, combined with the running clean-cycle sweep, to see whether `(1,2,2)`-style exceptional structure remains absent or mutates into a new candidate.
- A proof that only the `(1,2,2)` geometry can support the local clean template observed at `n = 8`.

### Key Parameters
- Frontier: exact pairwise mixed `n = 9`
- Class count: `35`
- Three-binary gap patterns: `(1,1,4)`, `(1,2,3)`, `(2,2,2)`

### Open Questions
- Is `(1,2,2)` actually necessary for a fully clean strict cycle, or just sufficient for the unique `n = 8` exception?
- Can the four-binary geometry `(1,1,1,2)` be ruled out abstractly by a strengthened entry-conflict counting argument?

## Synthesis after exploration 10

The theorem-range frontier no longer contains the exact geometry of the `n = 8` counterexample. That does not solve the residue by itself, but it changes the burden of proof in an encouraging way. The clean exception now looks less like the first member of a family and more like a one-off artifact of the only ring size where `(1,2,2)` can coexist with a single quaternary below threshold.

## Exploration 11

### Strategy
Extend the frontier-size and gap-geometry census to `n = 10` (and size-only to `n = 11`) to see whether the theorem-range frontiers continue to exclude the `n = 8` clean geometry.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The idea that the `(1,2,2)` clean geometry quickly reappears at the next frontier size.
- The idea that the exact frontier blows up into too many unrelated geometric types by `n = 10`.

### Surviving Structure
- Exact pairwise mixed frontier sizes:
  - `n = 10`: `135` classes,
  - `n = 11`: `395` classes.
- Exact `n = 10` gap-pattern decomposition:
  - three-binary classes: `(1,1,5)`, `(1,2,4)`, `(1,3,3)`, `(2,2,3)`;
  - four-binary classes: `(1,1,1,3)`, `(1,1,2,2)`;
  - five-binary classes: `(1,1,1,1,1)`.
- So the exceptional `n = 8` pattern `(1,2,2)` is absent at `n = 9` and remains absent at `n = 10`.

### Reformulations
- Any clean-cycle theorem for `n >= 9` can now plausibly target the finite list of theorem-range gap patterns rather than arbitrary mixed rings.

LOAD-BEARING ASSESSMENT: Medium. This is still empirical structure, not proof, but it shows the theorem-range frontier stays geometrically narrow and continues to exclude the unique `n = 8` anomaly.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exact frontier counts:
  - `n = 10`: `135`,
  - `n = 11`: `395`.
- Exact `n = 10` gap-pattern counts:
  - `(3 binaries, gaps (1,1,5))`: `4`,
  - `(3 binaries, gaps (1,2,4))`: `7`,
  - `(3 binaries, gaps (1,3,3))`: `4`,
  - `(3 binaries, gaps (2,2,3))`: `4`,
  - `(4 binaries, gaps (1,1,1,3))`: `37`,
  - `(4 binaries, gaps (1,1,2,2))`: `53`,
  - `(5 binaries, gaps (1,1,1,1,1))`: `26`.

STRUCTURAL RESULTS:
- The theorem-range frontiers appear to organize by a small set of binary-gap geometries.
- None of those geometries reproduces the `n = 8` clean pattern.

TOOLS:
- Reused `enumerate_classes(..., pairwise_nonadjacent_binary)` and summarized by binary count and gap multiset.

REPRESENTATIONS:
- Gap-pattern census for theorem-range frontiers.

### What Would Unblock This
- Completion of the running exact `n = 10` clean-cycle sweep, to pair the geometry census with exact clean/non-clean classification.
- If `n = 10` is clean-free, the next high-value target is a proof that none of the theorem-range gap patterns can realize the `n = 8` local template.

### Key Parameters
- `n = 10` frontier size: `135`
- `n = 11` frontier size: `395`
- `n = 10` gap patterns: `7` total

### Open Questions
- Does every theorem-range gap pattern admit a direct local contradiction, or do some require MNU/Escape after passing entry-conflict screening?
- Is there a concise necessary condition for clean strict cycles expressible purely in terms of the binary-gap multiset?

## Synthesis after exploration 11

The search space is not exploding uncontrollably as `n` grows. Even by `n = 10`, the exact frontier still falls into a short, explicit list of gap-pattern types, and none matches the unique `n = 8` clean geometry. That makes a structural theorem over frontier geometries look realistic rather than fanciful.

## Exploration 12

### Strategy
Upgrade the clean-cycle scanner to allow explicit target processor sets, then use that local search mode on the nearest `n = 9` extension `(2,3,3,2,3,3,2,3,4)` to see whether the obstruction still has to pass through the long-arc middle processors.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The tentative idea that the `n = 8` MNU/Escape localization at processors `1` and `5` directly extends to the nearest `n = 9` negative class.
- Any proof strategy that only tracks nonbinary processors in theorem-range classes.

### Surviving Structure
- In `(2,3,3,2,3,3,2,3,4)`, there exists a strict cycle clean on processors `1` and `5`.
- There also exists a strict cycle clean on the short-arc processors `7` and `8`.
- More strongly, there exists a strict cycle clean on **all nonbinary processors** `1,2,4,5,7,8`.
- For one such cycle, the unique entry conflict is a mover/nonmover conflict at binary processor `6` with context `(2,1,1)`.

### Reformulations
- The nearest theorem-range negative class does not force conflict on the “interesting” ternaries or on the quaternary. It can push the entire entry-conflict residue onto a single binary.

LOAD-BEARING ASSESSMENT: High. This is a real shift in the residue. It says theorem-range entry conflict can survive in an extremely concentrated binary form even when all nonbinary processors are clean.

### Concrete Artifacts
CODE:
- Extended `scripts/gec_conflict_scan.py` with explicit `target_procs` support for `find_bn_clean_cycle`, `enumerate_bn_clean_cycles`, and CLI flag `--target-procs`.
- Verified with `python3 -m py_compile scripts/gec_conflict_scan.py`.

COMPUTED EXAMPLES:
- Exact local-clean searches on `(2,3,3,2,3,3,2,3,4)`:
  - `--target-procs 1,5` finds a clean strict cycle;
  - `--target-procs 7,8` finds a clean strict cycle;
  - `--target-procs 1,2,4,5,7,8` finds a clean strict cycle.
- Example all-nonbinary-clean mover word:
  - `(0,1,2,1,2,3,4,5,4,5,6,7,6,7,8,7,6,7,8,7,8,0,1,2,3,4,5,6,7,8)`.
- Conflict analysis of that word:
  - exactly one conflict,
  - `ConflictRecord(proc=6, ctx=(2,1,1), kind='mover_nonmover', outputs=(0,), binary_neighbors=0, is_binary=True)`.

STRUCTURAL RESULTS:
- Entry conflict in theorem-range classes can be pushed entirely onto a binary processor.
- So any universal conflict theorem for `n >= 9` should not assume the contradiction appears at a ternary or at a processor adjacent to binaries.

TOOLS:
- Strengthened `scripts/gec_conflict_scan.py` with explicit local targeting.
- Reused `analyze_cycle` to classify the exact conflict locus of target-clean witnesses.

REPRESENTATIONS:
- Local-target clean search:
  - ask for strict cycles that are clean on a selected processor subset, not only on binary-neighbor classes.

### What Would Unblock This
- A frontier-wide census of how often theorem-range classes admit “all nonbinary clean” or “single-conflict” strict cycles.
- A proof that even these highly concentrated binary conflicts are enough to block determinism/self-stabilization globally.

### Key Parameters
- State counts: `(2,3,3,2,3,3,2,3,4)`
- All-nonbinary-clean target set: `(1,2,4,5,7,8)`
- Witness conflict location: binary `6`

### Open Questions
- Is the nearest `n = 9` class special, or do many theorem-range classes admit a unique binary conflict witness?
- Can the binary-only residue be characterized directly from the gap geometry?

## Synthesis after exploration 12

The theorem-range obstruction can be much more concentrated than the `n = 8` clean exception suggested. In the closest `n = 9` negative class, all nonbinary processors can be made clean and the entire determinism failure collapses to a single binary. That makes universal entry conflict look more plausible for `n >= 9`, but it also says the proof must be willing to find the contradiction at a binary, not just at the squeezed ternary structure.

## Exploration 13

### Strategy
Use explicit target sets to test a stronger binary-focused replacement conjecture on the exact `n = 9` frontier: is there any class for which every strict cycle has an entry conflict at some binary processor?

### Outcome
FAILED

### Concrete Counterexample
In fact the conjecture fails in the strongest possible way on the exact `n = 9` frontier:
- every one of the `35` pairwise mixed classes admits a strict cycle that is clean on **all** binary processors.

### What This Rules Out
- Any theorem of the form “for `n >= 9`, some binary must have an entry conflict.”
- Any proof strategy that tries to close the residue by forcing the contradiction onto the binary set alone.

### Surviving Structure
- Conflict location is highly movable on the theorem-range frontier:
  - in some classes, all binaries can be clean;
  - in at least one nearby class, all nonbinaries can be clean.
- Therefore the inevitable conflict in theorem-range classes is a genuinely global phenomenon. It cannot be pinned in advance to either the binary or nonbinary side of the ring.

### Reformulations
- The right replacement theorem is not “binary conflict is universal” and not “nonbinary conflict is universal.”
- What remains plausible is only the global statement: fully clean strict cycles do not occur on the theorem-range frontier, even though either side of the ring can be made individually clean.

LOAD-BEARING ASSESSMENT: High. This eliminates a natural proof route and clarifies the residue: conflict is universal on the exact `n = 9` frontier, but its location is not structurally fixed.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exact frontier-wide binary-clean search on all `35` pairwise mixed `n = 9` classes:
  - for each class `ms`, target set = all binary indices `{i : m_i = 2}`;
  - result: `binary_clean_count = 35`.
- Example binary-clean witness for `(2,3,3,2,3,3,2,3,4)`:
  - `(0,8,7,6,5,4,3,2,1,0,8,7,6,5,4,3,4,5,4,3,2,1,0,8,7,8,0,1)`.

STRUCTURAL RESULTS:
- The theorem-range frontier allows conflicts to be pushed entirely off the binaries.
- Combined with exploration 12, it also allows conflicts to be pushed entirely off the nonbinaries in at least one class.
- So the obstruction is set-theoretically nonlocal: neither side alone is guaranteed to witness it.

TOOLS:
- Reused `find_bn_clean_cycle(..., target_procs=binaries)` on every exact `n = 9` pairwise mixed class.

REPRESENTATIONS:
- Binary-clean frontier census for `n = 9`.

### What Would Unblock This
- The running all-nonbinary-clean frontier census at `n = 9`, which will show whether the nearest-class phenomenon is isolated or widespread.
- A theorem that directly forbids simultaneous cleanliness of the two complementary processor sets.

### Key Parameters
- Frontier: exact pairwise mixed `n = 9`
- Classes tested: `35`
- Binary-clean classes found: `35`

### Open Questions
- How many exact `n = 9` classes also admit an all-nonbinary-clean cycle?
- Is there a clean complementarity principle here: classes can clean one side or the other, but never both simultaneously?

## Synthesis after exploration 13

The residue is now sharply paradoxical in a useful way. On the exact `n = 9` frontier, full cleanliness never occurs, but binary cleanliness always does, and nonbinary cleanliness occurs at least in some classes. So the obstruction is real yet highly relocatable. That means the missing theorem is unlikely to be a local “bad processor type” lemma. It is more likely a complementary-coverage statement: one can hide conflict from one side of the ring, but not from both at once.

## Exploration 14

### Strategy
Complete the complementary census on the exact `n = 9` frontier by searching for strict cycles clean on **all nonbinary processors**, and compare that with the binary-clean census from exploration 13.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The idea that all-nonbinary-clean witnesses are common once binaries are no longer the bottleneck.
- The idea that binary-clean and nonbinary-clean behavior are symmetric on the theorem-range frontier.

### Surviving Structure
- Exact `n = 9` frontier-wide all-nonbinary-clean count:
  - `1 / 35`.
- The unique positive class is:
  - `(2,3,3,2,3,3,2,3,4)`,
  - the unique three-binary class with gap multiset `(2,2,2)`.
- Therefore the exact `n = 9` frontier shows a strong asymmetry:
  - every class is binary-clean (`35 / 35`);
  - only one class is all-nonbinary-clean (`1 / 35`);
  - no class is fully clean (`0 / 35` from exploration 6).

### Reformulations
- Binary conflicts are never forced by themselves on the exact `n = 9` frontier.
- Nonbinary conflicts are almost always forced, except in the unique balanced three-binary `(2,2,2)` geometry.

LOAD-BEARING ASSESSMENT: High. This is the strongest theorem-range structural split found so far. It isolates a single geometric class as the only one able to hide all nonbinary conflicts, while every other exact `n = 9` class still needs a nonbinary witness somewhere.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exact full-frontier all-nonbinary-clean census:
  - `all_nonbinary_clean_count 1`.
- Unique all-nonbinary-clean witness:
  - class `(2,3,3,2,3,3,2,3,4)`;
  - target set `(1,2,4,5,7,8)`;
  - mover word
    `(0,1,2,1,2,3,4,5,4,5,6,7,6,7,8,7,6,7,8,7,8,0,1,2,3,4,5,6,7,8)`.
- Three-binary exact subcensus:
  - `three_binary_all_nonbinary_clean_count 1`,
  - same unique positive class.

STRUCTURAL RESULTS:
- The unique all-nonbinary-clean `n = 9` class is exactly the nearest extension of the `n = 8` clean anomaly, obtained by replacing the short `(4)` arc with `(3,4)` so that all three binary gaps become length `2`.
- No four-binary `n = 9` class admits an all-nonbinary-clean cycle.

TOOLS:
- Reused `find_bn_clean_cycle(..., target_procs=nonbinaries)` on the full exact `n = 9` frontier.

REPRESENTATIONS:
- Complementary cleanliness table on the exact `n = 9` frontier:
  - binary-clean count `35`,
  - nonbinary-clean count `1`,
  - fully clean count `0`.

### What Would Unblock This
- A proof that all theorem-range classes except the balanced `(2,2,2)` geometry force a nonbinary conflict.
- A separate argument showing that even in the balanced `(2,2,2)` geometry, some binary conflict remains unavoidable, preventing full cleanliness.

### Key Parameters
- Frontier: exact pairwise mixed `n = 9`
- Binary-clean classes: `35 / 35`
- All-nonbinary-clean classes: `1 / 35`
- Fully clean classes: `0 / 35`

### Open Questions
- Does the balanced-gap pattern `(2,2,2)` remain the unique all-nonbinary-clean positive on the `n = 10` frontier among three-binary classes?
- Can the asymmetry `35/35` versus `1/35` be converted into a structural proof by gap geometry?

## Synthesis after exploration 14

The `n = 9` frontier now has a striking complementary structure. Binary cleanliness is universal, nonbinary cleanliness is almost nonexistent, and full cleanliness is absent. The unique nonbinary-clean positive is exactly the balanced three-binary `(2,2,2)` class, which also sits closest to the `n = 8` clean anomaly. That points toward a plausible proof split for the theorem range: first show nonbinary conflict is forced except in the balanced-gap geometry, then handle that single geometry separately by a binary obstruction.

## Exploration 15

### Strategy
Exhaust the full family of all-nonbinary-clean strict cycles in the unique `n = 9` balanced-gap class `(2,3,3,2,3,3,2,3,4)`, and classify where the remaining conflicts land and whether MNU/Escape survives on any member.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The idea that the unique all-nonbinary-clean `n = 9` class hides many qualitatively different residues.
- The idea that, even after isolating this class, one still needs a diffuse whole-ring analysis to kill it.

### Surviving Structure
- The all-nonbinary-clean residue in `(2,3,3,2,3,3,2,3,4)` is finite and rigid:
  - exactly `1080` strict cycles;
  - every one has length `30`.
- In every such cycle, **all** entry conflicts occur at the same processor:
  - processor `6`, which is binary.
- Conflict multiplicity varies, but support does not:
  - `480` cycles have `1` conflict record,
  - `480` cycles have `2` conflict records,
  - `120` cycles have `3` conflict records,
  - yet the conflict processor set is always exactly `{6}`.
- Every one of the `1080` cycles fails MNU.

### Reformulations
- The unique theorem-range class that can hide all nonbinary conflicts still collapses to a one-binary obstruction family.
- So the balanced-gap separate case is not open-ended: it is a pure binary-overload residue.

LOAD-BEARING ASSESSMENT: High. This gives a concrete separate-case target for a proof: the only class that avoids nonbinary conflict on the exact `n = 9` frontier reduces to a rigid family whose entire obstruction sits at one binary and triggers MNU universally.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exhaustive enumeration in `(2,3,3,2,3,3,2,3,4)` with target set `(1,2,4,5,7,8)`:
  - `count 1080`,
  - `checked 1080`,
  - `nodes 2194437`.
- Exact family summary:
  - length distribution `{30: 1080}`,
  - conflict-count distribution `{1: 480, 2: 480, 3: 120}`,
  - conflict-processor-set distribution `{(6,): 1080}`.
- Global obstruction summary:
  - `mnu_fail 1080`,
  - `escape_fail 0` under the direct test used here.

STRUCTURAL RESULTS:
- Once nonbinary conflicts are forbidden in the balanced-gap class, the cycle family has no freedom about where the remaining contradiction goes: it always lands on the same binary.
- This is the theorem-range analogue of the `n = 8` clean anomaly becoming rigid after quotienting, but it is even sharper because the conflict locus is literally fixed.

TOOLS:
- Reused `enumerate_bn_clean_cycles(..., target_procs=nonbinaries)` and `analyze_cycle`.
- Evaluated MNU on every enumerated cycle.

REPRESENTATIONS:
- Separate-case family for the theorem range:
  - balanced-gap class `(2,3,3,2,3,3,2,3,4)`,
  - all-nonbinary-clean cycles,
  - all conflict support concentrated at binary `6`.

### What Would Unblock This
- A direct proof that any all-nonbinary-clean cycle in the balanced-gap geometry forces repeated post-move binary context at processor `6`, hence MNU.
- A theorem that all other exact `n = 9` classes force a nonbinary conflict somewhere, leaving only this balanced-gap binary-overload family as residue.

### Key Parameters
- State counts: `(2,3,3,2,3,3,2,3,4)`
- All-nonbinary-clean cycles: `1080`
- Cycle length: `30`
- Conflict support: always `{6}`

### Open Questions
- Does the balanced-gap three-binary geometry at `n = 10` have an analogous all-nonbinary-clean family, and if so is the conflict support again forced onto a single binary?
- Can the universal MNU failure at processor `6` be proved from the local mover-word template?

## Synthesis after exploration 15

The theorem-range residue is finally starting to break into proof-sized pieces. On the exact `n = 9` frontier, every class except one needs a nonbinary conflict, and the sole exception is completely rigid: if you suppress all nonbinary conflicts in the balanced-gap class, the remaining family is finite, length `30`, and every contradiction sits on the same binary and fails MNU. That is a much cleaner endpoint than the original universal-entry-conflict conjecture.
