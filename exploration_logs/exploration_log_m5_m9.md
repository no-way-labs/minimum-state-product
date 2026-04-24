# Exploration Log

## Strategy Register

### Eliminated approach classes
- All-good product-72 systems for `n = 5` with state-count pattern `(2,2,2,3,3)` or `(2,2,3,2,3)`, under the necessary condition that every processor is enabled on at least one local context, are ruled out (exploration 1). Structural reason: the exact-one enabled-processor CSP is already unsatisfiable before target states are assigned.
- All product-72 systems for `n = 5` are ruled out (exploration 2). Structural reason: for each of the two product-72 pattern classes, every locally consistent good cycle forces an off-cycle recurrent component in the singleton-move graph that cannot be a fair good cycle (either branching or missing some processor), so every completion contains a bad cycle.
- All product-144 systems for `n = 6` with pattern class `(2,2,2,3,2,3)` or `(2,2,3,2,2,3)` are ruled out by the fatal recurrent-component screen (exploration 4).
- All product-192 systems for `n = 6` with pattern class `(2,2,2,3,2,4)` or `(2,2,3,2,2,4)` are ruled out by the fatal recurrent-component screen after symmetry-reduced exhaustive enumeration (exploration 6).
- The alternating product-216 class `(2,3,2,3,2,3)` for `n = 6` is ruled out by exhaustive symmetry-reduced cycle screening (exploration 7).
- The clustered product-216 class `(2,2,3,2,3,3)` for `n = 6` is ruled out by exhaustive symmetry-reduced cycle screening (exploration 8).
- The clustered product-216 class `(2,2,2,3,3,3)` for `n = 6` is ruled out by exhaustive symmetry-reduced cycle screening (exploration 9).
- Both product-240 classes `(2,2,2,3,2,5)` and `(2,2,3,2,2,5)` for `n = 6` are ruled out by exhaustive symmetry-reduced cycle screening (exploration 13).
- Both product-256 classes `(2,2,2,4,2,4)` and `(2,2,4,2,2,4)` for `n = 6` are ruled out by exhaustive symmetry-reduced cycle screening (exploration 15).
- The product-288 class `(2,3,2,3,2,4)` for `n = 6` is ruled out by exhaustive symmetry-reduced cycle screening (exploration 16).
- The unique product-288 class `(2,2,2,3,2,2,3)` for `n = 7` is ruled out by exhaustive symmetry-reduced cycle screening (exploration 30).
- The unique product-384 class `(2,2,2,3,2,2,4)` for `n = 7` is ruled out by exhaustive symmetry-reduced cycle screening (exploration 31).
- All product-432 classes `(2,2,2,3,2,3,3)`, `(2,2,3,2,2,3,3)`, and `(2,2,3,2,3,2,3)` for `n = 7` are ruled out by exhaustive symmetry-reduced cycle screening (exploration 32).
- The unique product-480 class `(2,2,2,3,2,2,5)` for `n = 7` is ruled out by exhaustive symmetry-reduced cycle screening (exploration 34).
- The unique product-512 class `(2,2,2,4,2,2,4)` for `n = 7` is ruled out by exhaustive symmetry-reduced cycle screening (exploration 35).
- The product-576 class `(2,2,3,2,4,2,3)` for `n = 7` is ruled out by exhaustive symmetry-reduced cycle screening (exploration 38).
- The upper-bound family with state counts `(2,2,2,4,3,...,3)` and the standard Dijkstra-solution-3 middle-processor ternary rule as a uniform bulk table is ruled out for `n = 7,8,9,10` (exploration 73). Structural reason: it already fails liveness on the explicit configurations `(1,1,1,2,1,...,1,0)`.
- The cleanest one-bulk fixed-boundary extensions of the `n = 6` block witness are ruled out at `n = 7` (exploration 75). Structural reason: the target family admits no locally consistent cycle for either of the known `n = 7` witness mover sequences, no locally consistent cycle for the exact `n = 6` block-witness mover sequence, no one-bulk completion for a 125-pattern family of local replacements around the old terminal ternary moves, and no interleaving of extra bulk-processor moves into the `n = 6` block-witness schedule for lengths `36..60`.

### Obstructions
- `M_5 >= 72` (exploration 1). Reason: fairness forces every processor to have at least 2 states, and the seminar obstruction rules out any ring containing four consecutive 2-state processors. The only 5-tuples with product below 72 are `(2,2,2,2,2)`, `(2,2,2,2,3)`, and `(2,2,2,2,4)`, each of which has four consecutive 2-state processors.
- In the all-good family at product 72, both cyclic pattern classes `(2,2,2,3,3)` and `(2,2,3,2,3)` fail at the enabled/disabled stage once each processor is required to be enabled somewhere (exploration 1). This is not yet a full-model impossibility result.
- `M_5 >= 80` (exploration 2). Reason: product 72 is impossible for both surviving pattern classes `(2,2,2,3,3)` and `(2,2,3,2,3)`, after exhaustive screening of all locally consistent good cycles up to state relabeling.
- `M_6 >= 192` (exploration 4), conditional on the same cycle-screen soundness used in exploration 2. Reason: the first `n = 6` product frontier avoiding four consecutive binary processors is 144, and both pattern classes at product 144 are eliminated by exhaustive good-cycle screening.
- `M_6 >= 216` (exploration 6), under the same cycle-screen soundness assumption. Reason: the next product frontier, 192, is also eliminated in both symmetry classes.
- `M_6 >= 240` (exploration 9), under the same cycle-screen soundness assumption. Reason: all three product-216 symmetry classes are now eliminated.
- Product 240 is impossible for `n = 6` (exploration 13), under the same cycle-screen soundness assumption. The next exact lower-bound value depends on the smallest attainable product above 240 and should be computed explicitly before being recorded here.
- `M_6 >= 256` (explorations 13 and 14), under the same cycle-screen soundness assumption. Reason: exploration 13 eliminates both product-240 classes, and exploration 14 shows that the next attainable product frontier above 240 is 256.
- `M_6 >= 288` (explorations 14 and 15), under the same cycle-screen soundness assumption. Reason: exploration 14 identifies 256 as the next product frontier above 240, and exploration 15 eliminates both product-256 classes.
- `M_7 >= 384` (explorations 29 and 30), under the same cycle-screen soundness assumption. Reason: exploration 29 identifies 288 as the first admissible `n = 7` product frontier, and exploration 30 eliminates its unique symmetry class.
- `M_7 >= 432` (explorations 29, 30, and 31), under the same cycle-screen soundness assumption. Reason: exploration 29 identifies 384 as the next admissible frontier after 288, and exploration 31 eliminates its unique symmetry class.
- `M_7 >= 480` (explorations 29, 30, 31, and 32), under the same cycle-screen soundness assumption. Reason: exploration 29 identifies 432 as the next admissible frontier after 384, and exploration 32 eliminates all three product-432 symmetry classes.
- `M_7 >= 512` (explorations 29, 30, 31, 32, and 34), under the same cycle-screen soundness assumption. Reason: exploration 29 identifies 480 as the next admissible frontier after 432, and exploration 34 eliminates its unique symmetry class.
- `M_7 >= 576` (explorations 29, 30, 31, 32, 34, and 35), under the same cycle-screen soundness assumption. Reason: exploration 29 identifies 512 as the next admissible frontier after 480, and exploration 35 eliminates its unique symmetry class.
- The centered local-context quotient `(m_{i-1..i+1}, p_{i-1..i+1})` is not fine enough to determine the forced output uniformly, even on the exact uniform-sweep Escape Lemma dataset (exploration 69). Structural reason: 9 of the 45 observed quotient classes merge raw radius-2 types with different forced outputs.
- Even the full raw radius-2 type `(m_{i-2..i+2}, p_{i-2..i+2})` does not determine the forced output once multiple uniform-sweep shadow-cycle families are aggregated (exploration 70). Structural reason: 201 of the 940 observed raw types at `n <= 8` appear with multiple forced outputs across different cycle families.
- The proved witnesses for `n = 5,6,7,8` contain no processors with local state-count triple `(3,3,3)` (exploration 73). Structural reason: direct extraction of a universal bulk ternary table `T*` from the existing witnesses is impossible; any such table must be synthesized rather than copied.
- The conjectured upper-bound family orientation `(2,2,2,4,3,3,...,3)` is not a rotation/reflection of the proved `n = 7` or `n = 8` witnesses (exploration 73). Structural reason: the current witness data does not already lie on the proposed family branch from `n = 7` onward.
- Even after canonical relabeling on ternary coordinates, same-triple boundary roles such as `(4,3,3)` and `(3,3,2)` do not stabilize across the proved `n = 5..8` witnesses (exploration 73). Structural reason: the conjectured “copy all boundaries from `n = 6`” family is not directly forced by the known witness data.

### Building blocks
- `p2_ring.py` (exploration 1): verifier for central-daemon token-ring candidates. It enumerates configurations, constructs the move graph, checks liveness, detects recurrent SCCs, and verifies fairness on every recurrent cycle.
- `scripts/p2_all_good_search.py` (exploration 1): backtracking solver for the restricted all-good family. It solves the exact-one enabled-processor CSP on local contexts, with an added per-processor coverage constraint.
- `scripts/p2_good_cycle_search.py` (exploration 2): DFS generator for locally consistent good cycles with partial rule-map propagation.
- `scripts/p2_cycle_screen.py` (exploration 2): exhaustive screener that takes a candidate good cycle and checks whether the cycle-forced singleton moves already create an off-cycle recurrent component that cannot become a fair good cycle.
- `scripts/p2_completion_search.py` (exploration 2): partial completion search that grows a selected good cycle into a full system using liveness propagation plus fatal recurrent-component pruning.
- `scripts/p2_survivor_completion.py` (exploration 3): pipeline that screens good cycles for nonfatal recurrent structure, then attempts full completion only on surviving cycles.
- Symmetry-reduced good-cycle enumeration (exploration 6): canonicalizes first appearance of local state labels, cutting duplicate branches from state-relabel symmetries.
- Exhaustion-count calibration (exploration 13): class-by-class screened-cycle totals are now predictive enough to decide whether a frontier should be attacked by a longer rerun or by a new optimization pass.
- `scripts/p2_smt_completion.py` (exploration 25): SMT-based completion engine for a fixed good cycle. It encodes the off-cycle subgraph as an acyclic rank function and validates candidate models with `verify_system`.
- `scripts/p2_prefix_batch.py` (exploration 57, extended in exploration 63): parallel mover-prefix screener that splits a hard class into independent DFS subtrees and aggregates their screened counts. It now works cleanly on `n = 9` after raising the recursion limit in the SCC screen path.
- `scripts/n9_sweep.py` (exploration 60): append-only `n = 9` sweep driver with explicit `--multiset`, `--start-orientation`, and `--end-orientation` controls, so long orientation batches can be resumed and logged without replaying earlier classes.
- `scripts/extract_escape_local_types.py` (explorations 68 and 69): local-type extractor built on top of `scripts/verify_lower_bound.py`. It replays the exact Escape Lemma datasets, records radius-2 forced-privilege patterns, and now also summarizes quotient families such as the centered local context `(m_{i-1..i+1}, p_{i-1..i+1})`.
- `scripts/escape_context_catalog.py` (exploration 71): post-processor for the local-type summary JSON that builds a proof-facing catalog of the 45 centered local-context escape classes, grouped by centered `m`-triple and annotated with raw completions and output ambiguity.
- `scripts/upper_bound_family.py` (exploration 73): extractor and sanity-check tool for the upper-bound family program. It reports witness local triples, canonicalized same-triple comparisons, target-orientation matches, and can assemble the one-bulk family with `n = 6` boundaries for quick verifier tests.
- `scripts/family_one_bulk_search.py` (exploration 74): bounded `n = 9` synthesizer for the one-bulk family. It fixes the `n = 6` boundary tables, ties all interior ternaries to one shared 27-entry table, searches for a bounded locally consistent cycle, and verifies each candidate bulk table as a full system.
- `scripts/family_one_bulk_search.py` (explorations 74 and 75): bounded family synthesizer for the one-bulk hypothesis. It now also supports fixed mover-sequence checks and an `--interleave-n6-block` mode that constrains the target mover sequence to the `n = 6` block-witness schedule with inserted moves by the new bulk processor.

### Known reformulations
- Configuration-graph view: a candidate system is a finite directed graph on global configurations, with one outgoing edge per privileged processor. Validity can be checked by separating branching states from deterministic tails/cycles and then testing fairness on the surviving cycles. LOAD-BEARING: likely yes, because it turns the problem into graph analysis plus local-consistency constraints.
- Two-phase all-good representation: first assign only the enabled/disabled bit for each local context so that every global configuration has exactly one enabled processor; only afterwards assign target states for the moving contexts. LOAD-BEARING: moderate. The first phase is solver-free and already strong enough to eliminate small families.
- Good-cycle-first representation: enumerate all locally consistent good cycles up to normalization, then study the recurrent structure already forced on off-cycle states before attempting full completion. LOAD-BEARING: yes. At product 72 this was strong enough to prove impossibility without full rule-table enumeration.
- Survivor-cycle pipeline: first eliminate doomed good cycles using the fatal recurrent-component screen, then run completion search only on surviving cycles. LOAD-BEARING: yes. This made product-96 construction feasible in milliseconds.
- Canonical state-introduction ordering: when a processor first uses a new local state along a cycle, introduce states in label order `1,2,3,...`. LOAD-BEARING: yes. This was enough to exhaust the `n = 6`, product-192 cycle space that previously timed out.
- Frontier calibration by nearby exhaustion counts: compare a partially screened class to recently closed classes of similar geometry before deciding whether more engineering is justified. LOAD-BEARING: moderate. This is a search-policy reformulation rather than a mathematical one, but it correctly predicted that product 240 was still in brute-force range.
- Acyclic bad-subgraph as rank function: for a fixed good cycle, completion can be encoded by assigning every off-cycle configuration a rank that strictly decreases along every enabled bad move. LOAD-BEARING: yes. This turned product-288 witness search from deep backtracking timeouts into fast SMT decisions.
- Recursive mover-prefix sharding: treat a hard class as a tree of constrained mover-prefix subproblems, and recurse only on the prefixes that survive their local time budget. LOAD-BEARING: yes. It collapsed the last open `n = 7`, product-576 residue and, by exploration 63, also breaks monolithic `screened=0` dead zones at `n = 9`.
- Orientation-indexed sweep slices: for large `n = 9` families, treat a sweep as an append-only list of explicit orientation checkpoints rather than one monolithic run. LOAD-BEARING: moderate. This is operational rather than mathematical, but it cleanly isolates pre-screen bottlenecks and avoids replaying already measured orientations.
- Radius-2 local-type catalog for the Escape Lemma: classify every forced-privileged non-good configuration by the `(m_{i-2..i+2}, p_{i-2..i+2})` window centered at a forced processor, then track type growth across `n`. LOAD-BEARING: promising. It makes the “finite local classification” question measurable instead of speculative.
- Centered local-context quotient for the Escape Lemma: collapse raw radius-2 types to `(m_{i-1..i+1}, p_{i-1..i+1})` and track only centered-escape behavior and coarse transition stability. LOAD-BEARING: high. On the exact uniform-sweep dataset it stabilizes at 45 classes by `n = 6`, with no new classes at `n = 7`, `n = 8`, or the canonical `n = 9` probe.
- Escape-only local typing: local types should be asked to certify “the centered forced move escapes the good set,” not to reconstruct the forced target state uniformly across different shadow-cycle families. LOAD-BEARING: high. Exploration 70 shows that even full raw radius-2 windows do not determine the target state globally, so any universal local proof has to phrase its conclusion at the level of escape behavior instead.
- Centered `m`-triple grouping of escape classes: the 45 stabilized centered local-context classes split into 8 centered `m`-triple groups with counts `2,3,6,5,6,9,8,6`, and all 9 output-ambiguous classes lie in the ternary-centered groups `(2,3,2)`, `(2,3,3)`, `(3,3,2)`, `(3,3,3)` (exploration 71). LOAD-BEARING: promising. This is the first compact grouping that isolates all residual transition ambiguity while leaving the escape classification finite.
- Centered `0/nonzero` quotient: collapse centered local-context classes by keeping the centered `m`-triple and replacing each centered state by its indicator `0` versus nonzero (exploration 72). LOAD-BEARING: high. On the exact uniform-sweep dataset this reduces the catalog from 45 classes to 24, still stabilizes by `n = 6`, and shrinks the ambiguous residue from 9 classes to 6.
- Upper-bound family extraction report: treat the proved witnesses as data for three separate questions — local-triple incidence, canonical boundary-table stability, and target-orientation membership — before attempting any synthesis of `T*` (exploration 73). LOAD-BEARING: high. It cleanly separates what the existing witnesses actually determine from what must still be synthesized.
- Interleaved-extension seed model: build the target family mover sequence by taking the `n = 6` block-witness mover sequence, relabeling the old last ternary to the new boundary processor, and inserting extra moves by the new bulk processor (exploration 75). LOAD-BEARING: moderate to high. It is strong enough to rule out the cleanest one-bulk extension mechanism at `n = 7`, so the next family hypothesis must loosen either the boundary rules or the bulk pattern.
- Witness-guided local-block transfer across nearby product frontiers: when one `n = 9` multiset family fails, first test the orientations that preserve the known tail-family binary placements and local neighborhood in the next higher-product multiset, then recurse only on the hottest of those blocks (exploration 80). LOAD-BEARING: moderate. It separated the cold product-9720 witness-adjacent block from the much hotter product-10368 tail-preserving orientation without sweeping `56 + 140` orientations blindly.

## Session Start (2026-03-07)

Resuming from exploration 0.

No prior `exploration_log_m5_m9.md` existed in the repository, so there is no earlier exploration state to reuse.

Next attempt: implement a verifier for candidate rings under the central-daemon model, then use it to probe the smallest unresolved mixed-state cases near `n = 5`, guided by the seminar obstructions on 2-state processors and the explicit suggestion that exhaustive checking should be feasible for small products.

## Exploration 1

### Strategy
Build a reusable verifier for the central-daemon model, then use seminar obstructions plus small exhaustive probes to sharpen the `n = 5` frontier and test the minimal surviving product-72 patterns inside the restricted all-good family.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
Any `n = 5` approach with total product below 72 is impossible. Within the all-good family, product-72 approaches of cyclic type `(2,2,2,3,3)` and `(2,2,3,2,3)` are also impossible once every processor is required to be enabled on some local context, because the exact-one enabled-pattern constraints are inconsistent.

### Surviving Structure
- The first unresolved product for `n = 5` is 72.
- Up to rotation and reflection, the only state-count patterns at product 72 are `(2,2,2,3,3)` and `(2,2,3,2,3)`.
- The verifier confirms known benchmark instances in the central-daemon model: Dijkstra solution 1 is valid for `(n,m) = (3,3)`, Dijkstra solution 3 is valid for `n = 4`, and Dijkstra solution 1 fails for five binary processors.

### Reformulations
- The configuration-graph verifier is workable in the central-daemon model and matches the March 12 seminar idea of detecting bad cycles via graph structure instead of transitive closure.
- For all-good families, target states can be deferred: the enabled/disabled pattern alone already carries strong information. This separates a mixed symbolic search into a boolean phase and a smaller target-assignment phase.

LOAD-BEARING ASSESSMENT: Yes for the configuration-graph view; probably yes for the two-phase all-good view. The latter immediately cut product-72 search down to a boolean feasibility test and showed that the natural all-good family fails before target values matter.

### Concrete Artifacts
COMPUTED EXAMPLES:
- All `n = 5` state-count multisets with product below 72 and all `m_i >= 2`: `(2,2,2,2,2)`, `(2,2,2,2,3)`, `(2,2,2,2,4)`.
- Product-72 pattern classes up to rotation and reflection: `(2,2,2,3,3)` and `(2,2,3,2,3)`.
- `python3 scripts/p2_all_good_search.py 2,2,2,3,3` reports no all-good enabled-pattern solution.
- `python3 scripts/p2_all_good_search.py 2,2,3,2,3` reports no all-good enabled-pattern solution.

STRUCTURAL RESULTS:
- `M_5 >= 72`.
- In the all-good family with per-processor coverage, the enabled-pattern CSP is unsatisfiable for both minimal product-72 pattern classes.

TOOLS:
- `p2_ring.py` with `verify_system`, `build_dijkstra_solution_1`, and `build_dijkstra_solution_3`.
- `scripts/p2_all_good_search.py` for boolean enabled-pattern search in the all-good family.

REPRESENTATIONS:
- SCC-based recurrent-cycle representation of validity.
- Local-context boolean representation for all-good enabled patterns.

### What Would Unblock This
Either of the following would move the search materially:
- Extend the all-good search to assign target states and enforce fairness on actual recurrent cycles, not just enabled-pattern feasibility.
- Generalize the search beyond all-good systems by allowing bad configurations plus a ranking or DAG certificate that forbids bad cycles.

The smallest useful targets are exactly the two product-72 patterns `(2,2,2,3,3)` and `(2,2,3,2,3)`.

### Key Parameters
- Verified benchmark systems: `(n,m) = (3,3)` for Dijkstra solution 1, `n = 4` for Dijkstra solution 3, `(n,m) = (5,2)` for Dijkstra solution 1 as a negative benchmark.
- Product frontier for `n = 5`: below 72 all tuples are ruled out by existing seminar obstructions; at product 72 there are exactly two cyclic pattern classes.
- Restricted family tested: all-good systems with exact-one enabled processor per configuration and at least one enabled context per processor.

### Open Questions
- Can either product-72 pattern work once bad configurations are allowed?
- In the all-good family, does adding target-state assignment and cycle fairness produce a stronger impossibility proof than the enabled-pattern contradiction already found?
- Is there a compact certificate for “no bad cycle” that is local enough to support exact search in the full model without external SAT/SMT tooling?

## Synthesis after exploration 1

The residue from the first pass is already structural. The known seminar obstruction pushes `n = 5` immediately to product 72, and that leaves only two pattern classes. Both of those classes already fail in the most natural “all configurations are good” search space before target values are even assigned. This strongly suggests that if a product-72 construction exists at all, it must use genuinely bad configurations and nontrivial convergence structure rather than a Gray-code-style or Hamiltonian all-good design.

## Exploration 2

### Strategy
Enumerate all locally consistent good cycles for the two product-72 pattern classes, then test whether the rule entries forced by each cycle already generate an off-cycle recurrent component that cannot be promoted to a fair good cycle.

### Outcome
SUCCEEDED

### Failure Constraint
For both product-72 patterns, every locally consistent good cycle forces an off-cycle recurrent SCC in the singleton-move graph that is structurally incompatible with the good-cycle axioms: either some node has more than one forced move, or the forced cycle omits at least one processor and therefore violates fairness. Since those singleton moves are already determined by the chosen good cycle, every completion contains a bad cycle.

### What This Rules Out
All `n = 5` systems of total product 72. Therefore `M_5 > 72`, hence `M_5 >= 80`.

### Surviving Structure
- Product 72 reduces to exactly two cyclic pattern classes, and both are now eliminated in full generality.
- The corrected recurrent-component screen distinguishes between fatal off-cycle recurrence and harmless additional good cycles; it accepts the known binary `n = 4` two-cycle behavior.
- The completion search recovers an explicit valid binary `n = 4` system with two recurrent cycles, so the new pruning is not accidentally forbidding multi-cycle systems.

### Reformulations
- The crucial move was to treat off-cycle recurrence as acceptable only when it can still become a good cycle. This sharpened the earlier over-strong “any off-cycle cycle is fatal” idea into a sound recurrent-component criterion.
- Enumerating good cycles first, rather than full rule tables, turns the product-72 problem into two finite searches over cycle space: 8392 cycles for `(2,2,2,3,3)` and 1248 cycles for `(2,2,3,2,3)`.

LOAD-BEARING ASSESSMENT: Yes. This is the first representation that reaches beyond the all-good family and actually closes the full product-72 case.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,3 --time-limit 30 --max-cycles 10000` screened 8392 cycles and found 0 survivors.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,3 --time-limit 30 --max-cycles 10000` screened 1248 cycles and found 0 survivors.
- `python3 scripts/p2_completion_search.py 2,2,2,2 --time-limit 10` found a valid binary `n = 4` system with 2 recurrent cycles, confirming that the corrected pruning permits multi-cycle systems when they are fair.

STRUCTURAL RESULTS:
- Product 72 is impossible for `n = 5`.
- Therefore `M_5 >= 80`.

TOOLS:
- Exhaustive cycle enumerator in `scripts/p2_good_cycle_search.py`.
- Fatal recurrent-component screener in `scripts/p2_cycle_screen.py`.
- Sounder partial completion search in `scripts/p2_completion_search.py`.

REPRESENTATIONS:
- Singleton-move graph induced by cycle-forced rule entries.
- Fatal-vs-harmless recurrent-component distinction: an off-cycle forced SCC is harmless only if it can still be a fair good cycle.

### What Would Unblock This
The next natural target is the smallest product above 80 that is not already excluded by the four-consecutive-binary obstruction. The useful artifact is a symmetry-reduced list of `n = 5` state-count patterns at the next product frontier, followed by the same good-cycle-first screen.

### Key Parameters
- Pattern classes screened at product 72: `(2,2,2,3,3)` and `(2,2,3,2,3)`.
- Exhaustive good-cycle counts: 8392 for `(2,2,2,3,3)`; 1248 for `(2,2,3,2,3)`.
- Positive sanity checks: `n = 3` binary cycle survives the screen; `n = 4` binary completion search finds a valid two-cycle system.

### Open Questions
- What is the next unresolved product for `n = 5` after excluding 72 and using the seminar obstruction to exclude 80-type patterns with four consecutive binary processors?
- Does the good-cycle-first screen also eliminate the next product frontier, or does a candidate survive to full completion search?
- Can the fatal recurrent-component criterion be abstracted into a paper-style proof, independent of the specific search scripts?

## Synthesis after exploration 2

The residue from exploration 1 was correct: product 72 could only survive by using bad configurations and possibly multiple good cycles. Exploration 2 addressed exactly that gap. The multi-cycle issue is now understood well enough to be handled soundly, and after doing so the entire product-72 frontier disappears. The investigation has moved from “first unresolved product is 72” to “first unresolved product is strictly above 72, in fact at least 80.”

## Exploration 3

### Strategy
Move to the next `n = 5` product frontier above 80, screen those pattern classes for survivor good cycles, and try full completion only on the survivors.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
Nothing new is ruled out in this exploration; instead it supplies explicit upper-bound constructions at product 96.

### Surviving Structure
- The next product frontier after 80 is 96, with exactly two cyclic pattern classes: `(2,2,2,3,4)` and `(2,2,3,2,4)`.
- Both classes have survivor good cycles under the fatal recurrent-component screen.
- For each survivor cycle, the completion search finds a full valid system quickly.

### Reformulations
- The product frontier can now be handled in two stages: arithmetic reduction of state-count multisets, then survivor-cycle completion. At product 96 this completely closes the case.

LOAD-BEARING ASSESSMENT: Yes. Combined with exploration 2, this effectively determines `M_5`.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Product 96 pattern classes up to rotation and reflection: `(2,2,2,3,4)` and `(2,2,3,2,4)`.
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,4 --time-limit 30 --max-cycles 10000` found a survivor at screened cycle 9.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,4 --time-limit 30 --max-cycles 10000` found a survivor at screened cycle 3.
- `python3 scripts/p2_survivor_completion.py 2,2,2,3,4 --screen-time-limit 30 --completion-time-limit 30 --max-cycles 10000` found a full valid system after screening 9 cycles.
- `python3 scripts/p2_survivor_completion.py 2,2,3,2,4 --screen-time-limit 30 --completion-time-limit 30 --max-cycles 10000` found a full valid system after screening 3 cycles.

STRUCTURAL RESULTS:
- `M_5 <= 96`.
- Since exploration 2 gave `M_5 >= 80`, and the only product frontiers between 72 and 96 are excluded before 96 is reached, the evidence now points to `M_5 = 96`.

TOOLS:
- `scripts/p2_survivor_completion.py`.

REPRESENTATIONS:
- Product-frontier reduction by symmetry plus survivor-cycle completion.

### What Would Unblock This
To turn the current evidence into a clean writeup, the next useful artifact is one explicit product-96 witness system in full rule-table form, plus a short arithmetic argument that no product in `(72,96)` can occur for five integers each at least 2 without falling into the four-consecutive-binary obstruction.

### Key Parameters
- Product frontier after 80: 96.
- Survivor indices found: cycle 9 for `(2,2,2,3,4)`; cycle 3 for `(2,2,3,2,4)`.
- Completion search sizes: 55 nodes / 21 backtracks for `(2,2,2,3,4)`; 62 nodes / 31 backtracks for `(2,2,3,2,4)`.

### Open Questions
- Can the completion witness for product 96 be simplified into a human-comprehensible construction?
- Is there a shorter proof that no `n = 5` product below 96 works, avoiding full good-cycle enumeration at product 72?
- Does the same survivor-cycle methodology scale to `n = 6`, at least enough to improve bounds there?

## Synthesis after exploration 3

The search has crossed from lower bounds into exact small-case determination. Exploration 2 killed the only product-72 patterns; exploration 3 found full constructions at the next frontier, product 96. Unless there is an arithmetic oversight in the list of possible products between 72 and 96, the combined result is `M_5 = 96`.

## Exploration 4

### Strategy
Test whether the good-cycle-first screen extends to `n = 6` by applying it to the first product frontier not already excluded by the four-consecutive-binary obstruction.

### Outcome
SUCCEEDED

### Failure Constraint
For both `n = 6` product-144 pattern classes, every locally consistent good cycle forces a recurrent component in the singleton-move graph that cannot be a fair good cycle.

### What This Rules Out
All product-144 systems for `n = 6`. Therefore the next unresolved `n = 6` frontier is product 192.

### Surviving Structure
- For `n = 6`, the first product frontier after the basic binary obstruction is 144, with pattern classes `(2,2,2,3,2,3)` and `(2,2,3,2,2,3)`.
- Both pattern classes are eliminated by exhaustive cycle screening: 1440 cycles in the first class, 1520 in the second.

### Reformulations
- The arithmetic-frontier plus cycle-screen pipeline is not just an `n = 5` trick; it survives the first nontrivial step to `n = 6`.

LOAD-BEARING ASSESSMENT: Promising. The method still closes the first frontier quickly at `n = 6`, suggesting it may scale at least one or two more frontiers.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,3 --time-limit 30 --max-cycles 2000` screened 1440 cycles and found 0 survivors.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,3 --time-limit 30 --max-cycles 2000` screened 1520 cycles and found 0 survivors.

STRUCTURAL RESULTS:
- Product 144 is impossible for `n = 6`.
- The next `n = 6` product frontier is 192, with classes `(2,2,2,3,2,4)` and `(2,2,3,2,2,4)`.

TOOLS:
- No new tools; the existing cycle screen handled this frontier directly.

REPRESENTATIONS:
- Same product-frontier reduction plus good-cycle-first fatal-recurrence screen as in explorations 2 and 3.

### What Would Unblock This
The natural next step is to screen the two product-192 pattern classes for `n = 6`, and if survivors appear, run the survivor-completion pipeline.

### Key Parameters
- `n = 6` first frontier: 144.
- Pattern classes: `(2,2,2,3,2,3)` and `(2,2,3,2,2,3)`.
- Exhaustive cycle counts: 1440 and 1520.

### Open Questions
- Does `n = 6` admit a construction already at product 192?
- Does the cycle-screen pipeline continue to scale, or does completion search become the bottleneck first?

## Synthesis after exploration 4

The methodology now has a second data point beyond `n = 5`: it closes the first `n = 6` frontier with no new machinery. That is good evidence that the cycle-screen representation is extracting real structure rather than merely overfitting the `n = 5` search space.

## Exploration 5

### Strategy
Push the same cycle screen to the next `n = 6` frontier, product 192, and see whether survivors appear quickly enough to justify launching survivor completion.

### Outcome
STALLED

### Failure Constraint
Pure-Python good-cycle enumeration at `n = 6`, product 192 does not exhaust the cycle space within the current 30-second budget. After 30 seconds, the screen had examined 15,692 cycles for `(2,2,2,3,2,4)` and 18,713 cycles for `(2,2,3,2,2,4)` without finding a survivor, but this is not exhaustive.

### What This Rules Out
No new pattern class is ruled out yet. The screen only gives substantial negative evidence against product 192; it does not close the case.

### Surviving Structure
- The first 5,000 cycles in each product-192 class fail immediately.
- Extending the budget to 30 seconds still finds no survivor in either class.
- The bottleneck is now cycle enumeration throughput, not the survivor completion or verifier stages.

### Reformulations
- The search has split cleanly into a “fast proof” regime (`n = 5`, `n = 6` product 144) and a “throughput-limited” regime (`n = 6` product 192). The next improvement is algorithmic rather than conceptual: better symmetry breaking, memoization of partial rule maps, or a compiled search path.

LOAD-BEARING ASSESSMENT: Moderate. The negative evidence is strong enough to prioritize product 192 as the next target, but not strong enough to record as an obstruction.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,4 --time-limit 30 --max-cycles 50000` screened 15,692 cycles and found 0 survivors before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,4 --time-limit 30 --max-cycles 50000` screened 18,713 cycles and found 0 survivors before the time limit.

STRUCTURAL RESULTS:
- None yet beyond “no survivor seen so far” for product 192.

TOOLS:
- Existing cycle screen remains the active bottleneck.

REPRESENTATIONS:
- No new representation; this is a computational-scale stall.

### What Would Unblock This
- Add stronger symmetry breaking to the good-cycle enumerator.
- Cache partial-rule states during cycle enumeration so repeated subtrees are merged.
- Move the cycle screen to a compiled or lower-overhead implementation if the current Python throughput remains the limiting factor.

### Key Parameters
- `n = 6` product-192 classes: `(2,2,2,3,2,4)` and `(2,2,3,2,2,4)`.
- 30-second screen totals: 15,692 cycles and 18,713 cycles.

### Open Questions
- Is product 192 actually impossible for `n = 6`, or is the screen simply not yet deep enough to reach the first survivor?
- Which optimization would buy the largest gain first: symmetry reduction, memoization, or a faster implementation?

## Synthesis after exploration 5

At five explorations the structure is clearer than the raw search tree. The current methodology cleanly solved `n = 5`, pushed the first `n = 6` frontier from 144 to 192, and then hit a computational wall at the next frontier without producing contradictory evidence. The residue points to an engineering conclusion: future progress on `n = 6` now depends more on search efficiency than on new mathematical reformulations, unless a new obstruction is found that bypasses enumeration entirely.

## Exploration 6

### Strategy
Exploit local state-label symmetry explicitly in the good-cycle enumerator, then re-run the `n = 6`, product-192 screen to see whether the previous computational stall was merely duplicate work.

### Outcome
SUCCEEDED

### Failure Constraint
For both product-192 classes, every symmetry-reduced locally consistent good cycle forces a recurrent component that cannot be a fair good cycle.

### What This Rules Out
All product-192 systems for `n = 6`. Therefore the next unresolved `n = 6` frontier is at least 216.

### Surviving Structure
- The symmetry reduction preserves all earlier benchmark behavior: `n = 3` survives, `n = 5` product 72 still dies, `n = 5` product 96 still has survivors and valid completions.
- At `n = 6`, product 192 is now closed completely rather than sampled.

### Reformulations
- State labels are not just bookkeeping; quotienting by first-use order is a genuine search-space reduction. This is the first time an implementation-level optimization changed a stalled computation into a proof.

LOAD-BEARING ASSESSMENT: High. The symmetry reduction is now part of the default representation for future cycle enumeration.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,4 --time-limit 30 --max-cycles 50000` screened 4590 cycles and found 0 survivors.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,4 --time-limit 30 --max-cycles 50000` screened 5394 cycles and found 0 survivors.
- After symmetry reduction, `python3 scripts/p2_cycle_screen.py 2,2,2,3,3 --time-limit 10 --max-cycles 10000` now screens 2098 cycles instead of 8392, with the same outcome.

STRUCTURAL RESULTS:
- Product 192 is impossible for `n = 6`.
- Therefore `M_6 >= 216`, subject to the same soundness assumption as the earlier cycle-screen arguments.

TOOLS:
- Updated `scripts/p2_good_cycle_search.py` with canonical state-introduction ordering.

REPRESENTATIONS:
- Symmetry-reduced good-cycle search by local label normalization.

### What Would Unblock This
The next step is purely frontier advancement: enumerate the `n = 6` product-216 classes and apply the same cycle screen. If survivors appear, run the survivor-completion pipeline.

### Key Parameters
- `n = 6` product-192 classes: `(2,2,2,3,2,4)` and `(2,2,3,2,2,4)`.
- Exhaustive cycle counts after symmetry reduction: 4590 and 5394.

### Open Questions
- Does `n = 6` first admit a survivor at product 216, or does the lower bound continue to rise?
- Will survivor completion become necessary at the next frontier, or will cycle screening keep closing frontiers by itself?

## Synthesis after exploration 6

The engineering bottleneck from exploration 5 was real but not fundamental. Once local state-label symmetries were quotiented out, the same conceptual pipeline advanced the `n = 6` lower bound from 192 to 216. The methodology is now alternating cleanly between two modes: exact closure by cycle screening when no survivor exists, and explicit witness construction when survivors do appear.

## Exploration 7

### Strategy
Advance one more `n = 6` frontier to product 216, screen all three symmetry classes with the symmetry-reduced cycle search, and see whether the frontier closes or whether survivor completion becomes necessary.

### Outcome
STALLED

### Failure Constraint
The alternating class `(2,3,2,3,2,3)` closes completely, but the other two product-216 classes do not exhaust within the 30-second budget. Their screens show no survivors so far, but not enough coverage for a proof.

### What This Rules Out
The product-216 class `(2,3,2,3,2,3)` is eliminated for `n = 6`.

### Surviving Structure
- Product 216 has three symmetry classes: `(2,2,2,3,3,3)`, `(2,2,3,2,3,3)`, and `(2,3,2,3,2,3)`.
- The alternating class `(2,3,2,3,2,3)` is exhausted and has 0 survivors after 1824 screened cycles.
- The other two classes still show 0 survivors after 7174 and 11023 screened cycles respectively, but those runs are time-limited rather than exhaustive.

### Reformulations
- The alternating pattern is substantially easier than the clustered ones under the current symmetry reduction. This suggests that arrangement of the non-binary processors affects cycle-space complexity sharply, not just the multiset of state counts.

LOAD-BEARING ASSESSMENT: Moderate. The main gain is structural triage inside a frontier: one class is dead, two remain computationally open.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,3,3 --time-limit 30 --max-cycles 50000` screened 7174 cycles and found 0 survivors before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,3,3 --time-limit 30 --max-cycles 50000` screened 11023 cycles and found 0 survivors before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,3,2,3,2,3 --time-limit 30 --max-cycles 50000` screened 1824 cycles exhaustively and found 0 survivors.

STRUCTURAL RESULTS:
- The alternating product-216 class is impossible for `n = 6`.
- The two clustered product-216 classes remain open, but with no survivors seen in the first 18,197 screened cycles combined.

TOOLS:
- No new tools; the current symmetry-reduced screen was sufficient to separate one class from the others.

REPRESENTATIONS:
- Frontier decomposition by cyclic arrangement is now an essential axis, not just product value.

### What Would Unblock This
- Add deeper memoization to the good-cycle search for the two remaining product-216 classes.
- If a survivor eventually appears, hand it directly to the survivor-completion pipeline instead of broadening the cycle search further.

### Key Parameters
- Product-216 classes: `(2,2,2,3,3,3)`, `(2,2,3,2,3,3)`, `(2,3,2,3,2,3)`.
- Exhaustive class: `(2,3,2,3,2,3)` with 1824 cycles.
- Time-limited classes: 7174 and 11023 screened cycles with no survivors.

### Open Questions
- Does either clustered product-216 class actually admit a survivor, or are both just waiting on more search time?
- Is there a pattern-level invariant that separates the alternating class from the clustered classes without enumeration?

## Synthesis after exploration 7

The `n = 6` frontier is no longer a single undifferentiated target. By product 216, arrangement matters enough that one symmetry class closes immediately while two others remain computationally open despite showing no positive evidence. The next gains are likely to come either from stronger caching in the cycle screen or from a new invariant that attacks clustered non-binary arrangements directly.

## Exploration 8

### Strategy
Revisit the two clustered product-216 classes with a much larger search budget, now that symmetry reduction has made the cycle screen significantly faster.

### Outcome
STALLED

### Failure Constraint
The class `(2,2,3,2,3,3)` exhausts cleanly with no survivors, but `(2,2,2,3,3,3)` still does not exhaust even with a 180-second budget. After 35,194 screened cycles it still shows no survivors, but the result remains non-exhaustive.

### What This Rules Out
The product-216 class `(2,2,3,2,3,3)` is eliminated for `n = 6`.

### Surviving Structure
- At product 216, two of the three symmetry classes are now dead: `(2,3,2,3,2,3)` from exploration 7 and `(2,2,3,2,3,3)` from exploration 8.
- The only remaining open class at product 216 is `(2,2,2,3,3,3)`.
- Even in that remaining class, no survivor appeared in 180 seconds across 35,194 screened cycles.

### Reformulations
- Product-frontier analysis has become class-by-class rather than all-or-nothing. This means the open `n = 6` frontier is now a single concrete arrangement class, not an entire product level.

LOAD-BEARING ASSESSMENT: High. The search space has been compressed from “product 216” to one specific cyclic arrangement.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,3,3 --time-limit 180 --max-cycles 1000000` screened 12,138 cycles and found 0 survivors, exhausting the class before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,3,3 --time-limit 180 --max-cycles 1000000` screened 35,194 cycles and found 0 survivors before the time limit.

STRUCTURAL RESULTS:
- Product-216 class `(2,2,3,2,3,3)` is impossible for `n = 6`.
- The only unresolved product-216 class is `(2,2,2,3,3,3)`.

TOOLS:
- No new tools; this was a higher-budget use of the symmetry-reduced cycle screen.

REPRESENTATIONS:
- The frontier is now represented by a single open arrangement class `(2,2,2,3,3,3)`.

### What Would Unblock This
- Stronger memoization keyed by partial rule maps in the good-cycle search, specifically for the open class `(2,2,2,3,3,3)`.
- A secondary invariant that distinguishes the “three consecutive binary processors plus three consecutive ternary processors” arrangement from the already eliminated mixed arrangements.

### Key Parameters
- Exhaustive clustered class: `(2,2,3,2,3,3)` with 12,138 cycles.
- Open clustered class: `(2,2,2,3,3,3)` with 35,194 screened cycles and 0 survivors in 180 seconds.

### Open Questions
- Is `(2,2,2,3,3,3)` actually impossible, or merely the first class whose cycle space is too large for the current implementation?
- Is the next useful improvement algorithmic caching, or a mathematical invariant tailored to the “block of three binary followed by block of three ternary” geometry?

## Synthesis after exploration 8

The `n = 6` product-216 frontier has almost collapsed. Two of its three symmetry classes are gone, and the remaining one has absorbed the full search budget without producing any positive evidence. The investigation is no longer spread across many configurations; it is concentrated on a single arrangement class, which is exactly where a targeted optimization or bespoke invariant becomes worthwhile.

## Exploration 9

### Strategy
Finish the remaining open `n = 6`, product-216 class `(2,2,2,3,3,3)` by running the symmetry-reduced cycle screen to exhaustion.

### Outcome
SUCCEEDED

### Failure Constraint
Every symmetry-reduced locally consistent good cycle in the class `(2,2,2,3,3,3)` forces a recurrent component that cannot be a fair good cycle.

### What This Rules Out
The last remaining product-216 class for `n = 6`. Therefore the entire product-216 frontier is impossible, and `M_6 >= 240`.

### Surviving Structure
- The whole `n = 6` product-216 frontier is now closed: all three symmetry classes are impossible.
- The next product frontier is 240, with classes `(2,2,2,3,2,5)` and `(2,2,3,2,2,5)`.

### Reformulations
- The “single open arrangement class” from exploration 8 was the right granularity. Once isolated, it could be finished directly without further algorithmic changes.

LOAD-BEARING ASSESSMENT: High. The cycle-screen methodology has now advanced `n = 6` across three full product frontiers: 144, 192, and 216.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,3,3 --time-limit 600 --max-cycles 10000000` screened 71,968 cycles and found 0 survivors, exhausting the class before the time limit.

STRUCTURAL RESULTS:
- Product 216 is impossible for `n = 6`.
- Therefore `M_6 >= 240`, subject to the same cycle-screen soundness assumption used in earlier `n = 6` bounds.

TOOLS:
- No new tools; this was an exhaustive use of the existing symmetry-reduced screen.

REPRESENTATIONS:
- Frontier closure at fixed product via arrangement-class decomposition plus exhaustive symmetry-reduced cycle screening.

### What Would Unblock This
The next natural step is product 240 for `n = 6`. If survivors appear there, hand them to the survivor-completion pipeline; if not, keep advancing the lower bound frontier.

### Key Parameters
- Exhaustive cycle count for the final open class `(2,2,2,3,3,3)`: 71,968.
- New next frontier: product 240, classes `(2,2,2,3,2,5)` and `(2,2,3,2,2,5)`.

### Open Questions
- Does `n = 6` first admit a valid construction at product 240?
- Will the frontier keep yielding to cycle screening alone, or is survivor completion about to become active again?

## Synthesis after exploration 9

The `n = 6` picture has sharpened materially. What began as a single lower-bound extension at product 144 has now advanced through 192 and 216, leaving 240 as the next concrete target. The methodology is no longer merely exploratory at `n = 6`; it is systematically converting product frontiers into either impossibility results or explicit survivor candidates.

## Exploration 10

### Strategy
Probe the next `n = 6` frontier, product 240, by screening both symmetry classes deeply enough to detect either a first survivor or another full elimination.

### Outcome
STALLED

### Failure Constraint
Neither product-240 class produced a survivor within a 180-second budget, but neither exhausted either. The current cycle-screen implementation again hits a throughput wall before resolving the frontier.

### What This Rules Out
No new class is ruled out yet at product 240.

### Surviving Structure
- Product 240 has two symmetry classes: `(2,2,2,3,2,5)` and `(2,2,3,2,2,5)`.
- Both classes show the same qualitative behavior: large screens with zero survivors and no exhaustion.
- The open `n = 6` frontier has therefore moved from “many classes” to “two hard classes at one product.”

### Reformulations
- The search has entered a third regime: not frontier explosion, not a single hard class, but a pair of hard classes that both resist the current screen. At this point, improvements must attack per-node screening cost or add a stronger invariant than the current recurrent-component test.

LOAD-BEARING ASSESSMENT: Moderate. The negative evidence is real, but not yet theorem-level.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,5 --time-limit 180 --max-cycles 1000000` screened 27,389 cycles and found 0 survivors before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,5 --time-limit 180 --max-cycles 1000000` screened 39,515 cycles and found 0 survivors before the time limit.

STRUCTURAL RESULTS:
- None yet beyond the absence of early survivors at product 240.

TOOLS:
- No new tools; this is a computational stall with the present cycle screen.

REPRESENTATIONS:
- The active frontier is now exactly two product-240 classes.

### What Would Unblock This
- Memoize repeated fatal-screen computations across DFS branches.
- Add a cheaper branch-level invariant stronger than “no dead config” but weaker than full cycle screening.
- If either class starts yielding a survivor under stronger pruning, hand it immediately to the survivor-completion pipeline.

### Key Parameters
- Product-240 classes: `(2,2,2,3,2,5)` and `(2,2,3,2,2,5)`.
- 180-second screen totals: 27,389 and 39,515 cycles.

### Open Questions
- Is product 240 the first feasible `n = 6` frontier, or just the first one that overwhelms the current implementation?
- Which optimization would give the best next return: caching, stronger branch pruning, or a targeted invariant for the `[2,2,2,3,2,5]` / `[2,2,3,2,2,5]` geometries?

## Synthesis after exploration 10

The methodology has not broken at `n = 6`; it has simply reached the next computational wall. Up through product 216 the pipeline converted frontiers into exact impossibility results. At product 240 it still sees no positive evidence, but the remaining two classes are now large enough that further progress depends on making the cycle screen cheaper or sharper, not on expanding the search target.

## Exploration 11

### Strategy
Profile the hard product-240 screen, optimize the hot path, and validate that the speedup preserves all established benchmark outcomes before returning to the open frontier.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
No new mathematical class is ruled out in this exploration; it improves the search engine.

### Surviving Structure
- The main hot spots were exactly where expected: `consistent_extension` in good-cycle DFS and the recurrent-component screen in `has_fatal_forced_cycle`.
- Precomputing per-configuration transition constraints and switching cycle screening to a singleton-only forced-map representation nearly doubled throughput on the hard product-240 benchmark.

### Reformulations
- For cycle screening, a full domain map is unnecessary because all non-forced contexts are maximally unconstrained. The right representation is a sparse singleton forced map plus cached per-configuration context keys.
- For good-cycle DFS, transitions should be treated as cached static constraints of the state space, not recomputed dynamically.

LOAD-BEARING ASSESSMENT: High. This is an implementation-level reformulation that materially changes what frontiers are computationally accessible.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Before optimization, the profile on `2,2,3,2,2,5` screened 2910 cycles in 20 seconds.
- After optimization, the profile on the same class screened 5764 cycles in 20 seconds.
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,3 --time-limit 10 --max-cycles 10000` still screens 2098 cycles with 0 survivors.
- `python3 scripts/p2_survivor_completion.py 2,2,2,3,4 --screen-time-limit 10 --completion-time-limit 10 --max-cycles 10000` still finds a valid product-96 witness.
- `python3 -m unittest discover -s tests -v` still passes.

STRUCTURAL RESULTS:
- None directly; this is a search-capacity improvement.

TOOLS:
- `scripts/p2_good_cycle_search.py` now uses cached transition tables and lighter consistency extension.
- `scripts/p2_completion_search.py` now includes cached screening data and a sparse singleton-screening routine.
- `scripts/p2_cycle_screen.py` now screens from singleton forced maps directly.

REPRESENTATIONS:
- Sparse forced-map screening representation.
- Cached transition-constraint representation for good-cycle DFS.

### What Would Unblock This
Use the new throughput immediately on the two product-240 classes; if neither exhausts, then the next optimization likely needs branch-level memoization rather than local constant-factor improvements.

### Key Parameters
- Hard benchmark class: `(2,2,3,2,2,5)`.
- 20-second throughput improvement: 2910 -> 5764 screened cycles.

### Open Questions
- Is the new throughput enough to close one or both product-240 classes outright?
- If not, is the next bottleneck still the recurrent-component test, or has the DFS itself become dominant again?

## Synthesis after exploration 11

The bottleneck is now better characterized. The search engine has been upgraded from “frontier-limited” to “frontier-competitive” again, at least temporarily. The next result should come from spending this speedup directly on the two product-240 classes rather than making further speculative optimizations first.

## Exploration 12

### Strategy
Spend the optimized cycle screen directly on the two open `n = 6`, product-240 symmetry classes for a full 180-second pass each, to test whether the throughput gain from exploration 11 is already enough to expose survivors or close a class outright.

### Outcome
STALLED

### Failure Constraint
The current search still does not exhaust either product-240 class within the 180-second budget. The screen is informative only when it either finishes the class or produces an actual survivor; a large survivor-free prefix by itself does not imply impossibility.

### What This Rules Out
This rules out the hope that the exploration-11 constant-factor optimization alone is enough to close product 240 on a short rerun. More generally, any approach that depends only on faster enumeration with the current branch structure is likely to hit the same wall on the remaining product-240 classes.

### Surviving Structure
- Both open product-240 classes still show no evidence of feasible good cycles under the fatal recurrent-component screen.
- The hard class from exploration 11 remains the harder one in absolute count, but both classes now have substantial screened prefixes with zero survivors.

### Reformulations
- Product-240 is now clearly a computational stall rather than a conceptual one. The next useful reformulation should prune DFS branches before full cycle completion, or memoize branch states across many sibling extensions, rather than only making the per-cycle screen cheaper.

LOAD-BEARING ASSESSMENT: Yes. This changes how the next search step should be chosen: the bottleneck is no longer “screen each completed cycle faster,” but “avoid generating so many completed cycles in the first place.”

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,5 --time-limit 180 --max-cycles 1000000` reports `screened=52887 survivors=0 elapsed=180.004s`.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,5 --time-limit 180 --max-cycles 1000000` reports `screened=64655 survivors=0 elapsed=180.000s`.

STRUCTURAL RESULTS:
- None new. Product 240 remains open.

TOOLS:
- The optimized `scripts/p2_cycle_screen.py` remains stable on the open frontier and can now screen roughly fifty to sixty-five thousand good cycles in three minutes on the two remaining classes.

REPRESENTATIONS:
- The singleton forced-map screen remains the right representation for completed cycles, but it is not yet the right representation for pruning partially built cycles.

### What Would Unblock This
- A branch-level prune that detects doomed partial cycles before full cycle completion.
- DFS-state memoization keyed by the partial rule constraints already forced, so equivalent subtrees are not re-explored.
- A class-specific invariant for `(2,2,2,3,2,5)` and `(2,2,3,2,2,5)` that cuts large parts of the good-cycle search tree without waiting for the fatal screen.

### Key Parameters
- Open product-240 classes: `(2,2,2,3,2,5)` and `(2,2,3,2,2,5)`.
- Screen budget per class: 180 seconds, `max_cycles = 1000000`.
- Screened counts with zero survivors: `52887` and `64655`.

### Open Questions
- Can a cheap partial-cycle invariant be derived from the singleton forced-map screen?
- Is branch memoization feasible with the current `consistent_extension` data flow, or does the DFS state need a different canonical encoding first?
- Are the two remaining product-240 classes genuinely impossible, or merely beyond the present exhaustive infrastructure?

## Synthesis after exploration 12

The recent `n = 6` frontiers are now showing a repeatable pattern. A class that survives an initial 180-second screen with zero survivors is not necessarily algorithmically out of reach; if its screened count is already near the total count of the hardest nearby closed class, then a single longer rerun can still finish it. That heuristic was good enough to justify one more brute-force pass at product 240 before spending another exploration on new engineering.

## Exploration 13

### Strategy
Run both remaining `n = 6`, product-240 symmetry classes with a long enough cycle-screen budget to determine whether they are genuinely open or simply a few minutes past the earlier cutoff.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
The entire product-240 frontier for `n = 6`. Any valid `n = 6` construction must have total product strictly larger than 240.

### Surviving Structure
- Product 240 is now completely closed for `n = 6`.
- The product-240 classes were significantly larger than the product-216 classes, but still small enough to settle by brute-force rerun with the post-exploration-11 engine.

### Reformulations
- Exhaustion-count calibration is now an operational tool. Comparing the 180-second screened count to the largest already-closed nearby class gave the right decision rule: the frontier was still in brute-force range, so a longer run was justified before more optimization work.

LOAD-BEARING ASSESSMENT: Moderate to high. This does not change the mathematics, but it changes the search policy and avoided an unnecessary round of implementation work.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,5 --time-limit 600 --max-cycles 10000000` reports `screened=142520 survivors=0 elapsed=449.573s`, exhausting the class before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,5 --time-limit 600 --max-cycles 10000000` reports `screened=174560 survivors=0 elapsed=430.662s`, exhausting the class before the time limit.

STRUCTURAL RESULTS:
- Product-240 class `(2,2,2,3,2,5)` is impossible for `n = 6`.
- Product-240 class `(2,2,3,2,2,5)` is impossible for `n = 6`.
- Therefore the entire product-240 frontier is impossible for `n = 6`.

TOOLS:
- No new tools; this was an exhaustive use of the optimized symmetry-reduced screen.

REPRESENTATIONS:
- Frontier classes should now be tracked together with their exhaustion counts and wall-clock costs, because that data is predictive enough to guide whether the next move is “rerun longer” or “re-engineer.”

### What Would Unblock This
- Compute the exact next product frontier above 240 for `n = 6`, up to rotation/reflection classes.
- Then run the same cycle-screen pipeline on those classes to determine whether the lower bound advances again or a survivor finally appears.

### Key Parameters
- Exhaustive product-240 classes: `(2,2,2,3,2,5)` and `(2,2,3,2,2,5)`.
- Exhaustive counts: `142520` and `174560` screened cycles.
- Wall-clock times: about `450s` and `431s`.

### Open Questions
- What is the exact next `n = 6` product frontier above 240?
- Does the next frontier remain within brute-force range, or does product 240 mark the start of a genuinely larger growth regime?
- Will the first survivor at `n = 6` appear immediately at the next frontier, or only after another full lower-bound step?

## Synthesis after exploration 13

The `n = 6` search has crossed an important threshold. Product 240 looked like the first frontier that might require a new algorithm, but it did not: it was still a finite brute-force problem once the optimized screen was given enough room. The pipeline therefore still has structural headroom. The next useful question is no longer “how do we speed up product 240,” but “what is the next exact frontier, and does the same pipeline still dominate there?”

## Exploration 14 (probe)

### Strategy
Enumerate attainable `n = 6` state-count classes above product 240, modulo rotation and reflection, to identify the exact next frontier before launching more cycle screening.

### Outcome
SUCCEEDED

### Concrete Artifacts
COMPUTED EXAMPLES:
- The next attainable product frontier above 240 is `256`.
- The product-256 symmetry classes are `(2,2,2,4,2,4)` and `(2,2,4,2,2,4)`.
- The next few higher frontiers after that are `288`, `320`, `324`, `336`, and `360`, with the class lists computed explicitly by the probe script.

## Exploration 15

### Strategy
Screen both product-256 symmetry classes for `n = 6` with the same long-budget exhaustive cycle-search pipeline that just closed product 240, to test whether the next frontier still lies within brute-force range.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
The entire product-256 frontier for `n = 6`. Any valid `n = 6` construction must have total product strictly larger than 256.

### Surviving Structure
- Product 256 closes much more easily than product 240: both classes exhaust in under two minutes with zero survivors.
- The apparent difficulty spike at product 240 was therefore not monotone in product size; arrangement and local alphabet geometry still matter more than raw product alone.

### Reformulations
- The search policy reformulation from exploration 13 remains valid, but with an added refinement: nearby-frontier difficulty is not monotone, so frontier choice should be based on actual class geometry and recent counts, not on product size alone.

LOAD-BEARING ASSESSMENT: Moderate. This sharpens the frontier-triage heuristic and warns against assuming that larger product always means harder search.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,4,2,4 --time-limit 600 --max-cycles 10000000` reports `screened=42456 survivors=0 elapsed=97.825s`, exhausting the class before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,2,4,2,2,4 --time-limit 600 --max-cycles 10000000` reports `screened=74008 survivors=0 elapsed=110.539s`, exhausting the class before the time limit.

STRUCTURAL RESULTS:
- Product-256 class `(2,2,2,4,2,4)` is impossible for `n = 6`.
- Product-256 class `(2,2,4,2,2,4)` is impossible for `n = 6`.
- Therefore the entire product-256 frontier is impossible for `n = 6`.
- Combining exploration 15 with the frontier probe from exploration 14 gives `M_6 >= 288`.

TOOLS:
- No new tools; this was another exhaustive use of the optimized symmetry-reduced screen.

REPRESENTATIONS:
- Frontier difficulty must be tracked per symmetry class, not inferred from product alone.

### What Would Unblock This
- Compute the explicit product-288 symmetry classes once more as the live frontier set for convenience in subsequent runs.
- Screen those classes, likely starting with the smallest geometrically clustered ones, to determine whether `M_6` advances again or whether the first survivor appears there.
- If product 288 yields survivors, compare backtracking completion against any available SMT-based completion tool.

### Key Parameters
- Exhaustive product-256 classes: `(2,2,2,4,2,4)` and `(2,2,4,2,2,4)`.
- Exhaustive counts: `42456` and `74008` screened cycles.
- Wall-clock times: about `98s` and `111s`.

### Open Questions
- Which product-288 classes are easiest under the current geometry-sensitive screen?
- Does product 288 finally produce a survivor, or does the lower bound rise again?
- Can the first survivor, if any, be completed faster by SMT than by the current backtracking completion search?

## Synthesis after exploration 15

The `n = 6` frontier is now behaving in a more nuanced way than a simple “harder as product grows” story. Product 240 was hard but finite; product 256 was easier again. That matters because it means the current pipeline is still structurally useful beyond one isolated frontier. The practical consequence is clear: keep advancing the exact frontiers while simultaneously preparing a second construction mechanism for the first survivor-bearing class, rather than prematurely switching the whole investigation into optimization mode.

## Exploration 16

### Strategy
Start the product-288 frontier with two geometrically different classes, one alternating-like and one clustered, to see whether arrangement still sharply controls screening difficulty at the new frontier.

### Outcome
STALLED

### Failure Constraint
The alternating-like class exhausts cleanly, but the clustered class `(2,2,3,3,2,4)` still does not exhaust within 180 seconds. Product 288 therefore does not collapse immediately as a full frontier, even though at least one class remains easy.

### What This Rules Out
The product-288 class `(2,3,2,3,2,4)` is impossible for `n = 6`.

### Surviving Structure
- Product 288 still exhibits the same geometry sensitivity seen at earlier frontiers: the alternating-like arrangement closes quickly, while a clustered arrangement remains computationally open.
- The open class `(2,2,3,3,2,4)` already has a large survivor-free screened prefix.

### Reformulations
- The frontier should again be attacked class-by-class rather than by product level. Product 288 is not a uniform target; it already splits into easy and hard geometries.

LOAD-BEARING ASSESSMENT: Moderate. This reinforces an established search policy rather than introducing a new representation, but it materially sharpens how the remaining product-288 work should be scheduled.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,3,2,3,2,4 --time-limit 180 --max-cycles 1000000` reports `screened=24254 survivors=0 elapsed=76.804s`, exhausting the class before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,2,3,3,2,4 --time-limit 180 --max-cycles 1000000` reports `screened=85222 survivors=0 elapsed=180.000s`.

STRUCTURAL RESULTS:
- Product-288 class `(2,3,2,3,2,4)` is impossible for `n = 6`.

TOOLS:
- No new tools; this was a direct application of the current screen to two representative product-288 classes.

REPRESENTATIONS:
- Product-288 now naturally decomposes into at least one “easy alternating-like” class and several harder clustered classes.

### What Would Unblock This
- Continue product-288 class triage, especially the classes with two adjacent 3-state processors, to see whether the hard/easy split aligns with obvious clustering features.
- If a survivor appears in any product-288 class, compare completion via the current backtracking search against a new SMT-based completion script.
- If all remaining classes show large survivor-free prefixes, the wave-filter perspective may be worth formalizing as a class-level invariant rather than a general conjecture.

### Key Parameters
- Product-288 classes tested: `(2,3,2,3,2,4)` and `(2,2,3,3,2,4)`.
- Exhaustive count for the alternating-like class: `24254`.
- Non-exhaustive screened count for the clustered class: `85222` in 180 seconds with 0 survivors.

### Open Questions
- Which remaining product-288 classes are closer to the easy alternating-like geometry, and which resemble the hard clustered geometry?
- Does any product-288 class produce a survivor, or is this another full lower-bound frontier in disguise?
- Can the wave-filter idea be formalized at least enough to rank product-288 classes by expected difficulty or impossibility?

## Exploration 17

### Strategy
Continue product-288 class triage with three more representative classes, specifically both `...2,6` classes and one clustered `...3,4` class, to determine whether product 288 is still purely a lower-bound frontier or whether a survivor finally appears.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
No new full product frontier is ruled out here, but the data strongly suggests that the `...2,6` classes are harder under the current screen than the clustered survivor-bearing `...3,4` class.

### Surviving Structure
- The product-288 class `(2,2,2,3,3,4)` has a surviving good cycle under the fatal recurrent-component screen.
- The classes `(2,2,2,3,2,6)` and `(2,2,3,2,2,6)` both show large survivor-free prefixes, but neither exhausts in 180 seconds.
- Product 288 is therefore the first `n = 6` frontier with confirmed survivor-bearing structure, at least at the good-cycle stage.

### Reformulations
- Product 288 is no longer just a frontier-elimination problem; it is now a two-mode frontier. Some classes still behave like lower-bound targets, while at least one class has crossed into the “construction” regime where completion search is the right next move.

LOAD-BEARING ASSESSMENT: High. This changes the default next action on the live frontier from more screening to explicit completion on the survivor-bearing class.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,6 --time-limit 180 --max-cycles 1000000` reports `screened=135983 survivors=0 elapsed=180.000s`.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,6 --time-limit 180 --max-cycles 1000000` reports `screened=173150 survivors=0 elapsed=180.000s`.
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,3,4 --time-limit 180 --max-cycles 1000000` finds a survivor at cycle `1438` in `7.782s`, with good-cycle length `28` and mover sequence `(0, 1, 2, 3, 2, 3, 4, 4, 5, 4, 5, 0, 1, 2, 3, 4, 5, 5, 4, 3, 4, 3, 2, 3, 4, 3, 4, 5)`.

STRUCTURAL RESULTS:
- Product 288 is the first tested `n = 6` frontier with a confirmed survivor-bearing class at the good-cycle screening stage.

TOOLS:
- No new tools yet; the existing screen is sufficient to locate survivor-bearing classes.

REPRESENTATIONS:
- The live frontier should now be split into “screen-only classes” and “completion-ready classes.”

### What Would Unblock This
- Run the survivor-completion pipeline on `(2,2,2,3,3,4)` immediately.
- If completion fails or times out, compare the current backtracking completion search with an SMT-based completion tool rather than spending more time on raw screening.
- If completion succeeds, freeze the witness and then return to the remaining product-288 classes only if the exact value of `M_6` is still open.

### Key Parameters
- Product-288 classes tested: `(2,2,2,3,2,6)`, `(2,2,3,2,2,6)`, `(2,2,2,3,3,4)`.
- Two hard classes show no survivors after `135983` and `173150` screened cycles in 180 seconds.
- The first survivor appears quickly in `(2,2,2,3,3,4)`, at cycle `1438`.

### Open Questions
- Does the surviving good cycle in `(2,2,2,3,3,4)` admit a full valid completion?
- Are there additional survivor-bearing product-288 classes, or is `(2,2,2,3,3,4)` exceptional?
- If a completion exists at product 288, is that enough to conclude `M_6 = 288`, or do we still need to clear any smaller open classes first?

## Exploration 18

### Strategy
Run the survivor-completion pipeline on the first confirmed survivor-bearing class `(2,2,2,3,3,4)` to determine whether its screened good cycles actually extend to full valid systems.

### Outcome
STALLED

### Failure Constraint
The current completion search rejects every attempted survivor cycle at the root node: `completion_nodes=1` and `completion_backtracks=1` throughout. So the blocker is not deep combinatorial branching, but an immediate incompatibility detected by the propagation/fatal-cycle stage used by the current completer.

### What This Rules Out
This does not rule out product 288 or even the class `(2,2,2,3,3,4)` outright. It does rule out the naive expectation that “survivor under the singleton fatal screen” is already close to a full completion under the present backtracking pipeline.

### Surviving Structure
- The class `(2,2,2,3,3,4)` contains many survivor cycles under the cycle screen.
- None of the survivor cycles among the first 20,000 screened cycles completed under the current backtracking search.
- The failure happens so early that the relevant object is likely the propagation model itself, not the branching heuristic.

### Reformulations
- There is now a clear gap between the singleton fatal-screen criterion and the stronger propagation model used in completion search. Product 288 is the first setting where that gap matters operationally.

LOAD-BEARING ASSESSMENT: High. This identifies a new phase boundary in the search pipeline: “survives screening” does not imply “worth deep backtracking,” because the completion propagator may already kill the cycle at depth 0.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_survivor_completion.py 2,2,2,3,3,4 --screen-time-limit 180 --completion-time-limit 300 --max-cycles 20000` reports `no valid completion found among 20000 screened cycles in 72.506s`.
- The first survivor appears at screened cycle `1438`, with length `28`, but its completion search immediately fails with `completion_nodes=1 completion_backtracks=1`.
- The same immediate failure pattern persists across many later survivor cycles, including screened cycles in the `14000` range.

STRUCTURAL RESULTS:
- None definitive for `M_6`; product 288 remains open.
- In class `(2,2,2,3,3,4)`, the current completion search finds no valid completion among the first 20,000 screened cycles.

TOOLS:
- `scripts/p2_survivor_completion.py` is informative here not because it finds a witness, but because it localizes the obstruction to the root propagation step.

REPRESENTATIONS:
- Product-288 class `(2,2,2,3,3,4)` is now a concrete testbed for comparing completion models: current propagation/backtracking versus any future SMT-based completion encoding.

### What Would Unblock This
- Inspect one specific survivor cycle from `(2,2,2,3,3,4)` to determine exactly which propagation rule kills it at depth 0.
- Compare that root failure against a second completion method, ideally SMT, to learn whether the current propagator is proving genuine impossibility or merely over-pruning.
- Screen the remaining product-288 classes to see whether another class yields survivors that are easier to complete.

### Key Parameters
- Survivor-bearing class tested: `(2,2,2,3,3,4)`.
- Survivor-completion budget: `screen_time_limit=180`, `completion_time_limit=300`, `max_cycles=20000`.
- Outcome: many survivor cycles, but all attempted completions fail immediately at the root.

### Open Questions
- What exact propagation contradiction kills the first survivor cycle in `(2,2,2,3,3,4)`?
- Is the contradiction intrinsic to the class, or an artifact of the current completion search design?
- Will a different product-288 class yield survivor cycles that do complete?

## Exploration 19 (probe)

### Strategy
Diagnose the first survivor cycle in `(2,2,2,3,3,4)` by replaying the root propagation step and checking which branch of the propagator causes immediate failure.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- For the first survivor cycle in `(2,2,2,3,3,4)`, root propagation reaches a fixed point after one round and then fails specifically because `has_fatal_forced_cycle(...)` returns `True`.
- The root failure is therefore not a dead configuration or an empty-domain contradiction; it is a forced recurrent-component obstruction produced after one propagation pass.

## Exploration 20 (probe)

### Strategy
Extract the specific forced recurrent component that kills the first survivor cycle in `(2,2,2,3,3,4)` after one propagation round.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- The first survivor cycle in `(2,2,2,3,3,4)` dies because propagation creates a fatal SCC of size `63`.
- This SCC involves all processors `0,1,2,3,4,5`, so the obstruction is not “missing fairness.”
- The fatality comes from branching: many nodes in the SCC already have multiple forced moves inside the SCC, violating the deterministic good-cycle structure required by the screen.

## Exploration 21

### Strategy
Finish the first-pass product-288 triage on the three unseen `...3,4` classes to determine whether survivor-bearing behavior is isolated to `(2,2,2,3,3,4)` or widespread across that subfamily.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
This rules out the hypothesis that `(2,2,2,3,3,4)` is an exceptional survivor-bearing class at product 288. Survivor-bearing structure is now confirmed across multiple `...3,4` geometries.

### Surviving Structure
- The classes `(2,2,2,3,4,3)`, `(2,2,3,2,3,4)`, and `(2,2,3,2,4,3)` all produce survivor cycles under the singleton fatal screen.
- In two of those classes, the very first screened cycle is already a survivor.
- Product 288 now looks more like a construction frontier than a pure lower-bound frontier, at least across the `...3,4` subfamily.

### Reformulations
- The product-288 frontier splits naturally into two empirical families: hard `...2,6` / clustered classes with large survivor-free prefixes, and `...3,4` classes that produce survivors almost immediately.

LOAD-BEARING ASSESSMENT: High. This identifies the `...3,4` classes as the main construction target and deprioritizes brute-force screening of those classes relative to completion work.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,4,3 --time-limit 180 --max-cycles 1000000` finds a survivor at cycle `183`, with length `36`, in `0.226s`.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,3,4 --time-limit 180 --max-cycles 1000000` finds a survivor at cycle `1`, with length `32`, in `0.464s`.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,4,3 --time-limit 180 --max-cycles 1000000` finds a survivor at cycle `1`, with length `29`, in `0.136s`.

STRUCTURAL RESULTS:
- Survivor-bearing behavior at product 288 is not isolated; it occurs in at least four distinct symmetry classes.

TOOLS:
- No new tools; the existing screen remains enough to classify product-288 classes into survivor-bearing and survivor-free prefixes.

REPRESENTATIONS:
- Product-288 is best viewed as two empirical subfamilies: `...3,4` classes with easy survivor discovery, and other classes that remain screening-dominated.

### What Would Unblock This
- Run completion immediately on `(2,2,3,2,3,4)` and `(2,2,3,2,4,3)`, since both produce a survivor at cycle `1`.
- If either completes, freeze the witness and update the main problem statement to `M_6 = 288` subject only to the remaining product-288 lower-bound obligations already screened.
- If neither completes under the current search, compare against an SMT-based completion method before abandoning the class.

### Key Parameters
- New survivor-bearing classes: `(2,2,2,3,4,3)`, `(2,2,3,2,3,4)`, `(2,2,3,2,4,3)`.
- Earliest survivor indices: `183`, `1`, and `1`.

### Open Questions
- Which survivor-bearing product-288 class is easiest to complete to a full valid system?
- Are the two hard `...2,6` classes genuinely non-survivor-bearing, or just slower to expose survivors?
- Can the branching-SCC obstruction seen in `(2,2,2,3,3,4)` be avoided by the cycle-1 survivors in the two mixed `...3,4` classes?

## Exploration 22

### Strategy
Run the survivor-completion pipeline on the two mixed product-288 classes `(2,2,3,2,3,4)` and `(2,2,3,2,4,3)`, since both expose a survivor at cycle `1` and are the strongest current candidates for an actual witness.

### Outcome
STALLED

### Failure Constraint
The current backtracking completer no longer fails immediately; instead it explores large search trees and then times out on individual survivor cycles. The bottleneck is now deep completion search, not root propagation.

### What This Rules Out
This rules out the hope that the first easy survivors in the mixed `...3,4` classes would convert immediately into a witness under the current completion pipeline. It does not rule out either class.

### Surviving Structure
- Both mixed `...3,4` classes have survivor cycles that survive root propagation and induce substantial completion branching.
- `(2,2,3,2,3,4)` reached a timed-out completion after screening `9` survivor cycles.
- `(2,2,3,2,4,3)` reached a timed-out completion after screening `16` survivor cycles.

### Reformulations
- Product 288 now has three empirically distinct behaviors:
  - classes with no survivor yet in large screened prefixes,
  - classes with survivors killed immediately by a branching forced SCC,
  - classes with survivors that induce deep completion search.

LOAD-BEARING ASSESSMENT: High. This refines the frontier map from a binary “survivor or not” split into a three-way classification that directly suggests different next tools for different classes.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_survivor_completion.py 2,2,3,2,3,4 --screen-time-limit 60 --completion-time-limit 300 --max-cycles 5000` reports `no valid completion found among 9 screened cycles in 347.225s`, with the last attempted survivor timing out after `145880` completion nodes.
- `python3 scripts/p2_survivor_completion.py 2,2,3,2,4,3 --screen-time-limit 60 --completion-time-limit 300 --max-cycles 5000` reports `no valid completion found among 16 screened cycles in 302.826s`, with the last attempted survivor timing out after `130658` completion nodes.

STRUCTURAL RESULTS:
- None definitive for `M_6`, but the mixed `...3,4` classes remain live witness candidates.

TOOLS:
- `scripts/p2_survivor_completion.py` is now distinguishing “root-impossible survivor classes” from “deep-completion survivor classes.”

REPRESENTATIONS:
- The product-288 frontier should now be tracked in three buckets: no-survivor-yet, root-failure survivors, and deep-search survivors.

### What Would Unblock This
- A second completion engine, ideally SMT-based, for the deep-search survivor classes `(2,2,3,2,3,4)` and `(2,2,3,2,4,3)`.
- Better branching heuristics or stronger propagation for the current backtracking completer, but targeted at the deep-search regime rather than the root-failure regime.
- A way to preserve and replay a specific timed-out survivor cycle so different completion engines can be compared on the exact same instance.

### Key Parameters
- Deep-search survivor classes: `(2,2,3,2,3,4)` and `(2,2,3,2,4,3)`.
- Timed-out completion sizes: about `145880` and `130658` nodes on the hardest attempted survivors so far.

### Open Questions
- Can an SMT completer decide one of the timed-out survivor cycles quickly?
- Is one mixed `...3,4` class materially easier than the other, or are they essentially symmetric in completion difficulty?
- Do the hard `...2,6` classes matter any longer for locating the first witness, or is the witness almost certainly in the mixed `...3,4` family if it exists at product 288?

## Exploration 23 (probe)

### Strategy
Check whether a local Z3 installation is available, so an SMT-based completion engine can be built without leaving the workspace.

### Outcome
SUCCEEDED

### Concrete Artifacts
TOOLS:
- `python3 -c 'import z3; print(z3.get_version_string())'` reports Z3 version `4.16.0`.
- No existing local SMT completion script matching `complete_96.py` or similar is present in the repository.

## Exploration 24 (probe)

### Strategy
Smoke-test the new SMT completion script on the known `n = 5`, product-96 witness class before using it on the open `n = 6` frontier.

### Outcome
SUCCEEDED

### Concrete Artifacts
TOOLS:
- `python3 scripts/p2_smt_completion.py 2,2,2,3,4 --screen-time-limit 10 --solver-timeout-ms 10000 --max-cycles 5000 --max-survivors 5` finds a valid system after screening `5` cycles and trying `1` survivor cycle.

## Exploration 25

### Strategy
Use the new SMT completion engine on the two mixed product-288 classes that timed out under backtracking, to see whether fast exact completion can separate them.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The first ten survivor cycles of `(2,2,3,2,3,4)` all fail exactly: none admits an acyclic completion in the SMT encoding.
- Product 288 is no longer merely a lower-bound frontier; it is feasible for `n = 6`.

### Surviving Structure
- The mixed class `(2,2,3,2,4,3)` contains a full valid system at product 288.
- The mixed class `(2,2,3,2,3,4)` remains open at the class level, but its first ten survivor cycles are all impossible under the exact acyclic-completion encoding.
- The SMT encoding cleanly resolves survivor cycles that were causing six-figure backtracking timeouts.

### Reformulations
- The right completion representation for the hard `n = 6` witness search is not backtracking on rule domains but SMT over rule-table variables plus a rank function on off-cycle configurations.

LOAD-BEARING ASSESSMENT: High. This changes the default witness-search engine on the live frontier and produces the first valid `n = 6` construction.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 2,2,3,2,3,4 --screen-time-limit 60 --solver-timeout-ms 120000 --max-cycles 5000 --max-survivors 10` reports `no valid SMT completion found among 10 survivor cycles within 10 screened cycles in 2.714s`.
- `python3 scripts/p2_smt_completion.py 2,2,3,2,4,3 --screen-time-limit 60 --solver-timeout-ms 120000 --max-cycles 5000 --max-survivors 10` finds `valid system with 1 recurrent cycle(s)` at screened cycle `16` after trying `9` survivor cycles, in `2.064s`.
- Explicit product-288 witness for `n = 6`, state counts `(2,2,3,2,4,3)`:
  - `P0`: `{(0,0,0)->1, (0,0,1)->0, (0,1,0)->1, (0,1,1)->1, (1,0,0)->0, (1,0,1)->0, (1,1,0)->0, (1,1,1)->1, (2,0,0)->0, (2,0,1)->0, (2,1,0)->0, (2,1,1)->0}`
  - `P1`: `{(0,0,0)->0, (0,0,1)->0, (0,0,2)->1, (0,1,0)->0, (0,1,1)->0, (0,1,2)->1, (1,0,0)->1, (1,0,1)->0, (1,0,2)->0, (1,1,0)->1, (1,1,1)->0, (1,1,2)->0}`
  - `P2`: `{(0,0,0)->0, (0,0,1)->0, (0,1,0)->2, (0,1,1)->0, (0,2,0)->2, (0,2,1)->2, (1,0,0)->1, (1,0,1)->0, (1,1,0)->1, (1,1,1)->1, (1,2,0)->2, (1,2,1)->1}`
  - `P3`: `{(0,0,0)->0, (0,0,1)->0, (0,0,2)->1, (0,0,3)->0, (0,1,0)->0, (0,1,1)->0, (0,1,2)->1, (0,1,3)->0, (1,0,0)->0, (1,0,1)->0, (1,0,2)->0, (1,0,3)->0, (1,1,0)->1, (1,1,1)->0, (1,1,2)->1, (1,1,3)->1, (2,0,0)->1, (2,0,1)->0, (2,0,2)->1, (2,0,3)->0, (2,1,0)->1, (2,1,1)->0, (2,1,2)->1, (2,1,3)->1}`
  - `P4`: `{(0,0,0)->0, (0,0,1)->1, (0,0,2)->0, (0,1,0)->2, (0,1,1)->1, (0,1,2)->2, (0,2,0)->2, (0,2,1)->0, (0,2,2)->2, (0,3,0)->0, (0,3,1)->0, (0,3,2)->0, (1,0,0)->1, (1,0,1)->0, (1,0,2)->0, (1,1,0)->1, (1,1,1)->1, (1,1,2)->0, (1,2,0)->3, (1,2,1)->0, (1,2,2)->3, (1,3,0)->3, (1,3,1)->3, (1,3,2)->3}`
  - `P5`: `{(0,0,0)->0, (0,0,1)->0, (0,1,0)->1, (0,1,1)->0, (0,2,0)->0, (0,2,1)->0, (1,0,0)->0, (1,0,1)->0, (1,1,0)->2, (1,1,1)->1, (1,2,0)->2, (1,2,1)->1, (2,0,0)->0, (2,0,1)->0, (2,1,0)->0, (2,1,1)->0, (2,2,0)->2, (2,2,1)->0, (3,0,0)->0, (3,0,1)->1, (3,1,0)->1, (3,1,1)->1, (3,2,0)->2, (3,2,1)->0}`

STRUCTURAL RESULTS:
- Product 288 is feasible for `n = 6`.
- Combined with exploration 15, this gives the exact value `M_6 = 288`.

TOOLS:
- `scripts/p2_smt_completion.py` successfully decides deep-search survivor cycles and finds a witness where backtracking timed out.

REPRESENTATIONS:
- Rank-function SMT completion is now the default representation for witness search once a class reaches the “deep-search survivor” regime.

### What Would Unblock This
- Freeze the explicit product-288 witness into a reusable file and add a regression test.
- Update `docs/p2.md` with the exact result `M_6 = 288`.
- Optionally return to the remaining product-288 classes only for structural classification, not for the value of `M_6`.

### Key Parameters
- Witness-bearing class: `(2,2,3,2,4,3)`.
- Witness found at screened cycle `16`, after `9` survivor attempts.
- SMT runtime to first witness: about `2.064s`.

### Open Questions
- What is the cleanest way to present the product-288 witness and the rank-function SMT method in the writeup?
- Are the remaining product-288 classes impossible, or simply irrelevant now that the exact minimum is known?
- Can the wave-filter idea explain why the mixed `...3,4` class admits a witness while the earlier survivor-bearing classes failed at the propagation stage?

## Synthesis after exploration 25

The search has now completed the full pattern seen across `n = 5` and `n = 6`: brute-force cycle screening raises the lower bound until survivor-bearing classes appear, and then a second-stage completion engine is needed to distinguish “illusory survivors” from actual constructions. At `n = 6`, the original backtracking completer was enough to prove structure but not enough to reach the witness. The key residue from those failures was diagnostic, not negative: it identified the precise regime where a rank-function encoding should replace branching search. Once that reformulation was in place, the witness emerged quickly. The exact value is now `M_6 = 288`.

## Exploration 26

### Strategy
Check whether the newly reported product-288 witness behavior extends to the other `...3,3,4` / `...3,4,3` classes by running the SMT completer directly on their canonical representatives.

### Outcome
STALLED

### Failure Constraint
For the first screened survivor cycles in both canonical classes `(2,2,2,3,3,4)` and `(2,2,2,3,4,3)`, the SMT pipeline does not even reach the solver on most candidates: the shared propagation phase already proves those cycles cannot complete.

### What This Rules Out
This rules out the naive inference that the existence of one product-288 witness automatically makes all nearby `...3,4` permutations easy witness classes. At least in the first several dozen survivor cycles, both canonical classes still fail at the propagation stage.

### Surviving Structure
- `(2,2,2,3,3,4)` still has many survivor cycles under the singleton fatal screen, but the first `48` survivor cycles within the first `5000` screened cycles all die at propagation.
- `(2,2,2,3,4,3)` behaves similarly: the first `31` survivor cycles within the first `5000` screened cycles all die at propagation.
- This does not yet refute a witness in the reflected orientation `(2,2,2,4,3,3)`; it only shows that the canonical search order for the two nearby classes does not quickly expose one.

### Reformulations
- Search order matters even within a symmetry class once completion is involved. A witness may be easy in one orientation/order and hard to surface in another, despite equivalence at the level of existence.

LOAD-BEARING ASSESSMENT: Moderate. This does not change the exact value result, but it matters for how additional witness classes should be sought and how search evidence should be interpreted.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 2,2,2,3,3,4 --screen-time-limit 60 --solver-timeout-ms 120000 --max-cycles 5000 --max-survivors 50` reports `no valid SMT completion found among 48 survivor cycles within 5000 screened cycles in 15.150s`.
- `python3 scripts/p2_smt_completion.py 2,2,2,3,4,3 --screen-time-limit 60 --solver-timeout-ms 120000 --max-cycles 5000 --max-survivors 100` reports `no valid SMT completion found among 31 survivor cycles within 5000 screened cycles in 6.513s`.

STRUCTURAL RESULTS:
- None new for `M_6`; the exact value remains `288`.

TOOLS:
- The SMT completer usefully distinguishes “deep search” from “propagation-impossible” even inside survivor-bearing classes.

REPRESENTATIONS:
- Orientation-sensitive witness search: equivalent classes may still need to be searched in multiple orientations if the goal is to exhibit a second witness rather than just prove existence.

### What Would Unblock This
- Test the exact reported orientation `(2,2,2,4,3,3)` directly rather than relying on its canonical representative.
- If a second witness is found, freeze it as comparative material for the writeup; if not, treat the parallel-agent report as unverified.

### Key Parameters
- Canonical classes tested: `(2,2,2,3,3,4)` and `(2,2,2,3,4,3)`.
- Survivor counts examined: `48` and `31` within the first `5000` screened cycles.

### Open Questions
- Does the reflected orientation `(2,2,2,4,3,3)` expose a witness earlier than the canonical orientation `(2,2,2,3,3,4)`?
- Is the apparent “translator position” effect real, or is it a byproduct of search order?
- Can multiple independent product-288 witness classes be documented cleanly enough to strengthen the writeup without overclaiming structural necessity?

## Exploration 27

### Strategy
Test the exact reported orientation `(2,2,2,4,3,3)` directly with the SMT completer, instead of inferring from its canonical representative.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
This rules out the concern that the parallel-agent witness report was just a search-order artifact or a mismatch with the local tooling. The orientation `(2,2,2,4,3,3)` genuinely admits a full verified product-288 construction in this repository.

### Surviving Structure
- Product 288 now has verified witnesses in at least two distinct symmetry classes: the earlier class `(2,2,3,2,4,3)` and the newly verified class `(2,2,2,4,3,3)` (equivalently canonical `(2,2,2,3,3,4)` under reflection).
- The same local SMT pipeline that found the first witness finds the second almost immediately in this orientation.

### Reformulations
- Orientation-sensitive search order is not just noise: it can be the difference between “no witness seen in thousands of screened cycles” and “witness found almost immediately,” even when existence is reflection-invariant.

LOAD-BEARING ASSESSMENT: Moderate to high. This does not change `M_6`, but it sharpens how witness classes should be explored and strengthens the evidentiary base for the product-288 writeup.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 2,2,2,4,3,3 --screen-time-limit 60 --solver-timeout-ms 120000 --max-cycles 5000 --max-survivors 50` finds `valid system with 1 recurrent cycle(s)` at screened cycle `76` after trying `1` survivor cycle, in `0.390s`.

STRUCTURAL RESULTS:
- The product-288 class represented by `(2,2,2,4,3,3)` is feasible for `n = 6`.
- Therefore product-288 feasibility is not confined to the mixed class `(2,2,3,2,4,3)`.

TOOLS:
- No new tools; this is a confirming use of `scripts/p2_smt_completion.py`.

REPRESENTATIONS:
- Additional evidence that explicit orientation should sometimes be treated as a search parameter, not only as a redundancy to quotient out.

### What Would Unblock This
- Extract and freeze the explicit `(2,2,2,4,3,3)` witness tables for comparative use in the writeup.
- Compare its good-cycle structure to the earlier `(2,2,3,2,4,3)` witness to see what is genuinely shared and what is orientation-specific.

### Key Parameters
- Witness orientation: `(2,2,2,4,3,3)`.
- Witness found at screened cycle `76`, first survivor tried.

### Open Questions
- What are the cleanest structural similarities between the two product-288 witnesses?
- Does the reflected class admit especially short good cycles compared with the mixed class?
- Can the wave-frequency heuristic be sharpened using the two explicit product-288 witnesses now in hand?

## Exploration 28 (probe)

### Strategy
Measure recurrent-cycle move frequencies for the explicit product-96 and product-288 witnesses, to test the emerging “binary reflectors versus higher-state wave carriers” heuristic.

### Outcome
SUCCEEDED

### Concrete Artifacts
COMPUTED EXAMPLES:
- `n = 5`, product `96`, state counts `(2,2,2,3,4)`: recurrent cycle length `18`, processor move counts `{0: 2, 1: 2, 2: 4, 3: 6, 4: 4}`, geometric mean `96^(1/5) ≈ 2.491462`.
- `n = 6`, product `288`, mixed witness `(2,2,3,2,4,3)`: recurrent cycle length `27`, processor move counts `{0: 2, 1: 4, 2: 4, 3: 6, 4: 8, 5: 3}`, geometric mean `288^(1/6) ≈ 2.569797`.
- `n = 6`, product `288`, block witness `(2,2,2,4,3,3)`: recurrent cycle length `35`, processor move counts `{0: 2, 1: 2, 2: 8, 3: 13, 4: 7, 5: 3}`, geometric mean `288^(1/6) ≈ 2.569797`.

STRUCTURAL RESULTS:
- The simple heuristic “binary processors are always low-frequency reflectors” is false in the `n = 6` witnesses: some binary processors move frequently.
- A weaker asymmetry survives: at least one boundary binary processor remains low-frequency in all three explicit witnesses, while the largest-state processor is among the highest-frequency movers.

## Exploration 29 (probe)

### Strategy
Enumerate the smallest admissible `n = 7` state-count products and symmetry classes under the known “four consecutive 2-state processors are impossible” obstruction, so the next computation starts on the true frontier.

### Outcome
SUCCEEDED

### Concrete Artifacts
COMPUTED EXAMPLES:
- The first admissible `n = 7` product is `288`, with a single symmetry class: `(2,2,2,3,2,2,3)`.
- The next few admissible frontiers are:
  - `384`: `(2,2,2,3,2,2,4)`
  - `432`: `(2,2,2,3,2,3,3)`, `(2,2,3,2,2,3,3)`, `(2,2,3,2,3,2,3)`
  - `480`: `(2,2,2,3,2,2,5)`
  - `512`: `(2,2,2,4,2,2,4)`

## Exploration 30

### Strategy
Apply the existing cycle screen directly to the unique `n = 7`, product-288 symmetry class `(2,2,2,3,2,2,3)` to determine whether the new frontier is survivor-bearing or closes immediately.

### Outcome
SUCCEEDED

### Failure Constraint
Every locally consistent good cycle in the class `(2,2,2,3,2,2,3)` already forces a recurrent component that cannot be a fair good cycle.

### What This Rules Out
The entire product-288 frontier for `n = 7`, since that frontier has only one symmetry class.

### Surviving Structure
- The `n = 7` search starts with an immediate class collapse rather than a wide frontier.
- The next admissible frontier is product `384`, again with a single symmetry class `(2,2,2,3,2,2,4)`.

### Reformulations
- The frontier-computation probe from exploration 29 was exactly the right precursor: because product 288 had only one class, the first `n = 7` step was effectively an all-or-nothing test, not a multi-class triage problem.

LOAD-BEARING ASSESSMENT: Moderate. This is not a new mathematical representation, but it confirms that the current frontiers for `n = 7` are still sparse enough to attack one class at a time.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,2,3 --time-limit 180 --max-cycles 1000000` reports `screened=430 survivors=0 elapsed=0.418s`, exhausting the class before the time limit.

STRUCTURAL RESULTS:
- Product 288 is impossible for `n = 7`.
- Therefore `M_7 >= 384`, under the same cycle-screen soundness assumption used for the earlier lower bounds.

TOOLS:
- No new tools; the existing cycle screen is still effective on the first `n = 7` frontier.

REPRESENTATIONS:
- None new beyond the single-class frontier reduction from exploration 29.

### What Would Unblock This
- Screen the unique product-384 class `(2,2,2,3,2,2,4)` immediately.
- If that also closes, the next nontrivial `n = 7` frontier will be product 432 with three symmetry classes, which is the first point where class triage will matter again.

### Key Parameters
- `n = 7` product-288 class: `(2,2,2,3,2,2,3)`.
- Exhaustive screened count: `430`.

### Open Questions
- Does the unique product-384 class also close immediately?
- At what `n = 7` frontier do survivor cycles first appear, if any?
- Does `M_7^{1/7}` continue the upward trend from `M_5^{1/5}` to `M_6^{1/6}`?

## Synthesis after exploration 30

The `n = 7` search is starting in a cleaner shape than `n = 6` did. The first admissible frontier is not a family but a single class, and it dies instantly. That means the next few `n = 7` steps can still be taken as exact frontier advances rather than heuristic fishing. The geometric means already computed, `96^(1/5) ≈ 2.491` and `288^(1/6) ≈ 2.570`, make this especially worth tracking: even a modest new lower bound at `n = 7` would continue the upward small-`n` trend.

## Exploration 31

### Strategy
Screen the unique `n = 7`, product-384 class `(2,2,2,3,2,2,4)` immediately, before the frontier branches into multiple classes at product 432.

### Outcome
SUCCEEDED

### Failure Constraint
Every locally consistent good cycle in the class `(2,2,2,3,2,2,4)` already forces a recurrent component that cannot be a fair good cycle.

### What This Rules Out
The entire product-384 frontier for `n = 7`, since that frontier also has only one symmetry class.

### Surviving Structure
- The `n = 7` frontiers at 288 and 384 both collapse outright.
- Product 432 is the first `n = 7` frontier with multiple symmetry classes: `(2,2,2,3,2,3,3)`, `(2,2,3,2,2,3,3)`, and `(2,2,3,2,3,2,3)`.

### Reformulations
- None new mathematically, but the “single class until product 432” pattern means `n = 7` is still behaving like a frontier-advancement problem rather than a witness-search problem.

LOAD-BEARING ASSESSMENT: Moderate. This narrows the next frontier exactly and keeps the computation focused.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,2,4 --time-limit 180 --max-cycles 1000000` reports `screened=5974 survivors=0 elapsed=8.084s`, exhausting the class before the time limit.

STRUCTURAL RESULTS:
- Product 384 is impossible for `n = 7`.
- Therefore `M_7 >= 432`, under the same cycle-screen soundness assumption used in earlier bounds.

TOOLS:
- No new tools; the current cycle screen remains effective on the first two `n = 7` frontiers.

REPRESENTATIONS:
- Product-432 frontier decomposition for `n = 7`: three symmetry classes.

### What Would Unblock This
- Screen the three product-432 classes next, preferably in parallel.
- Use the results to decide whether `n = 7` continues the “easy lower-bound advance” pattern or reaches the first survivor-bearing frontier.

### Key Parameters
- `n = 7` product-384 class: `(2,2,2,3,2,2,4)`.
- Exhaustive screened count: `5974`.

### Open Questions
- Does any product-432 class yield a survivor?
- Are alternating-like `n = 7` classes easier than clustered ones, as in `n = 6`?
- If product 432 also closes, how fast does `M_7^{1/7}` rise relative to the `n = 6` value?

## Exploration 32

### Strategy
Screen all three `n = 7`, product-432 symmetry classes in parallel to determine whether the first multi-class frontier is still purely eliminative or begins to show survivor-bearing structure.

### Outcome
SUCCEEDED

### Failure Constraint
For each of the three product-432 classes, every locally consistent good cycle already forces a recurrent component that cannot be a fair good cycle.

### What This Rules Out
The entire product-432 frontier for `n = 7`.

### Surviving Structure
- `n = 7` continues to behave as a lower-bound frontier problem rather than a witness-search problem through product 432.
- The next admissible frontier is product `480`, again with a single symmetry class `(2,2,2,3,2,2,5)`.

### Reformulations
- The geometry-sensitive split seen in `n = 6` has not appeared yet at `n = 7`; even the first three-class frontier closes uniformly.

LOAD-BEARING ASSESSMENT: Moderate. This is mainly a strong frontier advance, but it also says the `n = 7` search has not yet entered the survivor regime.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,3,3 --time-limit 180 --max-cycles 1000000` reports `screened=13459 survivors=0 elapsed=25.222s`.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,3,3 --time-limit 180 --max-cycles 1000000` reports `screened=14410 survivors=0 elapsed=25.592s`.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,3,2,3 --time-limit 180 --max-cycles 1000000` reports `screened=2140 survivors=0 elapsed=4.489s`.

STRUCTURAL RESULTS:
- Product 432 is impossible for `n = 7`.
- Therefore `M_7 >= 480`, under the same cycle-screen soundness assumption used for the earlier bounds.

TOOLS:
- No new tools; the cycle screen remains sufficient through the first multi-class `n = 7` frontier.

REPRESENTATIONS:
- Product-480 frontier for `n = 7`: single class `(2,2,2,3,2,2,5)`.

### What Would Unblock This
- Screen the unique product-480 class next.
- If that closes too, continue exact frontier advancement to 512 and then 576, where the class count starts growing enough to make triage relevant again.

### Key Parameters
- Product-432 classes: `(2,2,2,3,2,3,3)`, `(2,2,3,2,2,3,3)`, `(2,2,3,2,3,2,3)`.
- Exhaustive screened counts: `13459`, `14410`, and `2140`.

### Open Questions
- Does the unique product-480 class also collapse quickly?
- At which `n = 7` product will survivor cycles first appear?
- Does the absence of survivor-bearing classes through 432 indicate that `M_7^{1/7}` will keep rising substantially?

## Synthesis after exploration 32

The `n = 7` picture is now materially different from `n = 6`. At `n = 6`, survivor-bearing classes appeared exactly at the frontier that ended up being feasible. At `n = 7`, the first three admissible frontiers, 288, 384, and 432, all close outright, and even the first multi-class frontier shows no geometry split. This is the strongest small-`n` evidence so far that the per-processor geometric mean is still trending upward rather than settling near a low constant.

## Exploration 33

### Strategy
Screen the unique `n = 7`, product-480 class `(2,2,2,3,2,2,5)` to see whether exact frontier advancement continues smoothly past 432.

### Outcome
STALLED

### Failure Constraint
The class does not exhaust within the 180-second budget. The current evidence is only a large survivor-free prefix, not an impossibility proof.

### What This Rules Out
This rules out the hope that all early `n = 7` frontiers will collapse immediately. Product 480 is the first `n = 7` frontier to present a genuine computational stall under the current screen.

### Surviving Structure
- No survivor appears in the first `76,992` screened good cycles of `(2,2,2,3,2,2,5)`.
- Product 480 is the first `n = 7` frontier whose difficulty looks closer to the harder `n = 6` frontiers than to the early `n = 7` collapses.

### Reformulations
- The `n = 7` investigation has now entered the same “survivor-free but not exhausted” regime that product 240 created earlier for `n = 6`.

LOAD-BEARING ASSESSMENT: Moderate. This is a computational-phase transition rather than a new representation, but it changes the immediate search policy.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,2,5 --time-limit 180 --max-cycles 1000000` reports `screened=76992 survivors=0 elapsed=180.001s`.

STRUCTURAL RESULTS:
- None new. Product 480 remains open.

TOOLS:
- No new tools; this is the first `n = 7` class that seems to require either a longer run or another optimization.

REPRESENTATIONS:
- None new.

### What Would Unblock This
- A longer run on the same class, calibrated against earlier frontier closures.
- If no survivor appears after a significantly longer run, move to product 512 only after logging the computational wall clearly.
- If a survivor does appear, switch immediately to SMT completion rather than backtracking completion.

### Key Parameters
- Open class: `(2,2,2,3,2,2,5)`.
- Survivor-free screened prefix: `76,992` cycles in `180s`.

### Open Questions
- Is product 480 still in brute-force range with a 600-second rerun, or is it the first `n = 7` frontier that really needs a new idea?
- Would the next frontier, product 512, actually be easier despite being larger, as happened once at `n = 6`?
- Does the first `n = 7` survivor appear at 480, 512, or later?

## Exploration 34

### Strategy
Rerun the open `n = 7`, product-480 class `(2,2,2,3,2,2,5)` with a much longer budget to determine whether the 180-second stall was a genuine wall or just a near-miss.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
The entire product-480 frontier for `n = 7`.

### Surviving Structure
- Product 480 was not a new conceptual barrier; it was still in brute-force range once given enough time.
- The next admissible frontier is product `512`, again with a single symmetry class `(2,2,2,4,2,2,4)`.

### Reformulations
- The calibration heuristic from `n = 6` remains valid at `n = 7`: a survivor-free 180-second prefix can still be close enough to exhaustion that one longer run is the right move.

LOAD-BEARING ASSESSMENT: Moderate to high. This keeps the search in exact-frontier mode and avoids a premature switch to new tooling.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,2,5 --time-limit 600 --max-cycles 10000000` reports `screened=190160 survivors=0 elapsed=382.010s`, exhausting the class before the time limit.

STRUCTURAL RESULTS:
- Product 480 is impossible for `n = 7`.
- Therefore `M_7 >= 512`, under the same cycle-screen soundness assumption used for the earlier bounds.

TOOLS:
- No new tools; this was an exhaustive use of the current screen.

REPRESENTATIONS:
- Product-512 frontier for `n = 7`: single class `(2,2,2,4,2,2,4)`.

### What Would Unblock This
- Screen the unique product-512 class next.
- If that closes too, move to product 576, where the class count grows and the first genuine class triage for larger `n = 7` products will begin.

### Key Parameters
- `n = 7` product-480 class: `(2,2,2,3,2,2,5)`.
- Exhaustive screened count: `190160`.
- Exhaustive wall-clock time: `382.010s`.

### Open Questions
- Does the unique product-512 class also stay within brute-force range?
- At what `n = 7` frontier do survivor cycles first appear?
- How much of the remaining `n = 7` progression can still be handled by the current screen before SMT completion becomes relevant again?

## Synthesis after exploration 34

The `n = 7` story has sharpened: up through product 480, every admissible frontier closes. The only nontrivial behavior so far has been computational, not structural, and even that has yielded to a longer run. This is materially stronger than the `n = 6` progression, where survivor-bearing classes appeared exactly at the true frontier. At `n = 7`, the first four admissible frontiers are all impossible.

## Exploration 35

### Strategy
Screen the unique `n = 7`, product-512 class `(2,2,2,4,2,2,4)` to determine whether the exact frontier advance continues one more step before the class count expands at product 576.

### Outcome
SUCCEEDED

### Failure Constraint
Every locally consistent good cycle in the class `(2,2,2,4,2,2,4)` already forces a recurrent component that cannot be a fair good cycle.

### What This Rules Out
The entire product-512 frontier for `n = 7`.

### Surviving Structure
- Up through product 512, every admissible `n = 7` frontier is now closed.
- Product 576 is the next live frontier and the first one with many classes (`8` symmetry classes from exploration 29).

### Reformulations
- None new mathematically. Computationally, `n = 7` remains in exact-frontier mode through product 512.

LOAD-BEARING ASSESSMENT: Moderate. This materially advances the lower bound and identifies the first genuinely broader `n = 7` frontier.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,4,2,2,4 --time-limit 180 --max-cycles 1000000` reports `screened=80736 survivors=0 elapsed=141.547s`, exhausting the class before the time limit.

STRUCTURAL RESULTS:
- Product 512 is impossible for `n = 7`.
- Therefore `M_7 >= 576`, under the same cycle-screen soundness assumption used for the earlier bounds.

TOOLS:
- No new tools; the current screen is still sufficient through the product-512 frontier.

REPRESENTATIONS:
- Product-576 frontier for `n = 7`: eight symmetry classes (listed in exploration 29).

### What Would Unblock This
- Triage the product-576 classes rather than attempting all of them blindly at full depth.
- Start with the more alternating-looking `...3,4` / `...4,3` geometries to see whether survivor-bearing behavior finally appears there, mirroring the `n = 6` frontier split.

### Key Parameters
- `n = 7` product-512 class: `(2,2,2,4,2,2,4)`.
- Exhaustive screened count: `80736`.
- Exhaustive wall-clock time: `141.547s`.

### Open Questions
- Which of the eight product-576 classes are easiest under the current geometry-sensitive screen?
- Does product 576 finally produce survivor cycles?
- If the first survivor does appear at 576, will it belong to a mixed `...3,4` class as in `n = 6`?

## Exploration 36

### Strategy
Triage the product-576 frontier by screening three representative classes in parallel: an alternating-like class `(2,2,3,2,3,2,4)`, a mixed `...4,3` class `(2,2,2,3,2,4,3)`, and the large-alphabet class `(2,2,2,3,2,2,6)`.

### Outcome
STALLED

### Failure Constraint
Only the alternating-like class exhausts within the 180-second budget. The mixed `...4,3` and `...2,6` classes still do not exhaust, so the frontier does not yet collapse or produce a survivor.

### What This Rules Out
The product-576 class `(2,2,3,2,3,2,4)` is impossible for `n = 7`.

### Surviving Structure
- Product 576 is the first `n = 7` frontier to show the same kind of geometry-sensitive split that appeared at `n = 6`.
- The alternating-like class closes quickly.
- The mixed `...4,3` class and the `...2,6` class both show large survivor-free prefixes with no positive evidence yet.

### Reformulations
- The `n = 7` search has now entered class-triage mode in earnest. Product 576 is not uniform: some geometries are easy lower-bound targets, while others are computationally open.

LOAD-BEARING ASSESSMENT: Moderate to high. This is the first clear signal that the `n = 6` pattern of geometry-sensitive frontiers has reappeared at `n = 7`.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,3,2,4 --time-limit 180 --max-cycles 1000000` reports `screened=26970 survivors=0 elapsed=84.910s`, exhausting the class before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,4,3 --time-limit 180 --max-cycles 1000000` reports `screened=63362 survivors=0 elapsed=180.000s`.
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,2,6 --time-limit 180 --max-cycles 1000000` reports `screened=78156 survivors=0 elapsed=180.000s`.

STRUCTURAL RESULTS:
- Product-576 class `(2,2,3,2,3,2,4)` is impossible for `n = 7`.

TOOLS:
- No new tools; this was a frontier-triage use of the existing cycle screen.

REPRESENTATIONS:
- Product-576 now splits empirically into at least one “easy alternating-like” class and multiple harder clustered/large-alphabet classes.

### What Would Unblock This
- Either continue triage within product 576, or test structurally motivated witness candidates at larger products if there is a compelling pattern worth probing.
- If a survivor appears in any product-576 class, switch immediately to SMT completion rather than backtracking completion.

### Key Parameters
- Product-576 classes tested: `(2,2,3,2,3,2,4)`, `(2,2,2,3,2,4,3)`, `(2,2,2,3,2,2,6)`.
- One class exhausted at `26970` screened cycles; two others remain open after `63362` and `78156` screened cycles.

### Open Questions
- Are the mixed `...4,3` and `...2,6` classes genuinely open, or just a few minutes from closure?
- Does the first actual `n = 7` survivor live inside product 576, or at a larger structurally patterned product such as `864`?
- How predictive is the emerging “3 binary + 1 quaternary + rest ternary” pattern suggested by the known `n = 5` and `n = 6` witnesses?

## Exploration 37

### Strategy
Test the structurally motivated product-864 pattern `(2,2,2,4,3,3,3)` directly with the SMT completion pipeline, to see whether the `3` binary `+ 1` quaternary `+ (n-4)` ternary pattern extrapolates from `n = 5,6` to `n = 7`.

### Outcome
STALLED

### Failure Constraint
No survivor cycles appear at all within the first `5000` screened cycles, so the attempt does not even reach SMT completion. The current evidence is purely negative screening evidence, not impossibility.

### What This Rules Out
This rules out the hope that the pattern `(2,2,2,4,3,3,3)` would yield an immediate easy witness at `n = 7`.

### Surviving Structure
- The pattern remains conceptually interesting, but it does not surface a quick witness under the current enumeration order.
- The product-576 frontier remains the more concrete source of immediate progress.

### Reformulations
- None new. This was a direct pattern probe rather than a new representation.

LOAD-BEARING ASSESSMENT: Low to moderate. It weakens a tempting extrapolation, but does not yet say whether the pattern is false or merely hard to reach computationally.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 2,2,2,4,3,3,3 --screen-time-limit 60 --solver-timeout-ms 120000 --max-cycles 5000 --max-survivors 20` reports `no valid SMT completion found among 0 survivor cycles within 5000 screened cycles in 17.394s`.

STRUCTURAL RESULTS:
- None definitive for `n = 7`; product `864` remains completely open.

TOOLS:
- The SMT pipeline here effectively acts as a screened witness probe because no survivor cycles appear.

REPRESENTATIONS:
- None new.

### What Would Unblock This
- Either a longer screen on `(2,2,2,4,3,3,3)`, or a more targeted cycle generator seeded by the known `n = 5,6` witness structure.
- In the short term, continuing exact progress on product 576 is likely higher-yield.

### Key Parameters
- Pattern-tested class: `(2,2,2,4,3,3,3)`.
- No survivors within the first `5000` screened cycles.

### Open Questions
- Is the `32·3^(n-4)` pattern genuinely false at `n = 7`, or just hidden deeper in the cycle space?
- Would a structurally seeded cycle generator expose promising cycles for this class more efficiently than blind enumeration?
- Is the current product-576 frontier still the best next use of compute time?

## Exploration 38

### Strategy
Continue product-576 triage by screening three untested classes closer to the mixed `...3,4` witness-bearing geometries from `n = 6`: `(2,2,3,2,4,2,3)`, `(2,2,3,2,2,3,4)`, and `(2,2,3,3,2,2,4)`.

### Outcome
STALLED

### Failure Constraint
Only `(2,2,3,2,4,2,3)` exhausts within the 180-second budget. The other two classes still do not exhaust, so the frontier remains computationally open.

### What This Rules Out
The product-576 class `(2,2,3,2,4,2,3)` is impossible for `n = 7`.

### Surviving Structure
- The alternating/mixed class `(2,2,3,2,4,2,3)` closes, adding to the pattern that more alternating 576-classes are easier.
- The clustered classes `(2,2,3,2,2,3,4)` and `(2,2,3,3,2,2,4)` both show large survivor-free prefixes with no positive evidence yet.
- Product 576 still has no survivor in any screened class so far.

### Reformulations
- The `n = 7` product-576 frontier now appears to split similarly to `n = 6`: alternating-like classes die first, while clustered classes absorb the search budget.

LOAD-BEARING ASSESSMENT: Moderate. This is the clearest geometry-sensitive split at `n = 7` so far, even though it has not yet produced a survivor.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,4,2,3 --time-limit 180 --max-cycles 1000000` reports `screened=23706 survivors=0 elapsed=85.652s`, exhausting the class before the time limit.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,3,4 --time-limit 180 --max-cycles 1000000` reports `screened=94687 survivors=0 elapsed=180.001s`.
- `python3 scripts/p2_cycle_screen.py 2,2,3,3,2,2,4 --time-limit 180 --max-cycles 1000000` reports `screened=63649 survivors=0 elapsed=180.000s`.

STRUCTURAL RESULTS:
- Product-576 class `(2,2,3,2,4,2,3)` is impossible for `n = 7`.

TOOLS:
- No new tools; this was another frontier-triage use of the existing screen.

REPRESENTATIONS:
- Product-576 now has at least two empirically distinct subfamilies: easier alternating-like classes and harder clustered classes.

### What Would Unblock This
- Screen the last untested product-576 class `(2,2,2,3,3,2,4)`.
- Then decide whether to rerun one or two of the hard clustered classes longer, or move on to product 648/864 only if a compelling structural reason appears.

### Key Parameters
- Product-576 classes tested: `(2,2,3,2,4,2,3)`, `(2,2,3,2,2,3,4)`, `(2,2,3,3,2,2,4)`.
- Exhaustive count for the easy class: `23706`.
- Survivor-free screened prefixes for the harder classes: `94687` and `63649`.

### Open Questions
- Does the remaining untested class `(2,2,2,3,3,2,4)` behave like the easy alternating classes or the hard clustered ones?
- Is product 576 genuinely survivor-free, or are the clustered classes simply a few hundred thousand cycles away from their first survivors?
- If the first `n = 7` survivor appears later, will it again sit in a mixed `...3,4` class, or in a different geometry entirely?

## Exploration 39

### Strategy
Screen the last untested product-576 class `(2,2,2,3,3,2,4)` to complete the first-pass classification of the entire frontier.

### Outcome
STALLED

### Failure Constraint
The class does not exhaust within 180 seconds. Like the other clustered holdouts, it yields only a large survivor-free prefix.

### What This Rules Out
This rules out the possibility that `(2,2,2,3,3,2,4)` was an easy final class that would immediately collapse the frontier picture. All remaining open product-576 classes are now in the same hard clustered regime.

### Surviving Structure
- Product 576 is fully triaged: two more alternating-like classes are dead, and the remaining open classes are all clustered.
- The class `(2,2,2,3,3,2,4)` shows no survivor in the first `63,270` screened cycles.

### Reformulations
- Product 576 should now be treated as a clustered-class computational wall, not as a uniform frontier.

LOAD-BEARING ASSESSMENT: Moderate. This completes the first classification of the product-576 frontier and says exactly where the remaining uncertainty lives.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,3,2,4 --time-limit 180 --max-cycles 1000000` reports `screened=63270 survivors=0 elapsed=180.000s`.

STRUCTURAL RESULTS:
- None new for `M_7`; product 576 remains open.

TOOLS:
- No new tools; this is a classification result from the existing screen.

REPRESENTATIONS:
- Product-576 frontier split:
  - Exhausted dead classes so far: `(2,2,3,2,3,2,4)` and `(2,2,3,2,4,2,3)`
  - Open clustered classes so far: `(2,2,2,3,2,4,3)`, `(2,2,2,3,2,2,6)`, `(2,2,3,2,2,3,4)`, `(2,2,3,3,2,2,4)`, `(2,2,2,3,3,2,4)`

### What Would Unblock This
- A longer run on one or two of the clustered classes to see whether they close or reveal survivors.
- If longer runs still show no survivors, the next decision is whether to keep grinding product 576 or test larger structurally motivated classes for a quicker witness.

### Key Parameters
- Last-class screened prefix: `63270` cycles with `0` survivors in `180s`.

### Open Questions
- Which clustered product-576 class is closest to exhaustion under a longer run?
- Is the first `n = 7` survivor hidden inside product 576, or does it first appear at a larger product?
- Is a longer run more promising than returning to structured witness guesses such as the `864` family?

## Exploration 40

### Strategy
Take the hardest product-576 holdout `(2,2,3,2,2,3,4)` to a 600-second budget, to determine whether product 576 is still in brute-force range or has become the first real `n = 7` computational wall.

### Outcome
STALLED

### Failure Constraint
Even a 600-second run does not exhaust the class or expose a survivor. The evidence is now a very large survivor-free prefix rather than a near-miss.

### What This Rules Out
This rules out the idea that product 576 is just one longer rerun away from immediate closure. At least some clustered classes at this frontier are genuinely expensive under the current screen.

### Surviving Structure
- `(2,2,3,2,2,3,4)` remains survivor-free after `270,674` screened cycles.
- Product 576 is now the first `n = 7` frontier that clearly behaves like a true computational wall rather than a sequence of near-closing frontiers.

### Reformulations
- The current `n = 7` search has bifurcated: exact frontier advancement is still possible on easy classes, but the clustered product-576 classes now require either patience at scale or a stronger idea.

LOAD-BEARING ASSESSMENT: High. This is the clearest boundary yet between “frontier advance by brute force” and “frontier advance needs a new advantage.”

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,3,4 --time-limit 600 --max-cycles 10000000` reports `screened=270674 survivors=0 elapsed=600.000s`.

STRUCTURAL RESULTS:
- None new for `M_7`; product 576 remains open.

TOOLS:
- No new tools; this result measures the current limit of the existing screen on `n = 7`.

REPRESENTATIONS:
- None new.

### What Would Unblock This
- Either identify a clustered product-576 class that is actually closer to exhaustion, or pivot to a different kind of leverage: better pruning, a structural invariant, or a more targeted witness search.
- A particularly useful next data point would be a 600-second run on one of the `~63k-in-180s` clustered classes, to see whether they close materially faster than `(2,2,3,2,2,3,4)`.

### Key Parameters
- Hardest product-576 class tested so far: `(2,2,3,2,2,3,4)`.
- Survivor-free screened prefix: `270,674` cycles in `600s`.

### Open Questions
- Are the `~63k-in-180s` clustered classes close enough to close with a 600-second rerun?
- Is the first `n = 7` survivor more likely to appear at product 576 or at a larger structured family?
- What kind of structural invariant would cut clustered product-576 classes without waiting for full cycle completion?

## Exploration 41

### Strategy
Take one of the `~63k-in-180s` clustered classes, `(2,2,2,3,2,4,3)`, to a 600-second budget to see whether the product-576 wall is localized to the hardest class or shared across the clustered subfamily.

### Outcome
STALLED

### Failure Constraint
Even with a 600-second budget, the class does not exhaust and still produces no survivors. This shows the heavy behavior is not confined to a single outlier class.

### What This Rules Out
This rules out the optimistic hypothesis that some clustered product-576 classes are still close enough to close with a modest rerun. The clustered subfamily as a whole now looks genuinely difficult.

### Surviving Structure
- `(2,2,2,3,2,4,3)` remains survivor-free after `169,575` screened cycles in `600s`.
- Combined with exploration 40, there is now no positive evidence anywhere in the clustered product-576 subfamily, despite very large screened prefixes.
- `M_7 >= 576` remains the current exact lower bound; product 576 itself is the first substantial `n = 7` computational wall.

### Reformulations
- Product 576 should now be treated as a frontier where new leverage is likely needed. Longer brute-force runs may still help, but they are no longer obviously the dominant move.

LOAD-BEARING ASSESSMENT: High. This turns product 576 from “open frontier” into “identified wall,” which changes how the next work should be chosen.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,4,3 --time-limit 600 --max-cycles 10000000` reports `screened=169575 survivors=0 elapsed=600.000s`.

STRUCTURAL RESULTS:
- None new for `M_7`; product 576 remains open.

TOOLS:
- No new tools; this is another limit-measurement result for the current screen.

REPRESENTATIONS:
- Product-576 clustered subfamily now has two long-budget survivor-free examples: `(2,2,3,2,2,3,4)` and `(2,2,2,3,2,4,3)`.

### What Would Unblock This
- A stronger branch-level invariant for clustered product-576 classes.
- A more targeted witness search seeded by the `n = 5,6` witness structures, if the goal is to find the first `n = 7` construction rather than to keep advancing lower bounds uniformly.
- Another computational angle, such as symmetry-aware cycle seeding or a new completion-style screen that can work before full cycle exhaustion.

### Key Parameters
- Long-budget clustered class: `(2,2,2,3,2,4,3)`.
- Survivor-free screened prefix: `169,575` cycles in `600s`.

### Open Questions
- Is product 576 actually impossible, or merely beyond the present frontier machinery?
- Which new kind of leverage is most plausible here: pruning, seeding, or a structural invariant?
- Is the `864` family worth revisiting only after a better seeded cycle search is available?

## Exploration 42

### Strategy
Start the orientation sweep for the product-864 family with five explicit tuples from the `3 binary + 1 quaternary + 3 ternary` pattern, using deeper SMT-screen budgets (`20000` cycles) to test whether search order reveals survivor-bearing behavior as it did for `n = 6`.

### Outcome
STALLED

### Failure Constraint
No orientation in this first batch yields a witness. Four orientations show no survivors at all within `20000` screened cycles; the fifth yields many survivor cycles, but all fail immediately at the propagation stage.

### What This Rules Out
This rules out the hope that the product-864 family contains an immediate easy witness across all natural orientations. Any positive result in this family, if it exists, is now clearly orientation-sensitive and nontrivial.

### Surviving Structure
- Orientations with the `4` earlier in the tuple can be completely survivor-free over substantial screened prefixes.
- The orientation `(3,3,3,2,2,2,4)` is qualitatively different: it produces many survivors, but the current completion pipeline kills them at root propagation.
- This is similar to the `n = 6` phenomenon where some classes had abundant screened survivors that all died before deep completion.

### Reformulations
- Orientation sensitivity is real at product 864 too, but it currently manifests as “survivor-free versus root-failure survivors,” not yet as a witness.

LOAD-BEARING ASSESSMENT: Moderate. This is the first meaningful negative evidence against the naive `32·3^(n-4)` extrapolation at `n = 7`, while still leaving room for a more subtle witness in the same family.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 3,2,2,2,4,3,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 85.396s`.
- `python3 scripts/p2_smt_completion.py 3,3,4,2,2,2,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 74.837s`.
- `python3 scripts/p2_smt_completion.py 3,3,2,2,2,4,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 69.572s`.
- `python3 scripts/p2_smt_completion.py 3,4,2,2,2,3,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 88.311s`.
- `python3 scripts/p2_smt_completion.py 3,3,3,2,2,2,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 50 survivor cycles within 15298 screened cycles in 79.020s`, with every attempted survivor failing at propagation.

STRUCTURAL RESULTS:
- None definitive for product `864`.

TOOLS:
- The SMT completion script is again separating survivor-free orientations from root-failure survivor orientations.

REPRESENTATIONS:
- Product-864 orientation split, first batch:
  - Survivor-free orientations so far: `(3,2,2,2,4,3,3)`, `(3,3,4,2,2,2,3)`, `(3,3,2,2,2,4,3)`, `(3,4,2,2,2,3,3)`
  - Root-failure survivor orientation so far: `(3,3,3,2,2,2,4)`

### What Would Unblock This
- Run the remaining explicit orientations and reflections before drawing any stronger conclusion about the 864 family.
- If more orientations behave like `(3,3,3,2,2,2,4)`, inspect whether they all die by the same propagation mechanism.

### Key Parameters
- Screen budget per orientation: `max_cycles = 20000`, `screen_time_limit = 180s`.
- First batch size: `5` orientations.

### Open Questions
- Do any of the remaining explicit orientations produce deeper-than-root survivor behavior, or even a witness?
- Is the survivor behavior of `(3,3,3,2,2,2,4)` special, or generic once the `4` is pushed to an end?
- Should product 864 remain a live side-search, or return behind product 576 if the second batch is also negative?

## Exploration 43

### Strategy
Finish the explicit orientation sweep of the product-864 family by testing the remaining five tuples and reflections, again with deeper SMT-screen budgets (`20000` cycles), to determine whether the `3 binary + 1 quaternary + 3 ternary` pattern really produces an `n = 7` witness.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The product-864 family is not a dead extrapolation: at least one explicit orientation works.
- At the same time, witness-bearing behavior is highly orientation-sensitive within the family; several orientations are still survivor-free or root-failure-only over substantial screened prefixes.

### Surviving Structure
- The orientation `(3,2,2,2,3,4,3)` admits a full verified product-864 construction for `n = 7`.
- Other orientations remain much less favorable:
  - `(4,2,2,2,3,3,3)` is survivor-free through `17252` screened cycles in `180s`.
  - `(3,4,3,2,2,2,3)` is survivor-free through `20000` screened cycles.
  - `(3,2,2,2,3,3,4)` yields no survivors in `9449` screened cycles over the full `180s` budget.
  - `(4,3,3,2,2,2,3)` yields survivors, but the first two both die at propagation.

### Reformulations
- The `32·3^(n-4)` pattern survives at `n = 7`, but only in a sharply orientation-sensitive way. The right lesson is not “the pattern fails” but “orientation must be treated as part of the search space, not quotient out too early.”

LOAD-BEARING ASSESSMENT: High. This produces the first explicit `n = 7` witness and materially changes the global state from “lower bound only” to “nontrivial upper and lower bounds with a concrete construction.”

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 4,2,2,2,3,3,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 17252 screened cycles in 180.000s`.
- `python3 scripts/p2_smt_completion.py 3,2,2,2,3,4,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` finds `valid system with 1 recurrent cycle(s)` at screened cycle `2585` after trying `5` survivor cycles, in `12.001s`.
- `python3 scripts/p2_smt_completion.py 3,4,3,2,2,2,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 107.104s`.
- `python3 scripts/p2_smt_completion.py 3,2,2,2,3,3,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 9449 screened cycles in 180.000s`.
- `python3 scripts/p2_smt_completion.py 4,3,3,2,2,2,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 2 survivor cycles within 20001 screened cycles in 136.734s`, with both attempted survivors failing at propagation.

STRUCTURAL RESULTS:
- Product 864 is feasible for `n = 7`.
- Therefore `M_7 <= 864`.
- Combined with the established lower bound, the current exact bracket is `576 <= M_7 <= 864`.

TOOLS:
- No new tools; this is a decisive use of the SMT completion pipeline already in the repository.

REPRESENTATIONS:
- Product-864 orientation split, full sweep so far:
  - Witness-bearing orientation: `(3,2,2,2,3,4,3)`
  - Root-failure survivor orientations: `(3,3,3,2,2,2,4)`, `(4,3,3,2,2,2,3)`
  - Survivor-free orientations over substantial screened prefixes: `(3,2,2,2,4,3,3)`, `(3,3,4,2,2,2,3)`, `(3,3,2,2,2,4,3)`, `(3,4,2,2,2,3,3)`, `(4,2,2,2,3,3,3)`, `(3,4,3,2,2,2,3)`, `(3,2,2,2,3,3,4)`

### What Would Unblock This
- Extract and freeze the explicit product-864 witness into code and tests.
- Then probe lower candidate products with the SMT pipeline, especially product `648` and `768`, to tighten the `576 <= M_7 <= 864` gap from above.

### Key Parameters
- Witness orientation: `(3,2,2,2,3,4,3)`.
- Witness found at screened cycle `2585`, after `5` survivor attempts.
- SMT time to witness: `12.001s`.

### Open Questions
- Does product `648` admit a witness, or is the quaternary processor genuinely needed at `n = 7`?
- Is there also a product-768 witness in a simpler orientation than the 864 family?
- Can the extracted 864 witness suggest a seeded search that attacks product 576 or 648 more intelligently?

## Synthesis after exploration 43

The search has entered a new phase again. Product 576 is the first genuine `n = 7` lower-bound wall, but the pattern-guided side search has now supplied a concrete upper bound: `M_7 <= 864`. This is structurally reminiscent of the earlier `n = 5,6` work, where the key step was not uniformly grinding the lower bound forever, but switching to a construction engine once the frontier became expensive. The exact gap is now narrow enough to make targeted upper-bound probes at 648 and 768 more compelling than blind widening of the lower-bound search.

## Exploration 44

### Strategy
Test product `648` directly by sweeping four natural orientations of `(2,2,2,3,3,3,3)` with the SMT pipeline, to see whether the quaternary processor in the product-864 witness is actually unnecessary at `n = 7`.

### Outcome
STALLED

### Failure Constraint
All four tested orientations are survivor-free through `20000` screened cycles. The current evidence does not reach SMT completion at all.

### What This Rules Out
This rules out the simplest form of the “no quaternary processor needed at `n = 7`” hope. If product `648` is feasible, its witness is not surfacing quickly under the current orientation-sensitive screen.

### Surviving Structure
- No tested orientation of `(2,2,2,3,3,3,3)` yields even a screened survivor in the first `20000` cycles.
- This is negative evidence, not an impossibility proof, but it strengthens the suspicion that the 4-state processor is doing genuine structural work in the known `n = 7` witness.

### Reformulations
- None new. This is a construction-side negative probe rather than a new representation.

LOAD-BEARING ASSESSMENT: Moderate. It does not settle product 648, but it materially weakens the most obvious candidate for improving the `n = 7` upper bound.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 2,2,2,3,3,3,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20001 screened cycles in 85.388s`.
- `python3 scripts/p2_smt_completion.py 3,2,2,2,3,3,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 53.253s`.
- `python3 scripts/p2_smt_completion.py 3,3,2,2,2,3,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 65.015s`.
- `python3 scripts/p2_smt_completion.py 3,3,3,2,2,2,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 97.046s`.

STRUCTURAL RESULTS:
- None definitive for product `648`.

TOOLS:
- No new tools; this is a negative use of the existing SMT screen.

REPRESENTATIONS:
- Product-648 orientation sweep so far: no screened survivors in four natural orientations.

### What Would Unblock This
- Probe product `768` next, since it is the next natural structured family below the current upper bound that still includes quaternary states.
- If product `768` also shows no quick witness, the best upper-bound progress may require more structurally seeded cycle generation rather than blind orientation sweeps.

### Key Parameters
- Product-648 orientations tested: `(2,2,2,3,3,3,3)`, `(3,2,2,2,3,3,3)`, `(3,3,2,2,2,3,3)`, `(3,3,3,2,2,2,3)`.
- All four were survivor-free through `20000` screened cycles.

### Open Questions
- Does product `768` admit a witness that product `648` does not?
- Is the 4-state processor truly necessary at `n = 7`, or just necessary for the current search order?
- Should the next upper-bound probes stay pattern-driven, or switch to a broader SMT scan of intermediate products?

## Exploration 45

### Strategy
Probe the next structured upper-bound family with two quaternary processors by testing several orientations around `(2,2,2,4,3,3,4)` and `(3,2,2,2,4,3,4)` with the SMT pipeline.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The negative product-648 sweep from exploration 44 is not just an artifact of “all structured upper-bound probes fail”; a nearby larger two-quaternary family does work.

### Surviving Structure
- The orientation `(3,2,2,2,4,3,4)` admits a full verified construction, but its true product is `1152`, not `768`.
- Several nearby two-quaternary orientations are still survivor-free over substantial screened prefixes, so orientation sensitivity remains strong.

### Reformulations
- The `n = 7` upper-bound search is clearly pattern-sensitive and still productive, but this exploration does not improve the exact `M_7` bracket because the witness sits above the existing product-864 upper bound.

LOAD-BEARING ASSESSMENT: Moderate. This gives another explicit `n = 7` witness and validates the strategy of probing intermediate structured families, but it does not tighten the exact bracket.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 2,2,2,4,3,3,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 112.679s`.
- `python3 scripts/p2_smt_completion.py 4,2,2,2,4,3,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20001 screened cycles in 79.763s`.
- `python3 scripts/p2_smt_completion.py 4,3,3,2,2,2,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 7269 screened cycles in 180.000s`.
- `python3 scripts/p2_smt_completion.py 3,2,2,2,4,3,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` finds `valid system with 1 recurrent cycle(s)` at screened cycle `493` after trying `1` survivor cycle, in `5.525s`.

STRUCTURAL RESULTS:
- Product `1152` is feasible for `n = 7`.
- The exact bracket remains `576 <= M_7 <= 864`.

TOOLS:
- No new tools; this is another successful use of the SMT completion pipeline.

REPRESENTATIONS:
- Two-quaternary orientation split so far:
  - Witness-bearing orientation: `(3,2,2,2,4,3,4)`
  - Survivor-free orientations over substantial screened prefixes: `(2,2,2,4,3,3,4)`, `(4,2,2,2,4,3,3)`, `(4,3,3,2,2,2,4)`

### What Would Unblock This
- Extract and freeze the explicit product-1152 witness.
- Then decide whether the better next upper-bound probe is product `720`, another intermediate family, or a return to the open lower-bound frontier at 576.

### Key Parameters
- Witness orientation: `(3,2,2,2,4,3,4)`.
- Witness found at screened cycle `493`, first survivor tried.
- SMT time to witness: `5.525s`.
- Witness product: `1152`.

### Open Questions
- Is there a witness below 864, perhaps at 720 or 768?
- How structurally similar is the 1152 witness to the 864 witness?
- Is it now more effective to tighten the upper bound further, or to attack the clustered product-576 classes with new structural insight from the larger witness?

## Synthesis after exploration 45

The `n = 7` search now has the same shape that made `n = 6` tractable: a hard lower-bound wall and explicit upper-bound constructions. The exact bracket is still `576 <= M_7 <= 864`, because the new two-quaternary witness sits at product `1152`, not below the existing upper bound. Still, the search is no longer blind. Product 648 looks negative under broad orientation sweeps, product 864 is feasible, product 1152 is also feasible, and product 576 is the first serious clustered lower-bound wall. That is enough structure to guide the next upper-bound probes intelligently.

## Exploration 46 (probe)

### Strategy
Audit the newly extracted two-quaternary witness against the verifier and test suite to confirm its true product and correct the `n = 7` bracket if necessary.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- The witness orientation `(3,2,2,2,4,3,4)` has product `1152`, not `768`.
- Therefore the current exact `n = 7` bracket remains `576 <= M_7 <= 864`.

TOOLS:
- `python3 -m unittest discover -s tests -v` caught the arithmetic mismatch immediately when the witness was first frozen under the wrong name.

## Exploration 47

### Strategy
Finish the product-720 upper-bound probe systematically by enumerating all dihedral classes of the only admissible multiset `(2,2,2,2,3,3,5)` and screening every remaining class with the SMT pipeline.

### Outcome
SUCCEEDED

### Failure Constraint
All nine product-720 dihedral classes are survivor-free through the current SMT-screen budget. No run reaches SMT completion at all.

### What This Rules Out
- The earlier negative 720 batch was not just a bad orientation choice. At the present search depth, the full product-720 family behaves uniformly negatively.

### Surviving Structure
- Product 720 remains only a negative screen, not an impossibility proof.
- The negative signal is nevertheless much stronger than for product 648, because the sweep now covers the entire dihedral family rather than a hand-picked subset.

### Reformulations
- For `n = 7`, product `720` has exactly one nondecreasing multiset, `(2,2,2,2,3,3,5)`, splitting into nine dihedral classes.

LOAD-BEARING ASSESSMENT: High. This turns product 720 from an anecdotal side probe into a complete orientation sweep at fixed search depth, and it sharpens the remaining upper-bound search space substantially.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Earlier batch, all survivor-free through `20000` screened cycles:
  - `python3 scripts/p2_smt_completion.py 3,2,2,2,3,2,5 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 115.251s`.
  - `python3 scripts/p2_smt_completion.py 5,2,2,2,3,2,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 118.716s`.
  - `python3 scripts/p2_smt_completion.py 3,2,2,2,5,2,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 87.599s`.
  - `python3 scripts/p2_smt_completion.py 3,3,2,2,2,2,5 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20001 screened cycles in 116.029s`.
- Remaining canonical classes, all survivor-free:
  - `python3 scripts/p2_smt_completion.py 2,2,2,2,3,5,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 174.338s`.
  - `python3 scripts/p2_smt_completion.py 2,2,3,2,2,3,5 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 18380 screened cycles in 180.000s`.
  - `python3 scripts/p2_smt_completion.py 2,2,3,2,3,2,5 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20001 screened cycles in 78.715s`.
  - `python3 scripts/p2_smt_completion.py 2,2,3,2,5,2,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 18466 screened cycles in 180.001s`.
  - `python3 scripts/p2_smt_completion.py 2,2,3,3,2,2,5 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 90.414s`.

STRUCTURAL RESULTS:
- Every tested product-720 orientation is survivor-free through the current depth.
- The exact bracket is still `576 <= M_7 <= 864`.

REPRESENTATIONS:
- Product-720 dihedral classes, all screened negatively: `(2,2,2,2,3,3,5)`, `(2,2,2,2,3,5,3)`, `(2,2,2,3,2,3,5)`, `(2,2,2,3,2,5,3)`, `(2,2,2,3,3,2,5)`, `(2,2,3,2,2,3,5)`, `(2,2,3,2,3,2,5)`, `(2,2,3,2,5,2,3)`, `(2,2,3,3,2,2,5)`.

### What Would Unblock This
- Reduce the entire interval `(576,864)` arithmetically to the remaining attainable products, then probe the smallest live families systematically.
- In particular, product `768` is now the only substantial untested upper-bound family below `864`.

### Key Parameters
- Product-720 multiset: `(2,2,2,2,3,3,5)`.
- Dihedral classes screened: `9`.
- Screen budget per class: `180s`, `20000` cycles, `50` survivors max.

### Open Questions
- Is product `768` the first upper-bound family below `864` with any screened survivor?
- Is the lack of 720 survivors signaling a genuine structural gap, or only a search-order gap?

## Exploration 48

### Strategy
Enumerate every attainable product between the lower and upper bounds, discard the ones killed immediately by the four-consecutive-binary obstruction, and screen the singleton admissible classes at products `640`, `672`, and `800`.

### Outcome
SUCCEEDED

### Failure Constraint
- Product `640` and product `800` are survivor-free through `20000` screened cycles.
- Product `672` is survivor-free through `6678` screened cycles in the full `180s` budget.

### What This Rules Out
- There is no obvious easy witness below `864` hiding in the one-class products `640`, `672`, or `800`.
- Products `704` and `832` are not worth explicit cycle screening: their only multisets have six binary processors and therefore contain four consecutive 2-state processors immediately.

### Surviving Structure
- The only attainable products in the interval `576 < p < 864` are
  `640, 648, 672, 704, 720, 768, 800, 832`.
- After applying the binary obstruction and the current screened negatives:
  - `648` has a full negative orientation sweep at current depth.
  - `704` and `832` are structurally dead.
  - `640`, `672`, `720`, and `800` are now all negative at current SMT-screen depth.
  - Product `768` is the only substantial untested upper-bound family below `864`.

### Reformulations
- The upper-bound search between `576` and `864` has collapsed from “many integers” to one live arithmetic family, product `768`, plus the unresolved lower-bound wall at product `576`.

LOAD-BEARING ASSESSMENT: High. This converts the `n = 7` upper-bound gap into a very small structured checklist and cleanly identifies where the next computational effort belongs.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 2,2,2,4,2,2,5 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 43.919s`.
- `python3 scripts/p2_smt_completion.py 2,2,2,3,2,2,7 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 6678 screened cycles in 180.000s`.
- `python3 scripts/p2_smt_completion.py 2,2,2,5,2,2,5 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 59.802s`.

STRUCTURAL RESULTS:
- Attainable products in `576 < p < 864`: `640, 648, 672, 704, 720, 768, 800, 832`.
- Immediate obstruction products: `704`, `832`.
- Only live upper-bound family below `864` not yet substantially screened: `768`.

REPRESENTATIONS:
- Unique admissible classes at the singleton products screened here:
  - product `640`: `(2,2,2,4,2,2,5)`
  - product `672`: `(2,2,2,3,2,2,7)`
  - product `800`: `(2,2,2,5,2,2,5)`

### What Would Unblock This
- Run the admissible product-768 classes with the same SMT-screen budget.
- In parallel or afterward, decide whether product `576` should finally get full SMT-completion runs rather than more pure screening.

### Key Parameters
- Product interval reduced: `576 < p < 864`.
- Attainable products in that interval: `8`.
- Newly screened singleton admissible classes: `3`.

### Open Questions
- Does any product-768 class produce a survivor or a witness?
- If product `768` is also negative at current depth, is the best next move deeper SMT on `576`, or a stronger invariant for proving impossibility there?

## Exploration 49

### Strategy
Finish the remaining upper-bound gap below `864` by screening every admissible dihedral class at product `768` with the SMT pipeline.

### Outcome
SUCCEEDED

### Failure Constraint
- Eight admissible product-768 classes are survivor-free through `20000` screened cycles.
- The remaining high-arity class `(2,2,2,3,2,2,8)` does not even emit a first screened cycle within the full `180s` budget.

### What This Rules Out
- There is no quick product-768 witness hiding in the admissible class list.
- The current `n = 7` upper-bound gap is no longer “product 768 has not been looked at”; it has now been screened systematically, and negatively, across all admissible classes.

### Surviving Structure
- Product `768` remains open in principle because the current evidence is screening-based, not exhaustive.
- Still, the screened picture below `864` is now uniformly negative: every attainable product in `(576,864)` is either structurally dead or survivor-free at current depth.

### Reformulations
- Product `768` is the last substantial admissible family below `864`, and it does not behave like an easy missing witness.

LOAD-BEARING ASSESSMENT: High. This completes the systematic first-pass upper-bound scan of every attainable product below `864`.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_smt_completion.py 2,2,2,3,2,2,8 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 0 screened cycles in 180.000s`.
- `python3 scripts/p2_smt_completion.py 2,2,2,4,2,2,6 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20001 screened cycles in 77.996s`.
- `python3 scripts/p2_smt_completion.py 2,2,2,3,2,4,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20001 screened cycles in 108.954s`.
- `python3 scripts/p2_smt_completion.py 2,2,2,3,4,2,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 145.023s`.
- `python3 scripts/p2_smt_completion.py 2,2,2,4,2,3,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20001 screened cycles in 66.442s`.
- `python3 scripts/p2_smt_completion.py 2,2,3,2,2,4,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20001 screened cycles in 121.132s`.
- `python3 scripts/p2_smt_completion.py 2,2,3,2,4,2,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 151.350s`.
- `python3 scripts/p2_smt_completion.py 2,2,3,4,2,2,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 129.967s`.
- `python3 scripts/p2_smt_completion.py 2,2,4,2,3,2,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 20000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 20000 screened cycles in 99.531s`.

STRUCTURAL RESULTS:
- Every admissible product-768 class is negative at the current SMT-screen depth.
- The exact bracket remains `576 <= M_7 <= 864`.

REPRESENTATIONS:
- Admissible product-768 classes screened: `(2,2,2,3,2,2,8)`, `(2,2,2,4,2,2,6)`, `(2,2,2,3,2,4,4)`, `(2,2,2,3,4,2,4)`, `(2,2,2,4,2,3,4)`, `(2,2,3,2,2,4,4)`, `(2,2,3,2,4,2,4)`, `(2,2,3,4,2,2,4)`, `(2,2,4,2,3,2,4)`.

### What Would Unblock This
- A stronger seeded search than raw cycle enumeration.
- Or a direct return to the lower-bound wall at product `576`, now that the upper-bound side below `864` has been broadly screened.

### Key Parameters
- Product-768 admissible dihedral classes: `9`.
- Screen budget per class: `180s`, `20000` cycles, `50` survivors max.

### Open Questions
- Is product `864` actually the first feasible `n = 7` product, or just the first one the current search can see?
- Can a seeded cycle search transfer known witness dynamics into smaller state-count vectors?

## Exploration 50

### Strategy
Promote the witness-seeding idea into a reusable mover-sequence search: extract the recurrent mover sequence from a known witness, solve directly for a locally consistent good cycle with that sequence on a smaller target vector, and only then attempt SMT completion.

### Outcome
SUCCEEDED

### Failure Constraint
- For both known `n = 7` witness sequences (length `52` at product `864`, length `41` at product `1152`), the seeded cycle solver is UNSAT on every open product-576 class tested.
- The same is true on every admissible product-768 class tested.

### What This Rules Out
- The failure of products `576` and `768` under the current search is not just “the DFS has not rediscovered the right cycle yet,” at least not for the two known witness dynamics.
- The known `n = 7` constructions do not transplant verbatim into the smaller products even at the level of locally consistent good cycles.

### Surviving Structure
- This is not an impossibility proof for product `576` or `768`; it only rules out two concrete mover-sequence templates.
- Still, the result is structurally meaningful: any smaller witness must use recurrent dynamics genuinely different from both known `n = 7` constructions.

### Reformulations
- Fixed-mover-sequence cycle synthesis is now a first-class search representation in the repo. Instead of enumerating cycles blindly, we can ask whether a target state-count vector even admits the recurrent processor schedule of a known witness.

LOAD-BEARING ASSESSMENT: High. This adds a new search representation and immediately explains part of the negative behavior below `864`.

### Concrete Artifacts
TOOLS:
- New script: `scripts/p2_seeded_cycle_search.py`, which
  1. extracts the unique recurrent mover sequence from a witness,
  2. synthesizes a locally consistent good cycle with that sequence via Z3, and
  3. optionally hands the cycle to `scripts/p2_smt_completion.py` for full completion.

COMPUTED EXAMPLES:
- Positive smoke check:
  - `python3 scripts/p2_seeded_cycle_search.py 3,2,2,2,3,4,3 --witness n7-864 --skip-completion --cycle-timeout-ms 5000` reports `found a seeded good cycle of length 52` in `1.977s`.
- Negative representative checks:
  - `python3 scripts/p2_seeded_cycle_search.py 2,2,3,2,2,3,4 --witness n7-864 --skip-completion --cycle-timeout-ms 5000` reports `no locally consistent good cycle exists for this mover sequence` in `1.870s`.
  - `python3 scripts/p2_seeded_cycle_search.py 2,2,4,2,3,2,4 --witness n7-1152 --skip-completion --cycle-timeout-ms 5000` reports `no locally consistent good cycle exists for this mover sequence` in `1.160s`.
- Prototype full sweeps with the seeded solver show:
  - every open product-576 class is UNSAT for the length-41 mover sequence from the product-1152 witness,
  - every open product-576 class is UNSAT for the length-52 mover sequence from the product-864 witness,
  - every admissible product-768 class is UNSAT for both of those mover sequences.

STRUCTURAL RESULTS:
- Known `n = 7` witness dynamics are incompatible with all currently open product-576 classes.
- Known `n = 7` witness dynamics are also incompatible with all admissible product-768 classes.

REPRESENTATIONS:
- New seeded representation: “mover-sequence first, state assignment second, completion third.”

### What Would Unblock This
- Either a richer seed family, such as perturbed mover sequences or multiple witness templates,
- or a direct invariant on why clustered product-576 classes cannot realize any fair recurrent dynamics.

### Key Parameters
- Seeded witness sequences used: lengths `52` and `41`.
- Negative target families covered: all five open product-576 classes; all nine admissible product-768 classes.

### Open Questions
- Which mover-sequence features distinguish the known `n = 7` witnesses from any hypothetical smaller witness?
- Can the seeded solver be relaxed from an exact mover sequence to a local-pattern template that still prunes effectively?

## Exploration 51

### Strategy
Use the new seeded-cycle solver to finish the whole sub-864 picture: test the remaining admissible classes at products `640`, `672`, `720`, and `800` against both known `n = 7` witness mover sequences.

### Outcome
SUCCEEDED

### Failure Constraint
- Every tested class is UNSAT for the length-52 mover sequence from the product-864 witness.
- Every tested class is also UNSAT for the length-41 mover sequence from the product-1152 witness.

### What This Rules Out
- The entire admissible sub-864 region now fails both known `n = 7` witness dynamics.
- Any hypothetical witness below `864` must therefore use recurrent dynamics different from both currently known `n = 7` constructions.

### Surviving Structure
- This still leaves open the possibility of a smaller witness with a genuinely new mover sequence.
- But the search is no longer missing an easy transfer from the known constructions: that avenue is now closed across the entire sub-864 interval.

### Reformulations
- The upper-bound gap is now constrained in two orthogonal ways:
  1. raw SMT cycle screening is negative across all attainable products below `864`,
  2. seeded cycle synthesis from both known `n = 7` witnesses is UNSAT across all admissible products below `864`.

LOAD-BEARING ASSESSMENT: High. This upgrades the sub-864 evidence from “screened negative” to “screened negative and dynamically incompatible with all known witness templates.”

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 - <<'PY' ... PY` using `solve_good_cycle_from_movers` shows that each of
  - `(2,2,2,4,2,2,5)`,
  - `(2,2,2,3,2,2,7)`,
  - all nine product-720 classes
    `(2,2,2,2,3,3,5)`, `(2,2,2,2,3,5,3)`, `(2,2,2,3,2,3,5)`,
    `(2,2,2,3,2,5,3)`, `(2,2,2,3,3,2,5)`, `(2,2,3,2,2,3,5)`,
    `(2,2,3,2,3,2,5)`, `(2,2,3,2,5,2,3)`, `(2,2,3,3,2,2,5)`,
  - and `(2,2,2,5,2,2,5)`
  are UNSAT for both witness mover sequences.

STRUCTURAL RESULTS:
- Every admissible state-count class below product `864` now fails both known witness mover sequences.
- Combined with explorations 49 and 50, this means the entire interval `576 < p < 864` has been searched in two qualitatively different ways without finding a witness.

REPRESENTATIONS:
- “Known witness dynamics do not transplant below 864” is now a repo-level invariant candidate, not just a local observation at 576 and 768.

### What Would Unblock This
- Either discover a genuinely new mover-sequence family for `n = 7`,
- or prove that no such family can exist below `864`.

### Key Parameters
- Additional target classes covered here: product `640` singleton, product `672` singleton, all `9` product-720 classes, product `800` singleton.
- Witness mover sequences used: lengths `52` and `41`.

### Open Questions
- Is there a recognizable combinatorial obstruction behind the universal seeded UNSAT behavior below `864`?
- Can the seeded solver be generalized from exact mover sequences to motif counts or wave-pattern constraints?

## Exploration 52

### Strategy
Push the remaining three moderate product-576 holdouts from `180s` to `600s` to see whether the clustered wall is localized to only the hardest two classes or uniform across all five open classes.

### Outcome
SUCCEEDED

### Failure Constraint
All three classes remain survivor-free through the full `600s` budget.

### What This Rules Out
- The clustered product-576 wall is not concentrated in only `(2,2,3,2,2,3,4)` and `(2,2,2,3,2,4,3)`.
- There is no remaining moderate product-576 class that looks close to immediate closure under the current screen.

### Surviving Structure
- Every open product-576 class now has a `600s` survivor-free run.
- Product `576` still is not ruled out, but the frontier now looks uniformly hard rather than mixed.

### Reformulations
- The `n = 7` lower-bound picture at product `576` is now: five open clustered classes, all of them survivor-free through a long budget, with no class obviously easier than the rest.

LOAD-BEARING ASSESSMENT: High. This turns product `576` from “a wall with a couple of hard examples” into “a uniformly hard wall across the entire remaining frontier.”

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,2,6 --time-limit 600 --max-cycles 10000000` reports `screened=274086 survivors=0 elapsed=600.000s`.
- `python3 scripts/p2_cycle_screen.py 2,2,3,3,2,2,4 --time-limit 600 --max-cycles 10000000` reports `screened=175174 survivors=0 elapsed=600.001s`.
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,3,2,4 --time-limit 600 --max-cycles 10000000` reports `screened=158174 survivors=0 elapsed=600.000s`.

STRUCTURAL RESULTS:
- Combined with earlier `600s` runs on `(2,2,3,2,2,3,4)` and `(2,2,2,3,2,4,3)`, all five open product-576 classes are now survivor-free through `600s`.

REPRESENTATIONS:
- Full `600s` open product-576 roster:
  - `(2,2,2,3,2,2,6)` with `274086` screened cycles,
  - `(2,2,3,3,2,2,4)` with `175174`,
  - `(2,2,2,3,3,2,4)` with `158174`,
  - `(2,2,3,2,2,3,4)` with `270674`,
  - `(2,2,2,3,2,4,3)` with `169575`.

### What Would Unblock This
- A structural invariant that kills clustered classes without waiting for cycle exhaustion,
- or a much stronger pruning representation than the current cycle screen.

### Key Parameters
- Newly extended classes: `3`.
- Time budget per class: `600s`.

### Open Questions
- Is product `576` impossible, or just beyond the present cycle-screen regime?
- What hidden structure separates the clustered product-576 classes from the witness-bearing classes at higher product?

## Exploration 53 (probe)

### Strategy
Prototype a bounded-length SAT search that quantifies over mover sequences directly: ask whether any locally consistent good cycle of exact length `L` exists for a target state vector, without relying on DFS cycle enumeration.

### Outcome
PARTIAL

### Failure Constraint
- The prototype is too weak in its current form to become the new proof engine.
- It times out even on known positive cases, including:
  - product-864 witness class `(3,2,2,2,3,4,3)` at length `52`,
  - product-96 witness class `(2,2,2,3,4)` at length `18`.

### What This Rules Out
- In its current unsymmetrized form, direct bounded-length SAT is not yet competitive with the seeded fixed-mover search or the existing DFS screen.

### Surviving Structure
- The representation is still conceptually correct and may become useful with stronger symmetry breaking or more aggressive context abstraction.
- Right now it is exploratory, not load-bearing.

### Reformulations
- New exploratory script: `scripts/p2_bounded_cycle_sat.py`, which searches for any locally consistent good cycle of a fixed exact length `L` and can optionally hand a found cycle to the SMT completer.

LOAD-BEARING ASSESSMENT: Low for now. This is a plausible next representation, but the current implementation does not yet solve the lengths that matter.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_bounded_cycle_sat.py 3,2,2,2,3,4,3 --length 52 --timeout-ms 30000` reports `solver returned unknown: timeout` after `31.873s`.
- `python3 scripts/p2_bounded_cycle_sat.py 2,2,2,3,4 --length 18 --timeout-ms 5000` reports `solver returned unknown: timeout` after `5.190s`.

STRUCTURAL RESULTS:
- None definitive yet beyond “this representation needs substantially more symmetry reduction.”

### What Would Unblock This
- State-introduction symmetry breaking inside the SAT encoding.
- Additional constraints on mover counts or local-context reuse.

### Key Parameters
- Positive calibrations attempted: lengths `18` and `52`.

### Open Questions
- Can bounded-length SAT be repaired enough to certify UNSAT for moderate lengths on product-576 classes?
- Is there a compact way to encode state-introduction order in Z3 that materially cuts the search space?

## Exploration 54

### Strategy
Take the user-suggested “hail mary” literally: rerun all five open product-576 classes with an `1800s` screen budget, to test whether the wall behaves like the earlier `n = 6`, product-240 frontier that only closed after a longer push.

### Outcome
SUCCEEDED

### Failure Constraint
- Three classes remain survivor-free through the full `1800s` budget.
- But two classes now close exhaustively before the time limit.

### What This Rules Out
- Product `576` is no longer a five-class open frontier.
- The classes `(2,2,2,3,3,2,4)` and `(2,2,3,3,2,2,4)` are now fully ruled out.

### Surviving Structure
- Product `576` is still open only in the three classes
  `(2,2,2,3,2,2,6)`, `(2,2,3,2,2,3,4)`, and `(2,2,2,3,2,4,3)`.
- The first long-budget batch confirms that more time can genuinely close clustered classes; the wall is not purely illusory.

### Reformulations
- The product-576 problem has now split again:
  - two clustered classes turned out to be in brute-force range after all,
  - three clustered classes remain beyond the current long-budget screen.

LOAD-BEARING ASSESSMENT: High. This is the first real lower-bound progress at `n = 7` since the frontier hit 576.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Exhaustively closed under the `1800s` budget:
  - `python3 scripts/p2_cycle_screen.py 2,2,2,3,3,2,4 --time-limit 1800 --max-cycles 50000000` reports `screened=160869 survivors=0 elapsed=694.017s`.
  - `python3 scripts/p2_cycle_screen.py 2,2,3,3,2,2,4 --time-limit 1800 --max-cycles 50000000` reports `screened=194764 survivors=0 elapsed=760.099s`.
- Still open after the full `1800s` budget:
  - `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,2,6 --time-limit 1800 --max-cycles 50000000` reports `screened=634826 survivors=0 elapsed=1800.001s`.
  - `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,3,4 --time-limit 1800 --max-cycles 50000000` reports `screened=423533 survivors=0 elapsed=1800.000s`.
  - `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,4,3 --time-limit 1800 --max-cycles 50000000` reports `screened=271654 survivors=0 elapsed=1800.000s`.

STRUCTURAL RESULTS:
- Newly eliminated product-576 classes:
  - `(2,2,2,3,3,2,4)`
  - `(2,2,3,3,2,2,4)`
- Remaining open product-576 classes:
  - `(2,2,2,3,2,2,6)`
  - `(2,2,3,2,2,3,4)`
  - `(2,2,2,3,2,4,3)`

### What Would Unblock This
- Push the three surviving classes longer, since the first `1800s` batch did in fact convert two “walls” into proofs.
- If those three still do not close, the search should pivot to the `32·3^(n-4)` construction program.

### Key Parameters
- Open classes entering the batch: `5`.
- Classes eliminated by the batch: `2`.
- Classes still open afterward: `3`.

### Open Questions
- Are the three survivors merely farther from exhaustion, or qualitatively different?
- Does the remaining product-576 frontier now hide the actual minimum, or is it still a lower-bound wall below the true value?

## Exploration 55

### Strategy
Since exploration 54 actually eliminated two classes, keep going on the three survivors with a second longer batch at `3600s`, to determine whether the remaining frontier is still in brute-force range or truly qualitatively different.

### Outcome
SUCCEEDED

### Failure Constraint
All three surviving product-576 classes remain survivor-free through the full `3600s` budget.

### What This Rules Out
- The three remaining product-576 classes are not just slightly farther away than the two classes eliminated in exploration 54.
- A simple “double the time and finish the frontier” story is no longer credible.

### Surviving Structure
- Product `576` is still open in exactly three classes:
  - `(2,2,2,3,2,2,6)`
  - `(2,2,3,2,2,3,4)`
  - `(2,2,2,3,2,4,3)`
- None of them produced even a single survivor cycle in one hour.

### Reformulations
- The product-576 frontier has now cleanly separated into:
  - two classes that were brute-force eliminable after the `1800s` push,
  - three classes that survive even a `3600s` push with zero survivors.

LOAD-BEARING ASSESSMENT: High. This is the point where further lower-bound progress stops looking like “more patience” and starts looking like “new invariant required.”

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,2,6 --time-limit 3600 --max-cycles 100000000` reports `screened=1121664 survivors=0 elapsed=3600.001s`.
- `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,3,4 --time-limit 3600 --max-cycles 100000000` reports `screened=722414 survivors=0 elapsed=3600.001s`.
- `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,4,3 --time-limit 3600 --max-cycles 100000000` reports `screened=548934 survivors=0 elapsed=3600.000s`.

STRUCTURAL RESULTS:
- Remaining open product-576 classes after the longer rerun:
  - `(2,2,2,3,2,2,6)`
  - `(2,2,3,2,2,3,4)`
  - `(2,2,2,3,2,4,3)`

### What Would Unblock This
- A structural obstruction for the three surviving clustered classes,
- or a stronger symbolic search than the present cycle screen.

### Key Parameters
- Surviving classes entering the batch: `3`.
- Classes eliminated by the batch: `0`.
- Screen budget per class: `3600s`.

### Open Questions
- Are these three classes genuinely feasible candidates, or just the last artifacts of the current enumeration method?
- Can the phase-2 construction search reveal a pattern that indirectly explains why only these three classes resist elimination?

## Exploration 56

### Strategy
Start phase 2 by testing the hypothesized family `M_n = 32·3^(n-4)` at `n = 8`, i.e. the product-2592 multiset `(2,2,2,4,3,3,3,3)`, across all dihedral classes with the SMT completion pipeline.

### Outcome
SUCCEEDED

### Failure Constraint
- No product-2592 witness appears in the first-pass sweep.
- Across all `19` dihedral classes at the current depth, only one class produces any survivor cycles at all.

### What This Rules Out
- There is no easy `n = 8` extension of the `3 binary + 1 quaternary + rest ternary` pattern that surfaces under the same SMT search regime that found the `n = 6` and `n = 7` witnesses.
- The conjectural formula `M_n = 32·3^(n-4)` does not get immediate computational support from `n = 8`.

### Surviving Structure
- The class `(2,2,3,2,3,4,3,3)` is the only live class at the current search depth:
  - it produced survivor cycles immediately,
  - but none of the first `200` survivor cycles completed to a valid system.
- The other `18` dihedral classes are survivor-free through the current budget.

### Reformulations
- The phase-2 search now has a sharply localized residue: if the product-2592 family works at all, it is not generically easy; the only current construction-side signal comes from one specific class with many incomplete survivor cycles.

LOAD-BEARING ASSESSMENT: Moderate. This does not settle `n = 8`, but it cleanly says that the family is not trivially inductive under the present pipeline.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Representative negative classes:
  - `python3 scripts/p2_smt_completion.py 3,2,2,2,3,4,3,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 10000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 10000 screened cycles in 161.490s`.
  - `python3 scripts/p2_smt_completion.py 3,2,2,2,3,3,4,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 10000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 0 screened cycles in 180.000s`.
  - `python3 scripts/p2_smt_completion.py 2,3,2,3,3,3,2,4 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 10000 --max-survivors 50` reports `no valid SMT completion found among 0 survivor cycles within 10000 screened cycles in 166.922s`.
- Unique live class so far:
  - `python3 scripts/p2_smt_completion.py 2,2,3,2,3,4,3,3 --screen-time-limit 180 --solver-timeout-ms 120000 --max-cycles 10000 --max-survivors 50` finds survivor cycles immediately but no valid system among the first `50` survivors in `100.696s`.
  - `python3 scripts/p2_smt_completion.py 2,2,3,2,3,4,3,3 --screen-time-limit 600 --solver-timeout-ms 120000 --max-cycles 500 --max-survivors 200` finds no valid system among the first `200` survivor cycles in `160.424s`.

STRUCTURAL RESULTS:
- Product-2592 family at `n = 8`: no witness found in a complete first-pass dihedral sweep.
- Surviving class at current depth: `(2,2,3,2,3,4,3,3)`.

REPRESENTATIONS:
- Product-2592 dihedral sweep status:
  - `18` classes survivor-free at current depth,
  - `1` class survivor-bearing but completion-negative through the first `200` survivors.

### What Would Unblock This
- A more targeted completion strategy for the live class `(2,2,3,2,3,4,3,3)`,
- or an explicit inductive construction that bypasses cycle search entirely.

### Key Parameters
- `n = 8` product tested: `2592`.
- Dihedral classes screened: `19`.
- Screen budget per class: `180s`, `10000` cycles, `50` survivors max, plus a follow-up `200`-survivor completion attempt on the live class.

### Open Questions
- Is `(2,2,3,2,3,4,3,3)` a real `n = 8` witness class that just needs deeper completion, or another red herring like the live-but-impossible classes seen elsewhere?
- If the `32·3^(n-4)` family is real, what extra structure is missing from the current search that hides the `n = 8` witness?

## Exploration 57

### Strategy
Add mover-prefix constraints to the good-cycle screen, then benchmark first-mover sharding on the three surviving product-576 classes instead of continuing only monolithic DFS runs.

### Outcome
SUCCEEDED

### Failure Constraint
- Sharding does not by itself close any class immediately.
- But it is decisively faster than the old monolithic regime on every remaining class.

### What This Rules Out
- The remaining product-576 wall is not best attacked by one DFS per class.
- Search-order concentration matters enormously: distributing the budget across disjoint mover prefixes gives much better wall-clock coverage.

### Surviving Structure
- New tooling:
  - `scripts/p2_good_cycle_search.py` and `scripts/p2_cycle_screen.py` now support a fixed initial mover prefix.
  - `scripts/p2_prefix_batch.py` runs many prefix-constrained screens in parallel and aggregates the totals.
- At the `600s` level, first-mover sharding already approaches or exceeds the old `3600s` monolithic totals:
  - `(2,2,2,3,2,4,3)`: `562410` screened in sharded `600s`, versus `548934` in monolithic `3600s`;
  - `(2,2,3,2,2,3,4)`: `664351` screened in sharded `600s`, versus `722414` in monolithic `3600s`;
  - `(2,2,2,3,2,2,6)`: `730606` screened in sharded `600s`, versus `1121664` in monolithic `3600s`.

### Reformulations
- The right unit of work is now a mover-prefix subtree, not an entire class.
- This creates a recursive attack: split a hard class by first mover, then split only the stubborn prefixes by their next mover.

LOAD-BEARING ASSESSMENT: High. This is the first new computational idea that materially changes the `n = 7`, product-576 search frontier.

### Concrete Artifacts
COMPUTED EXAMPLES:
- First benchmark on `(2,2,2,3,2,4,3)`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,4,3 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=308660 survivors=0 elapsed=300.152s`.
  - This should be compared with the old monolithic `300s` count `79080`.
- Full `600s` first-mover batches:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,4,3 --prefix-length 1 --time-limit 600 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=562410 survivors=0 elapsed=600.139s`.
  - `python3 scripts/p2_prefix_batch.py 2,2,3,2,2,3,4 --prefix-length 1 --time-limit 600 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=664351 survivors=0 elapsed=600.175s`.
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,2,6 --prefix-length 1 --time-limit 600 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=730606 survivors=0 elapsed=600.162s`.

STRUCTURAL RESULTS:
- All three surviving product-576 classes remain survivor-free under the new sharded screen.
- The monolithic wall is therefore a search-organization problem, not a signal of nearby survivors.

### What Would Unblock This
- Apply recursive sharding to the easiest surviving class first, to see whether the prefix tree actually collapses.
- If recursive sharding works, use it to drive the product-576 frontier down class by class.

### Key Parameters
- Remaining classes entering the sharded phase: `3`.
- Prefix depth used here: `1`.
- Parallel worker count: `7` on the local `8`-core machine.

### Open Questions
- Does recursive mover-prefix sharding only accelerate screening, or can it completely eliminate the remaining classes?
- Is there a structural reason certain movers dominate the hard prefixes?

## Exploration 58

### Strategy
Use the new prefix-sharded attack to recurse on the class `(2,2,2,3,2,4,3)`, while simultaneously letting the old long monolithic run on `(2,2,3,2,2,3,4)` continue to completion.

### Outcome
SUCCEEDED

### Failure Constraint
- The class `(2,2,2,3,2,4,3)` does not collapse in one first-mover batch; one first-mover prefix survives and must be refined again.
- But recursive refinement does eliminate it completely.

### What This Rules Out
- Product `576` is impossible for both `(2,2,3,2,2,3,4)` and `(2,2,2,3,2,4,3)`.
- The product-576 frontier is no longer three classes wide; only one class survives.

### Surviving Structure
- `(2,2,3,2,2,3,4)` closes exhaustively under the continuing monolithic run.
- `(2,2,2,3,2,4,3)` has the following recursive structure:
  - first-mover batch at `1800s`: prefixes `0,1,2,4` close early; only `3,5,6` remain;
  - targeted rerun of prefixes `3,5,6`: prefixes `3` and `6` also close early;
  - second-mover split under prefix `5`: every child branch is impossible or closes early, so the whole class is dead.

### Reformulations
- Recursive sharding is not just a speedup; it is strong enough to convert a previously open class into a proof.
- The last remaining product-576 difficulty is therefore concentrated entirely in `(2,2,2,3,2,2,6)`.

LOAD-BEARING ASSESSMENT: Very high. This is the first substantive collapse of the “hard clustered residue” after the `3600s` wall.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Monolithic closure:
  - `python3 scripts/p2_cycle_screen.py 2,2,3,2,2,3,4 --time-limit 10800 --max-cycles 200000000 --progress-seconds 300` reports `screened=2213179 survivors=0 elapsed=9536.565s`.
- First-mover batch on `(2,2,2,3,2,4,3)`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,4,3 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports
    - `prefix=4 screened=192931 survivors=0 elapsed=1092.657s`,
    - `prefix=0 screened=151394 survivors=0 elapsed=1330.373s`,
    - `prefix=2 screened=159777 survivors=0 elapsed=1659.426s`,
    - `prefix=1 screened=149808 survivors=0 elapsed=1695.026s`,
    - `prefix=3 screened=198649 survivors=0 elapsed=1800.006s`,
    - `prefix=5 screened=273095 survivors=0 elapsed=1800.000s`,
    - `prefix=6 screened=279421 survivors=0 elapsed=1800.001s`.
- Refinement of the remaining first-mover residue:
  - `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,4,3 --time-limit 3600 --max-cycles 50000000 --mover-prefix 3 --progress-seconds 300` reports `screened=230242 survivors=0 elapsed=1462.079s`.
  - `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,4,3 --time-limit 3600 --max-cycles 50000000 --mover-prefix 6 --progress-seconds 300` reports `screened=443474 survivors=0 elapsed=1830.656s`.
- Final second-mover split under prefix `5`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,4,3 --base-prefix 5 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports
    `total prefixes=7 screened=568390 survivors=0 elapsed=810.339s`,
    with nontrivial child closures
    `prefix=5,4 screened=129635 survivors=0 elapsed=417.807s`,
    `prefix=5,5 screened=183979 survivors=0 elapsed=683.594s`,
    `prefix=5,6 screened=254776 survivors=0 elapsed=810.186s`,
    and the remaining child prefixes impossible immediately.

STRUCTURAL RESULTS:
- Product-576 classes eliminated in this exploration:
  - `(2,2,3,2,2,3,4)`
  - `(2,2,2,3,2,4,3)`
- Product-576 class still open afterward:
  - `(2,2,2,3,2,2,6)`

### What Would Unblock This
- Apply the same recursive sharding to the final remaining class `(2,2,2,3,2,2,6)`.
- If that class does not collapse the same way, extract whatever mover-pattern residue remains and treat it as a candidate invariant.

### Key Parameters
- Open product-576 classes entering this exploration: `3`.
- Open product-576 classes afterward: `1`.

### Open Questions
- Is `(2,2,2,3,2,2,6)` qualitatively different from the two classes just eliminated, or just deeper?
- Does the recursive residue in these classes correlate with the position of the largest-alphabet processor?

## Exploration 59

### Strategy
Attack the last remaining product-576 class `(2,2,2,3,2,2,6)` with the full new toolkit: one very long monolithic run, a first-mover sharded batch, and then second-mover refinements of the heaviest first-mover branches.

### Outcome
PARTIAL

### Failure Constraint
- The class `(2,2,2,3,2,2,6)` is still not closed exactly.
- But the open residue is now much more structured than before.

### What This Rules Out
- Product `576` is impossible for every class except `(2,2,2,3,2,2,6)`.
- The last surviving class has no survivor cycles even under much deeper screening than the old monolithic regime:
  - monolithic `10800s`,
  - sharded first-mover `1800s`,
  - and several sharded second-mover refinements.

### Surviving Structure
- The first-mover batch does not collapse any branch early, but it still screens `3063468` cycles in `1800s`, beating the old monolithic `10800s` total of `2645660`.
- The second-mover refinements reveal a very sparse depth-two residue:
  - under first mover `5`, only second mover `6` survives the full `1800s` budget;
  - under first mover `0`, only second mover `6` survives the full `1800s` budget;
  - under first mover `1`, the surviving second movers are `0` and `2`;
  - under first mover `2`, only second mover `3` survives the full `1800s` budget, while second mover `1` closes just before the limit;
  - under first mover `3`, the surviving second movers are `2`, `3`, and `4`;
  - under first mover `4`, the surviving second movers are `3` and `5`;
  - under first mover `6`, the surviving second movers are `0`, `5`, and `6`.
- So the hard residue is not “everything goes to mover `6`,” but rather “each heavy first-mover branch leaves only one to three second-mover possibilities, often including the `6`-state processor and often aligned with local neighbors.”

### Reformulations
- The final product-576 obstruction is no longer “an open class.”
- It is now a specific recursive mover-pattern residue inside `(2,2,2,3,2,2,6)`, heavily biased toward mover `6` at the second step.

LOAD-BEARING ASSESSMENT: High. This does not close `M_7`, but it materially changes the shape of the last open lower-bound problem.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Long monolithic screen:
  - `python3 scripts/p2_cycle_screen.py 2,2,2,3,2,2,6 --time-limit 10800 --max-cycles 200000000 --progress-seconds 300` reports `screened=2645660 survivors=0 elapsed=10800.000s`.
- First-mover sharded batch:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,2,6 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=3063468 survivors=0 elapsed=1800.078s`,
    with branch totals
    `prefix=0 screened=634204`,
    `prefix=5 screened=655185`,
    `prefix=6 screened=576200`,
    `prefix=2 screened=342974`,
    `prefix=1 screened=295773`,
    `prefix=4 screened=292696`,
    `prefix=3 screened=266436`.
- Second-mover refinement of prefix `5`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,2,6 --base-prefix 5 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=1194590 survivors=0 elapsed=1800.060s`,
    where only `prefix=5,6 screened=754920 survivors=0 elapsed=1800.001s` survives the full budget,
    while `prefix=5,4 screened=439670 survivors=0 elapsed=657.134s` closes and the other child prefixes are impossible immediately.
- Second-mover refinement of prefix `0`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,2,6 --base-prefix 0 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=1208819 survivors=0 elapsed=1800.063s`,
    where only `prefix=0,6 screened=769149 survivors=0 elapsed=1800.000s` survives the full budget,
    while `prefix=0,1 screened=439670 survivors=0 elapsed=592.975s` closes and the other child prefixes are impossible immediately.
- Second-mover refinement of prefix `6`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,2,6 --base-prefix 6 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=1998384 survivors=0 elapsed=1800.084s`,
    where the surviving children are
    `prefix=6,0 screened=702412`,
    `prefix=6,5 screened=719852`,
    `prefix=6,6 screened=576120`,
    and the others are impossible immediately.
- Second-mover refinement of prefix `1`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,2,6 --base-prefix 1 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=802918 survivors=0 elapsed=1800.086s`,
    where the surviving children are
    `prefix=1,0 screened=393836`,
    `prefix=1,2 screened=409082`,
    and the others are impossible immediately.
- Second-mover refinement of prefix `2`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,2,6 --base-prefix 2 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=561518 survivors=0 elapsed=1800.101s`,
    where `prefix=2,3 screened=121848 survivors=0 elapsed=1800.000s` survives the full budget,
    `prefix=2,1 screened=439670 survivors=0 elapsed=1750.446s` closes just before the limit,
    and the others are impossible immediately.
- Second-mover refinement of prefix `3`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,2,6 --base-prefix 3 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=780609 survivors=0 elapsed=1800.094s`,
    where the surviving children are
    `prefix=3,2 screened=332732`,
    `prefix=3,3 screened=175105`,
    `prefix=3,4 screened=272772`,
    and the others are impossible immediately.
- Second-mover refinement of prefix `4`:
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,2,2,6 --base-prefix 4 --prefix-length 1 --time-limit 1800 --max-cycles 50000000 --max-workers 7` reports `total prefixes=7 screened=825913 survivors=0 elapsed=1800.083s`,
    where the surviving children are
    `prefix=4,3 screened=392468`,
    `prefix=4,5 screened=433445`,
    and the others are impossible immediately.

STRUCTURAL RESULTS:
- Final remaining open product-576 class:
  - `(2,2,2,3,2,2,6)`
- Current hard residue inside that class:
  - first-mover branches all survive `1800s`,
  - but every first-mover branch has now been split at depth two and each leaves only one to three surviving second movers.

### What Would Unblock This
- Continue the recursive sharding on the surviving depth-two branches,
- or distill a proof invariant from the observed sparse depth-two residue.

### Key Parameters
- Open product-576 classes entering this exploration: `1`.
- Open product-576 classes afterward: `1`.
- Deepest mover-prefix depth reached: `2`.
- Surviving depth-two branches now isolated: `13`.

### Open Questions
- Does the surviving depth-two residue continue to stay this sparse at depth three and beyond?
- Is there a direct invariant explaining why almost all second-mover branches die immediately in the heavy first-mover prefixes?

## Exploration 60

### Strategy
Resume from exploration 59 by attacking the first unresolved `n = 9` phase-2 target directly: run the conjectural product-7776 family `(2,2,2,4,3,3,3,3,3)` at orientation `16/56` with the full `n9_sweep.py` pipeline, and determine whether the bottleneck is survivor completion or earlier cycle generation.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- Orientation `16/56` is not an easy survivor-bearing case under the current `n = 9` pipeline.
- More generally, for at least one representative hard orientation in the conjectured `32·3^(n-4)` family at `n = 9`, the active bottleneck occurs before the fatal-screen or SMT stages are reached at all.

### Surviving Structure
- Orientation `16/56` in the sweep order is `(2,2,3,3,3,2,3,3,4)`.
- The full `600s` run finishes with `screened=0` and `survivors=0`.
- So the current search does not even emit a first completed good cycle on this orientation within the default budget.

### Reformulations
- For `n = 9`, the right checkpoint unit is an indexed orientation slice, not a monolithic all-orientations sweep. The sweep driver now supports that directly, which makes long append-only progress possible without inventing fake earlier log state.
- This exploration also sharpens the phase-2 diagnosis: the present `n = 9` obstacle is pre-screen good-cycle generation, not SMT completion.

LOAD-BEARING ASSESSMENT: Moderate to high. This does not advance the theorem directly, but it cleanly identifies where the `n = 9` search is stuck and changes the operational representation of the sweep.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/n9_sweep.py --multiset 2,2,2,4,3,3,3,3,3 --start-orientation 16 --end-orientation 16` logs orientation `16/56`, `(2,2,3,3,3,2,3,3,4)`, with `screened=0 survivors=0 elapsed=600.0s dead`.

STRUCTURAL RESULTS:
- None theorem-level yet for `n = 9`; the conjectured product-7776 family remains open.
- Operationally, orientation `16/56` is a pre-screen bottleneck.

TOOLS:
- `scripts/n9_sweep.py` now accepts `--multiset`, `--start-orientation`, `--end-orientation`, `--screen-time-limit`, `--max-cycles`, `--solver-timeout-ms`, and `--max-survivors`, and writes append-only checkpoints to `scripts/n9_sweep_results.txt`.

REPRESENTATIONS:
- Orientation-indexed `n = 9` sweep log in `scripts/n9_sweep_results.txt`.

### What Would Unblock This
- Prefix-sharded good-cycle enumeration or seeded cycle search adapted to `n = 9`, because the current monolithic DFS does not reach the fatal-screen stage on this orientation in `600s`.
- A quick adjacent-orientation probe at `17/56` would show whether orientation `16` is an isolated outlier or the start of a long pre-screen dead zone.

### Key Parameters
- Multiset: `(2,2,2,4,3,3,3,3,3)` (product `7776`).
- Orientation index: `16/56`.
- Actual orientation: `(2,2,3,3,3,2,3,3,4)`.
- Budget: `screen_time_limit = 600s`, `max_cycles = 10_000_000`, `solver_timeout_ms = 300000`, `max_survivors = 20`.

### Open Questions
- Does orientation `17/56` also fail to emit a first screened cycle in `600s`?
- Can the prefix-sharding idea that broke the `n = 7` residue be transplanted directly into the `n = 9` good-cycle search?
- Is there a seeded mover-sequence family for the conjectured `32·3^(n-4)` pattern that bypasses raw DFS at `n = 9`?

## Synthesis after exploration 60

Phase 2 now splits sharply by where the bottleneck occurs. At `n = 8`, the product-2592 family reaches survivor cycles in one class but then fails in completion; at `n = 9`, the first targeted orientation of the conjectured product-7776 family does not even reach a first screened cycle in ten minutes. That means deeper SMT budgets are not the next leverage point for `n = 9`. The natural transfer from the `n = 7` residue is search organization: prefix sharding or seeded cycle synthesis should be tried before spending more time on monolithic orientation sweeps.

## Exploration 61

### Strategy
Test whether the orientation-16 bottleneck is isolated or local by running the adjacent product-7776 orientation `17/56` for the same `n = 9` family `(2,2,2,4,3,3,3,3,3)` with the unchanged `n9_sweep.py` budget.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The pre-screen stall at orientation `16/56` is not a one-off artifact of a single ordering.
- A blind adjacent-orientation rerun is not enough to move the `n = 9` witness search into the fatal-screen or SMT stages.

### Surviving Structure
- Orientation `17/56` in the sweep order is `(2,2,3,3,3,2,3,4,3)`.
- Like orientation `16/56`, it finishes the full `600s` budget with `screened=0` and `survivors=0`.
- So the current orientation block `16-17` is a genuine pre-screen dead zone under the monolithic DFS order.

### Reformulations
- The `n = 9` bottleneck is now localized more sharply: the issue is not just “hard orientation,” but an adjacent orientation cluster that does not emit a first completed good cycle in ten minutes.
- This shifts the best next move away from more sequential sweeps and toward search reorganization, especially prefix sharding or seeded cycle synthesis.

LOAD-BEARING ASSESSMENT: Moderate. This does not produce a new theorem-level obstruction, but it materially strengthens the case that the current `n = 9` search needs a different traversal strategy rather than more of the same.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/n9_sweep.py --multiset 2,2,2,4,3,3,3,3,3 --start-orientation 17 --end-orientation 17` logs orientation `17/56`, `(2,2,3,3,3,2,3,4,3)`, with `screened=0 survivors=0 elapsed=600.0s dead`.

STRUCTURAL RESULTS:
- The adjacent orientation block `16-17` of the conjectured product-7776 family is pre-screen dead at the current budget.

TOOLS:
- No new tools beyond the exploration-60 resume controls in `scripts/n9_sweep.py`.

REPRESENTATIONS:
- Orientation-indexed `n = 9` dead-zone evidence now covers two consecutive sweep indices, `16` and `17`.

### What Would Unblock This
- Apply the existing mover-prefix machinery to `n = 9` good-cycle search, because the current bottleneck is before screening.
- If one more cheap diagnostic is wanted before patching, run orientation `18/56`; if it is also `screened=0`, the local dead zone is at least three orientations wide.

### Key Parameters
- Multiset: `(2,2,2,4,3,3,3,3,3)` (product `7776`).
- Orientation index: `17/56`.
- Actual orientation: `(2,2,3,3,3,2,3,4,3)`.
- Budget: `screen_time_limit = 600s`, `max_cycles = 10_000_000`, `solver_timeout_ms = 300000`, `max_survivors = 20`.

### Open Questions
- Does orientation `18/56` also end with `screened=0`?
- Can prefix sharding break the `16-17` dead zone the way it broke the last `n = 7`, product-576 residue?
- Is there a useful seed derived from the `n = 7` or `n = 8` survivor structures for this `n = 9` family, or is the recurrent dynamics genuinely different?

## Exploration 62

### Strategy
Transfer the `n = 7` rescue tactic directly to `n = 9`: run a first-mover sharded screen on the dead orientation `16/56`, namely `(2,2,3,3,3,2,3,3,4)`, and check whether any first-mover branch reaches the fatal-screen stage in `300s`.

### Outcome
PARTIAL

### Failure Constraint
- The batch does not complete cleanly because prefix `(7,)` crashes inside `tarjan_scc(...)` with a Python `RecursionError`, so the aggregate runner aborts before producing a total summary.
- This is a tooling failure, not a mathematical obstruction.

### What This Rules Out
- The monolithic `screened=0` result for orientation `16/56` is not a statement that every first-mover branch is equally dead.
- At the same time, first-mover sharding does not immediately trivialize the class: even with sharding, some branches remain so deep that they overrun the nominal `300s` cap and one branch crashes the current recursive SCC implementation.

### Surviving Structure
- Prefix sharding does break the monolithic dead zone on several branches:
  - prefix `4` screens `422` cycles in `300s`,
  - prefix `5` screens `422`,
  - prefix `6` screens `380`,
  - prefix `3` screens `100`,
  - prefix `1` screens `51`,
  - prefix `2` screens `40`,
  - prefix `0` screens `0`.
- Every completed branch so far has `survivors=0`.
- The hard residue is therefore already smaller than “the whole orientation”: some first movers are productive, some are nearly dead, and at least one (`7`) currently crashes the screen implementation.

### Reformulations
- The `n = 9` problem is not uniformly pre-screen dead. It decomposes into a mix of low-yield, medium-yield, and crash-prone first-mover branches.
- This is the first evidence that the prefix-sharding representation from `n = 7` genuinely transfers to `n = 9`, but it also reveals a previously hidden implementation limit in the recursive SCC routine.

LOAD-BEARING ASSESSMENT: High. Even though the batch crashed, it changes the search picture materially and exposes a concrete tool bug whose fix is likely prerequisite for meaningful `n = 9` progress.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_prefix_batch.py 2,2,3,3,3,2,3,3,4 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 7` partially returns:
  - `prefix=3 screened=100 survivors=0 elapsed=300.000s`
  - `prefix=2 screened=40 survivors=0 elapsed=300.002s`
  - `prefix=4 screened=422 survivors=0 elapsed=300.001s`
  - `prefix=6 screened=380 survivors=0 elapsed=300.004s`
  - `prefix=1 screened=51 survivors=0 elapsed=300.004s`
  - `prefix=0 screened=0 survivors=0 elapsed=300.000s`
  - `prefix=5 screened=422 survivors=0 elapsed=300.001s`
- The same batch then aborts on prefix `(7,)` with:
  - `RuntimeError: could not parse screen output for prefix (7,)`
  - underlying cause in `scripts/p2_cycle_screen.py` / `scripts/p2_completion_search.py`: `RecursionError: maximum recursion depth exceeded` inside `tarjan_scc(...)`.

STRUCTURAL RESULTS:
- Orientation `16/56` is not globally pre-screen dead under first-mover sharding.
- No completed first-mover branch has produced a survivor yet.

TOOLS:
- The existing `scripts/p2_prefix_batch.py` is informative on `n = 9`, but `scripts/p2_cycle_screen.py` / `scripts/p2_completion_search.py` hit Python recursion depth on at least one branch.

REPRESENTATIONS:
- First-mover decomposition of orientation `(2,2,3,3,3,2,3,3,4)` is now partially visible:
  - productive branches: `3,4,5,6`
  - low-yield branches: `1,2`
  - dead-at-current-depth branch: `0`
  - crash-prone branch: `7`

### What Would Unblock This
- Raise or remove the recursion bottleneck in the cycle-screen/Tarjan path so the sharded `n = 9` batch can complete.
- After that, rerun the same first-mover batch on orientation `16/56` and inspect the missing prefixes, especially `7` and the still-unreported tail.

### Key Parameters
- Orientation attacked: `(2,2,3,3,3,2,3,3,4)` = `16/56`.
- Prefix depth: `1`.
- Budget per prefix: `300s`.
- Completed prefixes before crash: `7`.

### Open Questions
- Once the recursion limit is fixed, what are the missing results for prefixes `7` and `8`?
- Do the productive first-mover branches stay survivor-free under longer sharded budgets, or do they eventually reach SMT?
- Is the branch `7` special mathematically, or was it only the first one to expose the recursion-depth limit?

## Exploration 63

### Strategy
Fix the recursion-depth failure in the SCC screen and rerun the exact same first-mover sharded batch on orientation `16/56`, so the partially observed `n = 9` branch structure can be completed cleanly.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- Orientation `16/56` is no longer just “pre-screen dead” under better search organization; with first-mover sharding it is survivor-free through `2373` screened cycles at the current depth.
- The earlier crash on prefix `(7,)` was a tooling artifact, not evidence of a qualitatively different positive branch.

### Surviving Structure
- After raising the recursion limit in `scripts/p2_completion_search.py`, the first-mover batch completes normally.
- The previously missing branches are:
  - prefix `7`: `screened=958`, `survivors=0`,
  - prefix `8`: `screened=0`, `survivors=0`.
- Full first-mover total for orientation `(2,2,3,3,3,2,3,3,4)`:
  - `2373` screened cycles,
  - `0` survivors,
  - wall-clock `600.515s`.
- So orientation `16/56` has moved from “generator-dominated unknown” to a genuinely screened negative checkpoint under the sharded representation.

### Reformulations
- This is the first concrete transfer of the `n = 7` sharding idea to `n = 9`: a monolithic `screened=0` orientation becomes a nontrivial screened-negative object once decomposed by first mover.
- The right `n = 9` unit of work is therefore no longer an orientation alone, but an orientation together with a mover-prefix decomposition.

LOAD-BEARING ASSESSMENT: High. This changes the active search policy for `n = 9` from blind orientation sweeps to sharded orientation attacks, and it fixes a tool-level blocker on the same path.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Recursion-limit fix:
  - `scripts/p2_completion_search.py` now sets `sys.setrecursionlimit(50000)`, which prevents the `tarjan_scc(...)` path from failing on the deep `n = 9` branches.
- Clean rerun of the same batch:
  - `python3 scripts/p2_prefix_batch.py 2,2,3,3,3,2,3,3,4 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 7` reports
    - `prefix=3 screened=100 survivors=0 elapsed=300.000s`
    - `prefix=4 screened=422 survivors=0 elapsed=300.000s`
    - `prefix=5 screened=422 survivors=0 elapsed=300.004s`
    - `prefix=6 screened=380 survivors=0 elapsed=300.000s`
    - `prefix=0 screened=0 survivors=0 elapsed=300.011s`
    - `prefix=2 screened=40 survivors=0 elapsed=300.000s`
    - `prefix=1 screened=51 survivors=0 elapsed=300.000s`
    - `prefix=7 screened=958 survivors=0 elapsed=300.000s`
    - `prefix=8 screened=0 survivors=0 elapsed=300.000s`
    - `total prefixes=9 screened=2373 survivors=0 elapsed=600.515s`

STRUCTURAL RESULTS:
- Orientation `16/56`, `(2,2,3,3,3,2,3,3,4)`, is survivor-free at the current first-mover sharded depth.
- The productive mass is concentrated heavily in prefix `7`, with moderate counts in `4,5,6`, light counts in `1,2,3`, and zero counts in `0,8`.

TOOLS:
- The SCC-screen path is now robust enough for the `n = 9` sharded search regime.

REPRESENTATIONS:
- First-mover profile for orientation `16/56`:
  - heavy branch: `7`
  - medium branches: `4,5,6`
  - light branches: `1,2,3`
  - dead branches at current depth: `0,8`

### What Would Unblock This
- Apply the same first-mover sharded batch to orientation `17/56`, so the local dead zone can be compared on the same representation.
- If orientation `17` also becomes sharded-negative, recurse only on its heaviest first-mover branches rather than continuing monolithic sweeps.

### Key Parameters
- Orientation attacked: `(2,2,3,3,3,2,3,3,4)` = `16/56`.
- Prefix depth: `1`.
- Budget per prefix: `300s`.
- Aggregate screened count after sharding: `2373`.

### Open Questions
- Does orientation `17/56` also become sharded-negative, or does it reveal survivors once decomposed by first mover?
- Is prefix `7` on orientation `16` just the biggest negative branch, or the first branch worth a second-level split?
- Are the zero-count first movers (`0,8`) structurally impossible, or merely deeper than the current budget despite producing no completed cycles?

## Exploration 64

### Strategy
Apply the same first-mover sharded screen to the adjacent orientation `17/56`, `(2,2,3,3,3,2,3,4,3)`, so the local `n = 9` dead zone can be compared on a common representation instead of monolithic `screened=0` runs.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- Orientation `17/56` is not hiding an easy survivor that the monolithic sweep merely failed to reach.
- The local dead zone around orientations `16-17` is now screened-negative under first-mover sharding, not merely unobserved under monolithic DFS.

### Surviving Structure
- Full first-mover total for orientation `(2,2,3,3,3,2,3,4,3)`:
  - `1202` screened cycles,
  - `0` survivors,
  - wall-clock `600.545s`.
- Branch profile:
  - heaviest completed branch: prefix `3` with `370` screened cycles,
  - medium branches: `4` and `5` with `251` each, `2` with `220`, `6` with `102`,
  - light branch: `7` with `8`,
  - dead branches at current depth: `0`, `1`, `8`.
- Compared with orientation `16`, orientation `17` is both lighter overall (`1202` vs `2373`) and distributed differently; its residue is not dominated by prefix `7`.

### Reformulations
- Adjacent orientations can be sharded-negative for different reasons. Orientation `16` concentrates mass in prefix `7`, while orientation `17` spreads moderate mass across prefixes `2-6` and leaves `7` almost empty.
- So the useful object is no longer just “dead-zone block 16-17,” but a small family of orientation-specific prefix profiles.

LOAD-BEARING ASSESSMENT: Moderate to high. This does not produce a witness, but it materially sharpens where deeper recursion should be spent and shows that adjacent orientations are not interchangeable.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_prefix_batch.py 2,2,3,3,3,2,3,4,3 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 7` reports
  - `prefix=2 screened=220 survivors=0 elapsed=300.001s`
  - `prefix=4 screened=251 survivors=0 elapsed=300.001s`
  - `prefix=5 screened=251 survivors=0 elapsed=300.000s`
  - `prefix=6 screened=102 survivors=0 elapsed=300.001s`
  - `prefix=3 screened=370 survivors=0 elapsed=300.000s`
  - `prefix=1 screened=0 survivors=0 elapsed=300.002s`
  - `prefix=0 screened=0 survivors=0 elapsed=300.001s`
  - `prefix=8 screened=0 survivors=0 elapsed=300.000s`
  - `prefix=7 screened=8 survivors=0 elapsed=300.000s`
  - `total prefixes=9 screened=1202 survivors=0 elapsed=600.545s`

STRUCTURAL RESULTS:
- Orientation `17/56`, `(2,2,3,3,3,2,3,4,3)`, is survivor-free at the current first-mover sharded depth.
- The adjacent pair `16-17` is now fully screened-negative under the same first-mover representation.

TOOLS:
- No new tools; this is a direct use of the repaired sharded screen.

REPRESENTATIONS:
- First-mover profile for orientation `17/56`:
  - heavy branch: `3`
  - medium branches: `2,4,5`
  - light branches: `6,7`
  - dead branches at current depth: `0,1,8`

### What Would Unblock This
- Recurse one level deeper only where the mass sits:
  - orientation `16`, base prefix `7`,
  - orientation `17`, base prefix `3`.
- If those second-level splits also stay survivor-free, the next useful step is probably to classify orientation `18/56` at first-mover depth rather than keep drilling both branches indefinitely.

### Key Parameters
- Orientation attacked: `(2,2,3,3,3,2,3,4,3)` = `17/56`.
- Prefix depth: `1`.
- Budget per prefix: `300s`.
- Aggregate screened count after sharding: `1202`.

### Open Questions
- Does the heaviest branch `3` of orientation `17` stay survivor-free after a second-level split?
- Is orientation `18/56` closer to the orientation-16 profile, the orientation-17 profile, or something new?
- Do these adjacent sharded-negative profiles suggest a local combinatorial obstruction around the placement of the `4`-state processor?

## Exploration 65

### Strategy
Recurse on the heaviest known `n = 9` residue: split orientation `16/56`, `(2,2,3,3,3,2,3,3,4)`, under base prefix `7` into second-mover subbranches and see whether the large first-level count hides broad mass or only one or two real children.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The heavy first-mover branch `7` is not broadly hard across all second moves.
- Most of its apparent mass was not spread across many children: six second-mover choices are immediately dead and one more is dead at current depth.

### Surviving Structure
- Immediate dead children under base prefix `7`:
  - `7,0`, `7,1`, `7,2`, `7,3`, `7,4`, `7,5` all return `screened=0` in about `2.2s` to `2.5s`.
- Additional dead child at current depth:
  - `7,8` returns `screened=0` in `300s`.
- Productive second-level residue:
  - `7,6` screens `958` cycles, `0` survivors.
  - `7,7` screens `563` cycles, `0` survivors.
- Aggregate second-level total:
  - `1521` screened cycles,
  - `0` survivors,
  - wall-clock `302.799s`.
- This means the top-level heavy branch `7` has already collapsed to exactly two meaningful grandchildren, `(7,6)` and `(7,7)`.

### Reformulations
- The `n = 9` residue is now demonstrably recursive in the same way the final `n = 7` residue was: a seemingly heavy branch becomes mostly impossible once split one level deeper.
- Branch totals are not monotone under sharding; the second-level run can expose more screened cycles than the parent branch because the constrained subtrees are searched more effectively than the monolithic branch traversal.

LOAD-BEARING ASSESSMENT: High. This is the strongest evidence so far that recursive mover-prefix sharding is the right active search representation for the `n = 9` bottleneck.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_prefix_batch.py 2,2,3,3,3,2,3,3,4 --base-prefix 7 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 7` reports
  - `prefix=7,4 screened=0 survivors=0 elapsed=2.200s`
  - `prefix=7,2 screened=0 survivors=0 elapsed=2.242s`
  - `prefix=7,3 screened=0 survivors=0 elapsed=2.233s`
  - `prefix=7,0 screened=0 survivors=0 elapsed=2.362s`
  - `prefix=7,5 screened=0 survivors=0 elapsed=2.310s`
  - `prefix=7,1 screened=0 survivors=0 elapsed=2.472s`
  - `prefix=7,6 screened=958 survivors=0 elapsed=300.000s`
  - `prefix=7,7 screened=563 survivors=0 elapsed=300.015s`
  - `prefix=7,8 screened=0 survivors=0 elapsed=300.000s`
  - `total prefixes=9 screened=1521 survivors=0 elapsed=302.799s`

STRUCTURAL RESULTS:
- Orientation `16/56` remains survivor-free after a second-level split of its heaviest branch.
- The hard residue inside orientation `16/56` is now localized to exactly two depth-two prefixes: `(7,6)` and `(7,7)`.

TOOLS:
- No new tools; this is a direct use of recursive mover-prefix sharding on the repaired screen.

REPRESENTATIONS:
- Depth-two residue for orientation `16/56`:
  - live grandchildren: `(7,6)`, `(7,7)`
  - dead grandchildren: `(7,0)`, `(7,1)`, `(7,2)`, `(7,3)`, `(7,4)`, `(7,5)`, `(7,8)`

### What Would Unblock This
- Apply the same second-level split to the heaviest branch of orientation `17/56`, namely prefix `3`, to compare whether its residue is similarly sparse.
- If both orientations collapse to one or two depth-two prefixes, recurse only on those instead of widening to many new orientations immediately.

### Key Parameters
- Orientation attacked: `(2,2,3,3,3,2,3,3,4)` = `16/56`.
- Base prefix: `7`.
- New prefix depth: `2`.
- Budget per child: `300s`.
- Aggregate screened count: `1521`.

### Open Questions
- Does orientation `17/56` / prefix `3` collapse just as sharply under a second-level split?
- Between `(7,6)` and `(7,7)`, which child is the better target for a depth-three split?
- Is the dominance of repeated high-index movers here a real structural signature of the `n = 9` family, or just a local artifact of orientation `16`?

## Synthesis after exploration 65

The `n = 9` search is finally showing the same anatomy that made late-stage `n = 7` progress possible. Monolithic sweeps said “orientations 16 and 17 are dead.” First-mover sharding refined that to “both are sharded-negative, but with different branch profiles.” Exploration 65 refines further: the heaviest branch of orientation 16 is mostly fake mass, collapsing immediately to just two depth-two prefixes. That is exactly the kind of sparse recursive residue that sharding can keep attacking. The search is no longer a flat orientation sweep; it is becoming a small tree of explicit hard prefixes.

## Exploration 66

### Strategy
Run the matching second-level split on orientation `17/56`, base prefix `3`, so the two adjacent `n = 9` orientations can be compared at the same recursion depth.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- Orientation `17/56` / prefix `3` is not broadly hard across all second movers.
- The local `16-17` block does not just have different first-level profiles; both orientations now show sharply sparse depth-two residue.

### Surviving Structure
- Immediate dead children under base prefix `3`:
  - `3,0`, `3,1`, `3,5`, `3,6`, `3,7`, `3,8` all return `screened=0` in about `1.4s` to `2.2s`.
- Additional dead child at current depth:
  - `3,4` returns `screened=0` in `300s`.
- Productive second-level residue:
  - `3,2` screens `370` cycles, `0` survivors.
  - `3,3` screens `74` cycles, `0` survivors.
- Aggregate second-level total:
  - `444` screened cycles,
  - `0` survivors,
  - wall-clock `300.224s`.
- So orientation `17/56` collapses even more sharply than orientation `16/56`: its heaviest branch reduces to one clearly dominant grandchild, `(3,2)`, plus a small side branch `(3,3)`.

### Reformulations
- The shared pattern across orientations `16` and `17` is now clear: once the heaviest first-level branch is split, almost all second movers die immediately and the residue collapses to one or two explicit depth-two prefixes.
- That is strong evidence that the right active representation for this `n = 9` family is a recursive prefix tree, not an orientation list.

LOAD-BEARING ASSESSMENT: High. This confirms that the sparse-residue phenomenon is not a one-orientation accident and gives a concrete finite list of next hard prefixes.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_prefix_batch.py 2,2,3,3,3,2,3,4,3 --base-prefix 3 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 7` reports
  - `prefix=3,6 screened=0 survivors=0 elapsed=1.989s`
  - `prefix=3,1 screened=0 survivors=0 elapsed=1.995s`
  - `prefix=3,0 screened=0 survivors=0 elapsed=2.067s`
  - `prefix=3,5 screened=0 survivors=0 elapsed=2.156s`
  - `prefix=3,8 screened=0 survivors=0 elapsed=1.446s`
  - `prefix=3,7 screened=0 survivors=0 elapsed=1.470s`
  - `prefix=3,2 screened=370 survivors=0 elapsed=300.000s`
  - `prefix=3,3 screened=74 survivors=0 elapsed=300.000s`
  - `prefix=3,4 screened=0 survivors=0 elapsed=300.000s`
  - `total prefixes=9 screened=444 survivors=0 elapsed=300.224s`

STRUCTURAL RESULTS:
- Orientation `17/56` remains survivor-free after a second-level split of its heaviest branch.
- The hard residue inside orientation `17/56` is now localized to depth-two prefixes `(3,2)` and `(3,3)`, with `(3,2)` dominant.

TOOLS:
- No new tools; this is another direct use of recursive mover-prefix sharding.

REPRESENTATIONS:
- Depth-two residue for orientation `17/56`:
  - live grandchildren: `(3,2)`, `(3,3)`
  - dead grandchildren: `(3,0)`, `(3,1)`, `(3,4)`, `(3,5)`, `(3,6)`, `(3,7)`, `(3,8)`

### What Would Unblock This
- Recurse one level deeper only on the four current hard prefixes:
  - orientation `16`: `(7,6)`, `(7,7)`
  - orientation `17`: `(3,2)`, `(3,3)`
- If those also stay survivor-free, then the local `16-17` block is effectively compressed to a very small explicit frontier and orientation `18/56` becomes the next widening move.

### Key Parameters
- Orientation attacked: `(2,2,3,3,3,2,3,4,3)` = `17/56`.
- Base prefix: `3`.
- New prefix depth: `2`.
- Budget per child: `300s`.
- Aggregate screened count: `444`.

### Open Questions
- Which of the four current hard prefixes, `(7,6)`, `(7,7)`, `(3,2)`, `(3,3)`, is most promising for a depth-three split?
- Does orientation `18/56` continue the same sparse-residue pattern, or does it reintroduce a broader first-level profile?
- Is there a local rule around repeated late movers that explains why the surviving depth-two prefixes cluster where they do?

## Synthesis after exploration 66

The local `n = 9` picture is now explicit enough to guide the next round of compute. Orientations `16` and `17` are both monolithically opaque but sharded-negative. Their heaviest first-mover branches then collapse almost completely at depth two:
- orientation `16`: residue `(7,6)`, `(7,7)`
- orientation `17`: residue `(3,2)`, `(3,3)`
Everything else is already dead at the current depth. So the search is no longer “resume the sweep.” It is “choose among four concrete hard prefixes, or widen once to orientation 18 if a broader comparison is more useful.”

## Exploration 67

### Strategy
Drill one level deeper into the heaviest remaining prefix, orientation `16/56` under base prefix `(7,6)`, to test whether the sparse-residue pattern persists at depth three.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The depth-two residue `(7,6)` is not broadly hard across all third movers.
- Most of the branch mass again collapses immediately once the next mover is fixed.

### Surviving Structure
- Immediate dead children under base prefix `(7,6)`:
  - `7,6,0`, `7,6,1`, `7,6,2`, `7,6,3`, `7,6,4`, `7,6,8` all return `screened=0` in about `1.4s` to `2.5s`.
- Productive depth-three residue:
  - `7,6,5` screens `958` cycles, `0` survivors.
  - `7,6,6` screens `683` cycles, `0` survivors.
  - `7,6,7` screens `330` cycles, `0` survivors.
- Aggregate third-level total:
  - `1971` screened cycles,
  - `0` survivors,
  - wall-clock `302.627s`.
- So the single heaviest depth-two prefix now collapses to exactly three live depth-three prefixes.

### Reformulations
- The sparse-residue behavior is now stable across three levels of recursion on orientation `16`: broad-looking mass at one level becomes a handful of explicit children at the next.
- This is no longer merely analogous to the late `n = 7` search. It is the same search geometry, now visible in the `n = 9` family.

LOAD-BEARING ASSESSMENT: High. This justifies treating the remaining `n = 9` work as a small recursive prefix tree rather than a long orientation sweep.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_prefix_batch.py 2,2,3,3,3,2,3,3,4 --base-prefix 7,6 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 7` reports
  - `prefix=7,6,3 screened=0 survivors=0 elapsed=2.166s`
  - `prefix=7,6,0 screened=0 survivors=0 elapsed=2.148s`
  - `prefix=7,6,2 screened=0 survivors=0 elapsed=2.306s`
  - `prefix=7,6,4 screened=0 survivors=0 elapsed=2.257s`
  - `prefix=7,6,1 screened=0 survivors=0 elapsed=2.457s`
  - `prefix=7,6,8 screened=0 survivors=0 elapsed=1.403s`
  - `prefix=7,6,5 screened=958 survivors=0 elapsed=300.000s`
  - `prefix=7,6,6 screened=683 survivors=0 elapsed=300.000s`
  - `prefix=7,6,7 screened=330 survivors=0 elapsed=300.000s`
  - `total prefixes=9 screened=1971 survivors=0 elapsed=302.627s`

STRUCTURAL RESULTS:
- Orientation `16/56` remains survivor-free after a depth-three split of its heaviest branch.
- The live residue under orientation `16/56` now includes:
  - from branch `(7,6)`: `(7,6,5)`, `(7,6,6)`, `(7,6,7)`
  - plus still-unexpanded sibling branch `(7,7)`

TOOLS:
- No new tools; this is another direct use of recursive mover-prefix sharding.

REPRESENTATIONS:
- Depth-three residue under orientation `16/56` / `(7,6)`:
  - live children: `(7,6,5)`, `(7,6,6)`, `(7,6,7)`
  - dead children: `(7,6,0)`, `(7,6,1)`, `(7,6,2)`, `(7,6,3)`, `(7,6,4)`, `(7,6,8)`

### What Would Unblock This
- Expand `(7,7)` on orientation `16` and `(3,2)` on orientation `17`, since those are the next two biggest unresolved prefixes.
- Alternatively, widen once to orientation `18/56` if a third local comparison is more valuable than further recursion on the current tree.

### Key Parameters
- Orientation attacked: `(2,2,3,3,3,2,3,3,4)` = `16/56`.
- Base prefix: `(7,6)`.
- New prefix depth: `3`.
- Budget per child: `300s`.
- Aggregate screened count: `1971`.

### Open Questions
- Is sibling branch `(7,7)` smaller or larger than the newly expanded `(7,6)` tree?
- Does orientation `17` / `(3,2)` show the same three-child pattern at depth three?
- At what depth, if any, does a survivor finally appear in this local `16-17` block?

## Synthesis after exploration 67

The `n = 9` local block around orientations `16-17` is no longer opaque. It is a small recursive search tree with explicit surviving prefixes:
- orientation `16`: `(7,7)` and `(7,6,5)`, `(7,6,6)`, `(7,6,7)`
- orientation `17`: `(3,2)` and `(3,3)`
Everything else seen so far is dead at the current sharded depth. That is enough structure to resume from exact hard prefixes next time instead of from raw orientation numbers.

## Exploration 68

### Strategy
Build a data-driven local-type extractor for the Escape Lemma on top of the existing lower-bound scripts, starting with the exact uniform-sweep dataset behind the known `514,840`-configuration verification count, then extending to a broader mixed dataset and one canonical `n = 9` probe.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The current local-type data does not support the strongest hoped-for form of stabilization at the raw radius-2 state-pattern level by `n = 8`: the number of distinct `(m-window, state-window)` types is still increasing from `n = 5` through `n = 8`.
- On the other hand, the data rules out a more pessimistic picture where the Escape Lemma depends on rare nonlocal rescue moves. In every recorded type so far, the centered forced processor’s own forced move already stays outside the good set.

### Surviving Structure
- Uniform-sweep baseline dataset:
  - The new extractor reproduces the exact known count `514,840` forced-privileged non-good configurations with `0` Escape Lemma failures.
  - Forced processor instances in the same dataset: `736,288`.
- Raw local-type counts for the exact uniform baseline:
  - `n = 5`: `157`
  - `n = 6`: `552`
  - `n = 7`: `748`
  - `n = 8`: `940`
- Radius-2 architecture-window counts (`m_{i-2..i+2}` only) for the same baseline:
  - `n = 5`: `10`
  - `n = 6`: `23`
  - `n = 7`: `28`
  - `n = 8`: `29`
- New `m`-windows first seen at each `n` in the uniform baseline:
  - `n = 5`: `10`
  - `n = 6`: `13`
  - `n = 7`: `5`
  - `n = 8`: `1`
- Supplementary canonical `n = 9` uniform-sweep probe on `(2,2,2,3,3,3,3,3,3)`:
  - `4418` forced-privileged non-good configs,
  - `6408` forced processor instances,
  - `108` raw local types,
  - `8` distinct `m`-windows,
  - and crucially `0` new raw types beyond the `n = 8` uniform dataset.
- Broader `full` dataset (uniform + non-uniform + length-11 + mixed quaternary):
  - forced configs: `4,876,948`
  - forced instances: `6,838,650`
  - raw local types:
    - `n = 5`: `676`
    - `n = 6`: `1334`
    - `n = 7`: `3658`
    - `n = 8`: `6858`
  - distinct `m`-windows:
    - `n = 5`: `10`
    - `n = 6`: `44`
    - `n = 7`: `103`
    - `n = 8`: `155`
  - quaternary-local contribution in the full dataset:
    - `n = 6`: `144` quaternary-centered types, `560` types with a quaternary somewhere in the radius-2 window
    - `n = 7`: `672` quaternary-centered, `2624` with a quaternary in-window
    - `n = 8`: `1814` quaternary-centered, `5876` with a quaternary in-window

### Reformulations
- The finite-classification question now splits into two measurable versions:
  1. raw radius-2 state types `(m-window, state-window)`, which do not stabilize by `n = 8` on the uniform baseline,
  2. coarser architecture windows (`m-window` only), which nearly stabilize on the same baseline and show no new patterns in the canonical `n = 9` probe.
- The strongest local empirical fact is sharper than the original existential Escape Lemma statement: for every recorded forced-privilege type in the extracted datasets, the centered processor itself has an escaping forced move. The nonlocal “some other forced processor escapes” mechanism was not needed on any observed type.

LOAD-BEARING ASSESSMENT: High. This does not prove the Escape Lemma for all `n`, but it converts the vague “finite local type” strategy into a concrete data object and gives the first real indication of which level of abstraction might stabilize.

### Concrete Artifacts
TOOLS:
- New script: `scripts/extract_escape_local_types.py`.
  - `--dataset uniform` replays the exact `514,840`-configuration Escape Lemma dataset from `scripts/verify_lower_bound.py`.
  - `--dataset full` extends the same classification to the supplementary non-uniform, length-11, and mixed-quaternary cycle families.
  - `--include-n9-canonical` adds one canonical `n = 9` uniform-sweep cycle as a supplementary data point.

COMPUTED EXAMPLES:
- `python3 scripts/extract_escape_local_types.py --json-out scripts/escape_local_types_summary.json`
  reproduces the uniform-sweep baseline with
  `forced_configs=514840`, `forced_instances=736288`,
  and type counts `(157, 552, 748, 940)` for `n = 5,6,7,8`.
- `python3 scripts/extract_escape_local_types.py --include-n9-canonical --json-out scripts/escape_local_types_summary_n9.json`
  adds the canonical `n = 9` point and shows `0` new raw types beyond the `n = 8` uniform baseline.
- `python3 scripts/extract_escape_local_types.py --dataset full --json-out scripts/escape_local_types_full_summary.json`
  produces the broader mixed dataset and exposes the quaternary-local type counts listed above.

STRUCTURAL RESULTS:
- Uniform baseline: raw radius-2 state types do not stabilize by `n = 8`, but the underlying `m`-window vocabulary nearly does, and the canonical `n = 9` probe adds no new raw types at all.
- Across both the uniform baseline and the broader full dataset, every observed centered forced-privilege type has `center_escape = True` in all occurrences.

REPRESENTATIONS:
- Aggregate summaries:
  - `scripts/escape_local_types_summary.json`
  - `scripts/escape_local_types_summary_n9.json`
  - `scripts/escape_local_types_full_summary.json`

### What Would Unblock This
- Coarsen the type key from full radius-2 state patterns to a smaller structural invariant suggested by the data, probably something between raw `(m-window, state-window)` and pure `m-window`.
- In particular, test whether the raw types collapse under a quotient that identifies interior ternary states modulo the shadow permutation structure, rather than by literal labels.
- A useful next experiment is to group by `(m-window, centered local context, centered output)` plus a small number of block-position tags, and re-check stabilization.

### Key Parameters
- Exact uniform baseline reproduced: `514,840` forced-privileged non-good configs, `0` failures.
- Uniform raw-type counts: `157, 552, 748, 940` for `n = 5..8`.
- Uniform `m`-window counts: `10, 23, 28, 29` for `n = 5..8`.
- Canonical `n = 9` supplementary point: `108` raw types, `8` `m`-windows, `0` new raw types beyond the `n = 8` uniform baseline.
- Full-dataset raw-type counts: `676, 1334, 3658, 6858` for `n = 5..8`.

### Open Questions
- What is the right quotient of the raw radius-2 state patterns so that the type count actually stabilizes?
- Does the “centered forced move always escapes” phenomenon admit a direct symbolic proof?
- Are the new raw types first seen at `n = 8` all explainable as bulk all-ternary windows, or is there still a genuinely new boundary mechanism there?

## Synthesis after exploration 68

The local-type program is now concrete enough to guide proof work. The naive type key is too fine: raw radius-2 state patterns keep growing, so there is no immediate finite classification at that level. But the growth is not arbitrary. On the exact uniform baseline, the architecture windows nearly stabilize (`10,23,28,29`), and a canonical `n = 9` probe introduces no new raw types at all. Even better, the data shows a stronger local fact than the Escape Lemma itself: every observed centered forced-privilege type already escapes through its own forced move. So the next proof move is not “keep collecting raw types,” but “find the right quotient that preserves this centered-escape property while collapsing the raw catalog to something finite.”

## Exploration 69

### Strategy
Patch the Escape Lemma local-type extractor to summarize coarser quotient families directly, then rerun the exact uniform-sweep baseline and the canonical `n = 9` probe to test whether the centered local-context quotient really stabilizes and whether it preserves enough information to control the forced move.

### Outcome
SUCCEEDED

### Failure Constraint
The centered local-context quotient `(m_{i-1..i+1}, p_{i-1..i+1})` is not fine enough to reconstruct the forced transition uniformly. Even on the exact uniform-sweep dataset, 9 of the 45 observed quotient classes merge raw radius-2 types with different forced outputs.

### What This Rules Out
- Any proof plan that tries to derive the full shadow-step transition from the centered 3-site context alone will hit the same obstacle, because that quotient forgets radius-2 information that genuinely affects the forced output.
- More narrowly, the earlier informal inference that the centered local context already determines `T(i-1,i,i+1)` was an artifact of reading only one example per raw type; that shortcut is invalid.

### Surviving Structure
- Exact uniform-sweep dataset, now with quotient summaries embedded in the extractor output:
  - raw type counts remain `157, 552, 748, 940` for `n = 5,6,7,8`,
  - raw `m`-window counts remain `10, 23, 28, 29`,
  - centered local-context quotient counts are
    - `n = 5`: `27`
    - `n = 6`: `45`
    - `n = 7`: `45`
    - `n = 8`: `45`
  - and the last new centered local-context class appears at `n = 6`.
- Canonical `n = 9` probe:
  - raw type count `108`,
  - raw `m`-window count `8`,
  - centered local-context quotient count `12`,
  - and still `0` new centered local-context classes beyond the `n = 8` baseline.
- Stable centered-escape behavior survives the quotient perfectly:
  - all `45/45` observed centered local-context classes have stable `center_escape = True` across the observed data,
  - all `19/19` classes in the even coarser `center_kind_state_triple` quotient do as well.
- Deterministic forced output does not survive the quotient:
  - only `36/45` observed centered local-context classes have a unique forced output across the observed data,
  - only `15/19` classes in the `center_kind_state_triple` quotient do.

### Reformulations
- The local-type problem now naturally splits into two layers:
  1. an Escape Lemma quotient whose job is only to prove “the centered forced move stays outside the good set,” and
  2. a finer transition quotient, if needed, for reconstructing the actual shadow dynamics.
- This is better than treating “finite local classification” as a single target. The data says the escape property stabilizes on a strictly coarser quotient than the transition rule does.

LOAD-BEARING ASSESSMENT: High. This changes the proof target from “find one quotient that does everything” to “find the coarsest quotient that preserves centered escape.” That is a materially easier search space.

### Concrete Artifacts
TOOLS:
- `scripts/extract_escape_local_types.py` now emits a `quotients` section in its JSON summaries for:
  - `center_local_context`
  - `center_kind_state_triple`
  - `m_window_only`
  along with per-`n` class counts, new-class counts, deterministic-output counts, and centered-escape stability counts.

COMPUTED EXAMPLES:
- `python3 scripts/extract_escape_local_types.py --json-out scripts/escape_local_types_summary.json`
  now reports the stabilized centered local-context counts `27,45,45,45` for `n = 5..8`.
- `python3 scripts/extract_escape_local_types.py --include-n9-canonical --json-out scripts/escape_local_types_summary_n9.json`
  confirms `0` new centered local-context classes at `n = 9`.

STRUCTURAL RESULTS:
- On the exact uniform-sweep Escape Lemma dataset, the centered local-context quotient stabilizes by `n = 6` and stays stable through the canonical `n = 9` probe.
- The centered local-context quotient is sufficient for stable centered-escape behavior but insufficient for deterministic forced output.

REPRESENTATIONS:
- Updated aggregate summaries:
  - `scripts/escape_local_types_summary.json`
  - `scripts/escape_local_types_summary_n9.json`

### What Would Unblock This
- Identify a minimally finer quotient that still stabilizes through `n = 8` or `n = 9` but resolves the 9 ambiguous centered local-context classes.
- The smallest useful next computation is to classify those 9 ambiguous classes by which radius-2 bits actually split their forced output: left distance-2 state, right distance-2 state, or boundary-position metadata.

### Key Parameters
- Uniform baseline totals remain `514,840` forced configs and `736,288` forced processor instances.
- Centered local-context quotient counts: `27,45,45,45` for `n = 5..8`, `12` for the canonical `n = 9` probe.
- Observed centered local-context classes with deterministic forced output: `36/45`.
- Observed centered local-context classes with stable centered escape: `45/45`.

### Open Questions
- Which exact radius-2 datum separates the 9 ambiguous centered local-context classes with multiple forced outputs?
- Does the Escape Lemma proof need anything finer than the 45 stabilized centered local-context classes?
- Can the ambiguous classes be explained uniformly as boundary effects, or do some also occur in the bulk all-ternary region?

## Synthesis after exploration 69

The key structural split is now visible. There is no need to force one quotient to serve two unrelated purposes. The centered local-context quotient is already finite on the exact uniform baseline and appears sufficient for the Escape Lemma itself, because all 45 observed classes have the same centered-escape behavior across `n = 5..9`. What fails at that quotient is not escape but transition reconstruction: 9 classes still hide multiple forced outputs. So the proof program should separate “escape classification” from “shadow transition classification.” The next useful computation is to localize exactly which forgotten radius-2 datum resolves those 9 classes, rather than to keep searching for a single monolithic local invariant.

## Exploration 70 (probe)

### Strategy
Check whether the forced-output ambiguity seen in the centered local-context quotient disappears at the full raw radius-2 type level, using the updated JSON summaries from exploration 69.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- The forced-output ambiguity persists even at the full raw type level once multiple uniform-sweep shadow-cycle families are aggregated.
- Ambiguous raw-type counts by `n` in the exact uniform-sweep dataset:
  - `n = 5`: `20 / 157`
  - `n = 6`: `94 / 552`
  - `n = 7`: `148 / 748`
  - `n = 8`: `201 / 940`
  - canonical `n = 9`: `0 / 108`
- Across `n = 5..8`, `201 / 940` observed raw radius-2 types have multiple forced outputs across different cycle families.

COMPUTED EXAMPLES:
- Sample globally ambiguous raw types include
  - `((2,2,3,2,3), (0,1,0,0,0))` with outputs `{1,2}`
  - `((2,2,3,3,2), (0,1,0,0,0))` with outputs `{1,2}`
  - `((2,3,3,2,2), (0,1,0,1,0))` with outputs `{1,2}`

### Open Questions
- Which proof-facing quotient best catalogs the 45 stabilized centered-local-context escape classes in a human-usable form?
- Can those 45 classes be grouped into a smaller number of symbolic escape mechanisms once raw output values are forgotten?

## Synthesis after exploration 70

The attempted “transition refinement” line has now hit a real wall: even full raw radius-2 windows do not determine the forced output across the observed shadow-cycle families. That means the right universal object for the Escape Lemma is not a transition table at all. The load-bearing invariant is escape behavior. So the next productive move is to turn the stabilized 45 centered-local-context classes into a proof-facing catalog, grouped by escape mechanism rather than by target state.

## Exploration 71

### Strategy
Build a proof-facing catalog of the 45 stabilized centered local-context escape classes from the updated `n <= 9` summary, then inspect the catalog to see whether the residual output ambiguity is confined to a small structural subgroup.

### Outcome
SUCCEEDED

### Failure Constraint
N/A

### What This Rules Out
- The residual output ambiguity is not spread uniformly across the 45 centered local-context classes. Any proof outline that treats all classes as equally complicated is too coarse and will waste effort on deterministic cases that are already structurally clean.

### Surviving Structure
- The centered local-context catalog has exactly 45 classes, grouped by centered `m`-triple as:
  - `(2,2,2)`: `2`
  - `(2,2,3)`: `3`
  - `(2,3,2)`: `6`
  - `(2,3,3)`: `5`
  - `(3,2,2)`: `6`
  - `(3,2,3)`: `9`
  - `(3,3,2)`: `8`
  - `(3,3,3)`: `6`
- Exactly 9 of the 45 centered local-context classes have multiple observed forced outputs across the aggregated uniform-sweep families.
- Those 9 ambiguous classes are confined to ternary-centered contexts, specifically:
  - `(2,3,2)` with state triples `(1,0,0)` and `(1,0,1)`
  - `(2,3,3)` with state triple `(1,0,0)`
  - `(3,3,2)` with state triples `(1,0,0)`, `(1,0,1)`, `(2,0,0)`, `(2,0,1)`
  - `(3,3,3)` with state triples `(1,0,0)` and `(2,0,0)`
- All binary-centered centered local-context classes in the catalog are output-deterministic across the observed data.

### Reformulations
- The centered local-context classification is now usable as a two-tier proof object:
  1. first split by centered `m`-triple,
  2. then handle the 9 ambiguous ternary-centered state triples separately from the remaining 36 deterministic classes.

LOAD-BEARING ASSESSMENT: High. This is the first compact decomposition that isolates every residual complication into a 9-class ternary-centered residue.

### Concrete Artifacts
TOOLS:
- New script: `scripts/escape_context_catalog.py`.
  - Input: JSON from `scripts/extract_escape_local_types.py`
  - Output:
    - `scripts/escape_center_local_context_catalog.json`
    - `scripts/escape_center_local_context_catalog.md`

COMPUTED EXAMPLES:
- `python3 scripts/escape_context_catalog.py`
  writes the 45-class catalog and prints the centered `m`-triple group counts listed above.
- The 9 ambiguous centered local-context classes extracted from the catalog are:
  - `((2,3,2),(1,0,0))`
  - `((2,3,2),(1,0,1))`
  - `((2,3,3),(1,0,0))`
  - `((3,3,2),(1,0,0))`
  - `((3,3,2),(1,0,1))`
  - `((3,3,2),(2,0,0))`
  - `((3,3,2),(2,0,1))`
  - `((3,3,3),(1,0,0))`
  - `((3,3,3),(2,0,0))`

STRUCTURAL RESULTS:
- The residual output ambiguity inside the centered local-context quotient is entirely ternary-centered.
- All binary-centered centered local-context classes are deterministic across the observed `n <= 9` data.

REPRESENTATIONS:
- Proof-facing centered local-context catalog:
  - `scripts/escape_center_local_context_catalog.json`
  - `scripts/escape_center_local_context_catalog.md`

### What Would Unblock This
- Collapse the 45-class catalog further by forgetting output values and grouping classes by a smaller number of genuine escape mechanisms.
- The smallest useful next computation is to compare the 9 ambiguous ternary-centered classes against the 36 deterministic ones and test whether they still share the same centered-escape witness pattern under a coarser symbolic grouping.

### Key Parameters
- Source `n`-values in the catalog: `5,6,7,8,9`.
- Total centered local-context classes: `45`.
- Output-ambiguous centered local-context classes: `9`.
- Centered `m`-triple group sizes: `2,3,6,5,6,9,8,6`.

### Open Questions
- How many distinct escape mechanisms remain after forgetting forced-output labels?
- Do the 9 ambiguous ternary-centered classes split into more than one escape mechanism, or are they all the same proof case with different target states?
- Can the deterministic 36 classes be compressed to a short symbolic table by centered `m`-triple and a few state motifs?

## Synthesis after exploration 71

The escape-classification problem is now sharply reduced. The finite object is no longer a vague hope: it is a concrete 45-class catalog with a visibly small hard core. All residual transition ambiguity is isolated in 9 ternary-centered classes, while the other 36 classes are deterministic across the observed uniform-sweep families. This suggests a proof architecture with three layers: a bulk deterministic table, a 9-class ternary residue where output labels vary but centered escape persists, and a top-level argument that the Escape Lemma only needs the escape witness, not the target label.

## Exploration 72 (probe)

### Strategy
Test whether the 45 centered local-context classes collapse further if ternary state labels are forgotten and only the centered `0` versus nonzero pattern is retained alongside the centered `m`-triple.

### Outcome
SUCCEEDED

### Concrete Artifacts
STRUCTURAL RESULTS:
- The centered `0/nonzero` quotient has `24` observed classes across `n = 5..9`.
- Class counts by `n` in the exact uniform-sweep dataset are:
  - `n = 5`: `16`
  - `n = 6`: `24`
  - `n = 7`: `24`
  - `n = 8`: `24`
  - canonical `n = 9`: `12`
- No new centered `0/nonzero` classes appear after `n = 6` in the observed range.
- The output-ambiguous residue shrinks from `9` centered local-context classes to `6` centered `0/nonzero` classes.

COMPUTED EXAMPLES:
- The centered `0/nonzero` quotient keeps keys of the form
  `((m_{i-1},m_i,m_{i+1}), (z_{i-1},z_i,z_{i+1}))`
  where `z_j = 0` if `p_j = 0` and `z_j = 1` otherwise.

### Open Questions
- Do the 6 ambiguous centered `0/nonzero` classes still reduce further under a symbolic “escape mechanism” quotient?
- Is the `0/nonzero` quotient already sufficient for a finite manual Escape Lemma proof?

## Synthesis after exploration 72

The centered local data is compressing in the direction one would want for a proof. Forgetting literal ternary labels does not break stabilization; it improves it. The catalog now looks like a 24-class escape object with a 6-class ambiguous ternary residue. That is small enough that the next step should be to make this quotient explicit in the extractor and treat it as the default proof-facing summary, alongside the older 45-class centered local-context catalog.

## Exploration 73

### Strategy
Pivot from the now-closed Escape Lemma to the upper-bound family program: read the hardcoded `n = 5..8` witnesses, extract their local `m`-triples and canonicalized rule tables, test whether any existing witness already supplies a `(3,3,3)` bulk ternary table `T*`, and build a first reusable family-report script with a provisional one-bulk sanity test.

### Outcome
SUCCEEDED

### Failure Constraint
The proved witnesses do not contain any `(3,3,3)` processors at all, so the proposed bulk table `T*` cannot be extracted directly from `n = 5..8`. In addition, the conjectured family orientation `(2,2,2,4,3,3,...,3)` is not the same rotation/reflection branch as the proved `n = 7` and `n = 8` witnesses.

### What This Rules Out
- Any direct “read off `T*` from the proved witnesses” approach is blocked immediately, because there is no interior `(3,3,3)` data in the known witnesses.
- Any argument that the conjectured family is already visible in the proved `n = 7,8` witnesses up to cyclic symmetry is ruled out.
- The natural bulk guess “use the Dijkstra-solution-3 middle rule on the ternary bulk” is ruled out for the one-bulk family with `n = 6` boundaries, since it fails liveness already at `n = 7`.

### Surviving Structure
- Target-orientation membership:
  - `n = 5`: the witness `(2,2,2,3,4)` matches the length-5 target pattern up to symmetry.
  - `n = 6`: the witness `(2,2,2,4,3,3)` is exactly the proposed family boundary case.
  - `n = 7`: the witness `(3,2,2,2,3,4,3)` is **not** a rotation/reflection of `(2,2,2,4,3,3,3)`.
  - `n = 8`: the witness `(2,2,3,4,3,3,2,3)` is **not** a rotation/reflection of `(2,2,2,4,3,3,3,3)`.
- Local-triple inventory of the proved witnesses:
  - no processor with triple `(3,3,3)` appears in any of `n = 5,6,7,8`,
  - so there is no direct sample of an interior bulk ternary rule.
- Canonicalized same-triple comparisons across the proved witnesses:
  - even after ternary relabeling, all repeated local triples tested so far remain non-identical across `n`, including
    `(3,2,2)`, `(3,3,2)`, `(4,3,3)`, `(2,2,3)`, `(2,3,4)`, and `(3,4,3)`.
- One-bulk family sanity test with `n = 6` boundaries and provisional bulk rule = Dijkstra-solution-3 middle processor:
  - `n = 7`: fails liveness at `(1,1,1,2,1,1,0)`
  - `n = 8`: fails liveness at `(1,1,1,2,1,1,1,0)`
  - `n = 9`: fails liveness at `(1,1,1,2,1,1,1,1,0)`
  - `n = 10`: fails liveness at `(1,1,1,2,1,1,1,1,1,0)`

### Reformulations
- The upper-bound synthesis problem now splits cleanly into:
  1. what the proved witnesses actually determine (`n = 6` boundary tables, local-triple incidence, symmetry branch),
  2. what must be synthesized from scratch (the interior bulk rule `T*`, and possibly even some boundary adaptation).
- This is better than treating the known witnesses as if they already instantiate the family. They do not.

LOAD-BEARING ASSESSMENT: High. This prevents wasting time on a nonexistent direct-extraction path and gives a precise starting point for the shared-bulk SMT fallback.

### Concrete Artifacts
TOOLS:
- New script: `scripts/upper_bound_family.py`.
  - Reports witness local triples for `n = 5..8`
  - Checks rotation/reflection membership in the conjectured family orientation
  - Canonicalizes repeated local-triple rule tables across witnesses
  - Assembles the one-bulk family with `n = 6` boundaries
  - Can run a quick verifier ladder for provisional bulk candidates

COMPUTED EXAMPLES:
- `python3 scripts/upper_bound_family.py --json-out scripts/upper_bound_family_report.json --test-dijkstra3-middle`
  produced the extraction report above and ruled out the Dijkstra-3-middle bulk candidate on `n = 7..10`.

STRUCTURAL RESULTS:
- No `(3,3,3)` processors occur in the proved `n = 5..8` witnesses.
- The conjectured family orientation is new from `n = 7` onward.
- Same-triple boundary rules do not stabilize canonically across the known witnesses.

REPRESENTATIONS:
- `scripts/upper_bound_family_report.json`

### What Would Unblock This
- A constrained synthesis step that fixes the `n = 6` boundary tables and solves for a shared interior ternary table on the target family state counts, starting at `n = 9`.
- The smallest useful next computation is a bounded good-cycle plus SMT-completion search on `(2,2,2,4,3,3,3,3,3)` with all bulk processors tied to one 27-entry table.

### Key Parameters
- Proved witnesses read: `n = 5,6,7,8`.
- `(3,3,3)` processors found: `0`.
- One-bulk Dijkstra-3-middle candidate tested on `n = 7,8,9,10`: fails all four cases at liveness.

### Open Questions
- Can a shared-bulk `T*` exist with the `n = 6` boundaries, or must the family relax one of the boundary tables as well?
- What bounded good-cycle lengths are plausible for the `n = 9` target family?
- Is the first successful synthesis more likely to be one-bulk, period-2 bulk, or one-bulk plus end correction?

## Synthesis after exploration 73

The upper-bound family is now clearly a synthesis problem, not a normalization problem. The known witnesses do not contain the bulk table we want, and from `n = 7` onward they do not even sit on the conjectured orientation branch. That makes the right next move explicit: stop trying to read the family out of the existing witnesses and instead use them only to fix the plausible boundary data and to rule out cheap bulk guesses. The first real target is therefore a shared-bulk constrained search at `n = 9`, with the new report script acting as the extraction front-end.

## Exploration 74 (probe)

### Strategy
Implement a bounded one-bulk synthesizer for the `n = 9` target family that fixes the `n = 6` boundary tables, ties every interior ternary to one shared 27-entry table, and searches for a bounded locally consistent cycle before verifying the resulting full system.

### Outcome
STALLED

### Concrete Artifacts
TOOLS:
- New script: `scripts/family_one_bulk_search.py`.
  - family state counts fixed to `(2,2,2,4,3,3,3,3,3)` when `n = 9`
  - boundary processors fixed from the `n = 6` witness
  - bulk processors `P5,P6,P7` tied to one shared 27-entry table
  - candidate bulk tables verified as full systems with `verify_system`

COMPUTED EXAMPLES:
- `python3 scripts/family_one_bulk_search.py --n 9 --length-from 35 --length-to 40 --timeout-ms 2000 --max-models 3`
  returned only timeouts:
  - length `35`: unknown / timeout
  - length `36`: unknown / timeout
  - length `37`: unknown / timeout
  - length `38`: unknown / timeout
  - length `39`: unknown / timeout
  - length `40`: unknown / timeout

### What Would Unblock This
- A better bounded-cycle seed: either a narrower plausible length range or an informed mover-pattern constraint.
- Alternatively, a higher-timeout run on the current one-bulk synthesizer, now that the family constraints are encoded.

### Open Questions
- Is the correct `n = 9` family cycle length near the `35..40` band, or are we searching the wrong window entirely?
- Does the one-bulk hypothesis need a mover-sequence seed before the cycle search becomes tractable?

## Synthesis after exploration 74

The constrained search infrastructure is now real; the bottleneck has moved to bounded good-cycle synthesis under the family constraints. This is a computational stall, not a conceptual one. The next productive move is not more witness normalization, but a more informed cycle search for the one-bulk `n = 9` family — either by seeding mover structure or by probing a better length band.

## Exploration 75

### Strategy
Attack the smallest nontrivial family case `n = 7` under the one-bulk hypothesis with increasingly structured mover seeds: first the known `n = 7` witness mover sequences, then the exact `n = 6` block-witness mover sequence, then a 125-pattern family of local replacements around the old terminal ternary moves, and finally an SMT model where the `n = 7` mover sequence is any interleaving of extra bulk-processor moves into the `n = 6` block-witness schedule.

### Outcome
SUCCEEDED

### Failure Constraint
With `P0..P4` and `P6` fixed from the `n = 6` witness and a single shared bulk table at `P5`, the cleanest schedule-level extensions of the `n = 6` block witness are impossible at `n = 7`. The obstruction appears already at the locally consistent-cycle stage, before full-system verification.

### What This Rules Out
- The one-bulk family is not going to emerge from a simple deformation of the `n = 6` block witness dynamics while keeping the `n = 6` boundaries fixed.
- In particular, any family proof strategy that assumes the recurrent mover schedule at `n = 7` is just “the `n = 6` schedule plus a few inserted bulk moves” will hit the same obstruction.
- The target `n = 7` family also does not inherit either known `n = 7` witness mover sequence.

### Surviving Structure
- Known witness-sequence incompatibility at the target `n = 7` family state counts `(2,2,2,4,3,3,3)`:
  - `n7-1152` mover sequence, length `41`: no locally consistent good cycle exists.
  - `n7-864` mover sequence, length `52`: no locally consistent good cycle exists.
  - `n6-288-block` mover sequence, length `35`: no locally consistent good cycle exists.
- One-bulk fixed-seed replacement family from the `n = 6` block witness:
  - replace each old processor-`5` move by one of
    `(6)`, `(5,6)`, `(6,5)`, `(5,6,5)`, `(6,5,6)`,
  - across all `5^3 = 125` choices,
  - every resulting seed is negative under the one-bulk family constraints.
- Interleaved-extension model:
  - mover sequence projected onto the old processors must equal the `n = 6` block-witness schedule after relabeling the old final ternary to the new boundary processor,
  - extra moves are allowed only from the new bulk processor,
  - and this model is UNSAT for every tested length `36..60`.

### Reformulations
- The family synthesis problem now has a genuine schedule-level obstruction, not just a table-level one.
- That means the next hypothesis class should change the family template itself:
  1. period-2 bulk tables, or
  2. one-bulk plus boundary correction,
  rather than continuing to vary only the good-cycle seed under the same fixed-boundary one-bulk model.

LOAD-BEARING ASSESSMENT: High. This narrows the upper-bound search to a materially smaller set of plausible family hypotheses.

### Concrete Artifacts
TOOLS:
- `scripts/family_one_bulk_search.py` now supports:
  - `--movers` for fixed-sequence family checks,
  - `--interleave-n6-block` for the interleaved extension model.

COMPUTED EXAMPLES:
- `python3 scripts/p2_seeded_cycle_search.py 2,2,2,4,3,3,3 --witness n7-1152 --skip-completion --cycle-timeout-ms 5000`
  reports no locally consistent good cycle.
- `python3 scripts/p2_seeded_cycle_search.py 2,2,2,4,3,3,3 --witness n7-864 --skip-completion --cycle-timeout-ms 5000`
  reports no locally consistent good cycle.
- `python3 scripts/p2_seeded_cycle_search.py 2,2,2,4,3,3,3 --witness n6-288-block --skip-completion --cycle-timeout-ms 5000`
  reports no locally consistent good cycle.
- The 125 fixed-seed replacements around the old terminal ternary all return
  `no family cycle found for fixed mover sequence`.
- `python3 scripts/family_one_bulk_search.py --n 7 --length-from 36 --length-to 60 --timeout-ms 2000 --max-models 2 --interleave-n6-block`
  reports `no interleaved family cycle found` for every length `36..60`.

STRUCTURAL RESULTS:
- The target `n = 7` one-bulk family does not inherit any currently known witness dynamics.
- The rigid “insert extra bulk moves into the `n = 6` block schedule” model is false through length `60`.

### What Would Unblock This
- A generalized family synthesizer that allows either:
  - period-2 bulk tables, or
  - a corrected `P4` and/or `P(n-1)` boundary ternary,
  while still using the schedule-level seed models that were informative here.

### Key Parameters
- Target family case tested: `n = 7`, state counts `(2,2,2,4,3,3,3)`.
- Interleaving length band ruled out: `36..60`.
- Local replacement seed family ruled out: all `125` choices from the five short replacement patterns above.

### Open Questions
- Is the correct family hypothesis “one bulk plus last-boundary correction,” “one bulk plus `P4` correction,” or truly period-2 bulk?
- Does the `n = 7` target family admit *any* good cycle with fixed `P0..P3` from `n = 6`?
- If a boundary correction is needed at `n = 7`, does it stabilize once the first interior `(3,3,3)` processor appears?

## Synthesis after exploration 75

The one-bulk fixed-boundary hypothesis is no longer vague; it has taken several strong hits at `n = 7`. Not only do the known witness mover sequences fail, but the entire natural deformation cone around the `n = 6` block dynamics fails too. So the next move is not a wider search over the same model. The family template itself now has to bend: either the bulk must alternate, or one of the ternary boundary gadgets must change. That is a real structural narrowing of the upper-bound problem.

## Exploration 76

### Strategy
Abandon the `n = 6`-anchored target family and instead normalize the proved optimal `n = 6,7,8` witnesses into a genuine insertion chain, then search the induced `n = 9` family directly.

The normalized product-optimal orientations line up as:
- `n = 6`: `(2,2,4,3,3,2)`
- `n = 7`: `(2,2,3,4,3,3,2)`
- `n = 8`: `(2,2,3,4,3,3,2,3)`

This suggests the tail family
`(2,2,3,4,3,3,2) + (3)^(n-7)`,
equivalently `(2,2,3,4,3,3,2,3,3,...)`.

### Outcome
SUCCEEDED

### New Family Hypothesis
Use the `n = 8` optimal witness as the frozen prefix gadget:
- `P0..P6` copied from the `n = 8` witness
- `P7` becomes a corrected ternary with local triple `(2,3,3)`
- `P8..P(n-2)` are the bulk ternaries with local triple `(3,3,3)` when `n >= 10`
- `P(n-1)` reuses the old `n = 8` terminal ternary role `(3,3,2)` unless freed

This is the first upper-bound family template that is actually suggested by the proved optimal witnesses themselves.

### Concrete Artifacts
TOOLS:
- New script: `scripts/family_tail_search.py`.
  - family state counts: `(2,2,3,4,3,3,2) + (3,) * (n-7)`
  - frozen `n = 8` prefix rules at `P0..P6`
  - free corrected ternary `P7 : (2,3,3)`
  - optional one/period-2 bulk tables on `(3,3,3)` for `n >= 10`
  - optional free last ternary `(3,3,2)`
  - interleaved mover search driven by the `n = 8` witness prefix movers on processors `0..6`
  - fixed mover search via `--movers`
- New script: `scripts/family_tail_cone_scan.py`.
  - resumable scanners for fixed-schedule cones around the `n = 8` tail dynamics
  - `--mode nonuniform` scans the full independent replacement cone on the four old `P7` occurrences
  - `--mode extra-single-8` adds one genuinely new `P8` insertion gap on top of a nonuniform replacement pattern

STRUCTURAL DATA:
- The `n = 8` frozen-prefix mover subsequence on processors `0..6` has length `51`:
  `(0,1,2,1,2,3,2,3,2,1,2,3,3,2,3,4,3,2,1,2,3,4,5,4,3,3,2,3,2,1,2,3,3,2,3,4,3,4,5,6,6,0,1,2,3,2,3,4,5,6,6)`.

COMPUTED EXAMPLES:
- Symbolic interleaving on the `n = 9` tail family `(2,2,3,4,3,3,2,3,3)`:
  - `python3 scripts/family_tail_search.py --n 9 --length-from 53 --length-to 60 --timeout-ms 2000 --max-models 2`
  - `python3 scripts/family_tail_search.py --n 9 --length-from 53 --length-to 60 --timeout-ms 2000 --max-models 2 --free-last`
  - every tested length `53..60` returned `unknown / timeout`

- Fixed-mover local insertion samples using the exact `n = 8` mover sequence and inserting one new `P8` move:
  - sampled insertion positions `0,5,10,15,20,25,30,35,40,45,50,55`
  - all sampled cases are UNSAT both with fixed last rule and with `--free-last`

- Fixed-mover local insertion samples with two new `P8` moves:
  - sampled insertion pairs `(0,28),(5,30),(10,35),(15,40),(20,45),(25,50),(0,55),(12,55),(24,55),(36,55)`
  - all sampled cases are UNSAT both with fixed last rule and with `--free-last`

- Uniform local replacements of every old `P7` move in the `n = 8` schedule:
  - replacement words `(7,8)`, `(8,7)`, `(7,8,7)`, `(8,7,8)`
  - all four uniform replacement families are UNSAT both with fixed last rule and with `--free-last`

- Non-uniform local replacements of the four old `P7` moves in the `n = 8` schedule:
  - each occurrence independently chosen from `(7,8)`, `(8,7)`, `(7,8,7)`, `(8,7,8)`
  - all `256 / 256` patterns are UNSAT with zero solver-unknowns, both with fixed last rule and with `--free-last`

- Symbolic interleaving with bounded consecutive tail moves:
  - `python3 scripts/family_tail_search.py --n 9 --length-from 53 --length-to 60 --timeout-ms 2000 --max-models 2 --max-tail-run 2`
  - `python3 scripts/family_tail_search.py --n 9 --length-from 53 --length-to 60 --timeout-ms 2000 --max-models 2 --max-tail-run 2 --free-last`
  - every tested length `53..60` still returns `unknown / timeout`

- Extra-single-`P8` cone over the nonuniform replacement family:
  - `python3 scripts/family_tail_cone_scan.py --mode extra-single-8 --limit 256 --progress-every 64`
  - `python3 scripts/family_tail_cone_scan.py --mode extra-single-8 --free-last --limit 256 --progress-every 64`
  - checkpoints reached in both variants:
    - `64` cases checked, `0` solver-unknowns, resume at `choice_index = 1`, `gap = 3`
    - `128` cases checked, `0` solver-unknowns, resume at `choice_index = 2`, `gap = 7`

### Failure Constraint
The new tail-family template survives as a state-count hypothesis, but the easiest local schedule deformations of the `n = 8` witness do not extend to `n = 9`.

Concretely, if the `n = 9` tail family is real, its good cycle is not obtained by:
- inserting one or two isolated `P8` moves into the exact `n = 8` mover sequence, or
- replacing every old terminal `P7` move by one fixed short word over `{7,8}`.

### What This Narrows
- The witness-driven tail family is materially more plausible than the earlier `n = 6` target family, but it still faces a schedule-synthesis bottleneck at `n = 9`.
- The bottleneck is now sharper: local tail-gadget deformations of the `n = 8` cycle are already failing, so the surviving space is “global retiming of the old `P7` dynamics plus new `P8` behavior,” not a purely local patch.
- Even bounding the symbolic tail scheduler to runs of at most two consecutive tail moves does not break the timeout barrier, so the remaining search needs stronger discrete schedule control rather than just more local table constraints.
- The first extra-gap batch is also cleanly negative so far, which is early evidence that even “one new tail gap plus arbitrary local rewiring of the old four gaps” may still be too weak.

### What Would Unblock This
- Enumerate the full small local replacement cone around the four old `P7` moves, not just the uniform replacements.
- Add a mixed fixed-schedule generator that preserves the frozen prefix mover subsequence on `0..6` but allows both `P7` and `P8` to vary.
- If that still fails, move from family-first search back to finding an `n = 9` optimal witness in this orientation class and infer the family from it afterward.

### Open Questions
- Does the `n = 9` tail family require a globally different mover schedule, or is there still a short local replacement pattern that works on some subset of the four old `P7` occurrences?
- Once `n >= 10`, does a stable `(3,3,3)` bulk rule appear, or does the corrected-tail effect keep propagating farther than expected?

## Synthesis after exploration 76

The upper-bound search has a better template now. The optimal witnesses themselves point to a family with a frozen `n = 8` prefix and an appended ternary tail, and that is the strongest surviving hypothesis on the table. But the good-cycle dynamics do not extend by the obvious local edits. So the next productive work is no longer “guess a nicer state-count formula”; it is “search the `n = 9` tail family with stronger schedule control,” ideally by explicitly varying the old `P7` occurrences rather than asking Z3 to invent the whole tail schedule at once.

## Exploration 77

### Strategy
Pivot from schedule synthesis to direct recursive prefix-sharded screening on the exact `n = 9` tail-family orientation suggested by the proved witnesses.

The target orientation is
`(2,2,3,4,3,3,2,3,3)`,
which is orientation `30/56` in the `scripts/n9_sweep.py` necklace order.

### Outcome
SUCCEEDED

### Key Structural Result
The exact tail-family orientation is not a cheap dead branch like nearby orientation `31/56`, but it is also not exposing survivors at the first sharded depth. Instead it behaves as a sparse recursive prefix tree, with the mass concentrated in a small set of explicit prefixes and no survivors anywhere seen so far.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Sweep-order identification:
  - `python3 - <<'PY' ... distinct_necklaces((2,2,2,4,3,3,3,3,3)) ...`
  - tail-family orientation `(2,2,3,4,3,3,2,3,3)` is `30/56`

- First-level sharded screen on the exact tail-family orientation:
  - `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,2,3,3 --prefix-length 1 --time-limit 600 --max-cycles 50000000 --max-workers 9`
  - result:
    - `prefix=3 screened=8126 survivors=0`
    - `prefix=2 screened=6742 survivors=0`
    - `prefix=4 screened=6732 survivors=0`
    - `prefix=5 screened=445 survivors=0`
    - `prefix=6 screened=3 survivors=0`
    - `prefix=7 screened=1 survivors=0`
    - `prefix=0,1,8 screened=0 survivors=0`
    - total `screened=22049 survivors=0`

- Adjacent orientations in the necklace:
  - `29/56 = (2,2,3,4,3,2,3,3,3)`:
    - `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,2,3,3,3 --prefix-length 1 --time-limit 600 --max-cycles 50000000 --max-workers 9`
    - total `screened=10776 survivors=0`
    - main mass: `prefix=2 -> 4776`, `prefix=3 -> 3192`, `prefix=1 -> 2187`, `prefix=4 -> 597`
  - `31/56 = (2,2,3,4,3,3,3,2,3)`:
    - `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,3,2,3 --prefix-length 1 --time-limit 600 --max-cycles 50000000 --max-workers 9`
    - total `screened=2 survivors=0`
    - only `prefix=6` and `prefix=7` contribute `1` cycle each

- Second-level split on the three heavy first-mover branches of orientation `30/56`:
  - `--base-prefix 3`:
    - live children only `3,2 -> 5353`, `3,3 -> 4429`, `3,4 -> 1183`
    - all other second movers die immediately
  - `--base-prefix 2`:
    - live children only `2,1 -> 3916`, `2,2 -> 2252`, `2,3 -> 214`
    - all other second movers die immediately
  - `--base-prefix 4`:
    - live children only `4,3 -> 4836`, `4,4 -> 2458`, `4,5 -> 344`
    - all other second movers die immediately

- Deeper recursion on the heaviest residue of orientation `30/56`:
  - `--base-prefix 3,2`:
    - live children only `3,2,1 -> 5089`, `3,2,2 -> 3859`, `3,2,3 -> 2046`
  - `--base-prefix 4,3`:
    - live children only `4,3,2 -> 6183`, `4,3,3 -> 635`, `4,3,4 -> 280`
  - `--base-prefix 3,2,1`:
    - unique live child `3,2,1,0 -> 6681`
  - `--base-prefix 3,2,1,0`:
    - unique live child `3,2,1,0,8 -> 7560`
  - `--base-prefix 3,2,1,0,8`:
    - live children `3,2,1,0,8,0 -> 9015`,
      `3,2,1,0,8,7 -> 10128`,
      `3,2,1,0,8,8 -> 9987`

No survivor cycle has appeared anywhere in this exploration, so there was no SMT completion to run.

### Failure Constraint
The tail-family orientation is not positive at the first several sharded depths, but it is also not flattening out the way nearby orientation `31/56` does. The search mass organizes into a very small recursive prefix tree.

### What This Narrows
- The exact witness-predicted orientation `30/56` is the right active `n = 9` target in this neighborhood: it is much heavier than `31/56` and materially heavier than `29/56`.
- The search is no longer “try nearby rotations.” It is “recurse on the explicit live prefixes inside orientation `30/56`.”
- The strongest current spine is
  `3 -> 2 -> 1 -> 0 -> 8`,
  after which the residue branches again into exactly three children.

### What Would Unblock This
- Continue recursive sharding on the live residue of orientation `30/56`, prioritizing:
  - `3,2,1,0,8,7`
  - `3,2,1,0,8,8`
  - `3,2,1,0,8,0`
  - `4,3,2`
- If a survivor appears at any of those nodes, rerun `p2_cycle_screen.py` on that exact prefix and pass the resulting cycle straight to SMT completion.

### Open Questions
- Does the main tail-family spine eventually collapse to zero, or does one of the three children under `3,2,1,0,8` finally produce a survivor?
- Is the cross-check branch `4,3,2` a genuine alternative residue, or will it collapse more quickly than the `3,2,1,0,8,*` family?

## Synthesis after exploration 77

The tail-family orientation is now the clearest `n = 9` bottleneck in the whole product-7776 necklace neighborhood. It is not just “some heavy orientation”; it is a sparse recursive prefix tree with an explicit dominant spine and a finite live residue. That is a much better place to be than the earlier schedule-synthesis stall. The next productive work is not more family templating. It is straightforward recursive sharding on the live prefixes of orientation `30/56`, with SMT ready the moment a survivor finally appears.

## Exploration 78

### Strategy
Continue recursive sharding only on the live residue of the dominant tail-family spine inside orientation `30/56`, namely the three children under
`3,2,1,0,8`.

### Outcome
SUCCEEDED

### Key Structural Result
The live residue under the dominant spine remains extremely sparse:
- `3,2,1,0,8,0` has a unique live child `8`
- `3,2,1,0,8,8` has a unique live child `7`
- `3,2,1,0,8,7` has exactly two live children, `6` and `7`

No survivor appears anywhere in this continuation.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,2,3,3 --base-prefix 3,2,1,0,8,0 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
  - immediate dead children: `0,1,2,3,4,5,6,7`
  - unique live child: `3,2,1,0,8,0,8 -> 7074`
  - total `screened=7074 survivors=0`

- `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,2,3,3 --base-prefix 3,2,1,0,8,8 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
  - immediate dead children: `0,1,2,3,4,5,6,8`
  - unique live child: `3,2,1,0,8,8,7 -> 7872`
  - total `screened=7872 survivors=0`

- `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,2,3,3 --base-prefix 3,2,1,0,8,7 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
  - immediate dead children: `0,1,2,3,4,5`
  - dead-at-budget child: `8 -> 0`
  - live children:
    - `3,2,1,0,8,7,6 -> 7947`
    - `3,2,1,0,8,7,7 -> 7937`
  - total `screened=15884 survivors=0`

### What This Narrows
- The dominant tail-family residue is no longer a vague “hard branch.” It is already reduced to the explicit frontier:
  - `3,2,1,0,8,0,8`
  - `3,2,1,0,8,8,7`
  - `3,2,1,0,8,7,6`
  - `3,2,1,0,8,7,7`
- Two of those four fronts are unique-child spines, so the recursion is still collapsing rather than widening.

### What Would Unblock This
- Continue recursive sharding on exactly the four live depth-seven fronts above.
- The moment any one of them yields `survivors > 0`, rerun `p2_cycle_screen.py` on that exact prefix and hand the cycle to SMT completion immediately.

### Open Questions
- Do the two unique-child spines eventually terminate, or do they hide the first actual survivor deeper in the tree?
- Are `3,2,1,0,8,7,6` and `3,2,1,0,8,7,7` genuinely distinct residues, or will they collapse to the same local anatomy one depth lower?

## Synthesis after exploration 78

The exact tail-family orientation is now under control in the same sense that the old `16/17` block eventually was: not solved, but reduced to a tiny explicit frontier. The active `n = 9` search is no longer an orientation sweep and no longer a family-synthesis problem. It is four concrete recursive prefixes, all inside orientation `30/56`, with zero survivors so far and a clear trigger for SMT the moment one appears.

## Exploration 79

### Strategy
Continue recursive sharding on the four live depth-7 fronts requested for orientation `30/56`:
- `3,2,1,0,8,0,8`
- `3,2,1,0,8,8,7`
- `3,2,1,0,8,7,6`
- `3,2,1,0,8,7,7`

### Outcome
SUCCEEDED

### Key Structural Result
All four requested fronts remain survivor-free, and three of the four collapse immediately to unique-child spines:
- `3,2,1,0,8,0,8 -> 7`
- `3,2,1,0,8,7,6 -> 5`
- `3,2,1,0,8,7,7 -> 6`

The remaining front
`3,2,1,0,8,8,7`
splits into exactly two live children:
- `3,2,1,0,8,8,7,6`
- `3,2,1,0,8,8,7,7`

No survivor appears anywhere, so there was no SMT completion to run.

### Concrete Artifacts
COMPUTED EXAMPLES:
- `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,2,3,3 --base-prefix 3,2,1,0,8,0,8 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
  - immediate dead children: `0,1,2,3,4,5,6,8`
  - unique live child: `3,2,1,0,8,0,8,7 -> 5319`
  - total `screened=5319 survivors=0`

- `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,2,3,3 --base-prefix 3,2,1,0,8,7,6 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
  - immediate dead children: `0,1,2,3,4,6,7,8`
  - unique live child: `3,2,1,0,8,7,6,5 -> 6089`
  - total `screened=6089 survivors=0`

- `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,2,3,3 --base-prefix 3,2,1,0,8,7,7 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
  - immediate dead children: `0,1,2,3,4,5,7,8`
  - unique live child: `3,2,1,0,8,7,7,6 -> 6014`
  - total `screened=6014 survivors=0`

- `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,2,3,3 --base-prefix 3,2,1,0,8,8,7 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
  - immediate dead children: `0,1,2,3,4,5`
  - dead-at-budget child: `8 -> 0`
  - live children:
    - `3,2,1,0,8,8,7,6 -> 5971`
    - `3,2,1,0,8,8,7,7 -> 5927`
  - total `screened=11898 survivors=0`

### What This Narrows
- The active frontier inside orientation `30/56` is now exactly:
  - `3,2,1,0,8,0,8,7`
  - `3,2,1,0,8,7,6,5`
  - `3,2,1,0,8,7,7,6`
  - `3,2,1,0,8,8,7,6`
  - `3,2,1,0,8,8,7,7`
- Four of the five active fronts are unique-child spines inherited from a still-collapsing tree.

### What Would Unblock This
- Continue recursive sharding on exactly the five active depth-9 fronts above.
- Keep SMT idle until a front first reports `survivors > 0`; then rerun `p2_cycle_screen.py` on that exact prefix and complete it immediately.

### Open Questions
- Do the four unique-child spines terminate cleanly, or do they hide the first survivor deeper in the tree?
- Will the split pair `3,2,1,0,8,8,7,{6,7}` stay genuinely bifurcated one level deeper, or collapse back to a spine?

## Synthesis after exploration 79

The tail-family orientation has now been reduced to a handful of explicit deep prefixes, all inside a single recursive branch family and all still negative. The search state is no longer diffuse at all. It is a concrete frontier of five depth-9 prefixes, with no ambiguity about what to do next and no need to widen back to other orientations unless this exact frontier finally dies.

## Exploration 80

### Strategy
After the product-7776 family was swept negative by orientation, pivot to the next product frontiers for `n = 9`: exhaust the exact lower-bound candidate family `(2,2,3,3,3,3,3,3,3)` at first sharded depth, then test witness-guided local blocks in the next two families `(2,2,2,5,3,3,3,3,3)` and `(2,2,2,4,4,3,3,3,3)`, recursing one level deeper only on the hottest new residue.

### Outcome
SUCCEEDED

### Failure Constraint
The exact boundary candidate at product `8748` does not expose even a single first-level survivor in any of its four necklace orientations under the standard `n = 9` sharded screen. The witness-guided local `9720` block is even colder. The first nearby family that restores substantial search mass is product `10368`, but even there the mass immediately collapses to a sparse recursive residue with no survivors at depth 1 or 2 in the hottest tested branch.

### What This Rules Out
- Any hope that `M_9 = 8748` will surface as an easy witness in the almost-uniform family under the established prefix-sharded screen.
- Any search policy that prioritizes product `9720` over product `10368` purely because it is numerically smaller. In the witness-adjacent block, `9720` is much colder than the best tested `10368` orientation.
- Any need to broad-sweep all `56` or `140` higher-product orientations before testing the witness-preserving local blocks. The local transfer heuristic already separates cold and hot families sharply.

### Surviving Structure
- Product `8748` is not uniformly trivial: two of its four orientations are very sparse, but two are still heavy enough to warrant possible later recursion if all smaller-product alternatives die.
- Product `9720` retains one modest residue in the witness-adjacent block, namely orientation `29/56` under first mover `8`, but nothing else tested there looks active.
- Product `10368` orientation `57/140 = (2,2,3,4,3,3,2,3,4)` is currently the hottest explicit new frontier above `8748`. Its first-level residue sits almost entirely in movers `3,4,2`, and the heaviest child `3` immediately collapses to exactly three live grandchildren `3,2`, `3,3`, `3,4`.

### Reformulations
- The most effective way to compare nearby product frontiers is no longer “sort by product and sweep.” It is “transfer the witness-guided local block first, then recurse only where the sharded screen says the mass still lives.”

LOAD-BEARING ASSESSMENT: Moderate. This is operational rather than a proof reformulation, but it prevented a very expensive blind orientation sweep and immediately identified a new hottest branch.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Full first-level sweep of the product-`8748` family `(2,2,3,3,3,3,3,3,3)` over all four distinct necklace orientations, always with
  `python3 scripts/p2_prefix_batch.py ... --prefix-length 1 --time-limit 600 --max-cycles 50000000 --max-workers 9`.
  Results:
  - `(2,2,3,3,3,3,3,3,3)`: total `screened=309 survivors=0`, heaviest prefixes `3 -> 177`, `2 -> 66`, `4 -> 38`
  - `(2,3,2,3,3,3,3,3,3)`: total `screened=10845 survivors=0`, heaviest prefixes `8 -> 5274`, `0 -> 5147`
  - `(2,3,3,2,3,3,3,3,3)`: total `screened=145 survivors=0`, heaviest prefixes `3 -> 51`, `5 -> 48`, `6 -> 22`
  - `(2,3,3,3,2,3,3,3,3)`: total `screened=12260 survivors=0`, heaviest prefixes `8 -> 5827`, `0 -> 5791`, `5 -> 600`

- Witness-adjacent local block in the product-`9720` family:
  - `30/56 = (2,2,3,5,3,3,2,3,3)`: total `screened=7 survivors=0`
  - `29/56 = (2,2,3,5,3,2,3,3,3)`: total `screened=916 survivors=0`, dominated by `prefix=8 -> 886`
  - `31/56 = (2,2,3,5,3,3,3,2,3)`: total `screened=2 survivors=0`

- Tail-preserving probe in the product-`10368` family:
  - `57/140 = (2,2,3,4,3,3,2,3,4)`:
    - first level: total `screened=16821 survivors=0`
    - dominant prefixes: `3 -> 5639`, `4 -> 5232`, `2 -> 5150`, then `5 -> 592`, `6 -> 158`
  - depth-2 split of the hottest branch:
    - `python3 scripts/p2_prefix_batch.py 2,2,3,4,3,3,2,3,4 --base-prefix 3 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
    - immediate dead children: `3,0`, `3,1`, `3,5`, `3,6`, `3,7`, `3,8`
    - live children only:
      - `3,2 -> 5775`
      - `3,3 -> 4451`
      - `3,4 -> 1183`
    - total `screened=11409 survivors=0`

STRUCTURAL RESULTS:
- The exact lower-bound candidate product `8748` is first-level survivor-free across its entire necklace orbit under the current standard screen.
- The witness-adjacent `9720` block is colder than the best tested `8748` and `10368` blocks.
- Product `10368` is the first new family above `8748` that restores a large sparse-residue tree resembling the old product-`7776` tail-family behavior.

TOOLS:
- Reused `scripts/p2_prefix_batch.py` as the standard first-level and depth-2 `n = 9` screener.
- Reused `scripts/n9_sweep.py` necklace order to identify witness-adjacent orientation indices:
  - product `9720`: local block `29-31 / 56`
  - product `10368`: tail-preserving orientation `57 / 140`

REPRESENTATIONS:
- Cross-family witness-guided local block: preserve the old tail-family binary placement and local neighborhood when moving to a nearby higher-product multiset, then compare only that local orientation block first.

### What Would Unblock This
- Run the same depth-2 split on product-`10368` orientation `57/140` prefixes `4` and `2`, then recurse on the heaviest of `{3,2, 3,3, 4,?, 2,?}`.
- If all of those stay survivor-free, compare one neighboring tail-preserving `10368` orientation such as `58/140 = (2,2,3,4,3,3,2,4,3)` before widening further.
- If the higher-product branches also stay cold, return to the heavier product-`8748` orientations `(2,3,2,3,3,3,3,3,3)` and `(2,3,3,3,2,3,3,3,3)` and recurse on their dominant first movers `8` and `0`.

### Key Parameters
- Product `8748`: all `4` necklace orientations tested at first depth with `time_limit=600`, `max_cycles=50000000`, `max_workers=9`.
- Product `9720`: witness-adjacent local block `29-31 / 56` tested at first depth with the same parameters.
- Product `10368`: orientation `57 / 140` tested at first depth with the same parameters; depth-2 refinement on base prefix `3` used `time_limit=300`, `max_cycles=50000000`, `max_workers=9`.

### Open Questions
- Does product `10368` orientation `57/140` eventually produce the first actual survivor in one of the branches `3,2`, `3,3`, or one of the symmetric residues under first movers `4` and `2`?
- Is the heavier product-`8748` residue genuinely colder than product `10368`, or just distributed differently at first depth?
- Does product `9720` deserve any follow-up beyond orientation `29/56` / prefix `8`, or is that family effectively dominated already?

## Synthesis after exploration 80

The new frontier has a clear shape now. Product `8748` survives as the sharpest lower-bound target numerically, but not as the hottest active search family: all four necklaces are first-level negative. Product `9720` looks colder still in the witness-adjacent block. Product `10368`, by contrast, immediately recreates the sparse recursive anatomy that was useful in the old product-`7776` tail search. So the next productive move is not a blind widening over more orientations. It is to recurse on the explicit hot residue inside product `10368` orientation `57/140`, while keeping the two heavy product-`8748` necklaces as the lower-product fallback if the `10368` tree also dies.
