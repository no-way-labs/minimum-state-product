# Exploration Log

## Strategy Register

### Eliminated approach classes
- All six current Sol 3 adaptation families (`v1..v6`) are ruled out on the all-safe gap families
  `(2,2,2,3,3,3,3,3,5)`,
  `(2,2,2,3,3,3,3,4,4)`,
  `(2,2,2,3,3,3,3,3,6)`,
  `(2,2,2,3,3,3,3,4,5)`
  across every safe linear orientation tested in exploration 1. Structural reason: none of the `28,728` orientation/variant instances is even graph-valid under `p2_ring.verify_system`, so these mixed-state Sol-3-style bounce families do not realize a witness anywhere in the current all-safe residue.

### Obstructions
- In the gap `8748 < product < 13122`, there are `143` unordered multisets with `n = 9`, all entries at least `2`, and at least two binary processors. Existing Case-2 structure blocks `63` of these in every necklace orientation, leaving only `5` multisets with zero blocked necklaces and `75` mixed families with some blocked and some unblocked necklaces (exploration 1).
- `M_9 >= 8960`, conditional on the same accepted ingredients already used elsewhere in the project: the full product-`8748` family is dead by explicit sweep, and the unique product-`8832` family `(2,2,2,2,2,2,2,3,23)` has `7` binaries, so every orientation contains `4+` consecutive binaries and is blocked by Case 2 (exploration 1).

### Building blocks
- `scripts/n9_gap_inventory.py` (exploration 1): enumerates every unordered gap multiset, computes product, binary count, linear orientation count, necklace count, and the number of necklaces blocked by the `4+` consecutive-binary obstruction.
- `scripts/n9_gap_sol3_scan.py` (exploration 1): scans any selected gap multiset across all distinct linear orientations and any subset of the six Sol 3 adaptation variants, using `p2_ring.verify_system` and running the five-property verifier on any hit.

### Known reformulations
- Gap-inventory split: treat the `n = 9` lower-bound gap not as one product interval but as a finite inventory of multisets classified by three layers:
  1. arithmetic (`<=2` binaries impossible below `13122`),
  2. orientation-level Case-2 blocking (`4+` consecutive binaries),
  3. residual all-safe families that genuinely need computation.
  LOAD-BEARING: high. It turns an amorphous lower-bound gap into a finite explicit residue with only five fully Case-2-safe multisets.

## Session Start (2026-03-09)

Resuming from exploration 0.

No prior `exploration_log_m9_lb.md` existed in the repository, so there is no earlier exploration state to reuse.

Next attempt: inventory every multiset in the `n = 9` gap `(8748, 13122)`, classify them against the existing arithmetic and consecutive-binary obstructions, and then attack the residual families with sweep and bounce-style searches.

## Exploration 1

### Strategy
Enumerate every unordered `n = 9` gap multiset with product in `(8748,13122)` and at least two binaries, classify each family by orientation-level Case-2 coverage, then attack the fully Case-2-safe residue with two computational probes:
- broad bounce-family scans over all six current Sol 3 variants and all safe linear orientations,
- canonical first-level prefix-sharded sweeps on the smallest unresolved all-safe families.

### Outcome
SUCCEEDED

### Failure Constraint
No witness appears in any of the computational probes run so far. The broad Sol-3-family scans are completely negative on the four unresolved all-safe multisets, and the canonical first-level sharded sweeps on three of those families are also survivor-free at the current `300s / 50M / 9-way` budget.

### What This Rules Out
- The all-safe residual families do not admit any witness of the current six Sol 3 adaptation types.
- The smallest fully Case-2-safe gap family `(2,2,2,3,3,3,3,3,5)` is not an easy witness family under either:
  - broad Sol 3 variant scans over all safe linear orientations, or
  - a canonical first-level sharded sweep.
- Likewise, the all-safe families `(2,2,2,3,3,3,3,3,6)` and `(2,2,2,3,3,3,3,4,5)` are not easy witnesses under those same broad Sol 3 and canonical sweep probes.
- The theorem-frontier mixed family `(2,2,2,2,2,2,4,5,7)` at product `8960` does not admit any current Sol 3 variant on any safe linear orientation, and its first sampled safe orientation is also survivor-free at first sharding depth.

### Surviving Structure
- The gap is now explicit:
  - `143` unordered multisets total
  - binary-count histogram:
    - `2`: `1`
    - `3`: `4`
    - `4`: `11`
    - `5`: `23`
    - `6`: `41`
    - `7`: `46`
    - `8`: `17`
- Case-2 coverage at the multiset level:
  - `63` families: every necklace orientation blocked by `4+` consecutive binaries
  - `75` families: mixed, with some blocked and some safe necklaces
  - `5` families: all necklace orientations are Case-2-safe
- The five fully Case-2-safe gap multisets are:
  - product `9720`: `(2,2,2,3,3,3,3,3,5)`
  - product `10368`: `(2,2,2,3,3,3,3,4,4)`
  - product `11664`: `(2,2,3,3,3,3,3,3,4)` (already known orientation-sweep dead from prior work)
  - product `11664`: `(2,2,2,3,3,3,3,3,6)`
  - product `12960`: `(2,2,2,3,3,3,3,4,5)`
- The broad bounce-family residue is now strictly smaller than the structural Case-2 residue: none of the unresolved all-safe families supports a witness from any current Sol 3 variant.
- The very first unresolved product above the new formal lower bound is now `8960`, carried by the mixed family `(2,2,2,2,2,2,4,5,7)`.

### Reformulations
- For lower-bound work in this gap, the right primary object is not “product frontier” but “orientation-safe family residue.” Products like `10368` or `11664` contain several distinct multiset families, and only some survive the immediate consecutive-binary obstruction.

LOAD-BEARING ASSESSMENT: High. This gives the first finite searchable residue for the `n = 9` lower-bound gap and separates structural impossibility from genuinely computational cases.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Full gap inventory generated by `python3 scripts/n9_gap_inventory.py --json-out scripts/n9_gap_inventory.json`.
  Key summary:
  - total unordered gap multisets: `143`
  - fully Case-2-blocked families: `63`
  - mixed Case-2 families: `75`
  - fully Case-2-safe families: `5`

- Fully Case-2-safe family table:
  - `(2,2,2,3,3,3,3,3,5)`: product `9720`, binary count `3`, linear orientations `504`, necklaces `56`
  - `(2,2,2,3,3,3,3,4,4)`: product `10368`, binary count `3`, linear orientations `1260`, necklaces `140`
  - `(2,2,3,3,3,3,3,3,4)`: product `11664`, binary count `2`, linear orientations `252`, necklaces `28`
  - `(2,2,2,3,3,3,3,3,6)`: product `11664`, binary count `3`, linear orientations `504`, necklaces `56`
  - `(2,2,2,3,3,3,3,4,5)`: product `12960`, binary count `3`, linear orientations `2520`, necklaces `280`

- Broad Sol 3 bounce-family scans:
  - theorem-frontier mixed family:
    - `python3 scripts/n9_gap_sol3_scan.py --multiset 2,2,2,2,2,2,4,5,7 --safe-only --variant v1 --variant v2 --variant v3 --variant v4 --variant v5 --variant v6 --stop-on-witness`
    - tested `1080` safe orientation/variant instances
    - result: `no Sol 3 witness found`
  - `python3 scripts/n9_gap_sol3_scan.py --multiset 2,2,2,3,3,3,3,3,5 --safe-only --variant v1 --variant v2 --variant v3 --variant v4 --variant v5 --variant v6 --stop-on-witness`
    - tested `3024` safe orientation/variant instances
    - result: `no Sol 3 witness found`
  - same command shape on `(2,2,2,3,3,3,3,4,4)`
    - tested `7560` instances
    - result: `no Sol 3 witness found`
  - same command shape on `(2,2,2,3,3,3,3,3,6)`
    - tested `3024` instances
    - result: `no Sol 3 witness found`
  - same command shape on `(2,2,2,3,3,3,3,4,5)`
    - tested `15120` instances
    - result: `no Sol 3 witness found`
  - total broad Sol 3 negative instances this exploration: `29808`

- Canonical first-level sharded sweeps:
  - theorem-frontier mixed family:
    - first safe orientation found by brute force: `(2,2,2,4,2,2,2,5,7)`
    - `python3 scripts/p2_prefix_batch.py 2,2,2,4,2,2,2,5,7 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
    - total `screened=760 survivors=0`
    - dominant prefix: `7 -> 757`
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,3,3,3,3,5 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
    - total `screened=4809 survivors=0`
    - prefix profile:
      - `7 -> 3521`
      - `6 -> 734`
      - `4 -> 310`
      - `5 -> 244`
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,3,3,3,3,6 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
    - total `screened=767 survivors=0`
    - dominant prefix: `7 -> 761`
  - `python3 scripts/p2_prefix_batch.py 2,2,2,3,3,3,3,4,5 --prefix-length 1 --time-limit 300 --max-cycles 50000000 --max-workers 9`
    - total `screened=9537 survivors=0`
    - main mass:
      - `4 -> 1664`
      - `1 -> 1661`
      - `2 -> 1661`
      - `3 -> 1659`
      - `5 -> 1621`
      - `6 -> 653`
      - `7 -> 618`

- Imported prior sweep evidence from the earlier `n = 9` upper-bound track:
  - product `10368`, orientation `57/140 = (2,2,3,4,3,3,2,3,4)`:
    - first level `screened=16821 survivors=0`
    - hot prefixes `3 -> 5639`, `4 -> 5232`, `2 -> 5150`
    - depth-2 under prefix `3`: `3,2 -> 5775`, `3,3 -> 4451`, `3,4 -> 1183`, still `0` survivors
  - product `9720`, witness-adjacent local block:
    - `29/56`: `screened=916 survivors=0`
    - `30/56`: `screened=7 survivors=0`
    - `31/56`: `screened=2 survivors=0`

STRUCTURAL RESULTS:
- Assuming the same accepted Case-2 obstruction already used elsewhere in the project, the formal lower bound improves from `8748` to `8960`.
- The broad Sol 3 bounce-family search is now negative on all unresolved fully Case-2-safe gap families.
- The smallest fully Case-2-safe gap family `9720` is negative both under broad Sol 3 scans and under a canonical first-level prefix-sharded sweep.
- The large all-safe family `12960` is not cheap-dead under the canonical sweep, but it is still survivor-free at first sharding depth.
- The smallest unresolved product family `8960` is also negative under both the broad Sol 3 scan and the first sampled safe-orientation sweep.

TOOLS:
- New script: `scripts/n9_gap_inventory.py`
- New artifact: `scripts/n9_gap_inventory.json`
- New script: `scripts/n9_gap_sol3_scan.py`

REPRESENTATIONS:
- Linear-orientation count for rule-family scans versus necklace count for architecture-level sweeps:
  - linear orientations matter for distinguished-rule families like Sol 3 variants,
  - necklaces are the right quotient for unrestricted rule-table existence questions.

### What Would Unblock This
- Attack the new theorem frontier product by product:
  - `8960`: recurse on prefix `7` in safe orientations of `(2,2,2,2,2,2,4,5,7)` and test custom non-Sol-3 bounce templates there.
  - if `8960` dies, move next to `9072 = (2,2,2,2,3,3,3,3,7)`.
- Extend bounce-family search beyond Sol 3 variants on the five fully Case-2-safe families:
  - custom mixed binary/ternary/quaternary rule templates,
  - bounded-cycle SAT plus SMT completion on the canonical safe orientations,
  - seeded good-cycle search from the one-binary Sol 3 witness mover sequence adapted to two/three-binary families.
- For sweep-side work, recurse on the heaviest canonical prefixes now exposed:
  - `9720`: prefix `7`
  - `11664` with `6`: prefix `7`
  - `12960`: prefixes `4,1,2,3,5`
- Expand the inventory table to the mixed Case-2 families by counting only the safe linear orientations and then prioritizing the smallest products with the fewest safe orientations.

### Key Parameters
- Gap definition: unordered `n = 9` multisets with each `m_i >= 2`, product in `(8748,13122)`, and at least two binaries.
- Bounce-family scan mode:
  - all safe linear orientations
  - Sol 3 variants `v1..v6`
  - graph verifier only unless a hit appears
- Sweep mode:
  - `p2_prefix_batch.py`
  - `--prefix-length 1`
  - `--time-limit 300`
  - `--max-cycles 50000000`
  - `--max-workers 9`

### Open Questions
- Does the product-`8960` family `(2,2,2,2,2,2,4,5,7)` admit any witness under a non-Sol-3 bounce rule template?
- Does any fully Case-2-safe gap family admit a witness under a non-Sol-3 bounce rule template?
- Among the mixed Case-2 families, which smallest-product safe orientations are still computationally live after the inventory split?
- Is the best next lower-bound attack on `M_9` a deeper sweep recursion on `9720`/`12960`, or a custom bounce-family SAT search on the five fully safe families?

## Synthesis after exploration 1

The `n = 9` lower-bound gap is no longer an indistinct interval. It is an explicit inventory with a very small fully Case-2-safe core. Inside that core, the current six Sol 3 bounce families are completely dead, and the smallest canonical sweeps are also survivor-free. So the next progress is unlikely to come from “try more Sol 3.” It will come from one of two directions:
- deeper sweep recursion on the heaviest canonical prefixes of the smallest safe families,
- or genuinely new bounce-rule templates beyond the current Sol 3 repertoire.

There is also now a concrete theorem-level milestone: the formal lower bound reaches `8960` under the same accepted obstruction package already in use elsewhere. The immediate next lower-bound target is not `9720` but the mixed product-`8960` family `(2,2,2,2,2,2,4,5,7)`, whose sampled safe sweep residue is already concentrated almost entirely in prefix `7`.
