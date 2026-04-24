# Exploration Log

## Strategy Register

### Eliminated approach classes
- None yet.

### Obstructions
- None yet.

### Building blocks
- The one-binary Sol-3-v1 family `(2,3,3,...,3)` with bottom binary and all other processors ternary is valid for every tested `n = 5,6,7,8,9,10,11,12` (exploration 1). The recurrent cycle lengths are `13,16,19,22,25,28,31,34`, i.e. `3n-2` on this range.
- `scripts/sol3_adapt.py` (exploration 1): current mixed-state Sol 3 family checker built on `p2_ring.verify_system`, with support for the six previously sketched local-rule variants and optional widening to alternate binary placements if the direct family fails.
- `scripts/verify_witnesses.py` cycle extraction fix (exploration 1): the five-property verifier now detects a legitimate good cycle even when the first explored single-privileged state lies on a transient tail leading into that cycle.

### Known reformulations
- One-binary Sol 3 family: instead of searching mixed architectures first, treat the family `(2,3,3,...,3)` as the direct mixed-state analogue of Dijkstra Solution 3 and verify it as a concrete candidate upper-bound ladder. LOAD-BEARING: high. It immediately produces the current best `n = 9` bound and the first working `n = 10` witness.

## Session Start (2026-03-09)

Resuming from exploration 0.

No prior `exploration_log_m10.md` existed in the repository, so there is no earlier exploration state to reuse.

Next attempt: waiting for user instructions for the `m10` investigation.

## Exploration 1

### Strategy
Test the predicted `m10` witness directly by building the Sol-3-v1 one-binary family `(2,3,3,...,3)` with bottom binary and ternary middle/top rules, verify it with the current graph verifier plus the five-property witness verifier, and then extend the same pattern through `n = 11,12`; also compare the same family on `n = 5..8` to locate where this architecture first becomes competitive.

### Outcome
SUCCEEDED

### Failure Constraint
The only failure encountered was in the legacy five-property verifier, not in the family itself: `scripts/verify_witnesses.py` missed valid recurrent cycles whenever the first explored single-privileged state fed into the cycle through a tail. This was repaired by extracting the first repeated node in the local functional path, not only the special case `cur == start`.

### What This Rules Out
- Any need to widen immediately to alternate binary placements or the other five Sol-3 variants for `n = 10`: the direct predicted family already works.
- The hypothesis that the one-binary Sol-3-v1 family only becomes valid at `n = 9` or `n = 10`. It is already valid on every tested size `n = 5..12`, though it is not product-optimal on `n = 5..8`.

### Surviving Structure
- The exact predicted `m10` family works:
  - `n = 10`, `ms = (2,3,3,3,3,3,3,3,3,3)`, product `39366`
  - one recurrent cycle
  - cycle length `28`
  - all five Dijkstra properties verified
- The same family also works unchanged at:
  - `n = 9`, product `13122`, cycle length `25`
  - `n = 11`, product `118098`, cycle length `31`
  - `n = 12`, product `354294`, cycle length `34`
- On `n = 5..8`, the same family is valid but not product-optimal relative to the known smaller mixed witnesses.
- Across the full tested range `n = 5..12`, the recurrent cycle length follows the clean linear pattern `3n - 2`.

### Reformulations
- The right first attack on `M_10` was not a search over mixed families but a direct verification problem: instantiate the exact Sol-3-v1 local rules as finite transition tables and ask the verifiers whether the resulting ring is already self-stabilizing.

LOAD-BEARING ASSESSMENT: High. This turns the `m10` task from open search into immediate witness verification and shows that the one-binary family is a genuine upper-bound ladder.

### Concrete Artifacts
COMPUTED EXAMPLES:
- Direct Sol-3-v1 family verification with `python3 scripts/sol3_adapt.py --skip-fallback`:
  - `n = 5`, `ms = (2,3,3,3,3)`, product `162`, cycle length `13`, total configs `162`
  - `n = 6`, `ms = (2,3,3,3,3,3)`, product `486`, cycle length `16`, total configs `486`
  - `n = 7`, `ms = (2,3,3,3,3,3,3)`, product `1458`, cycle length `19`, total configs `1458`
  - `n = 8`, `ms = (2,3,3,3,3,3,3,3)`, product `4374`, cycle length `22`, total configs `4374`
  - `n = 9`, `ms = (2,3,3,3,3,3,3,3,3)`, product `13122`, cycle length `25`, total configs `13122`
  - `n = 10`, `ms = (2,3,3,3,3,3,3,3,3,3)`, product `39366`, cycle length `28`, total configs `39366`
  - `n = 11`, `ms = (2,3,3,3,3,3,3,3,3,3,3)`, product `118098`, cycle length `31`, total configs `118098`
  - `n = 12`, `ms = (2,3,3,3,3,3,3,3,3,3,3,3)`, product `354294`, cycle length `34`, total configs `354294`

STRUCTURAL RESULTS:
- `M_10 <= 39366`.
- The one-binary Sol-3-v1 family is valid for all tested `n = 5..12`.
- Relative to the current best witness ladder:
  - `n = 5`: Sol-3-v1 product `162` is worse than known `96`
  - `n = 6`: `486` is worse than known `288`
  - `n = 7`: `1458` is worse than known `864`
  - `n = 8`: `4374` is worse than known `2592`
  - `n = 9`: `13122` matches the new best known witness product
  - So the first tested `n` where Sol-3-v1 reaches the current best witness ladder is `n = 9`

TOOLS:
- Patched `scripts/sol3_adapt.py` to use:
  - `p2_ring.materialize_rule`
  - `p2_ring.verify_system`
  - `scripts.verify_witnesses.verify`
- Patched `scripts/verify_witnesses.py` so its good-cycle finder extracts a cycle reached through a single-privileged tail.

REPRESENTATIONS:
- Mixed-state Sol-3-v1 rule tables on `(2,3,3,...,3)`:
  - `P0` (binary bottom): `if (S+1)%2 == R%2 then (S-1)%2 else S`
  - `P1..P(n-2)` (ternary middle): `if (S+1)%3 == L%3 then L%3 elif (S+1)%3 == R%3 then R%3 else S`
  - `P(n-1)` (ternary top): `if L%3 == R%3 and (L%3+1)%3 != S then (L%3+1)%3 else S`

### What Would Unblock This
- If a lower product than `39366` is still desired for `n = 10`, the next move is not to widen Sol-3-v1 variants immediately; it is to compare this new one-binary upper bound against lower-product mixed families and only search below `39366`.
- If a family theorem is desired, prove the observed linear-cycle pattern `3n-2` and the validity of the one-binary Sol-3-v1 ladder for all `n >= 5`.

### Key Parameters
- Family tested: one binary at bottom, all other processors ternary.
- Variant tested: Sol-3 adaptation `v1` only.
- Sizes tested exhaustively: `n = 5..12`.
- No fallback to alternate placements or variants was needed because the direct family succeeded at every requested size.

### Open Questions
- Is `39366` optimal for `n = 10`, or can the product be pushed below the one-binary Sol-3-v1 family?
- Can the one-binary Sol-3-v1 family be proved correct for all `n >= 5` directly, rather than only verified case by case?
- Does any lower-product mixed family beat `13122` at `n = 9`, or does the one-binary family already give the true optimum there?

## Synthesis after exploration 1

The `m10` search did not begin as a search at all. The predicted Sol-3-v1 family is already a valid upper-bound ladder, and it stays valid well past `n = 10`. The real structural split is now clear: the earlier mixed witnesses with a quaternary gadget dominate at `n = 5..8`, but the one-binary Sol-3 family catches up at `n = 9` and gives a clean immediate witness at `n = 10`. So the next meaningful `m10` work is lower-bound tightening below `39366`, not upper-bound engineering.
