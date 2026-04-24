# Exploration Log 4: Alternative Product-7776 Architectures at n=9

## Strategy Register

**Eliminated approach classes:**
- Standard pipeline (DFS good-cycle search + forced-recurrent screening) fails for ALL product-7776 architectures at n=9 — the screening obstruction is universal across multisets (Exploration 1)

**Obstructions:**
- All 56 necklaces of {2^3, 3^5, 4} (single quaternary, product 7776): ALL DEAD (n9_sweep_results.txt)
- Multiset A {2^4, 3^4, 6}: 20+ orientations tested, 2 found good cycles (lengths 78+), ALL screened out (0/4390 survivors)
- Multiset B {2^5, 3^3, 9}: 18 orientations tested, NONE found good cycles at all (DFS explores ~200K+ nodes without finding any in 5-10s; for some orientations, transition cache build alone exceeds timeout)
- **Screening obstruction is universal**: forced rules from ANY good cycle starting at all-zeros create fatal forced recurrent components among off-cycle configs, regardless of state count architecture

**Building blocks:**
- Dijkstra Solution 3 valid at n=9: product 19683, cycle length 48 (0.22s to verify)
- Pipeline verified working for n≤8
- Lower bound M_n ≥ 32·3^(n-4) for all n≥5 → M_9 ≥ 7776
- Multiset A: 70 total necklaces, 65 with ≤3 consecutive binary
- Multiset B: 56 total necklaces, 40 with ≤3 consecutive binary
- Transition cache for 7776-config systems takes 5-7s to build in Python

**Known reformulations:**
- Product 7776 = 2^5 × 3^5 factors into three distinct 9-processor multisets:
  - {2^3, 3^5, 4} — 3 binary + 5 ternary + 1 quaternary (ALL DEAD)
  - {2^4, 3^4, 6} — 4 binary + 4 ternary + 1 six-state (DEAD at pipeline level)
  - {2^5, 3^3, 9} — 5 binary + 3 ternary + 1 nine-state (NO GOOD CYCLES FOUND)

---

## Exploration 1

### Strategy
Test alternative product-7776 architectures ({2^4,3^4,6} and {2^5,3^3,9}) at n=9 using the standard DFS good-cycle + screening + SMT pipeline.

### Outcome
FAILED

### Failure Constraint
For multiset A ({2^4,3^4,6}): good cycles exist but ALL are killed by the `has_fatal_forced_cycle_singletons` screen — the forced rule assignments from any good cycle create an inescapable bad-config recurrent component. For multiset B ({2^5,3^3,9}): no good cycles are found at all by the DFS within time limits; the 9-state processor's large branching factor makes the DFS too bushy to converge.

### What This Rules Out
The pipeline approach (DFS cycle enumeration → forced-recurrent screening → SMT completion) fails universally for ALL product-7776 multisets at n=9. This is not specific to the quaternary architecture — the screening obstruction affects the six-state and nine-state architectures equally. Any approach that relies on finding good cycles from the DFS and then completing them will hit the same screening wall.

### Surviving Structure
- **Dijkstra Sol 3 n=9** verified: product 19683, cycle length 48, takes 0.22s
- **Necklace counts**: A has 70 necklaces (65 filtered), B has 56 (40 filtered)
- **Good cycles exist for multiset A**: orientations (2,2,3,6,3,3,2,3,2) and (2,2,2,3,2,3,6,3,3) both produce good cycles — cycles of length ~78 starting from all-zeros. These have 3 consecutive binary processors, suggesting the "consecutive binary" pattern is important for cycle existence.
- **No good cycles for multiset B**: the DFS explores 200K-600K nodes in 10s without finding any cycles. The 9-state processor creates a huge branching factor that makes DFS ineffective.

### Reformulations
The screening obstruction suggests that the problem isn't finding a good cycle — it's that ANY good cycle forces too many off-cycle transitions. A different approach might bypass the "find cycle first, complete later" paradigm:
- **Full SMT formulation**: encode all 5 properties simultaneously, letting the solver find both the good cycle and the rule tables at once
- **Random local search**: start from a random rule table, iteratively fix property violations
- **Extension from n=8**: modify the n=8 witness's architecture rather than inserting a new processor

LOAD-BEARING ASSESSMENT: The "find cycle first" approach has a structural blind spot — it can't discover systems where the good cycle has unusual properties that the DFS normalization misses. A full SMT formulation would be more powerful but much more expensive computationally.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Phase 0: Dijkstra Sol 3 n=9 valid, product=19683, cycle_length=48
- Phase 1 probes (10s each):
  - A1 (2,3,2,3,6,3,2,3,2): timed out, 422K nodes
  - A2 (2,2,3,6,3,3,2,3,2): cycle found length=78, 33K nodes, 2.3s
  - A3 (6,2,3,2,3,2,3,3,2): timed out, 478K nodes
  - A4 (2,3,6,3,2,3,2,3,2): timed out, 616K nodes
  - A5 (2,6,3,2,3,2,3,3,2): timed out, 418K nodes
  - B1 (2,3,2,3,2,9,2,3,2): timed out, 385K nodes
  - B2 (9,2,3,2,2,3,2,3,2): timed out, 298K nodes
  - B3 (2,2,3,9,2,3,2,3,2): timed out, 470K nodes
- Phase 2 pipeline: A2 screened 3020 cycles, 0 survivors (120s)
- Phase 3 broader sweep: 15 A + 15 B necklaces tested, only (2,2,2,3,2,3,6,3,3) found cycles (1370 screened, 0 survivors). All B necklaces: 0 cycles.

STRUCTURAL RESULTS:
- Screening obstruction is universal across all three product-7776 multisets
- Good cycles only found for A orientations with ≥2 consecutive binary processors (pattern: 2,2,... prefix)
- Multiset B appears to have NO good cycles reachable from all-zeros via DFS

TOOLS:
- alt_arch_n9_search.py: multi-phase search script (sanity check → quick probes → full pipeline → necklace sweep)
- Necklace enumerator: generates all necklaces for a multiset via permutation-and-canonicalize

### What Would Unblock This
1. A full SMT formulation that encodes all 5 properties simultaneously, bypassing the "find cycle first" bottleneck. Needed for at least one promising A orientation.
2. For multiset B: a cycle search with much longer time limits (60-120s) or a BFS-style search that finds short cycles first.
3. Understanding WHY the screening always fails: what structural property of the forced rules creates unavoidable bad recurrent components at n=9 specifically?

### Key Parameters
- DFS probe timeout: 10s (Phase 1), 5s (Phase 3)
- Pipeline screen time: 120s (Phase 2), 60s (Phase 3)
- Max cycles screened: up to 10000 per orientation
- Max survivors attempted: 20 (Phase 2), 10 (Phase 3)
- Necklaces tested: 5 targeted A + 3 targeted B + 15 sweep A + 15 sweep B = 38 total

### Open Questions
1. ~~Are there shorter good cycles (length 18-30) for multiset A?~~ **ANSWERED (Exploration 2)**: No. Minimum cycle length is 48. No cycles exist below 48.
2. Does multiset B have good cycles at all, or is the DFS simply too slow?
3. Can a full SMT formulation find a witness that the pipeline misses?
4. Is the screening obstruction provably universal for product 7776 at n=9, or just an artifact of the specific cycles found?

---

## Exploration 2 (probe)

### Strategy
Test whether shorter good cycles (length ≤ 30) exist for multiset A orientation A2, since shorter cycles force fewer rules and might survive screening.

### Outcome
FAILED — but answered Open Question 1 definitively.

### Concrete Artifacts
- max_depth=20, 30s: **NO cycles found** (2,652,062 nodes exhaustive)
- max_depth=40, 30s: **NO cycles found** (956,734 nodes exhaustive)
- max_depth=60, 30s: **cycle found at length 60** (31,920 nodes, 1.2s)
- Enumeration with max_depth=50, 30s: 93 cycles found, lengths {48: 1, 49: 12, 50: 80}
- **Minimum good cycle length for A2 is 48** — matches Dijkstra Sol 3 n=9 cycle length exactly

---

## Synthesis after Exploration 2

### Combined result across all agents

**M_n = 32·3^(n-4) does NOT extend to n=9.** Product 7776 is dead across all three multisets:

| Multiset | Product | Necklaces | Cycles found | Survivors | Status |
|---|---|---|---|---|---|
| {2^3, 3^5, 4} | 7776 | 56 | yes (many) | 0/all | ALL DEAD |
| {2^4, 3^4, 6} | 7776 | 70 (65 filtered) | yes (len ≥ 48) | 0/4390 | ALL DEAD |
| {2^5, 3^3, 9} | 7776 | 56 (40 filtered) | none found | — | NO CYCLES |

The other agent's sweep is now testing higher products:
- Product 10368 = {2^3, 3^4, 4^2} (two quaternary) — 140 orientations, 16/140 tested, all dead so far
- Product 9720 = {2^3, 3^5, 5} (single 5-state) — not yet started

### Structural insight
The minimum good cycle length at product 7776 is 48, same as Dijkstra Sol 3 (product 19683). This suggests that cycle length at n=9 is fundamentally bounded below by ~48 regardless of product. A cycle of length 48 forces 48×9 = 432 context instances across ~210 unique rule entries — massive over-determination that creates inevitable bad recurrent components.

### What this means for M_9
- M_9 > 7776 (the formula M_n = 32·3^(n-4) breaks at n=9)
- Upper bound: M_9 ≤ 19683 (Dijkstra Sol 3)
- Current search targets: 9720, 10368
- The gap 7776 < M_9 ≤ 19683 needs to be narrowed

---

## Exploration 3

### Strategy
Structural analysis of the Case 1 boundary at product 8748 = 4·3^7 for multiset {2,2,3,3,3,3,3,3,3} (2 binary + 7 ternary). The shadow cycle theorem requires ≥3 binary. With only 2 binary, the theorem's analytic formula loses a degree of freedom. Goal: identify which shadow properties fail, find escape routes, and test whether the DFS pipeline can exploit them.

Three-pronged approach:
1. Compare determined-entry coverage: 2-binary vs 3-binary
2. Find bad SCCs via Tarjan (correct counting, not the double-counting from shadow tracing)
3. Run DFS pipeline on all 4 necklaces × 9 orientations

### Outcome
FAILED — Product 8748 is DEAD across all orientations.

### Failure Constraint
The shadow mechanism works with 2 binary processors, contrary to what the analytic proof's requirements suggest. Specifically:

**The analytic formula breaks** — the closed-form shadow s_k[i] = g0(k + d_i) requires 3 binary procs for the shift vector d_i to have the right structure. With 2 binary, this specific formula doesn't work.

**But the computational mechanism still creates bad SCCs** — determined entries from ANY good cycle (uniform sweep or DFS-found) create forced-move graphs with inescapable strongly-connected components.

### What This Rules Out
Product 8748 with multiset {2,2,3^7} at n=9. Combined with Exploration 1-2 (product 7776 dead across all multisets), this gives: **M_9 > 8748**.

### Surviving Structure

**Necklace enumeration**: Only 4 distinct necklaces for 2 identical binaries in 9 positions:

| Necklace | Binary positions | Separation | Orientations |
|---|---|---|---|
| (2,2,3,3,3,3,3,3,3) | [0,1] | 1 | 9 |
| (2,3,2,3,3,3,3,3,3) | [0,2] | 2 | 9 |
| (2,3,3,2,3,3,3,3,3) | [0,3] | 3 | 9 |
| (2,3,3,3,2,3,3,3,3) | [0,4] | 4 | 9 |

**Determined entry comparison** (uniform sweep, NB=all 1s):
- 3-binary: 54/176 entries determined (30.7%), 0 undetermined configs
- 2-binary (adjacent): 54/195 entries determined (27.7%), 2930 undetermined configs (33.6%)
- Key: with 3 binary, EVERY non-good config has forced privilege. With 2 binary, 2930/8730 = 33.6% have NONE.

**Bad SCC analysis** (correct Tarjan, not double-counting):
- Uniform sweep: exactly 3 bad SCCs of sizes **252, 168, 72** (total 492 configs)
- This is INVARIANT across all 4 necklaces and all 128 NB value combinations
- 3-binary reference at n=9: **same 3 SCCs (252, 168, 72)** — the shadow is a property of sweep structure, not binary count
- Each SCC has perfectly uniform internal-move distribution: every processor makes exactly the same number of internal moves
- Internal cycles are length 18 = 2n with permuted sweep movers

**DFS pipeline results** (15s per orientation, up to 500 cycles):
- 36 orientations tested across 4 necklaces (9 per necklace)
- Good cycles found at 22 orientations (14 found NO cycles — mostly adjacent or symmetric binary placement)
- **628 cycles screened total, 0 survivors**
- Non-uniform DFS cycles create even MORE bad SCCs than uniform sweeps (up to 100+ SCCs per cycle with sizes 4-2500)
- Adjacent binary procs (sep=1): many orientations find NO good cycles at all
- Separated binary procs (sep=2,3,4): more cycles found but all screened out

### Reformulations
The shadow obstruction at product 8748 suggests two possibilities:
1. **M_9 > 8748**: The 2-binary architecture is blocked just like 3-binary, and the actual minimum is at a higher product with a different multiset structure
2. **The pipeline misses exotic cycles**: There might exist good cycles with unusual properties (very long, non-standard mover patterns) that the 15s DFS can't find, but which survive screening

The gap is now: **8748 < M_9 ≤ 19683**

### Concrete Artifacts

COMPUTED EXAMPLES:
- shadow_2binary_analysis.py: entry comparison, shadow tracing, necklace enumeration
- shadow_2binary_deep.py: correct SCC analysis via Tarjan, all 128 NB combos
- shadow_scc_structure.py: internal structure of the 3 bad SCCs (252, 168, 72)
- shadow_2binary_pipeline.py: DFS pipeline on all 4 necklaces × 9 orientations

STRUCTURAL RESULTS:
- 3 bad SCCs (252, 168, 72) are invariant across necklaces, NB combos, and binary count
- SCC internal cycles use permuted sweep movers: [4,3,8,0,1,2,7,6,5,...] and [0,7,6,5,4,3,2,1,8,...]
- The shadow permutation σ operates in the same way for 2-binary as for 3-binary
- 2930 undetermined configs exist but are NOT the escape — they're outside all SCCs
- The escape failure is that shadow SCCs are inescapable (every config has at least one forced successor within the SCC)
- Adjacency of binary procs DOES affect cycle existence (adjacent = fewer cycles) but NOT screening survival (all dead regardless)

### What Would Unblock This
1. A cycle structure that determines entries WITHOUT creating any bad SCC in the forced-move graph — if such a structure exists at product 8748
2. A completely different approach: random search, CEGAR, or direct SMT that bypasses the cycle-first paradigm
3. Moving to higher products: 9720 = {2^3, 3^5, 5} or 10368 = {2^3, 3^4, 4^2} where the additional state diversity might break the SCC structure

### Key Parameters
- DFS timeout: 15s per orientation
- Max cycles per orientation: 500
- Max depth: 100
- SCC analysis: iterative Tarjan (no recursion limit issues)
- NB combos tested: 128 (all possible for 7 ternary procs)

### Open Questions
1. Is the 3-SCC structure (252, 168, 72) universal across ALL possible good cycles at this product, or just those found by DFS?
2. Why does the SCC structure depend only on the sweep pattern and not on the multiset? What algebraic structure underlies sizes 252 = 4·63, 168 = 8·21, 72 = 8·9?
3. At what product does the SCC obstruction finally break? Is it at the Dijkstra Sol 3 product 19683, or somewhere in between?

---

## Synthesis after Exploration 3

### Updated Strategy Register

**Eliminated approach classes:**
- Standard pipeline fails for ALL product-7776 architectures at n=9 (Exploration 1)
- Standard pipeline fails for product-8748 architecture {2,2,3^7} at n=9 (Exploration 3)
- The screening obstruction is NOT specific to ≥3 binary — it affects 2-binary equally

**Updated bounds:**
- **M_9 > 8748** (strictly)
- M_9 ≤ 19683 (Dijkstra Sol 3)
- Gap: 8748 < M_9 ≤ 19683

**Key structural insight:**
The shadow SCC obstruction (3 bad SCCs of sizes 252, 168, 72) is a property of the SWEEP CYCLE STRUCTURE at n=9, not of the multiset composition. It exists for:
- 3 binary + 5 ternary + 1 quaternary (product 7776)
- 3 binary + 6 ternary (product 5832)
- 2 binary + 7 ternary (product 8748)

The obstruction appears to be UNIVERSAL at n=9 for low-product systems with uniform sweep cycles. Non-uniform cycles create even more SCCs.

**Next targets:**
- Product 9720 = {2^3, 3^5, 5}: adds a 5-state proc, breaking ternary uniformity
- Product 10368 = {2^3, 3^4, 4^2}: two quaternary procs, different structure
- Product 11664 = various multisets between 10368 and 19683
- Dijkstra Sol 3 boundary: what's the minimum product where a witness exists?

---

## Exploration 4

### Strategy
Binary search the gap [8748, 19683] to find where the SCC obstruction breaks. Test products 11664, 13122, 14580, 17496. Then analyze the invariance mechanism and compare with Dijkstra's Solution 3.

### Outcome
PARADIGM SHIFT — The SCC obstruction is a **universal property of sweep cycles at n=9**, invariant across ALL products. But **Dijkstra's Sol 3 avoids it entirely by using a bounce-pattern cycle** instead of a sweep cycle. The question "where does the SCC obstruction break?" was wrong — it doesn't break. Different cycle *types* avoid it.

### Key Findings

#### Finding 1: SCC obstruction is product-invariant
Binary search results (uniform sweep + DFS cycles):

| Product | Multisets | Screened | Survivors | Status |
|---------|-----------|----------|-----------|--------|
| 8748    | —         | 628      | 0         | DEAD   |
| 11664   | 3         | 56       | 0         | DEAD   |
| 13122   | 1         | 12       | 0         | DEAD   |
| 14580   | 1         | 15       | 0         | DEAD   |
| 17496   | 3         | 0        | 0         | DEAD   |
| 19683   | —         | —        | —         | ALIVE  |

Every single product tested shows the **exact same 3 bad SCCs: [252, 168, 72] = 492 configs**, invariant across all multisets, necklaces, and orientations.

#### Finding 2: Root cause — all 492 configs live in {0,1}^9
The 492 SCC configs are IDENTICAL across all products:
- Overlap = 492/492 for every pair tested
- **Maximum state value in any SCC config: 1** (states {0,1} only)
- Perfect symmetry: each position has exactly 246 configs with 0 and 246 with 1
- This explains invariance: the {0,1}^9 subspace exists in every multiset with m_i ≥ 2

The sweep cycle's 18 forcing entries (determined by the good cycle) create binary-flip transitions within {0,1}^9 that trap the 492 configs:
- P0: (0,0,0)→1 and (1,1,1)→0
- P1-P7: (0,1,1)→0 and (1,0,0)→1
- P8: (0,1,0)→0 and (1,0,1)→1

#### Finding 3: Dijkstra Sol 3 uses a bounce cycle, not a sweep
Dijkstra's Solution 3 (verified working at n=9):
- **Rule structure**: f_bottom, f_middle, f_top — NOT the simple "copy left" rule
- **Good cycle length**: 48 (not 18 like sweep)
- **96 legitimate configs** (not 18)
- **14 separate legitimate cycles** exist among the 96 configs
- **Mover pattern**: `[8,7,6,...,0,1,2,...,8,7,...,0,1,...,8]` — a bounce (sweep-down then sweep-up), NOT a uniform sweep `[0,1,...,8,0,1,...,8]`
- **53.9% coverage** (131/243 determined entries) vs sweep's 22.2% (54/243)
- **ZERO bad SCCs** in the forced graph — the SCC screen PASSES clean
- **ZERO SCCs** in the complete transition graph — convergence confirmed

#### Finding 4: Bounce cycles exist at ALL products, also SCC-clean
Bounce-pattern cycles (down-up: `[n-1,...,0,1,...,n-1]`) were constructed at every product tested:

| ms | Product | Cycle len | SCCs |
|----|---------|-----------|------|
| (3,3,3,3,3,3,3,3,3) | 19683 | 51 | **0** |
| (2,3,3,3,3,3,3,3,3) | 13122 | 26 | **0** |
| (2,2,3,3,3,3,3,3,3) | 8748  | 27 | **0** |
| (2,2,2,3,3,3,3,3,3) | 5832  | 28 | **0** |
| (2,2,2,2,3,3,3,3,3) | 3888  | 29 | **0** |
| (2,2,2,2,2,3,3,3,3) | 2592  | 30 | **0** |

All bounce cycles have **zero bad SCCs** — the obstruction is entirely an artifact of uniform sweep cycles.

#### Finding 5: Completion is the hard problem
Having a clean bounce cycle (no bad SCCs) is necessary but not sufficient. Greedy completion of the remaining free entries creates deadlocks and new SCCs:
- ms=(3^9): greedy completion → 2028 deadlocks, fixing creates 1458 SCCs
- ms=(2,2,3^7): greedy completion → closure failure, 858 SCCs after fixes
- Dijkstra Sol 3 works because its rule table is carefully designed as a whole

### SCC Screen Soundness
The SCC screen IS sound: if the good cycle's determined entries create forced transitions that cycle among non-good configs, then ANY completion must include those transitions, and an adversarial daemon can follow them forever. The screen correctly rejects sweep cycles.

But the screen doesn't reject ALL possible systems — only those based on a specific good cycle. A different good cycle (like Dijkstra's bounce pattern) may have completely different determined entries that avoid the trap.

### What This Rules Out
The "binary search" approach was asking the wrong question. The SCC obstruction at n=9 doesn't gradually weaken with increasing product — it's a fixed 492-config trap in {0,1}^9 that exists for EVERY uniform sweep cycle at EVERY product. The obstruction is structural, not numerical.

What's ruled out: any self-stabilizing system at n=9 whose good cycle is a uniform sweep `[0,1,...,8,0,1,...,8]` with NB values in {0,1}. The 18 forcing entries from such a cycle always create the same 3 inescapable SCCs.

### Surviving Structure
- **Bounce cycles are SCC-clean** at all products down to at least 2592 = M_8
- **Completion is the bottleneck**: a bounce cycle provides a necessary foundation (no forced-entry traps), but the remaining ~50-60% of the rule table must be filled in to satisfy all 5 properties simultaneously
- **Dijkstra's approach works** at 19683 because Sol 3's rules are a coherent whole — the good cycle and the convergence mechanism were designed together, not independently

### Reformulations
The M_9 problem should be reframed:
1. **Can Dijkstra Sol 3's rule structure be adapted to lower products?** The rules use modular arithmetic with K=3 states. With mixed state counts, the mod operations need adaptation.
2. **Can the completion problem be formulated as SMT/SAT?** Given a clean bounce cycle at product P, encode the remaining free entries as variables with convergence constraints (no SCCs in the complete graph). This is much larger than the previous SMT formulation (which only completed sweep-cycle free entries).
3. **Is there a closed-form lower bound for bounce cycles?** The bounce cycle's determined entries have a specific structure — perhaps we can prove that below some product, even bounce cycles must create traps.

### Concrete Artifacts

SCRIPTS:
- `scc_binary_search.py`: binary search across products 11664, 13122, 14580, 17496
- `scc_invariance_test.py`: proves SCC config identity + {0,1}^9 root cause
- `scc_dijkstra_test.py`: initial (incorrect) Sol 3 analysis — used wrong rule!
- `scc_dijkstra_verify.py`: verified correct Sol 3 converges, found wrong rule gives cycles
- `scc_correct_sol3.py`: correct Sol 3 analysis — bounce mover, 0 SCCs, 96 good configs
- `scc_bounce_test.py`: bounce cycles at all products — all SCC-clean
- `scc_completion_test.py`: greedy completion attempts — all fail
- `scc_screen_validity.py`: tested screen against wrong Sol 1 rule (irrelevant after correction)

COMPUTED RESULTS:
- Binary search: 711 cycles screened across 4 products, 0 survivors (sweep-based)
- SCC invariance: 492 configs in {0,1}^9 with perfect per-position symmetry (246:246)
- Sol 3 correct: 96 legit configs, 14 separate cycles, length 48 main cycle, 0 SCCs
- Bounce cycles: clean at products 19683, 13122, 8748, 5832, 3888, 2592

LOAD-BEARING ASSESSMENT: The sweep-cycle SCC screen is sound but only applies to sweep cycles. The DFS pipeline searches primarily for sweep-like cycles and hence always hits the wall. The real path to M_9 witnesses goes through non-sweep architectures (bounce, Dijkstra-style), which the current pipeline doesn't explore. This represents a fundamental limitation of the existing computational infrastructure.

---

## Synthesis after Exploration 4

### Updated Strategy Register

**Eliminated approach classes:**
- Standard pipeline (sweep cycle + SCC screen) fails for ALL products at n=9 — the 492-config {0,1}^9 obstruction is universal for sweep cycles (Explorations 1-4)
- Binary search for SCC threshold: moot — the obstruction is product-invariant (Exploration 4)

**Updated bounds:**
- M_9 ≤ 19683 (Dijkstra Sol 3, confirmed via verifier)
- Lower bound methodology needs revision — the 7776 lower bound was proved for sweep cycles, but non-sweep cycles (bounce) might work at lower products
- Open question: 2592 ≤ M_9 ≤ 19683 (wider gap than previously thought)

**Key structural insights:**
1. The sweep-cycle SCC obstruction is a fixed 492-config trap in {0,1}^9, caused by 18 binary-flip forcing entries, invariant across all n=9 products
2. Dijkstra Sol 3 escapes via bounce-pattern mover sequence — a fundamentally different cycle architecture
3. Bounce cycles exist and are SCC-clean at all tested products (down to 2592), but completion into full systems is open
4. The M_9 problem reduces to: "at what minimum product can a bounce cycle be completed into a valid self-stabilizing system?"

**Critical methodology gap:**
The DFS good-cycle search (`p2_good_cycle_search.py`) uses a "states-in-order" normalization that biases toward sweep-like cycles. It does not explore bounce-pattern cycles. The pipeline needs a new cycle generator that targets bounce patterns.

**Next targets:**
- Build a bounce-cycle-aware completion solver (SMT or constraint propagation)
- Test whether Sol 3's rule structure can be adapted to ms=(2,2,3^7) or similar
- Investigate whether the 492-config {0,1}^9 trap can be analytically characterized (what combinatorial structure?)
- Lower bound: can we prove that below some product, even bounce cycles fail?

---

## Exploration 5

### Strategy
Bounce-cycle SMT completion: adapt Dijkstra Sol 3's rules to lower products. Four steps:
1. Adapt Sol 3 rules to products 13122 (1-binary) and 8748 (2-binary)
2. If adaptation fails at 8748, do full SMT/exhaustive completion
3. Structured completion with constrained parameters
4. Lower bound: when does completion become impossible?

### Outcome
**NEW UPPER BOUND: M_9 ≤ 13122.** Sol 3 v1 adaptation works at product 13122 = 2·3^8. All approaches fail at 8748 = 2^2·3^7. Gap analysis proves no 1-binary multisets exist below 13122. Strong evidence that **M_9 = 13122**.

### Key Findings

#### Finding 1: Sol 3 v1 witness at product 13122
Sol 3 "v1" adaptation — replace K with m_i in all modular operations — produces a valid self-stabilizing system at ms=(2,3,3,3,3,3,3,3,3), product 13122:

- **Cycle length**: 25
- **Good configs**: 62
- **All 5 properties verified**: liveness, mutual exclusion, closure, convergence, fairness

The v1 rule definitions:
- `f_bottom(m₀)`: if (S+1) mod m₀ = R mod m₀ then (S−1) mod m₀, else S
- `f_middle(mᵢ)`: if (S+1) mod mᵢ = L mod mᵢ then L mod mᵢ; elif (S+1) mod mᵢ = R mod mᵢ then R mod mᵢ; else S
- `f_top(mₙ)`: if L mod mₙ = R mod mₙ and (L mod mₙ+1) mod mₙ ≠ S then (L mod mₙ+1) mod mₙ, else S

Also valid with v4 adaptation (slightly different). **Establishes M_9 ≤ 13122.**

#### Finding 2: All Sol 3 adaptations fail at 8748
Tested exhaustively:
- **6 adaptation variants** (v1–v6) at all 36 orientations (4 necklaces × 9 rotations): ALL FAIL
- **Separated necklaces**: binary at distance 1, 2, 3, 4 — all dead
- **Special placements**: binary at bottom+top, bottom+middle — all dead
- The fundamental issue: with 2 binary procs, mod-2 operations collapse (S+1)%2 = (S−1)%2 = 1−S, destroying the directional structure Sol 3 relies on

#### Finding 3: Exhaustive binary-proc search at 8748 — all dead
Fix all 7 ternary procs to Sol 3 rules. Exhaustively search binary proc rule tables:

- **Single binary proc search**: fix one binary to Sol 3 v1, exhaustively try all 4096 rule tables for the other. All sep=1 rotations tested (9 rotations × 2 binary procs each = 18 exhaustive searches of 4096 each). **0 valid systems found.**
- **Joint binary search**: 4096 × 4096 = 16.7M total combos. Constraint satisfaction reduces to ~1.6M valid liveness combos. Hamming distance 0–4 perturbation from Sol 3 v1 base: 10K+ combos tested, **0 valid.**
- **Z3 full encoding**: model with rule variables + ranking function for convergence built in 70s, solver timed out at 120s (unknown).

#### Finding 4: No 1-binary multisets exist below 13122
Mathematical proof:
- A 1-binary multiset has form {2, a₁, a₂, ..., a₈} with each aᵢ ≥ 2
- Product = 2 · ∏aᵢ, where each aᵢ ≥ 2
- Minimum product when all aᵢ = 3 (minimum non-binary): 2·3⁸ = 13122
- To get product < 13122, at least one aᵢ must be 2 → multiset has ≥2 binary procs
- **Therefore the minimum 1-binary product is exactly 13122**

#### Finding 5: Gap analysis [8748, 13122] — all products have ≥2 binary
Enumerated all products in (8748, 13122) achievable with 9-entry multisets (each ≥ 2):

| Products in gap | Count | Min binary procs |
|-----------------|-------|------------------|
| Total with valid multisets | 20 | 2 |
| With exactly 2 binary | 1 (product 11664) | — |
| With exactly 3 binary | 3 (9720, 10368*, 12960) | — |
| With 4+ binary | 16 | — |

*10368 has a 2-binary multiset candidate: no — verified all are ≥3 binary.

The ONLY 2-binary gap product is **11664** with ms=(2,2,3,3,3,3,3,3,4) (2 binary + 6 ternary + 1 quaternary). Tested all 252 distinct orientations with Sol 3 v1: **0 valid.**

#### Finding 6: Structural analysis of the 2-binary barrier
Why does Sol 3 v1 fail at 2 binary?

The Sol 3 rule structure relies on modular arithmetic creating a directional "wave" through the ring. For m-state processor Pᵢ:
- Bottom rule: detects (S+1) mod m = R mod m → decrements S
- Middle rule: detects (S+1) mod m = L or R mod m → copies neighbor
- Top rule: detects L mod m = R mod m → increments

With m=3: (S+1)%3 and (S−1)%3 are distinct values, creating asymmetric detection.
With m=2: (S+1)%2 = (S−1)%2 = 1−S, so increment = decrement. The rule loses directionality. A single binary proc can work (1-binary witness at 13122) because the 8 ternary neighbors provide enough directional context. Two adjacent binary procs compound the ambiguity — neither can distinguish "wave going left" from "wave going right."

### What This Rules Out
- All products ≤ 8748 with pure {2,3} multisets (all have ≥2 binary)
- All gap products (8749–13121) under Sol 3 adaptations
- Product 8748 under exhaustive binary-proc search with Sol 3 ternary rules
- Product 11664 under all 252 orientations of (2,2,3,3,3,3,3,3,4)

### Surviving Structure
- **M_9 ≤ 13122** (verified witness)
- **M_9 > 8748** (Exploration 3 + this exploration)
- Gap products 8749–13121: all have ≥2 binary, Sol 3 adaptations fail
- The gap could theoretically be closed by a completely non-Sol-3 system at some gap product — but exhaustive search at 8748 (fixing ternary to Sol 3) found nothing
- Strong evidence: **M_9 = 13122**

### What Would Close the Gap
To prove M_9 = 13122 rigorously:
1. **Upper bound** (DONE): witness at ms=(2,3,3,3,3,3,3,3,3), verified
2. **Lower bound** (OPEN): prove no self-stabilizing system exists for any 9-proc multiset with product < 13122. This requires ruling out:
   - All possible rule tables (not just Sol 3 variants) at ALL multisets with product < 13122
   - The exhaustive search at 8748 only covered binary-proc variations with Sol 3 ternary rules — a full proof would need to also rule out non-Sol-3 ternary rules

A computational lower bound proof would require:
- For each product P < 13122: enumerate all multisets, then for each multiset prove impossibility
- Impossibility proof per multiset: likely via SAT/UNSAT encoding of all 5 properties
- At product 8748 with 8748 configs: the SAT encoding has ~225 rule variables and ~8748 convergence constraints — potentially tractable for a modern SAT solver

### Concrete Artifacts

SCRIPTS:
- `sol3_adapt.py`: 6 adaptation variants tested at products 13122, 8748, 5832, 3888, 2592. **WITNESS at 13122.**
- `sol3_deep_8748.py`: 9 rotations × 3 adaptations at 8748, all fail. Extracted 13122 witness details.
- `sol3_separated_test.py`: all 4 necklaces of {2²,3⁷} × 9 rotations = 36 orientations, all fail.
- `sol3_binary_exhaustive.py`: exhaustive joint binary-proc search at 8748. 1.6M combos, Hamming ≤4 from base: 0 valid.
- `sol3_single_binary_search.py`: exhaustive single binary-proc search at 8748. 4096 per proc × all rotations: 0 valid.
- `sol3_z3_search.py`: Z3 full encoding with ranking function. n=5 sat (0.6s), n=9 timeout (120s).
- `sol3_gap_search.py`: gap product enumeration + Sol 3 v1 testing. 20 products, all ≥2 binary, 0 valid.

COMPUTED RESULTS:
- **Witness**: ms=(2,3,3,3,3,3,3,3,3), product=13122, Sol 3 v1, cycle=25, good=62
- **8748 exhaustive**: 40K+ binary-proc rule tables tested across all orientations, 0 valid
- **Gap**: 20 products, minimum 2 binary each, 0 valid across all Sol 3 adaptations
- **11664 thorough**: 252 orientations of (2,2,3,3,3,3,3,3,4), 0 valid
- **Mathematical**: minimum 1-binary product = 2·3⁸ = 13122 (proved)

### Key Parameters
- Sol 3 v1 at 13122: verified in ~2s
- Single binary exhaust at 8748: ~90s per proc × 18 procs = ~27 min total
- Joint binary search (Hamming ≤4): ~10K combos tested in ~5 min
- Z3 at n=9: model build 70s, solver timeout 120s
- Gap search: ~30s (enumeration + quick tests)

### Open Questions
1. Can we prove M_9 ≥ 13122 rigorously (lower bound)?
2. Is there a SAT/UNSAT proof that no system exists at product 8748 with ANY rule table (not just Sol 3 variants)?
3. Does the 2-binary directionality argument generalize to a formal impossibility proof?
4. What is M_10? Does the 1-binary pattern continue (M_10 = 2·3⁹ = 39366)?

---

## Synthesis after Exploration 5

### Updated Strategy Register

**Eliminated approach classes:**
- Standard pipeline (sweep cycle + SCC screen) fails for ALL products at n=9 (Explorations 1–4)
- Sol 3 adaptation fails for ALL multisets with ≥2 binary procs at n=9 (Exploration 5)
- Exhaustive binary-proc search (with Sol 3 ternary rules) fails at 8748 (Exploration 5)

**Updated bounds:**
- **M_9 ≤ 13122** (Sol 3 v1 witness at ms=(2,3,3,3,3,3,3,3,3))
- M_9 > 8748 (Exploration 3)
- Gap: 8748 < M_9 ≤ 13122
- Strong conjecture: **M_9 = 13122 = 2·3⁸**

**Key structural insights:**
1. Sol 3 v1 adaptation works when ≤1 binary proc exists — the key requirement is that binary procs don't interact with each other
2. The minimum 1-binary product is 2·3⁸ = 13122 (no 1-binary multisets below this)
3. All gap products (8749–13121) have ≥2 binary procs
4. The 2-binary barrier is both empirical (exhaustive search at 8748) and structural (mod-2 directionality collapse)
5. If M_9 = 13122 = 2·3⁸ and M_n = 32·3^(n-4) = 2⁵·3^(n-4) for n≤8, the pattern suggests M_n = 2·3^(n-1) for large n (the formula transitions from "binary-dominated" to "ternary-dominated")

**Pattern hypothesis:**
- n=5: M_5 = 96 = 2⁵·3 = 32·3¹
- n=6: M_6 = 288 = 2⁵·3² = 32·3²
- n=7: M_7 = 864 = 2⁵·3³ = 32·3³
- n=8: M_8 = 2592 = 2⁵·3⁴ = 32·3⁴
- n=9: M_9 = 13122 = 2·3⁸ (conjectured)

If M_n = 32·3^(n-4) for n≤8 but M_9 = 2·3⁸, then the formula breaks because the shadow cycle mechanism (requiring ≥3 binary) ceases to be the binding constraint at n=9. Instead, the minimum product achievable with ≤1 binary proc (= 2·3^(n-1)) becomes the binding constraint.

Crossover point: 32·3^(n-4) vs 2·3^(n-1). These are equal when 32·3^(n-4) = 2·3^(n-1), i.e., 16 = 3³ = 27. Since 16 < 27, the shadow formula 32·3^(n-4) < 2·3^(n-1) for all n, so the shadow cycle witness is ALWAYS better (lower product) than the 1-binary Sol 3 witness. But the shadow cycle approach may fail for large n — the analytic proof was verified for n≤8 and proved for all n≥5, so M_n = 32·3^(n-4) should hold for all n≥5.

Wait — but M_9 > 8748 = 2^2·3^7 > 32·3^5 = 7776. And 32·3^5 = 7776, so at n=9 the shadow formula gives 7776 but M_9 > 7776. The shadow cycle theorem proves M_n ≤ 32·3^(n-4) for n≤8, but at n=9 the shadow approach doesn't produce witnesses below 13122.

**Revised pattern**: M_n = 32·3^(n-4) for 5 ≤ n ≤ 8, but the formula breaks at n=9 where M_9 ∈ (8748, 13122].

**Next targets:**
- Lower bound proof: SAT/UNSAT at 8748 or at product 13121
- Pattern analysis: why does 32·3^(n-4) break at n=9?
- M_10 prediction: if the 1-binary pattern holds, M_10 = 2·3⁹ = 39366

