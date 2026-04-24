# Strategy Register

## Eliminated approach classes

- Exploration 5: Any attempt to prove the 6-shadow theorem for all fair length-8 `Q4` cycles is dead. The property is false outside the conflict-free subclass.
- Exploration 19: Broad generic multi-start DFS as the main route for strengthening `n=5` controller-capacity evidence is a dead tactical class. It is too blunt compared with structural/controller reinterpretation of the old shadow proofs.

## Obstructions

- Exploration 3: In every conflict-free fair binary `Q4` cycle, after forgetting any one processor, every repeated 3-bit shadow supports at most 2 distinct movers. So binary obstruction-free dynamics cannot realize a 3-way local router on one repeated local context.
- Exploration 4: The projected geometry of conflict-free binary `Q4` cycles is rigid: after forgetting any processor, the 8-step cycle projects to exactly 6 distinct 3-bit shadows, with exactly 2 repeated shadows and 4 singleton shadows. This excludes any binary obstruction-free model for the witness’s all-8-shadow, multi-tripled projected behavior.
- Exploration 7: Binary obstruction-freeness at `n=4` is a word-level phenomenon. Among all 648 simple closed balanced 8-step mover words, exactly 8 avoid the symbolic signature-conflict condition, and they are precisely the cyclic/reverse-cyclic `σ σ` words.
- Exploration 12: The word theorem has a short local obstruction. If the first-half permutation `σ` contains an adjacent antipodal pair `anti(j), j`, then the processor `j` sees the same local signature before those two consecutive moves, first as non-mover and then as mover, so TF conflict is immediate. On `C4`, “no adjacent antipodal pair” is equivalent to `σ` being cyclic or reverse-cyclic.
- Exploration 14: The `w4` local 3-controller is irreducible to 2 states. Every merge of its three local states into two classes makes some merged class nondeterministic on a critical repeated shadow, so no binary-style deterministic 2-controller can recover the same local behavior.
- Exploration 17: The remaining binary proof gap is genuinely concentrated in the second-half agreement lemma `σ τ`, `τ ≠ σ => conflict`; the naive “first mismatch directly gives the conflict” approach is false.

## Building blocks

- Exploration 1: The optimal `M_4 = 24` witness `w4opt` uses state profile `(2,2,2,3)` with a 16-cycle good orbit. The ternary site is processor `3`.
- Exploration 1: Decoding `w4optGoodCycleCodes` as `(x0,x1,x2,x3)` with `x3 ∈ {0,1,2}` gives:
  `[(0,0,0,0),(1,0,0,0),(1,1,0,0),(1,1,1,0),(1,1,1,1),(1,1,0,1),(1,1,0,2),(0,1,0,2),(0,1,0,0),(0,1,1,0),(0,0,1,0),(1,0,1,0),(1,0,1,1),(0,0,1,1),(0,0,1,2),(0,0,0,2)]`.
- Exploration 1: Along the good cycle, the ternary coordinate distribution is `x3=0` eight times, `x3=1` four times, `x3=2` four times.
- Exploration 2: For the witness shadow projection `(x0,x1,x2)`, the repeated shadows `(1,1,0)` and `(0,0,1)` each occur with all three ternary values `x3=0,1,2`, and these three phase values correspond to three distinct movers `{left of P3, P3, right of P3}`.
- Exploration 2: More generally, the witness can be viewed as a control automaton over 3-bit shadows, where the ternary coordinate at `P3` disambiguates which outgoing edge is taken from a repeated binary shadow.
- Exploration 3: Across all 16 conflict-free fair `Q4` cycles and all 4 forgetful projections `Q4 -> {0,1}^3`, the maximum number of distinct movers attached to a repeated projected shadow is exactly 2.
- Exploration 3: The optimal witness violates this binary ceiling at the ternary forgetful projection: shadows `(1,1,0)` and `(0,0,1)` each support 3 distinct movers.
- Exploration 4: Every projected conflict-free binary cycle has signature “two doubled shadows + four singletons.” The `24`-state witness projection forgetting the ternary site uses all 8 shadows, with two shadows tripled, four doubled/singleton mixes, and two 3-way router shadows.
- Exploration 6: Conflict-free fair binary cycles are exactly the `σσ` mover words where `σ` is a cyclic or reverse-cyclic ordering of the ring processors. This reduces the binary side from a search over cycles to a tiny symbolic family.
- Exploration 7: The no-conflict criterion can be tested symbolically from prefix parities alone, without referring to start state or explicit cycle configs. This is a reusable formal object.
- Exploration 8: For every `σ σ` word and forgotten processor `p`, the projected binary walk has a closed-form signature: exactly two repeated shadows, those two are complements, and both carry mover set `{p, succσ(p)}`.
- Exploration 9: In the optimal witness `w4opt`, forgetting any binary processor yields projected router capacity at most `2`; forgetting the ternary processor `3` is the unique projection with router capacity `3`.
- Exploration 10: On the critical complementary shadow pair `(0,0,1)/(1,1,0)`, the witness’s 3-way mover set `{0,2,3}` is exactly the union of the two binary cyclic sweep options for forgetting processor `3`: one orientation gives mover pair `{0,3}`, the opposite orientation gives mover pair `{2,3}`.
- Exploration 11: In the explicit optimal witnesses for `n=4,5,6,7,8`, every projection with router capacity `3` exhibits a repeated shadow whose mover set is exactly the local triple `{left(p), p, right(p)}` of the forgotten processor `p`.
- Exploration 13: In all observed critical witness routers, the forgotten processor’s local state deterministically chooses the mover on the repeated shadow. When `m_p = 3`, the three state values bijectively realize `{left(p), p, right(p)}`; when `m_p = 4`, one of those three choices is duplicated.
- Exploration 15: Every critical witness controller from `w4` through `w8` is irreducible to 2 states, and every observed 4-state critical controller quotients cleanly to a deterministic 3-state controller. So the essential control complexity across the witness family is exactly 3.
- Exploration 16: In direct samples of consistent `n=5` product-72 cycles for both sub-threshold families `(2,2,2,3,3)` and `(2,2,3,2,3)`, every sampled cycle had controller-capacity profile `(2,2,2,2,2)`. No sampled sub-threshold cycle exhibited a 3-controller at any processor.
- Exploration 18: Stronger canonical-start `n=5` probes confirm 40 consistent length-10 cycles in each product-72 family, all with controller-capacity profile `(2,2,2,2,2)`.
- Exploration 20: The old product-72 shadow theorem is best understood as the dynamic half of the controller route: repeated-shadow deterministic 2-controller reuse induces a bad recurrent orbit.
- Exploration 21: For the standard `(2,2,2,3,3)` 10-cycle, the shadow cycle can be written step by step as reused good-cycle mover entries on non-good repeated shadows.
- Exploration 22: The same controller-language shadow construction works for the split-binary product-72 family `(2,2,3,2,3)`.
- Exploration 24: Across the first 40 canonical-start cycles in both product-72 families, the shadow mover words fall into the same four 10-step words, i.e. the same two 5-step rotation classes.
- Exploration 27: In all observed 4-state critical witness controllers, states `0` and `2` realize the same branch; the canonical quotient `(0,1,0,2)` captures the common 3-controller shape.
- Exploration 28: In the standard product-72 cycles, forgetting processor `3` yields the pair-controller `{3,4}`, while the threshold witness `w5` has a critical repeated shadow with controller `{2,3,4}`.
- Exploration 29: In 10 sampled canonical-start cycles from each product-72 family, the repeated-shadow pair-controllers at forgotten processor `3` are exactly `{2,3}` and `{3,4}` in the same `12/8` counts.
- Exploration 30: A PA pass distilled the binary proof into a short lemma chain and isolated the only real hard point: the second-half agreement lemma.
- Exploration 31: A PA pass distilled the dynamic theorem into the right abstract shape: reuse-closed deterministic repeated-shadow controller subsystem implies bad recurrence.

## Known reformulations

- Exploration 1: Decode the witness orbit as a binary triple plus a ternary phase register `(x0,x1,x2 ; x3)`.
  LOAD-BEARING ASSESSMENT: promising. This representation makes visible that the extra state resource is concentrated at one processor and used sparsely, which is exactly the kind of asymmetry a sub-threshold impossibility proof should try to characterize.
- Exploration 2: Shadow-control reformulation. Forget full 24-state configs and regard the witness as a walk on 3-bit shadows plus a local control state at one processor.
  LOAD-BEARING ASSESSMENT: high. This makes visible a candidate necessary feature for threshold validity: a processor may need to realize multiple distinct local routing decisions at the same binary shadow. That is the kind of statement that could force `m_i ≥ 3` without brute force.
- Exploration 3: Router-capacity reformulation. A processor with `m_i` states acts as a local router over the repeated shadows obtained by forgetting that processor. Binary obstruction-free dynamics has router capacity at most 2 on each repeated shadow; the `24`-state witness needs router capacity 3 at one repeated shadow.
  LOAD-BEARING ASSESSMENT: very high. This is the first reformulation that directly compares the threshold witness to all obstruction-free binary skeletons in a way that could plausibly become a theorem.
- Exploration 4: Projected-shadow signature reformulation. Instead of looking only at local capacity, classify the whole forgetful projection by the multiplicity profile of projected shadows. Binary obstruction-free cycles have a uniform 6-shadow signature; the witness has an 8-shadow signature with two tripled routers.
  LOAD-BEARING ASSESSMENT: high. This gives a global combinatorial invariant that may be easier to prove analytically from cycle structure than the full router story alone.
- Exploration 6: Mover-word reformulation. The relevant binary obstruction-free family is not “all conflict-free cycles” abstractly but the explicit symbolic class
  `σ σ` with `σ` a cyclic or reverse-cyclic permutation of `(0,1,2,3)`.
  LOAD-BEARING ASSESSMENT: very high. This is the cleanest bridge so far from computation to proof. If formalized, it turns the binary obstruction side into a finite symbolic normal form rather than a brute-force fact.
- Exploration 7: Prefix-signature reformulation. For a mover word `w`, the TF context seen by processor `j` at time `t` is determined by the prefix parity vector before `t`. TF conflict occurs exactly when some processor `j` sees the same local signature twice with opposite mover status.
  LOAD-BEARING ASSESSMENT: extremely high. This converts the binary side from state-space geometry into a pure combinatorics-on-words theorem. It is the best candidate so far for replacing the heavy `native_decide` core with a hand proof.
- Exploration 8: Closed-form projection reformulation. Once the mover word is in `σ σ` normal form, the forgetful projection is no longer mysterious data; it is a 3-bit walk with two complementary repeated shadows controlled by the local pair `{p, succσ(p)}`.
  LOAD-BEARING ASSESSMENT: extremely high. This makes the 6-shadow theorem effectively a one-line corollary of the word normal form, and it explains why binary obstruction-free routing is inherently 2-way.
- Exploration 9: Distinguished-forgetful-site reformulation. The threshold witness does not violate the binary ceiling in an arbitrary projection; the violation appears exactly when one forgets the processor carrying the extra state. This points to a necessity theorem about “router capacity of the forgotten processor.”
  LOAD-BEARING ASSESSMENT: high. This suggests the right lower-bound statement may be processor-local: if forgetting processor `p` reveals a repeated-shadow router of capacity `> 2`, then `m_p ≥ 3`.
- Exploration 10: Orientation-fusion reformulation. The ternary witness may be understood as fusing the two binary sweep orientations on one repeated complementary shadow pair. The third state is what lets the system realize both local neighbor choices at the same projected shadow, instead of committing to one orientation.
  LOAD-BEARING ASSESSMENT: very high. This is the first bridge that explains *why* the ternary site is needed in witness terms while remaining directly comparable to the binary normal forms.
- Exploration 11: Local-triple router reformulation. Threshold witnesses appear to use extra memory only to realize a repeated shadow with mover set `{left(p), p, right(p)}` for some forgotten processor `p`; even when many states are available, the witnessed excess capacity remains exactly `3`.
  LOAD-BEARING ASSESSMENT: extremely high. This is the first pattern that visibly persists across `n=4..8`, and it points to a general lower-bound mechanism: sub-threshold systems may be unable to realize local-triple routing on repeated shadows.
- Exploration 13: State-deterministic router reformulation. The repeated-shadow router is not just a set-valued phenomenon; on the witness family, the forgotten processor’s value itself is the control register that selects the local mover. Extra states beyond `3` refine this controller but do not add a fourth routing branch.
  LOAD-BEARING ASSESSMENT: extremely high. This is the strongest witness-side mechanism found so far. It suggests the right necessity statement may be about a processor encoding a deterministic local controller for the three directions `{left,self,right}`, not merely about set cardinalities.
- Exploration 14: Irreducible-controller reformulation. The witness controller is not merely larger than a binary controller; it cannot be quotiented to a deterministic 2-state controller on the critical repeated shadows. This makes the “3 states are really needed” claim much sharper.
  LOAD-BEARING ASSESSMENT: high. This is still witness-family evidence rather than a general theorem, but it pinpoints the exact failure mode of any 2-state replacement: nondeterministic local routing on the same repeated shadow.
- Exploration 15: Exact controller-complexity reformulation. The witness family suggests a precise invariant:
  the critical repeated-shadow controller has minimal deterministic quotient size `3`.
  LOAD-BEARING ASSESSMENT: extremely high. This is stronger than cardinality, stronger than “there exists a 3-router,” and much closer to a clean theorem schema: sub-threshold side has controller complexity at most `2`, witness side has controller complexity exactly `3`.
- Exploration 16: First `n=5` scaling reformulation. The controller-complexity split may already separate the `M_5` threshold witness from known sub-threshold consistent-cycle families: sampled sub-threshold cycles remain in the uniform `2`-controller regime.
  LOAD-BEARING ASSESSMENT: medium-high. This is still sample-based rather than exhaustive, but it is the first direct signal that the controller-complexity invariant may scale to the next case rather than being an `M_4` artifact.
- Exploration 12: Adjacent-antipair reformulation. The binary `n=4` word theorem reduces to a forbidden local pattern in the first-half permutation `σ`: adjacent antipodal jumps are exactly what create symbolic TF conflicts.
  LOAD-BEARING ASSESSMENT: extremely high. This turns the hardest-looking part of the binary theorem into a short hand-proof candidate:
  `no conflict => no adjacent antipodal pair => cyclic/reverse-cyclic`.
- Exploration 20: Shadow-cycle reformulation. The old small-`n` shadow theorems are not a separate obstruction mechanism; they are the dynamic manifestation of repeated-shadow controller reuse in the deterministic 2-controller regime.
  LOAD-BEARING ASSESSMENT: very high. This unifies the old product-72 impossibility proofs with the new controller-complexity program.
- Exploration 28: Pair-fusion reformulation at `n=5`. The threshold witness appears to fuse the pair-controllers `{2,3}` and `{3,4}` seen in the sub-threshold families into the triple-controller `{2,3,4}`.
  LOAD-BEARING ASSESSMENT: high. This is the strongest concrete `M_4/M_5` bridge so far.
- Exploration 31: Reuse-region reformulation. The right dynamic theorem is not “2-controller implies bad orbit” simpliciter, but “a reuse-closed deterministic repeated-shadow controller subsystem yields bad recurrence.”
  LOAD-BEARING ASSESSMENT: extremely high. This cleanly separates the abstract recurrence theorem from the family-specific work of constructing the bad reuse region.

## Exploration 1 (probe)

### Strategy
Inspect the optimal `24`-state witness directly to see what structural resource it uses that is absent below threshold.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES: `w4optGoodCycleCodes = [0,1,3,7,15,11,19,18,2,6,4,5,13,12,20,16]`, which decode to
`[(0,0,0,0),(1,0,0,0),(1,1,0,0),(1,1,1,0),(1,1,1,1),(1,1,0,1),(1,1,0,2),(0,1,0,2),(0,1,0,0),(0,1,1,0),(0,0,1,0),(1,0,1,0),(1,0,1,1),(0,0,1,1),(0,0,1,2),(0,0,0,2)]`.

STRUCTURAL RESULTS: The witness does not use the extra state to create a longer good cycle than binary `Q4`; the good cycle still has length `16`. The ternary resource instead appears as a sparse local phase register at processor `3`.

REPRESENTATIONS: Viewing witness states as `(x0,x1,x2 ; x3)` with three binary coordinates and one ternary coordinate makes visible that `x3` behaves more like a control/phase variable than bulk memory.

## Exploration 2

### Strategy
Treat the optimal witness as a control system over 3-bit shadows and ask whether the ternary site is really being used to disambiguate different outgoing moves at the same binary shadow.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This does not yet rule out an approach class, but it weakens the idea that the extra state is only used for a global phase count detached from local routing. In the `n=4` witness, the extra state is visibly local and operational.

### Surviving Structure
- The witness mover sequence is
  `[0,1,2,3,2,3,0,3,2,1,0,3,0,3,2,3]`.
- Grouping by 3-bit shadow `(x0,x1,x2)`, the repeated shadows carry different movers depending on `x3`:
  - `(1,1,0)`: `(x3,mover) = (0,2), (1,3), (2,0)`
  - `(0,0,1)`: `(x3,mover) = (0,0), (1,3), (2,2)`
  - `(1,1,1)`: `(0,3), (1,2)`
  - `(1,0,1)`: `(0,3), (1,0)`
  - `(0,1,0)`: `(2,3), (0,2)`
  - `(0,0,0)`: `(0,0), (2,3)`
- At the two critical shadows `(1,1,0)` and `(0,0,1)`, the three movers are exactly the local triple `{left of P3, P3, right of P3}`.

### Reformulations
The witness is better understood as a **local router with memory** than as a raw 24-state cycle. The 3-bit shadow specifies the binary environment; the ternary value at `P3` specifies which outgoing move from that environment is currently enabled.

LOAD-BEARING ASSESSMENT: yes. This is a plausible bridge from upper-bound witness analysis to lower-bound necessity. A native_decide-free proof could try to show that any valid `n=4` system needs some processor to act as such a 3-way local router on a repeated binary shadow, forcing at least 3 states at that processor.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Witness mover sequence:
  `[0,1,2,3,2,3,0,3,2,1,0,3,0,3,2,3]`.
- Shadow-occurrence table:
  - `(0,0,0) -> [(t=0,x3=0,m=0), (t=15,x3=2,m=3)]`
  - `(0,0,1) -> [(10,0,0), (13,1,3), (14,2,2)]`
  - `(0,1,0) -> [(7,2,3), (8,0,2)]`
  - `(0,1,1) -> [(9,0,1)]`
  - `(1,0,0) -> [(1,0,1)]`
  - `(1,0,1) -> [(11,0,3), (12,1,0)]`
  - `(1,1,0) -> [(2,0,2), (5,1,3), (6,2,0)]`
  - `(1,1,1) -> [(3,0,3), (4,1,2)]`

STRUCTURAL RESULTS:
- The ternary site at `P3` is not merely counting laps globally. It resolves different local successor choices at fixed binary shadows.
- Two shadows require a full 3-way routing choice; binary memory would only support at most 2 local phases at one processor.

TOOLS:
- Small Python probes reconstructing shadow occurrences, mover sequence, and the `(shadow, x3) -> mover` table from `w4optGoodCycleCodes`.

REPRESENTATIONS:
- `shadow = (x0,x1,x2)` together with local control value `x3`.
- `(shadow, x3) -> mover` table as the witness’s local control automaton.

### What Would Unblock This
- A structural lemma about arbitrary valid `n=4` good cycles showing that some repeated 3-bit shadow must support at least 3 distinct outgoing local choices.
- Alternatively, a classification of fair `Q4` obstruction-free skeletons that shows the witness is a phase-lift of an 8-cycle skeleton whose trap can only be broken by splitting a repeated shadow into at least 3 phases.

### Key Parameters
- Tested only the optimal witness `w4opt` with profile `(2,2,2,3)`.
- Projection used: forget processor `3` and keep `(x0,x1,x2)`.

### Open Questions
- Is the witness a lift of one of the 16 conflict-free `Q4` 8-cycles, or is the relationship looser?
- Can the “3-way local router” phenomenon be proved necessary for any valid `n=4` system, not just exhibited by the witness?
- Does the same local-routing-memory perspective explain the quaternary/phase-counter phenomena already seen for `n=5,6` witnesses?

## Exploration 3

### Strategy
Compare the witness’s shadow-control behavior against all obstruction-free binary `Q4` cycles by forgetting one processor and measuring how many distinct movers can occur on the same repeated 3-bit shadow.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out any `native_decide`-free lower-bound strategy that treats the witness’s ternary site as a cosmetic refinement of an obstruction-free binary cycle. The witness uses a routing behavior that binary obstruction-free cycles simply do not exhibit.

### Surviving Structure
- There are exactly 16 conflict-free fair `Q4` cycles, all of length 8.
- For each such cycle and each forgotten processor `p ∈ {0,1,2,3}`, if one groups cycle positions by the projected 3-bit shadow on the other processors, every repeated shadow carries at most 2 distinct movers.
- The global maximum over all 16 cycles and all 4 projections is exactly 2.
- In the optimal witness `w4opt`, forgetting the ternary processor `3` yields repeated shadows with 3 distinct movers:
  - `(1,1,0)`: movers `{2,3,0}`
  - `(0,0,1)`: movers `{0,3,2}`

### Reformulations
The right invariant may be **router capacity on repeated projected shadows**:

- choose a processor `p`
- project away `p`
- for each repeated projected shadow `σ`, count how many distinct movers occur at states mapping to `σ`

Binary obstruction-free skeletons have capacity `≤ 2`; the threshold witness needs capacity `3`.

LOAD-BEARING ASSESSMENT: yes. This turns the vague “extra phase memory” story into a sharp combinatorial invariant that separates the witness from every conflict-free binary skeleton.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Across all 16 conflict-free fair `Q4` cycles and all 4 forgetful projections, the maximum distinct-mover count on a repeated 3-bit shadow is `2`.
- Example from one binary conflict-free cycle, forgetting processor `3`:
  - shadow `(0,0,0)` occurs at `(forgotten bit,mover) = (0,0), (1,3)` giving movers `{0,3}`
  - shadow `(1,1,1)` occurs at `(0,3), (1,0)` giving movers `{0,3}`
- Witness counterexamples to the binary ceiling:
  - shadow `(1,1,0)` has `(x3,mover) = (0,2), (1,3), (2,0)`
  - shadow `(0,0,1)` has `(x3,mover) = (0,0), (1,3), (2,2)`

STRUCTURAL RESULTS:
- Binary obstruction-free local dynamics is 2-way on repeated projected shadows.
- The optimal witness requires 3-way local routing on repeated projected shadows.

TOOLS:
- A Python probe enumerating all fair `Q4` cycles, filtering TF-conflict cycles, projecting each cycle along each forgotten coordinate, and computing the repeated-shadow mover-capacity statistic.

REPRESENTATIONS:
- Forgetful projection `π_p : {0,1}^4 -> {0,1}^3`.
- Router-capacity statistic:
  `cap_p(C,σ) = |{ mover_t : π_p(cfg_t)=σ }|`.

### What Would Unblock This
- A proof that any valid `n=4` system with state profile below `24` must factor through a binary obstruction-free skeleton whose router capacity is at most 2.
- Or a direct theorem: if every processor has router capacity at most 2 on repeated projected shadows, then convergence fails.

### Key Parameters
- Binary reference family: all 16 conflict-free fair `Q4` cycles.
- Projection parameter: all 4 choices of forgotten processor.
- Witness tested: `w4opt` only, forgetting processor `3`.

### Open Questions
- Can the router-capacity `≤ 2` fact for conflict-free binary cycles be proved analytically from their 8-cycle structure?
- Is every valid `n=4` witness necessarily a lift of an obstruction-free binary skeleton, in a sense strong enough to transfer a router-capacity bound?
- For `n=5,6`, is there an analogous projection statistic on the optimal witnesses that exceeds the sub-threshold binary/ternary ceiling?

## Exploration 4

### Strategy
Strengthen the router-capacity probe by classifying the entire forgetful projection of every conflict-free binary `Q4` cycle, then compare that signature to the optimal `24`-state witness.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out a whole class of lower-bound stories that treat the witness as a mild phase refinement of a binary obstruction-free 8-cycle. Its projected geometry is not a small perturbation of any binary conflict-free projection.

### Surviving Structure
- For every one of the 16 conflict-free fair `Q4` cycles and every forgotten processor, the projected 3-bit shadow multiset has exactly:
  - 2 shadows appearing twice
  - 4 shadows appearing once
  - 2 shadows not appearing at all
- There are only 4 projection-signature types, corresponding to which adjacent mover pair appears on the repeated shadows:
  - repeated shadows with mover pair `{0,1}`
  - repeated shadows with mover pair `{1,2}`
  - repeated shadows with mover pair `{2,3}`
  - repeated shadows with mover pair `{0,3}`
- The optimal witness projection forgetting the ternary site uses all 8 shadows:
  - two shadows appear 3 times: `(1,1,0)` and `(0,0,1)`
  - several others appear twice
  - no shadow is missing

### Reformulations
The witness is not just a 3-way router locally; globally it is an **8-shadow completion** of a binary obstruction-free world that only ever exposes 6 shadows under forgetful projection.

LOAD-BEARING ASSESSMENT: yes. This suggests a two-level proof strategy:
1. classify binary obstruction-free projections analytically (6-shadow theorem),
2. show any valid threshold witness must escape that 6-shadow regime.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Binary conflict-free projection signature types:
  1. four singleton shadows with movers `{2},{3},{2},{3}` and two repeated shadows with mover pair `{0,1}`
  2. four singleton shadows with movers `{0},{3},{0},{3}` and two repeated shadows with mover pair `{1,2}`
  3. four singleton shadows with movers `{0},{1},{0},{1}` and two repeated shadows with mover pair `{2,3}`
  4. four singleton shadows with movers `{1},{2},{1},{2}` and two repeated shadows with mover pair `{0,3}`
- Witness projection forgetting processor `3`:
  - `(0,0,0)` occurs twice
  - `(0,0,1)` occurs three times with movers `{0,2,3}`
  - `(0,1,0)` occurs twice
  - `(0,1,1)` occurs once
  - `(1,0,0)` occurs once
  - `(1,0,1)` occurs twice
  - `(1,1,0)` occurs three times with movers `{0,2,3}`
  - `(1,1,1)` occurs twice

STRUCTURAL RESULTS:
- Binary obstruction-free projections are 6-shadow objects.
- The threshold witness is an 8-shadow object.
- The binary-to-threshold gap is therefore not only local routing capacity but also global projected support.

TOOLS:
- Python probe computing projection-signature multisets for all conflict-free `Q4` cycles.

REPRESENTATIONS:
- Projection signature = multiset of `(multiplicity, forgotten-bit set, distinct mover set)` over projected shadows.

### What Would Unblock This
- An analytic classification of conflict-free binary `Q4` cycles proving the 6-shadow theorem.
- A necessity argument that any valid `(2,2,2,3)` witness must use all 8 shadows under some projection, or at least must violate the 6-shadow theorem.

### Key Parameters
- Binary reference family: all 16 conflict-free fair `Q4` cycles, all 4 forgetful projections.
- Witness comparison: `w4opt`, forgetting the ternary processor `3`.

### Open Questions
- Can the 6-shadow theorem be proved directly from the alternating-pair 8-cycle description?
- Is “all 8 shadows appear” a theorem for every valid `(2,2,2,3)` system, or just this witness?
- Does the `n=5` witness exhibit an analogous “projected support exceeds sub-threshold ceiling” phenomenon?

## Exploration 5

### Strategy
Test the stronger conjecture that the 6-shadow signature might hold for all fair length-8 cycles in `Q4`, not just the conflict-free ones, in hopes of removing the TF-conflict hypothesis from the binary-side theorem.

### Outcome
FAILED

### Failure Constraint
The 6-shadow theorem is genuinely false for general fair length-8 `Q4` cycles. Among the 1296 fair length-8 cycles, only 336 satisfy the universal `[1,1,1,1,2,2]` projection multiplicity profile. A concrete counterexample is the fair 8-cycle
`[(0,0),(1,1),(3,0),(2,2),(6,1),(4,3),(12,2),(8,3)]`,
whose forgetful projection dropping processor `1` has multiplicities `[1,1,2,2,2]` rather than `[1,1,1,1,2,2]`.

### What This Rules Out
This rules out any approach that tries to deduce the needed projected-shadow rigidity from fairness + length-8 alone. The conflict-free hypothesis is load-bearing. Any analytic proof of the 6-shadow theorem must use structural properties specific to obstruction-free cycles, not just parity and cube geometry.

### Surviving Structure
- The 6-shadow theorem still holds for all 16 conflict-free fair cycles.
- The stronger statement fails sharply outside that class, which means the right proof target is likely “conflict-free cycles are alternating-pair 8-cycles,” then derive the 6-shadow theorem from that classification.

### Reformulations
This reframes the program:
do not classify all fair 8-cycles;
classify the **conflict-free** fair 8-cycles and prove the 6-shadow theorem inside that rigid family.

LOAD-BEARING ASSESSMENT: yes. The failure narrows the target theorem to the exact class that matters for the lower bound and prevents wasted effort on an overly broad false statement.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Total fair cycles in `Q4`: `29008`.
- Fair cycles of length `8`: `1296`.
- Length-8 fair cycles satisfying the 6-shadow theorem for all forgetful projections: `336`.
- Counterexample cycle:
  `[(0,0),(1,1),(3,0),(2,2),(6,1),(4,3),(12,2),(8,3)]`.
- For this counterexample, forgetting processor `1` yields shadow multiplicities `[1,1,2,2,2]`.

STRUCTURAL RESULTS:
- Conflict-free is not a cosmetic filter; it is exactly where the projected-shadow rigidity appears.

TOOLS:
- Python probe over all fair `Q4` cycles, restricted to length `8`, checking projection multiplicity profiles.

### What Would Unblock This
- An analytic classification of conflict-free fair cycles, ideally the alternating-pair 8-cycle description already hinted at in older `lb2222` analysis notes.
- A direct proof that alternating-pair 8-cycles imply the 6-shadow theorem.

### Key Parameters
- Universe tested: all fair `Q4` cycles of length `8`.
- Projection parameter: all 4 forgotten processors.

### Open Questions
- Can the alternating-pair classification be stated in a projection-friendly way that makes the 6-shadow theorem immediate?
- Among the 336 non-conflict-filtered 8-cycles satisfying the 6-shadow property, what extra condition singles out exactly the 16 conflict-free ones?

## Exploration 6

### Strategy
Characterize the conflict-free binary cycles by their mover words, starting from the empirical fact that all conflict-free cycles have length `8` and seem to repeat a 4-step pattern.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the need for a large combinatorial classification of binary obstruction-free cycles. The class is much smaller than “all conflict-free cycles viewed geometrically”; it is a tiny symbolic mover-word family.

### Surviving Structure
- Every conflict-free fair `Q4` cycle has mover word `σ σ`, where `σ` is a permutation of `{0,1,2,3}`.
- Among the 48 length-8 fair cycles with mover word `σ σ`, exactly the 16 with `σ` cyclic or reverse-cyclic are conflict-free.
- Equivalently, the conflict-free mover words are exactly:
  - cyclic shifts of `(0,1,2,3)`
  - cyclic shifts of `(0,3,2,1)`
- For each such `σ`, every start state in `Q4` yields a TF-conflict-free `σ σ` walk before quotienting by rotation.

### Reformulations
The binary obstruction-free world is exactly the world of **oriented ring sweeps repeated twice**. That means the binary side may admit a fully symbolic theorem:

1. conflict-free implies mover word `σ σ` with `σ` cyclic or reverse-cyclic,
2. any such word has the 6-shadow / capacity-2 projection signature.

LOAD-BEARING ASSESSMENT: yes. This is the first genuinely proof-shaped normal form on the sub-threshold side. It suggests the `native_decide`-free replacement for the heavy binary certificate should go through mover-word normal forms rather than ad hoc cycle enumeration.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Total fair length-8 cycles: `1296`.
- Length-8 fair cycles with mover word `σ σ` for some permutation `σ`: `48`.
- Conflict-free fair cycles: `16`.
- Every conflict-free fair cycle satisfies `σ σ`.
- Among `σ σ` words, TF-conflict-free occurs exactly for:
  - `(0,1,2,3)(0,1,2,3)`
  - `(1,2,3,0)(1,2,3,0)`
  - `(2,3,0,1)(2,3,0,1)`
  - `(3,0,1,2)(3,0,1,2)`
  - and the four reverse-cyclic analogues.

STRUCTURAL RESULTS:
- The conflict-free binary class is exactly the cyclic/reverse-cyclic sweep class.
- The 6-shadow theorem therefore only needs to be proved for cyclic/reverse-cyclic `σ σ` words.

TOOLS:
- Python probe checking all 24 permutations `σ`, all 16 starts, and testing TF conflict on the resulting `σ σ` walks.

REPRESENTATIONS:
- Mover-word normal form `σ σ`.
- Orientation class of `σ`: cyclic vs reverse-cyclic.

### What Would Unblock This
- A direct analytical proof that TF-conflict-freeness forces `σ` to be cyclic or reverse-cyclic.
- A symbolic proof that cyclic/reverse-cyclic `σ σ` words imply the 6-shadow theorem and router capacity `≤ 2`.

### Key Parameters
- Word class tested: all `24` permutations `σ`, doubled to `σ σ`.
- Start states tested: all `16` binary states of `Q4`.

### Open Questions
- Can the “cyclic or reverse-cyclic only” condition be derived from a simple local-overlap argument on TF contexts?
- Does the witness’s projected 10-step shadow walk decompose naturally as a controlled refinement of one cyclic/reverse-cyclic binary sweep?
- For `n=5,6`, is there an analogous mover-word normal form for the sub-threshold obstruction-free skeletons?

## Exploration 7

### Strategy
Recast binary TF conflict as a pure mover-word condition using prefix parities, then test this symbolic criterion on all balanced 8-step words rather than only on already constructed cycles.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the idea that the binary-side classification fundamentally needs explicit cube-cycle geometry or start-state casework. The relevant obstruction-free condition is already visible at the word level.

### Surviving Structure
- For a mover word `w` and processor `j`, let `p_t ∈ (Z/2)^4` be the prefix parity before step `t`.
- The local TF context signature seen by `j` at time `t` is
  `sig_j(t) = (p_t[left(j)], p_t[j], p_t[right(j)])`.
- If two times `t,u` have the same `sig_j` but `j` is mover at exactly one of them, then the word forces a TF conflict for processor `j`, independent of the start state.
- Exhaustive check over all balanced words of length 8:
  - total balanced words with each processor appearing twice: `2520`
  - simple closed words: `648`
  - simple closed words with no symbolic signature conflict: `8`
  - those `8` words are exactly the cyclic/reverse-cyclic `σ σ` words

### Reformulations
The binary `M_4` obstruction problem may now split cleanly:

1. **Word theorem**: classify all simple closed balanced 8-step words with no signature conflict. Result: exactly the cyclic/reverse-cyclic `σ σ` words.
2. **Projection theorem**: cyclic/reverse-cyclic `σ σ` words imply the 6-shadow / capacity-2 projection signature.
3. **Witness gap theorem**: any threshold-valid witness must exceed that projection capacity.

LOAD-BEARING ASSESSMENT: yes, decisively. This is the first formulation that feels robust enough to formalize without brute-force search: the hard part becomes a finite symbolic proof on 8-letter words and prefix parities, not a DFS over cycles.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Balanced 8-step mover words with counts `(2,2,2,2)`: `2520`
- Simple closed balanced words: `648`
- Simple closed balanced words with no prefix-signature conflict: `8`
- The `8` no-conflict words are exactly:
  - `(0,1,2,3,0,1,2,3)`
  - `(1,2,3,0,1,2,3,0)`
  - `(2,3,0,1,2,3,0,1)`
  - `(3,0,1,2,3,0,1,2)`
  - `(0,3,2,1,0,3,2,1)`
  - `(3,2,1,0,3,2,1,0)`
  - `(2,1,0,3,2,1,0,3)`
  - `(1,0,3,2,1,0,3,2)`

STRUCTURAL RESULTS:
- Binary TF conflict is independent of the start state once expressed via prefix signatures.
- The conflict-free binary class is exactly the word-theoretic cyclic/reverse-cyclic sweep class.

TOOLS:
- Python probe over all balanced length-8 words, checking simple closure and the symbolic prefix-signature conflict predicate.

REPRESENTATIONS:
- Prefix parity vector `p_t`.
- Signature predicate:
  `sig_j(t) = (p_t[left(j)], p_t[j], p_t[right(j)])`.
- Conflict criterion:
  repeated `sig_j` with opposite mover status.

### What Would Unblock This
- A pen-and-paper proof that among simple closed balanced 8-step words, the no-signature-conflict condition forces cyclic/reverse-cyclic `σ σ`.
- A clean formal encoding of prefix parities in Lean, probably as `Fin 4 -> Bool` or `Fin 4 -> Fin 2`.

### Key Parameters
- Universe tested: all balanced words of length `8` with multiplicity pattern `(2,2,2,2)`.
- Geometric filter: simple closed hypercube walk.
- Symbolic filter: no repeated signature with opposite mover status.

### Open Questions
- Can the no-signature-conflict classification be proved by a short local lemma on the first 4 letters of the word?
- Is there a direct derivation of the 6-shadow theorem from the prefix-signature model, without separately unpacking the cube geometry?
- For larger `n`, is there an analogue of the prefix-signature criterion that captures TF conflict symbolically on mover words?

## Exploration 8

### Strategy
Derive a closed-form description of the forgetful projections for `σ σ` mover words, rather than treating the 6-shadow theorem as another empirical statistic.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the need for a separate hard theorem “cyclic/reverse-cyclic `σ σ` implies 6-shadow.” The projection theorem is not an independent mystery; it is built into the `σ σ` word structure.

### Surviving Structure
- For any permutation `σ`, any `σ σ` walk on `Q4`, and any forgotten processor `p`:
  - exactly two projected shadows are repeated,
  - those two shadows are bitwise complements in `{0,1}^3`,
  - both repeated shadows carry the same mover set `{p, succσ(p)}`, where `succσ(p)` is the processor immediately after `p` in the cyclic order of the word `σ`.
- In particular, the projected router capacity is automatically `≤ 2`.
- For the conflict-free subclass, `succσ(p)` is always an actual ring neighbor of `p`, because `σ` is cyclic or reverse-cyclic.

### Reformulations
The binary side now has a full pipeline:

`no TF conflict`
`=>` `σ σ` with `σ` cyclic/reverse-cyclic
`=>` forgetful projection has two complementary repeated shadows
`=>` each repeated shadow has mover set exactly `{p, ring-neighbor of p}`

So the threshold witness exceeds the binary regime in a very specific way: it upgrades a 2-way complementary repeated-shadow router to a 3-way router on tripled shadows.

LOAD-BEARING ASSESSMENT: yes, decisively. This is the cleanest local-vs-global contrast yet and looks formalizable without any brute-force search.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Verified for all 24 permutations `σ` and all 4 forgotten processors `p`:
  - the two repeated shadows are complementary,
  - the repeated mover sets are exactly `{p, succσ(p)}`.
- Example:
  for `σ=(0,1,2,3)` and forgetting `p=3`, the repeated shadows are `000` and `111`, each with movers `{0,3}`.
- Example:
  for `σ=(0,2,3,1)` and forgetting `p=1`, the repeated shadows are `000` and `111`, each with movers `{0,1}`.

STRUCTURAL RESULTS:
- The 6-shadow theorem is an intrinsic consequence of `σ σ`.
- The repeated-shadow mover pair is controlled by local word order, not by the start state.

TOOLS:
- Python probe over all 24 permutations `σ`, checking repeated-shadow complementarity and the mover-pair formula for all forgotten processors.

REPRESENTATIONS:
- `succσ(p)`: the successor of `p` in the 4-letter word `σ`.
- Repeated-shadow theorem as a pair `(s, ¬s)` with mover set `{p, succσ(p)}`.

### What Would Unblock This
- A symbolic proof of the mover-word classification `no conflict => cyclic/reverse-cyclic σσ`.
- A matching necessity theorem on the witness side: some projection must realize a repeated shadow with mover set of size 3.

### Key Parameters
- Word class tested: all 24 permutations `σ`, doubled to `σ σ`.
- Projection parameter: all 4 forgotten processors.

### Open Questions
- Can the complement-pair theorem be proved directly from prefix parities with no geometric language at all?
- Is the witness’s 3-way routing best formulated as “tripled repeated shadow” or as “repeated shadow with mover set containing `{p, left(p), right(p)}`”?
- For `n=5,6`, do optimal witnesses similarly refine a binary/ternary sweep skeleton by splitting complementary repeated shadows?

## Exploration 9

### Strategy
Determine whether the witness’s 3-way routing is a diffuse projection artifact or is tied specifically to the processor carrying the extra state.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the broad statement “the witness has 3-way routing in many projections.” The phenomenon is sharply localized: the only projection that exceeds binary capacity is the one forgetting the ternary processor itself.

### Surviving Structure
- For `w4opt`, forgetting processors `0`, `1`, or `2` gives projected router capacity `2`.
- Forgetting processor `3` gives projected router capacity `3`.
- So the extra-memory processor is not merely adjacent to the routing phenomenon; it is exactly the coordinate whose removal exposes the forbidden 3-way router.

### Reformulations
The likely lower-bound invariant is:

`cap_p(C) := max over repeated shadows σ in the forgetful projection dropping p of`
`|{ movers at states projecting to σ }|`.

For binary obstruction-free systems, `cap_p ≤ 2` for every `p`.
For the optimal witness, `cap_3 = 3` while `cap_0 = cap_1 = cap_2 = 2`.

LOAD-BEARING ASSESSMENT: yes. This is the cleanest processor-local quantity yet. It suggests a theorem of the form “if `cap_p ≥ 3` then `m_p ≥ 3`,” which is tautologically plausible and potentially extensible to larger `n`.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Witness projection capacities:
  - forget `0`: max mover capacity `2`
  - forget `1`: max mover capacity `2`
  - forget `2`: max mover capacity `2`
  - forget `3`: max mover capacity `3`
- Critical `forget 3` repeated shadows:
  - `(1,1,0)` with movers `{0,2,3}`
  - `(0,0,1)` with movers `{0,2,3}`

STRUCTURAL RESULTS:
- The 3-way routing excess is uniquely attached to the non-binary site in the witness.
- Binary forgetful projections of the witness remain within the binary ceiling.

TOOLS:
- Python probe computing repeated-shadow mover capacities for each forgetful projection of the witness cycle.

REPRESENTATIONS:
- Processor-local router-capacity invariant `cap_p`.

### What Would Unblock This
- A proof that `cap_p ≥ 3` forces `m_p ≥ 3` in any system, not just the witness.
- A witness-side necessity statement showing some valid threshold-level system must have `cap_p ≥ 3` for some `p`.

### Key Parameters
- Tested only the optimal witness `w4opt`.
- Projections tested: all 4 forgotten processors.

### Open Questions
- Is `cap_p ≥ 3` actually necessary for every valid `(2,2,2,3)` system, or just this particular witness?
- For the `n=5,6` optimal witnesses, does the maximal-capacity projection again coincide with forgetting the largest-state processor?

## Exploration 10

### Strategy
Look for a direct bridge between the witness’s 3-way routing and the binary cyclic/reverse-cyclic sweep normal forms by comparing repeated-shadow pairs under the same forgetful projection.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This makes it less plausible that the witness’s ternary behavior is some unrelated higher-order gadget. At least at the critical complementary pair, it is visibly built from the two binary orientation options.

### Surviving Structure
- For forgetting processor `3`, the binary cyclic/reverse-cyclic `σ σ` words produce repeated complementary shadow pairs with 2-way mover sets:
  - one orientation realizes `(0,0,1)/(1,1,0)` with movers `{0,3}`
  - the opposite orientation realizes the same pair with movers `{2,3}`
- In `w4opt`, the same complementary pair `(0,0,1)/(1,1,0)` appears with mover set `{0,2,3}` at both shadows.
- So the witness is not inventing a totally new local picture; it is combining the two binary sweep choices at one projected local context.

### Reformulations
The ternary site behaves like an **orientation switch** for the binary sweep skeleton. Binary obstruction-free systems can only choose one local orientation at a repeated complementary pair. The threshold witness can realize both, because the extra state at the forgotten processor splits that pair into three local phases.

LOAD-BEARING ASSESSMENT: yes. This gives a plausible conceptual statement for the lower bound:
below threshold, a repeated complementary shadow pair can support at most one sweep orientation;
at threshold, validity requires being able to switch orientations locally.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Binary cyclic/reverse-cyclic projections forgetting processor `3`:
  - `σ=(2,3,0,1)` gives repeated pair `(0,0,1)/(1,1,0)` with movers `{0,3}`
  - `σ=(1,0,3,2)` gives repeated pair `(0,0,1)/(1,1,0)` with movers `{2,3}`
- Witness `w4opt`, forgetting processor `3`:
  - `(0,0,1)` occurs with movers `{0,3,2}`
  - `(1,1,0)` occurs with movers `{2,3,0}`

STRUCTURAL RESULTS:
- The witness’s critical 3-router is the union of the forward and reverse binary sweep routers on the same complementary repeated-shadow pair.

TOOLS:
- Python comparison of repeated-shadow pairs for cyclic/reverse-cyclic `σ σ` words and the witness projection.

REPRESENTATIONS:
- Orientation-fusion picture:
  forward `{p,right-neighbor}`
  vs reverse `{p,left-neighbor}`
  vs witness union `{p,left-neighbor,right-neighbor}`.

### What Would Unblock This
- A proof that validity at threshold requires local access to both orientations on some repeated complementary pair.
- A symbolic theorem saying binary obstruction-free systems cannot fuse these orientations without a TF conflict.

### Key Parameters
- Projection tested: forgetting processor `3`.
- Binary comparison class: cyclic/reverse-cyclic `σ σ` words only.

### Open Questions
- Can the witness be globally described as a binary sweep skeleton with local orientation-fusion at exactly one complementary pair, or is that only a local phenomenon?
- Is orientation-fusion the right abstraction for the `n=5,6` witnesses as well?

## Exploration 11

### Strategy
Test whether the `n=4` orientation-fusion / 3-router phenomenon is an isolated curiosity or persists in the known optimal witnesses for `n=5,6,7,8`.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the pessimistic view that the `n=4` router-capacity story is too special to be useful. The same local-triple routing pattern appears repeatedly in the higher-`n` optimal witnesses.

### Surviving Structure
- Witness router capacities by forgotten processor:
  - `w4`, `ms=(2,2,2,3)`: caps `[2,2,2,3]`
  - `w5`, `ms=(2,2,2,3,4)`: caps `[2,2,2,3,2]`
  - `w6`, `ms=(2,2,2,4,3,3)`: caps `[2,2,2,3,3,2]`
  - `w7`, `ms=(3,2,2,2,3,4,3)`: caps `[2,2,2,2,3,3,3]`
  - `w8`, `ms=(2,2,3,4,3,3,2,3)`: caps `[2,2,3,3,3,2,2,3]`
- In every case, whenever a forgotten processor `p` has capacity `3`, there exists a repeated shadow whose distinct movers are exactly the local triple `{left(p), p, right(p)}`.
- No witness among `n=4..8` needed capacity `> 3`, despite having processors with `4` states available.

### Reformulations
The emerging reusable invariant is not “large state counts” but **local-triple repeated-shadow routing**. The witnesses seem to use extra memory to unlock exactly one additional local direction, going from the binary `2`-router `{p, one neighbor}` to the threshold `3`-router `{left(p), p, right(p)}`.

LOAD-BEARING ASSESSMENT: yes, strongly. This is the first cross-`n` pattern that connects the `M_4` witness analysis directly to the higher witnesses. It suggests a lower-bound route that could plausibly scale:
prove sub-threshold systems cannot realize local-triple repeated-shadow routing, while optimal witnesses necessarily can.

### Concrete Artifacts

COMPUTED EXAMPLES:
- `w4`, forgetting `p=3`: repeated shadows `(1,1,0)` and `(0,0,1)` with movers `{0,2,3}`.
- `w5`, forgetting `p=3`: repeated shadow `(1,1,0,0)` with movers `{2,3,4}`.
- `w6`, forgetting `p=3`: repeated shadow `(1,1,1,0,0)` with movers `{2,3,4}`.
- `w6`, forgetting `p=4`: repeated shadow `(1,1,1,2,0)` with movers `{3,4,5}`.
- `w7`, forgetting `p=4`: repeated shadow `(2,1,1,0,0,0)` with movers `{3,4,5}`.
- `w7`, forgetting `p=5`: repeated shadow `(1,0,0,0,0,1)` with movers `{4,5,6}`.
- `w7`, forgetting `p=6`: repeated shadow `(0,1,1,1,0,1)` with movers `{5,6,0}`.
- `w8`, forgetting `p=2`: repeated shadow `(1,0,0,0,0,0,0)` with movers `{1,2,3}`.
- `w8`, forgetting `p=3`: repeated shadow `(0,0,0,1,2,0,2)` with movers `{2,3,4}`.
- `w8`, forgetting `p=4`: repeated shadow `(1,1,0,1,1,0,0)` with movers `{3,4,5}`.
- `w8`, forgetting `p=7`: repeated shadow `(0,0,0,0,0,0,0)` with movers `{7,0,6}`.

STRUCTURAL RESULTS:
- The witness-side excess capacity is uniformly `3` and locally geometric: left / self / right.
- Binary processors in these witnesses never exceed capacity `2`.

TOOLS:
- Python decoder/projection probe for the explicit witness cycles `w4` through `w8`, computing repeated-shadow router capacities and identifying local-triple shadows.

REPRESENTATIONS:
- Processor-local repeated-shadow capacity `cap_p`.
- Local-triple router condition:
  `∃ shadow σ repeated in projection forgetting p with mover set = {left(p), p, right(p)}`.

### What Would Unblock This
- A proof that local-triple repeated-shadow routing is necessary for threshold-level validity, at least for a broad class of witness-like cycles.
- A binary/sub-threshold theorem excluding local-triple routing under low state product.

### Key Parameters
- Tested explicit witness good cycles for `n=4,5,6,7,8`.
- Projection parameter: all forgotten processors in each witness.

### Open Questions
- Is local-triple routing necessary for every valid system near threshold, or only for the particular witness family in `Defs.lean`?
- Can the binary symbolic word theorem be generalized to show that low-state systems allow at most one neighbor direction on repeated shadows, never both?
- Is there a direct information-theoretic statement behind this: one extra state buys exactly one extra local routing branch?

## Exploration 13

### Strategy
Strengthen the cross-`n` local-triple routing pattern by checking whether the forgotten processor’s local state value deterministically selects the mover on the critical repeated shadows.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the interpretation that the repeated-shadow router is only a coarse set-valued effect of extra memory. In the witness family, the extra memory is being used as a genuine local control register.

### Surviving Structure
- For every critical witness projection found in explorations 9–11, the map
  `state of forgotten processor p` -> `mover at the repeated shadow`
  is deterministic.
- When `m_p = 3`, this map is a bijection onto `{left(p), p, right(p)}`.
- When `m_p = 4`, the image is still exactly `{left(p), p, right(p)}`; one of the three movers is realized by two different state values.

### Reformulations
The witness-side mechanism is now best described as a **3-direction local controller** stored at processor `p`.

- Binary/sub-threshold side: repeated shadows only admit a 2-way controller.
- Threshold witness side: some processor stores a deterministic 3-way controller for the local directions `{left, self, right}`.
- 4 states do not create a 4-way controller; they only add redundancy/refinement to the same 3-way controller.

LOAD-BEARING ASSESSMENT: yes, decisively. This is the first formulation that explains both why `3` states are enough and why `4` states may appear without changing the essential routing complexity. It feels like the right abstraction for a scalable lower-bound statement.

### Concrete Artifacts

COMPUTED EXAMPLES:
- `w4`, forget `p=3`, repeated shadow `(1,1,0)`:
  `x3=0 -> mover 2`, `x3=1 -> mover 3`, `x3=2 -> mover 0`.
- `w5`, forget `p=3`, repeated shadow `(1,1,0,0)`:
  `x3=0 -> 2`, `x3=1 -> 3`, `x3=2 -> 4`.
- `w6`, forget `p=4`, repeated shadow `(1,1,1,2,0)`:
  `x4=0 -> 3`, `x4=1 -> 4`, `x4=2 -> 5`.
- `w6`, forget `p=3` with `m_3=4`, repeated shadow `(1,1,1,0,0)`:
  `x3=0 -> 3`, `x3=1 -> 2`, `x3=2 -> 3`, `x3=3 -> 4`.
- `w7`, forget `p=5` with `m_5=4`, repeated shadow `(2,1,1,1,0,0)`:
  `x5=0 -> 4`, `x5=1 -> 5`, `x5=2 -> 4`, `x5=3 -> 6`.
- `w8`, forget `p=3` with `m_3=4`, repeated shadow `(1,1,0,0,0,0,0)`:
  `x3=0 -> 2`, `x3=1 -> 3`, `x3=2 -> 2`, `x3=3 -> 4`.

STRUCTURAL RESULTS:
- The essential witness resource is not “more than 2 states” abstractly; it is a deterministic controller for 3 local directions.
- Four-state witnesses seen so far use redundancy to realize the same 3-way control, not a fourth local branch.

TOOLS:
- Python probe over witness good cycles `w4`–`w8`, extracting repeated shadows with local-triple mover sets and tabulating the map from forgotten-state value to mover.

REPRESENTATIONS:
- Deterministic local controller:
  `ctrl_p,σ : state value at p -> {left(p), p, right(p)}` on a repeated shadow `σ`.

### What Would Unblock This
- A proof that any valid near-threshold system must have such a deterministic 3-direction local controller at some processor.
- A binary/sub-threshold theorem showing no processor can implement a deterministic 3-direction controller on a repeated shadow when all local capacities are below threshold.

### Key Parameters
- Witnesses tested: `w4` through `w8`.
- Critical projections: all forgotten processors `p` with repeated-shadow capacity `3`.

### Open Questions
- Is the duplicated branch in the `m_p = 4` cases always the “self” direction, or can it vary by witness?
- Can this deterministic controller viewpoint be extracted directly from the transition tables, without reference to a particular good cycle?

## Exploration 14

### Strategy
Test whether the `w4` 3-state local controller at the critical processor can be merged down to a binary 2-state controller while preserving deterministic local routing on the critical repeated shadows.

### Outcome
SUCCEEDED

### Failure Constraint
Every merge of the three local states `{0,1,2}` into two classes causes some merged class to correspond to multiple movers on a critical repeated shadow. So the quotient ceases to be a deterministic controller.

### What This Rules Out
This rules out the idea that the witness’s 3-state controller is just a cosmetic refinement of a 2-state controller. At least for `w4`, there is no deterministic 2-state quotient compatible with the critical repeated-shadow routing data.

### Surviving Structure
- Critical shadows for `w4`, forgetting processor `3`:
  - `(1,1,0)` with controller map `0 -> 2`, `1 -> 3`, `2 -> 0`
  - `(0,0,1)` with controller map `0 -> 0`, `1 -> 3`, `2 -> 2`
- The three possible merges of `{0,1,2}` to two states are:
  - `{0,1}|{2}`
  - `{0,2}|{1}`
  - `{1,2}|{0}`
- Under each merge, some merged state on a critical shadow carries two different movers, so determinism is lost immediately.

### Reformulations
The witness-side statement can be sharpened from
“there exists a 3-way router”
to
“there exists a repeated shadow on which the forgotten processor implements an irreducible deterministic 3-controller.”

LOAD-BEARING ASSESSMENT: yes. This is a cleaner necessity target than raw cardinality. If generalized, it would say that threshold validity requires an irreducible 3-controller at some processor, which binary/sub-threshold systems cannot supply.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Merge `{0,1}|{2}` on shadow `(1,1,0)`:
  merged state `0` carries movers `{2,3}`.
- Merge `{0,2}|{1}` on shadow `(1,1,0)`:
  merged state `0` carries movers `{0,2}`.
- Merge `{1,2}|{0}` on shadow `(0,0,1)`:
  merged state `0` carries movers `{2,3}`.
- So all three binary quotients fail determinism on at least one critical shadow.

STRUCTURAL RESULTS:
- The `w4` controller is irreducibly ternary.
- The obstruction to binary reduction is local and explicit: nondeterminism on one repeated shadow.

TOOLS:
- Python probe enumerating the 3 possible 2-state merges of the witness controller and checking deterministic routing on the critical repeated shadows.

REPRESENTATIONS:
- Controller quotient test:
  merge local states and inspect merged-state -> mover relation on repeated shadows.

### What Would Unblock This
- A proof that any valid `(2,2,2,3)` system must contain such an irreducible 3-controller.
- Extension of the quotient test to the higher witnesses, especially the `m_p=4` cases where one branch is duplicated.

### Key Parameters
- Tested witness: `w4`.
- Critical forgotten processor: `p=3`.
- Critical shadows: `(1,1,0)` and `(0,0,1)`.

### Open Questions
- Do the `m_p=4` witnesses also resist every quotient to a deterministic 2-state controller on their critical shadows?
- Is irreducibility the right witness-side notion to pair with the binary word theorem, or is raw local-triple routing already enough?

## Exploration 15

### Strategy
Generalize the `w4` quotient test to all critical witness controllers in `w4` through `w8`, checking both reducibility to 2 states and reducibility to 3 states.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out both extremes:
- the controller is not reducible to a binary 2-state local controller,
- but the 4-state critical controllers are also not essentially 4-way.

So neither “binary is enough” nor “the witness needs arbitrarily many local controller states” is correct.

### Surviving Structure
- For every critical repeated-shadow controller found in `w4` through `w8`, there is **no** surjective quotient to a deterministic 2-state controller.
- For every critical controller, there **is** a deterministic quotient to 3 states.
- In the `m_p = 3` cases this is tautological.
- In the observed `m_p = 4` cases (`w6:p=3`, `w7:p=5`, `w8:p=3`), a quotient such as
  `(0,1,0,2)` reduces the 4 local states to 3 controller classes while preserving deterministic routing on all critical repeated shadows.

### Reformulations
The right witness-side invariant is now:

**minimal deterministic repeated-shadow controller size = 3**.

This is strictly stronger than “router capacity is 3,” because it excludes 2-state quotienting even when many local states are present. It is also strictly weaker than “the processor has exactly 3 states,” which is good: it cleanly absorbs the 4-state witnesses.

LOAD-BEARING ASSESSMENT: yes, decisively. This feels like the correct abstraction for a scalable lower bound. If the sub-threshold theorem can show controller complexity `<= 2`, and the witness theorem can show valid near-threshold systems need controller complexity `>= 3`, then the whole mechanism becomes representation-independent.

### Concrete Artifacts

COMPUTED EXAMPLES:
- `w4`, critical controller at `p=3`:
  - 2-state deterministic quotients: `0`
  - 3-state deterministic quotients: `6`
- `w5`, critical controller at `p=3`:
  - 2-state deterministic quotients: `0`
  - 3-state deterministic quotients: `6`
- `w6`, critical controller at `p=3` (`m_p=4`):
  - 2-state deterministic quotients: `0`
  - 3-state deterministic quotients: `6`
  - example quotient: `(0,1,0,2)`
- `w7`, critical controller at `p=5` (`m_p=4`):
  - 2-state deterministic quotients: `0`
  - 3-state deterministic quotients: `6`
  - example quotient: `(0,1,0,2)`
- `w8`, critical controller at `p=3` (`m_p=4`):
  - 2-state deterministic quotients: `0`
  - 3-state deterministic quotients: `6`
  - example quotient: `(0,1,0,2)`

STRUCTURAL RESULTS:
- Critical controller complexity is uniformly `3` across the witness family.
- 4-state witnesses carry redundant local controller states, not extra local routing branches.

TOOLS:
- Python quotient probe enumerating all surjections from local state sets of size `3` or `4` onto `2` and `3` classes and testing deterministic routing on all critical repeated shadows simultaneously.

REPRESENTATIONS:
- Controller complexity:
  `cc_p = min { k : some surjection of states at p to k classes preserves deterministic routing on all critical repeated shadows }`.

### What Would Unblock This
- A proof that any sub-threshold system has controller complexity at most `2` at every processor.
- A proof that any valid near-threshold system has controller complexity at least `3` at some processor.

### Key Parameters
- Witnesses tested: `w4`–`w8`.
- Critical projections: all forgotten processors with repeated-shadow router capacity `3`.

### Open Questions
- Can controller complexity `3` be derived directly from the transition tables, without extracting a specific good cycle?
- Is the quotient `(0,1,0,2)` canonical in the `m_p=4` cases, or just one of several equivalent 3-state reductions?

## Exploration 16 (probe)

### Strategy
Check whether the controller-complexity invariant already distinguishes the `n=5` threshold witness from the known sub-threshold product-72 consistent-cycle families.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- For the known consistent sweep cycle in `ms=(2,2,2,3,3)`, the controller-capacity profile is `(2,2,2,2,2)`.
- Sampling 30 consistent length-10 cycles from start `(0,0,0,0,0)` in `ms=(2,2,2,3,3)`:
  every sampled cycle had controller-capacity profile `(2,2,2,2,2)`.
- Sampling 30 consistent length-10 cycles from start `(0,0,0,0,0)` in `ms=(2,2,3,2,3)`:
  every sampled cycle had controller-capacity profile `(2,2,2,2,2)`.

STRUCTURAL RESULTS:
- At least on the first direct `n=5` probe, the sub-threshold families stay entirely in the 2-controller regime, while the threshold witness `w5` has profile `[2,2,2,3,2]`.

TOOLS:
- Python DFS probe for short consistent cycles in the two product-72 families, followed by repeated-shadow controller-capacity computation.

### Open Questions
- Does the all-`2` controller-capacity profile hold for **all** consistent cycles in the product-72 families, not just the sampled ones?
- Can the old shadow-cycle impossibility proofs for product 72 be reinterpreted as a consequence of controller complexity staying at `2` everywhere?

## Exploration 17

### Strategy
Finish the binary symbolic theorem by collapsing the remaining step `σ τ` with `τ ≠ σ` implies conflict into a tiny local lemma, analogous to the adjacent-antipodal-jump lemma for the first-half permutation.

### Outcome
STALLED

### Failure Constraint
The theorem `τ ≠ σ => conflict` is true for all permutations `σ, τ`, but the conflict witness does not follow a single simple “first mismatch” rule. The responsible processor and time vary with the shape of the deviation, so the naive compression attempt failed.

### What This Rules Out
This rules out the simplest hoped-for binary proof shape:
“take the first index where `τ` differs from `σ`, and the conflict is immediately at that processor/time.”
The second-half lemma is more global than that.

### Surviving Structure

COMPUTED EXAMPLES:
- Exhaustive verification: for all ordered pairs of distinct permutations `(σ, τ)`, the word `σ τ` forces symbolic TF conflict.
- So the theorem remains fully true; only the first compressed proof attempt failed.

STRUCTURAL RESULTS:
- The unfinished binary step is now isolated very precisely:
  `σ σ` is handled;
  non-cyclic `σ` is handled;
  the only missing hand-proof is `τ ≠ σ => conflict`.

REPRESENTATIONS:
- A more promising future representation is by prefix sets
  `S_k = {σ_0, …, σ_{k-1}}`
  and
  `T_k = {τ_0, …, τ_{k-1}}`,
  since local signatures are determined by prefix parities, not by the first mismatching letter alone.

### What Would Unblock This
- A prefix-set lemma comparing the first-half signatures from `S_k` with the second-half signatures from `T_k`.
- Or a direct geometric interpretation of the mismatch `τ ≠ σ` on the 8-step hypercube walk.

### Open Questions
- Can the `τ ≠ σ` step be proved by comparing prefix sets rather than individual first mismatches?
- Is there a short invariant that explains why every second-half deviation already forces TF conflict?

## Exploration 18 (probe)

### Strategy
Strengthen the first `n=5` controller-complexity signal by exhausting more consistent length-10 cycles at the canonical start for both product-72 families and checking whether any processor ever exceeds capacity `2`.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- For `ms=(2,2,2,3,3)`, canonical start `(0,0,0,0,0)`:
  - consistent length-10 cycles found: `40`
  - controller-capacity histogram: `{(2,2,2,2,2): 40}`
  - maximum capacity observed: `2`
- For `ms=(2,2,3,2,3)`, canonical start `(0,0,0,0,0)`:
  - consistent length-10 cycles found: `40`
  - controller-capacity histogram: `{(2,2,2,2,2): 40}`
  - maximum capacity observed: `2`

STRUCTURAL RESULTS:
- The stronger `n=5` probe reinforces Exploration 16: in both product-72 candidate families, the observed consistent cycles remain uniformly in the 2-controller regime.
- This now looks less like a coincidence of one hand-picked sweep and more like a real sub-threshold structural phenomenon.

TOOLS:
- Focused Python DFS probe at the canonical start, with larger search limits than Exploration 16, followed by repeated-shadow controller-capacity computation.

### Open Questions
- Does the all-`2` profile persist across all starts and all consistent cycles in the two product-72 families?
- Can the shadow-cycle proofs for these families be reframed as “2-controller systems cannot escape the induced bad recurrent component”?

## Synthesis after exploration 18

The workstream is now bifurcated very clearly into a nearly-complete binary theorem and a scaling conjecture that has started to bite at `n=5`.

What now looks stable:
- Binary `n=4` side:
  - symbolic normal form,
  - adjacent-antipodal local obstruction,
  - complementary repeated-shadow 2-controller,
  - only one unfinished cleanup lemma (`τ ≠ σ => conflict`) remains on that side.
- Witness side:
  - cross-`n` deterministic local-triple controller,
  - minimal controller complexity exactly `3`,
  - irreducible to `2`, reducible to `3`.
- First scaling signal at `n=5`:
  sampled sub-threshold consistent cycles in both product-72 families stay uniformly at controller complexity `2`.

Cross-pattern observation:
- The old “shadow cycle” impossibility story and the new controller-complexity story are beginning to look like two views of the same thing. A 2-controller on repeated shadows seems unable to route out of the induced bad recurrent structure; a 3-controller is what the witnesses use to break that trap.

Best next direction:
- Either finish the last binary cleanup lemma and package the `n=4` controller-complexity theorem cleanly,
- or push the `n=5` probe from sampled evidence toward an exhaustive/structural statement that all product-72 consistent cycles remain 2-controllers.

The second direction is now likely the higher-value one for reusable `4..8` methods, because the binary side is already conceptually close to done.

## Exploration 19 (probe)

### Strategy
Upgrade the `n=5` controller-capacity probe from canonical-start sampling to the larger multi-start families used in the old product-72 shadow scripts.

### Outcome
STALLED

### Failure Constraint
The naive multi-start DFS is too blunt in this form. It does not return quickly enough to be an effective exploratory tool, even though the target search space is finite.

### What This Rules Out
This rules out using the current generic DFS as the main path to stronger `n=5` evidence. If we want a real all-cycles controller statement for the product-72 families, we need either a sharper enumerator or a structural reinterpretation of the existing shadow-cycle proofs.

### Surviving Structure

STRUCTURAL RESULTS:
- The stall is computational, not conceptual.
- Explorations 16 and 18 remain the best direct evidence: sampled product-72 cycles stay uniformly in the 2-controller regime.

TOOLS:
- The current generic multi-start DFS is not an efficient next-step tool for controller-complexity research at `n=5`.

### What Would Unblock This
- A more specialized cycle enumerator with stronger pruning / memoization.
- Or, better, a controller-theoretic reading of the old product-72 shadow-cycle analyses that avoids enumerating all cycles again.

### Key Parameters
- Families targeted: `(2,2,2,3,3)` and `(2,2,3,2,3)`.
- Search regime attempted: multiple starts, length-10 DFS, large per-start caps.

### Open Questions
- Can the old `n=5` shadow proofs be reframed directly as “2-controller systems induce a forced recurrent component”?
- Is there a much better combinatorial encoding of consistent cycles for these tiny sub-threshold families?

## Exploration 21

### Strategy
Work through one explicit product-72 shadow cycle in controller language, not just in the older “shadow mirror” language, to see whether the old obstruction really is repeated-shadow controller reuse step by step.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the worry that the controller-complexity picture is only a high-level reinterpretation with no concrete dynamical content. At least in the worked `n=5` example, the shadow cycle really is built step by step from reused mover entries of the good cycle.

### Surviving Structure
- For the standard consistent cycle in `ms=(2,2,2,3,3)`,
  starting from anti-sweep config `(0,0,1,0,0)`,
  the forced bad cycle has length `10`.
- Each forced shadow move is witnessed by a mover entry of the good cycle:
  - step 0 uses `P0` mover entry from good step 0 (`(0,0,0)` context),
  - step 1 uses `P3` mover entry from good step 3,
  - step 2 uses `P2` mover entry from good step 7,
  - step 3 uses `P1` mover entry from good step 1,
  - etc.
- So the shadow cycle is literally a daemon following the same local controller entries at non-good repeated shadows.

### Reformulations
The controller-complexity statement can now be sharpened dynamically:

> a repeated-shadow deterministic 2-controller does not merely limit what local routing is possible; it also supplies a reusable library of forced mover entries that can close into a bad recurrent orbit.

This is the dynamic half of the lower-bound mechanism, complementary to the static controller-capacity invariant.

LOAD-BEARING ASSESSMENT: yes. This worked example makes the old shadow proof feel like direct evidence for a future theorem of the form
`controller complexity <= 2 => forced bad orbit`.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Explicit shadow cycle from anti-sweep start `(0,0,1,0,0)` in `ms=(2,2,2,3,3)`:
  `(0,0,1,0,0)
   -> (1,0,1,0,0)
   -> (1,0,1,1,0)
   -> (1,0,0,1,0)
   -> (1,1,0,1,0)
   -> (1,1,0,1,1)
   -> (0,1,0,1,1)
   -> (0,1,0,0,1)
   -> (0,1,1,0,1)
   -> (0,0,1,0,1)
   -> (0,0,1,0,0)``
- Annotated forced moves:
  - `(0,0,1,0,0)` forces `P0 -> 1` using the good-cycle mover entry from step 0
  - `(1,0,1,0,0)` forces `P3 -> 1` using the good-cycle mover entry from step 3
  - `(1,0,1,1,0)` forces `P2 -> 0` using the good-cycle mover entry from step 7
  - `(1,0,0,1,0)` forces `P1 -> 1` using the good-cycle mover entry from step 1`
  - continuing analogously around the 10-step bad orbit

STRUCTURAL RESULTS:
- The shadow cycle is concretely built from reused good-cycle mover entries, not from free choices.
- This is exactly the behavior expected from a deterministic repeated-shadow controller of complexity `2`.

TOOLS:
- Python reconstruction of the good-cycle determined entries and forced shadow orbit for the standard `(2,2,2,3,3)` cycle.

REPRESENTATIONS:
- Shadow orbit as a sequence of reused mover-controller entries.

### What Would Unblock This
- A clean abstract statement turning “mover-entry reuse on repeated shadows” into “forced recurrent component.”
- A similar worked translation for the `(2,2,3,2,3)` family to confirm the same controller-dynamic structure there.

### Key Parameters
- Family: `ms=(2,2,2,3,3)`.
- Good cycle: the standard 10-cycle from `locality_bottleneck_v4.py`.
- Shadow start: anti-sweep config `(0,0,1,0,0)`.

### Open Questions
- Is there a compact graph-theoretic formulation of this mover-entry reuse phenomenon?
- Does the `(2,2,3,2,3)` family produce the same controller-dynamic pattern with a different shadow mover permutation?

## Exploration 22

### Strategy
Carry out the same controller-language shadow-cycle translation for the second product-72 family `ms=(2,2,3,2,3)` and compare it directly to the first family.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the possibility that the controller/shadow identification in Exploration 21 was specific to the consecutive-binary family `(2,2,2,3,3)`.

### Surviving Structure
- In the `ms=(2,2,3,2,3)` family, a standard consistent 10-cycle with movers
  `[0,1,2,3,4,0,1,2,3,4]`
  again yields a 10-step bad orbit through non-good states.
- As in Exploration 21, every forced shadow step is traced to a mover entry of the good cycle:
  - step 0 reuses the `P1` mover entry from good step 1,
  - step 1 reuses the `P4` mover entry from good step 4,
  - step 2 reuses the `P0` mover entry from good step 5,
  - step 4 reuses the `P2` mover entry from good step 2,
  - step 5 reuses the `P1` mover entry from good step 6,
  - etc.
- So the split-binary family exhibits the same controller-dynamic mechanism:
  the daemon follows a recurrent bad orbit generated entirely by repeated reuse of determined mover entries on non-good repeated shadows.

### Reformulations
The “2-controller => shadow recurrence” picture now survives the transition from the consecutive-binary product-72 family to the split-binary product-72 family. This strongly suggests that the controller-complexity invariant is not merely rephrasing one special shadow theorem but is capturing the common mechanism behind both product-72 impossibility proofs.

LOAD-BEARING ASSESSMENT: yes. This is the clearest cross-family confirmation so far. It materially strengthens the claim that controller complexity, not geometric sweep folklore, is the reusable lower-bound object.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Explicit consistent cycle in `ms=(2,2,3,2,3)`:
  `[(0,0,0,0,0),(1,0,0,0,0),(1,1,0,0,0),(1,1,1,0,0),(1,1,1,1,0),(1,1,1,1,1),(0,1,1,1,1),(0,0,1,1,1),(0,0,0,1,1),(0,0,0,0,1)]`
  with mover word `[0,1,2,3,4,0,1,2,3,4]`.
- Explicit shadow orbit from non-good state `(1,0,0,1,0)`:
  `(1,0,0,1,0)
   -> (1,1,0,1,0)
   -> (1,1,0,1,1)
   -> (0,1,0,1,1)
   -> (0,1,0,0,1)
   -> (0,1,1,0,1)
   -> (0,0,1,0,1)
   -> (0,0,1,0,0)
   -> (1,0,1,0,0)
   -> (1,0,1,1,0)
   -> (1,0,0,1,0)``
- Step-by-step shadow-entry reuse:
  - `(1,0,0,1,0)` forces `P1 -> 1` using good step 1
  - `(1,1,0,1,0)` forces `P4 -> 1` using good step 4
  - `(1,1,0,1,1)` forces `P0 -> 0` using good step 5
  - `(0,1,0,0,1)` forces `P2 -> 1` using good step 2
  - `(0,1,1,0,1)` forces `P1 -> 0` using good step 6
  - etc.

STRUCTURAL RESULTS:
- Both product-72 families now admit an explicit controller-language bad orbit built entirely from reused good-cycle mover entries.

TOOLS:
- Python reconstruction of the good-cycle determined entries and forced shadow orbit for one consistent 10-cycle in `ms=(2,2,3,2,3)`.

REPRESENTATIONS:
- Shadow orbit as repeated-shadow controller reuse in the split-binary family.

### What Would Unblock This
- A common abstract theorem covering both product-72 families:
  deterministic 2-controller repeated-shadow reuse closes into a bad recurrent orbit.
- A controller-language description of the mover permutation induced on the shadow orbit.

### Key Parameters
- Family: `ms=(2,2,3,2,3)`.
- Good cycle: first consistent 10-cycle from the standard DFS search.
- Shadow start: non-good state `(1,0,0,1,0)`.

### Open Questions
- Can the two product-72 families be unified under a single controller-reuse theorem without mentioning their specific binary layouts?
- Is there a concise combinatorial description of the shadow mover permutation induced by repeated-shadow controller reuse?

## Exploration 24

### Strategy
Check whether the product-72 shadow mover permutation is family-specific or whether the two `n=5` sub-threshold families actually share the same shadow-word statistics across many canonical-start cycles.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the idea that the two product-72 families need fundamentally different dynamic obstruction theorems. At least on the canonical-start 10-cycle population, their shadow-word behavior matches exactly.

### Surviving Structure
- For the first 40 consistent length-10 cycles from canonical start `(0,0,0,0,0)` in each family, the shadow-word histogram is identical.
- Shared histogram:
  - `12` cycles with shadow word `(1,4,0,3,2)^2`
  - `16` cycles with shadow word `(1,3,2,4,0)^2`
  - `8` cycles with shadow word `(2,1,4,0,3)^2`
  - `4` cycles with shadow word `(3,2,4,0,1)^2`
- So the shadow mover word is not arbitrary. It falls into a small common family across both product-72 layouts.

### Reformulations
The product-72 obstruction may admit a common **shadow-word theorem**:
for consistent 10-cycles in the 3-binary `n=5` sub-threshold families, the repeated-shadow 2-controller induces one of a tiny number of fixed bad-orbit mover words, independent of the exact binary layout.

LOAD-BEARING ASSESSMENT: high. This is the first cross-family dynamic regularity result. It materially strengthens the case that the controller-complexity obstruction is not family-by-family bookkeeping but a shared mechanism with a small shadow-word normal form.

### Concrete Artifacts

COMPUTED EXAMPLES:
- Family `(2,2,2,3,3)`, first 40 canonical-start cycles:
  - `12` with shadow word `(1,4,0,3,2,1,4,0,3,2)`
  - `16` with shadow word `(1,3,2,4,0,1,3,2,4,0)`
  - `8` with shadow word `(2,1,4,0,3,2,1,4,0,3)`
  - `4` with shadow word `(3,2,4,0,1,3,2,4,0,1)`
- Family `(2,2,3,2,3)`, first 40 canonical-start cycles:
  - exactly the same counts for exactly the same four shadow words.

STRUCTURAL RESULTS:
- The two product-72 families share the same sampled shadow-word dynamics.
- Each observed shadow word is itself periodic of the form `ρ ρ` with a 5-step block `ρ`.

TOOLS:
- Robust forced-transition graph extractor for canonical-start cycles, returning an actual directed cycle in the non-good forced graph and recording its mover word.

REPRESENTATIONS:
- Shadow mover word as the dynamic normal form of a repeated-shadow 2-controller.

### What Would Unblock This
- A structural explanation of why only these four shadow words appear.
- Extension of the same histogram check beyond the canonical start, or a proof that the mover-word family is complete.

### Key Parameters
- Families tested: `(2,2,2,3,3)` and `(2,2,3,2,3)`.
- Population tested: first 40 consistent canonical-start length-10 cycles in each family.

### Open Questions
- Can the four observed 5-step shadow blocks be derived directly from the local controller view?
- Do all consistent cycles in the two product-72 families produce one of these same four shadow words?

## Exploration 26 (probe)

### Strategy
Probe whether the `w5` critical 3-controller can be seen directly as fusing the pairwise 2-controllers that occur in the product-72 families by collecting repeated-shadow mover-pair histograms at the corresponding forgotten processor.

### Outcome
ABANDONED

### Failure Constraint
The obvious route again went through raw cycle enumeration, and it is too blunt in this form. The pair-histogram question itself is reasonable, but the current DFS implementation is not the right tool for answering it.

### What This Rules Out
This rules out pushing the `w5` fusion picture by generic cycle-space brute force right now. If this relation is important, it should be extracted from already-identified canonical cycles or from the controller/ shadow-word normal forms, not from another broad DFS.

### Surviving Structure

STRUCTURAL RESULTS:
- The attempted question remains good:
  whether the `w5` threshold controller fuses the same pairwise 2-controllers seen in the product-72 world is still an interesting bridge.
- The failure is tactical, not conceptual.

### What Would Unblock This
- A controller-side derivation from the worked product-72 shadow words rather than from broad cycle enumeration.
- Or a smaller canonical family of product-72 cycles from which the relevant pair-controller data can be extracted directly.

## Exploration 25 (probe)

### Strategy
Compress the four observed product-72 shadow 5-step blocks by rotation to see whether the dynamic theorem is really about four distinct words or about a smaller number of cyclic types.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- The four observed 5-step shadow blocks from Exploration 24 are:
  - `(1,4,0,3,2)`
  - `(1,3,2,4,0)`
  - `(2,1,4,0,3)`
  - `(3,2,4,0,1)`
- These collapse to exactly **two** rotation classes:
  1. `{(1,4,0,3,2), (2,1,4,0,3), (3,2,1,4,0), (4,0,3,2,1), (0,3,2,1,4)}`
  2. `{(1,3,2,4,0), (3,2,4,0,1), (2,4,0,1,3), (4,0,1,3,2), (0,1,3,2,4)}`

STRUCTURAL RESULTS:
- The sampled product-72 shadow dynamics appears to have only two essential 5-step types, up to cyclic relabeling of the starting point on the shadow orbit.

### Open Questions
- Do these two rotation classes correspond to two controller “orientation” types on the 2-controller repeated-shadow mechanism?

## Exploration 27 (probe)

### Strategy
Check whether the 4-state critical controllers in the witness family share a canonical internal shape, rather than merely admitting some 3-state quotient.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- `w6`, critical processor `p=3`:
  state-to-mover pattern on critical shadows is always
  `0 -> 3`, `1 -> 2`, `2 -> 3`, `3 -> 4`.
- `w7`, critical processor `p=5`:
  critical shadows include
  `0 -> 4`, `1 -> 5`, `2 -> 4`, `3 -> 6`.
- `w8`, critical processor `p=3`:
  critical shadows include
  `0 -> 2`, `1 -> 3`, `2 -> 2`, `3 -> 4`.

STRUCTURAL RESULTS:
- In every observed 4-state critical controller, states `0` and `2` realize the same branch.
- States `1` and `3` realize the other two branches.
- So the quotient `(0,1,0,2)` is not just *a* possible 3-state reduction in the known examples; it appears to be the canonical internal shape.

### Open Questions
- Is the `0/2` duplication pattern universal in the entire witness family?
- Can the canonical shape `(0,1,0,2)` be read directly from the transition tables, without going through the good cycle?

## Exploration 33 (probe)

### Strategy
Package the repeated-shadow controller computations into a reusable probe script instead of continuing to rely on ad hoc one-off Python snippets.

### Outcome
SUCCEEDED

### Concrete Artifacts

TOOLS:
- New reusable script:
  [controller_complexity_probe.py](./probes/controller_complexity_probe.py)
- Current capabilities:
  - decode a mixed-radix cycle from `ms` and `codes`
  - extract the mover word
  - compute repeated-shadow router capacity at every forgotten processor
  - list critical repeated shadows and their `state -> mover` maps
  - optionally compute minimal deterministic controller size

COMPUTED EXAMPLES:
- On `w4`, the script reproduces:
  - capacities `(2,2,2,3)`
  - minimal controller sizes `(2,2,2,3)`
  - critical shadows `(1,1,0)` and `(0,0,1)` with deterministic 3-controllers
- On `w5`, the script reproduces:
  - capacities `(2,2,2,3,2)`
  - critical shadow `(1,1,0,0)` at forgotten processor `3`

STRUCTURAL RESULTS:
- The controller-complexity route now has a stable computational tool rather than scattered scratch snippets.

### Open Questions
- Extend the script to compare witness controllers against sub-threshold pair-controller families directly.
- Add an option for controller quotients restricted to selected critical shadows only.

## Exploration 28 (probe)

### Strategy
Look for a lightweight `n=5` bridge between the threshold witness controller and the old product-72 families by comparing the repeated-shadow mover sets at the critical forgotten processor, using only the standard consistent cycles rather than broad DFS.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- Standard product-72 cycle in `(2,2,2,3,3)`, forgetting processor `3`:
  repeated shadows carry mover pair `{3,4}`.
- Standard product-72 cycle in `(2,2,3,2,3)`, forgetting processor `3`:
  repeated shadows again carry mover pair `{3,4}`.
- `w5` witness, forgetting processor `3`:
  one critical repeated shadow `(1,1,0,0)` carries the local-triple mover set `{2,3,4}`.

STRUCTURAL RESULTS:
- The two standard product-72 families agree on the same local 2-controller at forgotten processor `3`: `{3,4}`.
- The `w5` witness extends that local pattern by adding the missing direction `2`, producing the 3-controller `{2,3,4}`.
- So in `n=5`, the threshold witness can be read as a strict local upgrade of a sub-threshold 2-controller, not just as an unrelated larger-state mechanism.

### Open Questions
- Does the pair `{3,4}` remain the only repeated-shadow controller at processor `3` across all product-72 cycles, or just in the standard cycles?
- Can the `w5` witness’s `{2,3,4}` controller be characterized as “the unique minimal extension” of the sub-threshold `{3,4}` controller?

## Exploration 36

### Strategy
Package the dynamic half of the controller route into a theorem-oriented definitions note, so the abstract recurrence mechanism is no longer just a slogan in the exploration log.

### Outcome
SUCCEEDED

### Concrete Artifacts

TOOLS:
- New theorem-spec note:
  [controller_recurrence_theorem.md](./lean/docs/controller_recurrence_theorem.md)

STRUCTURAL RESULTS:
- The note records candidate definitions for:
  - repeated-shadow controller
  - controller entry
  - off-cycle realization
  - bad reuse region
- It states the current abstract theorem schema:
  reuse-closed deterministic repeated-shadow subsystem yields a recurrent bad orbit.
- It also records the family-specific corollary schema:
  low-state `2`-controller families are impossible once a bad reuse region is constructed.

REPRESENTATIONS:
- This note is the current cleanest packaging of the dynamic side, distinct from the broader route note and distinct from the raw exploration residue.

### Open Questions
- Which of the candidate definitions will survive first contact with formalization most cleanly?
- Should the first formal pilot be the product-72 `n=5` family or the binary `n=4` dynamic side?

## Exploration 39

### Strategy
Package the witness-side frontier into a theorem-target note so the program now has explicit static, dynamic, and witness-side theorem schemas rather than just exploration residue.

### Outcome
SUCCEEDED

### Concrete Artifacts

TOOLS:
- New theorem-target note:
  [witness_controller_necessity.md](./lean/docs/witness_controller_necessity.md)

STRUCTURAL RESULTS:
- The note isolates the current frontier theorem:
  valid near-threshold systems require a repeated-shadow controller of minimal deterministic size `3`.
- It records three plausible proof routes:
  - local routing-memory theorem
  - repeated-shadow escape theorem
  - witness-specific lift / pair-fusion theorem
- It also records the strongest current `n=5` bridge:
  sub-threshold pair-controllers `{2,3}` and `{3,4}` versus witness triple-controller `{2,3,4}`.

REPRESENTATIONS:
- The controller program is now split into three concrete notes:
  - [binary_q4_controller_theorem.md](./lean/docs/binary_q4_controller_theorem.md)
  - [controller_recurrence_theorem.md](./lean/docs/controller_recurrence_theorem.md)
  - [witness_controller_necessity.md](./lean/docs/witness_controller_necessity.md)

## Exploration 40

### Strategy
Use a dedicated RA sub-agent to compare raw response-pattern distinctness against repeated-shadow controller complexity across the explicit witnesses `w4..w8`, to test whether the older response-pattern route is really the same invariant or only a coarser witness-side tool.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out using raw response-pattern counts as the direct witness-side invariant. They are too coarse: they overcount the relevant control complexity in the 4-state witness processors.

### Surviving Structure

COMPUTED EXAMPLES:
- Exact response-pattern census reported by the sub-agent:
  - `w4`: `[2,2,2,4]`
  - `w5`: `[1,2,2,3,4]`
  - `w6`: `[2,1,2,4,3,3]`
  - `w7`: `[3,2,2,2,3,4,3]`
  - `w8`: `[2,2,3,4,3,3,2,3]`
- Critical repeated-shadow controller complexity remains uniformly `3` in the witness family.
- In the 4-state critical processors (`w4:p3`, `w6:p3`, `w7:p5`, `w8:p3`), the processor has 4 distinct response patterns but the repeated-shadow controller still quotients to size `3`.

STRUCTURAL RESULTS:
- Response-pattern distinctness is a valid lower bound on mergeability of local states, but it is not the same invariant as repeated-shadow controller complexity.
- The controller-complexity route is genuinely sharper: it captures the minimal dynamic control needed on the good cycle, whereas response patterns count all local `(L,R)` distinctions whether or not they matter to the repeated-shadow routing problem.

### Reformulations
The best current witness-side hierarchy is:

1. **response patterns**: coarse mergeability obstruction
2. **deterministic repeated-shadow controller**: exact routing object on the good cycle
3. **minimal controller complexity**: the sharp invariant currently separating threshold witnesses from the low-state side

LOAD-BEARING ASSESSMENT: yes. This cleanly positions the older response-pattern theorem inside the new program: useful, but strictly weaker than the controller-complexity invariant we now care about.

### Concrete Artifacts

TOOLS:
- The sub-agent traced the exact response-pattern census to the explicit witness tables in `verify_theorem.py`.

### What Would Unblock This
- A theorem relating response-pattern distinctness to repeated-shadow controller complexity, even if only as a one-sided inequality.
- Or a direct witness-side theorem that bypasses response patterns entirely and proves controller complexity `3` from good-cycle routing structure.

### Open Questions
- Is there a clean inequality such as “controller complexity at `p` <= response-pattern count at `p`” that is worth formalizing?
- Are there settings where response-pattern distinctness and controller complexity coincide exactly, or are they generically different once `m_p >= 4`?

## Synthesis after exploration 40

The witness-side frontier is now clearer than it was before the response-pattern census.

What is stable:
- response-pattern distinctness is real and useful as a mergeability obstruction
- but it is not the same invariant as repeated-shadow controller complexity
- the witness family consistently uses controller complexity exactly `3`
  even when raw response-pattern counts rise to `4`

So the witness-side theorem should not be stated in response-pattern language.
Response patterns remain a supporting tool, but the actual target invariant is
still minimal repeated-shadow controller complexity.

This is helpful because it prunes a tempting but wrong route:
trying to prove the witness theorem by directly demanding 4 distinct response
patterns everywhere would be stronger than needed and would obscure the actual
dynamic mechanism.

## Exploration 41

### Strategy
Use a dedicated PA sub-agent to compress the last binary gap (`σ τ`, `τ ≠ σ => conflict`) from 7 normalized cyclic/reverse cases to a tiny sweep-shape argument after normalization.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the need for raw 7-case checking on the final binary second-half lemma. The remaining proof is still finite and normalized, but it is now organized by two sweep-shape families rather than by isolated permutations.

### Surviving Structure

STRUCTURAL RESULTS:
- After the earlier reductions, normalize `σ = (0,1,2,3)`.
- The only first-half nonmover signatures needed are:
  - processor `0`: `010`, `011`
  - processor `1`: `110`, `111`
  - processor `2`: `110`
- If `τ` is cyclic/reverse-cyclic, its second-half mover signatures are forced by orientation:
  - forward sweep: `111, 011, 011, 010`
  - reverse sweep: `111, 110, 110, 010`
- Then:
  - forward sweeps with start `a ≠ 0` force either processor `1` to move on `111` or processor `0` to move on `011`
  - reverse sweeps force either processor `1` or `2` to move on `110`, or processor `1` to move on `111`
- In each case, that conflicts with a first-half nonmover signature, so the only conflict-free forward sweep is exactly `τ = σ`.

### Reformulations
The hard binary gap is now best viewed as a **small normalized family reduction**:

1. kill non-cyclic `τ` by the adjacent-antipodal lemma
2. normalize `σ`
3. reduce the remaining second-half words to forward vs reverse sweeps
4. use a tiny placement argument against the first-half signature table

LOAD-BEARING ASSESSMENT: yes. This is not the fully conceptual prefix-set proof once hoped for, but it is clean enough that the binary `n=4` theorem now looks genuinely formalizable rather than merely computationally verified.

### Concrete Artifacts

STRUCTURAL RESULTS:
- Two second-half sweep-shape lemmas:
  - forward sweep pattern
  - reverse sweep pattern
- One small placement argument per sweep type

### What Would Unblock This
- A clean write-up of the normalized first-half signature table and the two sweep-shape lemmas in one note or Lean scratch file.

### Open Questions
- Can the sweep-shape reduction itself be made invariant under dihedral symmetry in a way that is pleasant to formalize?

## Exploration 29 (probe)

### Strategy
Take a lighter `n=5` bridge probe than the abandoned broad DFS: sample a small canonical-start family of consistent cycles and extract the repeated-shadow pair-controllers at the critical forgotten processor `p=3`.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- In 10 sampled canonical-start cycles from `(2,2,2,3,3)`, forgetting processor `3`, the repeated-shadow pair-controller histogram is:
  - `{2,3}`: `12`
  - `{3,4}`: `8`
- In 10 sampled canonical-start cycles from `(2,2,3,2,3)`, forgetting processor `3`, the histogram is **identical**:
  - `{2,3}`: `12`
  - `{3,4}`: `8`
- In the threshold witness `w5`, forgetting processor `3`, the critical repeated shadow `(1,1,0,0)` carries the fused local-triple controller `{2,3,4}`.

STRUCTURAL RESULTS:
- The two product-72 families again align exactly under the controller view.
- At forgotten processor `3`, the sampled sub-threshold world exposes the two local pair-controllers `{2,3}` and `{3,4}`.
- The threshold witness can be read as fusing those pair-controllers into the triple-controller `{2,3,4}`.

### Reformulations
This is the cleanest `n=5` bridge so far:

- sub-threshold sampled pair-controllers at `p=3`:
  `{2,3}` and `{3,4}`
- threshold witness controller at `p=3`:
  `{2,3,4}`

So the `w5` witness does not just exceed sub-threshold controller complexity abstractly; it appears to glue together the two pair-controllers that the sub-threshold families can realize separately.

LOAD-BEARING ASSESSMENT: high. This is the first concrete `n=5` analogue of the `M_4` orientation-fusion picture. It suggests the controller-complexity mechanism really is scaling one step up rather than being confined to the `Q4` binary reduction.

### Open Questions
- Does the same pair-fusion picture hold beyond the sampled canonical-start cycles, or is it only a local sample phenomenon?
- Is there a structural reason the pair `{3,4}` and `{2,3}` are exactly the sub-threshold options at `p=3`?

## Exploration 32 (probe)

### Strategy
Upgrade the `n=5` pair-fusion bridge from the 10-cycle canonical-start sample to the full 40-cycle canonical-start populations in both product-72 families.

### Outcome
ABANDONED

### Failure Constraint
The exact 40-cycle pair-hist extraction is another case where the naive cycle enumerator is too blunt for the marginal gain in information. The sampled `10`-cycle bridge already gives the relevant structural picture, and pushing the same extractor to the exact `40`-cycle population is not an efficient next step with the current tooling.

### What This Rules Out
This rules out using the current raw cycle enumerator for increasingly fine-grained `n=5` controller statistics. The right next step for the pair-fusion question is structural, not a larger version of the same brute-force pass.

### Surviving Structure

STRUCTURAL RESULTS:
- The `10`-cycle canonical-start pair-fusion bridge from Exploration 29 remains the best-cost evidence:
  both families show the same sampled pair-controllers `{2,3}` and `{3,4}` at forgotten processor `3`,
  and the threshold witness upgrades to `{2,3,4}`.

### What Would Unblock This
- A controller-side derivation of the sub-threshold pair-controllers from the shadow-word normal forms.
- Or a more specialized enumerator that computes pair-controller data directly without regenerating full cycle families.

## Synthesis after exploration 29

The controller-complexity route now has a much more convincing `n=5` bridge.

What is now stable:
- `n=4`:
  - sub-threshold binary side is a 2-controller world
  - threshold witness side is a 3-controller world
- `n=5`:
  - both product-72 sub-threshold families show the same sampled 2-controller behavior
  - both admit controller-language shadow recurrence
  - and, at the critical forgotten processor `p=3`, the sampled sub-threshold pair-controllers are exactly `{2,3}` and `{3,4}`, while the threshold witness upgrades to `{2,3,4}`

This is the strongest small-`n` evidence so far that the route is really reusable:
the threshold witness is not just “more complicated”; it appears to fuse the very pair-controllers that the sub-threshold world can realize separately.

Best next direction:
- stop trying to squeeze more value from generic cycle enumeration,
- and instead turn the emerging `n=5` pair-fusion picture into a theorem candidate:

> sub-threshold systems can realize only pair-controllers on repeated shadows,
> while threshold witnesses fuse adjacent pair-controllers into a triple-controller.

If that statement can be made precise, it would be the first genuinely unified `M_4/M_5` mechanism in this campaign.

## Synthesis after exploration 28

The `n=5` controller story is now visibly connected to the old product-72 impossibility proofs.

What is stable after explorations 21, 22, 24, and 28:
- both product-72 families admit explicit bad recurrent orbits built from reused good-cycle mover entries
- the sampled shadow-word families match across the two product-72 layouts
- the standard cycles in both product-72 families show the same repeated-shadow pair-controller at forgotten processor `3`, namely `{3,4}`
- the `w5` witness upgrades that local pair-controller to the local-triple controller `{2,3,4}`

This is the first concrete bridge from the static witness-side `3`-controller story to the older `n=5` shadow machinery.

The likely reusable narrative is now:

1. sub-threshold systems are locked into pair-controllers on repeated shadows,
2. pair-controllers are dynamically unstable because determined-entry reuse closes into bad recurrent orbits,
3. threshold witnesses escape by upgrading one of those pair-controllers to a local-triple controller.

That is much closer to a reusable `4..8` method than either:
- the original brute-force DFS story, or
- the original small-`n` shadow theorem viewed in isolation.

## Synthesis after exploration 24

The `n=5` side is now no longer just “sampled controller complexity evidence.” It has a coherent dynamic pattern.

What is now stable:
- `n=4` binary side:
  symbolic normal form, local forbidden pattern, deterministic 2-controller, with only one cleanup lemma left.
- Witness side `w4..w8`:
  minimal controller complexity exactly `3`.
- `n=5` product-72 side:
  sampled consistent cycles remain in the uniform 2-controller regime,
  both sub-threshold families admit explicit bad recurrent orbits built from reused mover entries,
  and the shadow mover words seem to come from the same tiny 4-word family across both families.

This is an important shift:
- the static invariant (controller complexity `2` vs `3`) and the dynamic invariant (shadow-word recurrence) are now visibly tied together in both product-72 families, not just in one worked example.

Most promising next direction:
- stop broad DFS probing,
- focus on deriving the 4 observed shadow words from local controller structure,
- and try to formulate the common dynamic theorem:

> deterministic repeated-shadow 2-controllers on these sub-threshold `n=5` families generate one of a tiny set of bad recurrent mover words.

That would be the first real bridge from the static controller-complexity invariant to the old small-`n` shadow theorems.

## Exploration 23 (probe)

### Strategy
Test whether the shadow mover permutation is universal across many canonical-start product-72 cycles in both `n=5` families.

### Outcome
FAILED

### Concrete Artifacts

TOOLS:
- The first shadow-word extractor was too naive: it assumed every exploratory shadow trace has an available forced move at each step and crashed when a non-good config had no forced exit under that first-choice policy.

STRUCTURAL RESULTS:
- This failure is implementation-level, not mathematical. The right fix is to use the more robust shadow-cycle finder that searches over available forced continuations, or to restrict to already-verified shadow-producing traces.

## Synthesis after exploration 22

The `n=5` side has now crossed from “suggestive” to “structurally aligned.”

What is stable:
- `n=4` binary/sub-threshold side:
  symbolic normal form, local forbidden pattern, deterministic 2-controller.
- Threshold witness side `w4..w8`:
  deterministic local-triple controller, minimal controller complexity exactly `3`.
- `n=5` sub-threshold side:
  sampled product-72 cycles stay in the 2-controller regime,
  and both product-72 families admit explicit bad recurrent orbits built by reusing good-cycle mover entries on non-good repeated shadows.

Cross-pattern observation:
- The old shadow-cycle mirror theorem is now best understood as the dynamic theorem
  attached to controller complexity `2`.
- The new witness-side controller-complexity theorem is the static mechanism that explains why the optimal witnesses escape that bad-orbit trap.

This is the strongest reusable architecture so far:

1. **Static low-state theorem**:
   sub-threshold systems admit only deterministic 2-controllers on repeated shadows.
2. **Dynamic recurrence theorem**:
   deterministic 2-controller reuse generates a forced recurrent bad orbit.
3. **Witness necessity theorem**:
   valid near-threshold systems require minimal controller complexity `3` somewhere.

If that triad can be formalized, it is no longer just an `M_4` replacement plan.
It is a genuine candidate framework for `4..8`.

## Exploration 20

### Strategy
Re-read the old product-72 shadow-cycle proofs through the controller-complexity lens and test whether “shadow cycle” is really just the dynamical manifestation of a repeated-shadow 2-controller.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out treating the shadow theorem and the controller-complexity mechanism as two unrelated proof routes. They appear to be the same mechanism at different resolutions.

### Surviving Structure
- The old product-72 shadow theorem says:
  mover entries of the good cycle are fully determined at binary processors,
  the same local entries reappear at anti-sweep binary shadows,
  and these forced reuses close into a shadow cycle.
- The controller-complexity story says:
  sub-threshold systems only supply deterministic 2-controllers on repeated shadows,
  so reusing a mover entry at a repeated shadow leaves only one local direction available,
  which the daemon can chain into a forced recurrent orbit.
- The two views align:
  a “shadow cycle” is precisely the orbit generated by repeated reuse of a deterministic 2-controller on complementary/anti-sweep shadows.

### Reformulations
The emerging proof architecture is:

1. **Static side**: low-state systems have only 2-controller repeated-shadow behavior.
2. **Dynamic side**: 2-controller repeated-shadow behavior induces a forced recurrent component (shadow cycle / bad orbit).
3. **Witness side**: valid threshold systems break this by upgrading to controller complexity `3`.

LOAD-BEARING ASSESSMENT: yes. This is a major conceptual compression. It means the old shadow proofs are not legacy baggage; they are direct evidence that controller complexity is the right invariant, because they already exhibit the `2-controller => recurrent bad orbit` direction in concrete small-`n` families.

### Concrete Artifacts

STRUCTURAL RESULTS:
- In `exploration_log2.md`, the product-72 shadow theorem already states the key ingredients in controller language:
  - binary processors are fully determined,
  - determined entries are shared across configs,
  - anti-sweep shadows reuse those entries,
  - NB coordinates do not create escape.
- Combined with Explorations 16 and 18:
  sampled product-72 cycles remain uniformly in the 2-controller regime.

REPRESENTATIONS:
- Shadow cycle = forced recurrent orbit produced by repeated-shadow controller reuse.
- Threshold witness = local-triple controller that prevents this forced reuse from collapsing into the same bad orbit.

### What Would Unblock This
- A formal theorem schema:
  `controller complexity <= 2 on the relevant repeated shadows => ∃ forced bad orbit`.
- Or a small worked translation of one product-72 shadow proof entirely into controller-complexity language.

### Key Parameters
- Families interpreted: product-72 `n=5` candidates `(2,2,2,3,3)` and `(2,2,3,2,3)`.
- Source artifacts: old shadow theorem notes plus the new controller-capacity probes.

### Open Questions
- Can the product-72 shadow cycle mirror theorem be rewritten cleanly as a general “2-controller recurrence theorem”?
- Is there an abstract criterion weaker than full shadow-cycle structure but still strong enough to contradict convergence once controller complexity stays at `2`?

## Synthesis after exploration 15

The campaign now has a candidate invariant that is both sharp and reusable.

Binary/sub-threshold side:
- symbolic normal form,
- local forbidden pattern,
- deterministic controller complexity `<= 2`.

Witness/threshold side:
- local-triple routing,
- deterministic controller,
- irreducible to `2` states,
- reducible to `3` states even when `m_p = 4`.

So the likely theorem schema is no longer merely about state counts.
It is about **minimal local controller complexity on repeated shadows**:

> low-state systems admit controller complexity at most `2`,
> valid near-threshold systems require controller complexity exactly `3` somewhere.

That is the strongest and cleanest formulation found so far, and it looks much more likely to scale to `n=5,6` than any raw DFS argument.

## Synthesis after exploration 14

The picture is becoming genuinely theorem-shaped.

Binary side:
- symbolic normal form,
- local forbidden pattern,
- deterministic 2-controller on complementary repeated shadows.

Witness side:
- deterministic local-triple controller,
- cross-`n` persistence,
- and now explicit irreducibility at `n=4`.

The likely final abstraction is:

> sub-threshold systems admit only reducible 2-direction local controllers on repeated shadows,
> whereas threshold-valid systems require an irreducible 3-direction local controller.

That formulation finally sounds like a mechanism that could scale beyond `M_4`.

## Synthesis after exploration 13

The investigation has crossed an important threshold.

What is now stable across `n=4..8`:
- The sub-threshold binary side is a 2-way repeated-shadow controller world.
- The threshold witness side is a deterministic 3-way repeated-shadow controller world.
- Extra states beyond `3` only refine the same 3-way controller; they do not create a fourth branch.

This suggests the right conjectural theorem is no longer just:
“valid systems need local-triple routing.”
It is stronger and cleaner:

> Any near-threshold valid witness must contain a processor whose local state acts as a deterministic controller for the three local directions `{left(p), p, right(p)}` on some repeated shadow.

If that is the right statement, then the `M_4` native-decide-free route and the higher-`n` witness analyses are finally talking about the same mechanism.

## Exploration 12

### Strategy
Look for a short pen-and-paper proof of the binary word theorem by identifying a minimal forbidden local pattern in the first-half permutation `σ`.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the need for a long symbolic classification over all 24 permutations or all 648 simple closed words. The obstruction can be triggered by one adjacent antipodal jump.

### Surviving Structure
- For a `σ σ` word, TF conflict can be expressed in terms of prefix signatures.
- If `σ` contains adjacent antipodal processors `a, b` with `b = a + 2 mod 4`, let `j = b`.
- Then `a = anti(j)` is not in the local triple `{left(j), j, right(j)}`.
- So the local signature for `j` is unchanged between the moment just before `anti(j)` fires and the next moment just before `j` fires.
- At the first time, `j` is non-mover; at the second, `j` is mover. Hence a TF conflict is immediate.
- On the 4-cycle, a permutation with no adjacent antipodal pair is exactly a cyclic or reverse-cyclic order.

### Reformulations
The binary theorem now has a concise proof skeleton:

1. conflict-free `=>` mover word is `σ σ` (from prior explorations),
2. if `σ` has an adjacent antipodal pair, Exploration 12 gives an immediate symbolic TF conflict,
3. therefore `σ` has no adjacent antipodal pair,
4. on `C4`, that forces `σ` to be cyclic or reverse-cyclic.

LOAD-BEARING ASSESSMENT: yes. This is the first point where the binary-side theorem looks short enough to formalize without any serious search or ugly case tree.

### Concrete Artifacts

COMPUTED EXAMPLES:
- For every non-cyclic/non-reverse permutation `σ`, the adjacent-antipair lemma correctly predicts the same symbolic conflict found by the full prefix-signature checker.
- Representative examples:
  - `σ=(0,1,3,2)`: adjacent antipodal pair `(1,3)= (anti(3),3)` gives immediate conflict for processor `3`
  - `σ=(0,2,1,3)`: adjacent antipodal pair `(0,2)= (anti(2),2)` gives immediate conflict for processor `2`
  - `σ=(3,1,0,2)`: adjacent antipodal pair `(3,1)= (anti(1),1)` gives immediate conflict for processor `1`

STRUCTURAL RESULTS:
- Adjacent antipodal jumps are exactly the local forbidden pattern behind non-cyclic `σ`.
- The symbolic TF conflict proof no longer needs the full second half of the word; it is already visible in one consecutive pair of moves in the first half.

TOOLS:
- Python validation comparing the adjacent-antipair lemma against the full prefix-signature conflict detector on all non-cyclic permutations.

REPRESENTATIONS:
- `anti(j) = j+2 mod 4`.
- Local forbidden pattern: `anti(j), j` consecutive in `σ`.

### What Would Unblock This
- A clean proof that any conflict-free fair binary cycle indeed has mover word `σ σ` as a first step.
- A Lean encoding of the prefix-signature argument short enough to survive formalization without elaborate automation.

### Key Parameters
- Universe tested: all 16 non-cyclic/non-reverse permutations `σ`.
- Validation target: agreement between the local antipodal-jump lemma and the full symbolic conflict detector.

### Open Questions
- Can the step “conflict-free fair cycle => mover word `σ σ`” also be reduced to a comparably short local argument?
- Is there an `n > 4` analogue where “adjacent antipodal jump” is replaced by some larger forbidden local pattern on mover words?

## Synthesis after exploration 12

The binary side is now almost fully conceptual.

What has crystallized:
- A pure word-theoretic normal form (`σ σ`).
- A pure local obstruction (adjacent antipodal jump).
- A closed-form projection theorem (complementary repeated-shadow 2-router).

So the heavy native-decide block in `M_4_lower` now has a plausible replacement architecture:

1. reduce binary obstruction-free cycles to `σ σ`,
2. kill non-cyclic `σ` by the adjacent-antipodal-jump lemma,
3. read off the projection theorem for cyclic/reverse-cyclic sweeps,
4. contrast with the witness-side local-triple router.

That is a qualitatively different position from the start of this campaign. The open problem is no longer “find some noncomputational proof”; it is specifically “connect threshold validity to the existence of a local-triple repeated-shadow router.”

## Synthesis after exploration 11

The campaign now has a strong cross-`n` candidate mechanism.

Current residue:
- Binary obstruction-free systems at `n=4` are symbolically rigid:
  cyclic/reverse-cyclic `σ σ`, complementary repeated shadows, router capacity `2`.
- The `n=4` threshold witness exceeds that by orientation-fusion on a complementary pair, giving a local triple router.
- The higher witnesses `n=5..8` exhibit the same essential phenomenon:
  some forgotten processor `p` has a repeated shadow with mover set exactly `{left(p), p, right(p)}`.

This is the first point where the `M_4` investigation looks genuinely reusable.
The likely reusable conjecture is:

> Valid near-threshold witnesses require local-triple repeated-shadow routing at some processor.

If that is true, the lower-bound program becomes:
1. prove low-state systems cannot realize local-triple repeated-shadow routing,
2. prove optimal witnesses necessarily do.

That is much closer to a scalable mechanism than any DFS/native_decide architecture.

## Synthesis after exploration 10

The picture is now much cleaner than it was at exploration 1.

What the residue says:
- The binary obstruction-free world is a tiny symbolic family of sweep words.
- Its forgetful projections are complementary-pair 2-routers.
- The threshold witness exceeds this not by changing cycle length, but by fusing both binary orientation choices on one complementary repeated-shadow pair.

This is a qualitative upgrade in understanding:
- earlier explorations said “the witness needs 3-way routing”
- now the sharper statement is “the witness locally combines the two binary sweep orientations”

That is the first candidate mechanism that feels both conceptual and reusable:
sub-threshold systems are locked into one local sweep orientation,
while threshold-valid systems need a processor that can switch between them.

Future work should focus on making that orientation-fusion statement precise enough to prove.

## Synthesis after exploration 9

The route is now significantly sharper than when this campaign started.

What has stabilized:
- The sub-threshold binary world is completely rigid:
  - word-theoretic normal form `σ σ`,
  - cyclic/reverse-cyclic for no TF conflict,
  - complementary repeated-shadow theorem,
  - router capacity `2`.
- The threshold witness differs from that world in one precise processor-local way:
  forgetting the ternary site produces router capacity `3`, while forgetting any binary site does not.

What this suggests:
- The lower bound should be cast as a **processor-local routing-capacity theorem**, not a global cycle-count theorem.
- The likely statement to aim for is:
  “Any valid threshold-level `n=4` witness must have some processor `p` with `cap_p ≥ 3`.”
  Combined with the binary obstruction theorem `cap_p ≤ 2`, this would replace the heavy computational certificate with a conceptual separation.

Best next move:
- Stop mining more binary cycle data.
- Start proving the symbolic binary theorem on words and looking for a witness-side argument that `cap_p ≥ 3` is necessary for validity at threshold.

## Synthesis after exploration 8

The residue from explorations 1–8 now points to a coherent proof architecture.

Patterns across artifacts:
- The threshold witness and the sub-threshold binary world differ at the level of **projected local routing**, not at the level of cycle length.
- The binary obstruction-free family is far more rigid than expected:
  first it collapsed to the 16 conflict-free cycles,
  then to cyclic/reverse-cyclic `σ σ` mover words,
  and finally to a closed-form projection theorem with complementary repeated shadows and 2-way routing.
- The witness consistently violates this rigidity in the same place: repeated projected shadows are upgraded from 2-way to 3-way routing at the processor carrying extra memory.

Cross-pollination:
- Exploration 2’s witness-side “3-way local router” picture and Exploration 8’s binary-side “complementary repeated-shadow 2-router” picture now fit together almost perfectly. The lower bound should probably be framed as a routing-capacity mismatch, not as a generic phase-counting argument.

Most promising next direction:
- Prove the binary-side theorem symbolically in Lean:
  `no TF conflict -> cyclic/reverse-cyclic σσ -> complementary repeated-shadow 2-router`.
- In parallel, search for a witness-side necessity statement that turns “one ternary processor in the optimal witness acts as a 3-router” into “any valid threshold witness must admit a projection with 3-way repeated-shadow routing.”

This reformulation changes the effective search space. Future explorations should default to the routing-capacity representation rather than raw cycle enumeration.

## Exploration 30

### Strategy
Use a dedicated PA sub-agent to compress the binary `n=4` theorem into the shortest realistic lemma chain and identify the one proof obligation that is still genuinely hard.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the worry that the binary theorem still hides several equally difficult missing arguments. The proof-design pass isolates one real remaining gap rather than a diffuse cloud of unfinished work.

### Surviving Structure

STRUCTURAL RESULTS:
- A clean binary theorem route now looks like:
  1. prefix-signature conflict criterion
  2. permutation-halves lemma: no conflict implies `w = σ τ` with `σ, τ` permutations
  3. adjacent-antipodal obstruction: `anti(j), j` consecutive in `σ` gives immediate conflict
  4. on `C4`, no adjacent antipodal pair forces `σ` cyclic or reverse-cyclic
  5. second-half agreement lemma: if `w = σ τ` is no-conflict, then `τ = σ`
- Once this is done, the controller-complexity corollary is immediate: cyclic/reverse-cyclic `σ σ` gives complementary repeated shadows with deterministic 2-controllers.

### Reformulations
The main contribution is diagnostic:
the unresolved hard point on the binary side is concentrated in the second-half agreement lemma

`σ τ`, `τ ≠ σ`  =>  symbolic conflict.

Everything else now looks short and conceptual.

LOAD-BEARING ASSESSMENT: yes. This improves planning quality because future effort can target the one lemma that matters, instead of continuing broad binary experimentation.

### Concrete Artifacts

STRUCTURAL RESULTS:
- Proof skeleton from the PA sub-agent:
  - prefix-signature conflict criterion
  - permutation-halves lemma
  - adjacent-antipodal local obstruction
  - no-antipodal-pair implies cyclic/reverse-cyclic
  - second-half agreement lemma `τ = σ`
- The sub-agent’s assessment matches local progress:
  the unresolved hard point is exactly the `τ ≠ σ` symbolic-conflict compression.

### What Would Unblock This
- A clean “earliest inversion forces repeated local signature” lemma for `σ τ`.
- Or a prefix-set formulation that makes `τ ≠ σ` conflict inevitable without enumerating cases.

### Open Questions
- Can the permutation-halves lemma itself be shortened to a one-line local obstruction, or is it already close enough?
- Is the right abstraction for the hard step earliest inversion, prefix-set mismatch, or something geometric about the 8-step cube walk?

## Exploration 34 (probe)

### Strategy
Simplify the remaining binary second-half agreement gap by checking whether the same adjacent-antipodal local obstruction also kills any second-half permutation `τ` that is not cyclic/reverse-cyclic.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- On the 4-cycle, every non-cyclic permutation has an adjacent antipodal pair.
- So the same local lemma already used on the first-half permutation applies equally to `τ`:
  if `τ` is not cyclic/reverse-cyclic, then `σ τ` has an immediate symbolic TF conflict.

This reduces the remaining hard binary gap substantially:

- first prove `σ` is cyclic/reverse-cyclic
- then note `τ` must also be cyclic/reverse-cyclic
- so the unfinished second-half agreement lemma only needs to eliminate the 7 cyclic/reverse words `τ ≠ σ`, not all 23 alternatives

### Open Questions
- Can the 7 remaining cyclic/reverse `τ ≠ σ` cases be dispatched by one or two structured lemmas (rotations vs reversed orientation), rather than by raw case checking?

## Exploration 38 (probe)

### Strategy
Compress the 7 normalized cyclic/reverse `τ ≠ σ` cases further by grouping them into same-orientation rotations and reverse-orientation rotations of the normalized word `σ = (0,1,2,3)`.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- The 7 normalized second-half cases reduce to two structured families:

1. **Same-orientation rotations**
   - `τ = (1,2,3,0)` gives conflict at processor `1` with signature `(1,1,1)`
   - `τ = (2,3,0,1)` and `τ = (3,0,1,2)` give conflict at processor `0` with signature `(0,1,1)`

2. **Reverse-orientation rotations**
   - `τ = (0,3,2,1)` and `τ = (3,2,1,0)` give conflict at processor `2` with signature `(1,1,0)`
   - `τ = (2,1,0,3)` gives conflict at processor `1` with signature `(1,1,0)`
   - `τ = (1,0,3,2)` gives conflict at processor `1` with signature `(1,1,1)`

So the remaining binary second-half lemma now looks much smaller:
it is no longer “7 unrelated cases,” but two short rotation families.

### Open Questions
- Can these two rotation families be dispatched by direct formulas for the repeated signatures, avoiding any residual finite case split?

## Exploration 37

### Strategy
Package the static binary side into a theorem-target note with explicit lemmas, so the almost-finished `n=4` symbolic proof is no longer only implicit in the exploration residue.

### Outcome
SUCCEEDED

### Concrete Artifacts

TOOLS:
- New theorem-target note:
  [binary_q4_controller_theorem.md](./lean/docs/binary_q4_controller_theorem.md)

STRUCTURAL RESULTS:
- The note records the clean current decomposition of the binary theorem:
  1. prefix-signature conflict criterion
  2. permutation-halves lemma
  3. adjacent-antipodal obstruction
  4. no-adjacent-antipodal implies cyclic/reverse-cyclic
  5. second-half agreement lemma `τ = σ`
- It also records the current status:
  the only real hard gap is Lemma 5.

REPRESENTATIONS:
- This note is now the cleanest static-side package for future formalization, complementary to the dynamic theorem note [controller_recurrence_theorem.md](./lean/docs/controller_recurrence_theorem.md).

## Exploration 42

### Strategy
Create a small typechecked Lean anchor file for the binary word side, so the theorem program is no longer only in markdown notes.

### Outcome
SUCCEEDED

### Concrete Artifacts

TOOLS:
- New typechecked scratch Lean file:
  [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean)

STRUCTURAL RESULTS:
- The file currently packages:
  - `Proc4`, `Word4`
  - `left4`, `right4`, `anti4`
  - `flipBit4`
  - `prefixParity4`
  - `sig4`
  - `moverAt?`
  - `sigConflict4`
  - canonical cyclic/reverse words
  - basic local-triple distinctness lemmas on `Fin 4`
- It typechecks with `lake env lean LeanMn/SmallN/BinaryQ4Word.lean`.

REPRESENTATIONS:
- This is the first actual Lean artifact of the controller route, distinct from the theorem-target notes.

### Open Questions
- How much of the adjacent-antipodal lemma can be proved cleanly in this scratch file before importing heavier infrastructure?
- Should the next Lean step target the symbolic conflict criterion or the projection/controller corollary?

## Exploration 43

### Strategy
Push one actual local fact from the binary theorem into the scratch Lean file: flipping the antipode should preserve the local triple `(left, self, right)`.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added and typechecked:
  `flipBit4_anti_preserves_localTriple`
  in [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean).
- This is the first direct formalized piece of the adjacent-antipodal obstruction mechanism.

TOOLS:
- The scratch Lean file is no longer only definitional; it now contains one genuine theorem supporting the controller-route formalization.

### Open Questions
- Can the full adjacent-antipodal symbolic-conflict lemma be built on top of this local-triple preservation fact without importing too much extra infrastructure?

## Exploration 44

### Strategy
Use the local-triple preservation fact to prove an actual symbolic-conflict theorem in Lean for words containing an adjacent `anti(j), j` pattern.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added and typechecked in [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - `sig4_append_anti_self_eq`
  - `moverAt?_append_anti`
  - `moverAt?_append_self`
  - `sigConflict4_of_adjacent_anti_self`
- This is the first full symbolic-conflict theorem in Lean for the binary route, not just a local helper lemma.

TOOLS:
- The scratch Lean file now contains a real theorem corresponding to the adjacent-antipodal obstruction discovered in the exploration log.

### Open Questions
- Can the binary theorem’s other local pieces (especially the projection/controller corollary) be pushed into the same scratch file with similarly light infrastructure?

## Exploration 45

### Strategy
Package the two product-72 `n=5` impossibility families into a controller-language theorem note, so the dynamic half has a concrete first pilot family rather than only abstract theorem schemas and scattered worked examples.

### Outcome
SUCCEEDED

### Concrete Artifacts

TOOLS:
- New family-specific theorem note:
  [product72_controller_reuse.md](./lean/docs/product72_controller_reuse.md)

STRUCTURAL RESULTS:
- The note records the common static and dynamic pattern shared by the two product-72 families:
  - repeated-shadow controller complexity `<= 2`
  - off-cycle repeated-shadow states reuse good-cycle mover entries
  - the reused moves stay in a finite bad region
  - recurrence follows
- It also packages the strongest current `n=5` bridge:
  product-72 pair-controllers `{2,3}` and `{3,4}` at forgotten processor `3`
  versus witness triple-controller `{2,3,4}`.

REPRESENTATIONS:
- The controller program now has four concrete notes:
  - [binary_q4_controller_theorem.md](./lean/docs/binary_q4_controller_theorem.md)
  - [controller_recurrence_theorem.md](./lean/docs/controller_recurrence_theorem.md)
  - [witness_controller_necessity.md](./lean/docs/witness_controller_necessity.md)
  - [product72_controller_reuse.md](./lean/docs/product72_controller_reuse.md)

### Open Questions
- Is the product-72 theorem the right first formal pilot for the dynamic side, or should the first Lean pilot stay on the binary `n=4` side until the static theorem is more complete?

## Exploration 46

### Strategy
Push the binary scratch Lean file one notch further by formalizing the normalized first-half signature table for the base word `[0,1,2,3,0,1,2,3]`, since that table is exactly what the structured second-half reduction uses.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added and typechecked in [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - constants `p0`, `p1`, `p2`, `p3`
  - `baseWord4`
  - explicit normalized signature lemmas:
    - `baseWord4_sig_p0_t1`
    - `baseWord4_sig_p0_t2`
    - `baseWord4_sig_p1_t2`
    - `baseWord4_sig_p1_t3`
    - `baseWord4_sig_p2_t2`
    - `baseWord4_sig_p2_t3`
- Together with Exploration 44, the scratch file now contains:
  - the core local obstruction lemma
  - the normalized first-half signature table needed for the structured finite reduction of the remaining binary gap

### Open Questions
- Can the two sweep-shape second-half lemmas now be proved on top of this signature table with only light additional infrastructure?

## Exploration 47

### Strategy
Formalize one representative second-half conflict case in the binary scratch file, to test whether the structured finite reduction is realistic in Lean rather than only on paper.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added and typechecked in [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - `baseWord4_forwardRot1`
  - `baseWord4_forwardRot1_sig_p1_t3`
  - `baseWord4_forwardRot1_sig_p1_t4`
  - `sigConflict4_base_forwardRot1`
- This proves one normalized forward-sweep second-half conflict case directly in Lean.

TOOLS:
- The scratch file now contains:
  - one general local obstruction theorem (`sigConflict4_of_adjacent_anti_self`)
  - one explicit normalized second-half conflict theorem (`sigConflict4_base_forwardRot1`)

### Open Questions
- Is it better to continue adding the remaining normalized cases one by one, or to step back and seek a more compressed Lean statement for the whole forward-sweep family?

## Exploration 48

### Strategy
Add a representative reverse-orientation conflict theorem to the binary scratch file, so the Lean side now covers both sweep-shape families of the normalized second-half reduction.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added and typechecked in [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - `baseWord4_reverse0`
  - `baseWord4_reverse0_sig_p2_t3`
  - `baseWord4_reverse0_sig_p2_t6`
  - `sigConflict4_base_reverse0`
- The scratch file now contains one representative forward-sweep second-half conflict theorem and one representative reverse-sweep second-half conflict theorem.

### Open Questions
- Can the remaining cyclic/reverse normalized second-half cases be generated from these representatives by dihedral symmetry in Lean, or is it better to encode a small family reduction explicitly?

## Exploration 49

### Strategy
Introduce the natural `C4` symmetry operations into the binary scratch file, so the remaining explicit second-half cases can potentially be reduced by symmetry rather than multiplied by hand.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added and typechecked in [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - `rotProc4`
  - `revProc4`
  - equivariance lemmas:
    - `left4_rotProc4`
    - `right4_rotProc4`
    - `anti4_rotProc4`
    - `left4_revProc4`
    - `right4_revProc4`
- This is the right infrastructure for expressing dihedral symmetry of the ring at the theorem level.

### Open Questions
- Can `sigConflict4` be shown invariant under word renaming by `rotProc4` / `revProc4` with tolerable proof overhead?
- If yes, do the two representative second-half theorems already cover the whole normalized cyclic/reverse family?

## Exploration 51

### Strategy
Finish the rotation-symmetry step in the binary scratch file and use it to turn the representative forward/reverse second-half conflict theorems into whole families.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added and typechecked in [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - `invRotProc4`, `rotBits4`
  - `rotProc4_inv_left`, `rotProc4_inv_right`, `rotProc4_injective`
  - `flipBit4_rotBits4`
  - `foldl_flipBit4_rotBits4`
  - `prefixState4_rotWord4`
  - `prefixParity4_rotWord4`
  - `sig4_rotWord4`
  - `moverAt?_rotWord4`
  - `moverAt?_rot_eq`
  - `sigConflict4_rotWord4`
  - `sigConflict4_rot_base_forwardRot1`
  - `sigConflict4_rot_base_reverse0`
- So the scratch file now has a real symmetry reduction: one forward representative and one reverse representative generate their rotated families formally.

### Open Questions
- Is reversal invariance still worth proving, or is rotation plus the current normalized family reduction already enough for the binary side?

## Exploration 52

### Strategy
Package the adjacent-antipodal obstruction as a reusable word predicate theorem in the scratch Lean file, rather than only as a theorem about a specific decomposition.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added and typechecked in [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - `HasAdjacentAnti4`
  - `sigConflict4_of_hasAdjacentAnti4`
- So the local binary obstruction is now expressed in the right reusable theorem form:
  any word containing an adjacent `anti(j), j` pattern has symbolic conflict.

### Open Questions
- Is the next best step to formalize the “non-cyclic permutation implies `HasAdjacentAnti4`” reduction, or to continue expanding the normalized second-half family theorems?

## Exploration 53

### Strategy
Start the dynamic side in Lean by turning the controller-recurrence theorem note into actual scratch definitions for controller entries, realization, and bad reuse regions.

### Outcome
SUCCEEDED

### Concrete Artifacts

TOOLS:
- New typechecked scratch Lean file:
  [ControllerReuse.lean](./lean/LeanMn/SmallN/ControllerReuse.lean)

STRUCTURAL RESULTS:
- The file now packages generic definitions for:
  - `ControllerEntry`
  - `Realizes`
  - `BadReuseRegion`
- This gives the dynamic side a genuine formalization anchor, analogous to what [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean) already does for the static binary side.

REPRESENTATIONS:
- The controller route now has scratch Lean anchors on both sides:
  - static binary side: `BinaryQ4Word.lean`
  - dynamic recurrence side: `ControllerReuse.lean`

### Open Questions
- Is the next useful formalization step on the dynamic side the abstract recurrence theorem itself, or one small product-72 instantiation lemma that produces a concrete bad reuse region?

## Exploration 50

### Strategy
Add the induced ring symmetries on words to the binary scratch file, so the remaining finite reduction can be phrased at the word level rather than only at the processor level.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added and typechecked in [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - `rotWord4`
  - `revWord4`
- The scratch file now contains both processor-level and word-level dihedral symmetry data.

REPRESENTATIONS:
- The static binary theorem now has the basic vocabulary needed to state symmetry reductions directly in Lean.

### Open Questions
- Is it worth proving full `sigConflict4` invariance under `rotWord4` / `revWord4`, or is a smaller ad hoc use of symmetry enough for the remaining explicit cases?

## Exploration 35 (probe)

### Strategy
Reduce the last binary second-half gap further by classifying the 7 cyclic/reverse `τ ≠ σ` cases for the normalized first half `σ=(0,1,2,3)` into genuine conflict archetypes.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- The 7 remaining cyclic/reverse `τ ≠ σ` cases collapse to 5 conflict archetypes:
  1. `τ=(1,2,3,0)`:
     conflict at processor `1`, signature `(1,1,1)`, comparing first-half time `3` to second-half time `4`
  2. `τ=(2,3,0,1)` or `(3,0,1,2)`:
     conflict at processor `0`, signature `(0,1,1)`, comparing first-half time `3` to second-half time `6` or `5`
  3. `τ=(0,3,2,1)` or `(3,2,1,0)`:
     conflict at processor `2`, signature `(1,1,0)`, comparing first-half time `3` to second-half time `6` or `5`
  4. `τ=(2,1,0,3)`:
     conflict at processor `1`, signature `(1,1,0)`, comparing first-half time `2` to second-half time `5`
  5. `τ=(1,0,3,2)`:
     conflict at processor `1`, signature `(1,1,1)`, comparing first-half time `3` to second-half time `4`

STRUCTURAL RESULTS:
- The “7 remaining cases” are not genuinely 7 different behaviors.
- After normalizing the first half, only a handful of signature-repetition patterns remain.

### Open Questions
- Can these 5 archetypes themselves be compressed into 2 or 3 structured lemmas (same-orientation rotations, reverse-orientation rotations)?

## Exploration 31

### Strategy
Use a dedicated PA sub-agent to sharpen the dynamic side of the controller route and decide whether the right theorem is really “2-controller implies bad orbit” or something more structured.

### Outcome
SUCCEEDED

### Failure Constraint
Not applicable.

### What This Rules Out
This rules out the overly crude theorem statement
“controller complexity <= 2 implies recurrence”
as the main abstract engine. That is too strong and hides the real mechanism.

### Surviving Structure

STRUCTURAL RESULTS:
- The right abstract object is a **reuse-closed deterministic repeated-shadow controller subsystem**.
- The dynamic theorem should isolate:
  - controller entries reused off-cycle,
  - soundness of that reuse,
  - closure of the resulting bad region,
  - and then recurrence on the induced deterministic map.
- In that formulation, the recurrence conclusion is trivial; the real family-specific work is proving the existence of the bad reuse region.

### Reformulations
The recommended abstract theorem is:

**Controller-Reuse Recurrence Theorem.**
If a good cycle induces a deterministic repeated-shadow controller on some repeated shadows, and there exists a finite off-cycle bad reuse region `B` where:

1. every state realizes one of those controller entries,
2. the reused mover is still enabled there,
3. the reused move stays inside `B`,
4. `B` stays outside the legitimate/convergent region,

then the induced successor map on `B` is a total deterministic map on a finite set, hence contains a directed bad cycle, contradicting convergence.

This is a much better abstract theorem than
“2-controller implies bad orbit”
because it cleanly separates:
- the abstract recurrence mechanism,
- from the family-specific geometry needed to produce the bad reuse region.

LOAD-BEARING ASSESSMENT: yes. This is the cleanest formulation of the dynamic half so far, and it aligns perfectly with the old product-72 shadow proofs: those proofs are precisely concrete constructions of such a bad reuse region.

### Concrete Artifacts

STRUCTURAL RESULTS:
- Candidate abstract notions:
  - repeated-shadow controller
  - controller entry `(shadow, controller-class, mover)`
  - state realizes a controller entry
  - bad reuse region `B`
- Candidate theorem:
  `reuse-closed deterministic repeated-shadow subsystem => recurrent bad orbit`

### What Would Unblock This
- A clean definitions note for controller entries / bad reuse region / induced bad dynamics.
- One fully worked family-specific instantiation, probably the product-72 `n=5` shadow theorem rewritten in this language.

### Open Questions
- What is the weakest useful definition of “bad reuse region” that still makes the theorem reusable?
- Can the product-72 shadow proofs be rewritten almost verbatim in these definitions, or do they need a different organizing language?

## Exploration 54

### Strategy
Promote the abstract dynamic half from note-level schema into Lean by adding the deterministic reused-successor map and the finite-recurrence/cycle theorem for bad reuse regions.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Extended [ControllerReuse.lean](./lean/LeanMn/SmallN/ControllerReuse.lean) with:
  - `BadReuseRegion.reusedSucc`
  - `BadReuseRegion.exists_recurrence_pair`
  - `BadReuseRegion.exists_nontrivial_cycle`
- So the abstract dynamic theorem is now theorem-bearing Lean code, not just a route note.

VERIFICATION:
- `lake build LeanMn.SmallN.ControllerReuse` succeeds.

REPRESENTATIONS:
- The recurrence theorem is now cleanly factored into:
  - family-specific construction of a bad reuse region
  - generic finite deterministic recurrence on the carrier subtype

### Open Questions
- What is the best first family-specific instantiation: the standard product-72 cycle, or a smaller toy reuse region first?

## Exploration 55

### Strategy
Push the static binary scratch file past representative examples by lifting the normalized second-half conflict cases to generic forward/reverse sweep words via rotation.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Extended [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean) with:
  - all normalized forward/reverse mismatch words
  - `forwardSweepFrom0` / `reverseSweepFrom0`
  - generic sweep-word encodings `forwardSweepWord4` / `reverseSweepWord4`
  - normalization lemmas `forwardSweepWord4_eq_rot` and `reverseSweepWord4_eq_rot`
  - family theorems `sigConflict4_forwardSweepWord4_of_ne` and `sigConflict4_reverseSweepWord4`
- This means the whole cyclic/reverse second-half disagreement family is now covered in Lean at theorem level.

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4Word` succeeds.

REPRESENTATIONS:
- The old “7 normalized second-half cases” are no longer represented as a pile of isolated examples.
- They are now compressed into two sweep-shape families plus rotation.

LOAD-BEARING ASSESSMENT: yes. The remaining static binary work is now sharply localized to:
1. permutation-halves
2. adjacent-antipodal-to-cyclic/reverse reduction
3. hooking those reductions into the generic sweep-word theorems already formalized

### Open Questions
- Is the next best Lean step the permutation-halves lemma, or the explicit “no adjacent antipodal pair on `C4` implies cyclic/reverse-cyclic” theorem?

## Exploration 56

### Strategy
Formalize the remaining local `C4` combinatorics directly, without permutation enumeration: classify a distinct 4-term word by successive local neighbor choices and prove that forbidding adjacent antipodal jumps forces the forward/reverse sweep shapes.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Extended [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean) with:
  - local ring arithmetic lemmas (`left4_right4`, `right4_left4`, `left4_left4`, `right4_right4`, `anti4_anti4`, `left4_anti4`, `right4_anti4`)
  - `Proc4_rel_cases`
  - `eq_right_or_left_of_ne_self_ne_anti`
  - `sweep_or_reverse_of_distinct_no_adjacent_anti`
- This packages the “no adjacent antipodal pair on `C4` implies cyclic/reverse-cyclic” step in theorem form, without `native_decide` and without a large permutation case split.

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4Word` succeeds.

REPRESENTATIONS:
- The proof does not enumerate the 24 permutations.
- It works by local successor geometry:
  1. after rotating so the first element is anchored, the next distinct non-antipodal element must be a left or right neighbor
  2. the third element is then forced to be the antipode
  3. the fourth element is forced to be the remaining neighbor

LOAD-BEARING ASSESSMENT: very high. The static binary frontier is now essentially reduced to the permutation-halves lemma. Once the first-half/second-half permutation representation is in place, the current scratch file already contains the mechanism needed for the rest of the symbolic theorem.

### Open Questions
- What is the cleanest Lean representation for permutation-halves: a balanced/no-conflict word with explicit multiplicity assumptions, or a shorter direct lemma about repeated processors in the first half forcing symbolic conflict?

## Exploration 57

### Strategy
Probe the permutation-halves gap directly by normalizing first-half words with a repeat and checking whether the failure of first-half distinctness collapses to a small family of symbolic-conflict archetypes.

### Outcome
SUCCEEDED

### Concrete Artifacts

COMPUTED EXAMPLES:
- Up to relabeling by first occurrence, there are only 9 normalized first-half
  repeat shapes:
  - `(0,0,1,1)`
  - `(0,0,1,2)`
  - `(0,1,0,1)`
  - `(0,1,0,2)`
  - `(0,1,1,0)`
  - `(0,1,1,2)`
  - `(0,1,2,0)`
  - `(0,1,2,1)`
  - `(0,1,2,2)`
- Every balanced 8-word with non-distinct first half falls into one of those 9
  shapes, and every one empirically carries a short symbolic conflict witness.

STRUCTURAL RESULTS:
- The permutation-halves gap does not look like a large combinatorial wilderness.
- It has reduced to a tiny normalized family, suggesting a proof route by a
  short structural lemma on repeated/missing processors or, failing that, by a
  controlled normalized-family argument.

LOAD-BEARING ASSESSMENT: medium-high. This does not yet prove permutation-halves,
but it sharply lowers the complexity of the remaining binary work and makes it
look compatible with the existing normalization style.

### Open Questions
- Is there a single local mechanism that explains all 9 first-half-repeat shapes, or should permutation-halves be packaged as a short normalized-family lemma?

## Exploration 58

### Strategy
Push the controller route one step toward the live `M_4_lower` path by
tightening symbolic conflicts to real in-range witnesses and adding a bridge
module that speaks both the `Word4` language and the concrete `rs2222`
encoding used in [LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean).

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Strengthened [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - `sigConflict4` and `sigConflict4From` now require in-range witnesses
  - added arbitrary-start transport:
    - `prefixState4From`
    - `sig4From`
    - `sigConflict4.lift`
- New bridge file:
  [BinaryQ4LBBridge.lean](./lean/LeanMn/SmallN/BinaryQ4LBBridge.lean)
  with:
  - `cfgFromBits4`
  - `getBit_cfgFromBits4`
  - `tfKeyNat_cfgFromBits4`
  - `pathFromWord4`

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4Word` succeeds.
- `lake build LeanMn.SmallN.BinaryQ4LBBridge` succeeds.

REPRESENTATIONS:
- The symbolic side is no longer tied to the all-zero start state.
- There is now a theorem-bearing file that speaks both dialects:
  symbolic `Word4` traces and concrete `LB2222` encoded paths.

LOAD-BEARING ASSESSMENT: very high. The next integration theorem is now sharply
identified:

`sigConflict4From bits w -> isTFBlocked (pathFromWord4 bits w) = true`

Once that lands, the binary symbolic theorem will begin to feed the live
blocking checker directly rather than only running in parallel to it.

### Open Questions
- Is it cleaner to prove the conflict-to-`isTFBlocked` bridge via recursive
  entry-membership lemmas for `collectTF (pathFromWord4 bits w)`, or by
  defining a direct `collectTFWord4` recursion and proving it coincides with
  `collectTF ∘ pathFromWord4`?

## Exploration 59

### Strategy
Complete the direct bridge from symbolic conflicts to the concrete blocking
checker by proving recursive mover/nonmover `collectTF` membership and then
packaging `sigConflict4From` into `isTFBlocked` on the actual encoded path.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Extended [BinaryQ4LBBridge.lean](./lean/LeanMn/SmallN/BinaryQ4LBBridge.lean) with:
  - `moverEntry_mem_collectTF_pathFromWord4`
  - `nonmoverEntry_mem_collectTF_pathFromWord4`
  - `tfKeyNat_prefixState4From_eq_of_sigEq`
  - `hasTFConflict_of_mem_mem`
  - `sigConflict4From_imp_isTFBlocked`
  - `sigConflict4_imp_isTFBlocked`
  - `isTFBlocked_forwardSweepWord4_of_ne`
  - `isTFBlocked_reverseSweepWord4`

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4LBBridge` succeeds.

REPRESENTATIONS:
- The bridge is no longer just about encoding states.
- It now carries actual blocking information from the symbolic theorem side into
  the live `LB2222` checker language.

LOAD-BEARING ASSESSMENT: extremely high. The symbolic sweep-family theorems now
have concrete `isTFBlocked` corollaries on encoded traces. So the controller
route has crossed from “parallel scratch proof” into “usable live-path
replacement component.” The remaining main static obstacle is permutation-halves.

### Open Questions
- Can permutation-halves now be proved in the same theorem style, or should the
  9 normalized first-half repeat shapes be encoded explicitly as a short
  no-conflict exclusion family?

## Exploration 60

### Strategy
Exploit simplicity directly on the binary side to eliminate the easy repeat
geometries before attacking permutation-halves: adjacent repeats and the
alternating `abab` first-half pattern.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Extended [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean) with:
  - `flipBit4_commute`
  - `flipBit4_abab`
  - `prefixState4_append_abab_eq`
  - `not_simple_of_abab_before_end`
- The file already had:
  - `HasAdjacentRepeat4`
  - `SimpleWord4`
  - `prefixState4_append_self_self_eq`
  - `not_simple_of_adjacentRepeat4_before_end`

REPRESENTATIONS:
- Distance-1 first-half repeats are now structurally killed by simplicity.
- The `abab` double-repeat first-half pattern is also structurally killed by
  simplicity.

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4Word` succeeds.

LOAD-BEARING ASSESSMENT: high. This removes the easiest failure modes from
permutation-halves without any search, and it sets up a much tighter remaining
shape theorem.

### Open Questions
- After removing adjacent repeats and `abab`, can the remaining first-half
  non-nodup geometries be compressed to a tiny list of repeat-distance forms?

## Exploration 61

### Strategy
Package the remaining first-half non-nodup geometry for simple words into a
single theorem, so permutation-halves can proceed by a small disjunction of
repeat-distance forms rather than a diffuse case split.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Added to [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean):
  - `repeat_shape_of_not_nodup_adjacent_ne`
  - `first_four_repeat_shape_of_simple`
- Together these show:
  if the first four moves of a simple word are not distinct, then after ruling
  out adjacent repeats and `abab`, the prefix must have one of the three
  structural forms:
  - `abac`
  - `abca`
  - `abcb`

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4Word` succeeds.

REPRESENTATIONS:
- The permutation-halves blocker is no longer “all possible first-half repeats.”
- It is now a controlled three-form obstruction problem.

LOAD-BEARING ASSESSMENT: very high. The remaining binary blocker is now sharply
reduced to eliminating the `abac` / `abca` / `abcb` forms, rather than
establishing first-half distinctness from scratch.

### Open Questions
- Can each of the three repeat-distance forms be killed by one structural lemma,
  or does one of them still require a compact normalized-family exclusion?

## Exploration 62

### Strategy
Package the residual `abac` / `abca` / `abcb` first-half repeat families into
generic theorems, then use them to prove a single first-four conflict theorem
under simple + balanced hypotheses.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean)
  now contains:
  - generic `abac` family theorems
  - generic `abca` family theorems
  - generic `abcb` family theorem under balancedness
  - `sigConflict4_of_not_nodup_first_four`
  - `first_four_nodup_of_no_sigConflict`
  - `first_four_sweep_or_reverse_of_no_sigConflict`

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4Word` succeeds.

REPRESENTATIONS:
- The first-half part of permutation-halves is now theorem-shaped:
  1. if the first four are not distinct, there is symbolic conflict
  2. therefore no-conflict implies first four are distinct
  3. therefore no-conflict implies first four are a forward or reverse sweep

LOAD-BEARING ASSESSMENT: extremely high. This moves the main static blocker off
the first half entirely. The remaining binary work is now the second-half
agreement layer.

### Open Questions
- Can the second-half agreement layer be proved directly from the new
  first-half sweep theorem plus balancedness, or does it still need a compact
  normalized mismatch family statement?

## Exploration 63

### Strategy
Push the first-half sweep theorem across the live bridge so the same
`isTFBlocked` checker language used in
[LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean)
can already recover sweep structure from non-blocked traces.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- Extended [BinaryQ4LBBridge.lean](./lean/LeanMn/SmallN/BinaryQ4LBBridge.lean) with:
  - `first_four_sweep_or_reverse_of_isTFBlocked_false`

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4LBBridge` succeeds.

REPRESENTATIONS:
- The bridge now transports not only blocking results, but also first-half
  structural information back out of the concrete checker language.

LOAD-BEARING ASSESSMENT: very high. This is exactly the sort of corollary that
will be needed when replacing the `LB2222` certificate seam: from checker
output back to theorem hypotheses.

### Open Questions
- With the first half handled, is the cleanest next move to prove a direct
  second-half agreement theorem in `BinaryQ4Word`, or to derive a second-half
  structural corollary in the bridge first?

## Exploration 64

### Strategy
Push the first-half side one step further by turning the packaged repeat-family
theorems into an actual structural consequence of `¬ sigConflict4`: the first
four moves are not just distinct, they are a forward or reverse sweep.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean)
  now contains:
  - `sigConflict4_of_not_nodup_first_four`
  - `first_four_nodup_of_no_sigConflict`
  - `first_four_sweep_or_reverse_of_no_sigConflict`

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4Word` succeeds.
- `lake build LeanMn.SmallN.BinaryQ4LBBridge` succeeds.

REPRESENTATIONS:
- The first-half part of permutation-halves is no longer an informal story.
- It is now a theorem pipeline:
  `¬ sigConflict4` + simple + balanced
  `=>` first four distinct
  `=>` first four are a sweep

LOAD-BEARING ASSESSMENT: extremely high. This shifts the main remaining static
work entirely onto the second-half agreement layer.

### Open Questions
- Can the second-half agreement theorem now be proved directly by combining:
  1. balancedness,
  2. the first-half sweep theorem,
  3. the existing forward/reverse mismatch conflict theorems?

## Exploration 65

### Strategy
Finish the second-half agreement layer after the sweep-mismatch theorems, then
combine the forward and reverse branches into a full 8-step sweep theorem and
push that structure back across the live bridge.

### Outcome
SUCCEEDED

### Concrete Artifacts

STRUCTURAL RESULTS:
- [BinaryQ4Word.lean](./lean/LeanMn/SmallN/BinaryQ4Word.lean)
  now contains:
  - `second_four_agree_of_forward_no_sigConflict`
  - `second_four_agree_of_reverse_no_sigConflict`
  - `eight_word_sweep_of_no_sigConflict`
- [BinaryQ4LBBridge.lean](./lean/LeanMn/SmallN/BinaryQ4LBBridge.lean)
  now contains:
  - `eight_word_sweep_of_isTFBlocked_false`

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4Word` succeeds.
- `lake build LeanMn.SmallN.BinaryQ4LBBridge` succeeds.

REPRESENTATIONS:
- The binary static side is now a full 8-step structural theorem:
  under simple + balanced + no symbolic conflict, the whole word is one of the
  two repeated sweeps.
- The live bridge transports that result back into checker language:
  `isTFBlocked = false` implies the encoded 8-step word has sweep form.

LOAD-BEARING ASSESSMENT: extremely high. The main remaining gap is no longer the
binary word theorem itself. It is now the path-seam integration into
`LB2222`, i.e. replacing the DFS/certificate residual branch with the new
sweep theorem.

### Open Questions
- What is the cleanest `LB2222` seam theorem now? The likely target is:
  any encoded simple fair 8-step cycle with `isTFBlocked = false` must equal a
  repeated sweep word, after which the remaining branch can be discharged
  analytically.

## Exploration 66

### Strategy
Break the import-cycle blocker between the scratch bridge and the live
`LB2222` path, then test the first real live-path transport move:
getting from actual `rs2222` configs to the bridge’s boolean-state language.

### Outcome
PARTIAL

### Concrete Artifacts

CODE CHANGES:
- Added
  [BinaryQ4Core.lean](./lean/LeanMn/SmallN/BinaryQ4Core.lean)
  to hold the shared binary-`Q4` core:
  - `rs2222`
  - bit/TF primitives
  - `collectTF`, `isTFBlocked`, `buildTF`
  - `encCfg` / `decCfg`
  - `flipCfg`, `encCfg_flipCfg`, `encCfg_move`
  - `leftP_eq_left`, `rightP_eq_right`, `getBit_encCfg`
- Repointed
  [BinaryQ4LBBridge.lean](./lean/LeanMn/SmallN/BinaryQ4LBBridge.lean)
  to import the core module instead of `LB2222`.
- Repointed
  [LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean)
  to import the core module and removed the duplicated local core definitions.
- Added new bridge lemmas in
  [BinaryQ4LBBridge.lean](./lean/LeanMn/SmallN/BinaryQ4LBBridge.lean):
  - `bitsOfCfg4`
  - `cfgFromBits4_bitsOfCfg4`
  - `bitsOfCfg4_cfgFromBits4`
  - `cfgFromBits4_flipBit4_bitsOfCfg4`
  - `pathFromWord4_cons_bitsOfCfg4`

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4Core` succeeds.
- `lake build LeanMn.SmallN.BinaryQ4LBBridge` succeeds.
- `lake build LeanMn.SmallN.LB2222` succeeds.
- `lake build LeanMn.SmallN.Theorem` succeeds.

### What This Rules Out
This rules out the previous dependency-cycle excuse for not using the scratch
bridge on the live path. The blocker is no longer file structure.

### Surviving Structure

CURRENT FRONTIER:
- The bridge is now *legally usable* from the live side.
- The next live theorem still needs either:
  1. a clean `gcPathN = pathFromWord4 ...` transport theorem for 8-step
     cycles, or
  2. a different route that bypasses that transport by using generic
     no-entry-conflict / fire-count structure directly.

LOAD-BEARING ASSESSMENT: high. This was not the final seam theorem, but it
converted a structural blocker into a proof-design blocker, which is exactly
the right kind of progress at this stage.

## Exploration 67

### Strategy
Attempt the first actual live-path transport theorem:
for an 8-step `GoodCycle` on `rs2222`, identify `gcPathN` with the bridge path
`pathFromWord4 ...`.

### Outcome
PARTIAL

### What Failed
- A direct theorem inside
  [LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean)
  that manually threaded boolean states through 8 steps was too brittle.
- The proof kept getting dragged into:
  - dependent `gc.configs.length = 8` rewrites,
  - `nextIndex` arithmetic noise,
  - and low-level coercion rewrites around `encCfg_flipCfg`.

### Surviving Structure

NEW PROOF-SHAPE INSIGHT:
- The right bridge state is no longer
  `flipBit4 (bitsOfCfg4 c) mover`.
- The useful recursive state is
  `bitsOfCfg4 (flipCfg c mover)`.

This is now theoremized in
[BinaryQ4LBBridge.lean](./lean/LeanMn/SmallN/BinaryQ4LBBridge.lean)
via:
- `bitsOfCfg4_flipCfg`
- `pathFromWord4_cons_cfg`

So the next transport attempt should be:
1. recurse on actual configs,
2. use `gcMover_step` / `move_eq_flipCfg`,
3. and let `pathFromWord4_cons_cfg` absorb the boolean-state bookkeeping.

### Load-Bearing Assessment
Moderate but real. The failed live theorem still produced the correct normal
form for the next proof attempt, and that normal form is materially simpler
than the original boolean-threading approach.

## Exploration 68

### Strategy
Move the uniform-direction branch into the live `LB2222` path by proving that a
uniform `GoodCycle` on `rs2222` has an explicit 8-step sweep mover word.

### Outcome
SUCCEEDED

### Concrete Artifacts

LIVE-PATH THEOREMS:
- [LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean)
  now contains:
  - `gc_nextIndex_eq_succ`
  - `gcWordFrom_zero_eight_of_uniformCW`
  - `gcWordFrom_zero_eight_of_uniformCCW`

VERIFICATION:
- `lake build LeanMn.SmallN.LB2222` succeeds.

REPRESENTATIONS:
- A uniform clockwise `GoodCycle` on `rs2222` now has first eight movers
  exactly `a, right a, anti a, left a, a, right a, anti a, left a`.
- The uniform counterclockwise branch is the reverse analogue.
- This is now a theorem about the actual live `GoodCycle` mover sequence, not
  just a symbolic `Word4` scratch statement.

LOAD-BEARING ASSESSMENT: high. The next natural step is to use binary parity to
show that the uniform branch returns after 8 steps, hence has length exactly 8;
after that, this branch should be close to a direct explicit-bad-cycle
contradiction.

## Exploration 69

### Strategy
Push the live uniform-direction branch past “first eight movers are sweep” and
derive exact cycle length `8`, then collapse the full live path to the explicit
8-step sweep path.

### Outcome
SUCCEEDED

### Concrete Artifacts

LIVE-PATH RESULTS:
- [BinaryQ4GoodCyclePath.lean](./lean/LeanMn/SmallN/BinaryQ4GoodCyclePath.lean)
  now contains `gcWordFrom_snoc`.
- [LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean)
  now contains:
  - `gc_prefixFireCount_eq_count_gcWordFrom`
  - `gc_prefixFireCount_eight_eq_two_of_uniformCW`
  - `gc_prefixFireCount_eight_eq_two_of_uniformCCW`
  - `gc_config8_eq_start_of_uniformCW`
  - `gc_config8_eq_start_of_uniformCCW`
  - `gc_len_eq_8_of_uniformCW`
  - `gc_len_eq_8_of_uniformCCW`
  - `gcPathN_eq_forwardSweepPath_of_uniformCW`
  - `gcPathN_eq_reverseSweepPath_of_uniformCCW`

VERIFICATION:
- `lake build LeanMn.SmallN.BinaryQ4GoodCyclePath` succeeds.
- `lake build LeanMn.SmallN.LB2222` succeeds.

REPRESENTATIONS:
- The live file no longer merely knows the first 8 movers of a uniform branch.
- It now proves that any uniform-direction `GoodCycle` on `rs2222` has length
  exactly `8`.
- Consequently the entire encoded path is exactly one of the two explicit sweep
  paths.

LOAD-BEARING ASSESSMENT: very high. This means the native-decide seam is now
reduced to:
1. the mixed-direction branch, and
2. the explicit-bad-cycle contradiction for the two concrete 8-step sweep
   paths.

## Exploration 70

### Strategy
Replace the remaining “Python-only understanding” of the sweep shadow dynamics
with live Lean theorems: partner configs, flip commutation, and the 3-step
partner successor law on uniform sweeps.

### Outcome
SUCCEEDED

### Concrete Artifacts

LIVE-PATH RESULTS:
- [LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean)
  now contains:
  - `flipCfg_twice`
  - `flipCfg_comm`
  - `partnerCfg`
  - `partner_step3_of_uniformCW`
  - `partner_step3_of_uniformCCW`

VERIFICATION:
- `lake build LeanMn.SmallN.LB2222` succeeds.

REPRESENTATIONS:
- The live file now knows the exact sweep shadow dynamics:
  for a uniform branch, firing the mover at a partner config advances to the
  partner three steps later along the 8-cycle.
- This is the Lean version of the `k ↦ k+3 (mod 8)` complement-cycle pattern
  previously only observed in the Q4 kernel scripts.

LOAD-BEARING ASSESSMENT: high. The uniform branch now has:
1. exact length `8`,
2. exact good path shape,
3. exact partner successor law.

What remains for deleting the certificate on that branch is to prove the
partner states are all outside `gc.configs`, then feed the resulting 8-cycle of
`badStep`s into `not_acc_of_finite_cycle'`. After that, the only surviving
native-decide dependency should be the mixed-direction branch.

## Exploration 71

### Strategy
Finish the main missing theorem on the sweep-shadow route: prove that partner
states are genuinely off-cycle in the uniform branch, using only uniqueness of
the mover plus the already-proved 3-step partner successor law.

### Outcome
SUCCEEDED

### Concrete Artifacts

LIVE-PATH RESULTS:
- [LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean)
  now contains:
  - `gcMover_next_of_uniformCW`
  - `gcMover_next_of_uniformCCW`
  - `gcMover_next3_of_uniformCW`
  - `gcMover_next3_of_uniformCCW`
  - `partner_not_get_of_uniformCW`
  - `partner_not_get_of_uniformCCW`
  - `partner_not_mem_of_uniformCW`
  - `partner_not_mem_of_uniformCCW`

VERIFICATION:
- `lake build LeanMn.SmallN.LB2222` succeeds.

REPRESENTATIONS:
- The off-cycle fact is now structural, not computational:
  if a partner state were on the good cycle, then by uniqueness of the mover
  and `partner_step3`, the next cycle mover would have to be both `left m` and
  `right m`, impossible on `C4`.
- So the uniform branch now has:
  1. exact 8-step good path,
  2. exact partner successor law,
  3. partner states proven outside `gc.configs`.

LOAD-BEARING ASSESSMENT: very high. The remaining work on Step 1 is now only to
package those partner states into a finite `badStep` cycle and contradict
`WellFounded` via `not_acc_of_finite_cycle'`.

## Exploration 72

### Strategy
Complete the uniform-branch bypass in the live theorem by packaging the partner
orbit into an actual `badStep` 8-cycle and routing `goodCycle_gives_blocked_q4_cycle`
around the V2 certificate on `gc.uniformDirection`.

### Outcome
SUCCEEDED

### Concrete Artifacts

LIVE-PATH RESULTS:
- [LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean)
  now contains:
  - `partnerIdx_next3_of_uniform_len8`
  - `uniformCW_false`
  - `uniformCCW_false`
  - `uniformDirection_false`
- In
  [goodCycle_gives_blocked_q4_cycle](./lean/LeanMn/SmallN/LB2222.lean#L2892),
  the proof now branches on `gc.uniformDirection` before using
  `gc_encoded_blockedV2`.

VERIFICATION:
- `lake build LeanMn.SmallN.LB2222` succeeds.

REPRESENTATIONS:
- The heavy V2 certificate is no longer on the live path for uniform sweeps.
- Uniform-direction good cycles are now killed entirely by the direct
  partner/badStep orbit argument.
- The only remaining branch that still depends on the heavy certificate is the
  mixed-direction branch.

LOAD-BEARING ASSESSMENT: extremely high. This completes the plan’s first two
phases in the live file. The next work is purely Step 3: remove the certificate
from the mixed branch.

## Exploration 73

### Strategy
Start the mixed-branch elimination by proving the first structural bridge
the `BinaryQ4Word` route needs on the live `GoodCycle` side: the extracted
mover word is a local no-stay word.

### Outcome
SUCCEEDED

### Concrete Artifacts

LIVE-PATH RESULT:
- [LB2222.lean](./lean/LeanMn/SmallN/LB2222.lean)
  now contains `gcWordFrom_localNoStay`.

VERIFICATION:
- `lake build LeanMn.SmallN.LB2222` succeeds.

REPRESENTATIONS:
- The live extracted mover word now carries the same local adjacency invariant
  the scratch `BinaryQ4Word` theorems expect.
- This is the first direct bridge from the actual `GoodCycle` to the symbolic
  mixed-branch classification route.

LOAD-BEARING ASSESSMENT: moderate but necessary. The next missing bridge for the
mixed branch is `SimpleWord4` of the extracted mover word; after that the
existing symbolic no-conflict theorems become available on the live path.
