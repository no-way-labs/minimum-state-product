# Research Program: Is ∏mᵢ the Wrong Currency?

## Motivating hypothesis

The Knuth 1985 product-minimization problem asks for a lower bound on ∏mᵢ over valid self-stabilizing token rings. Forty years of attack on this bound have produced no uniform analytical result. The paper under discussion catalogs five families of standard invariants (flow-theoretic, ambient-topological, map-level, sheaf-cohomological, arithmetic) and diagnoses each as failing for a structurally distinct reason. The unifying observation offered — "the obstruction lives in the joint (C, µ) × detOf interaction" — is a diagnosis within the existing frame.

The conjecture of this program is that the frame itself is the obstruction. Specifically: ∏mᵢ is not the fundamental quantity that the self-stabilization dynamics constrains. It is an ambient aggregate that happens to track the fundamental quantity with some slack, and every attack on ∏mᵢ directly is fighting through that slack. The §7 failure pattern is consistent with this: each failed invariant is product-adjacent, and each fails for a reason that amounts to "does not see what the dynamics actually constrains."

If the hypothesis is correct, the research program is to identify the correct currency Q(system), prove a lower bound of the form Q ≥ q(n) using techniques that operate on Q natively, and then derive the product bound ∏mᵢ ≥ 2^{q(n)} or similar as a corollary via a counting or entropy argument. If the hypothesis is incorrect, the program will produce a clean diagnostic against itself: no candidate Q separates valid from sub-threshold with more margin than ∏mᵢ does, which is itself useful information and strengthens the case that ∏mᵢ is genuinely fundamental.

## Why the product is suspicious as a fundamental quantity

Three properties of ∏mᵢ suggest it is an ambient measure rather than a dynamical one.

**It is representation-dependent.** Adding an unused state to any processor increases mᵢ without changing the dynamics. The constraint mᵢ ≥ 2 is the only thing preventing trivial deflation of the product; there is no analogous constraint preventing inflation. A quantity that the dynamics fundamentally cared about would not be arbitrarily inflatable while leaving the dynamics fixed.

**It is insensitive to reachability.** ∏mᵢ counts |Config(m)|, the size of the ambient configuration space. A valid system's good cycle visits L ≪ ∏mᵢ configurations; the remainder are transient. The product does not distinguish a system whose good cycle visits 0.1% of the ambient space from one that visits 10%, even though these systems have very different dynamical structure.

**It is insensitive to rule-table information content.** Two systems with identical state-count vectors but very different rule tables (one with highly redundant entries, one with all-distinct entries) have the same product. A quantity tracking the system's intrinsic complexity should vary with rule-table content.

These are not proofs that ∏mᵢ is the wrong currency. They are reasons to suspect it might be, which is enough to motivate looking.

## The §7 failure pattern, re-read

The paper's §7 catalog, re-read through this hypothesis:

- **Ambient topology** fails because it is (n, L)-parametrized. But (n, L)-parametrization means the invariants see ambient structure; they do not see m beyond dimension counts. If the fundamental quantity is L-based, ambient-topological invariants are not wrong to be (n, L)-parametrized — they are looking at the right things, but the program is trying to extract a bound on ∏mᵢ from them, and ∏mᵢ is not where their signal lives.

- **Map-level** fails because no valid f exists at sub-threshold. But the good cycle C and its mover sequence µ are defined on candidate records regardless of whether f exists. A map-level invariant computed on (C, µ) alone, not on f, would not have this obstruction.

- **Sheaves** fail because they are local-cellular and the obstruction is global. But globality is a feature of dynamical quantities (convergence is global), not of ambient-space quantities. This is consistent with the fundamental quantity being dynamical rather than ambient.

- **Arithmetic** fails because the only separator extracted is log Bₙ - log ∏m, the threshold condition. The regression tautology is exactly what you get when you try to find a feature that predicts validity from ∏m-adjacent features, and the fundamental quantity is not in the feature space.

The pattern is: each family fails for a reason that would be a feature, not a bug, if the program were attacking the correct currency. This is circumstantial but worth noting — it is the shape of evidence you would expect if the reframing hypothesis is correct.

## Candidate currencies

Four candidate fundamental quantities are worth investigating, in rough order of how natural each is.

### Candidate 1: Good-cycle length L

L = |C|, the number of distinct configurations on the good cycle.

**Why it is plausibly fundamental.** L is a direct property of the dynamics, independent of ambient state-count choices. Fairness requires every position to fire at least once per cycle, so L ≥ n. Convergence from arbitrary bad configurations requires a certain amount of phase information in the cycle structure, which plausibly forces L to grow faster than linearly. The paper's measured L values support this: CLB has L = n² - 2n + 8, CUP-2 has L = (n+2)(n+3)/2 - 5, and the small-n absorbers have L in {18, 35, 52, 55} at n in {5, 6, 7, 8}, all roughly quadratic.

**Conjectural form of the bound.** L(valid) ≥ c·n² for some universal constant c and all n ≥ n₀. Best fit from the paper's data suggests c ≈ 1/2 to 1, with CUP-2 approximately saturating c = 1/2 and CLB approximately saturating c = 1.

**How it forces the product bound.** A valid good cycle visits L configurations, each of which is a point in Config(m). Fairness requires every position to fire, and convergence requires a certain amount of state diversity per position along the cycle. A counting argument of the form "if position i takes kᵢ distinct values along the cycle, then L ≥ f(k₁, ..., kₙ)" together with "kᵢ ≤ mᵢ" would convert a lower bound on L into a lower bound on ∏mᵢ. The exact counting argument is the thing to find.

**Why the paper did not emphasize this.** The paper treats L as a statistic of individual witness families, not as a fundamental quantity. It reports L for CLB, CUP-2, and absorber witnesses but does not formulate a cross-family L lower bound or attempt to derive the product bound from an L bound.

### Candidate 2: Determined-context count κ

For a good cycle C with mover sequence µ on state vector m, let κ(C) be the number of distinct (i, a, b, c) tuples such that at some step k of C, position i is the mover, cₖ(i-1) = a, cₖ(i) = b, cₖ(i+1) = c. This counts the detOf-determined entries in the rule table.

**Why it is plausibly fundamental.** κ is a direct measure of how much of the rule table is pinned by the good cycle versus how much is free. Convergence from bad configurations depends on the free entries, and the sink-kernel monotonicity observation (§6.5) is precisely a statement about how constraints on free entries propagate. A bound of the form "if κ < g(n), then some bad configuration has no forced path to the good cycle" would be a direct convergence argument.

**Conjectural form of the bound.** κ(valid) ≥ g(n) for some g growing at least polynomially. The exact form would need to be fit from data.

**How it forces the product bound.** More determined contexts require more state diversity at the three positions involved, which pushes the relevant mᵢ up. Again, a counting argument is needed.

**Relation to Axis C.** The sink-kernel monotonicity observation is a κ-adjacent statement: SK(detOf) ⊆ SK(f) for any extension f, and SK(f) = ∅ is required for validity. If κ is the fundamental quantity, then Axis C is already a currency-reframed detector — it is checking whether the determined contexts are numerous and well-connected enough to force every bad configuration into the good cycle. The uniform Axis C statement (Conjecture 20) might be most naturally proved in κ-native language.

### Candidate 3: Cycle entropy H

Several entropy-flavored quantities are worth testing.

- **Per-position entropy:** for each position i, let pᵢ(v) be the fraction of steps in C at which position i holds value v. Let Hᵢ = -Σᵥ pᵢ(v) log pᵢ(v). Define H_avg = (1/n) Σᵢ Hᵢ and H_total = Σᵢ Hᵢ.
- **Mover entropy:** let q(i) be the fraction of steps at which position i is the mover. Let H_mover = -Σᵢ q(i) log q(i).
- **Transition entropy:** for each position i, compute the entropy of the transition distribution (cₖ(i), cₖ₊₁(i)) over steps k. Average or sum across positions.
- **Joint entropy:** the entropy of the distribution of (i-1, i, i+1) value triples across cycle steps.

**Why plausibly fundamental.** Entropy is the natural measure of information content of the cycle, and information content is what convergence from arbitrary bad configurations must overcome. A system with low cycle entropy has little "phase information" to distinguish configurations, which should make convergence harder to achieve.

**Conjectural form of the bound.** H(valid) ≥ h(n) for some entropy lower bound h(n). The natural scaling is h(n) = Θ(n log 3) if the ternary-strip family saturates, since the strip's good-cycle configurations use ≈ n ternary positions with roughly-uniform distribution.

**How it forces the product bound.** ∏mᵢ ≥ 2^{H_total} for any distribution supported on Config(m) via standard max-entropy bounds. If H_total ≥ h(n), then ∏mᵢ ≥ 2^{h(n)}, and for h(n) = (n-2) log 3 this gives ∏mᵢ ≥ 3^{n-2}, which is within a factor of 4 of the conjectured bound. The factor of 4 would come from the binary endpoints contributing 2 bits that the entropy of the ternary-dominated interior does not account for.

**Why this is the most speculative of the three.** Entropy bounds on combinatorial objects are powerful but require the right choice of distribution and the right inequality, and there is no obvious reason a priori why the good-cycle distribution should have high entropy. The intuition is that convergence requires distinguishability, and distinguishability requires entropy, but making this precise is non-trivial.

### Candidate 4: Something unnamed

It is entirely possible that none of L, κ, or H is the right currency, and the correct quantity is some combination or something not yet identified. The program should not commit to one of the three in advance; the Phase 1 empirical work (below) is designed to discover which, if any, separates validly.

## Phase 1: Empirical separation test

**Goal.** Determine whether any candidate currency separates the 97-record corpus with more margin than ∏mᵢ does, and whether any of them saturates a clean lower-bound curve on the valid side.

**Method.** The paper's existing corpus provides valid witnesses (10 records across absorber and ternary-strip families at n ∈ {5, ..., 10}) and sub-threshold candidates (87 records at n ∈ {5, ..., 9}). For each record, compute:

- L (good cycle length; already available)
- κ (determined context count; computable from the stored cycle and detOf)
- Hᵢ, H_avg, H_total (per-position entropies; computable from the cycle)
- H_mover (mover entropy; computable from µ)
- H_joint (joint triple entropy; computable from the cycle and positions)
- Secondary ratios: L/n, L/n², κ/L, κ/(n·L), H_total/log(∏mᵢ), H_total/(n log 3)

For each quantity Q, plot Q against n on the valid side and on the sub-threshold side. Record:

- Does Q separate valid from sub-threshold? (Any overlap in Q-values at the same n?)
- Does Q saturate on the valid side? (Do valid witnesses at each n cluster near a single Q-value, or spread widely?)
- What does Q/f(n) look like, for candidate normalizations f?
- If valid witnesses saturate Q at Q(n) = q(n), is q(n) a clean function of n?

**Expected outcomes and their interpretations.**

1. *Some Q separates more cleanly than ∏mᵢ, and valid witnesses saturate it.* This is the success case. The currency reframing is probably correct; promote to Phase 2.

2. *Some Q separates more cleanly than ∏mᵢ, but valid witnesses do not saturate cleanly.* Q is correlated with the fundamental quantity but is not exactly it; look for transformations or related quantities.

3. *No Q separates more cleanly than ∏mᵢ, and valid witnesses saturate ∏mᵢ tightly.* Evidence against the reframing hypothesis; ∏mᵢ is probably fundamental after all, or the correct currency is not in the tested family. The §7 obstruction is likely correctly framed.

4. *No Q separates at all, including ∏mᵢ.* Something is wrong with the corpus or the computation; re-audit before concluding.

**Runtime.** This is one day of work for a researcher with the corpus in hand. The quantities are all O(|C|·n) to compute per record; the corpus is small; no LP or enumeration is needed.

**Deliverable.** A table and a plot per candidate Q, and a written interpretation. If the empirical work is inconclusive (outcome 2 or partial outcome 1), Phase 1 iterates on additional candidate currencies before committing to Phase 2.

## Phase 2: Structural derivation of the chosen currency's lower bound

**Conditional on Phase 1 identifying a clean currency Q, prove Q(valid system) ≥ q(n) for all n ≥ n₀.**

The shape of this proof depends on which Q is selected. Three archetypes:

**If Q = L.** The proof is a combinatorial argument on good-cycle structure. Fairness forces every position to fire at least once per cycle, so L ≥ n. Convergence forces additional structure: every configuration in NG must have a forced path to C. The argument to find is one that converts "every NG configuration forced into C" into a quantitative lower bound on how many distinct configurations C must contain. One candidate: a counting argument on the forced-NG graph's in-degree into C. If every NG configuration has at most k distinct C-configurations as forced successors, and |NG| = ∏mᵢ - L, then L ≥ (∏mᵢ - L)/k·(convergence-steps bound). Making this precise requires the right formulation of "convergence steps" as a cycle-length-forcing constraint.

**If Q = κ.** The proof is an information-flow argument on the rule table. Each determined entry in detOf fixes one rule-table cell; the free cells must be completable such that SK(f) = ∅. If κ is too small, some NG configuration is forced into a subset with no path to C, violating convergence. Axis C's monotonicity is a bound of this shape restricted to the corpus; the uniform version would be a κ lower bound. This is the direction most continuous with the paper's existing machinery.

**If Q = H_total or similar entropy.** The proof is an information-theoretic inequality. Convergence from |Config(m)| - L bad configurations to L good configurations requires the cycle to "have enough distinguishing information" to distinguish configurations; make this precise via a mutual-information argument between the cycle's state sequence and the position of the privileged processor. The specific inequality to find is one that forces H ≥ h(n) from the six validity properties.

In each case, the core mathematical work is finding the inequality that converts a validity property (probably convergence) into a quantitative bound on Q. The §7 catalog has tested this conversion for ∏mᵢ and failed; the bet is that the conversion is more natural for the correct Q.

## Phase 3: Derivation of the product bound from the Q bound

**Given Q(valid) ≥ q(n), derive ∏mᵢ ≥ F(q(n)).**

This is the "counting argument" step that makes the reframing produce a conventional product bound. Three archetypes matching Phase 2:

**From L ≥ c·n².** If the good cycle has L distinct configurations, and each configuration is a point in Config(m) of size ∏mᵢ, then L ≤ ∏mᵢ trivially. The non-trivial bound comes from "how much of Config(m) can L configurations occupy while maintaining the good-cycle structure"; this requires a fairness-derived density argument. The target inequality is probably ∏mᵢ ≥ L · (some factor depending on reachability density).

**From κ ≥ g(n).** If the determined-context count is κ, then the cycle visits κ distinct (position, context) pairs. Each position contributes at most mᵢ₋₁ · mᵢ · mᵢ₊₁ distinct contexts, so κ ≤ Σᵢ mᵢ₋₁ · mᵢ · mᵢ₊₁. An AM-GM-style lower bound on ∏mᵢ from Σᵢ mᵢ₋₁ · mᵢ · mᵢ₊₁ ≥ κ gives the product bound; the exact form requires optimizing over state-count vectors.

**From H_total ≥ h(n).** Standard max-entropy: if a distribution on Config(m) has entropy H, then |Config(m)| ≥ 2^H, hence ∏mᵢ ≥ 2^{h(n)}. This is the cleanest derivation if H is the right currency, because the inequality is textbook.

## Phase 4: Comparison to existing results and conjectures

**Check consistency.** The derived product bound F(q(n)) should match the paper's Conjecture 9 bound Mₙ ≥ 4·3^{n-2} at n ≥ 9. If it does not, either the currency is wrong, the bound is off by a constant, or the conjecture is off by a constant.

**Check small-n regime.** The derived bound should recover or supersede the small-n exact values at n ∈ {5, ..., 8}, where Mₙ = 32·3^{n-4}. If the reframed bound is looser at small n, it may still be correct asymptotically but not sharp; this is acceptable for a conjecture about large n.

**Check relation to ARG.** ARG's 1985 LCM bound covers the non-adjacent-binary sub-family. If Q is the right currency, ARG's bound should be a special case or shadow of the Q bound. If it is not, the reframing has a scope mismatch to understand.

**Check extension to the Knuth-relaxed convention.** The paper's §8.8 transport-to-relaxed question asks whether the connected-model bounds transport to the relaxed model. If Q is defined on cycle structure that is shared between the two models, the Q bound might transport more naturally than the product bound does. This would be a significant bonus outcome.

## Phase 5: Verification and proof

**If Phases 2-3 produce a candidate proof, formalize and verify.**

- Re-run the corpus against the derived bound: does it hold on every record?
- Extend to larger n with Python verification: does the bound hold at n = 10, 11, 12, ...?
- If the proof is clean, formalize in Lean alongside the existing upper-bound machinery.
- If the proof has gaps or conditional steps, identify them as sub-problems for further work.

## Risks and failure modes

**The reframing could be wrong.** None of L, κ, H separates the corpus more cleanly than ∏mᵢ. The hypothesis fails. This is a legitimate empirical outcome and would be publishable as a null result if carefully done: "we tested the reframing hypothesis and found that ∏mᵢ is the tightest separator on the corpus, consistent with the product being genuinely fundamental."

**The correct currency could be none of the candidates.** The Phase 1 feature space is L, κ, H variants, and their ratios. The right currency could be something combinatorial that none of these captures — a cycle-invariant from algebraic combinatorics, a spectral quantity of the forced-NG graph, a Möbius-function computation on a poset derived from the cycle. Phase 1 should include a "what else might Q be" brainstorming step and not commit to the three listed.

**The bound could be right but unprovable via the current techniques.** Even if the currency is right, the conversion from "validity property" to "Q lower bound" (Phase 2) may still require techniques outside the paper's catalog. The reframing is necessary but not sufficient.

**Phase 2 could recapitulate §7.** If the proof of Q ≥ q(n) requires sheaves, Conley indices, or other invariants from §7, the reframing has only moved the obstruction, not resolved it. The test is whether Phase 2's proof uses techniques that would have failed on ∏mᵢ but succeed on Q — i.e., whether the currency change genuinely enables a new technique.

## What success looks like

A successful execution produces:

1. Phase 1 identifies Q* as the clean-separating currency, with a plot showing valid-side saturation and sub-threshold-side gap.
2. Phase 2 proves Q*(valid) ≥ q(n) via a natural argument that exploits the dynamical structure directly.
3. Phase 3 derives ∏mᵢ ≥ F(q(n)) matching Conjecture 9's asymptotics.
4. Phase 4 recovers ARG's bound as a special case and clarifies the transport-to-relaxed question.
5. Phase 5 verifies on extended corpus and formalizes in Lean.

The paper this produces is not "exact values of Mₙ at small n plus a conjecture for large n"; it is "the Knuth gap closes once you ask the right question, and the right question is a lower bound on Q*." That paper closes the forty-year-open problem. It also provides a template: self-stabilization lower bounds should be sought on dynamical currencies, not on ambient aggregates.

## What partial success looks like

If Phase 1 identifies Q* cleanly but Phase 2 stalls, the paper this produces is "the Knuth product gap is a shadow of a cleaner dynamical quantity Q*; the lower bound on Q* is the real problem." That paper does not close the problem but reshapes it, and the reshaping is itself a substantive contribution — it tells the next attacker where to look.

If Phase 1 finds nothing but the corpus work is careful and the candidates are well-motivated, the paper this produces is "we tested the reframing hypothesis against the stratified corpus and found ∏mᵢ is the tightest separator; this is evidence that the obstruction is genuinely in the joint (C, µ) × detOf interaction as previously diagnosed, not in the currency of the question." That paper is a targeted null result, which is useful for the field even if not headline-grabbing.

## What to do first

Start with Phase 1, specifically with L and κ on the 97-record corpus. These two quantities are the most natural, the cheapest to compute, and the ones most directly connected to the paper's existing machinery. Before investing in entropy variants or in Phase 2 proof attempts, check whether the simplest candidate currencies separate the data more cleanly than the product does. If L or κ work, the direction is set. If neither works, the program needs to either expand its candidate set or reconsider the hypothesis.

One day of work to answer whether the hypothesis survives first contact with the corpus. That is a cheap test of an idea that, if correct, would change the shape of a forty-year-open problem.
