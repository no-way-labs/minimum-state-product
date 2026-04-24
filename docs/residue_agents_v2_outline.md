# Residue Agents v2: Outline

**Central thesis:** In multi-agent LLM research, orchestration decisions—task framing, information topology, failure diagnosis, and cross-pollination timing—are the primary determinant of ensemble output quality, dominating model choice and agent count. The Mn theorem serves as a worked example.

---

## 1. Opening: The Productive Failure

Open with the n=9 wall, not the result. Four agents, ~35% of total compute, proving the obvious approach was wrong. Frame the paper's question immediately: *what makes the difference between an ensemble that gets stuck and one that breaks through?*

The answer this paper argues: orchestration. Not the agents. Not the models. The decisions about who works on what, who sees whose results, when to kill an approach, and how to frame a task.

State the Mn result in one paragraph as the concrete deliverable, then pivot: "The process that produced this result is the subject of this paper."

## 2. Setup (compressed)

### 2.1 The Problem
- Dijkstra's self-stabilizing token ring, bidirectional reading, central daemon
- Mn = minimum state product
- What was known: RFC constraint, Dijkstra's small solutions, nothing for n ≥ 5
- One paragraph. Point to companion paper for details.

### 2.2 The Architecture
- Hub-and-spoke: orchestrator (LLM) + human oversight → worker agents
- 10 agents, 2 model families (Claude, GPT), ~42 orchestrator explorations
- The Residue prompt: structured record-keeping without constraining reasoning
- Consumer subscriptions only (~$400/month)
- Key design choice: agents never see each other's work

### 2.3 The Result
- Mn = 4·3^(n-2) for n ≥ 9, Mn = 32·3^(n-4) for 4 ≤ n ≤ 8
- New proof techniques required (shadow cycles, palindromic entry conflict, good-targeting completion, CUP-2 tables, 4-layer elimination)
- Full proof in companion document

## 3. Four Orchestration Problems

This is the core of the paper. Each section presents a concrete problem the orchestrator faced, the decision made, the outcome, and the generalizable principle. Replace the chronological five-phase narrative with problem-oriented case studies.

### 3.1 Diagnosing False Negatives vs. Real Impossibility

**The problem:** RC declares n=8 UNSAT after searching 500 cycles across 10 orientations. Is the answer really impossible, or did we not look hard enough?

**The decision:** Orchestrator diagnoses insufficient budget (500 cycles ≪ candidate space), prescribes exhaustive sweep of all 35 orientations with larger budgets. Witness found at orientation 21.

**The counterfactual:** If RC had been the only agent, this would be a published false negative.

**Later instance:** Same diagnosis needed at n=9, but this time the negative is real—the 492-config binary trap is product-invariant, so no budget increase helps. The orchestrator must distinguish these two cases.

**Three signals the orchestrator used:**
1. Was the search budget exhaustive relative to the space? (n=8: no. n=9: yes, all 56 orientations.)
2. Is there a structural reason independent of budget? (n=9: the binary trap exists at every product.)
3. Did independent agents hit the same wall via different methods? (n=9: four agents, four methods, same failure.)

**Principle:** Never trust an impossibility claim without verifying search exhaustiveness. But also: recognize when exhaustive failure points to structural impossibility rather than insufficient effort.

### 3.2 Breaking Paradigm Lock-in

**The problem:** All agents use sweep-cycle pipelines. All fail at n=9. No agent spontaneously questions the sweep assumption.

**The decision:** Orchestrator creates AA with explicit "alternative architectures" framing. AA examines Dijkstra's Solution 3, discovers it uses a bounce cycle, identifies the sweep/bounce distinction.

**What didn't work:** Broad mandates. GPT ("computational innovation") and AA ("exploratory search") both defaulted to optimizing within the sweep paradigm before AA was explicitly redirected.

**The deeper issue:** This is the paper's most important negative finding about LLM capabilities. Current LLMs are excellent at optimizing within a framework. They do not spontaneously question the framework. Paradigm shifts required the orchestrator to create the conditions for heterodox thinking through deliberate task framing.

**The human's role:** The decision to maintain methodological diversity—not just task diversity—was the human's. The orchestrator implemented it, but the strategic insight that "shared methodology creates shared blind spots" came from human oversight.

**Principle:** Cognitive diversity requires methodological diversity. If all agents share a methodology, no agent can diagnose that methodology as the problem. At least one agent must be framed to question the approach itself.

### 3.3 Information Topology and Independent Discovery

**The problem:** How much should agents know about each other's work?

**The design choice:** Hub-and-spoke. Agents see only what the orchestrator forwards.

**The payoff:** CLB (upper bound, "blue-sky thinking") and GLB (lower bound, automata minimization) independently identify (2,3,...,3,2) as the critical state vector. Neither knows the other exists. The convergence is genuine—both arrive at the same object from opposite mathematical directions.

**What this means:** The finding is structurally forced by the problem, not an artifact of a particular approach path. This provides confidence that the result is "natural." An open-forum design would have destroyed this evidence—the second agent to arrive would have been influenced by the first.

**The cost:** Cross-pollination is slow. The orchestrator must manually recognize when A's output is relevant to B and transfer the right excerpts. Missed connections are invisible (you don't know what you didn't forward). CLB's formulas forwarded to CUP enabled the universal tables; GLB's edge-triple lemma forwarded to CIC enabled the 4-layer proof. Both transfers required the orchestrator to recognize cross-domain relevance.

**Principle:** Hub-and-spoke enables genuine independence (valuable for confidence in results) at the cost of cross-pollination speed (expensive in time). The tradeoff is worth it when you need to know whether a finding is robust. It's not worth it when speed of iteration matters more than independence.

**Open design question:** A hybrid—hub-and-spoke for working process, shared read-only bulletin board for established results—might capture both benefits. This was not tested.

### 3.4 Task Framing as the Primary Lever

**The problem:** Same base model, same problem, wildly different outputs depending on how the task is framed.

**Evidence:**
- CLB: "blue-sky lower bound thinking" → produced an *upper bound* construction (good-targeting completion). The freedom to ignore the nominal direction was essential.
- AA: "alternative architectures" → produced the paradigm shift. Specific enough to direct attention, open enough to allow surprise.
- RC: "systematic exhaustive search" → produced definitive negative results. Valuable, but could never have produced a paradigm shift.
- CUP: "construct universal convergence proof" → succeeded where multiple prior agents failed, because the framing specified the *type* of result needed, not the technique.

**The spectrum:** Overly specific framing constrains creativity (agent executes rather than invents). Overly broad framing produces unfocused work (agent explores randomly). The orchestrator's skill in finding the productive middle is perhaps the most important and least formalizable aspect of the method.

**Principle:** Frame cognitive roles, not tasks. "Think about lower bounds structurally" ≠ "prove Mn ≥ X." The former invites invention; the latter constrains to known techniques.

## 4. The Error Regime

### 4.1 Error Catalog

Expand Table 2 from the original paper. For each error:
- What was claimed
- Who claimed it
- How it was detected (self-correction / cross-agent / orchestrator)
- Time to detection
- Downstream impact (did other agents build on the false claim?)

| Claim | Agent | Detection | Mechanism | Latency | Impact |
|-------|-------|-----------|-----------|---------|--------|
| n=8 UNSAT | RC | Orchestrator | Budget analysis | Same exploration | Low (caught early) |
| Quaternary necessity | TC | TC (self) | Counterexample (Sol 3) | Same session | Low |
| Mn = 32·3^(n-4) ∀n | Ensemble | RC (exhaustive) | n=9 wall | ~4 explorations | High (paradigm shift) |
| MNU universal | CBS | CIC | n=4 counterexample | Cross-session | Medium |
| UBO theorem | CBS | CBS (self) | Full-context check | Same session | Medium (approach abandoned) |
| M9 = 13,122 | AA, RC | CLB | Better construction | ~2 explorations | High (new target) |
| Tmid(2,1,1) → 0 | CUP | CUP (self) | Refire analysis failure | Same session | Low (single entry revised) |

### 4.2 Patterns

- Every agent produced at least one incorrect claim
- Three detection mechanisms: self-correction, cross-agent, orchestrator diagnosis
- No ensemble-verified claim later proved incorrect (in this project—not a general guarantee)
- Overclaiming universality is the dominant error mode: agents generalize from partial evidence
- Premature negative declarations are the second most common: agents conclude impossibility from limited search

### 4.3 What Would Ensemble Failure Look Like?

The paper should address this honestly. If two agents independently verify a false claim, the ensemble could converge on a wrong answer with high confidence. The n=8 near-miss illustrates the risk. Mitigation: computational verification as a backstop (the companion paper's scripts check every claim exhaustively for small n).

## 5. Where the Human Was Irreplaceable

Be precise about this. The human did not prove theorems, write code, or conduct searches. The human:

1. **Made the blue-sky framing decision.** When an agent session was available, the human chose "blue-sky lower bound thinking" over more constrained options. This produced the breakthrough. Could an LLM orchestrator have made this call? Maybe—but the decision required recognizing that the project was stuck in a local optimum and that unconstrained exploration was worth the risk of wasted compute.

2. **Maintained model diversity.** The human chose to use both Claude and GPT even when sufficient credits existed on one platform. The reasoning: different training regimes might produce genuine cognitive diversity. Whether this mattered is an open question (task assignment and model choice were confounded).

3. **Recognized when to redirect after Phase 2.** Four agents failing at n=9 with different methods constituted strong evidence that the approach was wrong. The human's judgment that this merited a strategic pivot (not just more compute) shaped the rest of the project.

4. **Provided oversight and course correction.** Reading orchestrator logs, catching when the orchestrator missed a connection, occasionally suggesting a fresh agent on a subproblem.

**The honest question:** Could a fully automated system replicate these decisions? The orchestrator (itself an LLM) handled most strategic calls. The human's interventions were few but load-bearing. The answer is probably "not yet, but the gap is smaller than expected."

## 6. Design Space and Comparison

### 6.1 Polymath Comparison (expanded)

Not a passing analogy—a serious design-space analysis.

| Dimension | Polymath | Residue Agents |
|-----------|----------|----------------|
| Information topology | Open forum | Hub-and-spoke |
| Participant diversity | Genuine (different humans) | Thin (2 model families, differentiated by framing) |
| Quality control | Reputation, social norms | Orchestrator judgment, computational verification |
| Paradigm shifts | Any participant can post "has anyone tried X?" | Requires orchestrator to create conditions |
| Independence claims | Hard to verify (participants read each other) | Strong (agents cannot communicate) |
| Coordination cost | Forum management, thread structure | Orchestrator bottleneck, manual cross-pollination |

### 6.2 What a Deliberately Polymath-Style LLM System Would Need

- Substitute for reputation/taste: agents must filter signal from noise without social mechanisms
- Wider model diversity: not just Claude/GPT but genuinely different architectures
- A forum curation mechanism (which is basically the orchestrator under a different name)
- Solution to herding: preventing agents from latching onto the most recent/detailed post

### 6.3 Other LLM Math Systems

AlphaProof, LeanDojo, etc.—one paragraph each, focused on the structural differences (bounded vs. open-ended problem space, single system vs. ensemble, formal vs. human-readable proofs). Don't belabor this.

## 7. Limitations and Open Questions

### 7.1 Limitations
- Single case study, single problem, specific model versions
- Human contribution was load-bearing despite "oversight" framing
- No formal verification (human-readable proofs + computational scripts, not Lean/Coq)
- Orchestration principles are hypotheses from one project, not established general claims
- Task assignment and model choice were confounded—can't separate their effects

### 7.2 Open Questions
- Does the method scale to problems requiring deep sequential reasoning with no computational foothold?
- Can the orchestrator role be fully automated? (Evidence: mostly yes, but the human's few interventions were at critical junctures)
- What is the right information topology? (Hub-and-spoke vs. open forum vs. hybrid)
- Does genuine model diversity (beyond Claude/GPT) improve ensemble quality?
- How do you calibrate confidence in ensemble-verified claims?

## 8. Conclusion

Short. The main contribution is not the Mn theorem (that's the companion paper). The main contribution is a documented case study showing that orchestration quality dominates model quality in multi-agent LLM research, with specific, replicable principles: diagnose false negatives carefully, break paradigm lock-in through deliberate methodological diversity, use information topology to enable independent verification, and frame cognitive roles rather than tasks.

---

## Appendix A: The Mn Theorem (summary)

One-page summary of the result with pointer to companion document. Enough math for readers to understand what was proved, not enough to constitute the proof.

## Appendix B: Agent Session Index

Compressed from original Table 3. Add: which agents made load-bearing contributions vs. supporting computation.

## Appendix C: Error Catalog (full)

Expanded version of Section 4.1 table with all known errors, detection mechanisms, and timing.

---

## Notes on Cuts from v1

Removed or drastically compressed:
- Five-phase chronological narrative → replaced by four problem-oriented case studies
- Agent taxonomy table → folded into relevant case studies
- Section 5 (mathematical inventions) → moved to companion paper, one-paragraph summary here
- AlphaProof/LeanDojo comparison → one paragraph
- Section 7 (orchestration principles as list) → integrated into case studies as evidence-based claims
- Appendix B (worker log excerpts) → cut entirely or move to supplementary materials
- Full discovery narrative detail (exploration numbers, script names, orientation counts) → supplementary
