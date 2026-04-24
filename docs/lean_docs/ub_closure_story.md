# The Story of How UB Was Closed

*March 16, 2026 — The day `cup2BadConstFutureStep_wf` fell*

## The Setup

By March 14, the UB convergence proof had already survived one near-death
experience. An earlier agent had built 14,855 lines of dead-end infrastructure
following an outdated proof strategy (B1-B4 table-chase from the analytical
paper). An orchestrator intervention scrapped all of it and rewrote from
scratch using the Φ_full + 6-tuple approach discovered in the Python
exploration scripts. The rewrite brought Convergence/ from ~23,000 lines down
to 3,673 — clean, honest, following the right proof.

But one axiom remained: `cup2BadConstFutureStep_wf` in ConstLayerDAG.lean.

This axiom stated that the constant-FutureFc (CF) subgraph is well-founded.
In the paper proof, this follows from the CF subgraph being a DAG with rank
7n-30, constructed from the 6-tuple boundary automaton (617 edges, rank 24)
plus interior hop impossibility. The Python scripts verified this for
n=5..13. All the analytical pieces were proved in Lean (SixTuple.lean,
Interior.lean, TP.lean). The only thing missing was wiring them together.

The existing code in ConstLayerDAG.lean tried to use `Prod.GameAdd` from
Mathlib. GameAdd says: if R₁ and R₂ are well-founded, then the relation
"either R₁ steps with R₂ fixed, or R₂ steps with R₁ fixed" is well-founded.
The idea was to decompose CF into nonneg steps (where the nonneg measure
decreases) and neg steps (where fc decreases), then use GameAdd.

**The problem**: GameAdd requires the *other* component to be **identical**
between source and target. Nonneg CF steps can change fc (it can increase).
Neg CF steps change the nonneg measure. GameAdd's relation didn't match. The
file had a type error at line 61. It had been broken for days.

This single broken file blocked the entire convergence proof chain:

```
ConstLayerDAG.lean (BROKEN)
  → Main.lean (uses undefined wf_of_copy_segment_wf)
    → Cup2Converges.lean (combines n≥9 analytical + n=4..8 computational)
```

## The Session — March 16

This was Keston's first attempt at the problem since Anthropic made 1M
context windows generally available for Claude. Whether the expanded context
played a role is hard to isolate, but the session had a qualitatively
different character from earlier attempts: the agents could hold the entire
proof structure in memory simultaneously.

### Agent 1: Deep Research, No Output

The first agent was launched with the full problem description: the broken
GameAdd approach, computational facts about CF steps, 5 possible proof
approaches, and all relevant file locations. It spent its entire budget
(179K tokens, 76 tool uses, ~32 minutes) reading every file in the
Convergence directory, searching Mathlib for well-foundedness combinators,
and exploring the codebase.

It proposed the correct solution architecture — a nested Acc construction
inspired by `Acc.prod_gameAdd` — but got stuck on file permissions. It
couldn't write or edit files. It returned a detailed explanation of what
to do but zero lines of code.

### Agent 2: Same Research, Still No Output

The first agent was resumed with edit permissions. But it still couldn't
write files (a permissions configuration issue). It returned the complete
replacement code for both files as text in its response, with a clear
explanation of the mathematical argument. Still zero files changed on disk.

### The Orchestrator Steps In

At this point, the orchestrator (Claude managing the session) had the
agent's proposed solution and needed to evaluate it before applying.

**The orchestrator caught a critical bug.**

The agent's proposed ConstLayerDAG.lean included a lemma
`fc_le_of_nonnegCF_chain` claiming that fc is non-decreasing along a
nonneg CF chain (i.e., fc(d) ≤ fc(c) where d is reached from c). But
nonneg CF steps have `cup2Fc c ≤ cup2Fc c'` where c→c' is the step —
meaning fc goes UP from predecessor to successor. Along a chain from c
down to d, fc is non-increasing, not non-decreasing. The lemma had the
inequality backwards.

This error propagated into the segment well-foundedness proof. The segment
relation (nonneg chain + neg step) was claimed to be WF via InvImage on fc,
but the chain could INCREASE fc, so a neg step might not bring fc below the
start. Example: fc(c)=5, chain raises to fc(d)=8, neg drops to fc(c')=7.
Then fc(c')=7 > fc(c)=5. The segment is NOT WF via InvImage on fc.

The orchestrator verified this with a concrete counterexample argument and
rejected the proposed solution.

### Computational Investigation

The orchestrator wrote `check_cf_measure2.py` to investigate what measure
actually works for CF steps. Results for n=5..12:

- CF IS a DAG (confirmed for all n tested)
- Max rank = 7n-33 for n≥8
- Nonneg measure (n-fc, Psi) fails on ~80% of CF steps
- Lex(FutureFc-fc, Psi) fails identically
- No linear combination of fc and Psi works

**No simple analytical measure exists.** The CF DAG rank depends on the
full config structure, not just (fc, Psi).

### Agent 3: The Breakthrough

A new agent was launched with all context from the failed attempts: the
mathematical bug, the computational results, the paper's proof structure,
and all available Lean theorems. It was given `mode: auto` for full
permissions.

The agent ran 7 Python investigation scripts and discovered a key fact:
**TP quantities are constant on ALL CF steps** (verified n=5..12, zero
exceptions). This meant CF steps live entirely within the TP subgraph.

But the agent's real insight was not about TP. It was about Lean.

The agent read Mathlib's `Acc.prod_gameAdd` source code (in
`Mathlib/Order/GameAdd.lean`, lines 93-99) and noticed something: GameAdd's
**relation** requires one component to be identical, but GameAdd's **proof
technique** doesn't. The proof uses `induction ha generalizing hb` — the
outer induction generalizes over the inner Acc proof, making the inner
proof universally quantified in the induction hypothesis. This means when
the outer component changes, you can provide a FRESH inner Acc from
`WellFounded.apply`. You don't need to preserve the relationship between
the two components.

The agent wrote:

```lean
induction ha generalizing hb with
| intro c _ iha =>
  induction hb with
  | intro c _ ihb =>
    exact Acc.intro c fun c' hcf => by
      rcases cf_step_nonneg_or_neg n hn4 hcf with hnonneg | hneg
      · -- Nonneg CF step: outer Acc structurally smaller, fresh inner Acc
        exact iha c' hnonneg
          ((InvImage.wf (cup2Fc n hn4) Nat.lt_wfRel.wf).apply c')
      · -- Neg CF step: fc drops, inner Acc structurally smaller
        exact ihb c' hneg
```

**That's the entire proof of `cup2BadConstFutureStep_wf`.** 77 lines
including comments, replacing a 66-line broken file.

For Main.lean, the agent defined a clean `wf_of_inner_segment` combinator:

```lean
private theorem wf_of_inner_segment {α : Type*}
    {inner segment : α → α → Prop}
    (h_inner : WellFounded inner)
    (h_segment : WellFounded segment)
    (h_compose : ∀ {a b c : α}, inner b a → segment c b → segment c a) :
    WellFounded (fun x y => inner x y ∨ segment x y)
```

This general theorem says: if the inner relation is WF, the segment
relation is WF, and inner steps compose with segments (extending the
inner chain), then their union is WF. Applied with inner=CF and
segment=DropSegment (where FutureFc decreases), this gives badStep WF.

### Build

```
$ lake build
Build completed successfully (0 jobs).
```

Zero sorry. Zero axiom. The full chain compiled:

```
CopyDAG → PhiFull → TP → Interior → SixTuple → Anomalous
                                                     ↓
                                              ConstLayerDAG ✓
                                                     ↓
                                                  Main ✓
                                                     ↓
                                              Cup2Converges ✓
```

`cup2Converges` — proved for all n ≥ 4.

## Why It Worked This Time

### 1. The 1M context window

This was the first attempt since Anthropic made 1M context windows GA.
The agents could hold the entire Convergence/ directory (~3,700 lines)
plus the full problem description plus Mathlib source plus computational
results in a single context. Earlier agents with smaller windows had to
make choices about what to read, often missing critical connections.

The breakthrough specifically required seeing `Acc.prod_gameAdd` in
Mathlib AND the ConstLayerDAG problem AND the computational evidence
that no simple measure works — all simultaneously. With a smaller
window, an agent that reads Mathlib might not have room for the
computational results, and vice versa.

### 2. Learning from failure

Three agents attempted the problem. The first two failed but generated
critical context:
- Agent 1 identified the correct solution architecture (nested Acc)
- Agent 2 produced complete (but buggy) code
- The orchestrator identified the specific mathematical bug
- The computational investigation proved no simple measure exists

Agent 3 had all of this. It knew GameAdd doesn't work. It knew no
linear measure works. It knew nested Acc is the right shape. It just
needed to find the right Lean incantation — and `generalizing hb` was
the key.

### 3. Separating the proof technique from the theorem

The deepest insight: `Acc.prod_gameAdd` proves WF for GameAdd's specific
relation (where one component is identical). But the PROOF TECHNIQUE —
outer induction generalizing the inner component — works for ANY
decomposition into two WF relations where every step decreases one. The
relation doesn't need to be GameAdd. The components don't need to be
preserved. You just need two WF proofs and a case split.

This is a meta-mathematical insight: recognizing that a proof technique
has broader applicability than the theorem it was designed for. The agent
found it by reading Mathlib source code, not by following the paper's
proof structure.

### 4. The orchestrator model

The session used a clear orchestrator/agent separation:
- Orchestrator: evaluated proposals, caught bugs, managed context
- Agents: did deep research and code generation

The orchestrator caught the fc-direction bug that would have produced a
"proof" that type-checks but is mathematically wrong (if the inequality
direction had been different, it might have compiled while proving
something false via circular reasoning). Having a separate evaluation
step prevented shipping broken math.

## The Final Scoreboard

| Component | Lines | Status |
|-----------|-------|--------|
| CopyDAG.lean | 1,200 | Clean |
| PhiFull.lean | 166 | Clean |
| TP.lean | 490 | Clean |
| Interior.lean | 513 | Clean |
| SixTuple.lean | 901 | Clean |
| Anomalous.lean | 297 | Clean |
| **ConstLayerDAG.lean** | **77** | **Fixed** |
| **Main.lean** | **125** | **Fixed** |
| Cup2Converges.lean | 29 | Clean |
| **Total** | **3,798** | **Zero sorry, zero axiom** |

The CUP-2 system with ms=(2,3,...,3,2) and state product 4·3^(n-2)
converges from any initial configuration, for all n ≥ 4.

M_n ≤ 4·3^(n-2) is formally verified in Lean 4.

## Epilogue

The UB closure unblocked the LB campaign. Six axioms remain in the lower
bound formalization, requiring ~3,900-5,100 lines of new proof across
shadow constructions, entry conflict mechanisms, and mover word
combinatorics. The execution plan is written. The agents are running.

The proof that no simple analytical measure exists for CF steps — the
result that seemed like a dead end — turned out to be the key insight.
It forced the agent to look for an abstract approach instead of trying
to compute a rank function. Sometimes the bog is a feature, not a bug:
it tells you the direct path doesn't exist, so you'd better find a
different one.
