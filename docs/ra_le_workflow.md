# RA/LE Workflow — Agent-Orchestrated Research and Engineering

## What this is

A workflow for attacking hard formalization problems using two specialized
agent roles and a human orchestrator. Developed during the lower bound proof
for self-stabilizing token rings (this project), but the pattern is general.

## The three roles

### RA (Research Agent)

Investigates mathematical questions computationally. Writes and runs Python
scripts. Does NOT write Lean or construct proofs.

**What RAs do:**
- Enumerate examples and counterexamples
- Verify conjectures computationally at multiple parameter sizes
- Characterize failure modes and edge cases
- Extract formulas and closed-form descriptions from data
- Disprove false claims before they waste PA/LE time

**What RAs produce:**
- Scripts with clear output and interpretation
- A verdict: "works 100%" or "fails at these cases" or "the mechanism is X"
- Computational evidence that feeds PA and LE work

**What RAs do NOT do:**
- Write formal proofs
- Construct proof arguments (that's PA work)
- Declare something proved (they declare things verified)

### PA (Proof Agent)

Invents proof arguments. Uses computation to guide reasoning but delivers
analytical proofs a mathematician would accept. Does NOT write Lean.

**What PAs do:**
- Take RA-verified claims and find the WHY behind them
- Construct step-by-step proof arguments with lemmas and justifications
- Identify the minimal hypotheses needed
- Resolve analytical gaps (the "verified but not proved" claims)

**What PAs produce:**
- A proof argument with: definitions, lemmas with proofs, main theorem
- Each step justified by reasoning, not by "checked computationally"
- Clear identification of any remaining gaps
- A spec detailed enough for an LE to translate into formal tactics

**What PAs do NOT do:**
- Just verify (that's RA work)
- Formalize in Lean (that's LE work)
- Accept "100% at n=5,7,9" as a proof

**The key prompt difference:**
- RA: "Check if X holds at n=5,7,9. Report counts."
- PA: "PROVE X. Use computation to guide reasoning, deliver an argument."

### LE (Lean Engineer)

Writes formal code — proofs, definitions, infrastructure. Works from PA specs,
not from open-ended investigation.

**What LEs do:**
- Create new files with type definitions and theorem statements
- Fill sorrys with proofs
- Wire existing theorems into new architectures
- Verify builds succeed

**What LEs produce:**
- Lean files that build clean
- Precise sorry annotations when they get stuck (what's needed, what was tried)
- Honest reports: "closed sorry-free" or "narrowed to X" or "stuck because Y"

**What LEs do NOT do:**
- Discover proof strategies (that's RA work)
- Investigate whether a mathematical claim is true (that's RA work)
- Spend time on approaches that haven't been computationally validated

## The orchestrator

The human (or a senior agent) manages the workflow:

- Decides what to investigate next
- Launches RAs and LEs with precise prompts
- Interprets RA results and decides whether to proceed or pivot
- Writes the LE prompt based on RA findings
- Maintains the sorry scoreboard and dependency graph
- Catches when work is becoming "stinky" (duct tape vs real progress)

## The loop

```
1. Identify a blocking problem (a sorry, an unknown, a design question)
2. Launch RA to investigate
3. RA reports: mechanism found / counterexample found / claim disproved
4. If mechanism found → write LE prompt with the spec
5. Launch LE to formalize
6. LE reports: sorry closed / narrowed / stuck
7. If stuck → back to step 2 with refined question
8. If closed → update scoreboard, pick next blocking problem
```

## When to use which

| Situation | Agent |
|---|---|
| "Does X work?" | RA |
| "Is this claim true?" | RA |
| "Why does this fail?" | RA |
| "Find me a formula for Y" | RA |
| "Write the Lean for X" | LE |
| "Fill this sorry" | LE |
| "Wire theorem A into file B" | LE |
| "Create a new type definition" | LE |
| "I tried X and got stuck at Y" | RA first (understand Y), then LE |

## Prompt discipline

### RA prompts should include:
- The precise mathematical question
- What's already known (hypotheses, previous results)
- What to test (parameter ranges, example families)
- What output format is needed (formula, counterexample, mechanism description)
- Available infrastructure (existing scripts, verifiers)

### LE prompts should include:
- The exact file and line number
- The exact theorem signature or sorry to fill
- The proof strategy (from RA findings)
- Available Lean infrastructure (what's imported, what lemmas exist)
- Build command to verify

### Bad prompts:
- "Figure out how to prove X" (too vague for LE, should be RA first)
- "Write some Lean code for this area" (no spec, no target)
- "Investigate everything about X" (too broad for RA, narrow the question)

## Parallelism

RAs and LEs can run in parallel when their work is independent:

- Multiple RAs investigating different questions simultaneously
- RA investigating question B while LE formalizes the answer to question A
- Multiple LEs working on independent files

Do NOT run in parallel when:
- LE depends on RA results (wait for RA)
- Two LEs modify the same file (sequential)
- RA question depends on LE's build result (sequential)

## The sorry scoreboard

Maintain a table of all sorrys with:

| Sorry | Location | What's needed | Blocker | Status |
|---|---|---|---|---|
| Name | File:line | Mathematical description | What blocks this | open/RA/LE/done |

Update after every RA report and LE completion. This is the source of truth
for what to work on next.

## Anti-patterns

### Sorry fission
One sorry splits into 2-3 sub-sorrys, each of which splits again. The count
goes up, not down.

**Diagnosis:** The proof strategy is wrong — you're cataloging cases instead of
finding mechanisms.

**Fix:** Stop LE work. Launch RA to find the real mechanism. Only resume LE when
RA gives a computationally verified strategy.

### Duct tape architecture
Workaround files, callback threading, bridge theorems that are themselves sorry'd.
The code compiles but the architecture is worse than before.

**Diagnosis:** You're solving import/dependency problems instead of math problems.

**Fix:** Step back. Ask: "is there a clean file that already does what I need?"
(PhaseExtractionClean was the answer in our case — sorry-free, importable, had
everything.)

### RA without validation
RA reports a mechanism but doesn't verify it exhaustively. LE spends hours
formalizing, then discovers counterexamples.

**Fix:** RAs must test at multiple parameter sizes (n=5,7,9 minimum). Report
exact counts: "X/Y cycles, 0 exceptions." If exceptions exist, characterize them.

### LE without spec
LE launches into a sorry with no RA-validated strategy. Gets stuck, adds more
sorrys, creates sub-problems.

**Fix:** Every LE prompt should include "the RA found: [mechanism]. Verified
[count]. The proof is: [step 1, step 2, step 3]." If you can't write this,
you need an RA first.

### Grinding past diminishing returns
The last 2 sorrys take longer than the first 5. Each attempt reveals more
complexity. The session becomes a war of attrition.

**Diagnosis:** You've hit a genuine mathematical difficulty, not a formalization
problem.

**Fix:** Document the precise state. Commit. Start fresh next session with the
hard problem clearly isolated. Don't throw more LEs at a problem that needs
rethinking.

## Session lifecycle

### Start of session
1. Read the sorry scoreboard and handoff doc
2. Identify the highest-leverage target (unblocks the most downstream work)
3. Check: is there an RA-validated strategy for this target?
4. If yes → launch LE
5. If no → launch RA

### During session
- Keep the sorry scoreboard updated
- Commit after each meaningful change (don't batch)
- When an approach fails, document WHY before pivoting
- When an RA finds something surprising, update the handoff doc

### End of session
1. Commit all work
2. Update the sorry scoreboard
3. Update the handoff doc with: what was done, what's next, what's blocked
4. Update memory with any corrections to prior understanding
5. The handoff doc should be self-contained — a new agent should be able to
   pick up where you left off without reading the full conversation

## Two modes of operation

### Mode 1: Orchestrator + sub-agents

The orchestrator (human or senior agent) spawns specialized sub-agents —
RA, PA, or LE — each with a narrow mandate. This is how session 2 of the
LB campaign worked.

**When to use:** Multiple independent problems to attack. The orchestrator
has context that no single agent should carry (the whole sorry graph, the
mathematical big picture, corrections from prior sessions). Sub-agents are
disposable: they do one job and report back.

**Shape of work:**
```
Orchestrator reads handoff doc + memory
  → spawns RA: "check if right²t fires adjacent in mixed case"
  → spawns LE: "fill sorry at NormalFormEC:498, strategy is X"
  → spawns PA: "prove the palindromic walk has CW/CCW structure"
Orchestrator interprets results, updates scoreboard, picks next target
```

**Strengths:** Parallelism. Clean separation of concerns. Each agent prompt
is precise and self-contained. Failed agents don't pollute the main context.

**Weaknesses:** The orchestrator carries all the synthesis burden. Sub-agents
can't course-correct when they discover the prompt's assumptions were wrong.
Context is lost between agents — each starts cold.

### Mode 2: Single agent, deliberate hat-switching

One agent does everything, but explicitly changes mode when the work demands
it. The agent announces which hat it's wearing and follows that hat's rules.

**When to use:** Deep sequential work where each step informs the next. The
problem requires tight feedback between investigation and formalization.
A single agent accumulates context that would be expensive to re-derive.

**Shape of work:**
```
Agent reads handoff doc + memory
[RA hat] "Let me check computationally whether the backward chain
          terminates before the boundary for n=9,11..."
          → writes and runs Python script
          → finds: terminates 98% of time, boundary hit only when
            left-sweep mover word appears
[PA hat] "The boundary case has a left-sweep mover word. Let me prove
          that this forces EC via a different mechanism..."
          → constructs analytical argument using the RA data
          → identifies: after the sweep, t sees (L_new, S, R_new) at
            step fR+1 and at step s. EC at t if fR+1 < s.
[LE hat] "Now I'll formalize the PA argument. The proof needs
          configVal_eq_of_noFire_between from fR+1 to s..."
          → writes Lean, compiles, fixes omega errors
          → closes the sorry or narrows to a precise sub-problem
[RA hat] "The sub-problem is whether fR+1 < s always holds.
          Let me check n=5..15..."
```

**The hat-switching rules:**

| Current hat | Switch to | When |
|---|---|---|
| RA | PA | Mechanism found, need analytical proof |
| RA | LE | Claim verified, formalization is mechanical |
| PA | RA | Analytical argument needs computational validation |
| PA | LE | Proof argument complete, ready for Lean |
| LE | RA | Stuck on a sorry, need to understand WHY |
| LE | PA | Know what's true but not why — need proof strategy |

**The critical discipline:** When wearing the RA hat, do NOT write Lean.
When wearing the LE hat, do NOT investigate open questions. When wearing
the PA hat, do NOT accept "verified at n=5,7,9" as a proof. The hats
enforce the same separation as Mode 1, but inside a single context window.

**Strengths:** Full context preserved across mode switches. The agent can
immediately use RA findings in LE work without a handoff doc. Tight
feedback loops — an LE discovery ("this omega fails because X") can
immediately trigger an RA investigation ("is X always true?").

**Weaknesses:** Risk of mode confusion — the agent starts "investigating"
while wearing the LE hat, or writes speculative Lean while wearing the
RA hat. Requires discipline. Single point of failure: if the agent goes
down a rabbit hole, all context is lost.

**Anti-pattern to watch for:** The agent stops announcing hat switches and
drifts into a hybrid mode where it's simultaneously guessing proof
strategies and writing Lean. This is the #1 failure mode. If you catch
yourself writing `sorry` without an RA-validated reason for what goes
there — stop, switch to RA hat, investigate.

### Choosing between modes

| Situation | Mode |
|---|---|
| 5+ independent sorrys to attack | Mode 1 (parallelize) |
| One deep sorry with unknown proof strategy | Mode 2 (tight feedback) |
| Mechanical translation of PA-proved claims | Mode 1 (LE sub-agent) |
| Exploring whether a claim is even true | Mode 2 (RA→PA→RA loop) |
| Fresh session, reading a handoff doc | Either (depends on sorry count) |
| Grinding on the last 2 hard sorrys | Mode 2 (need full context) |

---

## Why this works

The RA/PA/LE split enforces a discipline:

- **No speculative formalization.** You don't write Lean until you KNOW the
  proof works (RA verified it). This prevents sorry fission.

- **No unvalidated claims.** Every mechanism is tested at multiple sizes before
  anyone tries to formalize it. This catches false conjectures early.

- **Clear handoff.** RA produces a spec. LE consumes a spec. The orchestrator
  bridges them. No ambiguity about what's expected.

- **Honest accounting.** The sorry scoreboard tells you exactly where you are.
  You can't hide behind "making progress" when the count isn't going down.

The workflow is essentially the scientific method applied to formalization:
hypothesize (orchestrator), test (RA), formalize (LE), repeat.
