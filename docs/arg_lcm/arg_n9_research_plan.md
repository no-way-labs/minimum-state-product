# ARG-LCM and the n=9 Phase Transition: Research Plan

**Status.** Scoping plan, pre-execution. Binding pre-commits in §6.

**Thesis to test.** The exhaustive-sweep failure of `{2³, 3⁵, 4}` at n=9 is
ARG's 1985 LCM constraint (extended to odd binary count) applied at the
tight regime, not a brute computational fact. If true, the n=9 phase
transition in Knuth's state-product problem gets a principled name
inherited from the Stanford 1985 seminar.

**Scope isolation.** This investigation does not touch any SK/Clouds Lean
sorry, does not read from `LowerBound/SK/*`, does not depend on any Clouds
machinery. Paper and verifier are standalone artifacts. No dependency
flows either direction.

---

## 0. Shippable targets, in preference order

### A. Primary ship — GREEN scenario

Short note, 4–8 pages, roughly titled *"The n=9 phase transition in
self-stabilizing token rings: an extension of ARG's 1985 LCM bound."*
Contents:

1. Restatement of ARG's LCM result with proof reconstructed from Haddad
   (STAN-CS-85-1055).
2. Extension to odd binary count (2N+1 binaries), with proof.
3. Application: the extended bound, applied to any orientation of
   `{2³, 3⁵, 4}` at n=9 with non-adjacent binaries, is violated. Adjacent-
   binary orientations handled by a separate (shorter) argument.
   Conclusion: no valid system at product 7776.
4. Corollary: combined with the CLB upper bound `M_n ≤ 4·3^(n−2)`,
   `M_9 = 8748` exactly — now with an analytical, not computational, proof.

Shippable standalone. Does not depend on the Clouds LB program. Does not
touch any Lean sorry.

### B. Dispatch ship — YELLOW scenarios

Short note: *"ARG-LCM does not induce the n=9 phase transition."* The
question is naturally posed (and explicitly flagged in the primer §0);
answering it in the negative is a contribution. It kills a plausible-
looking thread and forces the search for the real cause of the transition
elsewhere. Less satisfying than A but a clean artifact.

### C. Lean formalization — optional follow-on, not on critical path

Zero-sorry, zero-axiom Lean 4 formalization of the extended ARG bound,
targeting mathlib-std imports only. Only attempted after A ships on paper.
Not a blocking deliverable for the paper. Scope-capped at ~2000 Lean lines;
exceed that → scope back to paper-only.

### D. Python verifier — bundled appendix

Self-contained Python script enumerating the 56 orientations of
`{2³, 3⁵, 4}` at n=9, computing the relevant quantity for each, checking
the bound. Standard library only, < 1 min runtime, deterministic.
Intended as appendix to the paper — a transparency check, **not** the
proof. The proof is analytical.

### High-standards commitment

Ships only when:

- Paper draft has no `[TK]` markers, no unresolved cases, no "modulo X"
  claims. Every case in `{2³, 3⁵, 4}` is accounted for by the analytical
  argument (possibly split into sub-cases, all proved).
- If Lean is involved: sorry count 0, axiom count 0
  (`#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`
  or equivalent standard set; no user-introduced axioms).
- Python verifier runs clean, deterministic, single command, documented
  dependencies.

No named-conjecture ship. No "result modulo plausible extension" ship.
Same hard constraint as the SK campaign — the investigation either lands
as a clean theorem or dispatches as a clean negative.

---

## 1. Background — what we know and what we don't

### 1.1. ARG's 1985 statement (paraphrased from p2)

Let the ring have 2N non-adjacent 2-state processors. The remaining
processors form 2N arcs of ternary-or-larger machines. Let `L` be the LCM
of the state counts along each arc. Then valid self-stabilization requires
`L ≥ N+1`; if `L < N+1`, a bad cycle of configurations can be constructed
and the ring is not self-stabilizing.

**What's unclear from p2 alone — Session A must resolve.**

- Is the bound per-arc (each arc independently), or is it a single
  constraint on all arcs' LCMs jointly?
- What exactly is the `L` being bounded — arc-LCM, arc-length,
  arc-state-product, or a phase-like quantity combining them?
- Does the proof extend to arcs of length 0 (adjacent binaries, currently
  excluded by "non-adjacent" hypothesis)?
- What is the actual parity dependence — where does `2N` enter the
  argument essentially, versus cosmetically?

### 1.2. The n=9 failure

From the SK primer §5:

- At n=9, product ≤ `7776 = 32·3⁵` forces ≥ 3 binary positions.
- All 56 orientations of `{2³, 3⁵, 4}` at n=9 exhaustively fail.
- So `M_9 > 7776`; the next achievable is `4·3⁷ = 8748` via the
  `(2,3,…,3,2)` CLB construction.

The question: *why* do they all fail? Computationally, we know.
Analytically, we don't.

### 1.3. Why arc-LCM alone cannot be the answer (prima facie obstruction)

This is the most important observation in the plan; it shapes Session A.

At **n=8** with 3 non-adjacent binaries (e.g. `{2³, 3⁴, 4}`): valid
systems exist, `M_8 = 2592`. Arcs partition 5 non-binary positions among
`{3,3,3,3,4}`; possible arc-LCMs are `{3, 12}`.

At **n=9** with 3 non-adjacent binaries (`{2³, 3⁵, 4}`): no valid system.
Arcs partition 6 non-binary positions among `{3,3,3,3,3,4}`; possible
arc-LCMs are `{3, 12}`.

**Same LCM set at both n.** A per-arc LCM bound, applied naively, cannot
distinguish them. Hence at least one of the following must hold:

1. **(Q-rich)** ARG's bound uses a quantity richer than arc-LCM (e.g.
   arc-length enters, or arcs interact jointly). Session A clarifies.
2. **(Parity-dependent)** The bound applies but is parameterized by N,
   and the extension to odd N introduces n-dependence that bites at n=9
   but not n=8.
3. **(Dispatch)** The phase transition is not ARG-induced. The §0 primer
   intuition is wrong. Dispatch ship.

Session A pins down which. If the answer is (3), the thread dies in one
session with a clean dispatch note. That is acceptable and shippable.

---

## 2. Session A — literature read

**Goal.** Produce `arg_statement.md`: a precise, self-contained restatement
of ARG's LCM result, in the notation used by the SK primer, with the
proof fully reconstructed.

**Source.** Haddad, R. W., and Knuth, D. E., *"A Programming and Problem-
Solving Seminar,"* Stanford CS Technical Report STAN-CS-85-1055, June 1985.
Problem 4, pages 67–79. Available via Stanford InfoLab; also DTIC and
possibly arXiv mirrors.

**Scope.** 3–6 hours. Primary-source literature work.

**Methodology.** Transcribe first, paraphrase second. The p2 primer's
one-sentence summary of ARG is exactly the kind of compression that may
hide whether the bounded quantity is arc-LCM or something richer. Start
with a direct transcription of the theorem and proof from Haddad, then
restate in modern notation, then interpret.

**Deliverable `arg_statement.md` — contents:**

1. Exact theorem statement, with all quantifiers made explicit.
2. The quantity `L` defined precisely. If it is arc-LCM, so stated. If it
   is something else, so stated.
3. The `N+1` bound — is it tight in ARG's proof, or is there slack that
   could be exploited for a sharper version?
4. The proof, reconstructed in modern notation, every step justified.
5. Whether the non-adjacency hypothesis is essential to the proof or
   cosmetic.
6. Explicit identification of every step using `2N` (even parity) — either
   as a substantive use or as a notational convenience.
7. A table comparing ARG's quantity on `{2³, 3⁴, 4}` at n=8 vs
   `{2³, 3⁵, 4}` at n=9. If identical under ARG's actual (not paraphrased)
   quantity, we have A-KILL. If different, we know what Q is and Session B
   has a target.

**Exit criteria.**

| Outcome | Condition | Next |
|---|---|---|
| A-PASS | ARG bounds a quantity Q that **differs** between n=8 `{2³,3⁴,4}` and n=9 `{2³,3⁵,4}`. | Session B with Q identified. |
| A-KILL | ARG bounds a quantity identical between the two cases. | Dispatch ship B. Thread dies in 1 session. |
| A-PARTIAL | ARG's actual statement is stronger or different than p2's paraphrase, but it's not yet clear whether Q-differs. | Extend Session A to 10 hour cap; force a binary verdict at cap. |

**Anti-goal.** Do not attempt to prove the odd-k extension during
Session A. Restatement + proof reconstruction only. Extension is
Session B. Mixing the two forces early commitment to an attack direction
before the target is understood.

---

## 3. Session B — odd-k extension attempt

**Only runs if Session A concludes A-PASS.**

**Goal.** Either a theorem extending ARG to 2N+1 binaries, or a precise
parity obstruction statement.

**Approach.** Rerun ARG's bad-cycle construction with 2N+1 binaries. At
each step where `2N` or evenness is used, do one of:

- Show the step generalizes with minor modification (+1 adjustment to the
  bound, parity-corrected cycle length, etc.), and verify the modified
  bound is still a valid necessary condition.
- Identify the step as a genuine parity obstruction; characterize what
  structural feature fails at odd N; state the obstruction precisely.

**Scope.** 6–12 hours. Mathematical reasoning + possibly small Python
probes to sanity-check candidate bounds on small cases (n=5, 6, 7 with
known-valid and known-invalid ms).

**Deliverable `arg_odd_extension.md`:**

Under B-PASS:

1. Extended theorem statement with explicit bound for 2N+1 binaries.
2. Proof, noting each place where the 2N argument generalized and how.
3. Worked sanity checks on small n (e.g. n=5, 6, 7) confirming the bound
   is consistent with known-valid ms.
4. Application: applied to `{2³, 3⁵, 4}` at n=9, does it rule out every
   orientation? (If yes → Session C. If no → ship as B-PASS-INSUFFICIENT.)

Under B-OBSTRUCT:

1. The parity obstruction, stated precisely.
2. Why the obvious workarounds (doubling the ring, padding, etc.) do not
   apply — or if they do, note that and return to B-PASS branch.
3. Dispatch write-up: *"ARG's argument has a genuine parity barrier;
   extension to odd binary count is open."*

**Exit criteria.**

| Outcome | Condition | Next |
|---|---|---|
| B-PASS | Extension works; rules out `{2³,3⁵,4}` at n=9. | Session C; Ship A. |
| B-PASS-INSUFFICIENT | Extension works; does not rule out `{2³,3⁵,4}`. | Dispatch: *"ARG extends to odd-k but phase transition source is different."* |
| B-OBSTRUCT | Genuine parity barrier, no workaround in 12 hours. | Dispatch: *"ARG-LCM parity barrier; n=9 transition source remains computational."* |

**Binding time cap.** 12 hours hard budget. At 12 hours, force one of the
three verdicts. Do not open a second scoping cycle inside Session B. If
both obstruction and workaround look plausible and time is out →
B-OBSTRUCT; the obstruction note is still shippable, the maybe-workaround
is not.

**Anti-goal.** No route-switching mid-session. Commit to the extension
strategy pre-registered in Session B's opening memo (which is written
after Session A clarifies what Q is). If that strategy dies, the session
dies — do not pivot to a second strategy without a fresh scoping memo,
which by pre-commit (§6) requires a separate budget.

---

## 4. Session C — mechanical verification + paper draft

**Only runs if Session B concludes B-PASS.**

**Goal.** Ship A.

### 4.1. Python verifier `arg_n9_verify.py`

Enumerate all 56 orientations of `{2³, 3⁵, 4}` at n=9. For each:

1. Compute the binary-position set; check non-adjacency.
2. If non-adjacent, compute the quantity Q from the extended bound;
   check whether the bound is violated.
3. If adjacent, defer to the separate adjacent-binary argument (also
   checkable — usually trivial because adjacent 2-state processors run
   into the DEK 1985 "never wants to move twice in a row" impossibility).

Output a table: orientation → binary positions → adjacency → Q → bound
violated? → disposition.

**Reproducibility.**

- Single command: `python arg_n9_verify.py`.
- No external dependencies beyond the Python standard library.
- Deterministic. Runtime < 1 minute on a laptop.
- Output committed alongside the script so any reader can diff.

**Role.** Transparency check for the analytical proof. **Not** load-bearing:
the proof is analytical, the verifier just lets the reader confirm the
arithmetic on the 56 specific cases without re-doing it by hand. If the
proof has a gap that the verifier is filling via exhaustive computation,
that violates §6.6 and is not a ship.

### 4.2. Paper draft `paper.md`

4–8 pages (markdown for draft; convert to LaTeX at ship time if the target
venue prefers). Sections:

1. **Introduction.** Knuth's 1985 state-product problem; Dijkstra's
   `3^n` upper bound; the `M_n ≤ 4·3^(n−2)` CLB improvement; the n=9
   phase transition; why a principled name matters.
2. **ARG's 1985 LCM result, restated.** Session A content.
3. **Extension to odd binary count.** Session B content.
4. **Application to n=9.** `{2³, 3⁵, 4}` orientations fall to the
   extension. Adjacent-binary sub-case.
5. **Corollary.** `M_9 = 8748` exactly, with combined UB (CLB
   construction) and LB (this paper) both analytical.
6. **Discussion.** What this does and does not say. Relation to Knuth's
   asymptotic `M_n^(1/n)` questions (it does not resolve them — see §7 of
   this plan).

Appendix A: Python verifier listing and output table.

### 4.3. Self-containment

Paper stands alone without reference to the SK/Clouds campaign. Does not
mention A1, sorry counts, Lean, or any in-campaign machinery. Clean
result on the 1985 problem, extending a 1985 technique; reads as a
standalone contribution to a 40-year-old open problem.

**Scope.** 8–16 hours (drafting, verifier coding, cross-check).

---

## 5. Optional follow-on — Lean formalization

Only after paper ship. Not on critical path. Strictly optional.

**Targets.**

- ARG's original theorem (from Session A).
- The odd-k extension (from Session B).
- Applied corollary: no valid system at product 7776 for n=9.

**Anticipated mathlib dependencies.** Cyclic ring / `Fin`-indexed state
spaces; `Nat.lcm` over `Finset`; hand-rolled bad-cycle construction
(likely not in mathlib); possibly `Fintype.card` facts for the
orientation enumeration.

**Ship criterion.**

- `lake build` green.
- `#print axioms` on every top-level theorem returns only the standard
  Lean/mathlib axiom set — no user-introduced axioms, no `sorry`,
  no `admit`, no `native_decide` in proof bodies of claimed theorems.
- Grep confirms zero `sorry` and zero `admit`.

**Scope cap.** If the formalization exceeds ~2000 Lean lines or requires a
non-trivial mathlib PR, abort and leave the paper as the artifact. This is
a "clean formalization if it's cheap" gate, not a second research project.

---

## 6. Binding pre-commits

Style matches `sk_portfolio_commitment_2026-04-18.md`. These are binding.

1. **Session A verdict triggers response immediately.**
   A-KILL → dispatch ship, no rescoping, thread dies cleanly.
   A-PARTIAL at 10 hours → force a binary verdict at the cap.

2. **Session B time cap = 12 hours.** No extension. Force one of
   `{B-PASS, B-PASS-INSUFFICIENT, B-OBSTRUCT}` at the cap.

3. **No named-conjecture ship.** If the proof has a gap, the paper does
   not ship with the gap labeled as a conjecture. Either close the gap or
   write the dispatch note. Same rule as the SK campaign — hard stop.

4. **Scope isolation.** This investigation does not touch any SK sorry,
   does not read from `LowerBound/SK/*`, does not depend on any Clouds
   machinery. Confirmed at ship time by a grep check on the paper and
   the verifier.

5. **No mid-session route-switching.** If Session B's pre-registered
   strategy dies, the session dies. Pivoting to a second strategy requires
   a fresh scoping memo and a fresh budget; it is not a continuation of
   the current session.

6. **Python verifier is appendix, not proof.** Ship criterion is an
   analytical proof. The verifier is a transparency check. If the proof
   has a gap that the verifier is filling via exhaustive computation, it
   violates this clause and is not a ship.

7. **High-standards commitment on Lean (if attempted).** Zero sorry,
   zero user axioms, `lake build` green. No carve-outs, no "modulo
   mathlib PR" shipping.

---

## 7. What this does not claim

Scope honesty, to anticipate review:

- Does not close any SK/Clouds Lean sorry.
- Does not resolve the full Knuth 1985 asymptotic question
  (`limsup M_n^(1/n)` bounds).
- Does not improve `M_n` bounds for `n ≠ 9`. Small-n (n ≤ 8) bounds remain
  as established; the `n ≥ 9` asymptotic gap is untouched.
- Does not prove ARG's 1985 binary-count conjecture (`k` binaries
  constant as n → ∞). That claim, if it lands, comes from the Clouds
  program, not from this extension.

Scope: the n=9 arithmetic in one clean paper, ≤ 8 pages, self-contained.

---

## 8. File deliverables

All paths relative to the investigation root.

| Session | File | Status at start | Status at ship |
|---|---|---|---|
| A | `arg_statement.md` | — | ARG's theorem restated with proof reconstructed; Q-quantity identified or A-KILL called |
| B | `arg_odd_extension.md` | — | Extension theorem + proof, OR precise parity obstruction |
| C | `arg_n9_verify.py` | — | Runnable, ≤ 1 min, stdlib only, deterministic output |
| C | `paper.md` | — | Draft; one-person reviewable; no `[TK]` |
| (opt) | `lean/ArgExtension/*.lean` | — | Zero-sorry, zero-axiom, `lake build` green |

Under B-KILL / B-OBSTRUCT / B-PASS-INSUFFICIENT (dispatch scenarios),
`paper.md` becomes a shorter dispatch note (2–4 pages) with different
contents, keeping sections 1–2 and replacing 3–5 with the dispatch result.

---

## 9. Opening move

Pull STAN-CS-85-1055 (Haddad & Knuth 1985) from Stanford InfoLab. Read
Problem 4, pp. 67–79. Begin `arg_statement.md` with a direct transcription
of the LCM result statement and proof; *then* restate in modern notation;
*then* interpret.

Transcribe first, interpret second. The p2 primer's one-sentence summary
is exactly the kind of compression that may hide the real structure of
Q. A two-hour read-and-transcribe sets the whole investigation on
accurate footing or ends it immediately with a clean dispatch — both
outcomes are productive, and both are cheaper than building on a
paraphrase.
