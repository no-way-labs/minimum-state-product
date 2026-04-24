# ARG's LCM Theorem: Restatement from STAN-CS-85-1055

**Session A deliverable.** Source: Haddad & Knuth, *A Programming and
Problem-Solving Seminar*, Stanford CS Technical Report STAN-CS-85-1055,
June 1985. Problem 4, pp. 67–79 (= PDF pp. 71–83).

Local PDF: `docs/arg_lcm/sources/stan-cs-85-1055.pdf`.

---

## 1. Verbatim theorem statement

From "Problem 4, Review of Solutions," p. 79 (full paragraph reproduced):

> ARG made the conjecture that there were no working schemes with more
> than a constant number of 2-state processors (as *n* gets large).
>
> ARG gives an argument for the proposition that: in any valid scheme
> with 2-state processors, every good cycle is *quasi-unidirectional*
> (once the baton is passed through one 2-state processor, it doesn't
> pass through the previous 2-state processor, again, until it has gone
> through all of the other 2-state processors). The main argument holds
> for three or more 2-state processors; the cases for either one or two
> 2-state processors are trivially true.
>
> Finally, he was able to show that: **in any valid scheme allowing 2*N*
> non-adjacent 2-state processors, the least common multiple, *L*, of
> the numbers of states in each of the blocks intervening between the
> 2-state processors must be at least *N* + 1.** Otherwise, it is easy
> to construct a cycle of bad configurations that look good locally to
> each of the processors that can move, and, hence, is infinite.

**Critical observation.** The proof is NOT in the transcript. Only the
statement and the one-sentence proof sketch ("easy to construct a cycle
of bad configurations that look good locally") appear.

ARG was absent on March 12 (the final day devoted to Problem 4, when
solutions were reviewed — see p. 77: "ARG was one of the five students
absent from class today"). His written solution was turned in; the
theorem appears in the editors' solutions-review section. No detailed
reconstruction from class dialogue is available.

## 2. Dialogue context preceding the statement

Relevant earlier material (pp. 67–78) that frames ARG's theorem:

- **March 7 (p. 73):** DEK's "baton can't reverse through a 2-state
  processor" argument. Quasi-unidirectionality is established first
  through a hand argument on `x_1 x_2 x_3 x_4 x_5` with 5 binaries, then
  generalized by RFC/DEK to "four 2-state processors in a row"
  impossibility.
- **March 7 (p. 74):** Replay of the 5-binary impossibility proof. DEA
  exhibits the explicit bad cycle.
- **March 7 (pp. 75–76):** `a_i α_i b_i β_i c_i γ_i` notation —
  2-state processors interspersed with non-binary blocks. DEK
  constructs a specific failing example at ring `[2,4,2,4,2,4]`
  (3 binaries, 3 quaternary arcs, each of length 1). Bad cycle length 32.
- **March 7 (p. 75):** MDD observes the structural dichotomy — a
  2-state processor acts either as a *reflector* (baton bounces back) or
  a *one-way gate* (baton passes through but cannot return via the
  same channel).
- **March 7 (p. 75):** AAM notes `[..., p_0, 2, 2, p_1, ...]` loses
  information — this is the seed of the "non-adjacent" hypothesis in
  ARG's statement.
- **March 12 (p. 77):** DEK's `α^(L,R)` notation for exhausted-block
  states; the block is treated as a 2-state machine with two boundary
  values — this is the conceptual core on which ARG's LCM argument
  likely builds.

## 3. Restatement in modern notation

Let the ring have processors $P_0, P_1, \ldots, P_{n-1}$ with state
counts $m_0, m_1, \ldots, m_{n-1}$. Each $P_i$ has transition function
$f_i(p_{i-1}, p_i, p_{i+1})$, with a central daemon (single-mover
master clock).

Let $B = \{i : m_i = 2\}$ be the set of binary positions, and let
$k = |B|$. Call $B$ **non-adjacent** iff no two elements of $B$ are
cyclically consecutive.

Decompose the ring into $k$ **arcs** (= ARG's "blocks") $A_1, \ldots, A_k$,
where $A_j$ is the maximal run of non-binary processors between
consecutive (in the cyclic order) binary positions. Each arc is non-empty
iff $B$ is non-adjacent.

**ARG's theorem (as stated in the transcript).** Suppose the ring admits
a valid self-stabilizing scheme, $B$ is non-adjacent, and $k = 2N$ (even
binary count, $N \geq 1$). Define

$$L = \mathrm{lcm}\{m_i : P_i \notin B\}.$$

Then $L \geq N + 1$.

---

## 4. Ambiguity: what is $L$?

The phrase "the least common multiple $L$ of the numbers of states in
each of the blocks intervening between the 2-state processors" admits
three plausible readings:

| Reading | Quantity defined as | Rationale |
|---|---|---|
| **R1 (global LCM)** | $L = \mathrm{lcm}\{m_i : P_i \notin B\}$ | Simplest parse; singular $L$ computed over state-count values aggregated across all blocks. |
| **R2 (per-arc, minimum)** | Bound holds per-arc: $\mathrm{lcm}\{m_i : P_i \in A_j\} \geq N+1$ for every $j$. | Matches "in each of the blocks" as a universal quantifier. Stricter than R1. |
| **R3 (block-product LCM)** | For each arc, $\pi_j = \prod_{P_i \in A_j} m_i$; then $L = \mathrm{lcm}\{\pi_1, \ldots, \pi_k\}$. | Matches "number of states in a block" = cardinality of block state-space. |

The transcript alone does not disambiguate; only the proof would. Since
the proof is missing, **reading (R1) is adopted as primary** in what
follows — it is grammatically the most literal parse and is consistent
with ARG's "constant number of 2-state processors" conjecture.

### 4.1. R1 supports the conjecture naturally

Under R1, if all non-binary processors have $m_i = 3$, then $L = 3$, and
the bound $L \geq N+1$ forces $N \leq 2$, i.e., at most 4 binaries.
Independent of $n$. Matches ARG's "constant number" conjecture.

If one non-binary is $m$-state, then $L = \mathrm{lcm}(3, m)$, and
binaries are bounded by $\mathrm{lcm}(3, m) - 1$. Still constant in $n$
when the non-binary states are bounded. This matches the conjectured
(but unproved) "no more than a constant number of binaries" form.

---

## 5. Application to the $n=8$ valid / $n=9$ invalid cases

Per the plan, the target question is whether ARG's theorem (extended to
odd binary count) distinguishes:

- **n=8**, multiset $\{2^3, 3^4, 4\}$ (product 2592) — known VALID.
- **n=9**, multiset $\{2^3, 3^5, 4\}$ (product 7776) — known INVALID
  (all 56 orientations fail).

Both have $k = 3$ binaries. **Note: $k = 3$ is odd, so $k = 2N$ has no
integer solution. ARG's theorem as stated does not apply to either.**

This is not a paraphrase artifact — the "2*N*" is essential to ARG's
phrasing. Extension to odd $k$ is Session B's task.

### 5.1. Table: $L$ under each reading, restricted to non-adjacent binaries

(For all non-adjacent orientations we compute the range of $L$ over
binary placements. "Min" and "max" are over distinct non-adjacent
orientations of the binaries.)

| Reading | n=8 $\{2^3, 3^4, 4\}$ | n=9 $\{2^3, 3^5, 4\}$ | Distinguishes? |
|---|---|---|---|
| R1 | $L = \mathrm{lcm}(3,3,3,3,4) = 12$ (constant) | $L = \mathrm{lcm}(3,3,3,3,3,4) = 12$ (constant) | **No** |
| R2 | min per-arc LCM = 3; max = 12 | min per-arc LCM = 3; max = 12 | **No** (same set) |
| R3 | arc-product LCM: depends on arrangement; values include 12, 36, 108, 324 | same general range; arrangement-dependent | Inconclusive; needs enumeration |

**R1 does not distinguish.** This is the "prima facie obstruction" from
the plan, confirmed against the source.

### 5.2. Consequence

If the odd-$k$ extension naturally yields an R1-shaped bound
($L \geq \text{something}(N)$ for $k = 2N+1$), it cannot separate the
two cases — the quantity $L = 12$ is identical. For Session B's extension
to land, either:

- (α) The extension pivots the bound to R2 or R3 structure, where
  arrangement enters, OR
- (β) The bound acquires an $n$-dependent factor (e.g., through the
  quasi-unidirectional baton traversal length, or the arc-length
  distribution), OR
- (γ) ARG is not the cause of the $n=9$ transition — A-KILL / dispatch.

---

## 6. What the proof sketch tells us (the one sentence that's there)

The only proof content is: "it is easy to construct a cycle of bad
configurations that look good locally to each of the processors that
can move."

Interpreted in terms of the earlier dialogue:

1. **"Look good locally."** Each mover $P_i$ must see a context
   $(p_{i-1}, p_i, p_{i+1})$ that, according to $f_i$, assigns $P_i$ a
   new state different from its current one — i.e., $P_i$ is privileged.
   But the overall configuration is bad.
2. **Construction uses locality.** The bad cycle is built by choosing
   boundary values at each binary position independently; the interior
   arcs are extended by the arc's own dynamics.
3. **LCM enters as cycle length.** The bad cycle closes when *all* arcs
   simultaneously return to their starting states. Arc $A_j$ has
   internal period dividing $\mathrm{lcm}\{m_i : P_i \in A_j\}$, so the
   full-ring cycle closes in time $= L$ (global LCM under R1; per-arc
   LCM under R2).
4. **$2N$ enters as baton count.** In $L$ time steps, each binary
   processor must fire on average $L / (2N)$ times. For the cycle to
   stay bad (avoid entering a good cycle), each binary must fire at
   least twice ($\geq 2$) — otherwise the baton would reach steady
   state. Bound: $L / (2N) \geq $ some constant, giving roughly
   $L \geq cN$.

**This is a reconstruction sketch, not a proof.** The exact $N + 1$
bound would come from quasi-unidirectionality forcing $L$ baton-returns
per arc, coupled with fairness. The precise structure is unclear from
the source.

---

## 7. The odd-$k$ parity gap (why ARG's statement has $2N$, not $k$)

Inspection of the dialogue gives three candidate reasons for the
even-$k$ restriction:

- **(P1) Proof artifact.** The bad cycle construction requires pairing
  binaries (each baton enters one and exits another). With odd $k$,
  pairing fails — one binary is unmatched. This is the most plausible
  source of the even-$k$ restriction.
- **(P2) Quasi-unidirectionality parity.** Quasi-unidirectionality makes
  the baton traverse all $k$ binaries in a single "lap" before returning.
  With odd $k$, the lap closure may impose a parity obstruction of its
  own (binary reversal over an odd number of reflectors).
- **(P3) Cosmetic.** $2N$ could be just notation and the proof extends
  unchanged to $2N+1$ with $N+1$ replaced by $\lceil (2N+1)/2 \rceil + 1$
  or similar. Unlikely given (P1)/(P2) but not excluded.

Without the proof, we cannot commit. **This is the Session B research
question.**

---

## 8. Session A verdict: A-PARTIAL

Neither A-PASS nor A-KILL. The transcription confirms ARG's statement
but the proof is not in the source, so the quantity $Q$ cannot be fully
disambiguated from text alone. However:

1. **R1 (most literal reading) does not distinguish** $n=8$ from $n=9$
   on the target multisets. $L = 12$ in both cases.
2. **R2 and R3 do not obviously distinguish either**, but their
   application requires arrangement-level enumeration that Session B
   would need to produce anyway.
3. **The odd-$k$ gap is real.** ARG's theorem as stated does not apply
   to $k = 3$. Session B must either:
   - Reconstruct the proof and identify where $2N$ is essential (P1/P2)
     vs cosmetic (P3), then derive the odd-$k$ version.
   - Or dispatch-ship: ARG's technique does not straightforwardly
     extend, phase transition source is elsewhere.

### 8.1. Pre-commits for Session B

Session B's opening memo (`arg_odd_extension.md`) must begin by:

1. **Reconstructing ARG's proof** from scratch, using the dialogue on
   pp. 73–77 (especially DEK's `α^(L,R)` boundary-exhausted notation
   on p. 77 and MDD's reflector/one-way dichotomy on p. 75) as scaffold.
2. **Pre-registering one of two strategies**:
   - **H1 (arc-structure refinement).** The proof's $L$ is arc-level,
     not global. Extension pivots to per-arc or block-product reading
     (R2 or R3). Arrangement enters.
   - **H2 (parity refinement).** The proof's $L$ is global. Extension
     introduces $n$-dependent factor via quasi-unidirectional lap length
     at odd $k$.
3. **Binding:** no route-switching mid-session. If H1/H2 dies, Session B
   dies and dispatch-ships. Pivoting requires a fresh scoping memo
   (per §6.5 of the research plan).

### 8.2. Observation worth carrying forward

One structural observation from the dialogue not captured by the one-line
statement: on p. 75, the failed example `[2,4,2,4,2,4]` at $n=6$ has
product 64, 3 binaries, 3 quaternary arcs of length 1, bad cycle of
length 32. Under R1: $L = 4$, $k = 3$, extended bound (guessing) may
be $L \geq \lceil k/2 \rceil + 1 = 3$, satisfied. So even the known
failing example at $n=6$ passes a naive R1 bound with rounding. This
hints that **any naive R1 extension will be too weak** to close
$n=9$, reinforcing the case for arc-structure refinement.

---

## 9. Next action

Session B opens with:
1. Reconstruction attempt on ARG's proof.
2. Pre-register H1 or H2.
3. Execute extension on odd $k$.
4. Apply to the 56 orientations of $\{2^3, 3^5, 4\}$ at $n=9$ and check
   whether the bound is violated for every orientation.

Artifact: `arg_odd_extension.md` in this directory.
