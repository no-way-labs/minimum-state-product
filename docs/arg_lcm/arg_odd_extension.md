# Session B: Odd-$k$ extension of ARG's LCM bound — B-OBSTRUCT

**Session B deliverable.** Outcome: **B-OBSTRUCT**. No extension of
ARG's 1985 LCM bound to odd binary count $k = 2N+1$, of the form
"some LCM functional on state counts $\geq$ threshold," can
distinguish the $n=8$ valid multiset $\{2^3, 3^4, 4\}$ from the
$n=9$ invalid multiset $\{2^3, 3^5, 4\}$.

The obstruction is a **structural insensitivity**, not a parity barrier
in ARG's specific machinery.

## 1. Opening commitment

Per research plan §6.5: this session pre-registers strategy H1 — arc-structure
refinement. That is, we test whether shifting from global LCM (R1) to
per-arc LCM (R2) or block-product LCM (R3) gives the quantity $Q$ that
discriminates the two cases. The search was settled quantitatively by
`probe01_enumerate_L.py`, reported in `notes/probe01_findings.md`.

## 2. The obstruction, stated

Let $\mathrm{Ms}_n = \{2^3, 3^{n-4}, 4\}$ for $n \geq 5$ be the target
"3 binary + (n−4) ternary + 1 quaternary" multiset. Let
$\mathcal{O}_n = \mathcal{O}_n^{\mathrm{adj}} \sqcup \mathcal{O}_n^{\mathrm{nadj}}$
be the set of distinct orientations of $\mathrm{Ms}_n$ on a ring of
length $n$, partitioned by adjacency of the 3 binaries.

Let $L_{R}(\omega)$ denote ARG's L-quantity under reading
$R \in \{R1, R2_{\min}, R2_{\max}, R3\}$, computed on orientation
$\omega \in \mathcal{O}_n^{\mathrm{nadj}}$.

**Theorem (Insensitivity).** For each of the four readings $R$,

$$\{L_R(\omega) : \omega \in \mathcal{O}_8^{\mathrm{nadj}}\} \,\subseteq\, \{L_R(\omega) : \omega \in \mathcal{O}_9^{\mathrm{nadj}}\}.$$

Specifically (computed over all orientations):

| Reading $R$ | Value-set at $n=8$ | Value-set at $n=9$ | Containment |
|---|---|---|---|
| R1 (global LCM) | $\{12\}$ | $\{12\}$ | equal |
| R2 min (min per-arc LCM) | $\{3\}$ | $\{3\}$ | equal |
| R2 max (max per-arc LCM) | $\{4, 12\}$ | $\{4, 12\}$ | equal |
| R3 (block-product LCM) | $\{36, 108\}$ | $\{36, 108, 324\}$ | proper |

**Corollary (No separating bound).** Suppose $b : \mathbb{N}^2 \to \mathbb{R}$
is a bound such that every valid self-stabilizing scheme on a non-adjacent
orientation $\omega$ of $\mathrm{Ms}_n$ satisfies $L_R(\omega) \geq b(k, n)$.
Then the hypothesis "every orientation of $\mathrm{Ms}_9$ violates the
bound" implies "at least one orientation of $\mathrm{Ms}_8$ violates the
bound." I.e., such a bound cannot distinguish the two cases.

**Proof.** For R1, R2min, R2max: the value-sets are equal. Any bound that
fails at some $\omega_9 \in \mathcal{O}_9^{\mathrm{nadj}}$ fails at every
$\omega_8 \in \mathcal{O}_8^{\mathrm{nadj}}$ with equal $L_R$ — and there
always is such an $\omega_8$.

For R3: the value-set at $n=9$ is $\{36, 108, 324\}$, containing $n=8$'s
$\{36, 108\}$. A bound that fails $\forall \omega_9$ must be $b > 324$
(strict). Such a bound also fails every $\omega_8$. $\blacksquare$

## 3. Why H1 fails — mechanism

The underlying reason: adding one 3-state processor from $n=8$ to $n=9$
does not alter:
- The multiset of non-binary state counts (it grows by one 3).
- The LCM of non-binary state counts (remains 12).
- The per-arc LCMs when arc-length compositions overlap.

ARG's LCM quantity is invariant under insertion of a processor whose
state count already divides $L$. The difference between valid $n=8$ and
invalid $n=9$ cannot be an LCM quantity because LCM is insensitive
to repetition.

What DOES change from $n=8$ to $n=9$:
- $n$ itself (ring length).
- Number of configurations: $2592 \to 7776$ (factor of 3).
- Arc-length partitions: $\{(1,1,3), (1,2,2)\} \to \{(1,1,4), (1,2,3), (2,2,2)\}$.
- Number of non-adjacent orientations: $10 \to 20$.

Any invariant that separates these cases must reference at least one of
these four. LCM references none.

## 4. Checking H2 (parity refinement) for completeness

H2 was "the proof's $L$ is global, extension introduces $n$-dependent
factor via quasi-unidirectional lap length at odd $k$."

Any refinement that preserves the form $L_R(\omega) \geq f(N, n)$ with
$L_R$ held to R1/R2/R3 is still killed by the Insensitivity Theorem
— the $L$ values are equal on $n=8$ and $n=9$ while $f(N, n)$ may change.
For a separating bound we'd need $f(N, 8) \leq 12 < f(N, 9)$, so the
threshold JUMPS between $n=8$ and $n=9$. This is not a "slight
modification of ARG's proof" — it's an essentially new argument with
sharp $n$-dependence that ARG's baton/cycle construction does not
naturally provide.

Hence H2 is not a viable rescue either. Any bound that jumps
discontinuously at $n=9$ is not a direct extension of ARG; it's a new
theorem whose source is not in the 1985 material.

## 5. Sanity checks: cases where ARG is still informative

ARG's bound is genuine and non-vacuous in adjacent domains:

- **$n=6$ all-binary** ($\{2^6\}$): $k = 6 = 2N$ with $N = 3$, bound
  $L \geq 4$; but non-binary set is empty, $L = 1$ by convention.
  Bound fails → no valid scheme. Matches seminar result (p. 73).

- **$n=8$ all-binary**: same argument, $N = 4$, $L \geq 5$ fails.

- **Uniform ternary ($\{3^n\}$, no binaries)**: $k = 0$, ARG vacuous.
  Dijkstra's Solution 3 works; $M$ $\leq 3^n$. ARG silent.

- **Many-binary mixed**: e.g., $\{2^{k}, 3^{n-k}\}$ with $k \geq$ some
  threshold. $L = 3$, bound $3 \geq N+1$ forces $N \leq 2$, i.e.,
  $k \leq 4$. Blocks too-many-binary schemes.

- **$n=9$ $\{2^4, 3^4, 6\}$** (5 non-adj orientations): $k=4$, $N=2$,
  bound $L \geq 3$, and $L = \mathrm{lcm}(3,3,3,3,6) = 6$. Bound met.
  But system is invalid. Shows ARG is necessary, not sufficient.

- **$n=6$ $[2,4,2,4,2,4]$** (transcript p. 75, invalid with product 512):
  $k=3$, $L=4$; any naive odd-$k$ extension $L \geq N+1$ for $2N+1=3$
  gives $L \geq 2$, trivially met. System is invalid despite passing
  the bound. Already a counterexample to "ARG-extended explains
  invalidity at $n=6$."

The last two rows are especially telling: ARG's own theorem in the
even case (the $\{2^4, 3^4, 6\}$ at $n=9$) and any natural odd
extension at $n=6$ are already both insufficient on *known* invalid
systems. The $n=9$ transition on $\{2^3, 3^5, 4\}$ is therefore not
an isolated failure of the LCM bound — it is part of a broader gap
between ARG's mechanism and the true structural obstruction.

## 6. Why the obvious workarounds don't apply

**Workaround A: double the ring.** If one could embed an odd-$k$ ring
into a $2k$-binary ring by duplication, ARG's even-$k$ theorem would
carry over. But the duplicated ring has $2n$ processors and product
$P^2$, and its validity status does not directly transfer to the
original ring. Duplication does not preserve Property (5) — fairness
across all processors — so a valid scheme on the $2n$-ring does not
induce one on the $n$-ring. This workaround fails.

**Workaround B: pad with a dummy processor.** Inserting a dummy
processor (e.g., a 1-state or trivially-connected node) to make $k$
even does not correspond to any Dijkstra-ring operation; the self-stab
conditions change.

**Workaround C: pair-up binaries via baton "virtual reflections."**
Quasi-unidirectionality implies the baton traverses all binaries in
cyclic order. With odd $k$, the baton returns to a binary after $k$
(odd) reflections, and the binary must be in its complement state.
After $2k$ reflections (two laps), it's back to start. So cycle length
$\geq 2k$ laps times lap-duration. This gives a lower bound on good-cycle
length, but the bound that emerges is $\sim 2nk$, which is the natural
expected cycle length and doesn't yield a state-count-product constraint
beyond what Dijkstra's $3^n$ construction already shows.

None of A/B/C yield a bound sharper than ARG's original at odd $k$.

## 7. Dispatch: what's left

Having ruled out ARG-extended as the source of the $n=9$ transition, the
open question becomes:

> **What structural invariant $I$, evaluated on a valid self-stabilizing
> scheme, has the property that $I$ is finite at $n=8$ $\{2^3, 3^4, 4\}$
> but infinite (or forbidden) at $n=9$ $\{2^3, 3^5, 4\}$?**

Candidate directions (NOT attempted here; flagged for future work):

1. **Good-cycle length vs configuration count.** At $n=9$ with product
   $7776$, the good cycle length (by fairness) must hit every processor.
   Quasi-unidirectional lap length = $\Theta(n)$. Total good cycle
   ≈ $3n - 2$ (CLB pattern) or similar. Bad-cycle count ≈ $P - \text{good}$.
   The $n$-dependence here is where the transition should be sought.

2. **Arc-phase incommensurability.** Arcs have internal periods; for a
   valid scheme, the arc-phase at each binary passage must be coherent.
   Incommensurate phase combinations give bad cycles. This is
   n-dependent in a way $L$ is not.

3. **Palindromic entry conflict** (primer CIC Expl 14): the known
   mechanism closing Case 3a (3 consecutive binaries). Generalization
   to non-adjacent 3-binary might close the remaining $n=9$ cases, but
   this is a different theorem entirely, not ARG-derived.

4. **Shadow cycles** (primer, paper2-dev main theorem): shadow arguments
   close Case 3c mixed systems. Already closed for $\{2^3, 3^5, 4\}$ via
   this route computationally — the open question is analytical.

## 8. Commitment to dispatch ship

This session terminates with B-OBSTRUCT. Per research plan §0.B,
§4.3-alt, and the dispatch branch in §8: the paper becomes a short
dispatch note titled *"ARG-LCM does not induce the n=9 phase
transition."* Draft in `paper.md`.

Decision rationale:
- Primary-ship thesis (A-GREEN) requires ARG-extended to rule out all
  56 orientations of $\{2^3, 3^5, 4\}$. Insensitivity Theorem (§2)
  rules out this possibility at the structural level, not merely at
  the level of current proof attempts.
- Dispatch is not a "failure"; it is the verdict the plan pre-registers
  for exactly this outcome. Kills a plausible thread and forces the
  search for the n=9 transition mechanism to a different invariant.

## 9. Artifacts at session end

- `arg_statement.md` — ARG restatement, R1/R2/R3 ambiguity, prima facie obstruction (Session A).
- `arg_odd_extension.md` — this file, B-OBSTRUCT writeup (Session B).
- `notes/probe01_findings.md` — data supporting §2.
- `probes/arg_lcm/probe01_enumerate_L.py` — reproducible verifier.
- `sources/stan-cs-85-1055.pdf` — primary source.
- `paper.md` — dispatch note (to be written).

No further scoping cycle is authorized without fresh Keston sign-off,
per research-plan pre-commit §6.5.

## 10. Postscript — witness-adjacency observation

Post-writeup check of the known $M_n$ witnesses in
`docs/verify_witnesses.py`:

| $n$ | witness ms | binary positions |
|---|---|---|
| 4 | $(2, 2, 2, 4)$ | $\{0, 1, 2\}$ |
| 5 | $(2, 2, 2, 3, 4)$ | $\{0, 1, 2\}$ |
| 6 | $(2, 2, 2, 4, 3, 3)$ | $\{0, 1, 2\}$ |
| 7 | $(3, 2, 2, 2, 3, 4, 3)$ | $\{1, 2, 3\}$ |
| 8 | $(2, 2, 3, 4, 3, 3, 2, 3)$ | $\{0, 1, 6\}$ |

Every $M_n$ witness for $4 \leq n \leq 8$ has at least two cyclically
adjacent binaries. ARG's theorem (non-adjacent hypothesis) is silent on
every one. This strengthens the dispatch: not only is ARG's LCM
functional insensitive on the non-adjacent orientations where it applies,
but ARG is *scoped out* of the adjacent-binary valid witnesses entirely.

The shipped paper (`paper.md`) incorporates this observation as its §2
("Observation 1 — ARG is silent on the valid witnesses"), alongside the
§3 Insensitivity Theorem. The combined argument is strictly stronger
than either alone.
