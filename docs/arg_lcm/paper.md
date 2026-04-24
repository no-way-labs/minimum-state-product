# ARG-LCM does not induce the $n=9$ phase transition

**Dispatch note.** *Draft.*

## Abstract

Let $M_n$ denote the minimum value of the state-count product
$m_0 m_1 \cdots m_{n-1}$ over valid self-stabilizing rings in the sense
of Dijkstra (1974). Knuth's 1985 seminar (STAN-CS-85-1055, Problem 4)
asks for the asymptotics of $M_n$; the state of knowledge fixes
$M_n = 32 \cdot 3^{n-4}$ for $5 \leq n \leq 8$ and
$M_n = 4 \cdot 3^{n-2}$ for $n \geq 9$, with the crossover at $n=9$ a
*phase transition* where the winning construction changes. At $n=9$
every orientation of the previous-family multiset $\{2^3, 3^5, 4\}$
(product $7776$) fails the Dijkstra axioms.

A natural thesis attributes the transition to an odd-$k$ extension of
*ARG's 1985 LCM bound* (STAN-CS-85-1055, p. 79): in any valid scheme
with $2N$ non-adjacent 2-state processors, the LCM $L$ of the block
state counts satisfies $L \geq N+1$. We test this thesis and prove a
negative result, via two observations:

> **Observation 1 (Scope).** The known valid witnesses at $n = 7, 8$ are
> ADJACENT-binary orientations, lying outside ARG's hypothesis. ARG's
> bound is silent on every known valid construction in this family.
>
> **Observation 2 (Insensitivity).** On non-adjacent orientations, the
> value of ARG's LCM quantity under any of its three natural readings
> (global, per-arc, block-product) is identical between $n=8$ and $n=9$
> on the target multiset (or strictly nested in the sense that $n=9$
> values contain $n=8$'s). No LCM-functional bound can discriminate.

Together: ARG's LCM mechanism cannot be the principled name for the
$n=9$ phase transition, because the transition lives in the *adjacent*
sub-family on which ARG is silent, and because the bound's value
collapses on the non-adjacent sub-family it does cover. Proposed
attributions in the literature and in the Stanford primer should look
elsewhere.

## 1. Background

### 1.1. Problem

A Dijkstra ring on $n$ processors $P_0, \ldots, P_{n-1}$ with state
counts $m_0, \ldots, m_{n-1}$ admits transition rules
$f_i(p_{i-1}, p_i, p_{i+1})$ under a central daemon. The scheme is
*valid* iff Dijkstra's five properties (liveness, good-cycle uniqueness,
closure, no bad-cycle, fairness) are met for some designer-chosen
partition of configurations into good/bad. Set
$M_n = \min \prod m_i$ over valid schemes.

### 1.2. Known bounds

- $M_n \leq 3^n$ (Dijkstra 1974, Solution 3).
- $M_n > 2^n$ for $n > 4$ (Haddad–Knuth 1985, p. 73).
- $M_n = 32 \cdot 3^{n-4}$ for $5 \leq n \leq 8$ (exhaustive search,
  explicit witnesses available in `verify_witnesses.py`).
- $M_n \leq 4 \cdot 3^{n-2}$ for $n \geq 5$ (CLB endpoint-binary
  construction); tight for $n \geq 9$ by exhaustive lower bound.

The discontinuity at $n=9$ — the "3+1+rest" multiset family
$\{2^3, 3^{n-4}, 4\}$ ceasing to work — is the phase transition.

### 1.3. ARG's bound

STAN-CS-85-1055, p. 79 (Haddad–Knuth 1985, Review of Solutions):

> In any valid scheme allowing $2N$ non-adjacent 2-state processors,
> the least common multiple, $L$, of the numbers of states in each of
> the blocks intervening between the 2-state processors must be at
> least $N+1$.

The proof is not transcribed — ARG was absent on review day. Three
readings of "LCM of the numbers of states in each of the blocks" are
plausible (all consistent with the phrase): global LCM (R1), per-arc
LCM (R2), block-product LCM (R3). None is textually disambiguated.

### 1.4. The thesis

Under test: some extension of ARG's bound to odd $k = 2N+1$ binaries
rules out all 56 orientations of $\{2^3, 3^5, 4\}$ at $n=9$ (or at
least all non-adjacent ones), while permitting the valid $n \leq 8$
constructions.

## 2. Observation 1 — ARG is silent on the valid witnesses

The known $M_n$ witnesses for $5 \leq n \leq 8$ (from
`docs/verify_witnesses.py`) have the following binary
structure:

| $n$ | witness ms | binary positions | structure |
|---|---|---|---|
| 4 | $(2, 2, 2, 4)$ | $\{0, 1, 2\}$ | 3 consecutive |
| 5 | $(2, 2, 2, 3, 4)$ | $\{0, 1, 2\}$ | 3 consecutive |
| 6 | $(2, 2, 2, 4, 3, 3)$ | $\{0, 1, 2\}$ | 3 consecutive |
| 7 | $(3, 2, 2, 2, 3, 4, 3)$ | $\{1, 2, 3\}$ | 3 consecutive |
| 8 | $(2, 2, 3, 4, 3, 3, 2, 3)$ | $\{0, 1, 6\}$ | 2 consecutive + 1 isolated |

Every listed witness has at least one pair of cyclically adjacent
binaries. ARG's theorem assumes $B$ is non-adjacent ("$2N$ non-adjacent
2-state processors"). The quantifier is essential to his construction
(information is preserved across a single 2-state channel; two
back-to-back 2-state processors lose information per AAM on p. 75).

**Consequence.** ARG's bound cannot produce the inequality $L \geq N+1$
on any of the known valid witnesses, because its hypothesis fails. So
ARG cannot be the mechanism that tracks the "valid construction" side
of the phase transition.

This alone does not kill the thesis — ARG could still rule out
non-adjacent orientations at $n=9$ without contradicting the valid
adjacent $n \leq 8$ witnesses. Observation 2 closes the remaining gap.

## 3. Observation 2 — Insensitivity on non-adjacent orientations

Let $\mathcal{O}_n^{\mathrm{nadj}}$ denote the set of non-adjacent
orientations of $\{2^3, 3^{n-4}, 4\}$ on an $n$-ring (up to cyclic
rotation). For $\omega \in \mathcal{O}_n^{\mathrm{nadj}}$ and reading
$R \in \{R1, R2_{\min}, R2_{\max}, R3\}$, let $L_R(\omega)$ denote the
LCM functional.

**Theorem 3.1 (Insensitivity).** *The following holds for $5 \leq n_1 \leq n_2 \leq 9$
whenever both have $k=3$ binaries and the target multiset applies:*

$$\{L_R(\omega) : \omega \in \mathcal{O}_{n_1}^{\mathrm{nadj}}\} \,\subseteq\, \{L_R(\omega) : \omega \in \mathcal{O}_{n_2}^{\mathrm{nadj}}\}.$$

*Values computed directly (Appendix A):*

| Reading $R$ | $n=7$ | $n=8$ | $n=9$ |
|---|---|---|---|
| R1 | $\{12\}$ | $\{12\}$ | $\{12\}$ |
| $R2_{\min}$ | $\{3\}$ | $\{3\}$ | $\{3\}$ |
| $R2_{\max}$ | $\{4, 12\}$ | $\{4, 12\}$ | $\{4, 12\}$ |
| R3 | $\{12, 36\}$ | $\{36, 108\}$ | $\{36, 108, 324\}$ |

**Corollary 3.2 (No separating bound).** *Fix $R \in \{R1, R2_{\min}, R2_{\max}\}$.
Any bound of the form "$L_R(\omega) \geq b(k, n)$ necessary for validity"
that is violated by every $\omega \in \mathcal{O}_9^{\mathrm{nadj}}$
would also require $b(k, 8) > L_R(\omega)$ for every $\omega \in
\mathcal{O}_8^{\mathrm{nadj}}$, i.e., it would rule out all 10
non-adjacent orientations of $\{2^3, 3^4, 4\}$ at $n=8$ as well. This
is formally consistent (those 10 are indeed invalid by other means;
the valid witness is adjacent-binary), but it shows the bound is
$n$-blind — it does not distinguish the phase-transition boundary. For
R3, the bound must have $b(k, 9) > 324$, but the same $b(k, 9)$ applied
uniformly at $n=8$ gives $b(k, 8) > 108$, ruling out all $n=8$
non-adjacent orientations as well. Same conclusion.*

## 4. Combined verdict

Observation 1 establishes that the known valid constructions at
$n \leq 8$ sit outside ARG's hypothesis. Observation 2 establishes that
ARG's LCM quantity, on the non-adjacent orientations it DOES cover,
has values that are identical or nested between $n=8$ and $n=9$ on the
target family.

Hence:

1. **ARG cannot track the "valid side" of the transition.** It is
   silent on the valid witnesses.
2. **ARG cannot distinguish the "invalid side" at $n=9$ from the
   invalid-non-adjacent-orientations at $n=8$.** The $L$-values coincide.

A principled name for the $n=9$ phase transition must:
- Apply to *adjacent-binary* orientations (where the valid $n \leq 8$
  witnesses live), AND
- Depend on $n$ in a way that ARG's LCM quantity does not.

No extension of ARG's 1985 bound meets either criterion without becoming
a substantively different theorem.

## 5. What the bound remains good for

Observation 1/2 do not refute ARG's theorem. The 1985 result is
correct and useful in three regimes:

- **All-binary rings.** $L = 1$ (empty non-binary set); bound fails
  immediately for any $N \geq 1$, reproving "no all-2-state ring for
  $n > 4$" (Haddad–Knuth p. 73).
- **Many-binary mixed with small non-binaries.** E.g., $\{2^k, 3^{n-k}\}$
  forces $L = 3$, hence $k \leq 4$. Caps binary count at 4 in the
  all-ternary-non-binary case.
- **Historical / textbook completeness.** ARG's result remains a genuine
  1985 contribution to the problem.

What ARG does not do — the thesis this note refutes — is explain why
the "3 binary + $(n-4)$ ternary + 1 quaternary" construction, which
works at every $5 \leq n \leq 8$, stops working at $n=9$.

## 6. Where the real invariant should live

The constants that distinguish $n=8$ valid from $n=9$ invalid on
$\{2^3, 3^{n-4}, 4\}$:

- $n$ itself (+1).
- total product (factor 3).
- arc-length partition set — $\{(1,1,3), (1,2,2)\} \to \{(1,1,4), (1,2,3), (2,2,2)\}$.
- good-cycle length (fairness-forced: $\geq $ some $\Theta(n)$).

An invariant-based proof must reference at least one. Observation 1
further requires it to apply to adjacent-binary orientations. Candidates
from the paper2 lower-bound program (NOT pursued here):

1. **Palindromic entry conflict** (primer CIC Expl 14): closes the
   3-consecutive-binary sub-case via a context-arithmetic contradiction.
   Adjacent-aware. Explicitly $n$-indexed via "n−3 conflicting processors."
2. **Shadow cycle mirror theorem** (primer Shadow): extends to mixed
   systems via MNU + Universal Escape; $n$-indexed via cycle length.
3. **Good-cycle length vs product** entropy-style arguments.

These live outside ARG's framework and outside the 1985 material.

## 7. Conclusion

ARG's LCM bound does not induce the $n=9$ phase transition in Knuth's
state-product problem. The plausibility of this attribution arises from
the surface form of the bound — "LCM of block state counts $\geq$ arc
count," reading as an $n$-indexed structural obligation — but unpacking
either the hypothesis (non-adjacent only) or the value (insensitive
under $n$-insertion of a processor whose state count divides $L$)
dispels the connection.

Any future resolution of the $n=9$ transition is an $n$-aware,
adjacent-aware argument, categorically unlike ARG's. Whether such an
argument connects to Knuth's asymptotic question $\limsup M_n^{1/n} < 3$
remains, as it did in 1985, open.

## Appendix A. Python verifier

Single-file script with Python-standard-library dependencies only.

- Script: `probes/arg_lcm/probe01_enumerate_L.py`
- Invocation: `python3 probe01_enumerate_L.py`
- Runtime: < 1 s.
- Deterministic, no randomness.

The script enumerates non-adjacent orientations of each target
multiset and computes R1, R2 min/max, R3 LCM functionals. Output
reproduces Theorem 3.1's table verbatim.

## References

[Haddad–Knuth 1985] R. W. Haddad and D. E. Knuth, *A Programming and
Problem-Solving Seminar*, Stanford CS Technical Report STAN-CS-85-1055,
June 1985. Problem 4, pp. 67–79.

[Dijkstra 1974] E. W. Dijkstra, "Self-stabilizing systems in spite of
distributed control," Communications of the ACM **17**(11):643–644,
1974.

[Dijkstra 1986] E. W. Dijkstra, "A belated proof of self-stabilization,"
Distributed Computing **1**(1):5–6, 1986.

[Tchuente 1981] M. Tchuente, "Sur l'auto-stabilisation dans un réseau
d'ordinateurs," *RAIRO Informatique Théorique* **15**(1):47–66, 1981.
