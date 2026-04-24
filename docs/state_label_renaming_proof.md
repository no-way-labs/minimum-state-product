# State-label renaming is validity-preserving — clause-by-clause proof

This document is the full proof of
[`lem:state-label-bijection`](../paper/main.tex) (paper Appendix C.3
item (4), *Soundness proofs of the pruning rules*). The paper gives
the two-sentence sketch; the clause-by-clause check below is the
referenceable expansion.

The template — "a routine check on the definitions" — is the one used
for the dihedral action (`enumi:orbit-red`). This document walks the
template step by step for the state-label renaming action.

---

## 1. Setup and notation

Fix $n \ge 3$ and a state-count vector $\mathbf{m} = (m_0, \ldots,
m_{n-1})$. A *configuration* is a tuple $c = (c(0), \ldots, c(n-1)) \in
\prod_i \mathrm{Fin}(m_i)$. A *rule* at position $i$ is a function
$f_i : \mathrm{Fin}(m_{i-1}) \times \mathrm{Fin}(m_i) \times
\mathrm{Fin}(m_{i+1}) \to \mathrm{Fin}(m_i)$ (indices mod $n$); a
*system* is $(\mathbf{m}, f_0, \ldots, f_{n-1})$.

Let
$\sigma = (\sigma_0, \ldots, \sigma_{n-1})$ with each
$\sigma_i \in \mathrm{Sym}(\mathrm{Fin}(m_i))$. Define the action

$$
(\sigma \cdot c)(i) \;=\; \sigma_i(c(i)),
\qquad
(\sigma \cdot f_i)(\ell, s, r) \;=\;
  \sigma_i\bigl( f_i(\sigma_{i-1}^{-1}(\ell), \sigma_i^{-1}(s),
                     \sigma_{i+1}^{-1}(r)) \bigr).
$$

Here $(\ell, s, r)$ is the rule-table's local context triple (left
neighbour, self, right neighbour), distinct from the configuration
variable $c$. Write $\sigma \cdot f$ for the tuple $(\sigma \cdot
f_0, \ldots, \sigma \cdot f_{n-1})$. We show that
$(\mathbf{m}, f) \mapsto (\mathbf{m}, \sigma \cdot f)$ is a bijection
on systems with the same state-count vector, and that it preserves
each of the six validity properties of paper §2.3.

Throughout, "good configuration" is a label that the designer attaches
to a subset $G \subseteq \prod_i \mathrm{Fin}(m_i)$ as part of
specifying a system. When we pass from $(\mathbf{m}, f)$ to
$(\mathbf{m}, \sigma \cdot f)$ we also pass the good set to
$\sigma \cdot G := \{ \sigma \cdot c : c \in G \}$. This is the
declaration half of the bijection; the proof that it preserves the
properties is the soundness half.

---

## 2. The key commutation identity

**Lemma 2.1** *(commutation on rule evaluation).* For every
configuration $c$ and every position $i$,
$$
(\sigma \cdot f_i)\bigl( (\sigma \cdot c)(i-1),
                         (\sigma \cdot c)(i),
                         (\sigma \cdot c)(i+1) \bigr)
\;=\;
\sigma_i\bigl( f_i(c(i-1), c(i), c(i+1)) \bigr).
$$

*Proof.* Expand the left-hand side using the definition of
$\sigma \cdot f_i$:
$$
(\sigma \cdot f_i)\bigl( \sigma_{i-1}(c(i-1)),
                          \sigma_i(c(i)),
                          \sigma_{i+1}(c(i+1)) \bigr)
=
\sigma_i\bigl( f_i(\sigma_{i-1}^{-1}\sigma_{i-1}(c(i-1)),
                   \sigma_i^{-1}\sigma_i(c(i)),
                   \sigma_{i+1}^{-1}\sigma_{i+1}(c(i+1))) \bigr)
$$
$$
= \sigma_i\bigl( f_i(c(i-1), c(i), c(i+1)) \bigr).
$$
$\square$

All six property checks below are algebraic consequences of Lemma 2.1
combined with the pointwise bijectivity of each $\sigma_i$.

---

## 3. Derived commutation for the three relations the properties use

Every property in paper §2.3 is phrased in terms of three relations:
*privilege*, *unique-move*, and *move-output*. We check each commutes
with the $\sigma$-action.

**(R1) Privilege.** Processor $i$ is *privileged at $c$ under $f$*
iff $f_i(c(i-1), c(i), c(i+1)) \ne c(i)$.

By Lemma 2.1,
$$
(\sigma \cdot f_i)((\sigma \cdot c)(i-1), (\sigma \cdot c)(i), (\sigma \cdot c)(i+1))
= \sigma_i(f_i(c(i-1), c(i), c(i+1))).
$$
This is compared with $(\sigma \cdot c)(i) = \sigma_i(c(i))$. Because
$\sigma_i$ is a bijection,
$$
\sigma_i(f_i(\ldots)) \ne \sigma_i(c(i))
\;\iff\;
f_i(\ldots) \ne c(i).
$$
So $i$ is privileged at $\sigma \cdot c$ under $\sigma \cdot f$ iff $i$
is privileged at $c$ under $f$.

**(R2) Unique-move.** The number of privileged positions at $\sigma
\cdot c$ under $\sigma \cdot f$ equals the number at $c$ under $f$,
immediately from (R1).

**(R3) Move-output.** If $i$ is privileged at $c$ under $f$, the
*move-output* is the configuration $c'$ with $c'(i) = f_i(c(i-1), c(i),
c(i+1))$ and $c'(j) = c(j)$ for $j \ne i$.

At $\sigma \cdot c$ under $\sigma \cdot f$, the corresponding output
has $i$-th coordinate $\sigma_i(f_i(\ldots))$ (Lemma 2.1) and $j$-th
coordinate $(\sigma \cdot c)(j) = \sigma_j(c(j)) = \sigma_j(c'(j))$
for $j \ne i$. Hence the move-output at $\sigma \cdot c$ under
$\sigma \cdot f$ is exactly $\sigma \cdot c'$.

---

## 4. The six properties, clause by clause

We now verify the six properties of paper §2.3.

### (1) Liveness
*"In every configuration at least one processor is privileged."*

Fix $c' \in \prod_i \mathrm{Fin}(m_i)$. Because $\sigma$ acts bijectively
on configurations, there is a unique $c$ with $\sigma \cdot c = c'$.
By liveness of $f$, some $i$ is privileged at $c$ under $f$. By
(R1), that same $i$ is privileged at $c' = \sigma \cdot c$ under
$\sigma \cdot f$. $\square$

### (2) Mutual exclusion
*"In every good configuration, exactly one processor is privileged."*

Take $c' \in \sigma \cdot G$, i.e.\ $c' = \sigma \cdot c$ for some
$c \in G$. Mutual exclusion for $f$ says exactly one $i$ is privileged
at $c$ under $f$. By (R1), exactly one $i$ is privileged at $c'$ under
$\sigma \cdot f$. $\square$

### (3) Closure
*"The unique move from a good configuration leads to another good
configuration."*

For any $c \in G$, closure for $f$ says the move-output $c^\ast$ at $c$
under $f$ lies in $G$. The move-output at $\sigma \cdot c$ under
$\sigma \cdot f$ is $\sigma \cdot c^\ast$ (R3), and
$\sigma \cdot c^\ast \in \sigma \cdot G$ by definition. $\square$

### (4) Convergence
*"No daemon schedule starting from any bad configuration cycles back to
itself; equivalently, every execution reaches a good configuration in
finitely many steps."*

The *bad* configurations of $\sigma \cdot f$ are, by declaration,
$\prod_i \mathrm{Fin}(m_i) \setminus (\sigma \cdot G)$. Since $\sigma$
acts bijectively on the full configuration product and $\sigma \cdot
c' \notin \sigma \cdot G$ iff $c' \notin G$, bad configurations are
carried bijectively to bad configurations by $\sigma$. It therefore
suffices to start a daemon schedule from an arbitrary $c' \in
\prod_i \mathrm{Fin}(m_i) \setminus (\sigma \cdot G)$ and show it
reaches $\sigma \cdot G$ in finitely many steps.

A *daemon schedule* from $c'$ under $\sigma \cdot f$ is a sequence
$c' = c'_0, c'_1, c'_2, \ldots$ in which each $c'_{t+1}$ is obtained
from $c'_t$ by firing one privileged processor. Set $c_t := \sigma^{-1}
\cdot c'_t$. By (R1) the set of privileged positions at $c'_t$ equals
that at $c_t$; by (R3) firing any such position at $c'_t$ produces
exactly $\sigma \cdot (\text{its fire at } c_t)$. Hence
$(c_0, c_1, c_2, \ldots)$ is a valid daemon schedule under $f$, with
$c_0$ bad under $f$ (by the bijection above).

Convergence of $f$ says this $f$-schedule reaches a good configuration
in finitely many steps, say at step $T$: $c_T \in G$. Then
$c'_T = \sigma \cdot c_T \in \sigma \cdot G$. Cycle-back to $c'_0 = c'$
would give a schedule under $f$ cycling back to $c_0$, contradicting
convergence of $f$. $\square$

### (5) Fairness
*"Every cycle of moves through good configurations fires every
processor at least once."*

Let $(c'_0, c'_1, \ldots, c'_{L-1}, c'_0)$ be a cycle of good moves
under $\sigma \cdot f$; set $c_t := \sigma^{-1} \cdot c'_t$. By (R1)
the processor fired at step $t$ under $\sigma \cdot f$ equals the
processor fired at step $t$ under $f$; by (R3) the $f$-sequence
$(c_0, c_1, \ldots, c_{L-1}, c_0)$ is a cycle of good moves. Fairness
of $f$ says the multiset of fired processors over one cycle includes
every position in $\{0, \ldots, n-1\}$ at least once. The multiset of
fired processors is the same under $\sigma \cdot f$, so fairness
holds there too. $\square$

### (6) Legitimate-state connectedness
*"For any two good configurations $g', h' \in \sigma \cdot G$, there is
a sequence of good moves from $g'$ to $h'$."*

Let $g := \sigma^{-1} \cdot g'$, $h := \sigma^{-1} \cdot h'$.
Connectedness under $f$ gives a good-move sequence
$(g = c_0, c_1, \ldots, c_k = h)$ with every $c_t \in G$. By (R3) the
sequence $(\sigma \cdot c_0, \sigma \cdot c_1, \ldots, \sigma \cdot c_k)
= (g', \sigma \cdot c_1, \ldots, h')$ is a good-move sequence under
$\sigma \cdot f$, with every intermediate in $\sigma \cdot G$.
$\square$

---

## 5. Invertibility and bijectivity

Define $\sigma^{-1} := (\sigma_0^{-1}, \ldots, \sigma_{n-1}^{-1})$.
From the definitions,

$$
((\sigma^{-1}) \cdot (\sigma \cdot f_i))(\ell, s, r)
=
\sigma_i^{-1}\bigl( (\sigma \cdot f_i)(\sigma_{i-1}(\ell), \sigma_i(s),
                                       \sigma_{i+1}(r)) \bigr)
=
\sigma_i^{-1}\sigma_i(f_i(\ell, s, r))
=
f_i(\ell, s, r),
$$

so $\sigma^{-1} \cdot (\sigma \cdot f) = f$. Symmetrically
$\sigma \cdot (\sigma^{-1} \cdot f) = f$. Hence the action is a group
action of $\prod_i \mathrm{Sym}(\mathrm{Fin}(m_i))$ on systems with
state-count vector $\mathbf{m}$, and the map
$(\mathbf{m}, f) \mapsto (\mathbf{m}, \sigma \cdot f)$ is a bijection
on that fibre for every $\sigma$.

On good sets, the analogous computation gives $\sigma^{-1} \cdot
(\sigma \cdot G) = G$, so $G \mapsto \sigma \cdot G$ is a bijection on
designer-declared good sets with the same state-count vector.

---

## 6. Corollary

Combining §4 (property-preservation) with §5 (invertibility): the map
$(\mathbf{m}, f, G) \mapsto (\mathbf{m}, \sigma \cdot f, \sigma \cdot G)$
is a bijection between valid systems with state-count vector
$\mathbf{m}$ that preserves the good-set/cycle structure. This is the
statement of `lem:state-label-bijection`. $\square$

---

## 7. Partial renamings extend to total permutations

§§1–6 prove the statement for *total* permutations $\sigma_i \in
\mathrm{Sym}(\mathrm{Fin}(m_i))$. The exhaustive search, however,
canonicalizes at the level of *candidate good cycles*: a candidate
cycle $C$ need not visit every label of $\mathrm{Fin}(m_i)$ at
coordinate $i$, and the canonicalization pass defines a renaming only
on labels that actually appear in $C$. We bridge the two by the
standard finite-set extension argument.

**Lemma 7.1** *(extension of injective partial relabelings).* Let
$A_i \subseteq \mathrm{Fin}(m_i)$ and let $\tilde{\sigma}_i : A_i \to
\mathrm{Fin}(m_i)$ be injective. Then $\tilde{\sigma}_i$ extends to a
permutation $\sigma_i \in \mathrm{Sym}(\mathrm{Fin}(m_i))$.

*Proof.* Because $\tilde{\sigma}_i$ is injective and $A_i$ is finite,
$|\tilde{\sigma}_i(A_i)| = |A_i|$, so the complements
$\mathrm{Fin}(m_i) \setminus A_i$ and $\mathrm{Fin}(m_i) \setminus
\tilde{\sigma}_i(A_i)$ have equal (finite) cardinality $m_i - |A_i|$.
Any bijection between them — for example, the unique order-preserving
one — defines $\sigma_i$ on $\mathrm{Fin}(m_i) \setminus A_i$, and
setting $\sigma_i|_{A_i} := \tilde{\sigma}_i$ completes a permutation
of $\mathrm{Fin}(m_i)$. $\square$

Applied coordinate by coordinate: any tuple $\tilde{\sigma} =
(\tilde{\sigma}_0, \ldots, \tilde{\sigma}_{n-1})$ of injective partial
relabelings extends to a tuple $\sigma = (\sigma_0, \ldots,
\sigma_{n-1}) \in \prod_i \mathrm{Sym}(\mathrm{Fin}(m_i))$. The
cycle-level canonicalization of the search is therefore the
restriction of a genuine state-label permutation on the full rule-
table domain, and §§4–6 apply verbatim to it.

---

## 8. Extendability of partial rule tables under renaming

The search emits candidate good cycles together with their determined
dictionaries $\mathrm{detOf}(C)$; the proof pipeline then asks
whether a candidate admits a valid completion of its partial rule
table. The soundness-critical question for canonicalization is:

> *Does canonicalizing by a state-label renaming ever discard an
> extendable candidate?*

**Corollary 8.1** *(extendability is $\sigma$-equivariant).* Let $C$
be a candidate good cycle with determined dictionary
$\mathrm{detOf}(C)$, and let $\sigma \in \prod_i
\mathrm{Sym}(\mathrm{Fin}(m_i))$. Then $C$ has a valid completion
$f$ if and only if $\sigma \cdot C$ has a valid completion
$\sigma \cdot f$; moreover $\sigma \cdot \mathrm{detOf}(C) =
\mathrm{detOf}(\sigma \cdot C)$.

*Proof.* ($\Rightarrow$) Given valid $(\mathbf{m}, f, G)$ with
$C \subseteq G$, §6 produces valid $(\mathbf{m}, \sigma \cdot f,
\sigma \cdot G)$; since $\sigma \cdot C \subseteq \sigma \cdot G$,
this is a valid completion for $\sigma \cdot C$. The identity
$\sigma \cdot \mathrm{detOf}(C) = \mathrm{detOf}(\sigma \cdot C)$ is
Lemma 2.1 applied edge by edge along the cycle.

($\Leftarrow$) By $\sigma^{-1}$, pull $\sigma \cdot f$ back to $f$
and $\sigma \cdot C$ back to $C$; §5 gives the inverse direction.
$\square$

**Consequence.** If the search canonicalizes $C$ to the lex-minimum
representative $C^\ast$ of its state-label-renaming orbit and then
decides extendability of $C^\ast$, the verdict applies uniformly to
the entire orbit. A "no valid completion" verdict on $C^\ast$
therefore legitimately rejects every $C$ in the orbit; the
canonicalization does not discard any extendable candidate.

---

## 9. Use in the exhaustive search

The canonicalization pass (paper Appendix C.4, item (C2)) applies
state-label renamings *per processor, per candidate good cycle* so
that the emitted good cycle is the lex-minimum representative of its
state-label-renaming orbit. §7 justifies treating these cycle-local
renamings as total state-label permutations; §8 justifies the search
decision rule "decide extendability on the canonical representative
and lift." §4.(2) further confirms that the mutual-exclusion count
(pruning-rule `enumi:forced-neighbor`) is computed on the canonical
representative and is correct for every member of the orbit.

This is the only consumer of `lem:state-label-bijection` in the proof
pipeline. All other appearances — particularly in the verifier of
paper §5 — operate on the canonical representative directly and do
not re-invoke the bijection.
