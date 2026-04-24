# Consecutive-Binary Outer-Pair Flip: What Is Immediate, What Still Needs a Lemma

We fix a good cycle
\[
gc=(C_0 \xrightarrow{p_0} C_1 \xrightarrow{p_1} \cdots \xrightarrow{p_{L-1}} C_0)
\]
in a valid self-stabilizing ring, where each \(C_k\) is good and \(p_k\) is the unique privileged processor in \(C_k\).

Assume \(P_i,P_{i+1},P_{i+2}\) are binary, and define
\[
b_1=i,\qquad b_2=i+2.
\]
Let \(F\) be the involution that flips exactly these two coordinates:
\[
F(c)[b_1]=1-c[b_1],\qquad F(c)[b_2]=1-c[b_2],\qquad F(c)[j]=c[j]\ (j\neq b_1,b_2).
\]
The proposed shadow configs are
\[
S_k := F(C_k).
\]

The right conclusion is:

- Properties 1 and 4 are unconditional.
- Property 2 reduces to a specific Hamming-2 uniqueness lemma.
- Property 3 reduces to a specific local context-matching lemma on the radius-2 window around \(i\).

So the simple outer-pair flip is **not** proved from the basic axioms alone. One needs two additional structural inputs.

## Preliminary Lemma: The Changed Coordinate Is Forced

For every \(k\), the configs \(S_k\) and \(S_{k+1}\) differ at exactly the same coordinate as \(C_k\) and \(C_{k+1}\), namely \(p_k\).

**Proof.** \(C_{k+1}\) is obtained from \(C_k\) by changing only coordinate \(p_k\). The map \(F\) changes values at \(b_1,b_2\), but it does not change the set of coordinates at which two configs differ. Hence \(F(C_k)\) and \(F(C_{k+1})\) still differ only at \(p_k\). Therefore \(S_k\) and \(S_{k+1}\) differ only at \(p_k\). ∎

This lemma is important: in Property 3, the witness processor \(q\) is not arbitrary. Since a single move changes only one coordinate, any move \(S_k\to S_{k+1}\) must fire **exactly** processor \(p_k\).

So Property 3 is equivalent to:

> For every \(k\), processor \(p_k\) is privileged in \(S_k\), and firing \(p_k\) sends \(S_k\) to \(S_{k+1}\).

## Property 1: Nonempty

The list \((S_k)\) is nonempty because the good cycle is nonempty. ∎

## Property 4: Distinct

The map \(F\) is a bijection, in fact an involution. Hence
\[
S_k=S_\ell \iff F(C_k)=F(C_\ell)\iff C_k=C_\ell.
\]
Since the good-cycle configs are distinct, the shadow configs are distinct. ∎

## Property 3: Closed

Let
\[
W:=\{i-1,i,i+1,i+2,i+3\}.
\]
If \(p_k\notin W\), then the local neighborhood of \(p_k\) is unchanged by \(F\). Therefore \(p_k\) sees exactly the same triple in \(S_k\) as in \(C_k\), so it is privileged in \(S_k\) with the same output as in \(C_k\). Since \(S_k,S_{k+1}\) differ only at \(p_k\), firing \(p_k\) in \(S_k\) yields \(S_{k+1}\).

So the only difficulty is the five-site window \(W\).

### Endpoint Steps: \(p_k=i\) or \(p_k=i+2\)

Assume \(p_k=i\). Since \(P_i\) is binary, \(C_{k+1}[i]=1-C_k[i]\). But
\[
S_k[i]=1-C_k[i]=C_{k+1}[i],
\]
and the neighbors of \(i\) are unchanged between \(C_k\) and \(C_{k+1}\). Hence the full local triple of \(P_i\) in \(S_k\) is exactly the local triple of \(P_i\) in \(C_{k+1}\).

Therefore:
\[
P_i \text{ is privileged in } S_k
\iff
P_i \text{ is privileged in } C_{k+1}.
\]
Because \(C_{k+1}\) is good and has a unique privileged processor, this is equivalent to
\[
p_{k+1}=i.
\]

Thus:

> If \(p_k=i\), then Property 3 at step \(k\) is equivalent to \(p_{k+1}=i\).

The same argument gives:

> If \(p_k=i+2\), then Property 3 at step \(k\) is equivalent to \(p_{k+1}=i+2\).

So endpoint steps are **not** automatic. They require an additional immediate-repeat lemma, or some stronger local shadow lemma implying the same conclusion.

### Middle Step: \(p_k=i+1\)

Now \(S_k\) changes both neighbors of \(P_{i+1}\). The required transition is
\[
f_{i+1}(1-C_k[i],\,C_k[i+1],\,1-C_k[i+2]) = C_{k+1}[i+1].
\]
This triple is not determined by the good step \(C_k\to C_{k+1}\), because in \(C_k\) the mover \(P_{i+1}\) sees
\[
(C_k[i],\,C_k[i+1],\,C_k[i+2]),
\]
not the doubly-flipped version.

So for the middle step one needs an additional lemma of the form:

> The altered triple
> \[
> (1-C_k[i],\,C_k[i+1],\,1-C_k[i+2])
> \]
> already appears as a mover context for \(P_{i+1}\) somewhere on the good cycle, with output \(C_{k+1}[i+1]\).

Without such a context-matching lemma, Property 3 is not proved.

### Adjacent External Steps: \(p_k=i-1\) or \(p_k=i+3\)

These are similar. If \(p_k=i-1\), the required transition is
\[
f_{i-1}(C_k[i-2],\,C_k[i-1],\,1-C_k[i]) = C_{k+1}[i-1].
\]
If \(p_k=i+3\), the required transition is
\[
f_{i+3}(1-C_k[i+2],\,C_k[i+3],\,C_k[i+4]) = C_{k+1}[i+3].
\]
Again these are altered triples, not the original mover triples from the good step \(k\), so they also require a separate context-matching lemma.

### Summary for Property 3

Property 3 is fully proved only under an extra hypothesis \(H_{\mathrm{cl}}\):

> **\(H_{\mathrm{cl}}\) (local shadow-closure hypothesis).**  
> For every \(k\) with \(p_k\in W\), the altered local triple seen by \(p_k\) in \(S_k\) is already determined by the good cycle to map to \(S_{k+1}[p_k]\).

Under \(H_{\mathrm{cl}}\), Property 3 follows:

- automatically for \(p_k\notin W\);
- by the explicit local equalities above for \(p_k\in W\).

Without \(H_{\mathrm{cl}}\), the proof stops here.

## Property 2: Disjoint

This also reduces to a sharp missing lemma.

Suppose \(S_k=C_j\) for some \(j\). Since \(S_k=F(C_k)\), this means
\[
C_j = F(C_k).
\]
Equivalently, \(C_j\) and \(C_k\) agree at all coordinates except \(i\) and \(i+2\), and at those two coordinates they are complementary:
\[
C_j[r]=C_k[r]\quad (r\notin\{i,i+2\}),
\]
\[
C_j[i]=1-C_k[i],\qquad C_j[i+2]=1-C_k[i+2].
\]
So \(C_j\) and \(C_k\) differ in Hamming distance exactly \(2\), supported on \(\{i,i+2\}\).

Therefore disjointness is exactly the statement:

> **\(H_2(i,i+2)\).** No two good-cycle configs differ only at the two outer binary positions \(i\) and \(i+2\).

Under \(H_2(i,i+2)\), Property 2 is immediate.

Without \(H_2(i,i+2)\), the argument does not go through.

### Why the Basic Axioms Do Not Supply \(H_2(i,i+2)\)

The standard validity axioms do not by themselves forbid such a Hamming-2 pair:

- liveness only says every config has some privileged processor;
- mutual exclusion only says each good config has exactly one privileged processor;
- convergence talks about off-cycle dynamics, not pairwise geometry inside the good cycle;
- fairness says every processor moves somewhere on the cycle;
- \(n\ge 9\) gives room on the ring, but does not by itself exclude Hamming-2 coincidences;
- sub-threshold product is a global counting condition, not a local uniqueness lemma.

So Property 2 needs a separate structural argument, not just the five Dijkstra axioms.

An alternative sufficient route would be:

> Prove every \(S_k\) is bad, for example by showing it has at least two privileged processors.

That would also imply disjointness, because good configs have exactly one privileged processor. But that is again extra local work, not automatic from the setup.

## Conditional Theorem

If one adds the two structural hypotheses

1. \(H_{\mathrm{cl}}\): local shadow closure on the five-site window \(W\);
2. \(H_2(i,i+2)\): no good-cycle Hamming-2 pair supported on \(\{i,i+2\}\);

then the family \((S_k)\) is a valid ShadowTrap:

- Property 1: nonempty;
- Property 2: disjoint;
- Property 3: closed;
- Property 4: distinct.

The proofs are exactly those given above.

## Bottom Line

For the simple shadow
\[
S_k = F(C_k)
\]
obtained by flipping the two outer processors of a consecutive binary triple:

- Properties 1 and 4 are immediate.
- Property 2 is equivalent to an Hamming-2 uniqueness lemma.
- Property 3 is equivalent to a local context-matching lemma near the flipped block.

So the construction is **not** an unconditional theorem from the listed hypotheses alone. To finish the proof one must add, and then prove, those two structural lemmas. That is exactly where the real mathematical work sits in the consecutive-binary branch.
