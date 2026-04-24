# Entry-Conflict Obstruction Theorem Package

Date: April 6, 2026

This note packages the first explicit-family theorem on the EC side of the
information-theory lower-bound branch.

Unlike the shadow-side package, this branch is not naturally captured by the
width-`n-2` forbidden-mass observable. The right quantity here is a zero-error /
confusability witness on the good cycle itself.

## 1. Setup

Fix:

- `n >= 5`,
- the canonical BAF mover word

`w = [0,1,...,n-1,n-2,...,1,0,n-1]`,

- and the canonical state vector

`ms = (2,2,2,3,...,3)`

with binary processors at positions `0,1,2`.

Let `C = (g_0, ..., g_{2n-1})` be the canonical BAF cycle built from the simple
state sequences `[0,1,0]` at every processor.

For processor `p`, define:

- mover-context set
  `M_p = { (g_t[p-1], g_t[p], g_t[p+1]) : w_t = p }`,
- non-mover-context set
  `N_p = { (g_t[p-1], g_t[p], g_t[p+1]) : w_t != p }`.

Define the processorwise overlap count

`ov_p = |M_p ∩ N_p|`

and the total EC witness

`E_conf = Σ_p ov_p`.

Validity requires `ov_p = 0` for every processor `p`.

## 2. Theorem Statement

### Theorem A. Canonical BAF overlap law.

For the canonical BAF family above, every interior processor

`p in {1, ..., n-3}`

has overlap count

`ov_p = 2`,

while the remaining processors have

`ov_p = 0`.

Hence the total confusability-edge count is

`E_conf = 2(n-3)`.

In particular, the EC witness is strictly positive for every `n >= 5`, so the
canonical BAF family is entry-conflict obstructed.

### Theorem candidate B. General BAF overlap law.

For any non-sweep `w = 0` / `fc = 2` BAF word on `C_n` with a consecutive binary
triple at `{0,1,2}`, at least one interior processor has mover/non-mover
context overlap, hence

`E_conf > 0`.

This is the witness-theoretic restatement of the palindromic entry-conflict
theorem.

More sharply, if the two turnarounds cut the ring into arcs of lengths `d` and
`n-d`, then the natural palindromic count heuristic gives

`(# conflicting processors) >= max(0,d-2) + max(0,n-d-2) = n-4`.

The weaker conclusion `E_conf > 0` is the clean symbolic theorem target.

### Status of Theorem candidate B

- symbolic proof idea: already present in the palindromic EC argument,
- computational audit: `cic_case3a_proof5.py` reports that all non-sweep
  `fc=2` words are killed through the tested range,
- the sharper `n-4` count should still be treated as a candidate until written
  more cleanly.

### Computational strengthening

On the tested range `n = 5, ..., 9`, the stronger count appears rigid:

- for every non-sweep `fc=2` word in the tested family,
- and for every valid state-sequence realization of that word,

the total confusability witness is

`E_conf = 2(n-3)`.

So the current computational picture is stronger than mere positivity:
the canonical BAF law appears to persist unchanged across the whole tested
non-sweep `fc=2` class.

### Theorem candidate C. Conflict-state indicator has nonzero forbidden mass.

Let `ConfState` be the set of good-cycle states participating in an EC overlap
at some processor, and define

`chi_conf(c) = 1[c in ConfState]`.

For the canonical BAF family, `chi_conf` is a nonlocal EC-derived scalar and
its width-`n-2` forbidden fraction is substantial on the tested range:

- `n=5`: `0.115741`
- `n=6`: `0.131944`
- `n=7`: `0.137037`
- `n=8`: `0.125857`

So although the raw local overlap scalar is spectrally invisible, a derived
global consequence of EC is not.

### Theorem C'. Canonical conflict-state geometry.

For the canonical BAF family, the conflict states are exactly the good-cycle
states with indices

`{1,2,...,n-2} ∪ {n+1,n+2,...,2n-2}`.

Equivalently, they are all good-cycle states except the four distinguished
turnaround / endpoint states

`g_0, g_{n-1}, g_n, g_{2n-1}`.

Hence

`|ConfState| = 2n - 4`.

This is the clean symbolic form of the conflict-state witness on the canonical
BAF family.

Equivalently, if for each interior processor `j` we set

`A_j = {j, j+1, 2n-2-j, 2n-1-j}`,

then

`ConfState = ⋃_{j=1}^{n-3} A_j`.

This is the processorwise decomposition of the support.

#### Proof

For each interior processor `j in {1, ..., n-3}`, the palindromic EC mechanism
produces exactly two overlap contexts:

- `(1,0,0)`,
- `(1,1,0)`.

These occur at four step positions:

- step `j`, where processor `j` itself moves on the clockwise pass and sees
  `(1,0,0)`,
- step `j+1`, where processor `j` is a non-mover while `j+1` fires on the
  clockwise pass and sees `(1,1,0)`,
- step `2n-2-j`, where processor `j` itself moves on the counter-clockwise
  pass and sees `(1,1,0)`,
- step `2n-1-j`, where processor `j` is a non-mover while the neighboring
  processor fires on the counter-clockwise pass and sees `(1,0,0)`.

So for each interior processor `j`, the conflict-step set is exactly

`A_j = {j, j+1, 2n-2-j, 2n-1-j}`.

Taking the union over all interior processors gives

`ConfState = ⋃_{j=1}^{n-3} A_j`.

Now

- `⋃_{j=1}^{n-3} {j, j+1} = {1,2,...,n-2}`,
- `⋃_{j=1}^{n-3} {2n-2-j, 2n-1-j} = {n+1,n+2,...,2n-2}`.

Hence

`ConfState = {1,2,...,n-2} ∪ {n+1,n+2,...,2n-2}`,

which is exactly the complement of the four distinguished states

`g_0, g_{n-1}, g_n, g_{2n-1}`.

Therefore `|ConfState| = 2n-4`. ∎

### Theorem C''. General BAF conflict-state geometry.

For a general non-sweep `fc=2` BAF word, let the two turnaround steps in the
cyclic mover word be `t_1` and `t_2`.

Then on the tested BAF family, the conflict-state set appears to be exactly the
complement of the four distinguished good-cycle steps

`{t_1, t_1+1, t_2, t_2+1}`  (mod `2n`).

Equivalently:

`ConfState = {g_0, ..., g_{2n-1}} \ {g_{t_1}, g_{t_1+1}, g_{t_2}, g_{t_2+1}}`.

So again

`|ConfState| = 2n - 4`.

This is the natural broader geometric extension of the canonical support
formula.

### Proof

The proof is given in `ec_baf_support_theorem.md`.

In brief:

1. for each non-turnaround processor `j`, with firing times `u_j < v_j`, the
   processor `j` witnesses conflict exactly on the four steps
   `{u_j, u_j+1, v_j, v_j+1}`,
2. taking the union over all non-turnaround processors gives the full
   conflict-state set,
3. this union simplifies to the complement of the two turnarounds and their
   immediate successors.

### Computational audit of Theorem C''

`ec_conflict_geometry_probe.py` verifies on the tested range `n=5..8` that for
every non-sweep `fc=2` BAF word:

- if the turnaround steps are `t_1, t_2`,
- then the conflict states are exactly the complement of
  `{t_1, t_1+1, t_2, t_2+1}`.

Audit summary:

- `n=5`: 5 non-sweep words, 0 failures
- `n=6`: 10 non-sweep words, 0 failures
- `n=7`: 7 non-sweep words, 0 failures
- `n=8`: 12 non-sweep words, 0 failures
- `n=9`: 9 non-sweep words, 0 failures

### Corollary C'''. Canonical subtraction formula.

On the canonical BAF family, let:

- `chi_good` be the indicator of the good cycle,
- `chi_exc` be the indicator of the four exceptional states
  `g_0, g_{n-1}, g_n, g_{2n-1}`.

Then

`chi_conf = chi_good - chi_exc`.

So the EC bridge object is literally the good-cycle indicator with the four
distinguished turnaround / endpoint states removed.

This gives a clean structural bridge from the EC witness to the cycle-spectrum
side of the program.

### Computational strengthening of Theorem candidate C

On the tested non-sweep `fc=2` BAF family through `n=7`, the derived global EC
witness `chi_conf` remains uniformly separated from zero:

- `n=5`: minima in the range `0.115741 .. 0.166667`
- `n=6`: minima in the range `0.129630 .. 0.175926`
- `n=7`: minima in the range `0.129012 .. 0.153086`

So the EC-side forbidden-mass phenomenon is not confined to the single
canonical BAF word; it persists across the whole tested non-sweep `fc=2`
family.

### Theorem candidate D. Weak global EC bridge law on the tested BAF family.

Across the tested non-sweep `fc=2` BAF family through `n=8`,

`ForbidFrac_{n-2}(chi_conf) >= 37/324 > 0.1141`.

This is the current EC-side analogue of the weaker global shadow-floor law.

It is weaker than the exact class-by-class values, but stronger as a bridge
statement: it says the derived global EC witness is uniformly visible to the
forbidden-mass observable across the whole tested BAF family.

### Route correction for Theorem candidate D

The broader BAF support theorem does **not** by itself determine the value of
`ForbidFrac_{n-2}(chi_conf)`.

The new probe `ec_bridge_geometry_probe.py` shows that even within the simple
two-turnaround BAF family:

- every tested word through `n=9` has the same coarse turnaround-gap class
  `(n,n)`,
- every tested word has the same support cardinality `|ConfState| = 2n-4`,
- but the forbidden fractions still vary across words.

So the weak bridge theorem must depend on **turnaround placement geometry** in
addition to the support formula.

### New placement-invariant candidate

The same probe now suggests a sharper invariant:

- on the simple two-turnaround BAF family through `n=9`,
- and on the full valid-fiber minima through `n=7`,

the value of `ForbidFrac_{n-2}(chi_conf)` appears to depend only on the cyclic
distance from the turnaround vertex to the middle binary processor `1`.

So the next EC-side bridge theorem should be phrased not in terms of the coarse
support formula alone, but in terms of:

- the broader BAF support theorem,
- plus the turnaround-distance-to-`1` placement class.

This first reduction is now recorded in:

- `ec_distance_class_reduction.md`,

which gives the reflection argument fixing the middle binary processor `1` and
reduces the simple two-turnaround BAF family to one representative per
distance-to-`1` class.

Moreover, on the solved small range `n=5,6,7`, the full valid-fiber minima in
each distance class already agree with those simple representatives.

The representatives can now be written explicitly:

- for `d in {0,...,floor(n/2)}`, take turnaround vertex `v_d = 1+d`,
- define
  `W_v = [0,1,...,v, v-1,...,0, n-1,...,v, v+1,...,n-1]`,
- and set `W_d = W_{1+d}`.

So the weak EC bridge theorem is now reduced to analyzing
`ForbidFrac_{n-2}(chi_conf(W_d))`.

There is now also a coefficient-level bridge route:

- `ec_mask_family_route.md`

records a tiny anchored forbidden-mask family which has positive ANOVA energy on
every tested representative `W_d` through `n=9`.

This has now been sharpened to an explicit basis-coefficient route:

- `ec_basis_coefficient_route.md`

defines the product basis vector

`Psi_d(x) = Π_{i in S_d} (1[x_i=0] - 1/m_i)`

on the candidate support `S_d`, and verifies through `n=11` that

`<chi_conf(W_d), Psi_d> != 0`.

The candidate complements are:

- `d=0`: `{1}`,
- `d>0` even: `{1,d+1}`,
- `d` odd: `{0,d+1}` or `{2,d+1}`.

This is now promoted to an exact representative theorem in:

- `ec_basis_coefficient_theorem.md`

which gives a closed-form formula for `<chi_conf(W_d), Psi_d>` and proves the
exact sign pattern:

- `d=0`: positive
- odd `d`: positive
- even `d >= 2`: negative

Hence `<chi_conf(W_d), Psi_d>` is nonzero for every `d`, and the candidate
forbidden support already carries positive forbidden energy on every
representative `W_d`.

However, this representative theorem does not yet lift coefficientwise to the
full tested BAF fibers:

- on the small full-fiber checks `n=5,6,7`, the same coefficient can change
  sign across valid goods in a fixed distance class,
- and at `n=6`, distance class `d=2`, no simple local product basis choice on
  that same support survives across all valid goods.

So the next lift theorem must be formulated at the level of support-energy or a
more flexible basis family, not as a rigid single-coefficient theorem on the
whole tested class.

The first concrete support-level route is now packaged in:

- `ec_support_lift_route.md`,

whose main example is the problematic class `n=6, d=2`: even there, one finds
multiple tiny forbidden supports with the same positive energy across all 16
valid goods in the class.

This now has a first genuine theorem on the full tested class:

- `ec_smallrange_support_lift_theorem.md`

which proves through `n=9` that:

- if `d=0` or `d=2`, the singleton complement `{1}` works,
- if `d=1`, the pair complement `{0,2}` works,
- if `d=3`, the singleton complement `{0}` works, and by reflection so does
  `{2}`,
- and at `n=8,9`, the next even class still uses the singleton complement
  `{1}`.

This also sharpens the status of the old finite-range bridge constant.

The tested theorem candidate

`ForbidFrac_{n-2}(chi_conf) >= 37/324`

is still correct on the tested BAF family through `n=8`, but the representative
table already shows it is not the right asymptotic target: on the simple family
at `n=10`, the minimum class value is `0.091306584362`.

So the next symbolic EC bridge target should be:

- positivity of `ForbidFrac_{n-2}(chi_conf(W_d))`,
  or
- an explicit `n`-dependent lower bound,

not a universal constant across all `n`.

### Canonical comparison with `chi_good`

On the canonical BAF family, the forbidden fractions are:

- `chi_good`:
  - `n=5`: `0.136111`
  - `n=6`: `0.121914`
  - `n=7`: `0.120811`
  - `n=8`: `0.115226`
  - `n=9`: `0.108406`
- `chi_conf`:
  - `n=5`: `0.115741`
  - `n=6`: `0.131944`
  - `n=7`: `0.137037`
  - `n=8`: `0.125857`
  - `n=9`: `0.118313`
- `chi_exc` (the exceptional four-state indicator):
  - `n=5`: `0.319444`
  - `n=6`: `0.319444`
  - `n=7`: `0.288580`
  - `n=8`: `0.260288`
  - `n=9`: `0.238169`

So `chi_conf` stays of the same spectral scale as `chi_good`, while the removed
exceptional four-state piece is even more nonlocal.

## 3. Proof Idea

This is just the palindromic EC mechanism rewritten as a witness theorem.

For each interior processor `p`:

1. on the clockwise pass, when processor `p+1` fires, processor `p` is a
   non-mover and sees a context of the form

   `(x_{p-1}, x_p, 0)`,

2. on the counter-clockwise pass, when processor `p` fires back, it again sees
   the same local context

   `(x_{p-1}, x_p, 0)`,

3. but one occurrence is non-mover and the other is mover,
4. so this context lies in both `M_p` and `N_p`.

In the canonical simple-state family, there are exactly two such overlapping
contexts at each interior processor:

- `(1,0,0)`,
- `(1,1,0)`.

So `ov_p = 2` for every interior `p`.

The endpoints and the top processor do not participate in the same palindromic
interior mechanism, so their overlap counts vanish in this canonical family.

## 4. Computational Audit

`ec_witness_probe.py` verifies exactly:

- conflict processors are `{1, ..., n-3}`,
- `ov_p = 2` on those processors,
- total overlap is `2(n-3)`,

for `n = 5,6, ..., 12`.

The resulting totals are:

- `n=5`: `4`
- `n=6`: `6`
- `n=7`: `8`
- `n=8`: `10`
- `n=9`: `12`
- `n=10`: `14`
- `n=11`: `16`
- `n=12`: `18`

`ec_baf_universality_probe.py` verifies on the tested range `n=5..9` that the
minimum `E_conf` over all non-sweep `fc=2` words is always exactly `2(n-3)`:

- `n=5`: minima `{4: 5}`
- `n=6`: minima `{6: 6}`
- `n=7`: minima `{8: 7}`
- `n=8`: minima `{10: 8}`
- `n=9`: minima `{12: 9}`

## 5. Why This Matters

This is the first explicit-family EC theorem package on the obstruction branch.

It shows that the lower-bound information-theory program really does need two
tracks:

- shadow-side witness:
  forbidden width-`n-2` mass,
- EC-side witness:
  zero-error/confusability overlap.

The EC witness is not visible to the current forbidden-mass observable because
the naive full-space overlap scalar is width-3 local. But it is still a clean
and growing obstruction quantity.

Theorem candidate C changes the picture: the EC side may reconnect to the
forbidden-mass observable at the level of global conflict-state structure, even
though the raw local overlap witness does not.

Theorem candidate B matters because it points toward the broader EC track:

- Theorem A is a model-case law,
- Theorem candidate B is the first plausible bridge from that model case to the
  full EC theorem architecture.

Theorem candidate C now strengthens that bridge:

- the EC track is not confined to a zero-error observable only,
- a derived global EC quantity can also be seen by the forbidden-mass
  observable on the tested family.

Theorem candidate C' further strengthens it:

- `chi_conf` is not only nonlocal,
- it has a simple geometric description on the canonical BAF family.

Theorem candidate C'' strengthens it further:

- the support geometry appears to be word-level, not just canonical-word
  specific.

## 6. Best Current Use

The theorem should be used as:

- the EC-side model case,
- parallel to the shadow-floor model case,
- in a future disjunctive witness theorem:

> every subthreshold system yields either an EC witness or a shadow witness.

## 7. What Remains Open

1. Identify the right canonical EC witness for arbitrary subthreshold systems,
   not just the canonical BAF family.
2. Decide whether `E_conf` itself is the right EC-side quantity, or whether one
   needs a more invariant confusability complexity.
3. Relate the explicit BAF overlap law to the broader EC theorem architecture
   already used in the lower-bound proof.
