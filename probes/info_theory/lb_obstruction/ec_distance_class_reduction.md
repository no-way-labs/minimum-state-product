# EC Distance-Class Reduction

Date: April 6, 2026

This note isolates the first real symmetry reduction for the EC bridge object
`chi_conf`.

The main point is that, on the anchored consecutive-binary family `{0,1,2}`,
reflection about the middle binary processor `1` reduces the simple
two-turnaround BAF family to one representative per distance-to-`1` class.

## 1. Setup

Fix:

- `n >= 5`,
- the anchored state multiset
  `ms = (2,2,2,3,...,3)`,
- and the ring reflection

`rho(i) = 2 - i (mod n)`.

Because `rho` preserves the anchored binary block `{0,1,2}`, we have

`m_{rho(i)} = m_i`

for every coordinate `i`.

So `rho` induces a coordinate permutation of the full configuration space

`Sigma_rho(x)_i = x_{rho(i)}`.

For the simple two-turnaround BAF family, let `W_v` denote the canonical cyclic
mover word whose turnaround vertex is `v`, normalized so the displayed word
starts at processor `0`.

## 2. Ring-Automorphism Invariance

### Proposition 2.1. Reflection preserves forbidden interaction fraction.

Let `f` be any scalar on the full configuration space for the anchored multiset
above. Then

`ForbidFrac_{n-2}(f ∘ Sigma_rho) = ForbidFrac_{n-2}(f)`.

#### Proof

The map `Sigma_rho` is a measure-preserving bijection of the finite product
space, so it preserves `L^2` norm.

If a function depends only on coordinates in a support `S`, then after
precomposition with `Sigma_rho` it depends only on coordinates in
`rho^{-1}(S)`. Hence the ANOVA subspace indexed by `S` is carried isometrically
to the ANOVA subspace indexed by `rho^{-1}(S)`.

Because `rho` is a dihedral automorphism of the cycle, it carries contiguous
windows of width `n-2` to contiguous windows of width `n-2`. Therefore a
support is allowed exactly when its reflected support is allowed. So the
allowed/forbidden split is preserved, and the forbidden-energy fraction is
unchanged. ∎

## 3. Reflection on the Simple BAF Family

### Proposition 3.1. Reflection preserves the simple two-turnaround BAF family.

On the simple two-turnaround BAF family, reflection by `rho` sends the cyclic
word `W_v` to the cyclic word `W_{rho(v)}`.

Equivalently, after coordinate reflection and cyclic renormalization to start at
processor `0`, the family is closed and the turnaround vertex transforms by

`v -> 2 - v (mod n)`.

#### Proof sketch

The simple BAF family is the family of two-turnaround back-and-forth cyclic
walks on the ring with the anchored consecutive-binary block `{0,1,2}`.

Reflection by `rho`:

- preserves adjacency on the cycle,
- preserves the anchored binary block as a set,
- reverses clockwise/counter-clockwise orientation,
- and therefore carries a two-turnaround back-and-forth walk to another
  two-turnaround back-and-forth walk.

The turnaround vertex `v` is sent to `rho(v) = 2-v (mod n)`.
Finally, cyclic renormalization of the displayed word only changes the starting
step, not the underlying cyclic mover word. ∎

## 4. Distance-Class Reduction

### Corollary 4.1. Reflection pairs the distance classes.

Let

`d(v) = dist_{C_n}(v, 1)`.

Then

`d(rho(v)) = d(v)`.

Moreover, every distance class is exactly:

- the singleton `{1}` when `d = 0`,
- the singleton `{1 + n/2}` when `n` is even and `d = n/2`,
- or the pair `{1-d, 1+d}` modulo `n`.

So reflection gives a full reduction to one representative per distance class.

#### Proof

The equality `d(rho(v)) = d(v)` is immediate because `rho` fixes `1` and is an
isometry of the cycle.

The description of the distance classes is the standard classification of
cyclic-distance fibers from a fixed basepoint on `C_n`. ∎

### Corollary 4.2. The EC bridge value is constant on each reflection class.

For the simple two-turnaround BAF family,

`ForbidFrac_{n-2}(chi_conf(W_v)) = ForbidFrac_{n-2}(chi_conf(W_{rho(v)}))`.

Hence `ForbidFrac_{n-2}(chi_conf)` is constant on each distance-to-`1` class.

#### Proof

By Proposition 3.1, reflection sends `W_v` to `W_{rho(v)}`.
By Proposition 2.1, forbidden interaction fraction is unchanged under the
induced coordinate reflection on the full configuration space.
So the two words have the same forbidden fraction. Corollary 4.1 then reduces
the statement to distance classes. ∎

### Computational Corollary 4.3. Full small-fiber minima already match the simple representatives.

On the tested range `n=5,6,7`, the minimum value of
`ForbidFrac_{n-2}(chi_conf)` inside each distance-to-`1` class on the full
valid fiber agrees exactly with the value obtained from the simple
state-sequence representative `W_v`.

So on the solved small range, the distance-class reduction is not merely a
reduction of the simple model family: it already captures the full class
minima.

## 5. Computational Audit

### 5.1 Canonical representatives

For each distance class `d in {0,1,...,floor(n/2)}`, choose the representative
with turnaround vertex

`v_d = 1 + d`.

For `v in {1,...,n-1}`, define the canonical simple two-turnaround BAF word

`W_v = [0,1,...,v, v-1,...,0, n-1,n-2,...,v, v+1,...,n-1]`.

Then the distance-class representative is

`W_d := W_{1+d}`.

By Corollary 4.2, every simple two-turnaround BAF word is reflection-equivalent
to exactly one of these representatives.

`ec_turnaround_reflection_probe.py` verifies the reflection pairing:

- simple two-turnaround family through `n=9`,
- full valid-fiber minima through `n=7`.

It also verifies the simple-vs-full class comparison through `n=7`:

- `n=5`: 3 classes, 0 failures
- `n=6`: 4 classes, 0 failures
- `n=7`: 4 classes, 0 failures

Observed distance-class tables on the simple family:

- `n=5`:
  - distance `0`: `0.166666666667`
  - distance `1`: `0.166666666667`
  - distance `2`: `0.115740740741`
- `n=6`:
  - distance `0`: `0.148148148148`
  - distance `1`: `0.175925925926`
  - distance `2`: `0.131944444444`
  - distance `3`: `0.129629629630`
- `n=7`:
  - distance `0`: `0.129629629630`
  - distance `1`: `0.153086419753`
  - distance `2`: `0.137037037037`
  - distance `3`: `0.129012345679`
- `n=8`:
  - distance `0`: `0.114197530864`
  - distance `1`: `0.135802469136`
  - distance `2`: `0.125857338820`
  - distance `3`: `0.126886145405`
  - distance `4`: `0.118141289438`
- `n=9`:
  - distance `0`: `0.101900842642`
  - distance `1`: `0.122476974329`
  - distance `2`: `0.118312757202`
  - distance `3`: `0.119145600627`
  - distance `4`: `0.116696061141`

These values are generated directly on the canonical representatives by:

- `ec_distance_class_values.py`.

## 6. Why this matters

This is the first actual symmetry reduction for the EC bridge theorem.

The weak bridge theorem is no longer an uncontrolled word-by-word statement.
It is now reduced to:

1. the broader BAF support theorem,
2. one representative per distance-to-`1` class.

What remains open is to explain the **value** attached to each distance class,
or at least prove a uniform lower bound across those classes.
