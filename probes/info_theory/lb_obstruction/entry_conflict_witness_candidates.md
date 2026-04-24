# Entry-Conflict Witness Candidates

Date: April 6, 2026

This note records the parallel obstruction track that is currently missing from
the information-theory lower-bound branch.

The lower-bound architecture has two main obstruction types:

1. **entry conflict (EC)**
2. **shadow-type bad-cycle obstruction**

The present obstruction package is strong on the shadow side and weak on the EC
side. This note defines the EC-side targets so the branch no longer treats
shadow as the whole story.

## 1. Why EC needs its own track

An information-theory lower-bound program that only models shadow-type
obstructions is incomplete.

Entry conflict is conceptually different:

- shadow obstruction is a bad-set / forced-move phenomenon,
- entry conflict is a good-cycle local-context collision phenomenon.

So if the branch aims at a universal witness theorem, the candidate witness
should probably be **disjunctive**:

- either an EC witness,
- or a shadow witness,
- or both.

## 2. Canonical EC viewpoint

Fix a good cycle `g_0, ..., g_{CL-1}` and processor `i`.

Define:

- local context at step `k`:
  `C_i(k) = (g_k[i-1], g_k[i], g_k[i+1])`
- mover bit:
  `R_i(k) = 1[moverAt(k) = i]`

Entry-conflict freedom at processor `i` is exactly:

- mover and non-mover context supports are disjoint,
  equivalently
- `R_i` is zero-error decodable from `C_i`.

So the EC-side obstruction should come from the failure of zero-error
decodability.

## 3. Candidate EC witnesses

These are candidates for a canonical EC witness attached to a system or good
cycle.

### Candidate A. Overlap indicator at a processor

For processor `i`, define

`EC_i = 1[supp(C_i | R_i = 1) ∩ supp(C_i | R_i = 0) != ∅]`.

This is the most literal EC witness.

Strength:

- exact match to the combinatorial notion.

Weakness:

- too coarse as a scalar,
- not obviously suitable for ANOVA / forbidden-mass analysis.

### Candidate B. Overlap count at a processor

Define

`ov_i = |supp(C_i | R_i = 1) ∩ supp(C_i | R_i = 0)|`.

This is a more quantitative EC witness.

Strength:

- counts how many colliding local contexts occur.

Weakness:

- still tied to the good cycle rather than the full configuration space.
- if promoted directly to a scalar on full configuration space by testing
  whether the local context at processor `i` lies in the overlap set, it is a
  width-3 local observable and therefore has zero width-`n-2` forbidden mass.

### Candidate C. EC overlap profile

Define the vector

`OV = (ov_0, ..., ov_{n-1})`.

This keeps the processorwise localization of the EC obstruction.

Potential use:

- the right witness might not be a single scalar but a profile, with a scalar
  extracted from it later.

Same warning:

- any direct profile made only of local overlap indicators remains width-3
  local, so it will be invisible to the same forbidden-mass obstruction used on
  the shadow side.

### Candidate D. Confusability-edge count

Define the bipartite graph at processor `i`:

- left vertices: mover appearances,
- right vertices: non-mover appearances,
- edge when the local contexts are identical.

Let `e_i` be the number of edges in this graph, and set

`E_conf = Σ_i e_i`.

Strength:

- directly tied to the zero-error coding interpretation.

Potential advantage:

- may interact more naturally with product-measure / spectral formulations than
  support-overlap counts do.

This is now the leading EC-side candidate, precisely because the naive local
overlap indicators are too local for the current forbidden-mass observable.

### Candidate E. Conflict-state indicator

Define the set of good-cycle states that participate in an EC overlap witness:

- a good state `g_t` belongs to `ConfState` if there exists some processor `p`
  such that the local triple of `g_t` at `p` lies in `M_p ∩ N_p`.

Define the full-space indicator

`chi_conf(c) = 1[c in ConfState]`.

This is no longer width-3 local, because membership asks whether the whole
configuration is one of the specific global cycle states participating in a
conflict witness.

This is now the leading candidate for reconnecting the EC track to the
forbidden-mass observable.

Current status:

- on the canonical BAF family, `chi_conf` has substantial nonzero
  width-`n-2` forbidden mass,
- and on the tested broader non-sweep `fc=2` BAF family through `n=8`, it
  remains uniformly positive.

So `chi_conf` is now the leading EC-side candidate for partial reunification
with the shadow-side observable.

## 4. First negative result

For canonical BAF-style EC examples on

- `ms = (2,2,2,3,3)`,
- `ms = (2,2,2,3,3,3)`,

the natural full-space EC scalar

`total_overlap(c) = Σ_i 1[(c_{i-1}, c_i, c_{i+1}) in O_i]`

has width-`n-2` forbidden fraction exactly `0`.

This is expected: it is a sum of width-3 local terms.

So the current shadow-side forbidden-mass observable does **not** directly
capture naive EC witnesses.

However, the first derived nonlocal EC quantity already changes the picture:

- for the canonical BAF family, the conflict-state indicator has substantial
  nonzero width-`n-2` forbidden mass through the tested range.

So the right lesson is not “EC cannot be seen spectrally,” but rather:

- **raw local EC witnesses are spectrally invisible,**
- **derived global consequences of EC may not be.**

## 5. Consequence for the universal witness program

The likely universal theorem shape is not:

> one witness scalar measured by one common forbidden-mass quantity.

It is more likely one of:

1. a disjunctive theorem with two different witness quantities:
   - shadow-side witness measured by forbidden mass,
   - EC-side witness measured by zero-error/confusability quantity;
2. or a more sophisticated EC witness that is no longer width-3 local;
3. or a partial reunification in which a derived global EC quantity is again
   measured by forbidden mass.

The current best candidate for option (3) is precisely `chi_conf`.

## 6. What a universal EC theorem would look like

The EC-side branch should aim at one of the following theorem shapes.

### Theorem shape 1. Universal EC witness

Every subthreshold system canonically yields an EC witness `Psi_S` such that:

- `Psi_S = 0` for valid systems,
- `Psi_S > 0` for EC-obstructed systems,
- and `Psi_S` has a forbidden-mass floor or another product-measure signature.

### Theorem shape 2. Disjunctive witness theorem

Every subthreshold system yields either:

- an EC witness with positive obstruction mass,
  or
- a shadow witness with positive obstruction mass.

This is the most faithful theorem shape if EC and shadow remain genuinely
separate mechanisms.

## 7. Immediate next EC tasks

1. Decide which EC witness candidate is most plausible as a spectral object:
   `EC_i`, `ov_i`, `OV`, `E_conf`, or `chi_conf`.
2. Test it on explicit EC-killed families already known in the lower-bound
   proof architecture.
3. Compare its behavior with the shadow-side forbidden-mass scalars.

## 8. Bottom Line

The current information-theory obstruction branch must explicitly bifurcate:

- **shadow witness track**
- **entry-conflict witness track**

Without the EC track, the branch does not reflect the actual lower-bound
mechanism split and risks optimizing around only half the theorem.
