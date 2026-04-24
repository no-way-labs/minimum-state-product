# Shadow-Floor Symbolic Route

Date: April 6, 2026

This note records an important proof-engineering correction for the explicit
shadow-floor theorem.

## 1. The subtlety

The current equivariance plan in
`shadow_floor_equivariance_lemmas.md` is framed around the algorithm

`find_shadow_cycle`.

That is useful computationally, but it is not the cleanest symbolic object.

Why not?

`find_shadow_cycle` does two conceptually different things:

1. it expresses the local forced-move rule,
2. it also performs a global search over starting configurations in product
   order and returns the first shadow cycle it encounters.

The first part is local and relabeling-stable.
The second part depends on a global enumeration order on configurations, and
that order is not obviously preserved by coordinatewise ternary relabeling.

So a direct symbolic proof of

`map tau (find_shadow_cycle(...)) = find_shadow_cycle(...)`

is more awkward than it first appears.

## 2. Better object: the explicit shadow family

The paper proof of the shadow theorem does not define the shadow cycle by
search. It defines it explicitly, via the shifted waterfall formulas
for the shadow configurations:

- the good sweep `g_j`,
- the shift data `d_i`,
- and the shadow configurations `s_k(i)`.

This is the right symbolic object.

Advantages:

1. It is defined by explicit formulas, not by search order.
2. Coordinatewise ternary relabeling acts pointwise on those formulas.
3. The five desired properties
   - closure,
   - movers,
   - distinctness,
   - disjointness,
   - determined-entry usage
   are all already stated in the paper proof in terms of this explicit family.

So the clean symbolic route to the shadow-floor theorem is:

1. define the explicit shadow family `S_{m,epsilon}` by formula,
2. prove that ternary relabeling transports that explicit family,
3. use relabeling invariance of forbidden fraction,
4. use `find_shadow_cycle` only as a corroborative audit that the search script
   rediscovers the same shadow object on the tested families.

## 3. Revised proof architecture

### Symbolic side

Prove:

1. coordinatewise relabeling preserves forbidden interaction fraction,
2. the explicit sweep family transports under ternary relabeling,
3. the explicit shadow family transports under ternary relabeling,
4. therefore shadow-indicator forbidden fraction is assignment-invariant within
   a binary-placement class.

### Computational side

For one representative ternary assignment in each binary-placement class:

1. compute the exact forbidden fraction,
2. record the exact rational value,
3. derive the global floor `>= 71/504`.

### Audit side

Retain `shadow_equivariance_check.py` as corroboration that the search routine
returns the transported cycle on the tested cases, but do not make that
algorithmic commutation the main symbolic theorem.

## 4. Consequence for Lean

This is better for Lean too.

Lean prefers:

- explicit formulas,
- pointwise transport lemmas,
- local equalities,

over:

- proofs about a search routine returning the first object in an enumeration.

So the formalization target should be:

- the explicit shadow family from the paper proof,
not
- the `find_shadow_cycle` search procedure.

## 5. New branch rule

Use `find_shadow_cycle` for:

- discovery,
- computational audits,
- representative-class certification.

Use the explicit shadow formulas for:

- symbolic proofs,
- Lean-facing lemmas,
- and the final paper theorem.
