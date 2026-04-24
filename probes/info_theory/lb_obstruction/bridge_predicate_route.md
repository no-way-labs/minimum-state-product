# Bridge Predicate Route

Date: April 6, 2026

This note packages the current bridge-predicate direction.

The branch now has:

- an explicit disjunctive bridge theorem candidate on the `n=5`
  consecutive-binary class,
- a concrete tested predicate

`P = any_overlap`,

- and a rigidity statement on the overlap-free side.

The goal of this note is to turn that into a clean proof program.

## 1. Current explicit bridge theorem candidate

On the explicit `n=5` consecutive-binary subthreshold class

`ms = (2,2,2,3,3)`,

every valid cycle falls into one of two classes:

1. `any_overlap = True`, hence EC-side obstruction,
2. `any_overlap = False`, hence shadow-side obstruction.

There are no unblocked cycles in the tested class.

## 2. Stronger rigidity fact

Within the same class, the overlap-free cycles are not an arbitrary residual
set.

All `24` overlap-free cycles lie in a single dihedral orbit of the mover word

`(0,1,2,3,4,0,1,2,3,4,3,4)`.

So the bridge predicate is stronger than a partition:

- overlap forces EC,
- no overlap forces a very small shadow-producing word class.

## 3. Why this matters

This is the first bridge object on the obstruction branch that already has the
shape of the hoped-for universal theorem:

> if local-overlap complexity is absent, then the cycle is forced into a
> shadow-producing regime.

That is qualitatively closer to the final lower-bound structure than merely
having two independent witness packages.

## 4. Immediate theorem target

### Explicit bridge predicate theorem (first class)

For the `n=5` consecutive-binary subthreshold class:

1. if `any_overlap = True`, then the cycle is EC-obstructed,
2. if `any_overlap = False`, then the mover word lies in the shadow-producing
   orbit above.

This theorem is still explicit-family only, but it is already bridge-shaped.

## 5. Longer-term bridge target

The natural generalization is:

> on a broader architecture class, absence of overlap forces the mover word into
> a small family of shadow-producing forms.

This would turn the disjunctive theorem from

- “either EC or shadow”

into

- “if not EC, then rigid shadow form.”

That is the most promising current bridge direction.

## 6. What remains open

1. Extend the bridge predicate beyond the explicit `n=5` class.
2. Decide whether `any_overlap` itself is the right stable predicate, or
   whether one needs a refined overlap measure.
3. Understand whether the overlap-free shadow orbit rigidity persists in a
   larger consecutive-binary class.

## 7. Bottom Line

The bridge branch now has a concrete proof route:

- not just two witnesses,
- but a first predicate that tries to explain how a cycle chooses between them.

That is the right object to keep pushing on the bridge side.
