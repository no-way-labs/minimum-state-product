# Bridge Theorem Candidates

Date: April 6, 2026

This note records the first actual bridge-theorem candidates that connect the
two-track obstruction program

- EC witness,
- shadow witness,

to a single theorem-shaped statement.

## 1. Explicit disjunctive bridge theorem on the consecutive-binary family

### Candidate A. Case 3a disjunctive bridge

On the explicit consecutive-binary subthreshold family, every valid good cycle
falls into at least one of two obstruction-producing classes:

1. **entry-conflict type**:
   the cycle has positive EC witness,
2. **shadow type**:
   the cycle has a shadow witness.

### Current evidence

For the `n=5` family `ms = (2,2,2,3,3)`, the script
`binscc_shadow_universality.py` reports:

- valid cycles: `6670`
- blocked by conflict: `210`
- blocked by shadow: `24`
- blocked by overlap only: `0`
- unblocked: `0`

So on this explicit architecture class, every valid cycle is accounted for by
the disjunction

`EC or SHADOW`.

### First explicit case-split predicate

On the same `n=5` explicit class, the cycle-level classification already comes
with a simple tested predicate:

- if the cycle has any local overlap (`any_overlap = True`), it lands on the EC
  side,
- if the cycle is overlap-free (`any_overlap = False`), it lands on the shadow
  side.

Tested summary:

- valid cycles: `6670`
- overlap / EC side: `6646`
- overlap-free shadow side: `24`
- unblocked: `0`

So the first concrete bridge predicate is:

> `P = "the cycle has some local overlap"`.

This is only an explicit-class result so far, but it is exactly the type of
predicate the universal bridge theorem will eventually need.

### Strengthening on the tested `n=5` class

On the same explicit class, the overlap-free cycles are not arbitrary:

- all `24` overlap-free cycles lie in a single dihedral orbit of the mover word

`(0,1,2,3,4,0,1,2,3,4,3,4)`.

So on this architecture class the bridge predicate is stronger than a mere
partition:

- `any_overlap = True` puts the cycle on the EC side,
- `any_overlap = False` forces the cycle into one explicit shadow-producing
  mover-word orbit.

This is the first true bridge theorem candidate on the branch:
not just one model family for each side separately, but one explicit class on
which the disjunction itself holds.

## 2. Why this matters

The branch has so far established:

- a shadow-side explicit-family theorem package,
- an EC-side explicit-family theorem package,
- and an explicit disjunctive witness theorem on the union of those packages.

Candidate A is stronger:

- it is one architecture class,
- with one cycle space,
- and every tested valid cycle in that class is blocked by one side or the
  other.

That is exactly the shape the universal theorem will need.

## 3. Immediate next steps

1. Confirm whether the same explicit bridge theorem persists for the `n=7`
   consecutive-binary class.
2. Decide whether the branch should now target:
   - a broader consecutive-binary bridge theorem,
   - or a more abstract bridge predicate explaining why a cycle falls on the EC
     side or the shadow side.

## 4. Bottom line

This is the first point at which the obstruction branch has something that
deserves the name “bridge theorem candidate,” not merely parallel witness
packages.
