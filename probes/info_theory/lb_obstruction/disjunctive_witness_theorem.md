# Explicit Disjunctive Witness Theorem

Date: April 6, 2026

This note states the first explicit disjunctive theorem candidate on the
obstruction branch.

The point is not that it solves the lower bound. The point is that it is the
first theorem-shaped object matching the actual two-track architecture:

- shadow-side witness,
- EC-side witness,
- and a single lower bound on whichever witness the system supplies.

## 1. Shadow-side explicit witness

On the explicit 3-binary `{2,3}` sweep-shadow families through `n=7`, the
shadow indicator `chi_shadow` satisfies

`ForbidFrac_{n-2}(chi_shadow) >= 71/504`.

This is the shadow-side weak global floor theorem candidate.

## 2. EC-side explicit witness

On the tested non-sweep `fc=2` BAF family through `n=8`, the derived global EC
witness `chi_conf` satisfies

`ForbidFrac_{n-2}(chi_conf) >= 37/324`.

This is the EC-side weak global bridge theorem candidate.

## 3. Immediate consequence

Since

`37/324 < 71/504`,

the common lower bound is

`min(71/504, 37/324) = 37/324`.

Therefore:

### Theorem candidate.

For every system in the union of the tested explicit obstruction classes:

- the 3-binary `{2,3}` sweep-shadow class through `n=7`,
- the tested non-sweep `fc=2` BAF class through `n=8`,

there exists a canonically defined derived witness `Phi` such that

`ForbidFrac_{n-2}(Phi) >= 37/324 > 0.1141`.

More concretely:

- in the shadow class, take `Phi = chi_shadow`,
- in the EC BAF class, take `Phi = chi_conf`.

## 4. Why this matters

This is the first theorem package on the branch that already has the **shape**
of the hoped-for universal result:

> every subthreshold system yields either
> an EC witness or a shadow witness.

The current theorem candidate is still explicit-family only, but it is no
longer split into two unrelated stories. It is one disjunctive witness
statement.

## 5. Remaining gap

To turn this into a universal theorem, one still needs a bridge theorem saying
that every subthreshold system falls into one of the two witness-producing
mechanisms, or yields a canonical witness reducing to one of them.

So this note should be read as:

- the first explicit disjunctive model theorem,
- not yet the final universal lower-bound theorem.
