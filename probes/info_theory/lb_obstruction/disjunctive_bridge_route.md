# Disjunctive Bridge Route

Date: April 6, 2026

This note states the current best route from the explicit obstruction packages
to a genuine lower-bound bridge theorem.

The key insight is that the branch now has:

- a shadow-side weak floor theorem candidate,
- an EC-side weak bridge theorem candidate,
- and the first explicit bridge predicate on one architecture class.

So the next theorem target should no longer be phrased vaguely as
“universalize the witnesses.” It should be phrased as a **disjunctive bridge
program**.

## 1. Current explicit theorem pieces

### Shadow side

On the tested explicit 3-binary `{2,3}` sweep-shadow families through `n=7`:

`ForbidFrac_{n-2}(chi_shadow) >= 71/504`.

### EC side

On the tested non-sweep `fc=2` BAF family through `n=8`:

`ForbidFrac_{n-2}(chi_conf) >= 37/324`.

On the canonical BAF family:

- `chi_conf = chi_good - chi_exc`,
- `ConfState` has an explicit support formula,
- `E_conf = 2(n-3)`.

### Explicit bridge class

On the explicit `n=5` consecutive-binary class:

- every tested valid cycle is blocked by `EC or SHADOW`,
- and the predicate `any_overlap` separates the two sides.

## 2. The actual bridge theorem shape

The branch should now target a theorem of the following form.

### Bridge Theorem (programmatic target)

For every subthreshold system in the target architecture class, one of the
following holds:

1. **EC case**
   the system yields a derived global EC witness `Phi_EC` with
   `ForbidFrac_{n-2}(Phi_EC) >= c_EC`,

2. **Shadow case**
   the system yields a shadow witness `Phi_Sh` with
   `ForbidFrac_{n-2}(Phi_Sh) >= c_Sh`.

Then

`ForbidFrac_{n-2}(Phi) >= min(c_EC, c_Sh)`

for the witness chosen by the case split.

At the explicit-family level, we already have:

- `c_Sh = 71/504`,
- `c_EC = 37/324`.

So the current explicit disjunctive floor is

`min(71/504, 37/324) = 37/324`.

## 3. Why this is better than “one scalar to rule them all”

The branch now knows something important:

- raw local EC overlap is too local for the forbidden-mass observable,
- but derived global EC witnesses are not.

So the right theorem is not

> every subthreshold system has one canonical scalar witness.

It is more likely

> every subthreshold system canonically yields one of two bridge objects.

This is a weaker but much more realistic target.

## 4. The immediate bridge tasks

### Task A. Generalize the bridge predicate

The explicit `n=5` class suggests the first bridge predicate:

`P = any_overlap`.

What remains is to determine whether a suitable refinement of this predicate
works on a broader architecture class.

### Task B. Promote the EC-side bridge object

The current best EC-side bridge object is `chi_conf`.

We need to decide whether:

- `chi_conf` is canonical enough,
or
- it needs to be replaced by a more invariant derived global EC witness.

### Task C. Promote the shadow-side bridge object

The current best shadow-side bridge object is still the shadow indicator on the
explicit family.

We need the first step toward a canonical shadow witness on a broader class.

## 5. Best near-term theorem targets

The next theorems worth proving are:

1. the broader BAF support theorem for `chi_conf`,
2. the weak global EC bridge law for `chi_conf`,
3. a broader explicit bridge theorem extending the `n=5` case-split class,
4. a first canonical shadow witness theorem beyond the explicit sweep family.

## 6. Bottom Line

The branch no longer lacks a bridge story.

It now has:

- explicit floors on both sides,
- a disjunctive theorem candidate,
- and one tested bridge predicate.

So the next work should be to prove a broader bridge theorem, not to keep
expanding witness packages in isolation.
