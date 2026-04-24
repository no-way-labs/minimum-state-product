# EC Support-Lift Route

Date: April 6, 2026

This note records the next bridge direction after the representative
basis-coefficient theorem.

The key correction is:

- coefficient-level lift from `W_d` to the full tested BAF class fails,
- but support-level lift may still succeed.

## 1. Why the route changed

The exact representative theorem in `ec_basis_coefficient_theorem.md` proves
that, on the canonical representatives `W_d`, one explicit coefficient is
nonzero on a candidate forbidden support `S_d`.

But small full-fiber checks show that the same coefficient is not rigid on the
full tested BAF class:

- it can flip sign,
- and in some classes it can vanish.

So the next lift theorem cannot be:

> the same explicit coefficient survives on every valid good cycle.

## 2. First positive support-level evidence

The right replacement target is:

> the same forbidden support `S` carries positive ANOVA energy across the whole
> class, even if no single fixed basis coefficient does.

The first strong example is the previously problematic class:

- `n=6`
- distance class `d=2`

where the representative coefficient route did **not** lift rigidly.

Running

- `ec_support_lift_probe.py --n 6 --d 2 --max-comp-size 2`

shows that there are many tiny forbidden complements of size `1` or `2` whose
support-energy is positive and in fact **constant across all 16 valid goods** in
the class.

Examples:

- complement `{1}`:
  support energy `0.000514403292`
- complement `{3}`:
  support energy `0.000342935528`
- complement `{5}`:
  support energy `0.000342935528`
- complement `{3,5}`:
  support energy `0.000685871056`
- complement `{0,3}`:
  support energy `0.000342935528`

So this class is not spectrally unstable. It is only coefficient-unstable for
the specific representative basis vector.

## 3. Why this matters

This is the first concrete sign that the full-class bridge theorem may still be
support-level rigid even when it is not coefficient-level rigid.

That is exactly the sort of theorem we should want:

- representatives give exact formulas and structural intuition,
- the broader class lifts at the level of support-energy,
- and the lower-bound obstruction only needs positive forbidden mass, not a
  fixed basis coefficient.

## 4. Current theorem target

The next plausible EC-side bridge theorem is now:

> for each distance class `d`, there exists a tiny anchored forbidden support
> `S_d^*` such that every valid good cycle in that class has positive forbidden
> ANOVA energy on `S_d^*`.

The support `S_d^*` might agree with the representative support, or it might be
slightly different. The new probe shows that this is the right level of
robustness to target.

## 5. Remaining gap

This route now has a first small-range theorem:

- `ec_smallrange_support_lift_theorem.md`

which proves the class-stable support pattern through `n=9`.

The remaining gap is no longer “does support-level lift ever happen?”.
It is whether the same pattern persists on the **full tested class** beyond
`n=9`.

So the next work should be:

1. extend the pattern beyond `n=8`,
2. identify the first changed class if the pattern breaks,
3. and then try to prove the stabilized support-family theorem symbolically.
