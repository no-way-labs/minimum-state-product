# Information-Theory LB Redirect

Date: April 6, 2026

This note redirects the information-theory branch around the actual lower-bound
goal:

> Can any of the current witness-side structure be turned into
> 1. a necessary condition on all valid systems, or
> 2. a forbidden condition on subthreshold systems?

If not, it should not remain on the lower-bound critical path.

## 1. Branch Admission Rule

From this point onward, an information-theory result only stays on the lower
bound critical path if it aims at one of the following:

1. **Universal valid-system condition**
   A statement that every valid self-stabilizing system must satisfy.

2. **Subthreshold forbidden condition**
   A statement that every system below the threshold must violate.

3. **Bridge theorem**
   A result that converts a witness-side exact code into one of the two forms
   above.

Everything else is witness anatomy. Useful residue, but not lower-bound
progress.

## 2. Strict Triage

### Keep on the lower-bound critical path

#### A. Forbidden width-`n-2` interaction suppression

This is still the strongest candidate necessary condition:

- it is calibrated against shuffled/null labels,
- it separates valid witnesses from known invalid/subthreshold obstruction-side
  scalars,
- and it aligns with the actual convergence architecture.

This remains the best live lower-bound-facing invariant.

#### B. Two-level suppression theorem

The decomposition

- `FutureFc` handles most forbidden suppression,
- slice-rank carries the residual

is worth keeping because it may turn a hard global obstruction into two smaller
ones:

1. a coarse-layer obstruction,
2. a residual slice obstruction.

#### C. Invalid/subthreshold gap theorem

Anything that shows explicit subthreshold families retain a positive forbidden
mass floor remains highly relevant. This is the cleanest current route from the
witness invariant toward an impossibility theorem.

### Continue only conditionally

These are not yet lower-bound results. Keep them only if they are reframed into
a universal or forbidden theorem.

#### D. Exact tiny `FutureFc` codes

Current status: witness-side only.

Keep only if the target becomes:

- every valid near-threshold system admits a reduced coarse code of this type,
  or
- subthreshold systems cannot realize such a code.

#### E. Reduced-prefix recovery-tree theorems

Current status: very promising structurally, but still witness-side.

Keep only if the target becomes:

- reduced-prefix recoverability is forced by validity,
  or
- subthreshold systems provably fail the same recoverability.

#### F. Compact local `CUP-2` theorem

Current status: the best symbolic foothold, but still only about the witness.

Keep only as a building block if it leads to:

- a universal local theorem for all valid systems with endpoint-binary
  architecture,
  or
- a contradiction for subthreshold architectures.

### Shelve from the lower-bound critical path

These should now be treated as background residue unless they re-enter via a
bridge theorem.

#### G. More exact decoder mining

- more family-basis continuation checks,
- more minimal-basis searches,
- more common-basis beautification,
- more shallow-tree extraction,
- more dominant-root cataloging.

These are now low-value for LB unless directly tied to a universal or forbidden
statement.

#### H. Raw capacity / entropy / cover counting

Already ruled out repeatedly. No more time here.

## 3. Next Admissible Theorem Targets

The following are the only information-theory targets that currently look worth
pursuing for the lower bound.

### Target 1. Universal suppression theorem

Prove that every valid system suppresses forbidden width-`n-2` interaction
energy for the rank extension, or at least for the coarse convergence layer.

This would convert the current witness observation into a necessary condition.

### Target 2. Subthreshold floor theorem

Prove that every subthreshold system has forbidden width-`n-2` energy above a
positive floor, possibly first on a restricted architecture class.

This would be the cleanest forbidden condition.

### Target 3. Necessary reduced-prefix condition

Prove that every valid near-threshold system must admit a reduced coarse code
of a certain type:

- small allowed-coordinate code,
- reduced prefix,
- shallow recovery.

This is weaker than exact witness matching, but it is the only way the current
decoder work can become lower-bound relevant.

### Target 4. Subthreshold code failure theorem

Show that subthreshold systems cannot realize the reduced-prefix recovery
structure, even if they can realize the local good-cycle constraints.

This is the sharpest possible use of the current decoder package.

## 4. Concrete Branch Discipline

### Allowed next moves

1. Test whether a candidate invariant holds for **all valid systems in a wider
   class**, not just the witness families.
2. Test whether explicit subthreshold candidate families **must fail** the
   invariant.
3. Search for a theorem that converts current witness-side exactness into a
   **necessary** structural condition.

### Disallowed next moves, unless justified by a bridge theorem

1. More brute-force decoder continuation beyond solved ranges.
2. More tree-shape mining on witness families alone.
3. More exact basis hunting on witness data without a universal or forbidden
   target.

## 5. Recommended Immediate Next Step

The highest-value next attempt is:

> Take the forbidden width-`n-2` interaction suppression invariant and ask for
> the strongest statement that is plausibly universal on valid systems and
> plausibly false on subthreshold systems.

Concretely:

1. formulate a universal coarse-layer suppression candidate,
2. formulate a subthreshold floor candidate,
3. only use the reduced-prefix / compact local theorems as supporting evidence
   if they help explain why such a universal condition should hold.

## 6. Bottom Line

The current information-theory branch has produced valuable witness structure.
But for the lower bound, almost all of it is only useful if it can be upgraded
into:

- a necessary condition on all valid systems,
  or
- a forbidden condition on subthreshold systems.

That is now the sole criterion for whether this branch is still moving the
theorem.
