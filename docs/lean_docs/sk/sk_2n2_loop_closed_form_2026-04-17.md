# SK 2n+2 Loop / Uniform Closure Report — 2026-04-17

## §1 The n=5..8 loop — symbolic structure

Representative cycles were extracted from the first canonical family
`ms = (2,2,2,3,...,3)`. In every representative, the lex-first forced chain
starts at `c*`, has `loop_start = 0`, and returns exactly to `c*` after
`2n+2` steps.

Representative move sequences `(position, pre, post)`:

- `n = 5`, `c* = (0,0,0,2,0)`, `q0 = 3`
  - `(0,0,1), (4,0,1), (3,2,0), (1,0,1), (0,1,0), (4,1,2),`
  - `(4,2,0), (2,0,1), (1,1,0), (3,0,1), (3,1,2), (2,1,0)`
- `n = 6`, `c* = (0,0,0,0,2,0)`, `q0 = 4`
  - `(0,0,1), (5,0,1), (4,2,0), (1,0,1), (0,1,0), (5,1,0),`
  - `(2,0,1), (1,1,0), (3,0,1), (3,1,2), (2,1,0), (4,0,1),`
  - `(4,1,2), (3,2,0)`
- `n = 7`, `c* = (0,0,0,0,0,1,0)`, `q0 = 5`
  - `(0,0,1), (6,0,1), (5,1,0), (1,0,1), (0,1,0), (6,1,0),`
  - `(2,0,1), (1,1,0), (3,0,1), (3,1,2), (2,1,0), (4,0,1),`
  - `(4,1,2), (3,2,0), (5,0,1), (4,2,0)`
- `n = 8`, `c* = (0,0,0,0,0,0,1,0)`, `q0 = 6`
  - `(0,0,1), (7,0,1), (6,1,0), (1,0,1), (0,1,0), (7,1,0),`
  - `(2,0,1), (1,1,0), (3,0,1), (3,1,2), (2,1,0), (4,0,1),`
  - `(4,1,2), (3,2,0), (5,0,1), (4,2,0), (6,0,1), (5,1,0)`

Common pattern:

- `q0 = n-2` in every extracted case at `n = 5..10`.
- The loop is built from a common sweep backbone beginning
  `0, n-1, n-2, 1, 0, n-1, 2, 1, ...`.
- Across all extracted loops at fixed `n`, the exact mover word is **not**
  literally unique. The raw loop signatures vary by cycle and by `ms`.
- The variation is not arbitrary: it is a small family of local surgeries
  concentrated at distinguished ternary positions.

Dependence on `ms`:

- For `(2,2,2,3,3,...)`, the generic extra-activity sites are `(3,4)`.
- For `(2,2,3,2,3,...)`, they shift to `(2,4)`.
- For `(2,2,2,2,3,...)`, they shift to `(4,5)`.
- Exceptional variants move one extra firing to the last ternary or to `q0`,
  or collapse both extras into a quadruple firing at the first distinguished
  ternary.

Conclusion for §1: there is a clear low-`n` symbolic family, but not one rigid
exact mover word independent of cycle/ms choice. The robust description is
“base sweep plus local ternary-site surgeries.”

## §2 The Hamming envelope

All extracted lex-first loops at `n = 5..8` stay inside `N_1(C) ∪ N_2(C)`.
No extracted loop ever reaches Hamming distance `>= 3`.

Representative Hamming trajectories:

- `n = 5`: `[1,1,1,1,1,1,1,1,1,1,2,1]`
- `n = 6`: `[1,1,1,1,1,1,1,1,1,2,2,1,2,1]`
- `n = 7`: `[1,1,1,1,1,1,1,1,1,2,2,1,2,2,1,1]`
- `n = 8`: `[1,1,1,1,1,1,1,1,1,2,2,1,2,2,1,2,1,1]`

Counts:

- `n = 5..8`: `65/65` extracted witness chains satisfy `max Hamming = 2`,
  except one `n = 5` loop that stays entirely in `N_1`.

This is not a strict alternation `N_1 -> N_2 -> N_1 -> ...`. The pattern is:

- a long initial `N_1` segment,
- then one or more short `N_2` clusters,
- then return(s) to `N_1`.

The `N_2` visits occur exactly where the local ternary-site surgery is active.

## §3 The analytical mechanism

Candidate (a), “each position fires exactly twice,” is false in literal form.
What survives is the modified statement:

- there is a `2n` sweep backbone,
- plus two units of extra firing mass,
- and that extra mass is always concentrated on distinguished ternary sites.

Empirical support:

- In the generic cases, two ternary positions fire three times and every other
  position fires twice.
- Exceptional cases collapse this to one ternary position firing four times, or
  move one extra firing to the last ternary / to `q0`.
- No extra firing mass migrates to arbitrary binary sites.

Candidate (b), “shadow of the good cycle,” is partially correct but not exact.
The good-cycle mover words are highly regular:

- `n = 5`: `0,1,2,3,3,4,0,1,2,3,4,4`
- `n = 6`: `0,1,2,3,3,4,4,5,0,1,2,3,4,5`
- `n = 7`: `0,1,2,3,3,4,4,5,6,0,1,2,3,4,5,6`
- `n = 8`: `0,1,2,3,3,4,4,5,6,7,0,1,2,3,4,5,6,7`

The witness loop is a perturbation of this doubled-then-single sweep, but not a
literal subsequence or literal copy. The right description is “sweep backbone
with local surgeries induced by the Hamming-1 perturbation.”

Candidate (c), “pure parity/bipartite cover,” is too weak. Evenness explains
almost nothing about which positions get the extra firings or why the raw loop
words vary by `ms`.

Conclusion for §3:

- The exact `2n+2` length at `n = 5..8` is real.
- Its mechanism is “`2n` sweep + `2` ternary-site surgery,” not one universal
  rigid exact word.
- That is enough to explain the low-`n` data, but it is not the right global
  proof object under the no-case-split constraint.

## §4 The n=9 regime shift

For the extracted canonical `n = 9` family
`ms = (2,2,2,2,3,3,3,3,3)`:

- `4/4` witness chains are lex-first dead ends, not `20`-loops.
- The full forward closure has size `225`.
- The sink-peel of that closure has size `218`.
- The SCC containing `c*` also has size `218`; empirically,
  `peel(forward_closure(c*)) = SCC(c*)`.
- `c*` lies in that large recurrent SCC.
- `shortest_cycle_through c* = 21`.
- Exact search found no directed cycle of length `20 = 2n+2` in the extracted
  `n = 9` closures.

Condensation structure (`4/4` extracted records agree):

- one main SCC of size `218` containing `c*`,
- six escape edges from that SCC to six singleton components,
- a lex-first exit chain of singleton components with profile
  `[0,0,0,0,0,0,0,0,0,0,0,0,4,5,6,7]`,
- first exit only at state index `12`,
- unique bottom SCC = final singleton sink.

So the replacement structure is **not** “a longer simple loop” and **not**
“a DAG with one tiny bottom cycle.” It is:

- a large recurrent peel-core/SCC containing `c*`,
- together with a short escape fringe chosen by lex-first tie-breaking.

`n = 10` continuation (canonical 4-binary family
`ms = (2,2,2,2,3,3,3,3,3,3)`):

- `2/2` cycles found in `50s`.
- good-cycle length `23`,
- `c* = (0,0,0,0,0,0,0,0,1,0)`, `q0 = 8`,
- lex-first chain dead end,
- forward closure size `317`,
- peel-core size `309`,
- peel rounds `9`,
- `shortest_cycle_through c* = 23`,
- dead-end prefix begins
  `0,9,8,1,0,9,2,1,3,2,4,3,0,1,2`.

This is strong evidence that the low-`n` `2n+2` loop presentation does **not**
extend unchanged beyond `n = 8`, while the peel-core mechanism does continue to
`n = 10`.

`n = 11`: attempted on the canonical 4-binary family, but cycle search did not
return in the working budget and was skipped.

## §5 Extension verdict

The original loop-based trichotomy `A/B/C` is not the proof-relevant answer
under the hard no-case-split constraint.

Loop verdict:

- `A` is false: the lex-first `2n+2` loop does not survive at `n = 9`, and the
  tested `n = 10` family shows the same failure mode.
- `B` is computationally accurate but proof-shape-invalid: “small-`n` loop,
  large-`n` SCC/peel” is exactly the forbidden seam.
- `C` is too pessimistic if interpreted as “no uniform structure exists at all.”

Proof-relevant verdict:

- A **uniform closure mechanism candidate exists**:
  `S(c*) := peel(forward_closure(c*))`.
- In every tested case `n = 5..10`, `c* ∈ S(c*)`, and empirically
  `S(c*) = SCC(c*)` inside the forced forward closure.
- The size/shape of `S(c*)` varies with `n`, but the witness object is the same.

Observed sizes:

- `n = 5`: `S = 21` or `26`
- `n = 6`: `S = 45, 52, 53, 54`
- `n = 7`: `S = 90, 91, 93`
- `n = 8`: `S = 142`
- `n = 9`: `S = 218`
- `n = 10`: `S = 309`

So the usable verdict is:

- abandon the hope of one universal `2n+2` loop theorem,
- keep the low-`n` loop analysis as evidence about the shape of `S(c*)`,
- and pursue the one-shot peel-core witness instead.

## §6 Lean-ready distillation

Do **not** target a theorem whose proof body splits into “`n <= 8` loop witness”
versus “`n >= 9` SCC/peel witness.” The seam-free target is:

For every sub-sharp good cycle `gc` and its canonical Hamming-1 witness `c*`,
let `T(c*)` be the finite forced-successor forward closure in `VC_NG`, and let
`S(c*) := peel(T(c*))` be the sink-peel (greatest subset in which every node
still has a forced successor in the subset). Empirically, across all tested
cases `n = 5..10`, `c* ∈ S(c*)`, and `S(c*)` is exactly the SCC of `c*` inside
`T(c*)`. For `n = 5..8`, the observed `2n+2` loop is just the simplest visible
shape of this same witness object; for `n = 9,10`, `S(c*)` is a larger
recurrent peel-core with escape branches outside it. So the Lean direction
should be: one inner lemma about forward closure + peel retaining `c*`, not a
loop theorem for small `n` and a different recurrent-core theorem for large
`n`. If Lean cannot obtain an analytic closed form for `S(c*)`, the correct
fallback is to port the computational forward-closure / peel construction, not
to reintroduce a case split.

## §7 Follow-Up: Uniform Membership Attempt

The follow-up question was stronger: prove uniformly in `n` that
`c* ∈ peel(forward_closure(c*))`, equivalently that there is always a directed
cycle from `c*` back to itself in the forced forward closure.

What improved:

- In every extracted record `n = 5..9`, the **shortest** directed cycle through
  `c*` has length exactly the good-cycle length `L`.
- In every extracted record `n = 5..9`, that cycle uses **exactly the same
  mover multiset** as the good cycle.
- Across all extracted data, the shortest shadow-sweep word through `c*`
  appears to be determined by the good mover word alone.

This is strong evidence for a uniform shadow-sweep theorem:

- for each good mover word `w`, there should exist an adaptive permutation
  `σ_w` such that replaying the mover entries of `w` in order `σ_w` yields a
  directed cycle through `c*`.

But the analytic proof did **not** close. The obstruction is precise:

- no closed-form / local symbolic description of the adaptive permutation
  `σ_w` was found;
- prior non-uniform shadow work in the repo hits the same gap;
- and without `σ_w`, the membership claim is still computationally supported
  rather than analytically proved.

So the correct status after the follow-up is:

- the seam-free witness object `S(c*) = peel(forward_closure(c*))` remains the
  best candidate;
- the strongest current uniform mechanism is a canonical shadow sweep through
  `c*`;
- but **no uniform analytical proof of `c* ∈ S(c*)` was found**.

That means LE still should **not** launch on the membership lemma as if it were
proved. The honest next pivot is one of:

- find a symbolic theorem for the adaptive shadow permutation `σ_w`, or
- weaken / change the witness object (for example, prove that a canonical
  forced successor of `c*` lies in the peel-core, if that is enough for
  `(SK gc).Nonempty`), or
- port the computational closure construction if the project decides that is
  acceptable after all.
