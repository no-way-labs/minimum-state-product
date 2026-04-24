---
title: "Witness Primer — State-Product Records for Self-Stabilizing Token Rings"
author: "K Alexander A-M"
date: "April 2026"
geometry: margin=1in
fontsize: 11pt
---

# Purpose

This primer is the second of a two-document onboarding for Knuth's 1985
open problem (minimize the state product of a self-stabilizing token ring).
It is a companion to [p2.md](p2.md), which gives the problem statement, the
three Dijkstra solutions, Knuth's optimization question, and the history
through 2024. The present document covers the other half of what a
lower-bound prover needs before attacking the problem: **what the
record-holding constructions look like**.

A reader who finishes p2.md and this document has everything needed to
start a lower-bound proof from scratch. We make no reference to any
in-progress attack; this is a snapshot of the state-product frontier as
set by known valid systems.

Recall the notation from p2.md §1: `n` processors `P_0, …, P_{n-1}` in a
ring; processor `P_i` has `m_i` states; transition function
`p_i' = f_i(p_{i-1}, p_i, p_{i+1})`; a valid ("self-stabilizing") system
satisfies liveness, mutual exclusion, closure, convergence, and fairness.
Write `M_n` for the minimum of `m_0 · m_1 · … · m_{n-1}` over all valid
systems on `n` processors. Every valid system on `n` processors
establishes `M_n ≤ ∏ m_i`; we call such a system a **witness**.

---

# 1. What a witness is

A witness is a concrete, verified valid system:

1. A state vector `ms = (m_0, …, m_{n-1})` with each `m_i ≥ 2`.
2. A transition table `f_i : Fin(m_{i-1}) × Fin(m_i) × Fin(m_{i+1}) → Fin(m_i)`
   for each processor.
3. A verification that the system satisfies Dijkstra's five properties
   (liveness, mutual exclusion, closure, convergence, fairness).

The witness certifies `M_n ≤ ∏ m_i`. A lower bound must rule out *every*
smaller product — every `ms` with `∏ m_i` below the target, under every
possible choice of transition tables.

To verify a candidate system by computer you enumerate the configuration
space (size `∏ m_i`) and check each property. Enumeration is feasible
through roughly `n ≈ 18` at the products exhibited below. The Python
verifier used throughout this project is
`probes/verifier.py` (function `verify_system(ms, fs)`);
accompanying scripts `verify_witnesses.py`, `clb_verify_8748.py`, and
`clb_witness_8748.py` check the witnesses described here. In addition,
the `n ∈ {4, …, 10}` portion of the frontier is mechanized in Lean
4 / Mathlib under `lean/LeanMn/`; the specific theorems
are named as they come up in §§3, 5, 7, 8.

A valid system partitions configurations into **good** and **bad**. In a
good configuration exactly one processor is privileged, and the good set
forms a single cycle (the **good cycle**) under the central daemon. The
five properties together say: every bad configuration converges to the
good cycle in finitely many steps, and every processor moves within one
lap around the cycle. The good cycle is the combinatorial heart of a
witness — its length, mover pattern, and shape determine most of the
construction's flavour.

---

# 2. Baseline witnesses (Dijkstra, 1974)

Three constructions from Dijkstra's original note (p2.md §2), all valid
for every `n ≥ 2`. None is tight for large `n`.

| Witness | `m_i` pattern | `M_n` ≤ … |
|---|---|---|
| Solution 1 (K-state uniform) | all `K ≥ n+1` | `(n+1)^n` |
| Solution 2 (4-state non-uniform) | 2, 4, 4, …, 4, 2 | `4^{n-1}` (line, not ring) |
| Solution 3 (3-state uniform) | all 3 | `3^n` |

Solution 3 is the classical uniform record: `M_n ≤ 3^n` for all `n`. The
lower bound `M_n > 2^n` (for `n > 4`) from the 1985 Stanford seminar
(p2.md §4.2) pins `M_n` into the gap `2^n < M_n ≤ 3^n`. The witnesses
below cut into the gap from above.

---

# 3. Small-n regime: `n ∈ {5, 6, 7, 8}`

## 3.1 Product formula

For `n ∈ {5, 6, 7, 8}` the exact value is

    M_n = 32 · 3^(n-4).

The upper bound `≤` is realized by the "3-binary + 1-quaternary +
ternary fill" family below. The lower bound `≥` was established by
exhaustive computational elimination of every smaller product; details
are out of scope here.

| `n` | `M_n` | factorization |
|---|---|---|
| 5 | 96   | `2^3 · 3  · 4` |
| 6 | 288  | `2^3 · 3^2 · 4` |
| 7 | 864  | `2^3 · 3^3 · 4` |
| 8 | 2592 | `2^3 · 3^4 · 4` |

Small cases outside this primer's scope: `M_3 = 8` and `M_4 = 16` via
Gray-code constructions (p2.md §4.1); under central-daemon fairness,
`M_4 = 24` is exact with witness `ms = (2, 2, 2, 3)`, formalized in
Lean as `M_4_eq_24` (`LeanMn/SmallN/Theorem.lean`). A looser
`(2, 2, 2, 4)` witness at product 32 also exists (stored as
`witness_n4` in `verify_witnesses.py`, and as `w4System` in
`LeanMn/SmallN/Defs.lean`).

## 3.2 Shape of the witnesses

Every witness in this regime uses the same ingredient list:

- **Three consecutive binary processors** (`m = 2`).
- **One quaternary processor** (`m = 4`), separated from the binary
  block by at least one ternary buffer.
- **Ternary fill** (`m = 3`) at the remaining positions.

The state product is therefore `2^3 · 4 · 3^{n-4} = 32 · 3^{n-4}`,
independent of where the quaternary and ternary positions sit in the
ring (subject to the buffer requirement).

A concrete set of placements used by the verified witnesses in
`docs/verify_witnesses.py`:

| `n` | `ms` | witness label |
|---|---|---|
| 5 | `(2, 2, 2, 3, 4)`          | `witness_n5` |
| 6 | `(2, 2, 2, 4, 3, 3)`       | `witness_n6` |
| 7 | `(3, 2, 2, 2, 3, 4, 3)`    | `witness_n7` |
| 8 | `(2, 2, 3, 4, 3, 3, 2, 3)` | `witness_n8` |

These are not the only valid placements: the multiset `{2^3, 4, 3^{n-4}}`
admits many cyclic orientations, and most of them carry a valid system
under a suitable rule table.

## 3.3 The good cycle is "other"-type

The good cycles of the small-n witnesses are neither a pure **sweep**
(mover walking uniformly around the ring once per lap) nor a pure
**bounce** (mover going up then down). They are mixed:
bounce-with-detours, with the quaternary processor serving as a local
pivot and the ternary processors threading through the binary block.

Empirically measured good-cycle lengths `L` for the witnesses above:

| `n` | `L` |
|---|---|
| 5 | 18 |
| 6 | 35 |
| 7 | 52 |
| 8 | 55 |

No closed-form description of `L(n)` is known in this regime. The
cycle length and mover pattern change qualitatively from one `n` to the
next — there is no single parameterized family that generates all four.
Each witness is, in effect, a hand-solved combinatorial puzzle
consistent with the shared skeleton above.

## 3.4 A worked example: `n = 5`, product 96

State vector `ms = (2, 2, 2, 3, 4)`. Verified good cycle has length 18
and visits every processor at least once (fairness).

The transition tables are given in full in `witnesses.md` (this
directory) under "n = 5". P0, P1, P2 are binary; P3 is ternary; P4 is
quaternary. The binary block `P0 P1 P2` sits at positions 0–2; the
quaternary `P4` is at position 4, separated from the binary block by
the ternary buffer `P3`.

The witness was found by a combination of search over placements and
hand-tuning of the rule tables; it is not unique. Any reader who wants
to reproduce a witness from scratch can run `verify_witnesses.py` for
the stored tables, or enumerate rule tables for a chosen `ms` by
brute-force verifying each property.

## 3.5 Why `32 · 3^{n-4}` at small `n`?

Informal intuition (not a proof): the quaternary processor supplies
enough local freedom to absorb the conflicts that three consecutive
binary processors would otherwise create. Three binaries together force
a wave to propagate across them unidirectionally (the 1985 seminar's
"quasi-unidirectionality" argument, p2.md §4.2); the quaternary at
distance 2 from the block is exactly the state budget needed to let
the wave re-enter the block after traversing the ternary ring. The
fourth state of the quaternary is not "wasted" — removing it (dropping
to ternary) breaks the good cycle at every tested placement.

This heuristic is consistent with the fact that the pattern fails at
`n = 9` (see §4) where the ring is long enough that a single quaternary
can no longer carry the wave across.

## 3.6 Lean formalization

The four small-n witnesses are formalized in `LeanMn/SmallN/Defs.lean`
as `w5System`, `w6System`, `w7System`, `w8System` at the placements
above. The packaged theorem is

```lean
theorem upper_bound_small (n : Nat) (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    ∃ sys : System, valid sys ∧ stateProduct sys.rs = 32 * 3 ^ (n - 4)
```

in `LeanMn/UpperBound/Theorem.lean`, closing `M_n ≤ 32 · 3^{n-4}` for
every `n ∈ {5, 6, 7, 8}`. Validity is proved per-n by an explicit good
cycle plus a bad-configuration rank function that strictly decreases on
every bad step; the rank tables are sealed by `native_decide +revert`.
No axioms beyond Lean's kernel.

---

# 4. The phase transition at `n = 9`

## 4.1 The `{2^3, 4, 3^5}` multiset fails

At `n = 9`, the small-n pattern would predict a witness at product
`32 · 3^5 = 7776`. **No such witness exists.** Every orientation of the
multiset `(2, 2, 2, 4, 3, 3, 3, 3, 3)` around the ring fails
verification (56 cyclic orientations, all eliminated by exhaustive
search). Likewise `(2, 2, 2, 2, 3, 3, 3, 3, 6)` and
`(2, 2, 2, 2, 2, 3, 3, 3, 9)`: every placement fails. Hence

    M_9 > 7776.

## 4.2 A counting lemma forces the next product to be `4 · 3^7`

At `n = 9`, a multiset with `≤ 2` binary positions has product
`≥ 2^2 · 3^7 = 4374` at minimum, and in fact `≥ 4 · 3^7 = 8748` once
you require the rest to be ternary (the smallest non-binary state count
is 3 at any non-binary position, and the tightest product among `≤ 2`
binary multisets is realized by `(2, 3, 3, …, 3, 2)` with `2^2 · 3^7 =
8748`). A multiset with `≥ 3` binary positions and product `≤ 7776` is
possible numerically, but exhaustive search rules out every such
multiset (§4.1).

Therefore: at `n = 9`, the smallest `∏ m_i` realized by a valid system
is at least `8748`, and a witness at exactly `8748` exists (§5). So

    M_9 = 4 · 3^7 = 8748.

## 4.3 The ratio jumps

Comparing adjacent `n`:

| ratio | value |
|---|---|
| `M_6 / M_5` | `3` (geometric) |
| `M_7 / M_6` | `3` (geometric) |
| `M_8 / M_7` | `3` (geometric) |
| `M_9 / M_8` | `8748 / 2592 = 27 / 8 ≈ 3.375` (not geometric) |

The jump from `M_8` to `M_9` is strictly larger than 3. The state-product
growth rate changes from `32 · 3^{n-4}` to `4 · 3^{n-2}` = `(27/8) · 3^{n-3}`
at `n = 9`. The ratio `M_n / M_{n-1}` returns to 3 from `n = 10` onward,
conjecturally, because the large-n family (§5) is geometric with ratio 3.

## 4.4 Why the transition?

The small-n witnesses rely on three consecutive binary processors. The
1985 seminar's quasi-unidirectionality bound says four or more
consecutive 2-state processors is outright impossible (p2.md §4.2,
RFC's observation).

A once-plausible candidate for the mechanism was ARG's 1985 LCM
constraint (p2.md §4.3), which lower-bounds the LCM of non-binary block
state counts when non-adjacent 2-state processors are present. That
attribution has been **ruled out**; see
[`docs/arg_lcm/paper.md`](arg_lcm/paper.md) for the full dispatch. Two
observations suffice:

1. Every known valid witness at `n ∈ {4..8}` has *adjacent* binaries (a
   3-consecutive block). ARG's hypothesis requires non-adjacency, so
   the bound is silent on every valid construction in the family.
2. On the *non-adjacent* orientations of `{2^3, 3^{n-4}, 4}` that ARG
   does cover, the LCM-functional values under all three natural
   readings are identical or nested between `n = 8` and `n = 9`:
   `R1 = {12}`, `R2_min = {3}`, `R2_max = {4,12}`, and `R3` nests
   (`{12,36} ⊆ {36,108} ⊆ {36,108,324}`). No LCM-functional bound can
   discriminate the phase-transition boundary.

So the correct invariant for the `n = 9` transition must be both
*adjacent-aware* (applicable to 3-consecutive-binary orientations) and
*n-aware* (sensitive to ring length in a way ARG-LCM is not). A fully
analytic derivation is open; candidate directions include palindromic
entry conflict, shadow-cycle mirror arguments, and good-cycle-length
vs. product entropy bounds (see `docs/arg_lcm/paper.md §6`).

The operational consequence for a lower-bound prover is that any proof
must distinguish `n ≤ 8` from `n ≥ 9`: the small-n bound is strictly
tighter than `4 · 3^{n-2}` (for example, `M_8 = 2592 < 4 · 3^6 = 2916`).

---

# 5. Large-n regime: `n ≥ 9`, the ternary-strip witness

## 5.1 The ternary-strip state vector

For every `n ≥ 3`, a valid system exists at

    ms = (2, 3, 3, …, 3, 2)

with product `2 · 3^{n-2} · 2 = 4 · 3^{n-2}`. We call this the
**ternary-strip** state vector. Two distinct rule tables on this
state vector are relevant:

- **CLB** ("canonical large-n") — more compact good cycle
  (`n² − 2n + 8` good configurations); Python-verified for
  `n ∈ {5, …, 18}`. Described in §5.2–§5.4.
- **CUP-2** — same state vector, different rule table (87 entries,
  n-independent); good cycle has `(n+2)(n+3)/2 − 5` configurations;
  Lean-formalized for `n ∈ {4, …, 10}` via per-n rank certificates.
  See §5.6.

Both rule tables give the same state product `4 · 3^{n-2}`, so both
yield the same upper bound `M_n ≤ 4 · 3^{n-2}`.

The shape is minimal: binary processors at the two endpoints `P_0` and
`P_{n-1}`, ternary fill everywhere in between. There is no quaternary,
no consecutive binary, no buffer structure. The construction is
uniform in `n` — one recipe covers every ring size.

## 5.2 The good cycle is a bounce

The good cycle is an **up-down bounce**: a wave travels from `P_0` up
to `P_{n-1}` and back down to `P_1`. In mover-sequence notation the
privileged processor at successive steps is

    0, 1, 2, …, n-1, n-2, n-3, …, 1, 0, 1, 2, …   (repeating)

with length `3n - 2`. One full lap fires each of the binary endpoints
once and each of the `n - 2` ternary interior positions three times
(twice during the sweep through, once during the return), closing
after `3n - 2` steps. More concretely, after three complete laps the
composed permutation on states returns every processor to its initial
value — so the bounce closes at period `3n - 2`, not `n - 1` or `2n - 2`.

Cycle statistics:

| quantity | value |
|---|---|
| good-cycle length | `3n - 2` |
| good configurations | `n² - 2n + 8` |
| worst-case convergence steps | `⌊(3n² - 4n - 11) / 4⌋ = Θ(n²)` |
| free entries to fix for liveness | `n - 3` |

The `n - 3` figure counts bad configurations that, after good-targeting
completion of the free transition-table entries, still have no
privileged processor; one additional transition-table entry per dead
configuration is enough to restore liveness. The completion procedure
is deterministic given the good cycle and minimizes the number of
non-good → non-good edges (a reasonable convergence heuristic).

## 5.3 The `n = 9` witness

For `n = 9`, the construction gives

    ms  = (2, 3, 3, 3, 3, 3, 3, 3, 2)
    product = 4 · 3^7 = 8748
    good cycle length = 25
    good configurations = 71
    bad configurations = 8677
    liveness fixes = 6

This is the `M_9 = 8748` witness. The CLB transition tables are
produced by `probes/clb_witness_8748.py`; verification
is by `probes/clb_verify_8748.py` (and
`verifier.py:verify_system`).

The Lean upper-bound proof at `n = 9` takes the CUP-2 rule table
(§5.6) on the same state vector, not CLB. Both give
`M_9 ≤ 8748`; CLB has the more compact good cycle but its convergence
argument stays unformalized, while CUP-2 has an explicit per-n rank
certificate suitable for Lean.

## 5.4 Verification at larger `n`

The CLB construction has been Python-verified for `n ∈ {5, …, 18}`,
covering up to 172M configurations at the largest tested `n`. In every
tested case the five Dijkstra properties hold, giving empirically

    M_n ≤ 4 · 3^{n-2} for all n ∈ {5, …, 18}.

The Lean formalization uses the sibling CUP-2 rule table (§5.6) on the
same state vector and certifies the same bound for `n ∈ {4, …, 10}`.
For `n ≥ 11`, no Lean upper-bound theorem is provided; the paper
cites Dijkstra's 1974 classical `M_n ≤ 3^n` construction (p2.md §2,
"Solution 3") as the fallback universal bound.

At `n ∈ {5, 6, 7, 8}` the `4·3^{n-2}` bound is loose (the small-n
regime §3 is tighter and Lean-formalized as `upper_bound_small`). At
`n = 9` it is sharp (`M_9 = 8748` exact, Lean-formalized). At
`n ≥ 10` it is conjectured sharp but unproved, and Lean-formalized
only up to `n = 10`.

## 5.5 Historical looser construction (Sol 3 v1)

One further related construction is worth naming briefly: **Sol 3 v1**,
with `ms = (2, 3, 3, …, 3)` — one binary at an endpoint, ternary
elsewhere. Product `2 · 3^{n-1}`. Valid for `n ≥ 3`; gives
`M_n ≤ 2 · 3^{n-1}`, looser than `4 · 3^{n-2}` by a factor `3/2`.
Historical interest only: it is the simplest valid non-uniform family
beyond Dijkstra's originals, showing that the distinguished-processor
trick extends beyond the uniform 3-state case.

## 5.6 CUP-2: the Lean-formalized large-n witness

The ternary-strip state vector `(2, 3, …, 3, 2)` carries a second
valid rule table, **CUP-2**, distinct from the CLB rule table of
§5.2–§5.4. CUP-2 properties:

| quantity | value |
|---|---|
| state vector | `(2, 3, …, 3, 2)` |
| state product | `4 · 3^{n-2}` |
| good-cycle length | `3n − 2` |
| good configurations | `(n+2)(n+3)/2 − 5` |
| rule-table size | 87 entries (n-independent) |
| rule-table split | 45 privileged / 40 copy-neighbor / 5 anomalous |

CUP-2 allocates more of the state-product budget to the good cycle than
CLB does (compare `(n+2)(n+3)/2 − 5` with CLB's `n² − 2n + 8`); in
exchange, its convergence argument is structurally cleaner. On paper the
convergence is fully analytic (`O(n²)` via a two-level potential
function). The Lean formalization uses an equivalent but more
machine-tractable device: a per-n rank function on bad configurations,
strictly decreasing on every bad step, sealed by `native_decide +revert`
on a pre-computed rank table.

The packaged theorem is

```lean
theorem upper_bound_cert (n : Nat) (h4 : 4 ≤ n) (h10 : n ≤ 10) :
    ∃ sys : System, valid sys ∧ stateProduct sys.rs = 4 * 3 ^ (n - 2)
```

in `LeanMn/UpperBound/Theorem.lean` (sorry-free). The 87-entry rule
table is in `LeanMn/Tables.lean`; the good cycle is in
`LeanMn/Cycle.lean`; the per-n rank certificates (`cup2Converges4`
through `cup2Converges10`) live in `LeanMn/SmallN/Cup2Convergence.lean`
and are auto-generated by
`probes/gen_cup2_ranks.py`. No axioms beyond Lean's
kernel. For `n ≥ 11` there is no Lean upper-bound theorem; the paper
cites Dijkstra's 1974 classical `M_n ≤ 3^n` construction.

---

# 6. What a lower-bound prover must do

Combining p2.md §3 with the witness data above, a proof of
`M_n ≥ (stated product)` must refute the existence of a valid system
at every smaller product. The witnesses tell you exactly what structure
such a proof cannot accidentally rule out:

## 6.1 Targets the LB must match

- **At `n ∈ {5, 6, 7, 8}`**: show that every `ms` with
  `∏ m_i < 32 · 3^{n-4}` admits no good cycle.
- **At `n ≥ 9`**: show that every `ms` with `∏ m_i < 4 · 3^{n-2}`
  admits no good cycle.

The large-`n` bound settles Knuth's asymptotic question: combined with
`M_n ≤ 3^n`, it would give `lim M_n^{1/n} = 3`, resolving both the
`limsup < 3` and `liminf > 2` questions from p2.md §3.

## 6.2 Structural features the LB must respect

- Three consecutive binary processors are **compatible** with a good
  cycle at `n ∈ {5, 6, 7, 8}` but **incompatible** at `n ≥ 9`. Any
  argument that uniformly blocks three consecutive binaries proves
  too much.
- A single quaternary processor separated from a binary block is the
  "extra state budget" that carries the small-n regime. An LB that
  ignores quaternary placements will not be tight at `n ∈ {5..8}`.
- Binary endpoints with a ternary strip between them are the tightest
  arrangement at `n ≥ 9`. Any LB must allow this shape to survive.
- The 1985 seminar's quasi-unidirectionality result (p2.md §4.2) is
  the principal non-computational structural fact currently available
  at the ring level. ARG's 1985 LCM constraint (p2.md §4.3) also
  applies in its stated regime, but is silent on every known valid
  witness (all have adjacent binaries, outside ARG's hypothesis) and
  cannot discriminate the `n = 9` phase transition on the orientations
  it does cover; see `docs/arg_lcm/paper.md`. The witnesses above are
  consistent with quasi-unidirectionality and outside ARG's scope.

## 6.3 What shape the LB obligation takes

A lower bound at threshold `T` must rule out every finite candidate
`(ms, f_0, …, f_{n-1})` with `∏ m_i < T`. Two common attack shapes:

1. **Good-cycle obstruction.** Show that no cyclic sequence of
   configurations can satisfy mutual exclusion + closure + fairness at
   any `ms` with `∏ m_i < T`. A good cycle, if it exists, has a rich
   combinatorial structure (mover pattern, privileged-at-each-step
   invariant, closure of the transition table on the cycle) — the LB
   argues that this structure is inconsistent at sub-threshold
   products.
2. **Bad-configuration obstruction.** Show that at sub-threshold `ms`,
   some bad configuration is necessarily fixed by the transition table
   (has no privileged processor) or participates in a bad cycle. This
   rules out liveness or convergence directly.

Historical LB progress on this problem has attacked shape (1). The 1985
seminar's `M_n > 2^n` for `n > 4` uses a bad-cycle construction, a
member of shape (2). Both shapes are open research territory at the
`4 · 3^{n-2}` threshold.

## 6.4 Useful handholds (not proofs)

- **ARG's binary-count conjecture** (p2.md §4.4): conjecturally no
  valid system has more than a constant number of binary processors
  for large `n`. The ternary-strip witness saturates this conjecture
  with exactly two binaries. Proving the large-`n` bound would imply
  the ARG conjecture with constant `2` at ternary-dense multisets: a
  multiset `{2^k, 3^{n-k}}` has product `2^k · 3^{n-k}`, which exceeds
  `4 · 3^{n-2}` iff `2^k · 3^{2-k} ≥ 4`, iff `k ≤ 2`.
- **The wave-filter perspective** (p2.md §4.5): Knuth's informal
  intuition is that a valid system filters `k`-waves down to
  `⌈k/2⌉`-waves per lap; the ceiling direction is the hard one. The
  ternary-strip witness is a minimal such filter (the bounce pattern
  is the shortest non-trivial wave on a ring with binary endpoints).

---

# 7. Reproducing the data

All witnesses described here are checked by scripts and Lean theorems
in the project tree. A clean-room reproduction does not need to trust
any prior work.

## 7.1 Python verification (all ranges)

- `probes/verifier.py` — generic verifier. `verify_system(ms, fs)`
  checks all five Dijkstra properties from a state vector and a list of
  transition functions.
- `docs/verify_witnesses.py` — small-n witnesses (n=4..8).
  Prints each property's status for each stored witness.
- `probes/clb_witness_8748.py` — builds the `n = 9`
  ternary-strip CLB witness from the bounce cycle plus good-targeting
  completion plus liveness fixes.
- `probes/clb_verify_8748.py` — dedicated verification
  pass on the `n = 9` CLB witness (71 good configs, 8677 bad configs,
  fairness by firing-sequence check).
- `probes/clb_inherent_cycles.py` — sweeps the
  ternary-strip CLB construction for `n` up to 18 and confirms validity.
- `probes/gen_cup2_ranks.py` — generates the per-n
  CUP-2 rank certificates consumed by Lean.

```
cd <repo-root>
python3 docs/verify_witnesses.py           # n = 4..8 (small-n + w4opt)
python3 probes/clb_verify_8748.py          # n = 9 (CLB)
python3 probes/clb_inherent_cycles.py      # n = 5..18 (CLB sweep)
```

Every script should print `PASS` / `Valid: True` and no diagnostics.

## 7.2 Lean verification (n ≤ 10)

The Lean upper-bound theorems `upper_bound_small` (n = 5..8) and
`upper_bound_cert` (n = 4..10) both live in
`LeanMn/UpperBound/Theorem.lean`, re-exported as
`upper_bound_small'` / `upper_bound_cert'` from `LeanMn/Main.lean`.
Additionally, `LeanMn/SmallN/Theorem.lean` states `M_4_eq_24`
(both bounds for `n = 4`) and `LeanMn/ModelTest/DijkstraSol3.lean`
certifies Dijkstra's 1974 Solution 3 as valid in our model at
`n = 4, K = 3` (a model-correctness test, not a record witness).

```
cd lean
lake exe cache get         # one-time Mathlib fetch (~minutes, cached after)
lake build LeanMn.UpperBound    # UB-reachable build, zero sorry
lake build LeanMn.Main          # full re-exports
```

The UB-reachable files contain no `sorry` and no axioms beyond Lean's
kernel plus `native_decide` on finite-state rank tables. Build output
prints no diagnostics on success.

---

# 8. Summary table

| `n` range | construction | `ms` shape | product | tight? | Lean-certified |
|---|---|---|---|---|---|
| `n = 3` | Gray code | `(2, 2, 2)` | 8 | yes, exact | no (out of scope) |
| `n = 4` (central-daemon) | endpoint-binary + ternary | `(2, 2, 2, 3)` | 24 | yes, exact | yes — `M_4_eq_24` |
| `n = 4` (Gray code, weak fairness) | Gray code | `(2, 2, 2, 2)` | 16 | yes, exact | no (different model) |
| `n = 5, 6, 7, 8` | 3 binary + 1 quaternary + ternary | `{2^3, 4, 3^{n-4}}` (various placements) | `32 · 3^{n-4}` | yes, exact | yes — `upper_bound_small` |
| `n = 9` | endpoint-binary ternary strip | `(2, 3, 3, 3, 3, 3, 3, 3, 2)` | `4 · 3^7 = 8748` | yes, exact | yes — `upper_bound_cert` (via CUP-2) |
| `n = 10` | endpoint-binary ternary strip | `(2, 3, …, 3, 2)` | `4 · 3^8 = 26244` | conjectured exact | yes — `upper_bound_cert` (via CUP-2) |
| `n ∈ {11, …, 18}` | endpoint-binary ternary strip (CLB) | `(2, 3, …, 3, 2)` | `4 · 3^{n-2}` | conjectured exact | no — Python-verified only |
| `n ≥ 19` | Dijkstra 1974 (classical) | uniform 3-state | `3^n` | loose | no — paper citation only |

Lean-formalized theorems (all sorry-free, no axioms beyond kernel + `native_decide` on finite rank tables):

- `upper_bound_small` — `M_n ≤ 32 · 3^{n-4}` for `n ∈ {5..8}`
- `upper_bound_cert` — `M_n ≤ 4 · 3^{n-2}` for `n ∈ {4..10}`
- `M_4_eq_24` — exact `M_4 = 24`

Paper-level fallback at `n ≥ 11` is Dijkstra's 1974 classical `M_n ≤ 3^n`
(p2.md §2, "Solution 3"); no Lean theorem in that range.

For a cold reader: that table plus p2.md is the entire briefing. The
rest of a lower-bound proof is yours to invent.
