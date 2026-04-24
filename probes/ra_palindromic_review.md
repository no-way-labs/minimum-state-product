# Palindromic EC Proof Review

## Verdict

**Needs PA**.

The script `zw_palindromic_ec_proof_FINAL.py` runs cleanly and gives strong computational evidence for the intended theorem, but it is **not yet ready for direct Lean formalization as a complete proof**. The main issue is that the prose case split is stronger and narrower than what the code actually verifies.

## What I ran

1. `python3 zw_palindromic_ec_proof_FINAL.py`
2. `python3 ra_palindromic_review_check.py`

Observed results:

- The target script reports full coverage for exhaustive enumeration at `n = 5, 7`.
- It verifies the advertised full-traverse witness for `n = 5..30`.
- It verifies a sample `Case A` BAF family for `n = 5..30`.
- The review checker extended exhaustive enumeration to `n = 5..12`.
- For every `n = 5..12`, there are exactly `2n` canonical words, `Case A` covers `2n - 3`, and exactly **3** words fail `Case A`.
- All `Case A` failures are covered by the code’s broad `verify_case_b`, but only **one** of those three failures is the exact `full_traverse_word(n)` handled in the prose.

## Main assessment

The script contains a plausible proof skeleton:

- `Case A` gives a clean binary-adjacent BAF witness using the step pair `(i_CW + 1, i_CCW)`.
- There is a real exceptional family when `Case A` fails.
- A proc-`3` witness exists for those exceptions, and often for many more words.

But the current writeup overclaims completeness:

- The prose says `Case A` fails only for **the** full-traverse word family.
- Exhaustive enumeration through `n = 12` shows **three** `Case A`-failure families, not one.
- The code’s `verify_case_b` does **not** check the prose’s narrow `Case B`; it checks a much broader condition and succeeds on many words that are not full-traverse.

So the computational evidence is good, but the analytical statement still needs cleanup before Lean.

## Concrete gaps

### 1. Case-B-as-written is not what the code checks

In `zw_palindromic_ec_proof_FINAL.py:274-311`, `verify_case_b`:

- does not check that the word equals `full_traverse_word(n)`;
- does not check the advertised witness pair `(n+3, n)`;
- only searches for **some** proc-`3` mover step and some proc-`2` nonmover step with parity-preserving fire counts.

This is enough for a broad computational search, but it does **not** justify the prose claim that the only remaining family is the full-traverse family with witness `(n+3, n)`.

### 2. The completeness claim is not proved

The docstring claims, around `zw_palindromic_ec_proof_FINAL.py:77-85` and `zw_palindromic_ec_proof_FINAL.py:134-145`, that if both binary pairs `{0,1}` and `{1,2}` fail `Case A`, then the word must be the full-traverse word.

That exact statement is not supported by the exhaustive data I ran. For `n = 5..12`, the `Case A` failures are always:

1. `(0, 0, n-1, n-2, ..., 1, 1, 2, ..., n-1)`
2. `(0, 1, 0, n-1, n-2, ..., 1, 2, ..., n-1)`  ← exact `full_traverse_word(n)`
3. `(0, 1, 2, ..., n-1, 0, n-1, ..., 1)`

Only family 2 is the exact prose `Case B`.

### 3. The exhaustive checks do not prove the structural lemma

`enumerate_zw_fc2` is useful evidence, and empirically every enumerated word is a two-phase BAF word. But the script still assumes rather than proves the structural bridge:

- zero winding;
- `fc(p) = 2` for all `p`;
- local moves in `{−1, 0, +1}`;
- implies the mover word has the required palindromic/back-and-forth shape with two turnarounds.

If `BAFWord.lean` already contains this, good. If not, this is a real prerequisite lemma.

### 4. The script is specialized to one state-size profile

The code hardcodes

`state_sizes = [2 if p < 3 else 3 for p in range(n)]`

at several points, so it directly models exactly three named binary processors `{0,1,2}` and all others ternary.

The theorem statement is weaker: `>= 3` consecutive binary processors. For Lean, you need an explicit WLOG reduction:

- choose any consecutive binary triple;
- rotate/relabel so it becomes `{0,1,2}`;
- show the witness argument is unaffected if processors beyond that triple are also binary.

This is probably manageable, but it is still an extra lemma.

## Evidence from the review script

The checker `ra_palindromic_review_check.py` shows:

- `Case A` failures are stable across `n = 5..12`: always exactly 3 families.
- Only one of those is `full_traverse_word(n)`.
- Only that one satisfies the prose’s exact `Case B` pair `(ms, nms) = (n+3, n)`.
- The broad `verify_case_b` succeeds on all 3 exceptional families and on many non-exceptional words as well.

So the likely fix is:

- either broaden `Case B` analytically to match what the code actually proves;
- or classify the 3 exceptional families explicitly and give a witness for each.

## Key lemmas needed before / during Lean

1. **BAF structure lemma**
   From zero winding + `fc = 2` + `cwStepCount > 0`, derive the two-phase back-and-forth structure with two turnarounds.

2. **WLOG normalization lemma**
   Reduce any run with at least three consecutive binary processors to the normalized binary block `{0,1,2}`.

3. **Case A witness lemma**
   If adjacent binary processors `b, b+1` are interior to both arcs, then the step pair `(i_CW + 1, i_CCW)` yields equal `(left, self, right)` context and therefore EC.

4. **Case A failure classification**
   When neither `{0,1}` nor `{1,2}` supports `Case A`, classify the resulting word family correctly.
   Current evidence says this is a 3-family statement in the chosen normalization, not a single-family statement.

5. **Exceptional-family EC lemma**
   For each `Case A` exception, produce an explicit witness at proc `3` or prove a single broader proc-`3` lemma that subsumes all three.

6. **Context preservation bridge**
   Use the existing no-fire / even-fire-count lemmas to convert interval fire counts into equality of local entry triples.

## Edge cases

- `n = 5` behaves consistently with the general pattern in the computations I ran.
- The proc-`3` witness does not seem to need proc `3` to be ternary; `0 mod m = 0` for any state size. The current prose is narrower than necessary here.
- The right neighbor in `Case B` also does not need to be ternary if its interval fire count is `0`.

## Estimated effort

Assuming the referenced Lean infrastructure already exists (`ContextBridge`, `BinaryParity`, `BAFWord`):

- **PA cleanup**: about **0.5 to 1.5 days**
  - rewrite the completeness statement;
  - classify the `Case A` exceptions correctly;
  - state a Lean-friendly exceptional-family lemma.

- **Lean formalization after PA cleanup**: about **2 to 4 days**
  - encode the normalized case split;
  - import the fire-count lemmas;
  - construct the explicit witnesses.

If the BAF structure lemma is not already formalized cleanly, add another **1 to 3 days**.

## Bottom line

The script is a good **research artifact** and gives convincing evidence that the theorem is true in the intended regime. But as of now it is **not ready to be translated verbatim into Lean**. The proof needs one more round of pen-and-paper cleanup, centered on the exact classification of the `Case A` failures and on aligning the written `Case B` with what the code actually certifies.
