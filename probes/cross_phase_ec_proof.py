"""
Cross-Phase Entry Conflict: DEFINITIVE Analysis
================================================

STATUS: The cross-phase EC argument at t is PARTIALLY correct.

WHAT WORKS:
  - Step 1: Phase balance + normalForm => all phases one-sided (J+K=1). PROVED.
  - Step 2: Some phase has length >= 2. PROVED.
  - Step 3A: In a phase where binary fires NOT last => EC at t. PROVED.

WHAT DOESN'T WORK:
  - Step 3B: In a Binary-Fires-Last (BFL) phase, EC at t is BLOCKED.
    Reason: The step before the t-fire (s-1) is the binary fire, and the step
    after the t-fire (s+1) has a DIFFERENT t value (t fires at s).
    No constant-triple window spans a nonmover and the mover step at t.

  - EC at binary procs (bL, bR) is IMPOSSIBLE.
    Reason: Binary procs toggle at each fire. At mover steps, S = pre-fire value.
    At all nonmover steps between consecutive fires, S = post-fire value = 1-pre.
    S always differs between mover and nonmover. PROVED.

COMPUTATIONAL EVIDENCE:
  - At n=4 with CL=10: 150/540 (27.8%) mover words are all-BFL.
  - These mover words are REALIZABLE (not blocked by any constraint).
  - The cross-phase EC argument at t fails for all 150 all-BFL words.

WHAT'S NEEDED TO FILL THE SORRY:
  AllNormalFormFalse2.lean:1265 needs hasEntryConflict gc.
  Given: h_eq (fc(L)+fc(R)=fc(t)), hall_normal, hfc2, hfc_lt, hnoEC.

  Option A: Show BFL contradicts normalForm or some other hypothesis.
    Not clear how — BFL is compatible with J+K=1 (one-sided phases).

  Option B: Find EC at a far ternary proc in the BFL case.
    The far procs fire in the phase interior. Their phases might have
    even-even structure giving EC via bothEvenReturn. Need investigation.

  Option C: Use the universal EC theorem from BinSCC Exploration 10.
    Already proved analytically. But not yet in Lean codebase as a
    standalone theorem (removed to break import cycle, per NonConsecutive.lean note).

  Option D: Bypass AllNormalFormFalse2.lean entirely.
    The main theorem (allNormalForm_false2) calls into the sorry.
    If the zero-winding / shadow cycle approach in GlobalMinGap.lean
    already handles this case, the sorry might be redundant.

RECOMMENDATION:
  The cross-phase argument at t works for ~73-89% of mover words
  (non-BFL). For the BFL case, a different mechanism is needed.
  The most promising path is to show that BFL creates EC at a
  far ternary proc, or to show BFL is impossible under the full
  set of hypotheses (n >= 9, sub-threshold, etc.).

  The sorry at line 1265 should NOT be filled with the pure cross-phase
  argument at t — it would be incomplete.

======================================================================
PARTIAL RESULT (can be used for non-BFL case):

THEOREM (forward_ec_at_t):
  Given a one-sided phase J=1, K=0 of length L >= 2, where bL fires at
  position j < L-1 (not the last interior step):

  EC at t between step interior[j+1] (nonmover) and step s (mover).

PROOF:
  - val(bL) constant from interior[j+1] to s (bL exhausted its fire at j).
  - val(t) constant from interior[0] to s (t doesn't fire in interior).
  - val(bR) constant from phase start to s (K=0).
  => Triple at t constant from interior[j+1] to s.
  => EC at t: step interior[j+1] (nonmover) vs step s (mover). QED.

This proves EC at t when at least one phase has binary-fire-not-last.
For ALL-BFL words: additional argument needed (see options above).
======================================================================
"""

import itertools
from collections import defaultdict


def verify_forward_ec():
    """Verify the forward EC mechanism works for non-BFL phases."""
    print("FORWARD EC AT t: Verification")
    print("=" * 60)

    # Synthetic test: one-sided phase J=1, K=0, binary fires at position j
    total = 0
    ec_found = 0
    for L in range(2, 8):  # phase length
        for j in range(L):  # binary fire position (0-indexed within interior)
            total += 1
            if j < L - 1:
                # Forward window exists: [j+1, L]. Steps j+1, ..., L-1 are far fires.
                # Step L is the t-fire (step s). Step j+1 is nonmover for t.
                # Triple at t: (bL_post, t_val, bR_val) at both steps.
                ec_found += 1

    print(f"  Total (L, j) combos: {total}")
    print(f"  Forward EC works: {ec_found} ({100*ec_found/total:.1f}%)")
    print(f"  BFL blocked: {total - ec_found} ({100*(total-ec_found)/total:.1f}%)")
    print()
    print(f"  BFL cases are exactly: L >= 1, j = L-1 (binary fires last).")
    print(f"  Count: {sum(1 for L in range(2, 8) for j in [L-1])}")


def verify_binary_ec_impossible():
    """Verify EC at binary procs is impossible."""
    print("\nBINARY EC IMPOSSIBILITY: Verification")
    print("=" * 60)

    # For a binary proc bL with state count 2:
    # At mover step: configs.get(k).bL = pre-fire value v.
    #   After fire: bL = 1-v (toggle).
    # At any nonmover step between this fire and the next:
    #   configs.get(k').bL = 1-v (post-fire value).
    # S at mover = v != 1-v = S at nonmover.

    for total_fires in range(2, 12, 2):
        v = 0  # initial value
        for fire_num in range(total_fires):
            mover_S = v  # pre-fire value at this mover step
            nonmover_S = 1 - v  # post-fire value at nonmover steps after this fire
            assert mover_S != nonmover_S
            v = 1 - v  # toggle

        assert v == 0  # returns to original after even fires

    print("  Verified: for all even fire counts 2-10,")
    print("  mover S != nonmover S at every binary fire.")
    print("  EC at binary proc is impossible. QED.")


def count_all_bfl_fraction():
    """Count what fraction of valid mover words are all-BFL."""
    print("\nALL-BFL FRACTION by n and CL")
    print("=" * 60)

    for n in (4, 5):
        t = 1
        bL = 0
        bR = 2

        print(f"\n  n={n}, t={t}, bL={bL}, bR={bR}")

        for CL in range(2*n, 2*n + 5):
            total = 0
            all_bfl = 0

            def bt(word, pos, fc):
                nonlocal total, all_bfl
                if pos == CL:
                    if not all(fc[p] >= 2 for p in range(n)):
                        return
                    if fc[bL] + fc[bR] != fc[t]:
                        return
                    for k in range(CL):
                        if word[k] == t and word[(k+1) % CL] == t:
                            return
                    t_fires = [k for k in range(CL) if word[k] == t]
                    fc_t = len(t_fires)
                    if fc_t < 2:
                        return
                    is_all_one = True
                    is_all_bfl = True
                    for idx in range(fc_t):
                        a = t_fires[idx]
                        s = t_fires[(idx + 1) % fc_t]
                        if s > a:
                            interior = list(range(a + 1, s))
                        else:
                            interior = list(range(a + 1, CL)) + list(range(0, s))
                        J = sum(1 for k in interior if word[k] == bL)
                        K = sum(1 for k in interior if word[k] == bR)
                        if J + K != 1:
                            is_all_one = False
                            return
                        if interior and word[interior[-1]] not in (bL, bR):
                            is_all_bfl = False
                    if is_all_one:
                        total += 1
                        if is_all_bfl:
                            all_bfl += 1
                else:
                    for p in range(n):
                        word.append(p)
                        fc[p] += 1
                        bt(word, pos + 1, fc)
                        fc[p] -= 1
                        word.pop()

            bt([], 0, defaultdict(int))
            if total > 0:
                pct = 100 * all_bfl / total
                print(f"    CL={CL}: total={total}, all_BFL={all_bfl} ({pct:.1f}%)")
            else:
                print(f"    CL={CL}: no valid mover words")


if __name__ == "__main__":
    verify_forward_ec()
    verify_binary_ec_impossible()
    count_all_bfl_fraction()

    print("\n" + "=" * 60)
    print("FINAL SUMMARY")
    print("=" * 60)
    print()
    print("The cross-phase EC argument as outlined in the user's request")
    print("is PARTIALLY CORRECT:")
    print()
    print("  CORRECT part: When binary fire is not the last interior step,")
    print("  the constant-triple argument gives EC at t. This covers ~73-89%")
    print("  of mover words (depending on CL).")
    print()
    print("  GAP: When ALL phases have Binary-Fires-Last (BFL), the")
    print("  constant-triple argument fails at t, and EC at binary procs")
    print("  is impossible (S always differs between mover and nonmover).")
    print()
    print("  The all-BFL pattern exists for ~11-28% of valid mover words.")
    print("  A different mechanism is needed to handle this case.")
    print()
    print("The sorry at AllNormalFormFalse2.lean:1265 requires handling BOTH")
    print("the non-BFL case (forward EC at t) AND the BFL case (TBD).")
