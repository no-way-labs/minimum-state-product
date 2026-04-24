"""
Cross-Phase EC: Check at n >= 5 whether all-binary-fires-last is possible.

Key insight: at n >= 5, there are >= 2 far procs. The "all-BFL" pattern
requires that in every phase, the step just before the binary fire is
a far proc fire. This constrains which far procs fire where.

Actually, the question is simpler: does there exist a mover word where
ALL one-sided phases have binary-fires-last? We just need to check the
COMBINATORIAL structure.

In a phase of length L: the binary fire is at position L-1 (last).
Positions 0, ..., L-2 are far fires. ANY far proc can fire at any position.

So: binary-fires-last is not constrained by the number of far procs.
It's always possible to arrange the binary fire last.

WAIT: but we need to count. With all phases one-sided and binary-fires-last:
- Each phase has 1 binary fire at the end.
- The rest are far fires.
- Total far fires = CL - fc(t) - fc(t) = CL - 2*fc(t) (since binary fires = fc(t)).
  Wait: total binary fires = fc(bL) + fc(bR) = fc(t) (from phase balance).
  Total t fires = fc(t). Total far fires = CL - fc(t) - fc(t) = CL - 2fc(t).
  With n-3 far procs, each firing >= 2: CL - 2fc(t) >= 2(n-3).

This is always satisfiable. So binary-fires-last IS possible even at large n.

NEW APPROACH: Don't try to show binary-fires-last is impossible.
Instead, find an EC mechanism that works even with binary-fires-last.

The key structural fact: in a BFL phase, the pattern is:
  [far, far, ..., far, binary, t]

At step s (t fires): triple at t = (bL_post, t_old, bR_val).
  bL_post because bL just fired at s-1.
  t_old because t hasn't fired since the start of the phase.

At step a+1 (first interior step, far fires): triple at t = (bL_pre, t_new, bR_val).
  bL_pre because bL hasn't fired yet in this phase.
  t_new because t fired at step a, changing from t_old to t_new.
  Wait: t fires at step a. configs.get(a) has t = t_old (before fire).
  configs.get(a+1) has t = t_new (after fire). So t_new at step a+1.

Different L (bL_pre vs bL_post) and different S (t_new vs t_old).
No EC between step a+1 and step s at proc t. Confirmed.

KEY OBSERVATION:
In a BFL phase: the t-fire step s has triple (bL_post, t_old, bR).
In the NEXT phase: the first interior step (s+1) has triple (bL_post, t_new, bR').

The bL value at step s+1 is bL_post (bL just fired at s-1, and doesn't
fire again until the next bL-phase). So:

Step s (mover at t): L = bL_post.
Step s+1 (nonmover at t): L = bL_post. SAME L!

But S at step s: t_old. S at step s+1: t_new. DIFFERENT S.

So: L matches, S doesn't. No EC.

BUT: what if t_old = t_new? That would mean t fires and returns to the
same value. Is that possible?

For a ternary proc: f_t(L, S, R) = new_val. If new_val = S: t wouldn't
be privileged (wouldn't fire). So new_val != S. Always.

So t_old != t_new. No EC from this mechanism.

COMPLETELY DIFFERENT IDEA: Use the EVEN binary parity across 2 phases.

Take two consecutive phases (phase i and phase i+1). Both are one-sided.

Case 1: Both have the same side (e.g., both bL fires).
  Over 2 phases: bL fires 2 times (even). bR fires 0 times.
  Window from step a_i+1 to step s_{i+1}: t fires once (at s_i = a_{i+1}).
  Can't use bothEvenReturn_ec because t fires in the window.

  BUT: consider the window from step a_i+1 to step s_i (within phase i).
  In this window: bL fires 1 time (odd), bR fires 0. Can't use even-even.

  And window from a_i+1 to... hmm.

Case 2: Opposite sides (phase i has bL, phase i+1 has bR).
  Over 2 phases: bL fires 1, bR fires 1. Total 2 (even).
  But one of each side. bothEvenReturn needs both individually even.

Hmm. The even-even mechanism doesn't help directly.

FINAL CORRECT APPROACH FOR THE SORRY:

Looking at this from the right angle: the sorry at line 1265 just needs
hasEntryConflict gc. It doesn't need EC specifically at t. It could be
EC at ANY proc.

And the comment at line 1260-1264 suggests a "domino argument" where
"binary parity constraint forces a full cycle around the ring."

This is exactly the universal entry conflict mechanism from BinSCC Expl 10
(already proved analytically!). The 4 mechanisms (Both-Even Return,
Toggle-FR, Zero-Side EC, Traversal Return) + 2 ring-level lemmas cover
ALL cycles.

So: the sorry at line 1265 should invoke the UNIVERSAL ENTRY CONFLICT
theorem, not a new cross-phase argument!

Let me check if this theorem is already in the Lean codebase.
"""

import itertools
from collections import defaultdict


def check_n5_bfl_feasibility():
    """Quick check: all-BFL feasible at n=5?"""
    print("=" * 60)
    print("ALL-BFL FEASIBILITY CHECK (n=5)")
    print("=" * 60)

    n = 5
    t, bL, bR = 2, 1, 3  # sandwiched ternary at position 2
    far = [0, 4]

    # CL = 10 (minimum: 2*5)
    # fc(t) = 2 (minimum). fc(bL) + fc(bR) = 2. All even: fc(bL)=2, fc(bR)=0 OR fc(bL)=0, fc(bR)=2.
    # But fc(bR) >= 2 (every proc fires >= 2). So fc(bR) >= 2 and fc(bL) >= 2.
    # fc(t) = fc(bL) + fc(bR) >= 4.

    # With fc(t) = 4: CL >= 2*5 = 10. fc(t) = 4.
    # Total far fires = CL - 2*4 = CL - 8. With far = 2 procs, each >= 2: CL - 8 >= 4, CL >= 12.

    # So min CL = 12 for fc(t) = 4 at n=5.

    # Example BFL mover word:
    # Phase 0: far0, bL, t  (length 2, BFL)
    # Phase 1: far4, bR, t  (length 2, BFL)
    # Phase 2: far0, bL, t  (length 2, BFL)
    # Phase 3: far4, bR, t  (length 2, BFL)
    # Total: 12 steps. fc(t)=4, fc(bL)=2, fc(bR)=2, fc(0)=2, fc(4)=2. All >= 2. Valid.

    word = [0, 1, 2, 4, 3, 2, 0, 1, 2, 4, 3, 2]
    CL = 12
    print(f"  Example BFL word at n=5, CL=12: {word}")

    # Verify
    fc = defaultdict(int)
    for w in word:
        fc[w] += 1
    print(f"  Fire counts: {dict(fc)}")
    assert all(fc[p] >= 2 for p in range(n))
    assert fc[bL] + fc[bR] == fc[t]

    # Verify phases
    t_fires = [k for k in range(CL) if word[k] == t]
    print(f"  t-fire steps: {t_fires}")

    for idx in range(len(t_fires)):
        a = t_fires[idx]
        s = t_fires[(idx + 1) % len(t_fires)]
        if s > a:
            interior = list(range(a + 1, s))
        else:
            interior = list(range(a + 1, CL)) + list(range(0, s))
        J = sum(1 for k in interior if word[k] == bL)
        K = sum(1 for k in interior if word[k] == bR)
        last_mover = word[interior[-1]] if interior else None
        is_bfl = last_mover in (bL, bR)
        print(f"  Phase {idx}: a={a}, s={s}, J={J}, K={K}, len={len(interior)}, BFL={is_bfl}")

    print("\n  ALL-BFL IS FEASIBLE at n=5 (and any n >= 4).")
    print("  Simple forward-EC at t is NOT universal.")
    print()
    print("  CONCLUSION: Need the universal EC theorem (from BinSCC)")
    print("  or a mechanism that works at non-t procs.")


if __name__ == "__main__":
    check_n5_bfl_feasibility()
    print()
    print("=" * 60)
    print("DIAGNOSIS")
    print("=" * 60)
    print()
    print("The cross-phase EC argument at t has a gap:")
    print("Binary-fires-last phases DON'T give EC at t.")
    print("This pattern IS realizable (example constructed).")
    print()
    print("Options:")
    print("1. Invoke universal EC from BinSCC Exploration 10")
    print("   (4 mechanisms + 2 ring lemmas cover ALL cycles)")
    print("2. Show EC at a DIFFERENT proc (bL, bR, or far)")
    print("3. Show binary-fires-last contradicts some OTHER hypothesis")
    print()
    print("Option 1 is already proved analytically (BinSCC Expl 10).")
    print("The sorry at AllNormalFormFalse2.lean:1265 should use this.")
