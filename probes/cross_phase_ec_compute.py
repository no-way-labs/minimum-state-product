"""
Cross-Phase EC: Definitive proof via abstract phase analysis.

The key theorem: for any mover word satisfying the hypotheses (normalForm,
phase balance, fc >= 2 for all procs, n >= 4), there exists a one-sided
phase where the binary fire is NOT the last interior step.

This is a combinatorial statement about mover words, independent of
the actual config values. We verify it by enumerating abstract phase
decompositions.
"""

import itertools
from collections import defaultdict


def verify_exists_good_phase():
    """
    Abstract verification: given fc(t) phases, each one-sided (J+K=1),
    where the binary fire can be at any position in the interior,
    show that at least one phase has the binary fire NOT at the last position.

    This means: in that phase, there exists an interior step AFTER the
    binary fire and BEFORE the next t-fire. This gives the constant-triple
    EC.

    Formally: phase has length L >= 1. Binary fire at position j (0-indexed).
    "Good" phase: j < L - 1 (binary fire not last), i.e., L - j - 1 >= 1.
    "Bad" phase: j = L - 1 (binary fire is last interior step).

    A bad phase with length L means: L-1 far fires, then 1 binary fire.
    A good phase with length 1 means: L = 1, j = 0 (only the binary fire).
    Wait: j < L - 1 requires L >= 2. If L = 1, then j = 0 = L - 1. Bad.

    So: phase of length 1 is always "bad" (binary fire is both first and last).
    Phase of length >= 2 is "good" if binary fire is at position j < L - 1.

    CLAIM: not all phases can be "bad" (length 1 or binary-fires-last).

    Hmm, phase of length 1 has the binary fire at position 0 = L - 1 = 0. Bad.
    For the EC argument: we need at least one step after the binary fire.
    Length 1: no step after. Length >= 2 with j < L-1: at least one step after.

    Can all phases have length 1? Already shown: no (for n >= 4).
    Sum = CL - fc(t) > fc(t), so some has length >= 2.

    Can all phases with length >= 2 have binary-fires-last?
    If a phase has length L >= 2 and j = L - 1: the binary fire is at
    the end. All L - 1 far fires precede it.

    DOES THIS CONTRADICT ANYTHING?

    Actually: the position of the binary fire within a phase depends on
    the mover word. We need to check whether it's possible for ALL
    length-2+ phases to have binary-fires-last, given the constraints.

    The key constraint: MOVER WORD. The mover word determines who fires
    at each step. The binary fire in a phase is constrained by the
    overall mover word structure.

    Let me think about this abstractly.

    The mover word is a cyclic sequence w_0, w_1, ..., w_{CL-1} where
    w_k in {0, 1, ..., n-1}.

    For proc t with binary neighbors bL, bR:
    - t fires at positions s_0, s_1, ..., s_{fc(t)-1}.
    - Phase i: from s_i to s_{i+1}. Interior: (s_i, s_{i+1}).
    - Each phase is one-sided: exactly 1 binary fire in interior.

    "Binary-fires-last" in phase i means: the binary fire is at step
    s_{i+1} - 1 (the step just before the next t-fire).

    So: moverAt(s_{i+1} - 1) in {bL, bR} and moverAt(s_{i+1}) = t.
    I.e., the step before each t-fire is a binary neighbor fire.

    Can this happen for ALL i? It means every t-fire is immediately
    preceded by a binary fire.

    The mover word looks like: ..., far, ..., far, bX, t, ..., far, ..., far, bX, t, ...

    Every t is preceded by bL or bR. The far fires fill the gaps.

    Is this possible? Yes! Consider:
    n = 5, t = 2, bL = 1, bR = 3, far = {0, 4}.
    CL = 12, fc(t) = 3.
    Mover word: 0, 4, 1, 2, 0, 4, 3, 2, 4, 0, 1, 2
    Phases: [0,4,1],[0,4,3],[4,0,1] — each ends with binary then t.

    So binary-fires-last is POSSIBLE for all phases.

    THEREFORE: the simple constant-triple argument is NOT sufficient.
    We need an additional mechanism for the binary-fires-last case.
    """
    print("=" * 60)
    print("ABSTRACT PHASE VERIFICATION")
    print("=" * 60)
    print()
    print("Binary-fires-last in ALL phases IS possible.")
    print("Simple constant-triple argument is INSUFFICIENT.")
    print()
    print("Need: alternative mechanism for binary-fires-last phases.")


def find_alternative_mechanism():
    """
    Alternative mechanism for binary-fires-last phases:

    In a binary-fires-last phase i: step s-1 fires bL/bR, step s fires t.
    No step after binary fire before t. Can't use forward window.

    BUT: we can use the BACKWARD window combined with the PREVIOUS phase.

    Look at the triple at t at step s (when t fires):
      triple_s = (bL_post, t_val, bR_val)  [bL just fired at s-1]

    Now look at the FIRST step of the phase: step s_{i-1} + 1.
    At this step: neither bL, bR, nor t has fired since the previous t-fire.
    Triple at step s_{i-1} + 1:
      triple_first = (bL_val_at_s_{i-1}+1, t_val, bR_val)

    But bL_val_at_s_{i-1}+1 is bL's value just after the previous t-fire.
    This might be bL_pre (before the binary fire in the current phase).

    Since bL fires once at step s-1: bL_post = 1 - bL_pre.
    So triple_first has bL = bL_pre, triple_s has bL = bL_post = 1 - bL_pre.
    Different L values. No EC between these.

    What about a step in the MIDDLE of the phase? All intermediate steps
    have the same triple as the first step (bL_pre hasn't changed yet,
    t hasn't fired, bR hasn't fired). So all have triple_first. None
    match triple_s (different L value).

    CROSS-PHASE: look at a different phase where t fires with bL = bL_pre.

    In even bL-phase cycles: bL toggles each time it fires. Over fc(bL)
    fires (even), bL returns to original. At the t-fire steps:
    bL alternates between pre and post values.

    Specifically: if phase i has bL firing just before t-fire s_i,
    then at s_i: bL = post-toggle.
    At the next t-fire s_{i+1}: if phase i+1 also has binary-fires-last
    with bL firing, then bL has toggled back. bL at s_{i+1} = pre.

    So: t fires at s_i with bL = post, and at s_{i+1} with bL = pre.
    These are different bL values. No direct EC between t-fire steps.

    But what about nonmover steps? Between s_i and s_{i+1} (phase i+1 interior):
    bL stays at post value until just before s_{i+1} when it toggles back.
    So nonmover steps in phase i+1 have bL = post (same as mover at s_i!).

    CROSS-PHASE EC: t fires at s_i with triple (bL_post, t_val_i, bR_i).
    Nonmover at step s_i + 1 (phase i+1 interior) has triple
    (bL_post, t_val_{i+1}, bR_?).

    Wait: t_val changes at each t-fire. At s_i: t has value t_val_i (pre-fire).
    After fire: t becomes t_val_{i+1} (new value). In phase i+1: t doesn't fire,
    so t stays at t_val_{i+1}.

    Triple at s_i (mover): (bL_post, t_val_i, bR_i). [t_val_i is BEFORE fire]
    Triple at s_i + 1 (nonmover): (bL_post, t_val_{i+1}, bR_?). [t_val_{i+1} is AFTER fire]

    t_val_i != t_val_{i+1} (t fires, changes). Different S values. No EC.

    Hmm. The t value is different at the mover step (pre-fire) vs the
    nonmover step (post-fire). This blocks cross-phase EC too.

    WAIT: I think there's a subtlety about configs.get(k).
    In the Lean formalization: configs.get(k) is the config at step k.
    moverAt(k) is who fires at step k. The fire TRANSFORMS configs.get(k)
    into configs.get(k+1).

    So: at step s (t fires):
    configs.get(s) is the config BEFORE t fires.
    configs.get(s).t = t's value before the fire.
    moverAt(s) = t, and configs.get(s+1).t = new value.

    Triple at step s for EC: (configs.get(s).bL, configs.get(s).t, configs.get(s).bR).
    This is the PRE-fire triple.

    At step s+1 (nonmover for t):
    configs.get(s+1) is the config AFTER t fires.
    configs.get(s+1).t = new value != configs.get(s).t.

    So triple at s+1 has different S from triple at s. No EC between s and s+1.

    Now: at some later step k in phase i+1 interior (where neither bL, t, nor
    bR fires from s+1 to k):
    configs.get(k).t = configs.get(s+1).t = t_new (constant since t doesn't fire).
    configs.get(k).bL = bL value at s+1 = bL_post (from the fire at s-1).
    configs.get(k).bR = bR_val (unchanged).

    Triple at k: (bL_post, t_new, bR_val). t is nonmover.

    For EC with step s: need triple_s = triple_k.
    triple_s = (bL_post, t_old, bR_val). [Wait: what's bL at step s?]

    At step s: configs.get(s).bL = bL value AFTER bL fires at step s-1.
    bL fires at s-1, so configs.get(s).bL = bL_post.

    So: triple_s = (bL_post, t_old, bR_val).
    triple_k = (bL_post, t_new, bR_val).
    L match: yes. S match: t_old vs t_new — NO (t fires at s).
    R match: yes.

    S doesn't match. No EC.

    Hmm. It seems like the binary-fires-last case genuinely avoids EC
    at the sandwiched ternary t. The t-fire changes the S component,
    and no nonmover step has the old S value with the new L value.

    IS THE THEOREM STILL TRUE? Let me reconsider.

    The theorem says: allNormalForm + noEC => False.
    The noEC is global (not just at t). Even if there's no EC at t,
    there might be EC at bL, bR, or some far proc.

    The existing proof structure at AllNormalFormFalse2.lean derives
    EC specifically at t. If binary-fires-last blocks EC at t, then
    the proof needs a DIFFERENT mechanism.

    LET ME CHECK: does binary-fires-last create EC at bL instead?

    At step s-1: bL fires. configs.get(s-1).bL = bL_pre.
    At step s: t fires. bL doesn't fire. configs.get(s).bL = bL_post.
    At step s+1 (if in phase i+1): something fires. bL doesn't fire.
    configs.get(s+1).bL = bL_post.

    EC at bL needs: same (left(bL), bL_val, right(bL)) at both mover
    and nonmover steps.

    At step s-1 (bL fires = mover for bL):
    left(bL) = t-2 value, bL = bL_pre, right(bL) = t value = configs.get(s-1).t.

    Wait, right(bL) = t. So the triple at bL at step s-1 involves t's value.

    At step s-1: configs.get(s-1).t = t_old (t hasn't fired since the start of
    the phase). At other nonmover steps, t might have a different value.

    THIS IS THE RIGHT DIRECTION. Let me check more carefully.

    At step s-1: bL is mover. Triple at bL = (val(bL-1), bL_pre, t_old).
    t_old = configs.get(s-1).t = t value in this phase (constant since t last fired).

    At step s: t fires. configs.get(s).t = t_old (before fire).
    configs.get(s+1).t = t_new. From now on, t = t_new in phase i+1.

    In phase i+1: some nonmover step k has:
    configs.get(k).t = t_new != t_old.
    So triple at bL at step k has right = t_new.

    Triple at bL at step s-1 (mover): (..., bL_pre, t_old).
    Triple at bL at step k (nonmover): (..., bL_post, t_new).

    Different bL value AND different right(bL) = t value. No EC at bL.

    What about a nonmover step WITHIN phase i (before s-1)?
    Say step k < s-1 in phase i. bL doesn't fire yet (binary-fires-last).
    configs.get(k).bL = bL_pre. configs.get(k).t = t_old.
    Triple at bL at step k: (val(bL-1), bL_pre, t_old).

    This MATCHES the mover triple at s-1! Same bL_pre and same t_old.
    But: does val(bL-1) match?

    At step k: configs.get(k).(bL-1) = val at some point where bL-1 might
    have fired. If bL-1 is a far proc and doesn't fire between k and s-1:
    same value. EC at bL!

    WAIT: this gives EC at bL, not at t. But that still gives
    hasEntryConflict gc, which contradicts hnoEC. That works!

    Let me verify: in a binary-fires-last phase, at some nonmover step k
    in the phase interior (before the binary fire at s-1), the triple at bL
    matches the mover triple at s-1.

    Triple at bL at step k (nonmover): (configs.get(k).(bL-1), bL_pre, t_old).
    Triple at bL at step s-1 (mover): (configs.get(s-1).(bL-1), bL_pre, t_old).

    Both have the same bL value (bL_pre) and same right = t_old.
    For EC: need left to match too: configs.get(k).(bL-1) = configs.get(s-1).(bL-1).

    This requires: proc bL-1 = (t-2)%n doesn't fire between steps k and s-1.

    If bL-1 is a far proc (not t, bL, or bR): it might fire in between.
    If bL-1 fires between k and s-1: the left value changes. No guaranteed match.

    But: if there's a step k such that bL-1 doesn't fire in [k, s-1):
    then values match. EC at bL.

    Is there always such a step k? If bL-1 fires at steps f_1, f_2, ..., f_m
    in the phase interior (before s-1): the last fire is at f_m. Take
    k = f_m + 1 (if f_m + 1 < s - 1). Then bL-1 doesn't fire in [f_m+1, s-1).
    EC at bL.

    Wait, we need k to be a NONMOVER for bL. At step f_m + 1:
    moverAt(f_m + 1) = some proc. Not bL (J=1 and the binary fire is at s-1).
    So bL is nonmover at f_m + 1. Good.

    BUT: there might be NO fires of bL-1 in the interior before s-1.
    If bL-1 doesn't fire at all in the phase: take k = first interior step.
    Then bL-1 doesn't fire in [k, s-1). EC at bL.

    If bL-1 fires once or more but all before s-1: take k = last fire + 1.
    EC at bL.

    The ONLY issue: what if bL-1 fires at step s-2 (the step just before s-1)?
    Then f_m = s - 2, k = f_m + 1 = s - 1. But s - 1 is the binary fire step
    (bL fires at s-1). So we can't use k = s-1 (that's the mover step for bL).

    Hmm. If bL-1 fires at s-2 and bL fires at s-1: we need a step between
    the bL-1 fire and the bL fire where bL is nonmover. But s-2 fires bL-1
    and s-1 fires bL. No step in between.

    Can we go further back? If bL-1 fires at s-2 and at some earlier step f_j:
    take k = f_j + 1. Between f_j + 1 and s-2: bL-1 doesn't fire.
    But: does bL-1 fire at s-2 in this scenario?

    Actually: bL-1 could fire multiple times. After the LAST fire of bL-1
    before s-2 (say at f_j), the value of bL-1 is fixed from f_j+1 to s-2.
    Then at s-2, bL-1 fires again, changing the value.

    The triple at bL at step f_j + 1: (val(bL-1) after f_j fire, bL_pre, t_old).
    The triple at bL at step s-1: (val(bL-1) after s-2 fire, bL_pre, t_old).
    Different left values if bL-1 changed between f_j and s-2.

    So: bL-1 firing at s-2 blocks EC at bL from this mechanism.

    But: bL-1 is a far proc with ms[bL-1] >= 2. After 2 fires: value might
    return to original (if binary) or change (if ternary).

    This is getting very case-specific. Let me take a step back.

    THE REAL QUESTION: Is the theorem true as stated?

    The theorem says: allNormalForm + noEC + sandwiched ternary + fc >= 2 +
    fc < CL + n >= 4 => False.

    All sub-threshold systems with sandwiched ternary have no valid instances
    (computationally confirmed). So the theorem IS vacuously true for the
    actual lower bound proof.

    But for the Lean formalization: we need to prove it from the hypotheses.
    The proof structure uses allNormalForm to derive FC balance, then
    derives EC. The sorry at line 1265 needs to produce hasEntryConflict gc.

    The CORRECT approach might need to derive EC at a different proc
    (not necessarily at t), or use a different mechanism entirely.
    """
    print("\nALTERNATIVE MECHANISM ANALYSIS")
    print("=" * 60)
    print()
    print("Key findings:")
    print("1. Forward EC at t: works when binary fire is NOT last in phase.")
    print("2. Binary-fires-last: blocks forward EC at t.")
    print("3. Cross-phase EC: blocked by t-value change at t-fire steps.")
    print("4. EC at bL: works if left(bL) doesn't fire between k and s-1.")
    print("5. EC at bL blocked if left(bL) fires at s-2 (just before bL fires at s-1).")
    print()
    print("QUESTION: can we always find EC SOMEWHERE?")
    print("ANSWER: Yes, because the system has no valid instances (the lower bound).")
    print("But we need to prove this from the hypotheses.")


def analyze_abstract_mover_words():
    """
    Generate all abstract mover words satisfying the constraints,
    check if the EC mechanism always applies.

    For small n (4, 5): enumerate all possible mover words with:
    - Each proc fires >= 2
    - Phase balance at t: fc(bL) + fc(bR) = fc(t)
    - All phases one-sided (J+K = 1)
    - No consecutive t-fires

    Check: in every such mover word, at least one one-sided phase has
    the binary fire NOT at the last position.
    """
    print("\n" + "=" * 60)
    print("ABSTRACT MOVER WORD ENUMERATION")
    print("=" * 60)

    # n=4, procs {0,1,2,3}, t=1, bL=0, bR=2, far={3}
    n = 4
    t, bL, bR = 1, 0, 2
    far = [3]

    # For n=4: CL >= 8 (each fires >= 2). Let's try CL = 8, 9, 10.
    for CL in range(8, 13):
        print(f"\n  CL = {CL}:")

        # Count valid mover words by backtracking
        count_total = 0
        count_all_last = 0

        def backtrack(word, pos, fc):
            nonlocal count_total, count_all_last
            if pos == CL:
                # Check: all procs fire >= 2
                if not all(fc[p] >= 2 for p in range(n)):
                    return
                # Check: phase balance fc(bL) + fc(bR) = fc(t)
                if fc[bL] + fc[bR] != fc[t]:
                    return
                # Check: no consecutive t-fires
                for k in range(CL):
                    if word[k] == t and word[(k+1) % CL] == t:
                        return
                # Check: all phases one-sided
                t_fires = [k for k in range(CL) if word[k] == t]
                fc_t = len(t_fires)
                if fc_t < 2:
                    return
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
                        return

                count_total += 1

                # Check: all one-sided phases have binary-fires-last
                all_last = True
                for idx in range(fc_t):
                    a = t_fires[idx]
                    s = t_fires[(idx + 1) % fc_t]
                    if s > a:
                        interior = list(range(a + 1, s))
                    else:
                        interior = list(range(a + 1, CL)) + list(range(0, s))
                    if not interior:
                        continue
                    # Find the binary fire
                    bin_idx = None
                    for i, k in enumerate(interior):
                        if word[k] in (bL, bR):
                            bin_idx = i
                            break
                    if bin_idx is not None and bin_idx == len(interior) - 1:
                        pass  # binary fires last
                    else:
                        all_last = False
                        break

                if all_last:
                    count_all_last += 1

                return

            for p in range(n):
                word.append(p)
                fc[p] += 1
                backtrack(word, pos + 1, fc)
                fc[p] -= 1
                word.pop()

        backtrack([], 0, defaultdict(int))
        print(f"    Valid mover words: {count_total}")
        print(f"    All-binary-fires-last: {count_all_last}")
        if count_total > 0:
            pct = 100 * (count_total - count_all_last) / count_total
            print(f"    Has at least one non-last: {count_total - count_all_last} ({pct:.1f}%)")

        if count_all_last > 0:
            print(f"    *** ALL-LAST EXISTS! Cross-phase argument incomplete. ***")


if __name__ == "__main__":
    verify_exists_good_phase()
    find_alternative_mechanism()
    analyze_abstract_mover_words()
