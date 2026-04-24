"""
Cross-Phase EC: Binary-Fires-Last mechanism.

When ALL one-sided phases have binary-fires-last: every t-fire step s
is immediately preceded by a binary fire at step s-1.

Key pattern at binary proc bL (when bL fires at step s-1):
  Step s-1: bL fires (mover at bL).
  Triple at bL: (val(bL-1), bL_pre, val(t))  where t hasn't fired since phase start.

  Step k (any nonmover step for bL before s-1 in same phase):
  Triple at bL: (val(bL-1)_at_k, bL_pre, val(t))

  If val(bL-1) is the same at k and s-1: EC AT bL.
  This happens when bL-1 (= t-2 mod n) doesn't fire between k and s-1.

Let's check computationally: do all-binary-fires-last mover words at n=4
always have EC at some proc?
"""

import itertools
from collections import defaultdict


def find_ec_in_abstract_cycle(word, CL, n, t, bL, bR, ms=None):
    """
    Given an abstract mover word and assigned state values,
    check for entry conflict.

    For abstract analysis: we don't have actual configs. We check
    structural conditions that FORCE EC.
    """
    pass


def enumerate_all_last_words_n4():
    """Enumerate all-binary-fires-last mover words at n=4."""
    n = 4
    t, bL, bR = 1, 0, 2
    far = [3]

    all_last_words = []

    for CL in range(8, 15):
        def backtrack(word, pos, fc):
            if pos == CL:
                if not all(fc[p] >= 2 for p in range(n)):
                    return
                if fc[bL] + fc[bR] != fc[t]:
                    return
                for k in range(CL):
                    if word[k] == t and word[(k + 1) % CL] == t:
                        return
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
                    # Check binary-fires-last
                    if not interior:
                        return
                    last_step = interior[-1]
                    if word[last_step] not in (bL, bR):
                        return  # not binary-fires-last

                all_last_words.append((CL, list(word)))

            else:
                for p in range(n):
                    word.append(p)
                    fc[p] += 1
                    backtrack(word, pos + 1, fc)
                    fc[p] -= 1
                    word.pop()

        backtrack([], 0, defaultdict(int))

    return all_last_words


def analyze_bfl_structure(word, CL, n, t, bL, bR):
    """
    Analyze the structure of a binary-fires-last mover word.

    Key question: in every binary-fires-last phase, what fires at step s-2?
    If step s-2 fires a far proc (not bL-1 = t-2): then the interval
    [s-2, s-1) has bL-1 not firing, and step s-2 is nonmover for bL.
    Triple at bL at s-2 matches triple at bL at s-1 (mover). EC at bL.

    If step s-2 fires bL-1 (= proc t-2 = proc (1-2)%4 = proc 3 for n=4):
    then bL-1 value changes at s-2. Need to look further back.
    """
    t_fires = [k for k in range(CL) if word[k] == t]
    fc_t = len(t_fires)

    phases = []
    for idx in range(fc_t):
        a = t_fires[idx]
        s = t_fires[(idx + 1) % fc_t]
        if s > a:
            interior = list(range(a + 1, s))
        else:
            interior = list(range(a + 1, CL)) + list(range(0, s))
        phases.append({'a': a, 's': s, 'interior': interior})

    # For each phase: check who fires at step s-2
    results = []
    for ph in phases:
        s = ph['s']
        interior = ph['interior']
        if len(interior) < 2:
            results.append('short')
            continue

        # Step s-1 fires bL or bR (binary-fires-last)
        s_minus_1 = interior[-1]
        binary_at_s1 = word[s_minus_1]

        # Step s-2 fires...
        s_minus_2 = interior[-2]
        firer_s2 = word[s_minus_2]

        # bL-1 = left(bL) = (bL - 1) % n
        bL_left = (bL - 1) % n  # = (t - 2) % n

        if binary_at_s1 == bL:
            # EC at bL: need left(bL) = bL_left to not fire between some k and s-1
            if firer_s2 == bL_left:
                results.append(f'bL_left_fires_at_s-2')
            else:
                results.append(f'bL_left_safe_at_s-2 => EC_AT_bL')
        elif binary_at_s1 == bR:
            # EC at bR: need right(bR) = bR_right = (bR + 1) % n to not fire
            bR_right = (bR + 1) % n  # = (t + 2) % n
            if firer_s2 == bR_right:
                results.append(f'bR_right_fires_at_s-2')
            else:
                results.append(f'bR_right_safe_at_s-2 => EC_AT_bR')

    return results


def check_all_bfl_words():
    """Check all binary-fires-last words for EC mechanism."""
    print("=" * 60)
    print("BINARY-FIRES-LAST: EC MECHANISM CHECK")
    print("=" * 60)

    n = 4
    t, bL, bR = 1, 0, 2

    words = enumerate_all_last_words_n4()
    print(f"\nTotal all-binary-fires-last words: {len(words)}")

    # Group by CL
    by_cl = defaultdict(list)
    for cl, w in words:
        by_cl[cl].append(w)

    for cl in sorted(by_cl.keys()):
        ws = by_cl[cl]
        print(f"\n  CL = {cl}: {len(ws)} words")

        all_have_ec_mech = True
        patterns = defaultdict(int)

        for w in ws:
            results = analyze_bfl_structure(w, cl, n, t, bL, bR)

            # Check: does at least one phase have the "safe" condition?
            has_safe = any('EC_AT' in r for r in results)
            pattern = tuple(results)
            patterns[pattern] += 1

            if not has_safe:
                all_have_ec_mech = False
                print(f"    *** NO EC MECHANISM: {w}")
                print(f"        Phases: {results}")

        if all_have_ec_mech:
            print(f"    ALL have EC mechanism! (via bL/bR neighbor safety)")
        else:
            print(f"    SOME lack EC mechanism.")

        # Show pattern distribution
        print(f"    Patterns:")
        for pat, cnt in sorted(patterns.items(), key=lambda x: -x[1])[:5]:
            print(f"      {pat}: {cnt}")


def deeper_analysis():
    """
    For the "blocked" cases: check if there's ALWAYS a step k further back
    where left(bL)/right(bR) doesn't change.

    The idea: even if left(bL) fires at s-2, there might be a step k < s-2
    where left(bL) last fired, and the interval [k+1, s-2) is clean.
    Then: triple at bL at step k+1 has left = post-fire value of left(bL) at k.
    Triple at bL at step s-1 has left = post-fire value of left(bL) at s-2.
    Different (left(bL) fired at k and at s-2 with potentially different values).

    But: if left(bL) is binary and fires an even number of times between
    k+1 and s-1: same value. EC.

    For ternary left(bL): more complicated.

    Actually: the key insight is that at n=4, there's only 1 far proc (proc 3).
    bL-1 = proc 3 = the far proc. bR+1 = proc 3 = the far proc.

    So: for n=4, left(bL) = right(bR) = the single far proc.

    In a binary-fires-last phase where bL fires at s-1:
    If the far proc fires at s-2: no EC from the simple mechanism at bL.
    But: the far proc has state count ms[3]. After even number of fires,
    it returns to its value.

    For n >= 5: there are multiple far procs. left(bL) = t-2, right(bR) = t+2.
    These are different procs (unless n = 4). They can't both fire at s-2.
    So: if bL fires at s-1, either left(bL) is safe at s-2 (EC at bL) or
    right(bR) is safe at s-2 (but bR doesn't fire here...).

    Wait, let me reconsider. In a phase where bL fires at s-1 (not bR):
    we try EC at bL. Need left(bL) safe. If left(bL) fires at s-2: blocked.

    In a phase where bR fires at s-1 (not bL):
    we try EC at bR. Need right(bR) safe. If right(bR) fires at s-2: blocked.

    For n >= 5: left(bL) = t-2 and right(bR) = t+2 are different far procs.
    In a given phase: at most one fires at s-2. So:
    - If bL fires at s-1 and left(bL) fires at s-2: try another phase.
    - If bR fires at s-1 and right(bR) fires at s-2: try another phase.

    Can ALL bL-phases have left(bL) firing at s-2 AND all bR-phases have
    right(bR) firing at s-2?

    At each t-fire, the step before is a binary fire, and the step before THAT
    is the "blocker" (left(bL) or right(bR)). This means:
    ... blocker, binary, t, ... blocker, binary, t, ...

    For fc(t) t-fires: fc(t) binary fires (each at s-1) and fc(t) blocker
    fires (each at s-2). The blockers use left(bL) for bL-phases and
    right(bR) for bR-phases.

    Total blocker fires = fc(t). But each blocker is a far proc that also
    fires at least 2 times total. If left(bL) is the blocker for all
    fc(bL) bL-phases: left(bL) fires at least fc(bL) times from this.
    Plus it might fire elsewhere. Total fc(left(bL)) >= fc(bL).

    For n >= 5: left(bL) and right(bR) are different. Their total
    "blocker" fires: fc(bL) + fc(bR) = fc(t). There are n - 3 far procs.

    If n - 3 >= 2 (n >= 5) and blocker fires = fc(t): other far procs
    have fc >= 2 each, contributing >= 2(n-4) fires. Total:
    CL >= fc(t) + fc(t) + fc(t) + 2(n-4) = 3fc(t) + 2(n-4).
    But CL = fc(t) + sum of phase lengths = fc(t) + CL - fc(t) = CL. Tautology.

    Hmm. Let me check: can blocker + binary + t consume all the fire budget?
    Pattern: ..., far1, ..., far1, blocker, binary, t, ... repeated.
    Between t-fires: "far1, ..., far1, blocker, binary" = some far fires +
    blocker + binary. If all-last: far fires + 1 blocker + 1 binary per phase.

    Total per phase: len = (far fires in phase) + 1 (blocker) + 1 (binary)?
    Wait no: the blocker IS a far fire. The binary IS bL/bR.
    Phase interior = (some far fires) + bL/bR at the end.
    The "blocker at s-2" is one of the far fires.

    So: in a length-L phase: L-1 far fires + 1 binary fire.
    One of the far fires (the last one, at position L-2) is the blocker.

    For the simple EC mechanism: need the blocker to NOT be left(bL)/right(bR).
    If the phase has L >= 3: there are L-1 >= 2 far fires. The last one is
    at position L-2 (step s-2). If there's a far fire at position L-3 (step s-3)
    that is NOT the blocker proc: then step s-3 is safe for the EC argument.
    Triple at bL at step s-3: left(bL) hasn't fired since some earlier step.
    But between s-3 and s-1: left(bL) fires at s-2. So left(bL) value at s-3
    differs from left(bL) value at s-1. No EC between s-3 and s-1.

    The EC mechanism is specifically: a nonmover step k with the SAME
    triple as the mover step s-1. This requires:
    - Same left(bL) value at k and s-1.
    - Same bL value at k and s-1 (both bL_pre since bL hasn't fired until s-1).
    - Same t value at k and s-1 (both t_old since t doesn't fire until s).

    The bL and t values always match (both constant in the phase until their
    respective fires). Only left(bL) might differ. It differs if left(bL)
    fires between k and s-1.

    So EC AT bL requires: a step k in [first interior step, s-2] where
    left(bL) doesn't fire in [k, s-1).

    If left(bL) fires at s-2: any step k has left(bL) firing at s-2 in [k, s-1).
    Unless k > s-2, but k must be < s-1. So k <= s-2, and s-2 is in [k, s-1).
    Blocked.

    UNLESS: k = s-1... but that's the mover step. Can't use.

    So: if left(bL) fires at s-2, EC at bL is blocked for ALL k.

    NEW IDEA: EC at left(bL) instead of bL.

    At step s-2: left(bL) fires (mover for left(bL)).
    Triple at left(bL) at s-2: (val(bL-2), val(bL-1), val(bL)).
    val(bL-2) = left-left(bL). val(bL-1) = left(bL) pre-fire. val(bL) = bL_pre.

    At some earlier step k (nonmover for left(bL)):
    Triple at left(bL) at k: (val(bL-2)_at_k, val(bL-1)_at_k, val(bL)_at_k).

    val(bL)_at_k = bL_pre (bL doesn't fire until s-1). Match.
    val(bL-1)_at_k = left(bL) at step k. If left(bL) fires between k and s-2:
    value changes. Need left(bL) not to fire in [k, s-2).

    This is the same problem recursively. We're just pushing the issue
    to the LEFT.

    For a ring: eventually we come back to t. The chain of "blockers"
    must terminate somewhere. But for small n (n=4): it wraps around quickly.

    I think the correct approach is COMPLETELY DIFFERENT.
    Instead of constant-triple at t or its neighbors: use the fact that
    in a binary-fires-last phase, bL fires at s-1 and bL is BINARY.
    After the fire: bL_post. Before: bL_pre. bL_post != bL_pre.

    The key is: bL fires exactly fc(bL) times (even). In the cycle:
    bL alternates between two values. At each bL fire: value flips.

    For even fc(bL): bL returns to original. The cycle of bL values at
    bL-fire steps is: v, 1-v, v, 1-v, ..., v, 1-v (fc(bL) entries,
    alternating). At nonmover steps between consecutive bL fires:
    bL value is constant.

    EC at bL needs: same triple at a mover and nonmover step.
    Mover steps have bL = pre-fire value. Nonmover steps have bL = whatever
    it currently is (pre or post from last fire).

    Let me just enumerate and check for n=4.
    """
    print("\n" + "=" * 60)
    print("DEEPER ANALYSIS: checking EC at ANY proc")
    print("=" * 60)

    n = 4
    t, bL, bR = 1, 0, 2
    # ms for n=4 sub-threshold with sandwiched ternary: ms = [2, 3, 2, 3]?
    # But ms[3] = 3, which is ternary. left(bL) = (bL-1)%4 = 3 (ternary).
    # For the EC argument: we need to know ms values.
    # At n=4 with sandwiched ternary t=1: ms[0]=2, ms[1]=3, ms[2]=2, ms[3]>=3.
    # Sub-threshold: product < 4*3^2 = 36.
    # ms = [2, 3, 2, 3]: product = 36 = threshold (not sub-threshold).
    # ms = [2, 3, 2, 2]: product = 24 < 36. But ms[3]=2 is binary.
    # Then proc 3 (binary) has neighbors 2 (binary) and 0 (binary).
    # 3 binary procs at {0, 2, 3} — but they're not consecutive: 0, 2, 3.
    # Is 3 sandwiched? ms[2]=2, ms[0]=2. Yes if ms[3]>=3. But ms[3]=2. No.

    # For n=4 with sandwiched ternary: must have ms[t]=3 and both neighbors binary.
    # ms = [2, 3, 2, x] where x >= 2. Product = 12x. Threshold = 36. Sub: 12x < 36 => x < 3 => x = 2.
    # ms = [2, 3, 2, 2]. Product = 24. Proc 1 ternary, neighbors 0, 2 both binary. Sandwiched.
    # Proc 3 binary, neighbors 2, 0 both binary. Not ternary, doesn't count.

    ms = [2, 3, 2, 2]
    print(f"\n  ms = {ms}, n = {n}, product = {2*3*2*2}, threshold = 36")
    print(f"  Sandwiched: t=1 (ms[0]=2, ms[2]=2)")
    print(f"  left(bL) = left(proc 0) = proc 3, ms[3] = 2 (binary)")

    # For this ms: all procs except t=1 are binary.
    # Good cycles: every proc fires even number of times.
    # Phase balance at t=1: fc(0) + fc(2) = fc(1).
    # All phases one-sided: J+K = 1 per phase.

    # Now: does EC ALWAYS hold for mover words with these constraints?
    # Enumerate abstract mover words and check EC structurally.

    # For EC at bL = proc 0:
    # left(bL) = proc 3 (binary). right(bL) = t = proc 1 (ternary).
    # EC at bL: same (val(3), val(0), val(1)) at mover and nonmover step.

    # In all-BFL word: step s-1 fires bL, step s fires t.
    # At step s-1: (val3, val0_pre, val1_old). bL fires here.
    # At step k (earlier, nonmover for bL): (val3_at_k, val0_pre, val1_old).
    # Need: val3_at_k = val3_at_{s-1}. Requires: proc 3 doesn't fire in [k, s-1).

    # Proc 3 fires somewhere. If it fires at s-2: blocked.
    # If it fires only BEFORE s-2: can find k between last proc-3 fire and s-1.

    # But wait: ALL procs must fire >= 2 times. Proc 3 (binary) fires even, >= 2.
    # The all-BFL pattern allocates proc 3 fires to specific positions.

    # Let's just enumerate and count.

    print("\n  Enumerating all-BFL mover words with ms=[2,3,2,2]...")

    words = []
    for CL in range(8, 15):
        def bt(word, pos, fc):
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
                all_one = True
                all_last = True
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
                        all_one = False
                        return
                    if interior and word[interior[-1]] not in (bL, bR):
                        all_last = False

                if all_one and all_last:
                    words.append((CL, list(word)))

            else:
                for p in range(n):
                    word.append(p)
                    fc[p] += 1
                    bt(word, pos + 1, fc)
                    fc[p] -= 1
                    word.pop()

        bt([], 0, defaultdict(int))

    print(f"  Found {len(words)} all-BFL words")

    # For each: check if proc 3 always fires at s-2
    for cl, w in words[:20]:
        t_fires_pos = [k for k in range(cl) if w[k] == t]
        fc_t = len(t_fires_pos)

        detail = []
        for idx in range(fc_t):
            a = t_fires_pos[idx]
            s = t_fires_pos[(idx + 1) % fc_t]
            if s > a:
                interior = list(range(a + 1, s))
            else:
                interior = list(range(a + 1, cl)) + list(range(0, s))

            # Who fires at s-2?
            if len(interior) >= 2:
                s2_firer = w[interior[-2]]
                s1_firer = w[interior[-1]]
                detail.append(f"s-2={s2_firer},s-1={s1_firer}->t")
            else:
                s1_firer = w[interior[-1]] if interior else '?'
                detail.append(f"s-1={s1_firer}->t")

        print(f"  CL={cl}: {w}  | {detail}")


if __name__ == "__main__":
    check_all_bfl_words()
    deeper_analysis()
