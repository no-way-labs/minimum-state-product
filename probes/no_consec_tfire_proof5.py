"""
Final proof investigation: check if fc(t) is always even for sandwiched ternary,
and if not, find the additional argument for odd fc(t).
"""

import itertools
import random


def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))


def privileged_set(config, fs, n):
    priv = []
    for i in range(n):
        L = config[(i - 1) % n]
        S = config[i]
        R = config[(i + 1) % n]
        if fs[i][(L, S, R)] != S:
            priv.append(i)
    return priv


def find_good_cycle_dict(ms, fs):
    n = len(ms)
    configs = all_configs(ms)
    good = {}
    for c in configs:
        priv = privileged_set(c, fs, n)
        if len(priv) == 1:
            good[c] = priv[0]
    if not good:
        return None, None
    succ = {}
    for c, mover in good.items():
        lst = list(c)
        L, S, R = c[(mover-1)%n], c[mover], c[(mover+1)%n]
        lst[mover] = fs[mover][(L, S, R)]
        nxt = tuple(lst)
        if nxt in good:
            succ[c] = (nxt, mover)
    if not succ:
        return None, None
    start = next(iter(succ))
    visited = {}
    current = start
    step = 0
    while current not in visited:
        if current not in succ:
            return None, None
        visited[current] = step
        current, _ = succ[current]
        step += 1
    cs = visited[current]
    cyc_c = []
    cyc_m = []
    c = current
    for _ in range(step - cs):
        if c not in succ:
            return None, None
        nxt, m = succ[c]
        cyc_c.append(c)
        cyc_m.append(m)
        c = nxt
    return cyc_c, cyc_m


def check_validity_full(ms, fs):
    n = len(ms)
    configs = all_configs(ms)
    good_configs = set()
    priv_map = {}
    for c in configs:
        priv = privileged_set(c, fs, n)
        priv_map[c] = priv
        if len(priv) == 0:
            return False
        if len(priv) == 1:
            good_configs.add(c)
    if not good_configs:
        return False
    for c in good_configs:
        mover = priv_map[c][0]
        lst = list(c)
        L, S, R = c[(mover-1)%n], c[mover], c[(mover+1)%n]
        lst[mover] = fs[mover][(L, S, R)]
        nxt = tuple(lst)
        if nxt not in good_configs:
            return False
    bad_set = set(c for c in configs if c not in good_configs)
    visited = set()
    for c in bad_set:
        if c in visited:
            continue
        path_set = set()
        cur = c
        while cur not in visited and cur in bad_set:
            if cur in path_set:
                return False
            path_set.add(cur)
            priv = priv_map[cur]
            mover = priv[0]
            lst = list(cur)
            L, S, R = cur[(mover-1)%n], cur[mover], cur[(mover+1)%n]
            lst[mover] = fs[mover][(L, S, R)]
            cur = tuple(lst)
        visited.update(path_set)
    return True


def has_ec(cyc_configs, cyc_movers, n):
    CL = len(cyc_configs)
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        for k in range(CL):
            c = cyc_configs[k]
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if cyc_movers[k] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True
    return False


def check_fc_parity_distribution():
    """Check fc(t) parity for sandwiched ternary across valid systems."""
    random.seed(42)

    ms_list = [
        [2, 3, 2, 2, 2],       # n=5
        [2, 3, 2, 2, 2, 2],    # n=6
        [2, 3, 2, 2, 2, 2, 2], # n=7
        [2, 2, 3, 2, 2],       # n=5
        [2, 3, 2, 2, 3],       # n=5
    ]

    print("=== Fire count parity distribution ===")
    print()

    for ms in ms_list:
        n = len(ms)
        threshold = 4 * 3 ** (n - 2)
        prod = 1
        for m in ms:
            prod *= m
        nbinary = sum(1 for m in ms if m == 2)
        if prod >= threshold or nbinary < 3:
            continue

        sandwiches = [i for i in range(n) if ms[i] >= 3 and ms[(i-1)%n] == 2 and ms[(i+1)%n] == 2]
        if not sandwiches:
            continue

        domains = []
        for i in range(n):
            m_L = ms[(i-1)%n]
            m_S = ms[i]
            m_R = ms[(i+1)%n]
            dom = list(itertools.product(range(m_L), range(m_S), range(m_R)))
            domains.append((dom, m_S))

        fc_counts = {}  # t -> {fc_val -> count}
        total_valid = 0

        for trial in range(500000):
            fs = []
            for dom, m_S in domains:
                f = {k: random.randint(0, m_S - 1) for k in dom}
                fs.append(f)

            if not check_validity_full(ms, fs):
                continue
            total_valid += 1

            cyc_c, cyc_m = find_good_cycle_dict(ms, fs)
            if cyc_c is None:
                continue

            CL = len(cyc_m)
            for t in sandwiches:
                fc_t = sum(1 for m in cyc_m if m == t)
                if t not in fc_counts:
                    fc_counts[t] = {}
                fc_counts[t][fc_t] = fc_counts[t].get(fc_t, 0) + 1

        print(f"ms={ms}, n={n}, valid={total_valid}")
        for t in sorted(fc_counts):
            even_count = sum(v for k, v in fc_counts[t].items() if k % 2 == 0)
            odd_count = sum(v for k, v in fc_counts[t].items() if k % 2 == 1)
            total = even_count + odd_count
            print(f"  t={t}: even_fc={even_count} ({100*even_count//max(total,1)}%), odd_fc={odd_count} ({100*odd_count//max(total,1)}%)")
            for fc_val in sorted(fc_counts[t]):
                cnt = fc_counts[t][fc_val]
                parity = "even" if fc_val % 2 == 0 else "odd"
                print(f"    fc(t)={fc_val} ({parity}): {cnt}")
        print()


def verify_parity_at_n3():
    """Check fc(t) parity in the n=3 counterexamples."""
    print("=== n=3 counterexample analysis ===")
    print("All n=3 counterexamples had fc(t)=3 (odd).")
    print("The parity argument handles even fc(t) but not odd.")
    print()


def prove_comprehensive():
    """
    THE COMPREHENSIVE PROOF.

    THEOREM: In a good cycle with sandwiched ternary t (m_t=3, m_{bL}=m_{bR}=2),
    all TernaryPhases normalForm, no EC, fc(t)>=2, fc(t)<CL, n>=9:
    t does not fire at two consecutive steps (linear or cyclic).

    PROOF:

    We use h_phase_le1 (already proved: each TernaryPhase has J+K<=1)
    and normalForm (each TernaryPhase has J+K>=1, specifically not BothEven).

    Suppose for contradiction that t fires at consecutive steps.

    LINEAR CASE: moverAt(a) = t, moverAt(a+1) = t, no t-fires between a and a+1.
    (The "no t-fires between" is vacuously true since there's nothing between.)

    Step 1: Count phases cyclically.
    The fc(t) t-fire steps divide the cycle into fc(t) cyclic gaps.
    The gap between step a and step a+1 is EMPTY (0 intermediate steps).
    Each other gap is non-empty and forms a TernaryPhase.

    Step 2: Sum J+K over all gaps.
    Non-empty gaps: J+K = 1 (from h_phase_le1 + normalForm: 1 <= J+K <= 1).
    Empty gap: J+K = 0.
    Total: fc(bL) + fc(bR) = (fc(t) - 1) * 1 + 0 = fc(t) - 1.

    Step 3: Binary parity.
    fc(bL) is even, fc(bR) is even (binary parity).
    fc(bL) + fc(bR) = fc(t) - 1.
    If fc(t) even: fc(t) - 1 odd. But fc(bL)+fc(bR) even. CONTRADICTION.

    Step 4: Odd fc(t) case.
    We need: fc(t) - 1 = fc(bL) + fc(bR) >= fc(bL) + fc(bR).
    This is consistent (both sides equal).
    But: from the sub-threshold condition and n >= 9, we can derive that
    fc(bL) + fc(bR) >= fc(t) WITHOUT the no-consec hypothesis.

    HOW? The key insight: in the WRAP-AROUND phase, J+K >= 1 (from normalForm).
    But we already counted the wrap-around as one of the fc(t) phases.

    Wait, let me re-examine. The fc(t) phases include all cyclic gaps.
    If the empty phase is between positions a and a+1 (both interior to the cycle):

    The phases are (cyclically, starting from the empty one):
    Phase 0: empty (steps a to a+1)
    Phase 1: non-empty (steps a+1 to next_t_fire)
    ...
    Phase fc(t)-1: non-empty (previous_t_fire to a)

    Each non-empty phase has J+K = 1. Total from non-empty: fc(t)-1.
    Empty contributes 0. Grand total: fc(t)-1.

    For odd fc(t): fc(t)-1 even, consistent with binary parity.
    fc(bL) + fc(bR) = fc(t) - 1.

    Now: can we derive a contradiction from fc(bL)+fc(bR) = fc(t)-1?

    The upper bound from AllNormalFormFalse2: fc(bL)+fc(bR) <= fc(t) (via h_le).
    This is proved BEFORE hno_consec, using h_phase_le1.
    Wait, is h_le proved before hno_consec? Let me check.

    Looking at the code: h_le is at line 1128, hno_consec at line 1237.
    But h_le is part of the same sorry block. Actually, h_le is:
    """

    print("THE PROOF (odd fc(t) case):")
    print()
    print("Step 4 (key): we need a new argument for odd fc(t).")
    print()
    print("APPROACH: The empty phase creates a config-triple at t (values v, v+1, v+2)")
    print("all with the same background. This complete fiber, combined with no-EC and")
    print("the transition function constraints, forces an entry conflict at a binary neighbor.")
    print()
    print("DETAIL:")
    print("At step a:   config C_a = (B, t=v).     Mover = t. f_t(c_L, v, c_R) != v.")
    print("At step a+1: config C_{a+1} = (B, t=v+1). Mover = t. f_t(c_L, v+1, c_R) != v+1.")
    print("At step a+2: config C_{a+2} = (B, t=v+2). Mover != t.")
    print()
    print("Step 1: f_t(c_L, v+2, c_R) = v+2 (otherwise 3-consec -> config collision).")
    print()
    print("Step 2: At C_{a+2}, the mover is bL or bR (only neighbors affected).")
    print("WLOG mover = bL. Then: f_{bL}(LL, c_L, v+2) != c_L.")
    print("And: f_{bL}(LL, c_L, v) = c_L, f_{bL}(LL, c_L, v+1) = c_L.")
    print()
    print("Step 3: bR at C_{a+2}: f_{bR}(v+2, c_R, RR) = c_R.")
    print("Plus: f_{bR}(v, c_R, RR) = c_R, f_{bR}(v+1, c_R, RR) = c_R.")
    print("So f_{bR}(*, c_R, RR) = c_R for ALL 3 L-values.")
    print("bR NEVER fires with S=c_R and R=RR.")
    print()
    print("Step 4: Now consider the phase AFTER the empty gap.")
    print("Phase 1 starts at step a+2 (after C_{a+2}). Mover at a+2 = bL.")
    print("So J=1 in phase 1 (bL fires). K=0 (bR doesn't fire -- does it?).")
    print()
    print("Actually: phase 1 goes from step a+2 to the next t-fire (say step s').")
    print("J1+K1 = 1 (from J+K=1 per phase).")
    print("The first step of phase 1 is a+2, where bL fires. So J1 >= 1.")
    print("Since J1+K1 = 1: J1=1, K1=0. bL fires ONLY at step a+2 in phase 1.")
    print("And bR doesn't fire in phase 1.")
    print()
    print("Step 5: Now consider phase fc(t)-1 (the phase BEFORE the empty gap).")
    print("This phase ends at step a (where t fires). J_{fc(t)-1}+K_{fc(t)-1} = 1.")
    print("Who fires in this phase? Either bL (J=1, K=0) or bR (J=0, K=1).")
    print()
    print("Step 6: For n >= 4, RR = proc(t+2) is distinct from bL.")
    print("bL's fire at step a+2 changes bL's value, not RR's value.")
    print("So at step a+3: bR's context includes R=RR (unchanged).")
    print("bR's value is still c_R (bR hasn't fired).")
    print("From Step 3: bR doesn't fire with (S=c_R, R=RR). So bR stays nonprivileged.")
    print()
    print("This means: throughout phase 1 (and beyond, until RR changes or bR's value changes):")
    print("bR remains at c_R and can't fire. bR is 'frozen'.")
    print()
    print("Step 7: bR must fire eventually (fc(bR) >= 2 from fairness + binary parity).")
    print("For bR to fire: need (bR != c_R) or (R != RR). Since bR only changes when it fires")
    print("(unique privilege means only one proc fires per step), bR stays at c_R until it fires.")
    print("So bR's first fire must have R != RR, meaning RR must change first.")
    print()
    print("Step 8: RR changes only when proc t+2 fires.")
    print("Proc t+2 fires only when it's the unique privileged proc at some config.")
    print("This can happen at any point in the cycle.")
    print()
    print("Step 9: NOW THE KEY.")
    print("bR = c_R throughout ALL phases until RR changes.")
    print("In each phase where bR is frozen (c_R, R=RR): bR doesn't fire, so K=0.")
    print("These phases have J=1 (to satisfy J+K=1).")
    print("So bL fires in EVERY phase where bR is frozen.")
    print()
    print("The number of 'frozen' phases = F. In these phases: fc(bL) gains F fires.")
    print("But fc(bL) is even. And the remaining fc(t)-1-F phases have bR firing (K=1, J=0).")
    print("So fc(bR) = fc(t)-1-F. And fc(bL) >= F + (bL fires in non-frozen phases too?).")
    print()
    print("Actually, in non-frozen phases (where bR is NOT frozen): K=1 or K=0.")
    print("If K=1: J=0, bL doesn't fire.")
    print("If K=0: J=1, bL fires.")
    print()
    print("Total: fc(bL) = #{phases with J=1} = #{phases with K=0} = fc(t)-1 - fc(bR).")
    print("Binary parity: fc(bL) even, fc(bR) even.")
    print()
    print("The frozen phases all have K=0, so they contribute to fc(bL).")
    print("After RR changes: bR might be able to fire. Then some phases have K=1.")
    print()
    print("This structural constraint is strong but doesn't immediately give a contradiction")
    print("for odd fc(t). Let me think about the CYCLIC wrap...")
    print()

    # THE REAL PROOF FOR ODD fc(t):
    # Actually, I think the proof is simpler than I've been making it.
    #
    # The key: h_le (fc(bL)+fc(bR) <= fc(t)) is proved in AllNormalFormFalse2
    # BEFORE hno_consec. It uses h_phase_le1 and the phase decomposition.
    # But h_le is actually at line 1128, and it says:
    # "fc(bL)+fc(bR) <= fc(t)". This uses hall_le1 (each consecutive pair has sum <= 1).
    # And hall_le1 is proved using within_phase_ec (non-empty gap) and the empty gap case
    # where it uses... wait, let me re-read lines 1180-1202.

    # Lines 1180-1202: h_le proof.
    # It computes: hall_le1 (each pair has J+K <= 1).
    # Then at line 1193: "Use intervalFireCount_add_phases to bound total."
    # Line 1201: sorry.

    # AH. h_le itself has a sorry at line 1201!
    # So h_le is NOT yet proved. It ALSO depends on infrastructure.

    # So the situation is:
    # - h_phase_le1 proved (each non-empty phase has J+K <= 1): YES, sorry-free
    # - h_le (total fc(bL)+fc(bR) <= fc(t)): NOT proved (sorry at line 1201)
    # - hno_consec: NOT proved (sorry at line 1237)

    # These may be independent or related. Let me check if h_le needs hno_consec.
    # h_le uses hall_le1 which handles the empty gap case at line 1182:
    # "Empty gap: a+1 >= s, so a+1 = s. ifc on [a, s) = 0."
    # The empty gap gives J+K = 0 <= 1. So h_le handles it fine!
    # The sorry at 1201 is about something else: the CYCLIC DECOMPOSITION.

    # So h_le needs: decompose the cycle into fc(t) phases (some empty, some not),
    # show total J+K <= fc(t) using hall_le1 (each <= 1) and there being fc(t) phases.
    # This is a combinatorial fact about cyclic decompositions.

    # If h_le could be proved: then fc(bL)+fc(bR) <= fc(t) AND (with empty phase)
    # fc(bL)+fc(bR) = sum J+K >= fc(t)-1 (from normalForm on non-empty phases).
    # So fc(t)-1 <= fc(bL)+fc(bR) <= fc(t).
    # Binary parity: fc(bL)+fc(bR) even.
    # fc(t) even -> fc(t)-1 odd: only fc(t) works. But fc(t) is even and fc(t) is fine.
    # Wait: if fc(bL)+fc(bR) is even and >= fc(t)-1:
    #   fc(t) even: must be fc(t) (the only even value in {fc(t)-1, fc(t)}).
    #   fc(t) odd: must be fc(t)-1 (the only even value in {fc(t)-1, fc(t)}).

    # If fc(bL)+fc(bR) = fc(t) (even fc(t) case): each phase has J+K=1.
    # But empty phase has J+K=0. Total = fc(t)-1 < fc(t). Contradiction with = fc(t).
    # So even fc(t) is impossible.

    # If fc(bL)+fc(bR) = fc(t)-1 (odd fc(t) case): consistent but need to show contradiction.
    # fc(bL)+fc(bR) <= fc(t) gives fc(t)-1 <= fc(t): trivially true.

    # So even with h_le, odd fc(t) isn't contradicted by counting alone.

    # WAIT. I just realized: if h_le gives fc(bL)+fc(bR) <= fc(t), and we have
    # fc(bL)+fc(bR) = fc(t)-1 (from counting with empty phase), then:
    # fc(t)-1 <= fc(t). True. No contradiction.
    # But also: fc(bL)+fc(bR) = fc(t) is impossible (would need all phases to have J+K=1,
    # but empty phase has J+K=0).

    # So for even fc(t): fc(bL)+fc(bR) must be even and in {fc(t)-1, fc(t)}.
    #   fc(t)-1 is odd: not even. fc(t) is even: possible.
    #   But fc(bL)+fc(bR) = fc(t) requires all phases J+K=1, impossible with empty phase.
    #   So fc(bL)+fc(bR) has no valid even value in {fc(t)-1, fc(t)}. CONTRADICTION.

    # For odd fc(t): fc(bL)+fc(bR) must be even and in {fc(t)-1, fc(t)}.
    #   fc(t)-1 is even: possible. fc(t) is odd: not even.
    #   So fc(bL)+fc(bR) = fc(t)-1. Consistent.
    #   No contradiction from counting.

    print("CORRECTED ANALYSIS:")
    print()
    print("With h_le (fc(bL)+fc(bR) <= fc(t)) and empty phase:")
    print("  fc(bL)+fc(bR) in {fc(t)-1, fc(t)}")
    print("  Binary parity: even.")
    print()
    print("  Even fc(t): fc(t) is even (good), fc(t)-1 is odd (bad).")
    print("    fc(bL)+fc(bR) must be fc(t) (only even option).")
    print("    But empty phase means total <= fc(t)-1 < fc(t). Contradiction. QED for even.")
    print()
    print("  Odd fc(t): fc(t) is odd (bad), fc(t)-1 is even (good).")
    print("    fc(bL)+fc(bR) = fc(t)-1. Consistent. No contradiction from counting.")
    print()
    print("NEED: additional argument for odd fc(t).")
    print()

    # OK so the real question is: how to handle odd fc(t)?
    # Let me think about whether the hypotheses (n>=9, sub-threshold, all-normalForm,
    # no-EC) actually force fc(t) to be even. Or if there's a completely different
    # argument for odd fc(t).

    # Actually, upon reflection: what if the proof of hno_consec doesn't need
    # to handle odd fc(t) at all, because the odd case is handled by the CYCLIC version?

    # hno_consec is the LINEAR version: a.val < s.val.
    # hno_cyclic_consec is the CYCLIC version.

    # For the linear version: if a and a+1 are in the interior (not wrapping around),
    # then the phase structure is as described.

    # For the cyclic version: the last step and the first step are consecutive.
    # This affects the wrap-around phase.

    # Hmm, actually hno_consec and hno_cyclic_consec are both needed by
    # sparse_phase_sum_ge. The linear version is used to establish that every
    # interior pair has J+K >= 1 (non-empty gap). The cyclic version is used
    # to ensure the wrap-around gap is non-empty.

    # Let me think about this differently. Maybe instead of counting arguments,
    # use the DIRECT config-collision argument from the beginning.

    # DIRECT PROOF (not using counting at all):
    #
    # If t fires at consecutive steps a, a+1:
    # C_a = (B, t=v), C_{a+1} = (B, t=v+1), C_{a+2} = (B, t=v+2).
    # f_t(c_L, v+2, c_R) = v+2 (Step 1).
    # Unique privileged at C_{a+2}: one of bL, bR (Step 2).
    #
    # For n >= 4: the argument about bR being frozen (Step 3) means
    # f_{bR}(*, c_R, RR) = c_R for all L-values.
    #
    # This is 3 entries in bR's transition table ALL mapping to c_R.
    # bR's transition table has m_L * m_S * m_R entries. With m_L = m_t = 3
    # (t is ternary), m_S = 2, m_R = m_{t+2}: 3 * 2 * m_{t+2} entries.
    # We've constrained 3 of them (the (*, c_R, RR) slice).
    #
    # For bR to fire at all: f_{bR}(L, S, R) != S for some (L,S,R).
    # The 3 constrained entries give f_{bR}(*, c_R, RR) = c_R = S. Not firing.
    # bR fires from: (L, 1-c_R, R) or (L, c_R, R != RR).
    #
    # Now: the GOOD CYCLE visits all good configs. Some configs have bR = c_R
    # and right-neighbor = RR. At these configs: bR is nonprivileged.
    # Other configs have bR = 1-c_R or right-neighbor != RR: bR MIGHT be privileged.
    #
    # bR fires fc(bR) >= 2 times. The first fire after step a+2:
    # bR = c_R (frozen). For bR to fire: need right-neighbor != RR.
    # This requires proc(t+2) to have fired (changing from RR to something else).
    #
    # When does proc(t+2) fire? At some step in the cycle.
    # Between step a+2 and the first proc(t+2) fire: bR can't fire.
    # After proc(t+2) fires: bR's right-neighbor changes, enabling bR to fire.
    #
    # This is valid but doesn't give EC directly.
    #
    # THE ENTRY CONFLICT AT bR:
    #
    # bR sees (*, c_R, RR) as nonmover (all 3 L-values give c_R).
    # When bR fires (from c_R or 1-c_R): the context has R != RR or S != c_R.
    #
    # For EC at bR: need a context (L0, S0, R0) that appears as both mover and nonmover.
    # The 3 nonmover contexts (v, c_R, RR), (v+1, c_R, RR), (v+2, c_R, RR) are ALWAYS nonmover.
    # If any of these appears as mover: EC. But they can't (f_{bR}(*, c_R, RR) = c_R = S).
    #
    # The mover contexts of bR have R != RR or S != c_R. These are DIFFERENT from the
    # always-nonmover contexts. So no EC at bR from this analysis alone.
    #
    # Similarly for bL: the always-nonmover contexts at bL are (LL, c_L, v), (LL, c_L, v+1).
    # The mover context at step a+2 is (LL, c_L, v+2).
    # If (LL, c_L, v+2) is always mover: no EC at bL.
    # But if at some OTHER step, bL sees (LL, c_L, v+2) as nonmover: EC at bL!
    #
    # Does (LL, c_L, v+2) ever appear as nonmover for bL?
    # At step a+2: bL is the mover. Context (LL, c_L, v+2), mover.
    # At other steps: if bL = c_L and left-neighbor = LL and right-neighbor(=t) = v+2:
    #   this is a nonmover step for bL iff moverAt != bL.
    #   Is there such a step? The cycle visits configs with bL=c_L, LL=LL_val, t=v+2.
    #   Step a+2 is one such config (the one we know). Are there others?
    #
    # If the cycle visits another config with the same (LL, c_L, v+2) at bL's context
    # but with a different mover: that's EC at bL.
    #
    # But how many configs have (LL, c_L, v+2) at bL's neighbors?
    # LL is proc(t-2)'s value. For n >= 5, proc(t-2) is distinct from t, bL, bR, proc(t+2).
    # So LL is determined by the rest of the ring.
    #
    # At step a+2: the full config is (B, t=v+2). B includes LL.
    # The next steps may change LL (if proc(t-2) fires).
    # If LL doesn't change: the context (LL, c_L, v+2) persists.
    # At step a+2: bL fires (mover). At step a+3: bL = 1-c_L (changed).
    # So the context at bL at step a+3 is (LL, 1-c_L, v+2). Different S. Not the same context.
    # But what about step a+2 vs. some step j where bL=c_L again and t=v+2 and LL unchanged?
    # bL returns to c_L (binary parity), but by then t might not be v+2 or LL might have changed.
    #
    # This depends on the cycle structure and can't be resolved without more information.

    # Let me try yet another approach.

    # APPROACH: For n >= 5, use the fact that C_a and C_{a+2} are Hamming-1 at position t.
    # Both are good configs in the cycle. The cycle has length CL.
    # The distance in the cycle between C_a (step a) and C_{a+2} (step a+2) is 2.
    # These are non-adjacent in the cycle graph (adjacent means distance 1).
    # They differ at exactly 1 position (t).
    #
    # The cycle visits C_a at step a, with mover t.
    # It visits C_{a+2} at step a+2, with mover bL (say).
    # C_a and C_{a+2} are distance 2 apart, Hamming distance 1.
    #
    # Is this a contradiction? Not directly. Hamming-1 non-adjacent pairs can exist.
    #
    # But: consider the config C_a = (B, t=v) and C_{a+2} = (B, t=v+2).
    # At C_a: t is privileged. At C_{a+2}: t is NOT privileged.
    # So the PRIVILEGE STATUS of t differs at these Hamming-1 configs.
    # This constrains f_t: f_t(c_L, v, c_R) != v but f_t(c_L, v+2, c_R) = v+2.
    #
    # Now: consider the config C* = (B, t=v') for v' = v+2 but at a DIFFERENT step j.
    # If C* = C_{a+2} (same config): j = a+2 (configs are unique in the cycle).
    # If C* != C_{a+2}: different background, not relevant.
    #
    # Each config appears exactly once in the cycle. So (B, t=v+2) appears only at step a+2.

    print()
    print("FINAL APPROACH: Use 3-consecutive-impossible + config collision.")
    print()
    print("For hno_consec (linear): Suppose a+1 = s. Then C_a, C_{a+1}, C_{a+2} share background B.")
    print("Step 1: f_t(c_L, v+2, c_R) = v+2 (else 3-consec -> collision).")
    print("Step 2: unique privileged at C_{a+2} is bL or bR.")
    print("Step 3: the 3 configs (B, v), (B, v+1), (B, v+2) are all in the cycle.")
    print("  These are 3 of the cycle's CL configs, forming a 'complete t-fiber' over B.")
    print()
    print("Step 4: Since (B, v+2) is a nonmover config for t (f_t(c_L,v+2,c_R) = v+2),")
    print("  and (B, v), (B, v+1) are mover configs for t:")
    print("  The transition f_t at slice (c_L, *, c_R) has an ABSORBING VALUE v+2.")
    print("  t can leave v+2 only with a DIFFERENT (L, R) context.")
    print()
    print("Step 5: For the cycle to be a valid good cycle with all procs firing:")
    print("  t must fire from v+2 eventually (with a different (L,R) context).")
    print("  Before t fires from v+2: bL or bR must change (to create a different context).")
    print("  Between C_{a+2} and the next t-fire from v+2: at least one binary fires.")
    print("  This is guaranteed by the phase structure (J+K >= 1 in each non-empty phase).")
    print()
    print("Step 6: PARITY CONTRADICTION for even fc(t). (Proved above.)")
    print()
    print("Step 7: For odd fc(t), use the CYCLIC PHASE PARITY argument:")
    print("  The phase adjacent to the empty gap (phase after step a+1) has J+K=1.")
    print("  The empty gap has J+K=0.")
    print("  Consider the sequence of phases: ..., P_{i-1}, EMPTY, P_{i+1}, ...")
    print("  P_{i-1} has J+K=1 (one binary fires).")
    print("  P_{i+1} has J+K=1 (one binary fires).")
    print("  EMPTY has J+K=0.")
    print()
    print("  In phase P_{i+1}: one binary fires. From Step 2: mover at a+2 is bL or bR.")
    print("  WLOG mover = bL. So P_{i+1} has J=1, K=0.")
    print("  This means: the binary fire in P_{i+1} is bL.")
    print()
    print("  In phase P_{i-1}: J+K=1. Either J=1 (bL fires) or K=1 (bR fires).")
    print()
    print("  KEY: at the boundary between P_{i-1} and EMPTY (step a, t fires):")
    print("  bL = c_L, bR = c_R. These are the values at the START of the empty gap.")
    print("  In P_{i-1}: the boundary values at the END are (c_L, c_R) at (bL, bR).")
    print("  If bL fires in P_{i-1} (J=1): bL changed once in P_{i-1}. Since bL=c_L at step a,")
    print("    bL must have been 1-c_L at the start of P_{i-1} and changed to c_L.")
    print("  If bR fires in P_{i-1} (K=1): similarly bR was 1-c_R at start, changed to c_R.")
    print()
    print("  Now consider the CYCLIC structure. As we go around all fc(t) phases:")
    print("  Each phase has one binary fire. The sequence of (bL_val, bR_val) at each phase boundary")
    print("  changes by one flip per phase.")
    print()
    print("  Starting from (c_L, c_R) at the empty gap:")
    print("  Phase i+1: bL flips to 1-c_L. Boundary: (1-c_L, c_R).")
    print("  Phase i+2: one binary flips. Either (c_L, c_R) or (1-c_L, 1-c_R).")
    print("  ...")
    print("  After fc(t)-1 phases: we return to (c_L, c_R) (cycle closes).")
    print("  This requires an EVEN number of bL-flips and EVEN number of bR-flips.")
    print("  fc(bL) = #{phases with J=1} must be even.")
    print("  fc(bR) = #{phases with K=1} must be even.")
    print("  fc(bL) + fc(bR) = fc(t) - 1.")
    print("  Both even: fc(t) - 1 must be even, so fc(t) odd. CONSISTENT for odd fc(t).")
    print()
    print("So counting alone doesn't resolve odd fc(t).")
    print()
    print("NEED: a structural argument that uses n >= 9 or sub-threshold specifically.")
    print("The constraint from Step 3 (bR frozen with (S=c_R, R=RR)) might interact with")
    print("n >= 9 to force a contradiction.")
    print()

    # OK I think I need to step back and look at what EXISTING Lean infrastructure
    # could help. Let me check if there's a "Hamming-1" or "config collision" lemma.


def main():
    print("=" * 70)
    print("FINAL PROOF INVESTIGATION")
    print("=" * 70)
    print()

    verify_parity_at_n3()
    check_fc_parity_distribution()
    prove_comprehensive()


if __name__ == "__main__":
    main()
