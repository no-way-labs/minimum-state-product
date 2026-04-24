"""
Detailed analysis of consecutive t-fire counterexamples at n=3 and proof for n>=4.

n=3 counterexamples exist (6 found). Need to understand why n=3 is special
and prove the theorem for n >= 4 (or n >= 9 as needed).
"""

import itertools
import random
from collections import Counter


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


def analyze_n3_counterexample():
    """
    Reproduce and analyze the n=3 counterexample.
    Trial 4715: CL=7, movers [1,0,2,1,1,0,2], consec at steps 3,4.
    """
    ms = [2, 3, 2]
    n = 3
    t = 1

    print("=== Analyzing n=3 counterexamples ===")
    print()

    random.seed(42)

    domains = []
    for i in range(n):
        m_L = ms[(i-1)%n]
        m_S = ms[i]
        m_R = ms[(i+1)%n]
        dom = list(itertools.product(range(m_L), range(m_S), range(m_R)))
        domains.append((dom, m_S))

    count = 0
    for trial in range(2000000):
        fs = []
        for dom, m_S in domains:
            f = {k: random.randint(0, m_S - 1) for k in dom}
            fs.append(f)

        if not check_validity_full(ms, fs):
            continue

        cyc_c, cyc_m = find_good_cycle_dict(ms, fs)
        if cyc_c is None:
            continue

        CL = len(cyc_m)
        fc_t = sum(1 for m in cyc_m if m == t)

        has_consec = any(cyc_m[k] == t and cyc_m[(k+1) % CL] == t for k in range(CL))

        if has_consec and fc_t < CL and fc_t >= 2:
            ec = has_ec(cyc_c, cyc_m, n)
            all_fire = all(sum(1 for m in cyc_m if m == p) > 0 for p in range(n))
            if not ec and all_fire:
                count += 1
                if count <= 3:
                    print(f"Counterexample {count} (trial {trial}):")
                    print(f"  CL={CL}, movers={cyc_m}")
                    fcs = [sum(1 for m in cyc_m if m == p) for p in range(n)]
                    print(f"  Fire counts: {fcs}")
                    print(f"  Configs:")
                    for k in range(CL):
                        marker = " *" if (cyc_m[k] == t and cyc_m[(k+1)%CL] == t) or \
                                         (cyc_m[(k-1)%CL] == t and cyc_m[k] == t) else ""
                        print(f"    Step {k}: {cyc_c[k]}  mover={cyc_m[k]}{marker}")

                    # Print transition tables
                    print(f"  Transition tables:")
                    for i in range(n):
                        print(f"    Proc {i} (m={ms[i]}):")
                        for (l, s, r), v in sorted(fs[i].items()):
                            arrow = " <-FIRE" if v != s else ""
                            print(f"      ({l},{s},{r}) -> {v}{arrow}")

                    # Analyze the consecutive steps
                    for k in range(CL):
                        if cyc_m[k] == t and cyc_m[(k+1) % CL] == t:
                            print(f"\n  Consecutive t-fires at steps {k} and {(k+1)%CL}:")
                            ck = cyc_c[k]
                            ck1 = cyc_c[(k+1)%CL]
                            ck2 = cyc_c[(k+2)%CL]
                            v = ck[t]
                            c_L = ck[(t-1)%n]
                            c_R = ck[(t+1)%n]
                            print(f"    bL={c_L}, t_val={v}, bR={c_R}")
                            print(f"    Step k:   {ck} -> mover={t}, t goes {v}->{ck1[t]}")
                            print(f"    Step k+1: {ck1} -> mover={t}, t goes {ck1[t]}->{ck2[t]}")
                            print(f"    Step k+2: {ck2} -> mover={cyc_m[(k+2)%CL]}")

                            # Check: at config k+2, who is privileged?
                            priv = privileged_set(ck2, fs, n)
                            print(f"    Privileged at step k+2: {priv}")

                    print()

        if count >= 3:
            break

    # Now check: what makes n=3 special?
    print("=" * 60)
    print("ANALYSIS: Why n=3 is special")
    print("=" * 60)
    print()
    print("At n=3 with ms=(2,3,2): ring has only 3 procs.")
    print("bL = proc 0, t = proc 1, bR = proc 2.")
    print("left(bL) = bR, right(bR) = bL. (The ring wraps tightly.)")
    print("So bL's left neighbor is bR, and bR's right neighbor is bL.")
    print("This means: bL's context is (c_R, c_L, v) -- bR is bL's left neighbor!")
    print("And bR's context is (v, c_R, c_L) -- bL is bR's right neighbor!")
    print()
    print("At n=3, the left-of-bL = right-of-bR = the OTHER binary.")
    print("The second-neighbors overlap with the first-neighbors.")
    print("This tight wrapping is special to n=3.")
    print()
    print("For n >= 4: left(bL) != bR and right(bR) != bL.")
    print("The second-neighbors are DISTINCT from the sandwich trio.")
    print("This gives more room for the EC argument.")
    print()


def verify_n4_n5_n6():
    """Verify no counterexamples at n=4,5,6 with heavy sampling."""
    random.seed(42)

    for ms in [[2,3,2,2], [2,3,2,3], [3,2,3,2],
               [2,3,2,2,2], [2,3,2,3,2], [2,2,3,2,2],
               [2,3,2,2,2,2], [2,3,2,3,2,2], [2,3,2,2,3,2],
               [2,2,3,2,2,2], [2,2,3,2,3,2]]:
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

        print(f"n={n}, ms={ms}, sandwiches={sandwiches}, prod={prod}")

        domains = []
        for i in range(n):
            m_L = ms[(i-1)%n]
            m_S = ms[i]
            m_R = ms[(i+1)%n]
            dom = list(itertools.product(range(m_L), range(m_S), range(m_R)))
            domains.append((dom, m_S))

        total_valid = 0
        total_consec = 0

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
                if fc_t >= CL or fc_t < 2:
                    continue

                has_consec = any(cyc_m[k] == t and cyc_m[(k+1) % CL] == t for k in range(CL))
                if not has_consec:
                    continue

                ec = has_ec(cyc_c, cyc_m, n)
                if ec:
                    continue

                all_fire = all(sum(1 for m in cyc_m if m == p) > 0 for p in range(n))
                if not all_fire:
                    continue

                total_consec += 1
                print(f"  COUNTEREXAMPLE: trial {trial}, t={t}, CL={CL}")

        print(f"  Valid: {total_valid}, Counterexamples: {total_consec}")
        print()


def prove_config_collision():
    """
    THE PROOF (for n >= 4):

    Assume t fires at consecutive steps k, k+1.
    Config C_k = (..., LL, c_L, v, c_R, RR, ...) with mover = t.
    Config C_{k+1} = (..., LL, c_L, v+1, c_R, RR, ...) with mover = t.
    Config C_{k+2} = (..., LL, c_L, v+2, c_R, RR, ...) with mover != t.

    Step 1: f_t(c_L, v+2, c_R) = v+2 (else 3-consec -> collision, proved above).

    Step 2: At C_{k+2}, exactly one of bL, bR is privileged.
    WLOG bL. f_{bL}(LL, c_L, v+2) != c_L. Since binary: = 1-c_L.

    Step 3: At C_{k+2}, bR is NOT privileged.
    f_{bR}(v+2, c_R, RR) = c_R.
    Combined with step k: f_{bR}(v, c_R, RR) = c_R.
    And step k+1: f_{bR}(v+1, c_R, RR) = c_R.
    So f_{bR}(*, c_R, RR) = c_R for ALL 3 L-values.
    bR NEVER fires with (S=c_R, R=RR).

    Step 4 (THE KEY FOR n >= 4):

    For n >= 4: right(bR) != bL. Let RR denote the proc right of bR (= proc t+2).
    RR is NOT in {bL, t, bR}. RR's value doesn't change during steps k, k+1, k+2
    (only t and then bL change). So RR's value is constant throughout.

    Now: bR NEVER fires with (S=c_R, R=RR_val). Since bR is binary:
    bR fires only when S = 1-c_R (with R = RR_val), or when R != RR_val.

    For the good cycle: bR fires fc(bR) >= 2 times (even, fairness).
    Each time bR fires: either S = 1-c_R, or R != RR_val (i.e., RR fires
    before that step, changing RR's value).

    Actually, wait. RR_val is the value at step k, but RR can fire at other
    steps in the cycle, changing its value. "bR NEVER fires with (S=c_R, R=RR_val)"
    means: whenever bR's value is c_R AND bR's right neighbor has value RR_val,
    bR does not fire. This is a constraint on the TRANSITION TABLE, not on the cycle.

    From Step 3: f_{bR}(L, c_R, RR_val) = c_R for ALL L. (We showed this for
    L = v, v+1, v+2, which are all 3 possible L-values since t is ternary.)

    This means: whenever bR has value c_R and right neighbor = RR_val, bR is nonprivileged.
    Regardless of what the left neighbor (t) is.

    So: bR fires only when bR-value != c_R, OR right-neighbor-value != RR_val.

    Now: in the good cycle, at the step just before bR fires for the first time after k+2:
    bR has value c_R (unchanged since step k). For bR to fire:
    either bR's value is NOT c_R (contradiction: it IS c_R), or RR's value is NOT RR_val.
    So RR must have changed before the first bR fire after step k+2.

    This means: some proc changes RR's value (i.e., RR fires at some step between k+2 and
    the first bR fire). But RR is NOT bL, t, or bR. RR is a "far" proc.

    This argument works for n >= 4 because RR is distinct from bL.
    For n = 3: RR = bL, and bL fires at step k+2 (changing its own value, not RR's).
    Wait, at n=3: right(bR) = right(proc 2) = proc 0 = bL. So RR = bL.
    And bL fires at step k+2 (from c_L to 1-c_L). So RR changes!
    At step k+3: bR's right-neighbor (= bL) has value 1-c_L != LL.
    Wait, LL is the left neighbor of bL (= proc t-2 = proc n-1 = proc 2 = bR for n=3).
    Hmm, n=3 is circular: bL = proc 0, t = proc 1, bR = proc 2.
    left(bL) = proc 2 = bR. right(bR) = proc 0 = bL.

    So at n=3: LL = bR's value, RR = bL's value.
    The constraint "f_{bR}(*, c_R, RR_val) = c_R" becomes
    "f_{bR}(*, c_R, c_L) = c_R" (since RR_val = bL's value = c_L).

    But at step k+2, bL fires, changing to 1-c_L. So at step k+3:
    bR's right-neighbor is 1-c_L != c_L = RR_val. The constraint doesn't apply!
    bR CAN fire at step k+3 or later (when right-neighbor = 1-c_L).

    For n >= 4: RR = proc t+2 is NOT bL. RR doesn't fire at step k+2 (bL does).
    So RR's value stays RR_val through step k+3. bR still has (S=c_R, R=RR_val)
    and can't fire. bR needs RR to change first.

    THIS is why n=3 is different! At n=3, bL's fire at step k+2 immediately
    changes bR's right-neighbor context, enabling bR to fire. At n >= 4,
    bL's fire doesn't affect bR's right-neighbor, so bR stays locked.

    Step 5 (n >= 4): bR is "frozen" until RR fires.

    Between steps k+2 and the first RR-fire: bR has value c_R and can't fire.
    bL fires at k+2 (from c_L to 1-c_L). But bR is frozen.

    Who fires between k+2 and the first RR-fire?
    Not t (unless t fires again, which is fine).
    Not bR (frozen).
    bL might fire again.
    Other procs fire.

    The cycle must return to C_k eventually. For that:
    - bL must return to c_L (fires even times).
    - bR must still be c_R (it hasn't fired since before step k; but it must fire
      fc(bR) >= 2 times total, which is ≥ 2 times SOMEWHERE in the cycle).

    Wait: bR has value c_R at step k. It stays c_R through step k+2 and beyond
    (frozen). When does bR fire? It fires fc(bR) >= 2 times in the cycle.
    These fires must occur at steps where bR's right-neighbor != RR_val, or bR's
    value != c_R.

    Since bR starts at c_R and stays at c_R until it first fires: the first bR fire
    must have right-neighbor != RR_val (since bR = c_R at that point).

    After bR fires (from c_R to 1-c_R): bR = 1-c_R. Now bR can fire from 1-c_R
    regardless of right-neighbor (the constraint only blocks (S=c_R, R=RR_val)).

    Eventually bR returns to c_R (even fires). If bR returns to c_R at a step
    where right-neighbor = RR_val: bR is again frozen.

    THIS IS PROMISING but I need to connect it to EC or contradiction.

    Step 6: THE ENTRY CONFLICT AT bR.

    At step k: bR's context is (v, c_R, RR_val). bR is nonmover.
    f_{bR}(v, c_R, RR_val) = c_R.

    At step k+1: bR's context is (v+1, c_R, RR_val). bR is nonmover.
    f_{bR}(v+1, c_R, RR_val) = c_R.

    At step k+2: bR's context is (v+2, c_R, RR_val). bR is nonmover.
    f_{bR}(v+2, c_R, RR_val) = c_R.

    So for ALL (L, c_R, RR_val) with L in {0,1,2}: f_{bR} = c_R. Nonmover.
    These contexts NEVER appear as mover for bR.

    For EC at bR: need a context that appears as BOTH mover and nonmover.
    The 3 contexts above are always nonmover. No EC from them directly.

    But: when bR fires at some step j (with bR = c_R, right-neighbor != RR_val):
    context (L_j, c_R, R_j) with R_j != RR_val. Mover.
    Is (L_j, c_R, R_j) ever nonmover? Yes, if at some step j' bR has value c_R,
    context (L_j, c_R, R_j), and bR doesn't fire. Then EC.

    Can we FORCE this? That depends on the cycle structure.

    Wait, actually there's a simpler approach. Let me count more carefully.

    Step 7: THE PARITY + WRAP ARGUMENT.

    The consecutive t-fires at k, k+1 create an "empty phase" (no binary fires).
    The sparse_phase_sum_ge machinery needs: every phase contributes >= 1.
    With one empty phase: total binary fires in non-wrap phases is >= fc(t) - 2
    (fc(t)-1 interior phases, 1 empty, fc(t)-2 non-empty with >= 1 each).
    Plus wrap phase contribution >= 1 (if non-empty).

    Total: fc(bL) + fc(bR) >= fc(t) - 2 + wrap_contribution.

    If wrap is non-empty: >= fc(t) - 1.
    Binary parity: fc(bL)+fc(bR) even.
    If fc(t) - 1 odd (fc(t) even): minimum even value >= fc(t) - 1 is fc(t). But
    we also have fc(bL)+fc(bR) <= fc(t) (from J+K <= 1). Contradiction if fc(t) even!

    If fc(t) - 1 even (fc(t) odd): fc(bL)+fc(bR) >= fc(t)-1 (even), consistent.

    Hmm wait, I need to verify: is the wrap phase non-empty?

    The wrap phase: from the last t-fire to the first t-fire (wrapping around).
    If the consecutive fires are at k, k+1, and the t-fires are at positions
    p_0, p_1, ..., p_{fc(t)-1}, then the wrap goes from p_{fc(t)-1} + 1 to p_0 - 1
    (mod CL), with CL - (p_{fc(t)-1} - p_0) - 1 steps? This is CL minus the
    span of the fc(t) t-fires.

    Since fc(t) < CL: there's at least one non-t step. The wrap phase has at least
    one step. Since fc(t) >= 2 and CL >= fc(t) + 1: CL >= 3. The wrap phase is
    non-empty (has at least 1 step, which is a non-t step).

    But does the wrap phase have J+K >= 1? Under normalForm, if it's a valid
    TernaryPhase, yes. The wrap phase is the gap from the last t-fire to the first
    t-fire. This IS a TernaryPhase (a = first step after last t-fire, s = first t-fire,
    a < s in the cyclic sense).

    OK but the wrap construction in the Lean code handles this carefully with the
    cyclic case. Let me just use the parity argument and check if it suffices.

    THE PARITY ARGUMENT (CLEAN VERSION):

    fc(t) phases total (between consecutive t-fires, cyclically).
    1 phase is empty (the consecutive pair).
    fc(t) - 1 phases are non-empty.

    Each non-empty phase has J+K >= 1 (from normalForm: bothEven(0,0) is excluded).
    Each phase has J+K <= 1 (from h_phase_le1, which is proved in AllNormalFormFalse2).

    Wait: h_phase_le1 requires n >= 9. Let me check.
    """

    print("CHECKING: does the J+K <= 1 upper bound hold at small n?")
    print()

    # The J+K <= 1 bound comes from within_phase_ec arguments in AllNormalFormFalse2.
    # It uses second-neighbor (left^2 t, right^2 t) arguments that need n >= 4 or so.
    # For n >= 9: definitely holds. For n = 3,4: may not.

    # Actually, reading the code more carefully, h_phase_le1 is proved inline
    # in AllNormalFormFalse2.lean around lines 1070-1200 using within_phase_ec_left/right
    # and adjacent-chain arguments. These use left(left(t)) and right(right(t)) which
    # are well-defined for any n >= 4 (need left^2 t != t, right^2 t != t).

    # For the theorem we only need n >= 9, so this is fine.

    print("For n >= 9: h_phase_le1 (J+K <= 1 per phase) is proved.")
    print("Under consecutive t-fires: 1 empty phase + (fc(t)-1) non-empty phases.")
    print("Total: fc(bL) + fc(bR) = sum(J_i + K_i) over all phases.")
    print("  = 0 (empty) + sum over non-empty phases.")
    print("  >= fc(t) - 1 (each non-empty contributes >= 1).")
    print("  <= fc(t) - 1 (each phase contributes <= 1, empty contributes 0).")
    print("  = fc(t) - 1 exactly.")
    print()
    print("Binary parity: fc(bL) even, fc(bR) even => fc(bL)+fc(bR) even.")
    print("fc(t) - 1 even iff fc(t) odd.")
    print()
    print("CASE 1: fc(t) even.")
    print("  fc(bL)+fc(bR) = fc(t)-1 (odd). But binary parity says even. CONTRADICTION.")
    print("  Done. No consecutive t-fires when fc(t) even.")
    print()
    print("CASE 2: fc(t) odd.")
    print("  fc(bL)+fc(bR) = fc(t)-1 (even). Consistent.")
    print("  Need a different argument.")
    print()

    # CASE 2: fc(t) odd.
    # Each non-empty phase has J+K = 1 exactly (both bounds tight).
    # Let a = #{phases with J=1, K=0}, b = #{phases with J=0, K=1}.
    # a + b = fc(t) - 1. fc(bL) = a, fc(bR) = b. Both even.
    # a even, b even, a+b = fc(t)-1 (even since fc(t) odd).

    # The phase ADJACENT to the empty phase:
    # Phase i (empty, steps k to k+1).
    # Phase i+1 (steps k+1 to p_{i+2}).
    # Phase i-1 (steps p_{i-1} to k).

    # Phase i+1: J+K = 1. Either bL fires once (J=1) or bR fires once (K=1).
    # From Step 2: at C_{k+2}, either bL or bR fires.
    # If bL fires at step k+2: bL fires in the FIRST step of phase i+1.
    #   Phase i+1 has J=1 (bL fires), K=0.
    # If bR fires at step k+2: similarly K=1, J=0.

    # So: the phase immediately after the empty phase determines which binary fires.

    # WLOG bL fires at k+2 (so phase i+1 has J=1, K=0).

    # Now: for bR to fire fc(bR) = b >= 2 times, all in phases where K=1.
    # These b phases are spread among the fc(t)-1 non-empty phases.
    # The phase i+1 has K=0, so bR doesn't fire there.

    # Consider the phase i-1 (before the empty phase).
    # bR doesn't fire at steps k, k+1 (only t fires).
    # At step k: bR has value c_R. At step p_{i-1}: t fires.
    # In phase i-1: J+K = 1. Either J=1 or K=1.

    # If K=1 (bR fires once in phase i-1): bR fires between p_{i-1} and k.
    #   bR goes from some value to some other value.
    #   At step k: bR = c_R. So after the fire: bR = 1-c_R.
    #   Wait, bR fires ONCE in phase i-1 (between p_{i-1}+1 and k-1).
    #   After that fire, bR changes. But bR = c_R at step k.
    #   So the fire RESTORED bR to c_R: before fire = 1-c_R, after fire = c_R.

    # If J=1 (bL fires once in phase i-1): bR doesn't fire. bR = c_R throughout.

    # So in all cases: bR = c_R at step k (as given).

    # THE ARGUMENT FOR fc(t) ODD:

    # Actually, I just realized: the parity argument for even fc(t) is ALREADY
    # sufficient for most cases. Let me check: is fc(t) always even?

    # t is ternary (m_t = 3). In the good cycle, t fires fc(t) times.
    # Each fire changes t's value. The net change mod 3 is 0 (returns to start).
    # If t always increments by 1: fc(t) = 0 mod 3.
    # If some fires decrement (increment by 2): net = fc(t) * 1 + (adjustments).
    # In general: fc(t) is NOT necessarily even or a multiple of 3.

    # fc(t) can be any value >= 2. So we CAN'T assume fc(t) even.

    # Need a proof for odd fc(t) too. Let me think...

    # APPROACH FOR ODD fc(t):

    # We have fc(bL) + fc(bR) = fc(t) - 1 (even).
    # Each non-empty phase has EXACTLY J+K = 1.
    # fc(bL) = a (even), fc(bR) = b (even), a+b = fc(t)-1.

    # Since a >= 2 and b >= 2 (fairness: each proc fires at least once, and binary
    # fires even times): a+b >= 4. So fc(t) >= 5.

    # But actually, fc(bL) >= 2 and fc(bR) >= 2 means a >= 2 and b >= 2 means a+b >= 4.
    # And fc(t) = a+b+1 >= 5. With the empty phase: CL = sum fc(p) >= fc(t) + a + b + (n-3)*2
    # (at least 2 fires per other proc). For n=9: CL >= 5 + 4 + 6*2 = 21. And fc(t) = 5 (minimum odd).

    # The key constraint: fc(bL)+fc(bR) = fc(t)-1 combined with the UPPER bound
    # fc(bL)+fc(bR) <= fc(t) from h_phase_le1.

    # Wait, I already showed fc(bL)+fc(bR) = fc(t)-1 (tight). That's one less than fc(t).
    # But sparse_phase_sum_ge claims fc(bL)+fc(bR) >= fc(t) (WITHOUT the empty phase).
    # If we COULD prove sparse_phase_sum_ge independently of hno_consec: done.
    # But sparse_phase_sum_ge NEEDS hno_consec. That's the circularity.

    # Let me look at this differently. The WRAP-AROUND phase.

    # Interior phases: fc(t)-1 pairs (between consecutive t-fires in linear order).
    # Wrap-around phase: last t-fire to first t-fire.
    # Total: fc(t) cyclic phases.

    # 1 empty phase (interior).
    # fc(t)-2 non-empty interior phases with J+K >= 1, J+K <= 1. So J+K = 1.
    # 1 wrap-around phase with J+K >= 1 (if non-empty; it IS non-empty since fc(t) < CL).

    # Sum = 0 + (fc(t)-2)*1 + wrap_J_K = fc(t)-2 + wrap_J_K.
    # = fc(bL) + fc(bR).

    # Also: wrap_J_K <= 1? Does h_phase_le1 apply to the wrap?
    # In the Lean code, h_phase_le1 only applies to interior phases (a.val < s.val).
    # The wrap is separate.

    # If wrap_J_K <= 1: total = fc(t)-2 + wrap_J_K <= fc(t)-2+1 = fc(t)-1.
    # If wrap_J_K >= 1: total = fc(t)-2 + wrap_J_K >= fc(t)-2+1 = fc(t)-1.
    # So total = fc(t)-1 exactly.

    # But what if wrap_J_K > 1? Then total > fc(t)-1. Is that possible?
    # The wrap-around phase is a TernaryPhase if properly constructed.
    # Under the all-normalForm hypothesis: it's normalForm, so J+K >= 1.
    # But does J+K <= 1 hold for the wrap? The argument that proves J+K <= 1
    # (within_phase_ec and friends) should apply to any TernaryPhase, including wrap.

    # If YES (wrap J+K <= 1): total = fc(t)-1. Binary parity check:
    # fc(t) odd: fc(t)-1 even. Consistent. No contradiction.
    # fc(t) even: fc(t)-1 odd. Contradiction with binary parity. Done.

    # If the wrap has J+K >= 2 (violating h_phase_le1 for the wrap):
    # that would contradict the all-normalForm + n >= 9 hypothesis.

    # Hmm. Actually, h_phase_le1 IS proved for ALL TernaryPhases (it uses only the
    # phase structure and normalForm, not the linear ordering). So the wrap also
    # has J+K <= 1. So total = fc(t) - 1 always.

    # This means: for even fc(t), we get a contradiction. For odd fc(t), no contradiction
    # from counting alone. We need a SEPARATE argument for odd fc(t).

    # WAIT: I may have the counting wrong.

    # Let me recount. The cyclic phases: there are exactly fc(t) cyclic phases.
    # One of them is empty (consecutive t-fires at k, k+1).
    # The other fc(t)-1 are non-empty, each with J+K = 1.
    # Total J+K = fc(t)-1.

    # But we HAVEN'T included the wrap separately. The fc(t) cyclic phases
    # INCLUDE the wrap. So:
    # fc(t) cyclic phases, 1 empty, fc(t)-1 non-empty with J+K=1 each.
    # Total = fc(t)-1.

    # For n >= 9, fc(bL) >= 2 and fc(bR) >= 2 (binary + fairness).
    # So a >= 2 and b >= 2 and a+b = fc(t)-1.
    # fc(t) >= a+b+1 >= 5.

    # Now: can we derive a contradiction for odd fc(t)?

    # Let me check: in the n=3 counterexamples, what's fc(t)?
    # Trial 4715: CL=7, movers [1,0,2,1,1,0,2]. fc(t=1) = 3 (odd!).
    # fc(0) = 2, fc(2) = 2. fc(0)+fc(2) = 4. But fc(t)-1 = 2. Hmm, 4 != 2.
    # Something's wrong with my counting.

    # Oh wait: at n=3, the J+K <= 1 bound may NOT hold (requires n >= 4 or more).
    # So the n=3 counterexample doesn't satisfy the premise.

    # At n >= 9 with h_phase_le1: total = fc(t)-1.
    # fc(t) odd: no contradiction from parity alone.

    # Need: an argument that works for odd fc(t) at n >= 9.

    # IDEA: The empty phase creates a PARITY MISMATCH in the phase sequence.

    # Each phase has J+K = 1 (one-sided). Let's label phases as "L" (J=1,K=0) or "R" (J=0,K=1).
    # There are a "L" phases and b "R" phases, a+b = fc(t)-1, a=fc(bL), b=fc(bR), both even.
    # The sequence of phases around the cycle is: ..., L/R, EMPTY, L/R, L/R, ...

    # The phase sequence (excluding the empty one) has fc(t)-1 phases.
    # In this sequence, the phases ALTERNATE? Not necessarily.

    # Actually, the phase type (L or R) is determined by who fires in that gap.
    # bL and bR fire in a specific pattern.

    # THE DOMINOES ARGUMENT:
    # Consider the context at t's boundary. At the END of each phase
    # (just before the next t-fire): the boundary triple is (bL_val, t_val, bR_val).
    # The t-fire changes t_val. The next phase starts with new t_val.
    # Between t-fires: either bL or bR fires once. This changes bL_val or bR_val.

    # At the END of the empty phase (just before step k+2's mover fires... wait,
    # the empty phase ends at step k+1 which is a t-fire, leading to step k+2).

    # OK the details depend on the exact timing. Let me think about it differently.

    # THE TRANSITION FUNCTION CONSTRAINT:
    #
    # From Step 3: f_{bR}(L, c_R, RR_val) = c_R for ALL L in {0,1,2}.
    # This is a UNIVERSAL nonmover constraint on bR at (S=c_R, R=RR_val).
    #
    # Now: bR fires fc(bR) = b >= 2 times in the cycle.
    # At these fires: either bR-val != c_R, or bR's right-neighbor != RR_val.
    #
    # Since the right-neighbor of bR is proc t+2 (for n >= 4), and proc t+2 has
    # some state count m_{t+2} >= 2, RR_val is one of m_{t+2} values.
    #
    # From the CYCLE STRUCTURE:
    # bR's value oscillates between c_R and 1-c_R (binary).
    # bR fires even times: alternating between c_R -> 1-c_R and 1-c_R -> c_R.
    #
    # Fires from c_R: need right-neighbor != RR_val (since f_{bR}(*, c_R, RR_val) = c_R).
    # Fires from 1-c_R: no constraint (the universal nonmover is only for S=c_R, R=RR_val).
    #
    # Since b/2 fires go from c_R to 1-c_R, each needing right-neighbor != RR_val.
    # And b/2 fires go from 1-c_R to c_R, no constraint.
    #
    # So: the right-neighbor of bR must be != RR_val at b/2 specific moments.
    # This means proc t+2 must have changed from RR_val to something else at least once
    # before the first c_R-to-1-c_R fire of bR.
    #
    # This is a nontrivial constraint on the cycle structure but doesn't directly give EC.

    # Actually, I think the proof for odd fc(t) might work through a different route:
    # showing that fc(t) is NECESSARILY even in the sub-threshold regime.
    #
    # Or: showing that the empty phase is impossible regardless of parity, using
    # the TRANSITION FUNCTION CONSTRAINTS at t, bL, bR jointly.

    # Let me try yet another approach. The DIRECT EC at t.

    # From the consecutive fires:
    # f_t(c_L, v, c_R) = v+1 (step k, mover)
    # f_t(c_L, v+1, c_R) = v+2 (step k+1, mover)
    # f_t(c_L, v+2, c_R) = v+2 (step k+2, nonmover)

    # The cycle visits config C_{k+2} = (B, t=v+2) where B is the background.
    # The cycle also visits other configs with t=v+2 but different backgrounds.

    # At ANY step where t=v+2: t's context is (bL_val, v+2, bR_val).
    # If (bL_val, bR_val) = (c_L, c_R): t is nonmover (always).
    # If (bL_val, bR_val) != (c_L, c_R): might be mover or nonmover.

    # For the cycle to return to C_k (with t=v): t must fire from v+2 at some point.
    # At that step: (bL_val, bR_val) != (c_L, c_R) and f_t(bL_val, v+2, bR_val) != v+2.

    # Between C_{k+2} (t=v+2, bL=c_L, bR=c_R) and the next t-fire (from v+2):
    # bL and/or bR change values. At the TRANSITION point where (bL, bR) changes
    # from (c_L, c_R) to something else: either bL or bR fires.

    # At the step just BEFORE this change: t=v+2, (bL, bR)=(c_L, c_R).
    # t sees (c_L, v+2, c_R): nonmover (Step 1).
    # At the step AFTER: t=v+2, (bL, bR) = (1-c_L, c_R) or (c_L, 1-c_R).
    # t sees (1-c_L, v+2, c_R) or (c_L, v+2, 1-c_R).

    # If t is nonmover at this new context: f_t(new_context) = v+2.
    # If t is mover: f_t(new_context) != v+2. EC? Only if the same context appears as nonmover.

    # SCENARIO: bL fires at step k+2 (as established). After: bL = 1-c_L.
    # t's context at step k+3: (1-c_L, v+2, c_R).
    # If f_t(1-c_L, v+2, c_R) = v+2: nonmover. t stays at v+2.
    # If f_t(1-c_L, v+2, c_R) != v+2: mover. t fires.

    # In the latter case: t fires at step k+3. This is fine (not consecutive with k+1:
    # step k+2 had mover = bL, not t). But this means t fires from v+2 to some w.

    # Then: (1-c_L, v+2, c_R) is a MOVER context for t.
    # And (c_L, v+2, c_R) is a NONMOVER context for t.
    # Different contexts (differ at L). No EC from these.

    # But: does (1-c_L, v+2, c_R) appear as NONMOVER anywhere?
    # In the cycle, at step k+3 it's mover. At any other step where t sees (1-c_L, v+2, c_R):
    # if nonmover: EC. If always mover: no EC.

    # Under no-EC: (1-c_L, v+2, c_R) is always mover for t.
    # And (c_L, v+2, c_R) is always nonmover for t.

    # So: f_t(1-c_L, v+2, c_R) != v+2 (always mover).
    # And: f_t(c_L, v+2, c_R) = v+2 (always nonmover).

    # OK so t's transition table at S=v+2:
    # f_t(c_L, v+2, c_R) = v+2
    # f_t(1-c_L, v+2, c_R) != v+2

    # What about (c_L, v+2, 1-c_R) and (1-c_L, v+2, 1-c_R)?
    # These depend on whether bR changes during the cycle.

    # For a CLEAN proof: we need to show that the constraints on f_t force a contradiction.

    # INSIGHT: Let's count nonmover contexts for t at value v+2.
    # There are 2*2 = 4 possible (L, R) pairs for t when S=v+2.
    # (c_L, c_R): nonmover (proved).
    # The other 3: might be mover or nonmover.

    # Under no-EC: each pair is EXCLUSIVELY mover or nonmover.
    # Let M = #{mover pairs at S=v+2}, NM = #{nonmover pairs at S=v+2}.
    # M + NM = 4 (total pairs). We know NM >= 1 (the (c_L, c_R) pair).

    # For the cycle to fire t from v+2: need M >= 1 (at least one mover pair).
    # So: 1 <= NM <= 3, 1 <= M <= 3.

    # Does this constrain anything? Not obviously.

    # I think the clean proof for n >= 9 works through the parity argument alone,
    # because fc(t) is forced to be even by the sub-threshold condition + n >= 9.
    # Let me check this computationally.

    print()
    print("CHECKING: is fc(t) always even for n >= 9?")
    print("(If so: parity argument suffices.)")
    print()


def check_fc_parity():
    """
    Check if fc(t) for sandwiched ternary is always even in sub-threshold systems.

    Actually, in Dijkstra-style systems, the fire count of a ternary proc t depends
    on the cycle structure. Let me check known systems.
    """
    import sys
    sys.path.insert(0, 'claude')

    # Check the CLB (CUP-2) construction at n=9
    # From MEMORY: CUP-2 has ms = (2,3,...,3,2), cycle length 3n-2.
    # For n=9: CL = 25. Each proc fires fc(p) times.
    # For ternary procs (p=1..7): fc(p) = 3 (since CL=25, n=9, 25/9 ~ 2.8).
    # Actually from memory: each ternary fires 3 times (m_p = 3).

    # In the CUP-2 system: ms = (2,3,3,3,3,3,3,3,2) for n=9.
    # This has NO sandwiched ternary (the ternary procs have binary neighbors
    # only at positions 1 and 7, not sandwiched). Wait: proc 1 is ternary,
    # left(1) = 0 (binary), right(1) = 2 (ternary). Not sandwiched.

    # Sandwiched ternary: both neighbors binary. This requires the ternary proc
    # to be surrounded by binaries. In a sub-threshold system with >= 3 binaries,
    # this is common.

    # For ms = (2,3,2,...): proc 1 is sandwiched ternary.

    # Let me check fire count parity for known systems.
    # From the M_5=96 witness: ms = (2,2,2,3,4).
    # Sandwiched ternary: proc 3 (m=3) with neighbors proc 2 (m=2) and proc 4 (m=4).
    # Proc 4 is quaternary, not binary. So proc 3 is NOT sandwiched between two binaries.

    # Hmm, sandwiched ternary with BOTH neighbors binary is a specific configuration.
    # In the sub-threshold regime for n >= 9: product < 4*3^7 = 8748.
    # With >= 3 binary: the multiset has >= 3 twos.
    # A sandwiched ternary: some proc with m=3 flanked by two m=2 procs.

    # Example: ms = (2,3,2,3,3,3,3,3,3) at n=9. Product = 2*3*2*3^6 = 4*3^7 = 8748.
    # Not sub-threshold (need strict <). Need product < 8748.

    # ms = (2,3,2,2,3,3,3,3,3) at n=9. Product = 2*3*2*2*3^5 = 24*243 = 5832 < 8748.
    # Sandwiched ternary at proc 1 (m=3, left=2, right=2).

    print("Known fire counts for CUP-2 (ms=(2,3,...,3,2)):")
    print("  CL = 3n-2, each proc fires: binary 2 times, ternary 3 times.")
    print("  fc(ternary) = 3 (odd). But ternary is NOT sandwiched in CUP-2.")
    print()
    print("For sandwiched ternary in sub-threshold: need computational check.")
    print()


def main():
    analyze_n3_counterexample()
    print()
    prove_config_collision()
    check_fc_parity()
    print()
    verify_n4_n5_n6()


if __name__ == "__main__":
    main()
