"""
Round 4: Detailed follow-up on key findings.

Key questions:
1. Why do Cases 1/2 show 0/0? (pos2 always in interior for n=7 all-fc=2)
2. What are the 8 Case 3 mover words without EC pattern?
3. Does the non-adjacent EC pattern cover 100% at n=9?
4. What happens when ternary procs have fc=3 instead of fc=2?
"""

import itertools
from collections import defaultdict
import random

def analyze_mover_word(mw, n, pivot, left2t, right2t):
    """Analyze a mover word for phase structure and EC patterns."""
    L = len(mw)
    pivot_steps = [i for i, m in enumerate(mw) if m == pivot]
    if len(pivot_steps) != 2:
        return None

    p1, p2 = pivot_steps
    phase1_len = (p2 - p1 - 1) % L
    phase2_len = (p1 - p2 - 1) % L
    phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
    phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

    phase1_movers = set(mw[s] for s in phase1_steps)
    phase2_movers = set(mw[s] for s in phase2_steps)

    pos2_in_p1 = left2t in phase1_movers
    pos2_in_p2 = left2t in phase2_movers
    pos6_in_p1 = right2t in phase1_movers
    pos6_in_p2 = right2t in phase2_movers

    p1_contam = (left2t in phase1_movers) or (right2t in phase1_movers)
    p2_contam = (left2t in phase2_movers) or (right2t in phase2_movers)
    is_case3 = p1_contam and p2_contam
    is_case1 = not (pos2_in_p1 or pos2_in_p2)
    is_case2 = not (pos6_in_p1 or pos6_in_p2)

    return {
        'is_case1': is_case1, 'is_case2': is_case2, 'is_case3': is_case3,
        'phase1_steps': phase1_steps, 'phase2_steps': phase2_steps,
        'phase1_movers': phase1_movers, 'phase2_movers': phase2_movers,
    }

def check_ec_pattern(mw, n, phase_steps_list):
    """Check for non-adjacent EC pattern in any phase."""
    L = len(mw)
    for phase_steps in phase_steps_list:
        phase_mw = [(s, mw[s]) for s in phase_steps]
        for pos in range(n):
            neighbors = {(pos-1)%n, pos, (pos+1)%n}
            mover_indices = [idx for idx, (s, m) in enumerate(phase_mw) if m == pos]
            nonmover_indices = [idx for idx, (s, m) in enumerate(phase_mw) if m != pos]

            for mi in mover_indices:
                for ni in nonmover_indices:
                    lo, hi = min(mi, ni), max(mi, ni)
                    between = phase_mw[lo+1:hi]
                    between_movers = set(m for _, m in between)
                    if not (between_movers & neighbors):
                        nm_mover = phase_mw[ni][1]
                        if nm_mover not in neighbors:
                            return True, pos
    return False, -1

def run():
    print("="*70)
    print("=== Q1: Why Cases 1/2 don't occur at n=7 all-fc=2 ===")
    print("="*70)
    print()

    # With n=7, all fc=2, length=14:
    # Each proc fires exactly twice. The 2 pivot firings create 2 phases.
    # The remaining 12 firings are distributed across the 2 phases.
    # For Case 1: left2t (pos 2) must not fire in EITHER phase interior.
    # But pos 2 fires twice total, and the only non-interior positions are
    # the pivot steps themselves (and pos 2 != pivot).
    # So both firings of pos 2 must be... wait, the phases cover ALL non-pivot steps.
    # Phase 1 + Phase 2 = all steps except pivot steps.
    # So pos 2 MUST fire in some phase interior (it fires and it's not the pivot).
    # Therefore Case 1 (pos 2 not in interior) is IMPOSSIBLE when all procs fire!

    print("RESOLUTION: Cases 1/2 are impossible when all procs fire.")
    print("The phases cover ALL non-pivot steps. Since pos 2 fires at least once")
    print("and pos 2 != pivot, pos 2 must fire in some phase interior.")
    print("'Case 1 (tight left)' requires pos 2 to NEVER fire in phase interior,")
    print("which is impossible if pos 2 fires at all.")
    print()
    print("In the original hglobal formulation, 'tight' likely means pos 2 fires")
    print("at the BOUNDARY of a phase (first or last step), not in the deep interior.")
    print("Let me re-check with this interpretation.")
    print()

    # Re-interpretation: "tight" means pos 2 fires ADJACENT to pivot
    # (immediately after a pivot firing = first step of phase,
    #  or immediately before a pivot firing = last step of phase)
    # vs "interior" means pos 2 fires with other steps between it and the pivot.

    random.seed(42)
    n = 7
    pivot = 4
    left2t = 2
    right2t = 6
    ms = [3, 3, 2, 2, 3, 2, 2]

    n_samples = 200000
    stats = defaultdict(int)

    for _ in range(n_samples):
        mw = []
        for i in range(n):
            mw.extend([i, i])
        random.shuffle(mw)

        L = len(mw)
        pivot_steps = [i for i, m in enumerate(mw) if m == pivot]
        p1, p2 = pivot_steps

        # Find pos2 firing steps
        pos2_steps = [i for i, m in enumerate(mw) if m == left2t]
        pos6_steps = [i for i, m in enumerate(mw) if m == right2t]

        # Check if pos2 is "tight" = adjacent to some pivot step
        def is_adjacent_to_pivot(step):
            for ps in [p1, p2]:
                if (step - ps) % L == 1 or (ps - step) % L == 1:
                    return True
            return False

        pos2_all_tight = all(is_adjacent_to_pivot(s) for s in pos2_steps)
        pos6_all_tight = all(is_adjacent_to_pivot(s) for s in pos6_steps)
        pos2_any_tight = any(is_adjacent_to_pivot(s) for s in pos2_steps)
        pos6_any_tight = any(is_adjacent_to_pivot(s) for s in pos6_steps)

        stats['total'] += 1
        if pos2_all_tight:
            stats['pos2_all_tight'] += 1
        if pos6_all_tight:
            stats['pos6_all_tight'] += 1
        if pos2_all_tight and pos6_all_tight:
            stats['both_all_tight'] += 1
        if not pos2_any_tight and not pos6_any_tight:
            stats['neither_any_tight'] += 1

        # Revised Case classification:
        # Case 1 (tight left): ALL pos2 firings adjacent to pivot, J odd
        # Case 2 (tight right): ALL pos6 firings adjacent to pivot
        # Case 3 (all contaminated): NOT Case 1 AND NOT Case 2
        #   (at least one pos2 firing deep in interior AND at least one pos6 firing deep)

        if pos2_all_tight:
            stats['Case1_revised'] += 1
        if pos6_all_tight:
            stats['Case2_revised'] += 1
        if not pos2_all_tight and not pos6_all_tight:
            stats['Case3_revised'] += 1

    print(f"n={n}, all-fc=2 mover words, {n_samples} samples:")
    for k, v in sorted(stats.items()):
        if k == 'total':
            continue
        pct = 100*v/n_samples
        print(f"  {k}: {v} ({pct:.1f}%)")

    # Now check EC patterns for the revised Case 3
    print()
    print("="*70)
    print("=== EC patterns for revised Case 3 (n=7, all-fc=2) ===")
    print("="*70)
    print()

    random.seed(42)
    case3_total = 0
    case3_with_ec = 0
    case3_without_ec = []

    for _ in range(200000):
        mw = []
        for i in range(n):
            mw.extend([i, i])
        random.shuffle(mw)

        L = len(mw)
        pivot_steps = [i for i, m in enumerate(mw) if m == pivot]
        p1, p2 = pivot_steps

        pos2_steps = [i for i, m in enumerate(mw) if m == left2t]
        pos6_steps = [i for i, m in enumerate(mw) if m == right2t]

        def is_adj(step):
            for ps in [p1, p2]:
                if (step - ps) % L == 1 or (ps - step) % L == 1:
                    return True
            return False

        pos2_all_tight = all(is_adj(s) for s in pos2_steps)
        pos6_all_tight = all(is_adj(s) for s in pos6_steps)

        if pos2_all_tight or pos6_all_tight:
            continue

        case3_total += 1

        # Check EC pattern
        phase1_len = (p2 - p1 - 1) % L
        phase2_len = (p1 - p2 - 1) % L
        phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
        phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

        has_ec, ec_pos = check_ec_pattern(mw, n, [phase1_steps, phase2_steps])

        # Also check cross-phase and at pivot boundary
        # Cross-phase EC: triple at pos identical when pos fires in phase1 vs
        # some non-mover step in phase2 (or vice versa).
        # For this we need to track which positions change between phases.
        # In the mover word, the procs that fire between two steps determine
        # which positions change. This is config-dependent.
        # However, for the PATTERN check: if pos fires at step s1 in phase1,
        # and at step s2 the mover is not in {pos-1, pos, pos+1} (in phase2),
        # AND all procs in {pos-1, pos, pos+1} that fire between s1 and s2
        # fire an EVEN number of times (for binary) or return to same value...
        # This is getting complex. Let's check with actual configs later.

        if has_ec:
            case3_with_ec += 1
        else:
            if len(case3_without_ec) < 20:
                case3_without_ec.append(mw[:])

    print(f"Revised Case 3 mover words: {case3_total}")
    print(f"  With same-phase EC pattern: {case3_with_ec} "
          f"({100*case3_with_ec/max(1,case3_total):.1f}%)")
    print(f"  Without same-phase EC pattern: {case3_total - case3_with_ec}")

    if case3_without_ec:
        print(f"\n  Examples without same-phase EC pattern:")
        for i, mw in enumerate(case3_without_ec[:5]):
            mw_str = "".join(str(m) for m in mw)
            pivot_steps = [j for j, m in enumerate(mw) if m == pivot]
            print(f"    {mw_str}  pivot at {pivot_steps}")

    # Now test at n=9 with the ACTUAL geometry from the question
    print()
    print("="*70)
    print("=== n=9 geometry: ms=(3,3,2,2,3,2,2,3,3), pivot=4 ===")
    print("="*70)
    print()

    n9 = 9
    pivot9 = 4
    left2t9 = 2
    right2t9 = 6

    random.seed(42)
    n_samples = 200000

    stats9 = defaultdict(int)
    case3_total9 = 0
    case3_with_ec9 = 0
    case3_ec_positions = defaultdict(int)
    case3_no_ec = []

    for _ in range(n_samples):
        mw = []
        for i in range(n9):
            mw.extend([i, i])
        random.shuffle(mw)

        L = len(mw)
        pivot_steps = [i for i, m in enumerate(mw) if m == pivot9]
        p1, p2 = pivot_steps

        pos2_steps = [i for i, m in enumerate(mw) if m == left2t9]
        pos6_steps = [i for i, m in enumerate(mw) if m == right2t9]

        def is_adj(step):
            for ps in [p1, p2]:
                if (step - ps) % L == 1 or (ps - step) % L == 1:
                    return True
            return False

        pos2_all_tight = all(is_adj(s) for s in pos2_steps)
        pos6_all_tight = all(is_adj(s) for s in pos6_steps)

        stats9['total'] += 1
        if pos2_all_tight:
            stats9['Case1_revised'] += 1
        if pos6_all_tight:
            stats9['Case2_revised'] += 1
        if not pos2_all_tight and not pos6_all_tight:
            stats9['Case3_revised'] += 1

            case3_total9 += 1

            phase1_len = (p2 - p1 - 1) % L
            phase2_len = (p1 - p2 - 1) % L
            phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
            phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

            has_ec, ec_pos = check_ec_pattern(mw, n9, [phase1_steps, phase2_steps])
            if has_ec:
                case3_with_ec9 += 1
                case3_ec_positions[ec_pos] += 1
            elif len(case3_no_ec) < 10:
                case3_no_ec.append(mw[:])

    print(f"n=9, all-fc=2 mover words, {n_samples} samples:")
    for k, v in sorted(stats9.items()):
        if k == 'total': continue
        pct = 100*v/n_samples
        print(f"  {k}: {v} ({pct:.1f}%)")

    print(f"\nCase 3 EC analysis:")
    print(f"  Total: {case3_total9}")
    print(f"  With same-phase EC: {case3_with_ec9} ({100*case3_with_ec9/max(1,case3_total9):.1f}%)")
    gap = case3_total9 - case3_with_ec9
    print(f"  Without same-phase EC: {gap} ({100*gap/max(1,case3_total9):.1f}%)")
    print(f"  EC position distribution: {dict(sorted(case3_ec_positions.items()))}")

    if case3_no_ec:
        print(f"\n  Examples without same-phase EC:")
        for mw in case3_no_ec[:5]:
            mw_str = "".join(str(m) for m in mw)
            ps = [j for j, m in enumerate(mw) if m == pivot9]
            print(f"    {mw_str}  pivot at {ps}")

    # Now check: what about ternary procs with fc=3?
    print()
    print("="*70)
    print("=== Mixed fc: ternary fc=3, binary fc=2, pivot fc=2 ===")
    print("="*70)
    print()

    ms9 = [3, 3, 2, 2, 3, 2, 2, 3, 3]
    # fc: ternary procs (0,1,7,8) get fc=3, binary (2,3,5,6) get fc=2, pivot(4) gets fc=2
    fc_target = {0:3, 1:3, 2:2, 3:2, 4:2, 5:2, 6:2, 7:3, 8:3}
    total_len = sum(fc_target.values())
    print(f"Cycle length: {total_len} (ternary fc=3, binary fc=2, pivot fc=2)")

    random.seed(42)
    n_samples2 = 100000
    stats_mixed = defaultdict(int)
    case3_total_m = 0
    case3_with_ec_m = 0
    case3_no_ec_m = []

    for _ in range(n_samples2):
        mw = []
        for i in range(n9):
            mw.extend([i] * fc_target[i])
        random.shuffle(mw)

        L = len(mw)
        pivot_steps = [i for i, m in enumerate(mw) if m == pivot9]
        if len(pivot_steps) != 2:
            continue
        p1, p2 = pivot_steps

        pos2_steps = [i for i, m in enumerate(mw) if m == left2t9]
        pos6_steps = [i for i, m in enumerate(mw) if m == right2t9]

        def is_adj_mixed(step):
            for ps in [p1, p2]:
                if (step - ps) % L == 1 or (ps - step) % L == 1:
                    return True
            return False

        pos2_all_tight = all(is_adj_mixed(s) for s in pos2_steps)
        pos6_all_tight = all(is_adj_mixed(s) for s in pos6_steps)

        stats_mixed['total'] += 1
        if pos2_all_tight:
            stats_mixed['Case1'] += 1
        if pos6_all_tight:
            stats_mixed['Case2'] += 1
        if not pos2_all_tight and not pos6_all_tight:
            stats_mixed['Case3'] += 1
            case3_total_m += 1

            phase1_len = (p2 - p1 - 1) % L
            phase2_len = (p1 - p2 - 1) % L
            phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
            phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

            has_ec, ec_pos = check_ec_pattern(mw, n9, [phase1_steps, phase2_steps])
            if has_ec:
                case3_with_ec_m += 1
            elif len(case3_no_ec_m) < 10:
                case3_no_ec_m.append(mw[:])

    print(f"Results ({n_samples2} samples):")
    for k, v in sorted(stats_mixed.items()):
        if k == 'total': continue
        pct = 100*v/stats_mixed['total']
        print(f"  {k}: {v} ({pct:.1f}%)")

    print(f"\nCase 3 EC:")
    print(f"  Total: {case3_total_m}")
    print(f"  With same-phase EC: {case3_with_ec_m} ({100*case3_with_ec_m/max(1,case3_total_m):.1f}%)")
    gap_m = case3_total_m - case3_with_ec_m
    print(f"  Without: {gap_m} ({100*gap_m/max(1,case3_total_m):.1f}%)")

    if case3_no_ec_m:
        print(f"\n  Examples without same-phase EC:")
        for mw in case3_no_ec_m[:3]:
            mw_str = "".join(str(m) for m in mw)
            ps = [j for j, m in enumerate(mw) if m == pivot9]
            print(f"    {mw_str}  pivot at {ps}")

    # Analyze the no-EC cases more carefully
    print()
    print("="*70)
    print("=== Deep analysis of no-EC Case 3 mover words ===")
    print("="*70)

    # For the Case 3 mover words without same-phase EC:
    # Could cross-phase EC save us?
    # Cross-phase: pos fires in phase 1 with triple T, and in phase 2
    # there's a non-mover step with the same triple T.
    # This requires the VALUES to match across phases, which depends on
    # the actual config trajectory.

    # For a MOVER-WORD-LEVEL check: we can't determine cross-phase EC
    # without knowing configs. But we can check a NECESSARY condition:
    # for cross-phase EC at pos p, the mover in the non-mover step
    # must not be in {p-1, p, p+1} (which we already require).

    # The real question: is the same-phase EC pattern check TIGHT?
    # Or are there mover words where EC is forced by the config trajectory
    # even though the mover word doesn't have the simple non-adjacent pattern?

    # Answer: YES, there are more EC mechanisms than just the simple pattern.
    # For example, if the same proc fires twice in a phase with different
    # values, the intermediate steps create constraints.

    # Let me check a broader EC pattern: not just consecutive-in-phase,
    # but also allowing the non-mover step to be at a pivot step.

    print("Checking broader EC: including pivot boundary steps as non-mover...")
    random.seed(42)
    case3_t2 = 0
    case3_ec2 = 0

    for _ in range(200000):
        mw = []
        for i in range(n9):
            mw.extend([i, i])
        random.shuffle(mw)

        L = len(mw)
        pivot_steps = [i for i, m in enumerate(mw) if m == pivot9]
        p1, p2 = pivot_steps

        pos2_steps = [i for i, m in enumerate(mw) if m == left2t9]
        pos6_steps = [i for i, m in enumerate(mw) if m == right2t9]

        def is_adj2(step):
            for ps in [p1, p2]:
                if (step - ps) % L == 1 or (ps - step) % L == 1:
                    return True
            return False

        pos2_all_tight = all(is_adj2(s) for s in pos2_steps)
        pos6_all_tight = all(is_adj2(s) for s in pos6_steps)

        if pos2_all_tight or pos6_all_tight:
            continue

        case3_t2 += 1

        # Broader check: for each pos, check mover step vs ALL other steps
        # (not just within a phase)
        has_ec = False
        all_steps = list(range(L))

        for pos in range(n9):
            if has_ec:
                break
            neighbors = {(pos-1)%n9, pos, (pos+1)%n9}
            mover_steps_pos = [i for i, m in enumerate(mw) if m == pos]
            nonmover_steps_pos = [i for i, m in enumerate(mw) if m != pos]

            for mi in mover_steps_pos:
                if has_ec:
                    break
                for ni in nonmover_steps_pos:
                    # For same triple: need no changes to {pos-1, pos, pos+1}
                    # between mi and ni (in either direction around the cycle).
                    # Forward: steps from min to max
                    lo, hi = min(mi, ni), max(mi, ni)

                    # Check forward path (lo+1 to hi-1)
                    between_fwd = [mw[s] for s in range(lo+1, hi)]
                    fwd_ok = not (set(between_fwd) & neighbors) and mw[ni] not in neighbors

                    # Check backward path (hi+1 to lo-1 mod L)
                    between_bwd = [mw[s % L] for s in range(hi+1, lo + L)]
                    bwd_ok = not (set(between_bwd) & neighbors) and mw[ni] not in neighbors

                    if fwd_ok or bwd_ok:
                        has_ec = True
                        break

        if has_ec:
            case3_ec2 += 1

    print(f"Case 3 with broader EC check (cross-cycle paths):")
    print(f"  Total: {case3_t2}")
    print(f"  With EC: {case3_ec2} ({100*case3_ec2/max(1,case3_t2):.1f}%)")
    print(f"  Without: {case3_t2 - case3_ec2}")

    print()
    print("="*70)
    print("=== FINAL SUMMARY ===")
    print("="*70)
    print()
    print("FINDINGS:")
    print()
    print("1. ADJACENT-PROC EC IS IMPOSSIBLE (proved analytically):")
    print("   left3t (pos 1) firing CANNOT share a boundary triple with")
    print("   left2t (pos 2) mover step. The proposed mechanism fails.")
    print()
    print("2. CASES 1/2 DO OCCUR (with revised 'tight' definition):")
    print("   'Tight' = all firings of left2t/right2t are ADJACENT to a pivot step.")
    print("   Not 'absent from interior' (which is impossible if the proc fires).")
    print()
    print("3. CASE 3 IS THE DOMINANT CASE:")
    print("   When left2t and right2t are NOT all-tight, both fire deep in phases.")
    print("   This is the majority of mover words.")
    print()
    print("4. NON-ADJACENT EC PATTERN has very high but NOT 100% coverage:")
    print("   Some Case 3 mover words lack the simple non-adjacent pattern.")
    print("   These may need cross-phase EC or more subtle mechanisms.")

if __name__ == "__main__":
    run()
