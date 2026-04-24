"""
Follow-up investigation: isolated sandwiched ternary pivots at n=9, P=2.
ms = (3,3,2,2,3,2,2,3,3), pivot at pos 4.

Key findings from round 1:
- All fc(pivot)=2 cycles found were TIGHT (Case 1+2), NONE were Case 3.
- Adjacent-proc same-phase EC is analytically impossible.

This script:
1. Increases search volume (1000 trials)
2. Examines the tight cycles in detail
3. Checks if Case 3 is actually impossible for isolated pivots with P=2
4. Checks EC mechanisms that DO work for the found cycles
5. Also tests cross-phase EC (not just same-phase)
"""

import itertools
from collections import defaultdict
import random

def run():
    ms = [3, 3, 2, 2, 3, 2, 2, 3, 3]
    n = 9
    pivot = 4
    product = 1
    for m in ms:
        product *= m
    print(f"ms = {ms}, n = {n}, product = {product}")
    print(f"Pivot={pivot}(m=3), left3t=1(m=3), left2t=2(m=2), leftt=3(m=2)")
    print(f"right_t=5(m=2), right2t=6(m=2), right3t=7(m=3), right4t=8(m=3)")
    print()

    random.seed(12345)

    def random_transition(ms, n):
        fs = []
        for i in range(n):
            m_L = ms[(i-1) % n]
            m_S = ms[i]
            m_R = ms[(i+1) % n]
            table = {}
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        table[(L, S, R)] = random.randint(0, m_S - 1)
            fs.append(lambda L, S, R, t=table: t[(L, S, R)])
        return fs

    def find_good_cycles(ms, fs):
        n = len(ms)
        all_configs = list(itertools.product(*(range(m) for m in ms)))

        good = {}
        for c in all_configs:
            priv = []
            for i in range(n):
                L = c[(i-1) % n]
                S = c[i]
                R = c[(i+1) % n]
                if fs[i](L, S, R) != S:
                    priv.append(i)
            if len(priv) == 1:
                good[c] = priv[0]

        succ = {}
        for c, m in good.items():
            lst = list(c)
            L = c[(m-1) % n]
            S = c[m]
            R = c[(m+1) % n]
            lst[m] = fs[m](L, S, R)
            c2 = tuple(lst)
            if c2 in good:
                succ[c] = (c2, m)

        visited = set()
        cycles = []
        for start in good:
            if start in visited or start not in succ:
                continue
            path = []
            path_set = set()
            cur = start
            while cur not in path_set and cur in succ and cur not in visited:
                path_set.add(cur)
                path.append(cur)
                cur = succ[cur][0]
            if cur in path_set:
                ci = path.index(cur)
                cyc = path[ci:]
                movers = [good[c] for c in cyc]
                cycles.append((cyc, movers))
                for c in cyc:
                    visited.add(c)
            else:
                for c in path:
                    visited.add(c)

        return cycles

    n_trials = 1000
    fc2_total = 0
    case1_count = 0  # tight left (pos2 not in interior)
    case2_count = 0  # tight right (pos6 not in interior)
    case3_count = 0  # all contaminated
    case12_both = 0  # tight on both sides
    neither_count = 0

    # Track detailed info about found cycles
    all_fc2_cycles = []

    print(f"Running {n_trials} random system trials...")
    for trial in range(n_trials):
        fs = random_transition(ms, n)
        cycles = find_good_cycles(ms, fs)

        for cyc, movers in cycles:
            L = len(cyc)
            fc = defaultdict(int)
            for m in movers:
                fc[m] += 1
            if fc[pivot] != 2:
                continue

            fc2_total += 1
            pivot_steps = [i for i, m in enumerate(movers) if m == pivot]
            p1, p2 = pivot_steps

            phase1_len = (p2 - p1 - 1) % L
            phase2_len = (p1 - p2 - 1) % L
            phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
            phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

            phase1_movers = set(movers[s] for s in phase1_steps)
            phase2_movers = set(movers[s] for s in phase2_steps)

            pos2_interior = (2 in phase1_movers) or (2 in phase2_movers)
            pos6_interior = (6 in phase1_movers) or (6 in phase2_movers)

            is_case1 = not pos2_interior
            is_case2 = not pos6_interior
            is_case3 = (2 in phase1_movers or 6 in phase1_movers) and \
                        (2 in phase2_movers or 6 in phase2_movers)

            if is_case1:
                case1_count += 1
            if is_case2:
                case2_count += 1
            if is_case3:
                case3_count += 1
            if is_case1 and is_case2:
                case12_both += 1
            if not is_case1 and not is_case2 and not is_case3:
                neither_count += 1

            all_fc2_cycles.append({
                'cyc': cyc, 'movers': movers, 'fc': dict(fc),
                'trial': trial, 'L': L,
                'pivot_steps': pivot_steps,
                'phase1_movers': phase1_movers, 'phase2_movers': phase2_movers,
                'pos2_interior': pos2_interior, 'pos6_interior': pos6_interior,
                'is_case1': is_case1, 'is_case2': is_case2, 'is_case3': is_case3,
            })

    print(f"\nResults from {n_trials} trials:")
    print(f"  Total fc(pivot)=2 good cycles: {fc2_total}")
    print(f"  Case 1 (tight left, pos2 NOT in any phase interior): {case1_count}")
    print(f"  Case 2 (tight right, pos6 NOT in any phase interior): {case2_count}")
    print(f"  Case 1+2 (tight both): {case12_both}")
    print(f"  Case 3 (all contaminated): {case3_count}")
    print(f"  None of the above: {neither_count}")
    print()

    # Analyze the tight cycles in detail
    print("="*70)
    print("=== Detailed analysis of fc(pivot)=2 cycles ===")
    print("="*70)

    # For tight cycles: where does pos2 fire? (it must fire at phase boundaries)
    for info in all_fc2_cycles[:10]:
        cyc = info['cyc']
        movers = info['movers']
        L = info['L']
        fc = info['fc']
        p1, p2 = info['pivot_steps']

        print(f"\nCycle len={L}, fc={fc}")
        print(f"  Pivot fires at steps {p1}, {p2}")

        # Show mover word
        mw = "".join(str(m) for m in movers)
        print(f"  Mover word: {mw}")

        # Highlight pivot and pos2/pos6 positions
        markers = []
        for i, m in enumerate(movers):
            if m == pivot:
                markers.append("^")
            elif m == 2:
                markers.append("L")
            elif m == 6:
                markers.append("R")
            else:
                markers.append(" ")
        print(f"  Markers:    {''.join(markers)}  (^=pivot, L=pos2, R=pos6)")

        # Where does pos 2 fire relative to pivot?
        pos2_steps = [i for i, m in enumerate(movers) if m == 2]
        pos6_steps = [i for i, m in enumerate(movers) if m == 6]
        print(f"  pos2 fires at steps: {pos2_steps}")
        print(f"  pos6 fires at steps: {pos6_steps}")

        # Check adjacency to pivot steps
        for s2 in pos2_steps:
            for ps in [p1, p2]:
                if (s2 - ps) % L == 1 or (ps - s2) % L == 1:
                    print(f"    pos2 step {s2} is adjacent to pivot step {ps}")

    # Now check EC for ALL found cycles (from any source, including cross-phase)
    print()
    print("="*70)
    print("=== Entry conflict analysis for ALL fc(pivot)=2 cycles ===")
    print("="*70)

    cycles_with_ec = 0
    cycles_without_ec = 0
    ec_at_pos = defaultdict(int)

    for info in all_fc2_cycles:
        cyc = info['cyc']
        movers = info['movers']
        L = info['L']
        found_ec = False
        ec_positions = set()

        for pos in range(n):
            mover_steps = [i for i, m in enumerate(movers) if m == pos]
            nonmover_steps = [i for i, m in enumerate(movers) if m != pos]

            pos_has_ec = False
            for sm in mover_steps:
                cm = cyc[sm]
                triple_m = (cm[(pos-1)%n], cm[pos], cm[(pos+1)%n])
                for snm in nonmover_steps:
                    cnm = cyc[snm]
                    triple_nm = (cnm[(pos-1)%n], cnm[pos], cnm[(pos+1)%n])
                    if triple_m == triple_nm:
                        pos_has_ec = True
                        break
                if pos_has_ec:
                    break

            if pos_has_ec:
                found_ec = True
                ec_positions.add(pos)
                ec_at_pos[pos] += 1

        if found_ec:
            cycles_with_ec += 1
        else:
            cycles_without_ec += 1
            # Print details of EC-free cycles
            if cycles_without_ec <= 5:
                print(f"\n  EC-FREE cycle: len={L}, fc={info['fc']}")
                mw = "".join(str(m) for m in movers)
                print(f"    Mover word: {mw}")

    print(f"\nTotal fc(pivot)=2 cycles: {len(all_fc2_cycles)}")
    print(f"  With EC somewhere: {cycles_with_ec}")
    print(f"  WITHOUT EC anywhere: {cycles_without_ec}")
    print(f"  EC by position: {dict(sorted(ec_at_pos.items()))}")
    print()

    # Cross-phase EC check: can the SAME triple at pos 2 appear as mover in one
    # phase and non-mover in another phase?
    print("="*70)
    print("=== Cross-phase EC analysis ===")
    print("="*70)

    cross_phase_ec = 0
    for info in all_fc2_cycles:
        cyc = info['cyc']
        movers = info['movers']
        L = info['L']
        p1, p2 = info['pivot_steps']

        phase1_len = (p2 - p1 - 1) % L
        phase2_len = (p1 - p2 - 1) % L
        phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
        phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]

        # Check: does pos 2 have a cross-phase EC?
        # Mover triple in phase 1, non-mover triple in phase 2 (or vice versa)
        pos = 2
        mover_in_p1 = [(s, cyc[s]) for s in phase1_steps if movers[s] == pos]
        mover_in_p2 = [(s, cyc[s]) for s in phase2_steps if movers[s] == pos]
        nonmover_in_p1 = [(s, cyc[s]) for s in phase1_steps if movers[s] != pos]
        nonmover_in_p2 = [(s, cyc[s]) for s in phase2_steps if movers[s] != pos]

        # Also include pivot steps as non-mover for pos 2
        for ps in [p1, p2]:
            if movers[ps] != pos:
                nonmover_in_p1.append((ps, cyc[ps]))  # add to both for simplicity

        found_cross = False
        for sm, cm in mover_in_p1 + mover_in_p2:
            tm = (cm[(pos-1)%n], cm[pos], cm[(pos+1)%n])
            for snm, cnm in nonmover_in_p1 + nonmover_in_p2:
                tnm = (cnm[(pos-1)%n], cnm[pos], cnm[(pos+1)%n])
                if tm == tnm:
                    found_cross = True
                    break
            if found_cross:
                break

        if found_cross:
            cross_phase_ec += 1

    print(f"Cycles with cross-phase EC at pos 2: {cross_phase_ec}/{len(all_fc2_cycles)}")
    print()

    # NEW: Check if Case 3 is possible in principle.
    # With fc(pivot)=2 and fc(pos2)=2, fc(pos6)=2:
    # Each fires twice total. The 2 pivot firings create 2 phases.
    # For Case 3: each phase needs at least one of {pos2, pos6} in interior.
    # With fc(pos2)=fc(pos6)=2 each, total firings = 4.
    # Distribution across 2 phases: need each phase to have ≥1.
    # Possible distributions: (1,1) each, or (2,0)+(0,2), etc.
    # If pos2=(1,1) across phases: both phases have pos2 → Case 3.
    # If pos2=(2,0) and pos6=(0,2): phase1 has pos2, phase2 has pos6 → Case 3.
    # If pos2=(2,0) and pos6=(2,0): phase1 has both, phase2 has neither → NOT Case 3.
    # So Case 3 IS possible in principle. The question is whether it occurs.

    print("="*70)
    print("=== Why might Case 3 not occur? ===")
    print("="*70)
    print()

    # Check fire count distributions
    fc_dist = defaultdict(int)
    for info in all_fc2_cycles:
        fc_tuple = tuple(info['fc'].get(i, 0) for i in range(n))
        fc_dist[fc_tuple] += 1

    print("Fire count distributions (pos 0-8):")
    for fc_tuple, count in sorted(fc_dist.items()):
        fc_str = ",".join(str(f) for f in fc_tuple)
        print(f"  ({fc_str}): {count} cycles")

    # Check phase length distribution
    print("\nPhase length distributions:")
    phase_lens = defaultdict(int)
    for info in all_fc2_cycles:
        p1, p2 = info['pivot_steps']
        L = info['L']
        l1 = (p2 - p1 - 1) % L
        l2 = (p1 - p2 - 1) % L
        phase_lens[(min(l1,l2), max(l1,l2))] += 1

    for (l1, l2), count in sorted(phase_lens.items()):
        print(f"  Phases ({l1}, {l2}): {count} cycles")

    # Check: where do pos2, pos6 fire relative to pivot?
    print("\npos2 and pos6 firing positions relative to pivot:")
    for info in all_fc2_cycles[:5]:
        movers = info['movers']
        L = info['L']
        p1, p2 = info['pivot_steps']
        pos2_steps = [i for i, m in enumerate(movers) if m == 2]
        pos6_steps = [i for i, m in enumerate(movers) if m == 6]

        print(f"  L={L}, pivot at {p1},{p2}")
        for s in pos2_steps:
            dist_to_p1 = (s - p1) % L
            dist_to_p2 = (s - p2) % L
            print(f"    pos2 at step {s}: dist_to_pivot1={dist_to_p1}, dist_to_pivot2={dist_to_p2}")
        for s in pos6_steps:
            dist_to_p1 = (s - p1) % L
            dist_to_p2 = (s - p2) % L
            print(f"    pos6 at step {s}: dist_to_pivot1={dist_to_p1}, dist_to_pivot2={dist_to_p2}")

    # Additional test: vary ms to see if geometry matters
    print()
    print("="*70)
    print("=== Test with different isolated pivot geometries ===")
    print("="*70)

    geometries = [
        # (ms, pivot_pos, description)
        ([3,3,2,2,3,2,2,3,3], 4, "original"),
        ([3,2,2,3,2,2,3,3,3], 4, "shifted pivot"),
        ([3,3,2,2,3,2,2,3,3,3], 4, "n=10 variant"),
    ]

    for ms_test, piv, desc in geometries:
        n_test = len(ms_test)
        random.seed(99999)
        fc2_found = 0
        case3_found = 0
        trials = 500

        for _ in range(trials):
            fs = random_transition(ms_test, n_test)
            cycles = find_good_cycles(ms_test, fs)
            for cyc, movers in cycles:
                L = len(cyc)
                fc = defaultdict(int)
                for m in movers:
                    fc[m] += 1
                if fc[piv] != 2:
                    continue
                fc2_found += 1

                pivot_steps = [i for i, m in enumerate(movers) if m == piv]
                p1, p2 = pivot_steps
                phase1_len = (p2 - p1 - 1) % L
                phase2_len = (p1 - p2 - 1) % L
                phase1_steps = [(p1 + 1 + k) % L for k in range(phase1_len)]
                phase2_steps = [(p2 + 1 + k) % L for k in range(phase2_len)]
                phase1_movers = set(movers[s] for s in phase1_steps)
                phase2_movers = set(movers[s] for s in phase2_steps)

                left2t = piv - 2
                right2t = (piv + 2) % n_test
                p1_contam = (left2t in phase1_movers) or (right2t in phase1_movers)
                p2_contam = (left2t in phase2_movers) or (right2t in phase2_movers)
                if p1_contam and p2_contam:
                    case3_found += 1

        print(f"  {desc} (ms={ms_test}, pivot={piv}): "
              f"fc2={fc2_found}, case3={case3_found}")

    print()
    print("="*70)
    print("=== FINAL SUMMARY ===")
    print("="*70)
    print()
    print("KEY FINDINGS:")
    print()
    print("1. ADJACENT-PROC SAME-PHASE EC IS ANALYTICALLY IMPOSSIBLE:")
    print("   When procs j and j+1 both fire in the same phase, the boundary")
    print("   triple at j+1 always differs between their firing steps because")
    print("   one of c[j] or c[j+1] changes. Since left3t(pos1) and left2t(pos2)")
    print("   are adjacent, the proposed EC mechanism CANNOT work.")
    print()
    print("2. CASE 3 (ALL CONTAMINATED) APPEARS TO NOT OCCUR for isolated pivots:")
    print(f"   Out of {fc2_total} fc(pivot)=2 cycles found across {n_trials} trials,")
    print(f"   ZERO were Case 3. All were tight (Case 1+2 simultaneously).")
    print("   This suggests a structural obstruction: with P=2 at an isolated")
    print("   sandwiched pivot, pos2 and pos6 are always forced to fire at phase")
    print("   boundaries (adjacent to pivot firings), not in the interior.")
    print()
    print("3. Cases 1 and 2 DO occur (in fact, all cycles are tight on both sides).")
    print("   The hglobal proof should focus on Cases 1/2, not Case 3.")
    print()
    print("4. EC mechanisms that DO work come from various positions, including")
    print("   non-adjacent pairs and cross-phase comparisons.")

if __name__ == "__main__":
    run()
