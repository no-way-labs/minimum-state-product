"""
BFL investigation -- v4: precise ratios and structural analysis.

Focus: n=9, ms=[2,3,2,3,3,3,3,3,3], sandwiched t=1.
Check ratio of BFL vs non-BFL among normalForm one-sided long phases.
Also analyze: is the second-neighbor binary or ternary?
"""

import random
from math import prod


def check_phases_at_t(word, t, ms):
    """Detailed phase analysis at sandwiched ternary t."""
    n = len(ms)
    CL = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    left2t = (t - 2) % n
    right2t = (t + 2) % n

    t_fires = [i for i, m in enumerate(word) if m == t]
    if len(t_fires) < 2:
        return {'all_normal': True, 'phases': [], 'stats': {}}

    phases = []
    all_normal = True

    for idx in range(len(t_fires)):
        a = t_fires[idx]
        s = t_fires[(idx + 1) % len(t_fires)]
        if s <= a:
            s += CL

        J = K = 0
        left2_count = right2_count = 0
        # Also track ALL other-proc fires
        other_fires = {}

        for step in range(a + 1, s):
            actual = step % CL
            mover = word[actual]
            if mover == bL:
                J += 1
            elif mover == bR:
                K += 1
            if mover == left2t:
                left2_count += 1
            if mover == right2t:
                right2_count += 1
            if mover != t:
                other_fires[mover] = other_fires.get(mover, 0) + 1

        plen = s - a - 1

        both_even = (J % 2 == 0) and (K % 2 == 0)
        toggle_left = (J >= 2) and (K == 0)
        toggle_right = (J == 0) and (K >= 2)
        is_normal = not (both_even or toggle_left or toggle_right)

        if not is_normal:
            all_normal = False

        is_os_left = (J == 1 and K == 0)
        is_os_right = (J == 0 and K == 1)

        has_bfl = False
        bfl_side = None
        bfl_second_m = None

        if is_normal and plen >= 2:
            if is_os_left and left2_count > 0:
                has_bfl = True
                bfl_side = 'left'
                bfl_second_m = ms[left2t]
            if is_os_right and right2_count > 0:
                has_bfl = True
                bfl_side = 'right'
                bfl_second_m = ms[right2t]

        phases.append({
            'a': a % CL, 's': s % CL, 'J': J, 'K': K,
            'plen': plen, 'is_normal': is_normal,
            'is_os_left': is_os_left, 'is_os_right': is_os_right,
            'left2_count': left2_count, 'right2_count': right2_count,
            'has_bfl': has_bfl, 'bfl_side': bfl_side,
            'bfl_second_m': bfl_second_m,
        })

    return {'all_normal': all_normal, 'phases': phases}


def main():
    random.seed(42)
    NUM = 500000

    # Test multiple architectures at n=9
    archs = [
        # 3 binary, gap-1 sandwiched ternary
        ([2, 3, 2, 3, 3, 3, 3, 3, 3], [1]),     # 3 binary, left2t=8(tern), right2t=3(tern)
        ([2, 3, 2, 2, 3, 3, 3, 3, 3], [1]),     # 4 binary, left2t=8(tern), right2t=3(bin)
        ([3, 2, 3, 2, 3, 3, 3, 3, 2], [0, 2]),  # 3 binary
    ]

    for ms, sand_ts in archs:
        n = len(ms)
        threshold = 4 * (3 ** (n - 2))
        product = prod(ms)
        if product >= threshold:
            print(f"\nms={ms}: product={product} >= threshold={threshold}, SKIP")
            continue

        for t in sand_ts:
            bL = (t - 1) % n
            bR = (t + 1) % n
            left2t = (t - 2) % n
            right2t = (t + 2) % n

            print(f"\n{'='*70}")
            print(f"ms={ms}, product={product}, threshold={threshold}")
            print(f"sandwiched t={t}: bL={bL}(m={ms[bL]}), bR={bR}(m={ms[bR]})")
            print(f"  left2t={left2t}(m={ms[left2t]}), right2t={right2t}(m={ms[right2t]})")
            print(f"{'='*70}")

            elements = []
            for i, m in enumerate(ms):
                elements.extend([i] * m)

            # Counters
            total = 0
            all_normal_count = 0
            total_normal_phases = 0
            os_long_phases = 0  # one-sided with length >= 2
            os_long_no_bfl = 0  # one-sided long without BFL
            os_long_with_bfl = 0  # one-sided long with BFL

            # Track where the first-neighbor fire is relative to phase start
            bfl_by_gap = {}  # gap between a and first-neighbor fire
            no_bfl_gap_dist = {}

            # Track second neighbor state sizes
            bfl_left2_ternary = 0
            bfl_left2_binary = 0
            bfl_right2_ternary = 0
            bfl_right2_binary = 0

            for _ in range(NUM):
                word = list(elements)
                random.shuffle(word)
                total += 1

                result = check_phases_at_t(word, t, ms)
                if not result['all_normal']:
                    continue

                all_normal_count += 1

                for phase in result['phases']:
                    if not phase['is_normal']:
                        continue
                    total_normal_phases += 1

                    if phase['plen'] < 2:
                        continue

                    is_os = phase['is_os_left'] or phase['is_os_right']
                    if not is_os:
                        continue

                    os_long_phases += 1

                    if phase['has_bfl']:
                        os_long_with_bfl += 1
                        if phase['bfl_side'] == 'left':
                            if ms[left2t] == 2:
                                bfl_left2_binary += 1
                            else:
                                bfl_left2_ternary += 1
                        else:
                            if ms[right2t] == 2:
                                bfl_right2_binary += 1
                            else:
                                bfl_right2_ternary += 1
                    else:
                        os_long_no_bfl += 1

            print(f"\nSampled: {total}")
            print(f"All-normalForm words: {all_normal_count} "
                  f"({100*all_normal_count/total:.1f}%)")
            print(f"Total normalForm phases (in all-NF words): "
                  f"{total_normal_phases}")
            print(f"One-sided long phases: {os_long_phases}")
            if os_long_phases > 0:
                print(f"  With BFL:    {os_long_with_bfl} "
                      f"({100*os_long_with_bfl/os_long_phases:.1f}%)")
                print(f"  Without BFL: {os_long_no_bfl} "
                      f"({100*os_long_no_bfl/os_long_phases:.1f}%)")
                print(f"\nBFL by second-neighbor type:")
                print(f"  left2t ternary:  {bfl_left2_ternary}")
                print(f"  left2t binary:   {bfl_left2_binary}")
                print(f"  right2t ternary: {bfl_right2_ternary}")
                print(f"  right2t binary:  {bfl_right2_binary}")

    # Also check: distribution of phase lengths for BFL vs non-BFL
    print(f"\n{'='*70}")
    print("PHASE LENGTH DISTRIBUTION (n=9, ms=[2,3,2,3,3,3,3,3,3], t=1)")
    print(f"{'='*70}")

    ms = [2, 3, 2, 3, 3, 3, 3, 3, 3]
    n = len(ms)
    t = 1
    elements = []
    for i, m in enumerate(ms):
        elements.extend([i] * m)

    bfl_lengths = {}
    no_bfl_lengths = {}

    for _ in range(500000):
        word = list(elements)
        random.shuffle(word)

        result = check_phases_at_t(word, t, ms)
        if not result['all_normal']:
            continue

        for phase in result['phases']:
            if not phase['is_normal'] or phase['plen'] < 2:
                continue
            is_os = phase['is_os_left'] or phase['is_os_right']
            if not is_os:
                continue

            plen = phase['plen']
            if phase['has_bfl']:
                bfl_lengths[plen] = bfl_lengths.get(plen, 0) + 1
            else:
                no_bfl_lengths[plen] = no_bfl_lengths.get(plen, 0) + 1

    all_lens = sorted(set(list(bfl_lengths.keys()) + list(no_bfl_lengths.keys())))
    print(f"{'Length':>6} | {'BFL':>8} | {'No BFL':>8} | {'BFL %':>7}")
    print("-" * 40)
    for l in all_lens:
        b = bfl_lengths.get(l, 0)
        nb = no_bfl_lengths.get(l, 0)
        total = b + nb
        pct = 100 * b / total if total > 0 else 0
        print(f"{l:>6} | {b:>8} | {nb:>8} | {pct:>6.1f}%")

    total_b = sum(bfl_lengths.values())
    total_nb = sum(no_bfl_lengths.values())
    print(f"{'TOTAL':>6} | {total_b:>8} | {total_nb:>8} | "
          f"{100*total_b/(total_b+total_nb):.1f}%")


if __name__ == '__main__':
    main()
