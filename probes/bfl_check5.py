"""
BFL scaling analysis: how does BFL rate change with n?

For each n from 5 to 15, sample random mover words for a canonical
architecture with sandwiched ternary and measure BFL rate.
"""

import random
from math import prod


def check_phases_at_t_quick(word, t, n):
    """Quick phase check: only track BFL occurrence."""
    CL = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    left2t = (t - 2) % n
    right2t = (t + 2) % n

    t_fires = [i for i, m in enumerate(word) if m == t]
    if len(t_fires) < 2:
        return 'all_normal', False, False

    all_normal = True
    has_osl = False  # one-sided long
    has_bfl = False

    for idx in range(len(t_fires)):
        a = t_fires[idx]
        s = t_fires[(idx + 1) % len(t_fires)]
        if s <= a:
            s += CL

        J = K = 0
        left2_count = right2_count = 0

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

        plen = s - a - 1

        both_even = (J % 2 == 0) and (K % 2 == 0)
        toggle_left = (J >= 2) and (K == 0)
        toggle_right = (J == 0) and (K >= 2)
        is_normal = not (both_even or toggle_left or toggle_right)

        if not is_normal:
            all_normal = False

        if is_normal and plen >= 2:
            is_os_left = (J == 1 and K == 0)
            is_os_right = (J == 0 and K == 1)
            if is_os_left or is_os_right:
                has_osl = True
                if is_os_left and left2_count > 0:
                    has_bfl = True
                if is_os_right and right2_count > 0:
                    has_bfl = True

    return all_normal, has_osl, has_bfl


def main():
    random.seed(42)
    NUM = 200000

    print(f"{'n':>3} | {'ms':>35} | {'prod':>8} | {'thresh':>8} | "
          f"{'allNF%':>7} | {'OSL/NF%':>8} | {'BFL/OSL%':>9} | "
          f"{'BFL/NF%':>8}")
    print("-" * 120)

    for n in [5, 6, 7, 8, 9, 10, 11, 13, 15]:
        threshold = 4 * (3 ** (n - 2))

        # Architecture: [2, 3, 2, 3, 3, ..., 3] with t=1 sandwiched
        ms = [2, 3, 2] + [3] * (n - 3)
        product = prod(ms)

        if product >= threshold:
            # Reduce: add more binary procs
            # [2, 3, 2, 2, 3, 3, ..., 3]
            ms = [2, 3, 2, 2] + [3] * (n - 4)
            product = prod(ms)

        if product >= threshold:
            ms = [2, 3, 2, 2, 2] + [3] * (n - 5)
            product = prod(ms)

        if product >= threshold:
            print(f"{n:>3} | {str(ms):>35} | {product:>8} | {threshold:>8} | SKIP")
            continue

        t = 1
        bL = 0
        bR = 2
        assert ms[bL] == 2 and ms[bR] == 2 and ms[t] == 3

        elements = []
        for i, m in enumerate(ms):
            elements.extend([i] * m)

        all_nf = 0
        osl = 0
        bfl = 0

        for _ in range(NUM):
            word = list(elements)
            random.shuffle(word)

            is_an, is_osl, is_bfl = check_phases_at_t_quick(word, t, n)
            if is_an:
                all_nf += 1
                if is_osl:
                    osl += 1
                if is_bfl:
                    bfl += 1

        nf_pct = 100 * all_nf / NUM
        osl_pct = 100 * osl / all_nf if all_nf else 0
        bfl_osl_pct = 100 * bfl / osl if osl else 0
        bfl_nf_pct = 100 * bfl / all_nf if all_nf else 0

        ms_str = str(ms) if len(str(ms)) <= 35 else str(ms)[:32] + "..."
        print(f"{n:>3} | {ms_str:>35} | {product:>8} | {threshold:>8} | "
              f"{nf_pct:>6.1f}% | {osl_pct:>7.1f}% | {bfl_osl_pct:>8.1f}% | "
              f"{bfl_nf_pct:>7.1f}%")

    # Now check: does BFL rate INCREASE with phase length?
    # At n=13 specifically
    print(f"\n{'='*70}")
    print("BFL rate by phase length at n=13")
    print(f"{'='*70}")

    n = 13
    ms = [2, 3, 2, 2] + [3] * 9
    product = prod(ms)
    threshold = 4 * (3 ** (n - 2))
    t = 1

    elements = []
    for i, m in enumerate(ms):
        elements.extend([i] * m)

    bfl_by_len = {}
    nobfl_by_len = {}

    for _ in range(300000):
        word = list(elements)
        random.shuffle(word)

        CL = len(word)
        bL = (t - 1) % n
        bR = (t + 1) % n
        left2t = (t - 2) % n
        right2t = (t + 2) % n

        t_fires = [i for i, m in enumerate(word) if m == t]
        if len(t_fires) < 2:
            continue

        all_normal = True
        for idx in range(len(t_fires)):
            a = t_fires[idx]
            s = t_fires[(idx + 1) % len(t_fires)]
            if s <= a:
                s += CL
            J = K = 0
            for step in range(a + 1, s):
                mover = word[step % CL]
                if mover == bL:
                    J += 1
                elif mover == bR:
                    K += 1
            both_even = (J % 2 == 0) and (K % 2 == 0)
            toggle_left = (J >= 2) and (K == 0)
            toggle_right = (J == 0) and (K >= 2)
            if both_even or toggle_left or toggle_right:
                all_normal = False
                break

        if not all_normal:
            continue

        for idx in range(len(t_fires)):
            a = t_fires[idx]
            s = t_fires[(idx + 1) % len(t_fires)]
            if s <= a:
                s += CL
            J = K = left2_count = right2_count = 0
            for step in range(a + 1, s):
                mover = word[step % CL]
                if mover == bL:
                    J += 1
                elif mover == bR:
                    K += 1
                if mover == left2t:
                    left2_count += 1
                if mover == right2t:
                    right2_count += 1
            plen = s - a - 1
            if plen < 2:
                continue
            is_os_left = (J == 1 and K == 0)
            is_os_right = (J == 0 and K == 1)
            if not (is_os_left or is_os_right):
                continue
            has_bfl = (is_os_left and left2_count > 0) or \
                      (is_os_right and right2_count > 0)
            if has_bfl:
                bfl_by_len[plen] = bfl_by_len.get(plen, 0) + 1
            else:
                nobfl_by_len[plen] = nobfl_by_len.get(plen, 0) + 1

    all_lens = sorted(set(list(bfl_by_len.keys()) + list(nobfl_by_len.keys())))
    print(f"{'Len':>4} | {'BFL':>7} | {'NoB':>7} | {'BFL%':>6}")
    print("-" * 35)
    for l in all_lens[:25]:
        b = bfl_by_len.get(l, 0)
        nb = nobfl_by_len.get(l, 0)
        tot = b + nb
        pct = 100 * b / tot if tot else 0
        print(f"{l:>4} | {b:>7} | {nb:>7} | {pct:>5.1f}%")
    tb = sum(bfl_by_len.values())
    tnb = sum(nobfl_by_len.values())
    print(f"{'ALL':>4} | {tb:>7} | {tnb:>7} | {100*tb/(tb+tnb):.1f}%")


if __name__ == '__main__':
    main()
