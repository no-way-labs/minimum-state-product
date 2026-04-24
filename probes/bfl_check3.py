"""
BFL sub-case investigation -- v3.

Focus on the architectures that ACTUALLY arise in the LB proof at n>=9:
- Sub-threshold product < 4*3^(n-2)
- >= 3 binary procs
- No 3 consecutive binary (that case is handled by shadow/palindromic)
- Sandwiched ternary t: ms[left(t)]=2, ms[right(t)]=2, ms[t]>=3

At n=9 with 3 binary and 6 ternary, sub-threshold means product < 4*3^7 = 8748.
But 2^3 * 3^6 = 5832 < 8748. So ms could be [2,3,3,2,3,3,2,3,3] (3 binary
equally spaced). This has NO sandwiched ternary (gaps of size 2 between binary).

For sandwiched ternary to exist, we need a gap of exactly 1: two binary procs
with exactly one ternary between them. Like [...,2,3,2,...].

With 3 binary on a 9-ring and no 3 consecutive, possible gap patterns:
- (1,2,3), (1,3,2), (2,1,3), (2,3,1), (3,1,2), (3,2,1)
  where gaps are distances between binary procs (must sum to 6 = n-3).
- For sandwiched ternary: need at least one gap of exactly 1.

So we need gap patterns like (1,2,3), (1,3,2), (2,1,3), (2,3,1), (3,1,2), (3,2,1),
(1,1,4), (1,4,1), (4,1,1), (1,1,1) [but this would be 3 consecutive if gap=1,1,1
means b,t,b,t,b,t -- 3 gaps of 1 on 9-ring: binary at 0,2,4 with total gap = 6,
no that's gaps 2,2,2 not 1,1,1].

Actually gap = number of ternary procs between consecutive binary. With 3 binary
on a 9-ring, gaps = (g1, g2, g3) where g1+g2+g3 = 6 (6 ternary procs).
Gap of 1 means one ternary sandwiched between two binary.

Let me enumerate and use random sampling of mover words for large spaces.
"""

import random
from collections import Counter
from math import factorial, prod


def find_sandwiched_ternary(ms):
    n = len(ms)
    result = []
    for t in range(n):
        if ms[t] >= 3:
            bL = (t - 1) % n
            bR = (t + 1) % n
            if ms[bL] == 2 and ms[bR] == 2:
                result.append(t)
    return result


def check_phases_at_t(word, t, ms):
    """Check TernaryPhase structure at sandwiched ternary t.

    Returns (all_normal, has_one_sided_long, has_bfl, bfl_details)
    """
    n = len(ms)
    CL = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    left2t = (t - 2) % n
    right2t = (t + 2) % n

    t_fires = [i for i, m in enumerate(word) if m == t]
    if len(t_fires) < 2:
        return True, False, False, []

    all_normal = True
    has_one_sided_long = False
    has_bfl = False
    bfl_details = []

    for idx in range(len(t_fires)):
        a = t_fires[idx]
        s = t_fires[(idx + 1) % len(t_fires)]
        if s <= a:
            s += CL

        J = 0
        K = 0
        left2_fires = []
        right2_fires = []

        for step in range(a + 1, s):
            actual_step = step % CL
            mover = word[actual_step]
            if mover == bL:
                J += 1
            if mover == bR:
                K += 1
            if mover == left2t:
                left2_fires.append(step - a)
            if mover == right2t:
                right2_fires.append(step - a)

        phase_length = s - a - 1

        both_even = (J % 2 == 0) and (K % 2 == 0)
        toggle_left = (J >= 2) and (K == 0)
        toggle_right = (J == 0) and (K >= 2)
        is_normal = not (both_even or toggle_left or toggle_right)

        if not is_normal:
            all_normal = False

        is_one_sided_left = (J == 1 and K == 0)
        is_one_sided_right = (J == 0 and K == 1)

        if is_normal and phase_length >= 2:
            if is_one_sided_left or is_one_sided_right:
                has_one_sided_long = True

                # Check BFL
                if is_one_sided_left and len(left2_fires) > 0:
                    has_bfl = True
                    bfl_details.append({
                        'a': a % CL, 's': s % CL,
                        'J': J, 'K': K, 'len': phase_length,
                        'side': 'left', 'left2t': left2t,
                        'l2_fires': left2_fires,
                        'ms_left2t': ms[left2t],
                    })
                if is_one_sided_right and len(right2_fires) > 0:
                    has_bfl = True
                    bfl_details.append({
                        'a': a % CL, 's': s % CL,
                        'J': J, 'K': K, 'len': phase_length,
                        'side': 'right', 'right2t': right2t,
                        'r2_fires': right2_fires,
                        'ms_right2t': ms[right2t],
                    })

    return all_normal, has_one_sided_long, has_bfl, bfl_details


def random_mover_word(ms):
    """Generate a random mover word where proc i appears ms[i] times."""
    elements = []
    for i, m in enumerate(ms):
        elements.extend([i] * m)
    random.shuffle(elements)
    return elements


def gen_architectures_with_sandwiched(n, num_binary=3):
    """Generate architectures with sandwiched ternary at n procs.

    Place num_binary binary procs with remaining ternary, ensuring
    at least one gap of exactly 1.
    """
    remaining = n - num_binary  # number of ternary procs
    # Gaps: (g1, g2, ..., g_{num_binary}) summing to remaining
    # Each gap >= 1 to avoid 3-consecutive (gap 0 means adjacent binary).
    # Wait: gap 0 = two adjacent binary = 2 consecutive binary (allowed).
    # Gap 0 + gap 0 at same binary = 3 consecutive binary (forbidden).
    # Actually, "no 3 consecutive binary" means no three binary procs
    # i, i+1, i+2 on the ring. This means no two consecutive gaps of 0.

    # For sandwiched ternary: need at least one gap == 1.

    results = []

    # Enumerate gap tuples
    def gen_gaps(num_gaps, total, current):
        if num_gaps == 1:
            current.append(total)
            yield list(current)
            current.pop()
            return
        for g in range(0, total + 1):
            current.append(g)
            yield from gen_gaps(num_gaps - 1, total - g, current)
            current.pop()

    for gaps in gen_gaps(num_binary, remaining, []):
        # Check: no 3 consecutive binary (no two adjacent 0-gaps on ring)
        has_3consec = False
        for i in range(num_binary):
            if gaps[i] == 0 and gaps[(i + 1) % num_binary] == 0:
                has_3consec = True
                break
        if has_3consec:
            continue

        # Check: at least one gap == 1
        if 1 not in gaps:
            continue

        # Build ms vector
        # Place binary at positions, ternary in gaps
        # First binary at position 0
        ms = []
        for i in range(num_binary):
            ms.append(2)  # binary
            ms.extend([3] * gaps[i])  # ternary gap

        assert len(ms) == n
        assert sum(1 for m in ms if m == 2) == num_binary

        results.append(ms)

    return results


def main():
    random.seed(42)
    NUM_SAMPLES = 200000  # per architecture

    print("BFL Sub-case Investigation at n=9..13")
    print("=" * 70)

    for n in [5, 7, 9, 11]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n={n}, threshold={threshold}")
        print(f"{'='*70}")

        # For each n, get architectures with sandwiched ternary
        for num_bin in [3, 4]:
            if num_bin >= n:
                continue

            archs = gen_architectures_with_sandwiched(n, num_bin)

            for ms in archs:
                product = prod(ms)
                if product >= threshold:
                    continue

                sand = find_sandwiched_ternary(ms)
                if not sand:
                    continue

                CL = sum(ms)  # cycle length with fc = m_p

                # How many unique mover words?
                num_perms = factorial(CL)
                for i in range(n):
                    num_perms //= factorial(ms[i])

                # Sample or enumerate
                if num_perms <= 500000:
                    # Enumerate all
                    sample_type = "exhaustive"
                    num_to_check = num_perms
                else:
                    sample_type = "sampled"
                    num_to_check = NUM_SAMPLES

                total_words = 0
                words_all_normal = 0
                words_osl = 0  # one-sided long
                words_bfl = 0
                bfl_examples = []

                if sample_type == "exhaustive":
                    # Use generator
                    elements = []
                    for i, m in enumerate(ms):
                        elements.extend([i] * m)

                    def unique_perms(seq):
                        if len(seq) <= 1:
                            yield list(seq)
                            return
                        seen = set()
                        for i, elem in enumerate(seq):
                            if elem in seen:
                                continue
                            seen.add(elem)
                            rest = seq[:i] + seq[i+1:]
                            for perm in unique_perms(rest):
                                yield [elem] + perm

                    for word in unique_perms(elements):
                        total_words += 1
                        for t in sand:
                            all_n, osl, bfl, details = check_phases_at_t(word, t, ms)
                            if all_n:
                                words_all_normal += 1
                                if osl:
                                    words_osl += 1
                                if bfl:
                                    words_bfl += 1
                                    if len(bfl_examples) < 3:
                                        bfl_examples.append({
                                            'word': word[:20],
                                            't': t,
                                            'details': details[:2],
                                        })
                                break  # count word once
                else:
                    for _ in range(num_to_check):
                        word = random_mover_word(ms)
                        total_words += 1
                        for t in sand:
                            all_n, osl, bfl, details = check_phases_at_t(word, t, ms)
                            if all_n:
                                words_all_normal += 1
                                if osl:
                                    words_osl += 1
                                if bfl:
                                    words_bfl += 1
                                    if len(bfl_examples) < 3:
                                        bfl_examples.append({
                                            'word': word[:20],
                                            't': t,
                                            'details': details[:2],
                                        })
                                break

                print(f"\n  ms={ms}, product={product}, CL={CL}, "
                      f"sandwiched={sand}")
                print(f"  {sample_type}: {total_words} words checked "
                      f"(of {num_perms} total)")
                print(f"  all-normalForm: {words_all_normal}  "
                      f"one-sided-long: {words_osl}  BFL: {words_bfl}")

                if bfl_examples:
                    for ex in bfl_examples[:2]:
                        print(f"  BFL: t={ex['t']}, word={ex['word']}...")
                        for d in ex['details']:
                            print(f"    phase ({d['a']},{d['s']}): "
                                  f"J={d['J']},K={d['K']},len={d['len']}, "
                                  f"side={d['side']}")

    # Also check: at what n does BFL become impossible?
    # The key question: at n=9 with gap-1 architectures, does BFL occur?
    print(f"\n{'='*70}")
    print("FOCUSED CHECK: n=9, ms=[2,3,2,3,3,3,3,3,3] and variants")
    print(f"{'='*70}")

    for ms in [
        [2, 3, 2, 3, 3, 3, 3, 3, 3],  # gap (1, 5): sandwiched at t=1
        [2, 3, 2, 2, 3, 3, 3, 3, 3],  # 4 binary, gap (1,0,4)
        [2, 3, 2, 3, 3, 2, 3, 3, 3],  # 3 binary, gaps (1,2,3)
        [2, 3, 2, 3, 2, 3, 3, 3, 3],  # 3 binary, gaps (1,1,4)
        [3, 2, 3, 2, 3, 3, 3, 3, 2],  # 3 binary, gaps (1,3,2)
    ]:
        n = len(ms)
        product = prod(ms)
        threshold = 4 * (3 ** (n - 2))
        sand = find_sandwiched_ternary(ms)

        if product >= threshold or not sand:
            print(f"  ms={ms}: product={product} (thresh {threshold}), "
                  f"sand={sand} -- SKIP")
            continue

        CL = sum(ms)

        total = 0
        an = 0  # all_normal
        osl = 0  # one_sided_long
        bfl = 0
        bfl_examples = []

        for _ in range(NUM_SAMPLES):
            word = random_mover_word(ms)
            total += 1
            for t in sand:
                all_n, is_osl, is_bfl, details = check_phases_at_t(word, t, ms)
                if all_n:
                    an += 1
                    if is_osl:
                        osl += 1
                    if is_bfl:
                        bfl += 1
                        if len(bfl_examples) < 3:
                            bfl_examples.append({'t': t, 'details': details[:2],
                                                 'word': word[:25]})
                    break

        print(f"\n  ms={ms}, product={product}, CL={CL}, sand={sand}")
        print(f"  sampled {total}: all_normal={an}, one_sided_long={osl}, BFL={bfl}")

        if bfl_examples:
            for ex in bfl_examples[:2]:
                print(f"  BFL: t={ex['t']}, word prefix={ex['word']}")
                for d in ex['details']:
                    side = d['side']
                    second = d.get('left2t', d.get('right2t'))
                    print(f"    phase ({d['a']},{d['s']}): "
                          f"J={d['J']},K={d['K']},len={d['len']}, "
                          f"side={side}, 2nd-neighbor=proc {second} "
                          f"(m={ms[second]})")


if __name__ == '__main__':
    main()
