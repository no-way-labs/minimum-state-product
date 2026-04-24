"""
Comprehensive provider existence verification with CORRECT phase finder.

Check all zero-winding walks with the right properties have a provider.
"""
import sys
sys.path.insert(0, './claude')


def check_provider_correct(word, ms, n):
    """Correct provider check: enumerate ALL valid TernaryPhases."""
    L = len(word)

    # Fire steps for each proc
    fire_steps = {p: [] for p in range(n)}
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    # For each proc t, for each firing step s, for each valid start a
    for t in range(n):
        fsteps = fire_steps[t]
        for s in fsteps:
            # Find the previous firing of t (or use 0 if no earlier firing)
            prev_fire = -1
            for k in range(s - 1, -1, -1):
                if word[k] == t:
                    prev_fire = k
                    break

            # a can be any step in (prev_fire, s) where t is nonmover
            for a in range(prev_fire + 1, s):
                if word[a] == t:
                    continue  # a must be nonmover for t

                left_t = (t - 1) % n
                right_t = (t + 1) % n

                # Count neighbor fires in [a, s)
                left_fires = sum(1 for k in range(a, s) if word[k] == left_t)
                right_fires = sum(1 for k in range(a, s) if word[k] == right_t)

                # Check provider conditions
                if left_fires == 0 and ms[right_t] == 2 and right_fires >= 2 and right_fires % 2 == 0:
                    return True, (t, a, s, 'left_silent', right_fires)
                if right_fires == 0 and ms[left_t] == 2 and left_fires >= 2 and left_fires % 2 == 0:
                    return True, (t, a, s, 'right_silent', left_fires)

    return False, None


def generate_walks(n, L):
    """Generate ring walks of length L (consecutive movers adjacent)."""
    def extend(word):
        if len(word) == L:
            yield word[:]
            return
        last = word[-1]
        for nxt in [(last - 1) % n, last, (last + 1) % n]:
            word.append(nxt)
            yield from extend(word)
            word.pop()

    for start in range(n):
        yield from extend([start])


def check_ms(n, ms, max_L=None):
    """Check all valid ZW walks for a given ms."""
    if max_L is None:
        max_L = 3 * n

    binary_procs = [i for i in range(n) if ms[i] == 2]
    print(f"\nn={n}, ms={ms}, binary={binary_procs}")

    total_checked = 0
    total_provider = 0
    counter_examples = []

    for L in range(2 * n, max_L + 1):
        count_valid = 0
        count_provider = 0

        for word in generate_walks(n, L):
            # ZW check
            disp = 0
            cw = 0
            for i in range(L):
                nxt = word[(i + 1) % L]
                diff = (nxt - word[i]) % n
                if diff == 1:
                    disp += 1
                    cw += 1
                elif diff == n - 1:
                    disp -= 1
            if disp != 0 or cw == 0:
                continue

            # fc >= 2 for all
            fc = [0] * n
            for m in word:
                fc[m] += 1
            if any(f < 2 for f in fc):
                continue

            # some fc >= 3
            if max(fc) < 3:
                continue

            # no safe proc
            touched = set()
            for m in word:
                touched.add(m)
                touched.add((m - 1) % n)
                touched.add((m + 1) % n)
            if len(touched) < n:
                continue

            count_valid += 1

            found, info = check_provider_correct(word, ms, n)
            if found:
                count_provider += 1
            else:
                counter_examples.append((L, word[:], fc[:]))

        if count_valid > 0:
            pct = count_provider / count_valid * 100
            print(f"  L={L}: {count_valid} valid, {count_provider} with provider ({pct:.1f}%)")

        total_checked += count_valid
        total_provider += count_provider

    print(f"  TOTAL: {total_checked} valid, {total_provider} with provider")
    if counter_examples:
        print(f"  {len(counter_examples)} COUNTER-EXAMPLES!")
        for L, w, fc in counter_examples[:5]:
            print(f"    L={L}: {w}, fc={fc}")
    else:
        print(f"  ALL HAVE PROVIDER")

    return len(counter_examples) == 0


def main():
    print("=== Provider existence verification (correct finder) ===\n")

    # Test cases: n=5 with 3 non-consecutive binary
    test_cases = [
        (5, [2, 3, 2, 3, 2]),
        (5, [3, 2, 3, 2, 2]),  # 2 consecutive at end -- skip if consecutive
    ]

    for n, ms in test_cases:
        # Check non-consecutive binary
        has3 = sum(1 for m in ms if m == 2) >= 3
        non_consec = True
        for i in range(n):
            if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
                non_consec = False
        if not has3 or not non_consec:
            print(f"Skipping n={n}, ms={ms}: not 3 non-consecutive binary")
            continue

        check_ms(n, ms, max_L=3*n)

    # Also check n=6
    print("\n\n=== n=6 checks ===")
    n6_cases = [
        [2, 3, 2, 3, 2, 3],
        [2, 3, 3, 2, 3, 2],
    ]
    for ms in n6_cases:
        n = 6
        has3 = sum(1 for m in ms if m == 2) >= 3
        non_consec = True
        for i in range(n):
            if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
                non_consec = False
        if not has3 or not non_consec:
            print(f"Skipping n={n}, ms={ms}")
            continue
        check_ms(n, ms, max_L=2*n+4)  # Shorter range for n=6


if __name__ == "__main__":
    main()
