"""
Fast provider check at n=5 only, restricted cycle lengths.
"""
import sys
sys.path.insert(0, './claude')


def check_provider(word, ms, n):
    """Check if provider exists in walk word."""
    L = len(word)

    fire_steps = {}
    for p in range(n):
        fire_steps[p] = []
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    for t in range(n):
        fsteps = fire_steps[t]
        for s in fsteps:
            # Find latest previous fire of t
            prev_fire = -1
            for k in range(s - 1, -1, -1):
                if word[k] == t:
                    prev_fire = k
                    break

            left_t = (t - 1) % n
            right_t = (t + 1) % n

            # Try each valid start a
            # Cumulative counts from s-1 down to prev_fire+1
            left_acc = 0
            right_acc = 0

            for a in range(s - 1, prev_fire, -1):
                if word[a] == t:
                    continue
                if word[a] == left_t:
                    left_acc += 1
                elif word[a] == right_t:
                    right_acc += 1

                # At this point, left_acc = fires of left_t in [a, s), etc.
                # But we need [a, s), so we need fires from a to s-1
                # We're accumulating from s-1 down, so this IS [a, s)
                lf = left_acc
                rf = right_acc

                if lf == 0 and ms[right_t] == 2 and rf >= 2 and rf % 2 == 0:
                    return True
                if rf == 0 and ms[left_t] == 2 and lf >= 2 and lf % 2 == 0:
                    return True

    return False


def main():
    n = 5
    ms = [2, 3, 2, 3, 2]
    print(f"n={n}, ms={ms}")

    total = 0
    found = 0
    missing = 0

    for L in range(2 * n + 1, 2 * n + 6):  # L = 11, 12, 13, 14, 15
        count = 0
        count_found = 0
        counterexamples = []

        # Generate walks
        def gen(word):
            nonlocal count, count_found, counterexamples
            if len(word) == L:
                # Check properties
                disp = 0
                cw = 0
                for i in range(L):
                    nxt = word[(i + 1) % L]
                    diff = (nxt - word[i]) % n
                    if diff == 1:
                        cw += 1
                        disp += 1
                    elif diff == n - 1:
                        disp -= 1
                if disp != 0 or cw == 0:
                    return

                fc = [0] * n
                for m in word:
                    fc[m] += 1
                if any(f < 2 for f in fc):
                    return
                if max(fc) < 3:
                    return

                touched = set()
                for m in word:
                    touched.add(m)
                    touched.add((m - 1) % n)
                    touched.add((m + 1) % n)
                if len(touched) < n:
                    return

                count += 1
                if check_provider(word, ms, n):
                    count_found += 1
                else:
                    if len(counterexamples) < 3:
                        counterexamples.append((list(word), list(fc)))
                return

            last = word[-1]
            for nxt in [(last - 1) % n, last, (last + 1) % n]:
                word.append(nxt)
                gen(word)
                word.pop()

        for start in range(n):
            gen([start])

        print(f"  L={L}: {count} valid, {count_found} provider ({count - count_found} missing)")
        for w, fc in counterexamples:
            print(f"    CE: {w}, fc={fc}")

        total += count
        found += count_found

    print(f"\nTOTAL: {total} valid, {found} provider, {total - found} missing")


if __name__ == "__main__":
    main()
