"""
Analyze counter-examples in detail.

CE: [1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2], fc=[2, 3, 2, 3, 2], n=5, ms=[2,3,2,3,2]

The issue: maybe the provider definition is too restrictive.
The active side must be binary with EVEN fire count >= 2.
But what if the active side is TERNARY with fire count being a multiple of 3?

Let me check: what if we generalize the provider to allow any proc
on the active side whose fire count is a multiple of m_p?
"""
import sys
sys.path.insert(0, './claude')


def check_provider_generalized(word, ms, n):
    """Generalized provider: active side fire count is multiple of m_p (not just binary even)."""
    L = len(word)

    fire_steps = {}
    for p in range(n):
        fire_steps[p] = []
    for i, m in enumerate(word):
        fire_steps[m].append(i)

    for t in range(n):
        fsteps = fire_steps[t]
        for s in fsteps:
            prev_fire = -1
            for k in range(s - 1, -1, -1):
                if word[k] == t:
                    prev_fire = k
                    break

            left_t = (t - 1) % n
            right_t = (t + 1) % n

            left_acc = 0
            right_acc = 0

            for a in range(s - 1, prev_fire, -1):
                if word[a] == t:
                    continue
                if word[a] == left_t:
                    left_acc += 1
                elif word[a] == right_t:
                    right_acc += 1

                lf = left_acc
                rf = right_acc

                # Original: binary active with even fires
                if lf == 0 and ms[right_t] == 2 and rf >= 2 and rf % 2 == 0:
                    return True, "original_binary"
                if rf == 0 and ms[left_t] == 2 and lf >= 2 and lf % 2 == 0:
                    return True, "original_binary"

                # Generalized: active side fire count is multiple of m_p
                if lf == 0 and rf >= ms[right_t] and rf % ms[right_t] == 0:
                    return True, f"generalized: right={right_t}, m={ms[right_t]}, fires={rf}"
                if rf == 0 and lf >= ms[left_t] and lf % ms[left_t] == 0:
                    return True, f"generalized: left={left_t}, m={ms[left_t]}, fires={lf}"

    return False, None


def analyze_ce(word, ms, n):
    """Detailed analysis of a counter-example."""
    L = len(word)
    print(f"\n=== CE Analysis: word={word} ===")
    print(f"n={n}, ms={ms}, L={L}")

    fc = [0] * n
    fire_steps = {p: [] for p in range(n)}
    for i, m in enumerate(word):
        fc[m] += 1
        fire_steps[m].append(i)
    print(f"fc={fc}")
    print(f"fire_steps={dict(fire_steps)}")

    # Walk directions
    print("\nWalk steps:")
    for i in range(L):
        nxt = word[(i + 1) % L]
        curr = word[i]
        diff = (nxt - curr) % n
        if diff == 1:
            d = "CW"
        elif diff == n - 1:
            d = "CCW"
        elif diff == 0:
            d = "STAY"
        else:
            d = f"JUMP({diff})"
        print(f"  Step {i}: mover={curr} -> {nxt} ({d})")

    # Check all phases
    print("\nAll phases with silent side:")
    for t in range(n):
        fsteps = fire_steps[t]
        for s in fsteps:
            prev_fire = -1
            for k in range(s - 1, -1, -1):
                if word[k] == t:
                    prev_fire = k
                    break

            left_t = (t - 1) % n
            right_t = (t + 1) % n
            left_acc = 0
            right_acc = 0

            for a in range(s - 1, prev_fire, -1):
                if word[a] == t:
                    continue
                if word[a] == left_t:
                    left_acc += 1
                elif word[a] == right_t:
                    right_acc += 1
                lf = left_acc
                rf = right_acc

                has_silent = (lf == 0 or rf == 0)
                if has_silent and (lf >= 1 or rf >= 1):
                    silent = "L" if lf == 0 else "R"
                    active_p = right_t if lf == 0 else left_t
                    active_fires = rf if lf == 0 else lf
                    m_active = ms[active_p]
                    mult = "YES" if active_fires % m_active == 0 else "NO"
                    binary_even = "YES" if m_active == 2 and active_fires % 2 == 0 else "NO"
                    print(f"  t={t}, a={a}, s={s}: {silent}_silent, active={active_p}(m={m_active}), fires={active_fires}, mult_of_m={mult}, binary_even={binary_even}")

    # Check generalized
    found, reason = check_provider_generalized(word, ms, n)
    print(f"\nGeneralized provider: {found} ({reason})")


def main():
    n = 5
    ms = [2, 3, 2, 3, 2]

    ces = [
        [1, 0, 1, 0, 1, 2, 3, 4, 3, 4, 3, 2],
        [3, 4, 3, 4, 3, 2, 1, 0, 1, 0, 1, 2],
    ]

    for ce in ces:
        analyze_ce(ce, ms, n)

    # Now run comprehensive check with generalized provider
    print("\n\n=== Comprehensive check with GENERALIZED provider ===")
    total = 0
    found_orig = 0
    found_gen = 0
    missing = 0
    ces_gen = []

    for L in range(2 * n + 1, 2 * n + 6):
        def gen(word):
            nonlocal total, found_orig, found_gen, missing, ces_gen
            if len(word) == L:
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

                total += 1
                f, reason = check_provider_generalized(word, ms, n)
                if f:
                    found_gen += 1
                    if "original" in reason:
                        found_orig += 1
                else:
                    missing += 1
                    if len(ces_gen) < 3:
                        ces_gen.append((list(word), list(fc)))
                return

            last = word[-1]
            for nxt in [(last - 1) % n, last, (last + 1) % n]:
                word.append(nxt)
                gen(word)
                word.pop()

        for start in range(n):
            gen([start])

    print(f"Total: {total}")
    print(f"Original binary provider: {found_orig}")
    print(f"Generalized provider: {found_gen}")
    print(f"Missing: {missing}")
    for w, fc in ces_gen:
        print(f"  CE: {w}, fc={fc}")


if __name__ == "__main__":
    main()
