#!/usr/bin/env python3
"""
CIC Exploration 13h: Analytical Closure Proof.

Closure requires: for all t ∈ {0,...,L-1} and all j ∈ {0,...,n-1},
  gs_eff[j](t+1) - gs_eff[j](t) = 1 if j = shadow_mover[t], 0 otherwise (mod fc[j])

where gs_eff[j](t) = g[j][σ(t)] + Δ[j](t) + offset[j].

This reduces to:
  g[j][σ(t+1)] - g[j][σ(t)] + Δ[j](t+1) - Δ[j](t) = 1_{j=mover[t]} (mod fc[j])

Since g[j][σ(t+1)] - g[j][σ(t)] = #{steps s in [σ(t), σ(t+1)) where w[s] = j},
this is a finite algebraic identity for each (t, j) pair.

This script:
1. Enumerates all consecutive (t, t+1) pairs with their Δ types
2. Verifies the closure identity for each pair analytically (as function of n)
3. Identifies which pairs require modular arithmetic
"""

import sys


def sigma_12wiggle(t, n):
    if t == 0: return n - 2
    elif t == 1: return n + 1
    elif 2 <= t <= n - 3: return n + t
    elif t == n - 2: return 2 * n
    elif t == n - 1: return n - 1
    elif t == n: return 2 * n - 2
    elif t == n + 1: return 2 * n + 1
    elif n + 2 <= t <= 2 * n - 1: return t - (n + 2)
    elif t == 2 * n: return n
    elif t == 2 * n + 1: return 2 * n - 1
    else: raise ValueError(f"t={t}")


def delta_12wiggle(t, j, n):
    if t == 0 or t == n:
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 5: return -1
        elif n - 4 <= j <= n - 1: return 0
    elif (1 <= t <= n - 3) or t == n + 1:
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 5: return -1
        elif j == n - 4: return 0
        elif j == n - 3: return -1
        elif j == n - 2: return -1
        elif j == n - 1: return 0
    elif t == n - 2:
        if j == 0: return -1
        elif j == 1: return -2
        elif j == 2: return -2
        elif 3 <= j <= n - 4: return -1
        elif j == n - 3: return -2
        elif j == n - 2: return -1
        elif j == n - 1: return 0
    elif t == n - 1:
        if j == 0: return 0
        elif j == 1: return -1
        elif j == 2: return -1
        elif 3 <= j <= n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 1
    elif t == 2 * n + 1:
        if 0 <= j <= n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 1
    elif t == 2 * n:
        if 0 <= j <= n - 4: return 1
        elif j == n - 3: return 0
        elif j == n - 2: return 1
        elif j == n - 1: return 2
    elif n + 2 <= t <= 2 * n - 1:
        if 0 <= j <= n - 5: return 1
        elif j == n - 4: return 2
        elif j == n - 3 or j == n - 2: return 1
        elif j == n - 1: return 2
    raise ValueError(f"t={t}, j={j}, n={n}")


def delta_type(t, n):
    if t == 0 or t == n: return 'A'
    elif (1 <= t <= n - 3) or t == n + 1: return 'B'
    elif t == n - 2: return 'C'
    elif t == n - 1: return 'D'
    elif t == 2 * n + 1: return 'E'
    elif t == 2 * n: return 'F'
    elif n + 2 <= t <= 2 * n - 1: return 'G'


def make_word(n):
    return [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))


def compute_waterfall(word, n):
    L = len(word)
    g = [[0] * (L + 1) for _ in range(n)]
    for t in range(L):
        for j in range(n):
            g[j][t + 1] = g[j][t]
        g[word[t]][t + 1] = g[word[t]][t] + 1
    return g


def main():
    print("CIC Exploration 13h: Analytical Closure Proof")
    print("=" * 70)

    # PART 1: Enumerate all consecutive Δ-type transitions
    print("\nPART 1: Consecutive Δ-Type Transitions")
    print("-" * 70)

    for n in [9, 11, 15]:
        w = make_word(n)
        L = len(w)
        g = compute_waterfall(w, n)

        fc = [0] * n
        for p in w:
            fc[p] += 1

        transitions = {}
        for t in range(L):
            t1 = (t + 1) % L
            type_t = delta_type(t, n)
            type_t1 = delta_type(t1, n)
            key = (type_t, type_t1)
            if key not in transitions:
                transitions[key] = []
            # Shadow mover at step t
            st = sigma_12wiggle(t, n)
            mover = w[st]
            transitions[key].append((t, mover))

        print(f"\n  n={n} (L={L}):")
        for (ta, tb), steps in sorted(transitions.items()):
            movers = [m for _, m in steps]
            print(f"    {ta}→{tb}: {len(steps)} steps, "
                  f"movers={movers}")

    # PART 2: Verify closure identity for each transition
    print("\n\nPART 2: Closure Identity Verification")
    print("-" * 70)

    for n in range(8, 20):
        w = make_word(n)
        L = len(w)
        g = compute_waterfall(w, n)

        fc = [0] * n
        for p in w:
            fc[p] += 1

        all_ok = True
        for t in range(L):
            t1 = (t + 1) % L
            st = sigma_12wiggle(t, n)
            st1 = sigma_12wiggle(t1, n)
            mover = w[st]

            for j in range(n):
                # g difference
                g_diff = g[j][st1] - g[j][st]
                # But we need to account for wraparound
                # If st1 < st, the good cycle wraps, so:
                if st1 < st:
                    g_diff = (g[j][L] - g[j][st]) + g[j][st1]
                # Actually g[j][L] = fc[j], so:
                # g_diff = fc[j] - g[j][st] + g[j][st1] if st1 < st

                # Δ difference
                d_diff = delta_12wiggle(t1, j, n) - delta_12wiggle(t, j, n)

                # Expected
                expected = 1 if j == mover else 0

                # Check
                total = g_diff + d_diff
                if total % fc[j] != expected % fc[j]:
                    all_ok = False
                    if n <= 10:
                        print(f"  n={n} t={t}→{t+1} j={j}: "
                              f"g_diff={g_diff} d_diff={d_diff} "
                              f"total={total} exp={expected} "
                              f"fc={fc[j]} FAIL")

        print(f"  n={n}: {'✓' if all_ok else '✗'}")

    # PART 3: Show which identities need mod reduction
    print("\n\nPART 3: Identities Needing Mod Reduction")
    print("-" * 70)

    for n in [9, 12]:
        w = make_word(n)
        L = len(w)
        g = compute_waterfall(w, n)

        fc = [0] * n
        for p in w:
            fc[p] += 1

        print(f"\n  n={n}:")
        for t in range(L):
            t1 = (t + 1) % L
            st = sigma_12wiggle(t, n)
            st1 = sigma_12wiggle(t1, n)
            mover = w[st]
            type_t = delta_type(t, n)
            type_t1 = delta_type(t1, n)

            for j in range(n):
                g_diff = g[j][st1] - g[j][st]
                if st1 < st:
                    g_diff = fc[j] - g[j][st] + g[j][st1]
                d_diff = (delta_12wiggle(t1, j, n)
                          - delta_12wiggle(t, j, n))
                expected = 1 if j == mover else 0
                total = g_diff + d_diff

                if total != expected:
                    # Needs mod reduction
                    print(f"    t={t}({type_t})→{t1}({type_t1}) "
                          f"j={j} mover={mover}: "
                          f"g_diff={g_diff} d_diff={d_diff} "
                          f"total={total} exp={expected} "
                          f"[mod {fc[j]}: {total % fc[j]}]")

    # PART 4: Summarize the closure proof structure
    print("\n\nPART 4: Closure Proof Summary")
    print("-" * 70)

    n = 12  # representative
    w = make_word(n)
    L = len(w)
    g = compute_waterfall(w, n)
    fc = [0] * n
    for p in w:
        fc[p] += 1

    # Enumerate distinct transition types with their algebraic identity
    seen = set()
    for t in range(L):
        t1 = (t + 1) % L
        st = sigma_12wiggle(t, n)
        st1 = sigma_12wiggle(t1, n)
        mover = w[st]
        type_t = delta_type(t, n)
        type_t1 = delta_type(t1, n)

        key = (type_t, type_t1)
        if key in seen:
            continue
        seen.add(key)

        print(f"\n  Transition {type_t}→{type_t1} "
              f"(t={t}, mover={mover}):")

        for j in range(n):
            g_diff = g[j][st1] - g[j][st]
            if st1 < st:
                g_diff = fc[j] - g[j][st] + g[j][st1]
            d_diff = (delta_12wiggle(t1, j, n)
                      - delta_12wiggle(t, j, n))
            expected = 1 if j == mover else 0
            total = g_diff + d_diff
            mod_needed = (total != expected)

            j_label = "mover" if j == mover else ""
            if mod_needed or j == mover:
                print(f"    j={j}: g_diff={g_diff:+d} "
                      f"d_diff={d_diff:+d} = {total} "
                      f"{'≡' if mod_needed else '='} "
                      f"{expected} "
                      f"{'(mod ' + str(fc[j]) + ')' if mod_needed else ''} "
                      f"{j_label}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
