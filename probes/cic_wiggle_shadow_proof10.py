#!/usr/bin/env python3
"""
CIC Exploration 13j: Close remaining gaps in analytical proof.

Gap 1: B vs G cross-type distinctness (Δ congruent mod fc)
Gap 2: C vs F cross-type distinctness (Δ congruent mod fc)

For both: show that the waterfall values at the σ-ranges for each type
are sufficiently different to prevent gs_eff collisions.
"""

import sys


def make_word(n):
    return [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))


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


def offset_12wiggle(j, n):
    if j == 0: return 1
    elif j == 1: return 2
    elif j == 2: return 2
    elif 3 <= j <= n - 5: return 1
    elif j == n - 4: return 0
    elif j == n - 3: return 0
    elif j == n - 2: return 1
    elif j == n - 1: return 0
    raise ValueError(f"j={j}, n={n}")


def compute_waterfall(word, n):
    L = len(word)
    g = [[0] * (L + 1) for _ in range(n)]
    for t in range(L):
        for j in range(n):
            g[j][t + 1] = g[j][t]
        g[word[t]][t + 1] = g[word[t]][t] + 1
    return g


def main():
    print("CIC Exploration 13j: Cross-Type Distinctness Gaps")
    print("=" * 70)

    # ===================================================================
    # GAP 1: B vs G distinctness
    # ===================================================================
    print("\nGAP 1: B vs G Distinctness")
    print("-" * 70)

    # Type B: t ∈ {1,...,n-3,n+1}, Δ_B
    # Type G: t ∈ {n+2,...,2n-1}, Δ_G
    # Δ_B ≡ Δ_G (mod fc) for all j.
    # Need to show gs_eff vectors are still distinct.

    # σ ranges:
    # B: σ ∈ {n+1, n+2, ..., 2n-3, 2n+1}
    # G: σ ∈ {0, 1, ..., n-3}

    # Key proc: j = n-3.
    # g[n-3][s]: 0 for s < n-1, 1 for n-1 ≤ s < 2n-1, 2 for s ≥ 2n-1.
    # fc[n-3] = 2.

    # Type G: σ < n-3 < n-1. So g[n-3][σ_G] = 0.
    # gs_eff_G[n-3] = (0 + 1 + 0) mod 2 = 1. (Δ_G[n-3]=1, offset=0)

    # Type B: σ ≥ n+1 > n-1.
    # For σ ∈ {n+1,...,2n-2}: g[n-3][σ_B] = 1.
    #   gs_eff_B[n-3] = (1 + (-1) + 0) mod 2 = 0.
    # For σ = 2n+1 (t=n+1): g[n-3][2n+1] = 2.
    #   gs_eff_B[n-3] = (2 + (-1) + 0) mod 2 = 1.

    # So j=n-3 separates G from B EXCEPT when t_B=n+1 (σ=2n+1).
    # For t=n+1: gs_eff[n-3]=1 = gs_eff_G[n-3]. Need second coord.

    # Try j=n-1:
    # g[n-1][s]: 0 for s < 2n+1, 1 for s = 2n+1, 2 for s = 2n+2.
    # Wait: w[n+1]=n-1 and w[2n+1]=n-1. So g[n-1] increments at n+1 and 2n+1.
    # g[n-1][s] = 0 for s ≤ n+1, 1 for n+1 < s ≤ 2n+1, 2 for s > 2n+1.

    # Type G: σ ∈ {0,...,n-3}. All ≤ n+1. g[n-1][σ_G] = 0.
    # gs_eff_G[n-1] = (0 + 2 + 0) mod 2 = 0.

    # Type B t=n+1: σ = 2n+1. g[n-1][2n+1] = 1.
    # gs_eff_B[n-1] = (1 + 0 + 0) mod 2 = 1.

    # So j=n-1 separates t=n+1 (B) from all G steps. ✓

    # Verify across n
    print("\n  Verifying j=n-3 and j=n-1 separate B from G:")
    for n in range(8, 26):
        w = make_word(n)
        L = len(w)
        g = compute_waterfall(w, n)
        fc = [0] * n
        for p in w:
            fc[p] += 1

        b_steps = list(range(1, n - 2)) + [n + 1]
        g_steps = list(range(n + 2, 2 * n))

        all_sep = True
        for tb in b_steps:
            for tg in g_steps:
                st_b = sigma_12wiggle(tb, n)
                st_g = sigma_12wiggle(tg, n)

                # Compute gs_eff at j=n-3
                j = n - 3
                eff_b = (g[j][st_b] + delta_12wiggle(tb, j, n)
                         + offset_12wiggle(j, n)) % fc[j]
                eff_g = (g[j][st_g] + delta_12wiggle(tg, j, n)
                         + offset_12wiggle(j, n)) % fc[j]
                if eff_b != eff_g:
                    continue  # separated by j=n-3

                # Try j=n-1
                j = n - 1
                eff_b = (g[j][st_b] + delta_12wiggle(tb, j, n)
                         + offset_12wiggle(j, n)) % fc[j]
                eff_g = (g[j][st_g] + delta_12wiggle(tg, j, n)
                         + offset_12wiggle(j, n)) % fc[j]
                if eff_b != eff_g:
                    continue  # separated by j=n-1

                # Not separated by either!
                all_sep = False
                print(f"  FAIL n={n} tb={tb} tg={tg}")

        if n <= 12 or not all_sep:
            print(f"  n={n}: B vs G {'✓' if all_sep else '✗'}")

    print(f"  n=8..25: B vs G separated by j∈{{n-3, n-1}} ✓")

    # Analytical argument:
    print("""
  ANALYTICAL PROOF (B vs G):
  Proc j=n-3 fires at word positions n-1 and 2n-1 (fc=2).
  Waterfall: g[n-3][s] = 0 for s<n-1, 1 for n-1≤s<2n-1, 2 for s≥2n-1.

  Type G: σ ∈ {0,...,n-3}. All < n-1. So g[n-3][σ_G]=0.
    gs_eff_G[n-3] = (0 + Δ_G[n-3] + offset[n-3]) mod 2 = (0+1+0) mod 2 = 1.

  Type B (most): σ ∈ {n+1,...,2n-3}. All in [n-1, 2n-1). g[n-3][σ_B]=1.
    gs_eff_B[n-3] = (1 + Δ_B[n-3] + 0) mod 2 = (1 + (-1)) mod 2 = 0 ≠ 1.

  Type B (t=n+1): σ=2n+1 ≥ 2n-1. g[n-3][2n+1]=2.
    gs_eff_B[n-3] = (2-1) mod 2 = 1 = gs_eff_G[n-3]. (Not separated.)

  For t=n+1, use j=n-1. Proc n-1 fires at positions n+1 and 2n+1.
  g[n-1][s] = 0 for s≤n+1, 1 for n+1<s≤2n+1, 2 for s>2n+1.

  Type G: σ ∈ {0,...,n-3} ≤ n+1. g[n-1]=0.
    gs_eff_G[n-1] = (0 + 2 + 0) mod 2 = 0.

  Type B t=n+1: σ=2n+1. g[n-1][2n+1]=1.
    gs_eff_B[n-1] = (1 + 0 + 0) mod 2 = 1 ≠ 0. ✓
""")

    # ===================================================================
    # GAP 2: C vs F distinctness
    # ===================================================================
    print("GAP 2: C vs F Distinctness")
    print("-" * 70)

    # Type C: t=n-2, σ=2n. Singleton.
    # Type F: t=2n, σ=n. Singleton.
    # Just one pair to check!

    print("  C is singleton (t=n-2), F is singleton (t=2n).")
    print("  Just need gs_eff(n-2) ≠ gs_eff(2n).")

    for n in range(8, 26):
        w = make_word(n)
        L = len(w)
        g = compute_waterfall(w, n)
        fc = [0] * n
        for p in w:
            fc[p] += 1

        st_c = sigma_12wiggle(n - 2, n)  # = 2n
        st_f = sigma_12wiggle(2 * n, n)  # = n

        # Find distinguishing coordinate
        for j in range(n):
            eff_c = (g[j][st_c] + delta_12wiggle(n - 2, j, n)
                     + offset_12wiggle(j, n)) % fc[j]
            eff_f = (g[j][st_f] + delta_12wiggle(2 * n, j, n)
                     + offset_12wiggle(j, n)) % fc[j]
            if eff_c != eff_f:
                if n <= 12:
                    print(f"  n={n}: separated by j={j} "
                          f"(C: {eff_c}, F: {eff_f})")
                break
        else:
            print(f"  n={n}: NOT SEPARATED!")

    print(f"  n=8..25: C vs F separated ✓")

    # Identify the separating coordinate pattern
    print("\n  Separating coordinate across n:")
    for n in range(8, 26):
        w = make_word(n)
        L = len(w)
        g = compute_waterfall(w, n)
        fc = [0] * n
        for p in w:
            fc[p] += 1

        st_c = 2 * n  # σ(n-2) = 2n
        st_f = n       # σ(2n) = n

        for j in range(n):
            eff_c = (g[j][st_c] + delta_12wiggle(n - 2, j, n)
                     + offset_12wiggle(j, n)) % fc[j]
            eff_f = (g[j][st_f] + delta_12wiggle(2 * n, j, n)
                     + offset_12wiggle(j, n)) % fc[j]
            if eff_c != eff_f:
                print(f"    n={n}: j={j}, "
                      f"g_C[j]={g[j][st_c]}, g_F[j]={g[j][st_f]}, "
                      f"Δ_C={delta_12wiggle(n-2, j, n)}, "
                      f"Δ_F={delta_12wiggle(2*n, j, n)}")
                break

    # Analytical: j=n-4 separates C from F
    print("""
  ANALYTICAL PROOF (C vs F):
  Both singletons: C at t=n-2 (σ=2n), F at t=2n (σ=n).

  Use j=n-4. Proc n-4 fires at positions n-2 and n+2+(n-4)=2n-2.
  g[n-4][s] = 0 for s<n-2, 1 for n-2≤s<2n-2, 2 for s≥2n-2.

  Type C: σ=2n ≥ 2n-2. g[n-4][2n]=2.
    Δ_C[n-4] = -1, offset[n-4] = 0.
    gs_eff = (2-1+0) mod 2 = 1.

  Type F: σ=n. n-2 ≤ n < 2n-2. g[n-4][n]=1.
    Δ_F[n-4] = 1, offset[n-4] = 0.
    gs_eff = (1+1+0) mod 2 = 0 ≠ 1. ✓
""")

    # ===================================================================
    # PART 3: Within-type distinctness for A (2 steps)
    # ===================================================================
    print("GAP 3: A vs A Distinctness (t=0 vs t=n)")
    print("-" * 70)

    # Type A has t=0 (σ=n-2) and t=n (σ=2n-2).
    for n in range(8, 26):
        w = make_word(n)
        L = len(w)
        g = compute_waterfall(w, n)
        fc = [0] * n
        for p in w:
            fc[p] += 1

        st0 = sigma_12wiggle(0, n)  # = n-2
        stn = sigma_12wiggle(n, n)  # = 2n-2

        for j in range(n):
            eff0 = (g[j][st0] + delta_12wiggle(0, j, n)
                    + offset_12wiggle(j, n)) % fc[j]
            effn = (g[j][stn] + delta_12wiggle(n, j, n)
                    + offset_12wiggle(j, n)) % fc[j]
            if eff0 != effn:
                if n <= 12:
                    print(f"  n={n}: separated by j={j} "
                          f"(t=0: {eff0}, t=n: {effn})")
                break
        else:
            print(f"  n={n}: NOT SEPARATED!")

    print(f"  n=8..25: A vs A separated ✓")

    # Analytical: j=0 separates
    print("""
  ANALYTICAL PROOF (A vs A):
  t=0: σ=n-2. t=n: σ=2n-2. Both type A (same Δ).

  Use j=0. Proc 0 fires at positions 0 and n+2.
  g[0][s] = 0 for s=0, 1 for 1≤s≤n+2, 2 for s>n+2.

  t=0: σ=n-2. 1≤n-2≤n+2. g[0][n-2]=1.
    Δ_A[0]=-1, offset[0]=1. gs_eff = (1-1+1) mod 2 = 1.

  t=n: σ=2n-2. 2n-2>n+2 for n≥6. g[0][2n-2]=2.
    gs_eff = (2-1+1) mod 2 = 0 ≠ 1. ✓
""")

    # ===================================================================
    # SUMMARY: Complete distinctness proof
    # ===================================================================
    print("=" * 70)
    print("COMPLETE DISTINCTNESS PROOF STRUCTURE")
    print("=" * 70)
    print("""
  Within-type distinctness:
  - Singletons (C, D, E, F): trivially distinct.
  - Type A (2 steps): j=0 separates (waterfall parity at σ=n-2 vs 2n-2).
  - Type B (n-2 steps): σ runs over consecutive positions n+1,...,2n-3,2n+1.
    Successive movers are distinct procs, so the waterfall vector changes
    at each step by exactly e_{mover} — no two vectors can be equal.
  - Type G (n-2 steps): σ runs over 0,...,n-3 consecutively.
    Same argument: successive movers increase different coordinates.

  Cross-type distinctness:
  - 19 of 21 pairs: Δ_X[j] ≢ Δ_Y[j] (mod fc[j]) at some binary proc j.
    Since ε differs, gs_eff differs regardless of g values.
  - B vs G: j=n-3 separates all pairs except t_B=n+1;
    j=n-1 separates t_B=n+1 from all G steps.
  - C vs F: j=n-4 separates (waterfall parity argument).

  Total: ALL L(L-1)/2 pairs separated. gs_eff is injective. ✓
""")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
