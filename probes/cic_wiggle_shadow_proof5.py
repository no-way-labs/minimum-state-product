#!/usr/bin/env python3
"""
CIC Exploration 13e: Shadow Offset Consistency.

Key insight: shadow[t][j] = ss[j][(offset[j] + gs[j][t]) mod fc[j]]
where gs[j][t] = g[j][σ(t)] + Δ[j](t).

For the mover entry to apply at step t, we need the context to match:
shadow[t][j] = good[σ(t)][j] for j in {mover-1, mover, mover+1}

This requires: (offset[j] + Δ[j](t)) mod fc[j] = 0 for those j.
I.e., offset[j] = -Δ[j](t) mod fc[j].

QUESTION: Is -Δ[j](t) mod fc[j] constant across all t where j is in the context?
If YES → shadow cycle exists by construction.
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


def main():
    print("CIC Exploration 13e: Shadow Offset Consistency")
    print("=" * 70)

    # For the canonical {1,2}-wiggle word:
    # w = [0, 1, 2, 1, 2, 3, 4, ..., n-1, 0, 1, 2, 3, 4, ..., n-1]
    # w[t] is the mover at good step t.
    # Shadow step t uses entry from good step σ(t), so mover = w[σ(t)].
    # Context positions: {w[σ(t)]-1, w[σ(t)], w[σ(t)]+1} mod n.
    # Need: offset[j] = -Δ[j](t) mod fc[j] for these three positions.

    for n in range(8, 26):
        w = [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))
        L = len(w)

        # Fire counts
        fc = [0] * n
        for p in w:
            fc[p] += 1

        # For each j, collect all -Δ[j](t) mod fc[j] values
        # across all t where j is in the mover context
        required_offset = {}  # j -> set of required offset values
        for j in range(n):
            required_offset[j] = set()

        for t in range(L):
            st = sigma_12wiggle(t, n)
            mover = w[st]
            context_procs = [(mover - 1) % n, mover, (mover + 1) % n]
            for j in context_procs:
                d = delta_12wiggle(t, j, n)
                req = (-d) % fc[j]
                required_offset[j].add(req)

        # Check consistency
        consistent = True
        for j in range(n):
            if len(required_offset[j]) > 1:
                consistent = False

        if consistent:
            offsets = [list(required_offset[j])[0] if required_offset[j]
                       else 0 for j in range(n)]
            print(f"  n={n}: CONSISTENT ✓  offsets={offsets}")
        else:
            print(f"  n={n}: INCONSISTENT ✗")
            for j in range(n):
                if len(required_offset[j]) > 1:
                    print(f"    j={j} fc={fc[j]}: "
                          f"required offsets = {required_offset[j]}")

    # PART 2: Detailed analysis at n=9
    print("\n\nPART 2: Detailed Offset Analysis (n=9)")
    print("-" * 70)

    n = 9
    w = [0, 1, 2, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5, 6, 7, 8]
    L = len(w)
    fc = [0] * n
    for p in w:
        fc[p] += 1

    print(f"  Fire counts: {fc}")
    print(f"  Word: {w}")
    print()

    for t in range(L):
        st = sigma_12wiggle(t, n)
        mover = w[st]
        context = [(mover - 1) % n, mover, (mover + 1) % n]
        deltas = [delta_12wiggle(t, j, n) for j in context]
        offsets = [(-d) % fc[j] for d, j in zip(deltas, context)]
        print(f"  t={t:2d} σ={st:2d} mover={mover} "
              f"ctx={context} Δ={deltas} -Δ mod fc={offsets}")

    # PART 3: What offset values arise?
    print("\n\nPART 3: Offset Pattern Across n")
    print("-" * 70)

    for n in range(8, 16):
        w = [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))
        L = len(w)
        fc = [0] * n
        for p in w:
            fc[p] += 1

        offsets = []
        for j in range(n):
            vals = set()
            for t in range(L):
                st = sigma_12wiggle(t, n)
                mover = w[st]
                ctx = [(mover - 1) % n, mover, (mover + 1) % n]
                if j in ctx:
                    d = delta_12wiggle(t, j, n)
                    vals.add((-d) % fc[j])
            assert len(vals) == 1
            offsets.append(list(vals)[0])

        print(f"  n={n}: offsets = {offsets}  fc = {fc}")

    # PART 4: Does offset depend on binary placement?
    print("\n\nPART 4: Offset = f(fc, Δ types)")
    print("-" * 70)

    # The offset[j] = -Δ[j](t) mod fc[j] for any t where j is in context.
    # For the canonical word, the offsets are fixed.
    # This means: shadow[t][j] = good[σ(t)][j] whenever j is in the context.
    # The shadow config MATCHES the good config at the context positions!
    # This is necessary for the mover entry to apply.
    # At non-context positions, the shadow can differ.

    # What is the shadow state at non-context positions?
    # shadow[t][j] = ss[j][(offset[j] + g[j][σ(t)] + Δ[j](t)) mod fc[j]]
    # = ss[j][(g[j][σ(t)] + Δ[j](t) + offset[j]) mod fc[j]]
    # For context j: offset[j] + Δ[j](t) ≡ 0 (mod fc[j])
    #   → shadow[t][j] = ss[j][g[j][σ(t)]] = good[σ(t)][j]
    # For non-context j: offset[j] + Δ[j](t) may ≠ 0 (mod fc[j])
    #   → shadow[t][j] = ss[j][(g[j][σ(t)] + (offset[j]+Δ[j](t)) mod fc[j])

    # Let ε[j](t) = (offset[j] + Δ[j](t)) mod fc[j]
    # ε[j](t) = 0 iff j is in context at step t
    # ε[j](t) ≠ 0 otherwise — this is the "shadow shift" at non-context positions

    for n in [9, 11]:
        w = [0, 1, 2, 1, 2] + list(range(3, n)) + list(range(n))
        L = len(w)
        fc = [0] * n
        for p in w:
            fc[p] += 1

        # Compute offsets
        offsets = []
        for j in range(n):
            vals = set()
            for t in range(L):
                st = sigma_12wiggle(t, n)
                mover = w[st]
                ctx = [(mover - 1) % n, mover, (mover + 1) % n]
                if j in ctx:
                    d = delta_12wiggle(t, j, n)
                    vals.add((-d) % fc[j])
            offsets.append(list(vals)[0])

        print(f"\n  n={n} offsets={offsets}")
        print(f"  ε[j](t) = (offset[j] + Δ[j](t)) mod fc[j]:")
        print(f"  {'t':>3}", end="")
        for j in range(n):
            print(f"  ε[{j}]", end="")
        print(f"  mover  ctx")

        for t in range(L):
            st = sigma_12wiggle(t, n)
            mover = w[st]
            ctx = [(mover - 1) % n, mover, (mover + 1) % n]
            print(f"  {t:3d}", end="")
            for j in range(n):
                d = delta_12wiggle(t, j, n)
                eps = (offsets[j] + d) % fc[j]
                marker = "*" if j in ctx else " "
                print(f"  {eps:3d}{marker}", end="")
            print(f"  {mover:5d}  {ctx}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
