#!/usr/bin/env python3
"""
§9.1' CUP-2 Cycle Existence: Extract cycle configs and identify
the closed-form pattern for all n.

The CUP-2 system: ms = (2, 3, ..., 3, 2), product = 4·3^(n-2).
5 n-independent tables (T_bot, T_low, T_mid, T_high, T_top).
Goal: prove cycle of length 3n-2 exists for all n ≥ 4.
"""

import sys
from itertools import product as iproduct


# ── The 5 CUP-2 tables ──

T_bot = {  # P_0 (binary, L=2, S=2, R=3)
    (0,0,0):1, (0,0,1):1, (0,0,2):0,
    (0,1,0):1, (0,1,1):1, (0,1,2):1,
    (1,0,0):0, (1,0,1):1, (1,0,2):0,
    (1,1,0):0, (1,1,1):1, (1,1,2):0,
}

T_low = {  # P_1 (ternary, L=2, S=3, R=3)
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):0, (0,1,1):1, (0,1,2):0,
    (0,2,0):0, (0,2,1):2, (0,2,2):0,
    (1,0,0):1, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):2,
    (1,2,0):0, (1,2,1):1, (1,2,2):2,
}

T_mid = {  # P_i for 2 ≤ i ≤ n-3 (ternary, L=3, S=3, R=3)
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):0, (0,1,1):1, (0,1,2):0,
    (0,2,0):0, (0,2,1):2, (0,2,2):0,
    (1,0,0):1, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):2,
    (1,2,0):0, (1,2,1):1, (1,2,2):2,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):0, (2,1,2):2,
    (2,2,0):0, (2,2,1):2, (2,2,2):2,
}

T_high = {  # P_{n-2} (ternary, L=3, S=3, R=2)
    (0,0,0):0, (0,0,1):0,
    (0,1,0):0, (0,1,1):0,
    (0,2,0):0, (0,2,1):0,
    (1,0,0):1, (1,0,1):1,
    (1,1,0):1, (1,1,1):2,
    (1,2,0):0, (1,2,1):2,
    (2,0,0):0, (2,0,1):2,
    (2,1,0):0, (2,1,1):2,
    (2,2,0):2, (2,2,1):2,
}

T_top = {  # P_{n-1} (binary, L=3, S=2, R=2)
    (0,0,0):0, (0,0,1):0,
    (0,1,0):0, (0,1,1):0,
    (1,0,0):0, (1,0,1):1,
    (1,1,0):1, (1,1,1):1,
    (2,0,0):1, (2,0,1):1,
    (2,1,0):1, (2,1,1):1,
}


def get_table(pos, n):
    if pos == 0: return T_bot
    elif pos == 1: return T_low
    elif pos == n - 2: return T_high
    elif pos == n - 1: return T_top
    else: return T_mid


def ms(pos, n):
    if pos == 0 or pos == n - 1: return 2
    return 3


def apply_rules(config, n):
    """Find privileged processor and apply its rule. Return (new_config, mover)."""
    c = list(config)
    # Find privileged: processor whose table output differs from current state
    priv = []
    for p in range(n):
        L = c[(p - 1) % n]
        S = c[p]
        R = c[(p + 1) % n]
        table = get_table(p, n)
        new_val = table[(L, S, R)]
        if new_val != S:
            priv.append(p)

    if len(priv) != 1:
        return None, priv  # not exactly 1 privileged

    p = priv[0]
    L = c[(p - 1) % n]
    S = c[p]
    R = c[(p + 1) % n]
    table = get_table(p, n)
    c[p] = table[(L, S, R)]
    return tuple(c), p


def find_cycle(n):
    """Find the good cycle starting from all-zeros config."""
    start = tuple([0] * n)
    config = start
    path = [config]
    movers = []

    for step in range(5 * n):
        result, mover = apply_rules(config, n)
        if result is None:
            return None, None, f"step {step}: {len(mover)} privileged"
        movers.append(mover)
        config = result
        if config == start and step > 0:
            return path, movers, "OK"
        path.append(config)

    return None, None, "did not close"


def main():
    print("§9.1' CUP-2 Cycle Existence")
    print("=" * 70)

    # PART 1: Extract cycles for n=4..12
    print("\nPART 1: Cycle Extraction")
    print("-" * 70)

    all_cycles = {}
    for n in range(4, 13):
        path, movers, status = find_cycle(n)
        if status != "OK":
            print(f"  n={n}: FAILED ({status})")
            continue

        cycle_len = len(movers)
        print(f"  n={n}: cycle length = {cycle_len} = 3·{n}-2 = {3*n-2} "
              f"{'✓' if cycle_len == 3*n-2 else '✗'}")
        all_cycles[n] = (path, movers)

        if n <= 7:
            print(f"    Movers: {movers}")
            for i, c in enumerate(path):
                m = movers[i] if i < len(movers) else '-'
                print(f"    [{i:2d}] {list(c)} → P{m}")

    # PART 2: Mover pattern
    print("\n\nPART 2: Mover Word Pattern")
    print("-" * 70)

    for n in range(4, 13):
        if n not in all_cycles:
            continue
        _, movers = all_cycles[n]
        print(f"  n={n}: {movers}")

    # Identify pattern: should be [0, 1, 2, ..., n-1, n-2, ..., 1, ...]
    print("\n  Pattern analysis:")
    for n in range(5, 10):
        _, movers = all_cycles[n]
        # Check: first n movers are 0,1,...,n-1 (sweep up)
        up = movers[:n]
        # Next n-2 movers are n-2,...,1 (sweep down)
        down = movers[n:2*n-2]
        print(f"  n={n}: up={up} down={down} remaining={movers[2*n-2:]}")

    # PART 3: Config pattern analysis
    print("\n\nPART 3: Config Pattern — Wavefront Structure")
    print("-" * 70)

    # For each cycle step, show the config as a "wavefront"
    for n in [5, 6, 7]:
        path, movers = all_cycles[n]
        print(f"\n  n={n} (cycle length {len(movers)}):")
        print(f"  {'step':>4} {'mover':>5} {'config':>30} {'pattern':>15}")
        for i in range(len(movers)):
            c = path[i]
            m = movers[i]
            # Identify pattern: count of 0s, 1s, 2s
            counts = [0, 0, 0]
            for v in c:
                counts[v] += 1
            pat = f"({counts[0]}×0,{counts[1]}×1,{counts[2]}×2)"
            print(f"  {i:>4} P{m:>4} {str(list(c)):>30} {pat:>15}")

    # PART 4: Closed-form config formula
    print("\n\nPART 4: Closed-Form Config Identification")
    print("-" * 70)

    # Hypothesis: configs have a "staircase" structure
    # where a front of 1s sweeps up, then a front of 2s sweeps up
    for n in [7, 8, 9]:
        path, movers = all_cycles[n]
        print(f"\n  n={n}:")

        for i in range(len(movers)):
            c = path[i]
            m = movers[i]

            # Find the "front" positions
            # Count consecutive leading values
            front1 = 0  # number of initial non-zero positions
            front2 = 0  # number of positions with value 2

            # Better: find the pattern as (prefix of higher values)
            # Let's track where the transitions happen
            transitions = []
            for j in range(n - 1):
                if c[j] != c[j + 1]:
                    transitions.append((j, c[j], c[j+1]))

            # Simpler: show as a compact string
            s = ''.join(str(v) for v in c)
            print(f"  [{i:2d}] {s} P{m}")

    # PART 5: Exact mover word identification
    print("\n\nPART 5: Mover Word Closed Form")
    print("-" * 70)

    for n in range(4, 13):
        if n not in all_cycles:
            continue
        _, movers = all_cycles[n]

        # Check if movers = [0,1,...,n-1, n-2,...,1, n-2,...,1]
        # = up(0..n-1) + down(n-2..1) + down(n-2..1)
        expected = list(range(n)) + list(range(n-2, 0, -1)) + list(range(n-2, 0, -1))
        # Length: n + (n-2) + (n-2) = 3n-4... that's too short

        # Try: up(0..n-1) + down(n-2..2) + up(2..n-1) + down(n-2..2) ...
        # Actually let me just check structure
        up = list(range(n))
        down = list(range(n-2, 0, -1))

        # Check segments
        if movers[:n] == up:
            rest = movers[n:]
            if rest == down:
                print(f"  n={n}: UP + DOWN = [0..{n-1}] + [{n-2}..1]")
            elif len(rest) >= n-2 and rest[:n-2] == down:
                rest2 = rest[n-2:]
                print(f"  n={n}: UP + DOWN + {rest2}")
            else:
                print(f"  n={n}: UP + ?{rest}")
        else:
            print(f"  n={n}: not simple UP start")

    # PART 6: Direct successor verification
    print("\n\nPART 6: Successor Verification by Position Class")
    print("-" * 70)

    # For each cycle step, identify which position class the mover is in
    # and what (L, S, R) → new_S transition occurs
    for n in [6, 8]:
        path, movers = all_cycles[n]
        print(f"\n  n={n}:")
        for i in range(len(movers)):
            c = path[i]
            m = movers[i]
            L = c[(m - 1) % n]
            S = c[m]
            R = c[(m + 1) % n]
            table = get_table(m, n)
            new_S = table[(L, S, R)]

            if m == 0: pclass = "bot"
            elif m == 1: pclass = "low"
            elif m == n - 2: pclass = "high"
            elif m == n - 1: pclass = "top"
            else: pclass = "mid"

            print(f"    [{i:2d}] P{m}({pclass:>4}): "
                  f"({L},{S},{R})→{new_S}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
