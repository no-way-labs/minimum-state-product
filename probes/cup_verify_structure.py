#!/usr/bin/env python3
"""CUP: Extract and verify the good cycle structure of Sol 3 v1 for ms=(2,3,...,3).

For each n from 3 to 13, compute:
  - Good cycle configs and mover sequence
  - Verify all 5 properties
  - Extract config structure (state values at each position)
  - Identify the bounce pattern
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system


def sol3_v1(ms, n):
    """Sol 3 v1 adaptation: replace K with m_i."""
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f

    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f

    def make_middle(m_i):
        def f(L, S, R):
            new_L = L % m_i
            new_R = R % m_i
            if (S + 1) % m_i == new_L:
                return new_L
            if (S + 1) % m_i == new_R:
                return new_R
            return S
        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def privileged_set(config, fs, ms):
    n = len(ms)
    priv = []
    for i in range(n):
        L = config[(i - 1) % n]
        S = config[i]
        R = config[(i + 1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv


def apply_move(config, i, fs, ms):
    n = len(ms)
    L = config[(i - 1) % n]
    S = config[i]
    R = config[(i + 1) % n]
    new_s = fs[i](L, S, R)
    lst = list(config)
    lst[i] = new_s
    return tuple(lst)


def extract_cycle(n):
    """Extract the good cycle for ms=(2,3,...,3) with n processors."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1(ms, n)

    # Verify
    result = verify_system(ms, fs)
    if not result.get('valid'):
        print(f"  n={n}: INVALID! {result.get('properties', {})}")
        return None

    cycle = result['cycle']
    cycle_len = result['cycle_length']
    good_count = len(result['good_configs'])

    # Extract mover sequence
    movers = []
    for c in cycle:
        priv = privileged_set(c, fs, ms)
        assert len(priv) == 1
        movers.append(priv[0])

    print(f"n={n}: VALID, product={2*3**(n-1)}, cycle_len={cycle_len}, "
          f"good={good_count}, expected_cycle={3*n-2}, expected_good={8*n-10}")

    # Print mover sequence
    print(f"  Movers: {movers}")

    # Print configs
    if n <= 6:
        print(f"  Cycle configs:")
        for step, c in enumerate(cycle):
            priv = privileged_set(c, fs, ms)
            mover = priv[0]
            next_c = apply_move(c, mover, fs, ms)
            print(f"    step {step:2d}: {c} -> P{mover} moves -> {next_c}")

    # Analyze the bounce pattern
    # Check: is the mover sequence [n-1, n-2, ..., 1, 0, 1, ..., n-1]?
    expected_bounce = list(range(n-1, -1, -1)) + list(range(1, n))  # length 2n-1
    # But cycle_len = 3n-2, so there might be a different pattern

    # Let me check what the actual pattern is
    # Look for repeating structure
    down_sweep = list(range(n-1, -1, -1))  # [n-1, n-2, ..., 0]
    up_sweep = list(range(1, n))            # [1, 2, ..., n-1]

    # Check if movers start with down then up
    if movers[:n] == down_sweep:
        print(f"  Pattern starts with full down-sweep [n-1..0]")
        remaining = movers[n:]
        if remaining == up_sweep[:len(remaining)]:
            print(f"  Followed by up-sweep [1..{n-1}]")
            if len(movers) == 2*n - 1:
                print(f"  Full bounce: down + up = {2*n-1} moves")
    else:
        # Check for partial patterns
        # Find where each sweep starts/ends
        direction_changes = []
        for i in range(1, len(movers)):
            if movers[i] > movers[i-1]:
                if i == 1 or movers[i-1] <= movers[i-2]:
                    pass  # continuing up
                else:
                    direction_changes.append(('up', i))
            elif movers[i] < movers[i-1]:
                if i == 1 or movers[i-1] >= movers[i-2]:
                    pass  # continuing down
                else:
                    direction_changes.append(('down', i))

    # Check specific bottom rule behavior
    # P_0 has m=2: (S+1)%2 == R%2 → 1-S == R%2
    # When S=0: privileged if R%2 = 1, i.e., R=1
    # When S=1: privileged if R%2 = 0, i.e., R ∈ {0, 2}
    # Output: (S-1)%2 = 1-S (toggle)

    # Track P_0 state through cycle
    p0_states = [c[0] for c in cycle]
    if n <= 10:
        print(f"  P0 states: {p0_states}")
        # Track P_{n-1} states
        pn_states = [c[n-1] for c in cycle]
        print(f"  P{n-1} states: {pn_states}")

    return {
        'n': n,
        'cycle': cycle,
        'movers': movers,
        'cycle_len': cycle_len,
        'good_count': good_count,
    }


def analyze_privilege_structure(n):
    """For each config in the cycle, show L, S, R and which rule fires."""
    ms = [2] + [3] * (n - 1)
    fs = sol3_v1(ms, n)
    result = verify_system(ms, fs)
    if not result.get('valid'):
        return

    cycle = result['cycle']
    print(f"\n{'='*70}")
    print(f"PRIVILEGE ANALYSIS for n={n}")
    print(f"{'='*70}")

    for step, c in enumerate(cycle):
        priv = privileged_set(c, fs, ms)
        mover = priv[0]
        i = mover
        L = c[(i - 1) % n]
        S = c[i]
        R = c[(i + 1) % n]
        new_S = fs[i](L, S, R)

        if i == 0:
            rule = "BOTTOM"
            detail = f"(S+1)%2={1-S}==R%2={R%2}"
        elif i == n - 1:
            rule = "TOP"
            detail = f"L%3={L%3}==R%3={R%3}, (L%3+1)%3={(L%3+1)%3}!=S={S}"
        else:
            rule = "MIDDLE"
            if (S + 1) % 3 == L % 3:
                detail = f"(S+1)%3={(S+1)%3}==L={L} → copy L"
            elif (S + 1) % 3 == R % 3:
                detail = f"(S+1)%3={(S+1)%3}==R={R} → copy R"
            else:
                detail = "???"

        print(f"  step {step:2d}: {list(c)} P{mover}({rule}): "
              f"L={L} S={S} R={R} → S'={new_S}  [{detail}]")


def check_formulas(max_n=13):
    """Verify cycle_len = 3n-2 and good_count = 8n-10 for n=3..max_n."""
    print("="*70)
    print("FORMULA VERIFICATION")
    print("="*70)
    all_ok = True
    for n in range(3, max_n + 1):
        ms = [2] + [3] * (n - 1)
        fs = sol3_v1(ms, n)
        result = verify_system(ms, fs)
        if not result.get('valid'):
            print(f"  n={n}: INVALID")
            all_ok = False
            continue
        cl = result['cycle_length']
        gc = len(result['good_configs'])
        exp_cl = 3 * n - 2
        exp_gc = 8 * n - 10
        ok_cl = cl == exp_cl
        ok_gc = gc == exp_gc
        status = "OK" if (ok_cl and ok_gc) else "MISMATCH"
        print(f"  n={n}: cycle={cl} (exp {exp_cl}) {'✓' if ok_cl else '✗'}, "
              f"good={gc} (exp {exp_gc}) {'✓' if ok_gc else '✗'}  [{status}]")
        if not (ok_cl and ok_gc):
            all_ok = False
    print(f"\nAll formulas match: {all_ok}")
    return all_ok


if __name__ == "__main__":
    # First verify formulas
    check_formulas(13)

    print("\n" + "="*70)
    print("CYCLE STRUCTURE EXTRACTION")
    print("="*70)

    results = {}
    for n in range(3, 8):
        r = extract_cycle(n)
        if r:
            results[n] = r

    # Detailed privilege analysis for small n
    analyze_privilege_structure(3)
    analyze_privilege_structure(4)
    analyze_privilege_structure(5)
