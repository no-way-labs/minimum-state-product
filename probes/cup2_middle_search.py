#!/usr/bin/env python3
"""Search over middle rule variants + binary endpoint exhaustive search.

For the middle ternary processors, try parameterized rule families.
For binary endpoints, do exhaustive search over bounce-compatible functions.
"""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system


def build_bounce_cycle(ms, n):
    up_down = list(range(n)) + list(range(n - 2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * (3 * n)
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            return cycle, full[:step + 1]
        if nc in visited:
            raise RuntimeError(f"Revisited {nc}")
        visited.add(nc)
        cycle.append(nc)
    raise RuntimeError("Cycle didn't close")


def get_determined(cycle, movers, ms, n):
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p - 1) % n]
            S = c[p]
            R = c[(p + 1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S
    return det


# Middle rule families
def sol3_middle(L, S, R, m=3):
    if (S + 1) % m == L % m:
        return L % m
    if (S + 1) % m == R % m:
        return R % m
    return S

def sol3_plus_top(L, S, R, m=3):
    """Sol3 middle + Sol3 top condition."""
    if (S + 1) % m == L % m:
        return L % m
    if (S + 1) % m == R % m:
        return R % m
    if L % m == R % m and (L % m + 1) % m != S:
        return (L % m + 1) % m
    return S

def sol3_plus_agree(L, S, R, m=3):
    """Sol3 middle + if L=R and S≠L, copy L."""
    if (S + 1) % m == L % m:
        return L % m
    if (S + 1) % m == R % m:
        return R % m
    if L % m == R % m and S != L % m:
        return L % m
    return S

def sol1_other(L, S, R, m=3):
    """Sol 1 other: if L≠S, copy L."""
    if L % m != S:
        return L % m
    return S

def sol3_reversed(L, S, R, m=3):
    """Sol3 with reversed priority: check R first."""
    if (S + 1) % m == R % m:
        return R % m
    if (S + 1) % m == L % m:
        return L % m
    return S

def sol3_minus1(L, S, R, m=3):
    """Sol3 with S-1 instead of S+1."""
    if (S - 1) % m == L % m:
        return L % m
    if (S - 1) % m == R % m:
        return R % m
    return S

def sol3_copy_L(L, S, R, m=3):
    """If L≠S and (S+1)%3=L, copy L. If R≠S and (S+1)%3=R, copy R.
    Also: if L=R≠S, copy L."""
    if (S + 1) % m == L % m:
        return L % m
    if (S + 1) % m == R % m:
        return R % m
    if L == R and S != L:
        return L
    return S

def majority(L, S, R, m=3):
    """If two of {L%m, S, R%m} agree, go with majority. Else stay."""
    lm = L % m
    rm = R % m
    if lm == S:
        return S
    if rm == S:
        return S
    if lm == rm:
        return lm
    return S


MIDDLE_RULES = {
    "sol3": sol3_middle,
    "sol3+top": sol3_plus_top,
    "sol3+agree": sol3_plus_agree,
    "sol1_other": sol1_other,
    "sol3_rev": sol3_reversed,
    "sol3_m1": sol3_minus1,
    "sol3_copyL": sol3_copy_L,
    "majority": majority,
}


def check_middle_compatible(rule_fn, det, n, ms):
    """Check if a middle rule is compatible with determined entries."""
    for p in range(1, n - 1):
        m_L = ms[(p - 1) % n]
        m_S = ms[p]
        m_R = ms[(p + 1) % n]
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key in det:
                        actual = rule_fn(L, S, R, m_S)
                        if actual != det[key]:
                            return False, p, (L, S, R), det[key], actual
    return True, None, None, None, None


def enumerate_binary_fns(m_L, m_S, m_R, determined):
    inputs = [(L, S, R) for L in range(m_L) for S in range(m_S) for R in range(m_R)]
    free_inputs = [t for t in inputs if t not in determined]
    results = []
    for bits in cartesian(range(m_S), repeat=len(free_inputs)):
        table = dict(determined)
        for i, t in enumerate(free_inputs):
            table[t] = bits[i]
        results.append(table)
    return results, free_inputs


def table_to_fn(table):
    def f(L, S, R):
        return table[(L, S, R)]
    return f


def main():
    n = 5
    ms = [2] + [3] * (n - 2) + [2]
    print(f"n={n}, ms={tuple(ms)}, product={4 * 3**(n-2)}")

    cycle, movers = build_bounce_cycle(ms, n)
    det = get_determined(cycle, movers, ms, n)
    print(f"Bounce cycle length: {len(cycle)}")

    # Check each middle rule's compatibility with bounce cycle
    print("\nMiddle rule compatibility with bounce cycle:")
    compatible_rules = []
    for name, rule in MIDDLE_RULES.items():
        ok, p, lsr, expected, actual = check_middle_compatible(rule, det, n, ms)
        if ok:
            print(f"  {name}: COMPATIBLE")
            compatible_rules.append((name, rule))
        else:
            print(f"  {name}: INCOMPATIBLE at P{p} f{lsr}: expected={expected}, got={actual}")

    # For each compatible middle rule, do exhaustive binary endpoint search
    det_p0 = {(L, S, R): v for (p, L, S, R), v in det.items() if p == 0}
    det_ptop = {(L, S, R): v for (p, L, S, R), v in det.items() if p == n - 1}

    m_L0, m_S0, m_R0 = ms[n - 1], ms[0], ms[1]
    m_Ltop, m_Stop, m_Rtop = ms[n - 2], ms[n - 1], ms[0]

    p0_cands, p0_free = enumerate_binary_fns(m_L0, m_S0, m_R0, det_p0)
    ptop_cands, ptop_free = enumerate_binary_fns(m_Ltop, m_Stop, m_Rtop, det_ptop)

    print(f"\nP0: {len(p0_cands)} candidates ({len(p0_free)} free entries)")
    print(f"P{n-1}: {len(ptop_cands)} candidates ({len(ptop_free)} free entries)")

    for mid_name, mid_rule in compatible_rules:
        print(f"\n{'='*60}")
        print(f"Middle rule: {mid_name}")
        print(f"{'='*60}")

        valid_count = 0
        tested = 0
        configs = list(cartesian(*(range(m) for m in ms)))

        for p0_table in p0_cands:
            for ptop_table in ptop_cands:
                tested += 1

                fs = [table_to_fn(p0_table)]
                for i in range(1, n - 1):
                    fs.append(lambda L, S, R, _rule=mid_rule, _m=ms[i]: _rule(L, S, R, _m))
                fs.append(table_to_fn(ptop_table))

                # Quick liveness check
                dead = False
                for c in configs:
                    has_priv = False
                    for i in range(n):
                        L = c[(i - 1) % n]
                        S = c[i]
                        R = c[(i + 1) % n]
                        if fs[i](L, S, R) != S:
                            has_priv = True
                            break
                    if not has_priv:
                        dead = True
                        break

                if dead:
                    continue

                result = verify_system(ms, fs)
                if result['valid']:
                    valid_count += 1
                    gcnt = len(result.get('good_configs', set()))
                    clen = result.get('cycle_length', '?')
                    print(f"\n  VALID #{valid_count}: good={gcnt}, cycle_len={clen}")
                    print(f"  P0 table (free entries marked F):")
                    for L in range(m_L0):
                        for S in range(m_S0):
                            for R in range(m_R0):
                                out = p0_table[(L, S, R)]
                                mark = "F" if (L, S, R) in dict.fromkeys(p0_free) else "D"
                                priv = "←" if out != S else " "
                                print(f"    f({L},{S},{R})={out} {priv} {mark}")
                    print(f"  P{n-1} table (free entries marked F):")
                    for L in range(m_Ltop):
                        for S in range(m_Stop):
                            for R in range(m_Rtop):
                                out = ptop_table[(L, S, R)]
                                mark = "F" if (L, S, R) in dict.fromkeys(ptop_free) else "D"
                                priv = "←" if out != S else " "
                                print(f"    f({L},{S},{R})={out} {priv} {mark}")

                    if valid_count >= 10:
                        break
            if valid_count >= 10:
                break

        print(f"  Total: {valid_count} valid / {tested} tested")


if __name__ == "__main__":
    main()
