#!/usr/bin/env python3
"""Test Sol 3 v1 rules applied directly to ms=(2,3,...,3,2).

Rules:
  P0 (bottom, m=2):  (S+1)%2 = R%2 → flip S
  P_i (middle, m=3): (S+1)%3 = L%3 → copy L;  (S+1)%3 = R%3 → copy R
  P_{n-1} (top, m=2): L%2 = R%2 and (L%2+1)%2 ≠ S → flip S
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from verifier import verify_system


def sol3_rules_232(ms, n):
    """Standard Sol 3 v1 rules for any ms."""
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
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f

    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def test_n(n):
    ms = [2] + [3] * (n - 2) + [2]
    fs = sol3_rules_232(ms, n)
    result = verify_system(ms, fs)

    prod = 1
    for m in ms:
        prod *= m
    status = "VALID" if result['valid'] else "INVALID"
    props = result.get('properties', {})
    detail = "; ".join(f"{k}: {v[1]}" for k, v in props.items() if v[1])

    print(f"n={n}, ms={tuple(ms)}, prod={prod}: {status}", end="")
    if detail:
        print(f"  [{detail}]", end="")
    if result['valid']:
        print(f"  good={len(result.get('good_configs', set()))}, "
              f"cycle_len={result.get('cycle_length', '?')}", end="")
    print()
    return result


if __name__ == "__main__":
    print("Sol 3 v1 rules on ms=(2,3,...,3,2)")
    print("=" * 70)
    for nv in range(3, 14):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500000:
            print(f"n={nv}: SKIP (prod={prod})")
            continue
        test_n(nv)
