#!/usr/bin/env python3
"""Diagnose why rule combinations fail for ms=(2,3,...,3,2)."""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system


def make_middle(m_i):
    def f(L, S, R):
        if (S + 1) % m_i == L % m_i:
            return L % m_i
        if (S + 1) % m_i == R % m_i:
            return R % m_i
        return S
    return f


def test_and_diagnose(n, bot_rule, top_rule, label):
    ms = [2] + [3] * (n - 2) + [2]
    nn = n
    fs = [bot_rule]
    for i in range(1, nn - 1):
        fs.append(make_middle(ms[i]))
    fs.append(top_rule)

    configs = list(cartesian(*(range(m) for m in ms)))

    # Check liveness
    dead = []
    for c in configs:
        priv = []
        for i in range(nn):
            L = c[(i - 1) % nn]
            S = c[i]
            R = c[(i + 1) % nn]
            if fs[i](L, S, R) != S:
                priv.append(i)
        if not priv:
            dead.append(c)

    if dead:
        print(f"  {label}: {len(dead)} dead config(s)")
        for c in dead[:3]:
            print(f"    dead: {c}")
        return

    # Check via verifier
    result = verify_system(ms, fs)
    if result['valid']:
        print(f"  {label}: VALID! good={len(result['good_configs'])}, "
              f"cycle_len={result['cycle_length']}")
    else:
        props = result.get('properties', {})
        failures = [(k, v[1]) for k, v in props.items() if not v[0]]
        print(f"  {label}: INVALID — {failures}")


n = 5
print(f"n={n}, ms=(2,3,3,3,2)")
print()

# Test a selection of combos
combos = [
    ("sol3+sol3",
     lambda L, S, R: (1 - S) if (S + 1) % 2 == R % 2 else S,
     lambda L, S, R: (1 - S) if L % 2 == R and (L % 2 + 1) % 2 != S else S),
    ("sol3+revtop",
     lambda L, S, R: (1 - S) if (S + 1) % 2 == R % 2 else S,
     lambda L, S, R: L % 2 if L % 2 == R and S != L % 2 else S),
    ("sol3+agreeflip",
     lambda L, S, R: (1 - S) if (S + 1) % 2 == R % 2 else S,
     lambda L, S, R: (1 - S) if L % 2 == R else S),
    ("sol1dist+revtop",
     lambda L, S, R: (1 - S) if L == S else S,
     lambda L, S, R: L % 2 if L % 2 == R and S != L % 2 else S),
    ("sol1dist+agreeflip",
     lambda L, S, R: (1 - S) if L == S else S,
     lambda L, S, R: (1 - S) if L % 2 == R else S),
    ("agreeflip+agreeflip",
     lambda L, S, R: (1 - S) if L == R % 2 else S,
     lambda L, S, R: (1 - S) if L % 2 == R else S),
    ("conform_R+revtop",
     lambda L, S, R: R % 2 if R % 2 != S else S,
     lambda L, S, R: L % 2 if L % 2 == R and S != L % 2 else S),
    ("conform_R+agreeflip",
     lambda L, S, R: R % 2 if R % 2 != S else S,
     lambda L, S, R: (1 - S) if L % 2 == R else S),
    ("sol1other+sol1other",
     lambda L, S, R: L if L != S else S,
     lambda L, S, R: L % 2 if L % 2 != S else S),
    ("sol1dist+sol1dist",
     lambda L, S, R: (1 - S) if L == S else S,
     lambda L, S, R: (1 - S) if R == S else S),
]

for label, bot, top in combos:
    test_and_diagnose(n, bot, top, label)

# Also try: what if P_{n-2} gets a special hybrid rule instead of pure middle?
print("\n\nWith hybrid P_{n-2} (middle + extra condition):")

def make_hybrid_penult(m_i, m_R):
    """P_{n-2}: Sol 3 middle + top-like: if L%3=R%3 and (L%3+1)%3≠S → (L%3+1)%3"""
    def f(L, S, R):
        if (S + 1) % m_i == L % m_i:
            return L % m_i
        if (S + 1) % m_i == R % m_i:
            return R % m_i
        # Extra: if L=R (mod 3) and (L+1)%3 ≠ S
        if L % 3 == R % 3 and (L % 3 + 1) % 3 != S:
            return (L % 3 + 1) % 3
        return S
    return f

for label, bot, top in combos[:6]:
    ms = [2] + [3] * (n - 2) + [2]
    fs = [bot]
    for i in range(1, n - 2):
        fs.append(make_middle(ms[i]))
    fs.append(make_hybrid_penult(3, 2))  # P_{n-2}
    fs.append(top)

    configs = list(cartesian(*(range(m) for m in ms)))
    dead = [c for c in configs if not any(
        fs[j](c[(j-1)%n], c[j], c[(j+1)%n]) != c[j] for j in range(n))]

    if dead:
        print(f"  hybrid {label}: {len(dead)} dead")
        for c in dead[:2]:
            print(f"    {c}")
        continue

    result = verify_system(ms, fs)
    if result['valid']:
        print(f"  hybrid {label}: VALID! good={len(result['good_configs'])}, "
              f"cycle_len={result['cycle_length']}")
    else:
        props = result.get('properties', {})
        failures = [(k, v[1]) for k, v in props.items() if not v[0]]
        print(f"  hybrid {label}: INVALID — {failures}")
