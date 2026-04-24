#!/usr/bin/env python3
"""Find the dead config in Sol 3 v1 rules on ms=(2,3,...,3,2)."""

import sys
import os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian


def sol3_rules_232(ms, n):
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


for nv in range(3, 10):
    ms = [2] + [3] * (nv - 2) + [2]
    n = nv
    fs = sol3_rules_232(ms, n)
    configs = list(cartesian(*(range(m) for m in ms)))

    for c in configs:
        priv = []
        for i in range(n):
            L = c[(i - 1) % n]
            S = c[i]
            R = c[(i + 1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        if len(priv) == 0:
            print(f"n={nv}: dead config = {c}")
            # Analyze why each proc is not privileged
            for i in range(n):
                L = c[(i - 1) % n]
                S = c[i]
                R = c[(i + 1) % n]
                print(f"  P{i}: L={L}, S={S}, R={R}, f={fs[i](L,S,R)}")
