#!/usr/bin/env python3
"""Examine CLB's witness at ms=(2,3,...,3,2) to find patterns in transition rules."""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict

def build_bounce_cycle(ms, n):
    """Build the bounce cycle: movers [0,1,...,n-1,n-2,...,1]."""
    up_down = list(range(n)) + list(range(n-2, 0, -1))
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}
    full = up_down * 5
    for step, mover in enumerate(full):
        config = list(cycle[-1])
        config[mover] = (config[mover] + 1) % ms[mover]
        nc = tuple(config)
        if nc == cycle[0]:
            return cycle, full[:step+1]
        if nc in visited:
            raise RuntimeError(f"Revisited {nc} at step {step}")
        visited.add(nc)
        cycle.append(nc)
    raise RuntimeError("Cycle didn't close")


def examine_cycle(n):
    ms = [2] + [3]*(n-2) + [2]
    print(f"\n{'='*70}")
    print(f"n={n}, ms={tuple(ms)}, product={2*2*3**(n-2)}")
    print(f"{'='*70}")

    cycle, movers = build_bounce_cycle(ms, n)
    print(f"Cycle length: {len(cycle)}")
    print(f"Movers: {movers}")

    # Print cycle configs with movers
    print(f"\nBounce cycle:")
    for i, c in enumerate(cycle):
        mv = movers[i]
        c_str = ''.join(str(x) for x in c)
        print(f"  step {i:2d}: {c_str}  mover=P{mv}")

    # Extract determined entries
    det = {}
    for idx in range(len(cycle)):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % len(cycle)]
        mv = movers[idx]
        for p in range(n):
            L = c[(p-1) % n]; S = c[p]; R = c[(p+1) % n]
            key = (p, L, S, R)
            if p == mv:
                det[key] = c_next[p]
            else:
                det[key] = S

    # Count entries per processor
    print(f"\nDetermined entries: {len(det)}")
    for p in range(n):
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]
        total = m_L * m_S * m_R
        p_det = sum(1 for k in det if k[0] == p)
        p_priv = sum(1 for k in det if k[0] == p and det[k] != k[2])
        print(f"  P{p} (m={m_S}): {p_det}/{total} determined, {p_priv} privileged")

    # Print determined rules per processor, grouped by privilege type
    print(f"\nDetermined transition entries (privileged only):")
    for p in range(n):
        m_L = ms[(p-1) % n]; m_S = ms[p]; m_R = ms[(p+1) % n]
        priv_entries = []
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    key = (p, L, S, R)
                    if key in det and det[key] != S:
                        priv_entries.append((L, S, R, det[key]))
        if priv_entries:
            print(f"  P{p} (m={m_S}):")
            for L, S, R, out in priv_entries:
                print(f"    f({L},{S},{R}) = {out}  [S→{out}]")

    return cycle, movers, det, ms


if __name__ == "__main__":
    for nv in [5, 6, 7, 8, 9]:
        examine_cycle(nv)
