#!/usr/bin/env python3
"""Analyze CLB's witness transition tables to find closed-form rules."""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import defaultdict
from clb_witness_8748 import build_system


def analyze_rules():
    ms, fs, comp = build_system()
    n = len(ms)

    print(f"ms={tuple(ms)}, n={n}")
    print()

    # For each processor, print full truth table
    for p in range(n):
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]

        priv_entries = []
        non_priv = []
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    out = fs[p](L, S, R)
                    if out != S:
                        priv_entries.append((L, S, R, out))
                    else:
                        non_priv.append((L, S, R))

        print(f"P{p} (m_L={m_L}, m_S={m_S}, m_R={m_R}): {len(priv_entries)} privileged entries")
        for L, S, R, out in priv_entries:
            print(f"  f({L},{S},{R}) = {out}")
        print()

    # Now test candidate rules
    print("=" * 60)
    print("TESTING CANDIDATE RULES")
    print("=" * 60)

    # Test: middle procs use standard Sol3 rule
    print("\nMiddle procs (P1..P{n-2}) — Sol 3 rule test:")
    for p in range(1, n-1):
        m_L = ms[(p-1) % n]
        m_S = ms[p]
        m_R = ms[(p+1) % n]
        mismatches = 0
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    actual = fs[p](L, S, R)
                    # Sol 3 middle rule
                    sol3 = S
                    if (S+1) % 3 == L % 3:
                        sol3 = L % 3
                    elif (S+1) % 3 == R % 3:
                        sol3 = R % 3
                    if actual != sol3:
                        mismatches += 1
                        if mismatches <= 3:
                            print(f"  P{p} f({L},{S},{R}): actual={actual}, sol3={sol3}")
        if mismatches == 0:
            print(f"  P{p}: EXACT MATCH with Sol 3 middle rule")
        else:
            print(f"  P{p}: {mismatches} mismatches")

    # Test: P_{n-2} uses Sol3 middle + top hybrid
    print(f"\nP{n-2} — Sol 3 middle+top hybrid test:")
    p = n-2
    m_L = ms[(p-1) % n]; m_S = ms[p]; m_R = ms[(p+1) % n]
    mismatches = 0
    for L in range(m_L):
        for S in range(m_S):
            for R in range(m_R):
                actual = fs[p](L, S, R)
                # Hybrid: middle rule first, then top-like if L=R
                hybrid = S
                if (S+1) % 3 == L % 3:
                    hybrid = L % 3
                elif (S+1) % 3 == R % 3:
                    hybrid = R % 3
                elif L % 3 == R % 3 and (L % 3 + 1) % 3 != S:
                    hybrid = (L % 3 + 1) % 3
                if actual != hybrid:
                    mismatches += 1
                    print(f"  f({L},{S},{R}): actual={actual}, hybrid={hybrid}")
    if mismatches == 0:
        print(f"  EXACT MATCH with middle+top hybrid")
    else:
        print(f"  {mismatches} mismatches")

    # Test: P_{n-1} (top binary) uses "L=R, S≠L" rule
    print(f"\nP{n-1} (top binary) — 'L=R≠S → copy L' test:")
    p = n-1
    m_L = ms[(p-1) % n]; m_S = ms[p]; m_R = ms[(p+1) % n]
    mismatches = 0
    for L in range(m_L):
        for S in range(m_S):
            for R in range(m_R):
                actual = fs[p](L, S, R)
                # Candidate: fire when L%2 == R%2 and S != L%2
                candidate = S
                if L % 2 == R % 2 and S != L % 2:
                    candidate = (S + 1) % 2
                if actual != candidate:
                    mismatches += 1
                    print(f"  f({L},{S},{R}): actual={actual}, candidate={candidate}")
    if mismatches == 0:
        print(f"  EXACT MATCH")
    else:
        print(f"  {mismatches} mismatches")

    # Test: P0 (bottom binary) — try various rules
    print(f"\nP0 (bottom binary) — testing candidates:")
    p = 0
    m_L = ms[(p-1) % n]; m_S = ms[p]; m_R = ms[(p+1) % n]

    # Candidate 1: Sol 3 bottom (S+1)%2 = R%2
    # Candidate 2: L=S and (R+S)%3=0
    # Candidate 3: L%2=R%2 and S!=L%2 (symmetric to top)
    # Candidate 4: L=S (only)
    # Candidate 5: (S+1)%2 = L%2 (detect left, not right)

    candidates = {
        "Sol3 bot: (S+1)%2=R%2": lambda L,S,R: (S+1)%2 if (S+1)%2==R%2 else S,
        "L=S and (R+S)%3=0": lambda L,S,R: (S+1)%2 if L==S and (R+S)%3==0 else S,
        "Symm top: L%2=R%2,S≠L%2": lambda L,S,R: (S+1)%2 if L%2==R%2 and S!=L%2 else S,
        "L%2=S and R%2≠S": lambda L,S,R: (S+1)%2 if L%2==S and R%2!=S else S,
        "L=S": lambda L,S,R: (S+1)%2 if L==S else S,
        "L=S, R≠(S+1)%3": lambda L,S,R: (S+1)%2 if L==S and R!=(S+1)%3 else S,
    }

    for name, rule in candidates.items():
        mismatches = 0
        details = []
        for L in range(m_L):
            for S in range(m_S):
                for R in range(m_R):
                    actual = fs[p](L, S, R)
                    cand = rule(L, S, R)
                    if actual != cand:
                        mismatches += 1
                        details.append(f"f({L},{S},{R}): actual={actual}, cand={cand}")
        print(f"  {name}: {mismatches} mismatches")
        for d in details[:5]:
            print(f"    {d}")

    # Print P0's full table
    print(f"\nP0 full truth table:")
    for L in range(m_L):
        for S in range(m_S):
            for R in range(m_R):
                out = fs[p](L, S, R)
                priv = "←" if out != S else " "
                print(f"  f({L},{S},{R}) = {out} {priv}")


if __name__ == "__main__":
    analyze_rules()
