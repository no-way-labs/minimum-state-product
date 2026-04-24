#!/usr/bin/env python3
"""Systematic search over top/bottom binary rule variants for ms=(2,3,...,3,2).

Middle ternary procs always use Sol 3 middle rule.
We try all reasonable binary rules for P0 (bottom) and P_{n-1} (top).
"""

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


# Candidate bottom rules (P0: m_L=2, m_S=2, m_R=3)
# P0's left neighbor is P_{n-1} (binary), right is P1 (ternary)
bottom_rules = {}

# Sol3 bottom: (S+1)%2 = R%2 → flip
bottom_rules["sol3_bot"] = lambda L, S, R: (1 - S) if (S + 1) % 2 == R % 2 else S

# Sol1 distinguished: L=S → increment
bottom_rules["sol1_dist"] = lambda L, S, R: (1 - S) if L == S else S

# Sol1 other: L≠S → copy L
bottom_rules["sol1_other"] = lambda L, S, R: L if L != S else S

# Conform to R: R%2≠S → copy R%2
bottom_rules["conform_R"] = lambda L, S, R: R % 2 if R % 2 != S else S

# Conform to L: L≠S → copy L
bottom_rules["conform_L"] = lambda L, S, R: L if L != S else S  # same as sol1_other

# Fire when R%2=L and S≠R%2 (neighbors agree, self disagrees)
bottom_rules["agree_neigh"] = lambda L, S, R: (1 - S) if L == R % 2 and S != L else S

# Sol3 bot + extra: also fire when L=S and R%3=0
bottom_rules["sol3_extra"] = lambda L, S, R: (1 - S) if ((S + 1) % 2 == R % 2) or (L == S and R % 3 == (2 * S) % 3) else S

# Always fire when L=R%2=S (all agree → flip, Sol1-like)
bottom_rules["all_agree_flip"] = lambda L, S, R: (1 - S) if L == R % 2 == S else S

# Fire when (S+1)%2 = R%2 OR (L=R%2 and S≠L) — Sol3 + conform
bottom_rules["sol3_or_conform"] = lambda L, S, R: (1 - S) if ((S + 1) % 2 == R % 2) or (L == R % 2 and S != L) else S


# Candidate top rules (P_{n-1}: m_L=3, m_S=2, m_R=2)
# P_{n-1}'s left neighbor is P_{n-2} (ternary), right is P0 (binary)
top_rules = {}

# Sol3 top: L%2=R and (L%2+1)%2 ≠ S → produce (L%2+1)%2
# i.e., L%2=R=S → flip
top_rules["sol3_top"] = lambda L, S, R: (1 - S) if L % 2 == R and (L % 2 + 1) % 2 != S else S

# Reverse Sol3 top: L%2=R and S≠L%2 → copy L%2
top_rules["rev_sol3_top"] = lambda L, S, R: L % 2 if L % 2 == R and S != L % 2 else S

# Always flip when L%2=R (neighbors agree mod 2)
top_rules["agree_flip"] = lambda L, S, R: (1 - S) if L % 2 == R else S

# Sol1 other: L%2≠S → copy L%2
top_rules["sol1_other"] = lambda L, S, R: L % 2 if L % 2 != S else S

# Sol1 distinguished: R=S → flip
top_rules["sol1_dist"] = lambda L, S, R: (1 - S) if R == S else S

# Conform to R: R≠S → copy R
top_rules["conform_R"] = lambda L, S, R: R if R != S else S

# Fire when L%2=R and S≠R → conform to R
top_rules["conform_agree"] = lambda L, S, R: R if L % 2 == R and S != R else S

# Fire when L%2=R=S (all agree → flip) OR (L%2=R≠S → conform)
# This is just "always flip when L%2=R"
top_rules["combined"] = lambda L, S, R: (1 - S) if L % 2 == R else S  # same as agree_flip


def test_combination(n, bot_name, bot_rule, top_name, top_rule):
    ms = [2] + [3] * (n - 2) + [2]
    fs = [bot_rule]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(top_rule)
    result = verify_system(ms, fs)
    return result


def main():
    print("Searching top/bottom rule combinations for ms=(2,3,...,3,2)")
    print("=" * 80)

    # Test at n=5 first (small enough to be fast)
    for nv in [5, 7, 9]:
        print(f"\n--- n={nv} ---")
        valid_combos = []
        for bname, brule in bottom_rules.items():
            for tname, trule in top_rules.items():
                r = test_combination(nv, bname, brule, tname, trule)
                if r['valid']:
                    valid_combos.append((bname, tname, r))
                    gcnt = len(r.get('good_configs', set()))
                    clen = r.get('cycle_length', '?')
                    print(f"  VALID: bot={bname}, top={tname}, "
                          f"good={gcnt}, cycle_len={clen}")

        if not valid_combos:
            print("  No valid combinations found!")
        else:
            print(f"  {len(valid_combos)} valid combination(s)")


if __name__ == "__main__":
    main()
