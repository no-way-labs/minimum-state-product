#!/usr/bin/env python3
"""Prove anomalous transitions can't create cycles.

We know:
- Δfc≤0 subgraph is a DAG (verified n=5..12)
- 5 anomalous entries have Δfc>0
- Need: full graph (Δfc≤0 + anomalous) is still a DAG

Strategy: define fc*(c) = fc(c) + correction terms, such that
Δfc* ≤ 0 on EVERY transition (including anomalous).
Then fc* ≤ 0 + Δfc=0 DAG → full graph is DAG.

The correction terms "pre-charge" configs that COULD fire anomalous entries.
When the anomalous entry fires, the pre-charge is consumed.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque


def delta_fc(L, S, R, out):
    before_left = int(L != S)
    before_right = int(S != R)
    after_left = int(L != out)
    after_right = int(out != R)
    return (after_left - before_left) + (after_right - before_right)


def classify_entry(L, S, R, out):
    if out == S: return "stay"
    if out == L: return "copy_L"
    if out == R: return "copy_R"
    return "anomalous"


def alpha_indicators(c, n):
    """Compute all anomalous-entry indicator values.
    Returns dict mapping indicator name to value (0 or 1).
    """
    indicators = {}
    # T_bot(0,0,0)→1: c[n-1]=0, c[0]=0, c[1]=0
    indicators['bot_000'] = int(c[n-1]==0 and c[0]==0 and c[1]==0)
    # T_bot(1,1,2)→0: c[n-1]=1, c[0]=1, c[1]=2
    indicators['bot_112'] = int(c[n-1]==1 and c[0]==1 and c[1]==2)
    # T_mid(2,1,1)→0: c[i-1]=2, c[i]=1, c[i+1]=1 for any interior i
    mid_count = sum(1 for i in range(2, n-2)
                    if c[i-1]==2 and c[i]==1 and c[i+1]==1)
    indicators['mid_211'] = mid_count
    # T_high(1,1,1)→2: c[n-3]=1, c[n-2]=1, c[n-1]=1
    indicators['high_111'] = int(c[n-3]==1 and c[n-2]==1 and c[n-1]==1) if n >= 4 else 0
    # T_top(2,0,0)→1: c[n-2]=2, c[n-1]=0, c[0]=0
    indicators['top_200'] = int(c[n-2]==2 and c[n-1]==0 and c[0]==0)
    return indicators


def fc_star(c, n, weights):
    """Modified frontier count: fc(c) + Σ w_i * α_i(c)."""
    fc = sum(1 for i in range(n) if c[i] != c[(i+1)%n])
    alpha = alpha_indicators(c, n)
    correction = (weights['bot_000'] * alpha['bot_000'] +
                  weights['bot_112'] * alpha['bot_112'] +
                  weights['mid_211'] * alpha['mid_211'] +
                  weights['high_111'] * alpha['high_111'] +
                  weights['top_200'] * alpha['top_200'])
    return fc + correction


def test_weights(weights, nv):
    """Test if fc* with given weights has Δfc* ≤ 0 on all bad→bad transitions."""
    ms, fs = build_system(nv)
    n = nv
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    violations = 0
    worst = 0
    worst_trans = None
    for c in bad_set:
        fc_c = fc_star(c, n, weights)
        for i in range(n):
            Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
            out = fs[i](Li, Si, Ri)
            if out != Si:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    fc_s = fc_star(succ, n, weights)
                    diff = fc_s - fc_c
                    if diff > 0:
                        violations += 1
                        if diff > worst:
                            worst = diff
                            worst_trans = (c, succ, i, fc_c, fc_s)
    return violations, worst, worst_trans


def main():
    print("MODIFIED FRONTIER fc* SEARCH")
    print("=" * 70)

    # The anomalous entries have these Δfc values:
    # bot_000: +2, bot_112: +1, mid_211: +1, high_111: +2, top_200: +1
    # When they fire, the corresponding α indicator goes from 1 to 0.
    # So Δfc* = Δfc + w*(0-1) = Δfc - w.
    # For Δfc*≤0: w ≥ Δfc. So w_bot_000 ≥ 2, w_bot_112 ≥ 1, etc.
    # But OTHER transitions might INCREASE α, making Δfc* > 0.

    # Try the minimal weights first
    base_weights = {
        'bot_000': 2, 'bot_112': 1, 'mid_211': 1,
        'high_111': 2, 'top_200': 1
    }

    for nv in range(5, 11):
        prod = 4 * 3 ** (nv - 2)
        if prod > 100000:
            break
        viol, worst, wt = test_weights(base_weights, nv)
        print(f"  n={nv}: violations={viol}, worst_increase={worst}")
        if wt and nv <= 7:
            c, succ, mv, fc_c, fc_s = wt
            print(f"    Example: {c} →[P{mv}]→ {succ}: fc*={fc_c}→{fc_s}")

    # Try larger weights
    print("\nTrying larger weights...")
    for w_extra in range(0, 5):
        weights = {
            'bot_000': 2 + w_extra, 'bot_112': 1 + w_extra,
            'mid_211': 1 + w_extra,
            'high_111': 2 + w_extra, 'top_200': 1 + w_extra
        }
        viol6, _, _ = test_weights(weights, 6)
        print(f"  all+{w_extra}: n=6 violations={viol6}")

    # Try asymmetric weights
    print("\nAsymmetric weight search (n=6)...")
    best_viol = float('inf')
    best_w = None
    for w1 in range(0, 8):
        for w2 in range(0, 8):
            for w3 in range(0, 8):
                for w4 in range(0, 8):
                    for w5 in range(0, 8):
                        weights = {
                            'bot_000': w1, 'bot_112': w2,
                            'mid_211': w3, 'high_111': w4,
                            'top_200': w5
                        }
                        viol, _, _ = test_weights(weights, 6)
                        if viol < best_viol:
                            best_viol = viol
                            best_w = dict(weights)
                            if viol == 0:
                                break
                    if best_viol == 0:
                        break
                if best_viol == 0:
                    break
            if best_viol == 0:
                break
        if best_viol == 0:
            break

    print(f"  Best: violations={best_viol}, weights={best_w}")
    if best_viol == 0:
        # Verify for larger n
        for nv in range(7, 13):
            prod = 4 * 3 ** (nv - 2)
            if prod > 300000:
                break
            viol, _, _ = test_weights(best_w, nv)
            print(f"  n={nv}: violations={viol}")


if __name__ == "__main__":
    main()
