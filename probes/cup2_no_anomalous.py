#!/usr/bin/env python3
"""Check if anomalous entries can be eliminated by alternative choices.

Key insight: if ALL entries are copy-neighbor, then ALL transitions have
Δfc ≤ 0, and the (fc, Ψ) proof covers the full graph automatically.

For each anomalous entry, check if a copy-neighbor alternative exists
that preserves the system properties (0 dead configs, valid for all n).
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from verifier import verify_system
from itertools import product as cartesian
from collections import deque
from copy import deepcopy


def classify_entry(L, S, R, out):
    if out == S: return "stay"
    if out == L: return "copy_L"
    if out == R: return "copy_R"
    return "anomalous"


def check_system(tables_override, nv):
    """Build system with overridden entries and check validity."""
    # Unpack overrides
    t_bot = dict(T_bot)
    t_low = dict(T_low)
    t_mid = dict(T_mid)
    t_high = dict(T_high)
    t_top = dict(T_top)

    for (tbl_name, key), val in tables_override.items():
        if tbl_name == 'bot': t_bot[key] = val
        elif tbl_name == 'low': t_low[key] = val
        elif tbl_name == 'mid': t_mid[key] = val
        elif tbl_name == 'high': t_high[key] = val
        elif tbl_name == 'top': t_top[key] = val

    n = nv
    tables = [t_bot, t_low, t_mid, t_high, t_top]
    ms = [2] + [3] * (n - 2) + [2]

    def make_func(tbl, mL, mS, mR):
        def f(L, S, R):
            return tbl.get((L % mL, S % mS, R % mR), S)
        return f

    fs = []
    ms_list = ms
    for i in range(n):
        if i == 0:
            fs.append(make_func(t_bot, ms_list[-1], ms_list[0], ms_list[1]))
        elif i == 1:
            fs.append(make_func(t_low, ms_list[0], ms_list[1], ms_list[2]))
        elif i == n - 2:
            fs.append(make_func(t_high, ms_list[n-3], ms_list[n-2], ms_list[n-1]))
        elif i == n - 1:
            fs.append(make_func(t_top, ms_list[n-2], ms_list[n-1], ms_list[0]))
        else:
            fs.append(make_func(t_mid, ms_list[i-1], ms_list[i], ms_list[i+1]))

    result = verify_system(ms_list, fs)
    return result


def main():
    print("CAN ANOMALOUS ENTRIES BE ELIMINATED?")
    print("=" * 70)

    # The 5 anomalous entries:
    anomalous = [
        ('bot', (0,0,0), 1, 2),   # T_bot(0,0,0)→1, ms_bot=2
        ('bot', (1,1,2), 0, 2),   # T_bot(1,1,2)→0, ms_bot=2
        ('mid', (2,1,1), 0, 3),   # T_mid(2,1,1)→0, ms_mid=3
        ('high', (1,1,1), 2, 3),  # T_high(1,1,1)→2, ms_high=3
        ('top', (2,0,0), 1, 2),   # T_top(2,0,0)→1, ms_top=2
    ]

    print("\nFor each anomalous entry, check copy-neighbor alternatives:\n")

    for tbl_name, key, current_out, ms_pos in anomalous:
        L, S, R = key
        print(f"  {tbl_name.upper()}({L},{S},{R})→{current_out} [anomalous]:")

        # What are the copy-neighbor options?
        options = []
        if L != S and L < ms_pos:
            options.append(('copy_L', L))
        if R != S and R < ms_pos:
            options.append(('copy_R', R))
        if S < ms_pos:
            options.append(('stay', S))

        # Also check all possible outputs
        for v in range(ms_pos):
            if v == S:
                continue  # STAY
            cls = classify_entry(L, S, R, v)
            if cls in ('copy_L', 'copy_R'):
                if ('copy_L' if v == L else 'copy_R', v) not in options:
                    options.append((cls, v))

        print(f"    Current: {current_out} ({classify_entry(L,S,R,current_out)})")
        print(f"    Copy-neighbor options: {options}")

        # For non-STAY options, check if the system stays valid
        for cls_name, alt_val in options:
            if cls_name == 'stay':
                continue  # STAY would remove the privilege
            override = {(tbl_name, key): alt_val}
            # Check for a few n values
            valid_all = True
            for nv in range(5, 10):
                try:
                    result = check_system(override, nv)
                    if not result['valid']:
                        valid_all = False
                        break
                except Exception as e:
                    valid_all = False
                    break
            print(f"    Alt {cls_name}→{alt_val}: valid n=5..9: {'YES' if valid_all else 'NO'}")

    # Check the specific alternative: T_mid(2,1,1)=2 (copy_L instead of 0)
    print("\n\nDETAILED: T_mid(2,1,1)=2 (copy_L):")
    override = {('mid', (2,1,1)): 2}
    for nv in range(4, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        try:
            result = check_system(override, nv)
            dead = len(result.get('dead_configs', []))
            good = len(result.get('good_configs', set()))
            valid = result['valid']
            dag = 'Y' if result.get('is_dag', False) else 'N'
            print(f"  n={nv}: valid={valid}, dead={dead}, good={good}, dag={dag}")
        except Exception as e:
            print(f"  n={nv}: error: {e}")

    # Check: with T_mid(2,1,1)=2, how many anomalous entries remain?
    print("\n\nWith T_mid(2,1,1)=2: remaining anomalous entries:")
    t_mid_alt = dict(T_mid)
    t_mid_alt[(2,1,1)] = 2
    for name, tbl, mL, mS, mR in [
        ('bot', T_bot, 2, 2, 3), ('low', T_low, 2, 3, 3),
        ('mid', t_mid_alt, 3, 3, 3), ('high', T_high, 3, 3, 2),
        ('top', T_top, 3, 2, 2)]:
        for L_ in range(mL):
            for S_ in range(mS):
                for R_ in range(mR):
                    out = tbl[(L_, S_, R_)]
                    if out != S_:
                        cls = classify_entry(L_, S_, R_, out)
                        if cls == 'anomalous':
                            from cup2_psi_proof import delta_fc
                            dfc = delta_fc(L_, S_, R_, out)
                            print(f"  {name}({L_},{S_},{R_})→{out}: Δfc={dfc:+d}")

    # FUNDAMENTAL OBSTRUCTION CHECK:
    print("\n\nFUNDAMENTAL OBSTRUCTION:")
    print("Position 0 (bot, binary {0,1}):")
    print("  T_bot(0,0,0)→?: must be non-STAY. Options: 1 only. 1 is anomalous.")
    print("  T_bot(1,1,2)→0: L=1, R=2 (but R=2 > ms=2). Copy options: L=1 (STAY only).")
    print("  → Both entries MUST be anomalous (no copy-neighbor non-STAY option).")
    print()
    print("Similarly T_high(1,1,1)→2: L=1, R=1. Copy: L=1 (STAY), R=1 (STAY).")
    print("  Only non-STAY option: 0 or 2. Both anomalous.")
    print()
    print("T_top(2,0,0)→1: L=2, R=0. Copy: L=2 (exceeds ms=2), R=0 (STAY).")
    print("  Only non-STAY option: 1. Anomalous.")
    print()
    print("CONCLUSION: At least 4 anomalous entries are STRUCTURALLY FORCED.")
    print("No copy-neighbor system exists for ms=(2,3,...,3,2).")


if __name__ == "__main__":
    main()
