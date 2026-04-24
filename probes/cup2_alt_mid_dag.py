#!/usr/bin/env python3
"""Properly check DAG property for T_mid(2,1,1)=2 variant.

With T_mid(2,1,1)=2 (copy_L), ALL entries are copy-neighbor except
the 4 structurally forced anomalous entries at boundary positions.
Check if bad graph is still a DAG and if (fc, Ψ) potential is affected.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top
from verifier import verify_system
from itertools import product as cartesian
from collections import deque


def build_system_alt(nv, mid_211_val=0):
    """Build system with specified T_mid(2,1,1) value."""
    t_mid = dict(T_mid)
    t_mid[(2,1,1)] = mid_211_val

    n = nv
    ms = [2] + [3] * (n - 2) + [2]

    def make_func(tbl):
        def f(L, S, R):
            return tbl.get((L, S, R), S)
        return f

    fs = []
    for i in range(n):
        if i == 0:
            fs.append(make_func(T_bot))
        elif i == 1:
            fs.append(make_func(T_low))
        elif i == n - 2:
            fs.append(make_func(T_high))
        elif i == n - 1:
            fs.append(make_func(T_top))
        else:
            fs.append(make_func(t_mid))

    return ms, fs


def delta_fc(L, S, R, out):
    return (int(L != out) - int(L != S)) + (int(out != R) - int(S != R))


def classify_entry(L, S, R, out):
    if out == S: return "stay"
    if out == L: return "copy_L"
    if out == R: return "copy_R"
    return "anomalous"


def check_dag(ms, fs, nv):
    """Full DAG check via Kahn's algorithm."""
    n = nv
    result = verify_system(ms, fs)
    good_set = result['good_configs']
    all_configs = list(cartesian(*(range(m) for m in ms)))
    bad_set = set(c for c in all_configs if c not in good_set)

    in_deg = {c: 0 for c in bad_set}
    adj = {c: [] for c in bad_set}
    edge_count = 0

    for c in bad_set:
        for i in range(n):
            Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
            out = fs[i](Li, Si, Ri)
            if out != Si:
                lst = list(c); lst[i] = out; succ = tuple(lst)
                if succ in bad_set:
                    adj[c].append(succ)
                    in_deg[succ] += 1
                    edge_count += 1

    q = deque(c for c in bad_set if in_deg[c] == 0)
    processed = 0
    while q:
        c = q.popleft()
        processed += 1
        for s in adj[c]:
            in_deg[s] -= 1
            if in_deg[s] == 0:
                q.append(s)

    return processed == len(bad_set), len(bad_set), edge_count


def main():
    print("DAG CHECK: ORIGINAL vs T_mid(2,1,1)=2 VARIANT")
    print("=" * 70)

    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break

        # Original: T_mid(2,1,1)=0
        ms_orig, fs_orig = build_system_alt(nv, 0)
        dag_orig, bad_orig, edges_orig = check_dag(ms_orig, fs_orig, nv)

        # Alternative: T_mid(2,1,1)=2
        ms_alt, fs_alt = build_system_alt(nv, 2)
        dag_alt, bad_alt, edges_alt = check_dag(ms_alt, fs_alt, nv)

        print(f"  n={nv}: orig DAG={dag_orig} ({bad_orig} bad, {edges_orig} edges), "
              f"alt DAG={dag_alt} ({bad_alt} bad, {edges_alt} edges)")

    # Count anomalous entries in alt variant
    print("\n\nANOMALOUS ENTRIES COMPARISON")
    print("-" * 60)

    t_mid_alt = dict(T_mid)
    t_mid_alt[(2,1,1)] = 2

    for label, t_mid_use in [("original (2,1,1)→0", T_mid),
                              ("alt (2,1,1)→2", t_mid_alt)]:
        count = 0
        entries = []
        for name, tbl, mL, mS, mR in [
            ('bot', T_bot, 2, 2, 3), ('low', T_low, 2, 3, 3),
            ('mid', t_mid_use, 3, 3, 3), ('high', T_high, 3, 3, 2),
            ('top', T_top, 3, 2, 2)]:
            for L in range(mL):
                for S in range(mS):
                    for R in range(mR):
                        out = tbl[(L, S, R)]
                        if out != S:
                            cls = classify_entry(L, S, R, out)
                            dfc = delta_fc(L, S, R, out)
                            if cls == 'anomalous':
                                count += 1
                                entries.append(f"{name}({L},{S},{R})→{out} Δfc={dfc:+d}")
        print(f"\n  {label}: {count} anomalous entries")
        for e in entries:
            print(f"    {e}")

    # Check: does the (fc, Ψ) argument cover the ALT variant?
    # With 4 anomalous entries (all boundary), check Δfc on all alt entries
    print("\n\nΔfc ANALYSIS FOR ALT VARIANT")
    print("-" * 60)
    t_mid_alt = dict(T_mid)
    t_mid_alt[(2,1,1)] = 2

    for name, tbl, mL, mS, mR in [
        ('bot', T_bot, 2, 2, 3), ('low', T_low, 2, 3, 3),
        ('mid', t_mid_alt, 3, 3, 3), ('high', T_high, 3, 3, 2),
        ('top', T_top, 3, 2, 2)]:
        dfc_pos = 0
        dfc_zero = 0
        dfc_neg = 0
        for L in range(mL):
            for S in range(mS):
                for R in range(mR):
                    out = tbl[(L, S, R)]
                    if out != S:
                        dfc = delta_fc(L, S, R, out)
                        if dfc > 0: dfc_pos += 1
                        elif dfc == 0: dfc_zero += 1
                        else: dfc_neg += 1
        print(f"  {name}: Δfc>0={dfc_pos}, Δfc=0={dfc_zero}, Δfc<0={dfc_neg}")

    # KEY: In alt variant, T_mid(2,1,1)=2 has Δfc=0 (copy_L).
    # So the ONLY Δfc>0 entries are the 4 boundary anomalous ones.
    # Does the (fc, Ψ) potential still work for the Δfc≤0 subgraph?
    print("\n\n(fc, Ψ) POTENTIAL FOR ALT VARIANT Δfc≤0 SUBGRAPH")
    print("-" * 60)
    from cup2_psi_proof import psi

    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 300000:
            break
        ms, fs = build_system_alt(nv, 2)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        violations = 0
        total = 0
        for c in bad_set:
            fc_c = sum(1 for j in range(n) if c[j] != c[(j+1)%n])
            psi_c = psi(c, n)
            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    dfc = delta_fc(Li, Si, Ri, out)
                    if dfc <= 0:
                        lst = list(c); lst[i] = out; succ = tuple(lst)
                        if succ in bad_set:
                            total += 1
                            fc_s = sum(1 for j in range(n)
                                       if succ[j] != succ[(j+1)%n])
                            psi_s = psi(succ, n)
                            if (fc_s, psi_s) >= (fc_c, psi_c):
                                violations += 1

        status = "✓" if violations == 0 else f"✗ {violations}"
        print(f"  n={nv}: {total} Δfc≤0 transitions, {status}")


if __name__ == "__main__":
    main()
