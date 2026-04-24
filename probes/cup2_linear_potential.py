#!/usr/bin/env python3
"""Search for a linear potential φ = a·fc + b·Ψ + c·sum + d·count_2 + e·nonzero
that strictly decreases on ALL bad→bad transitions (including anomalous).

Also check: ΔΨ distribution on anomalous transitions, and whether
a 2-component potential (fc, Ψ) extended with a correction works.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import build_system
from verifier import verify_system
from cup2_psi_proof import psi, frontier_type, w1, w2, delta_fc
from itertools import product as cartesian


def classify_entry(L, S, R, out):
    if out == S: return "stay"
    if out == L: return "copy_L"
    if out == R: return "copy_R"
    return "anomalous"


def count_2s(c, n):
    return sum(1 for i in range(1, n - 1) if c[i] == 2)


def main():
    print("LINEAR POTENTIAL SEARCH")
    print("=" * 70)

    for nv in [6, 7, 8]:
        ms, fs = build_system(nv)
        n = nv
        result = verify_system(ms, fs)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        # Collect feature deltas for all transitions
        anom_deltas = []  # (Δfc, ΔΨ, Δsum, Δcount2, Δnonzero) for anomalous
        copy_deltas = []  # same for copy-neighbor
        all_deltas = []

        for c in bad_set:
            fc_c = sum(1 for j in range(n) if c[j] != c[(j+1)%n])
            psi_c = psi(c, n)
            sum_c = sum(c)
            c2_c = count_2s(c, n)
            nz_c = sum(1 for x in c if x > 0)

            for i in range(n):
                Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
                out = fs[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c); lst[i] = out; succ = tuple(lst)
                    if succ in bad_set:
                        fc_s = sum(1 for j in range(n) if succ[j] != succ[(j+1)%n])
                        psi_s = psi(succ, n)
                        sum_s = sum(succ)
                        c2_s = count_2s(succ, n)
                        nz_s = sum(1 for x in succ if x > 0)

                        d = (fc_s - fc_c, psi_s - psi_c, sum_s - sum_c,
                             c2_s - c2_c, nz_s - nz_c)
                        cls = classify_entry(Li, Si, Ri, out)
                        all_deltas.append(d)
                        if cls == "anomalous":
                            anom_deltas.append(d)
                        else:
                            copy_deltas.append(d)

        print(f"\nn={nv}: {len(copy_deltas)} copy-neighbor, "
              f"{len(anom_deltas)} anomalous transitions")

        # ΔΨ distribution on anomalous transitions
        dpsi_vals = sorted(set(d[1] for d in anom_deltas))
        print(f"  Anomalous ΔΨ range: [{min(dpsi_vals)}, {max(dpsi_vals)}]")
        # Show distribution
        from collections import Counter
        dpsi_counts = Counter(d[1] for d in anom_deltas)
        print(f"  Anomalous ΔΨ distribution: {dict(sorted(dpsi_counts.items()))}")

        # Anomalous Δfc distribution
        dfc_counts = Counter(d[0] for d in anom_deltas)
        print(f"  Anomalous Δfc distribution: {dict(sorted(dfc_counts.items()))}")

        # Check: does φ = -Ψ strictly decrease? (i.e., does Ψ always increase?)
        psi_inc = sum(1 for d in all_deltas if d[1] > 0)
        psi_dec = sum(1 for d in all_deltas if d[1] < 0)
        psi_same = sum(1 for d in all_deltas if d[1] == 0)
        print(f"  ΔΨ overall: inc={psi_inc}, same={psi_same}, dec={psi_dec}")

        # Try: φ = a*fc + b*Ψ for various (a,b)
        print(f"\n  Searching φ = a·fc + b·Ψ:")
        best_viol = len(all_deltas)
        best_ab = None
        for a in range(-20, 21):
            for b in range(-20, 21):
                if a == 0 and b == 0:
                    continue
                viol = sum(1 for d in all_deltas if a*d[0] + b*d[1] >= 0)
                if viol < best_viol:
                    best_viol = viol
                    best_ab = (a, b)
        print(f"    Best (a,b)={best_ab}: {best_viol} violations "
              f"({100*best_viol/len(all_deltas):.1f}%)")

        # Try: φ = a*fc + b*Ψ + c*sum
        if nv <= 7:
            print(f"  Searching φ = a·fc + b·Ψ + c·sum:")
            best_viol = len(all_deltas)
            best_abc = None
            for a in range(-10, 11):
                for b in range(-10, 11):
                    for c in range(-10, 11):
                        if a == 0 and b == 0 and c == 0:
                            continue
                        viol = sum(1 for d in all_deltas
                                   if a*d[0] + b*d[1] + c*d[2] >= 0)
                        if viol < best_viol:
                            best_viol = viol
                            best_abc = (a, b, c)
                            if viol == 0:
                                break
                    if best_viol == 0:
                        break
                if best_viol == 0:
                    break
            print(f"    Best (a,b,c)={best_abc}: {best_viol} violations "
                  f"({100*best_viol/len(all_deltas):.1f}%)")

        # Try 5-component
        if nv <= 6:
            print(f"  Searching φ = a·fc + b·Ψ + c·sum + d·count2 + e·nonzero:")
            best_viol = len(all_deltas)
            best_w = None
            for a in range(-5, 6):
                for b in range(-5, 6):
                    for c in range(-5, 6):
                        for d in range(-5, 6):
                            for e in range(-5, 6):
                                if a == 0 and b == 0 and c == 0 and d == 0 and e == 0:
                                    continue
                                viol = sum(1 for dd in all_deltas
                                           if a*dd[0]+b*dd[1]+c*dd[2]+d*dd[3]+e*dd[4] >= 0)
                                if viol < best_viol:
                                    best_viol = viol
                                    best_w = (a, b, c, d, e)
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
            print(f"    Best (a,b,c,d,e)={best_w}: {best_viol} violations "
                  f"({100*best_viol/len(all_deltas):.1f}%)")


if __name__ == "__main__":
    main()
