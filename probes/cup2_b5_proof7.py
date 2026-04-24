"""
B5 CASE SPLIT — Check if ALT system's (fc, Ψ) decreases at B5.

Key question: The convergence theorem proves (fc, Ψ) is a potential
for the Δfc≤0 subgraph of the ALT system. Does this same (fc, Ψ)
also decrease on B5 transitions in the ORIGINAL system?

If YES: the ALT proof directly extends to the original.
If NO: need a modified potential or different argument.
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from collections import deque
from cup2_theorem import T_bot, T_low, T_mid, T_high, T_top, build_system
from cup2_convergence_theorem import psi, build_system as build_alt
from verifier import verify_system


def fc(c):
    n = len(c)
    return sum(1 for i in range(n) if c[i] != c[(i + 1) % n])


def delta_fc_firing(c, i, new_val):
    n = len(c)
    old = c[i]
    lv = c[(i - 1) % n]
    rv = c[(i + 1) % n]
    return ((1 if lv != new_val else 0) + (1 if new_val != rv else 0)
            - (1 if lv != old else 0) - (1 if old != rv else 0))


def main():
    print("B5 vs (fc, Ψ) POTENTIAL")
    print("=" * 65)

    # ── PART 1: Does (fc, Ψ) decrease at B5? ──
    print("\nPART 1: (fc, Ψ) at B5 Transitions")
    print("-" * 65)

    for nv in range(5, 14):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500_000:
            break
        ms, fs_orig = build_system(nv)
        n = nv
        result = verify_system(ms, fs_orig)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        total_b5 = 0
        fc_psi_violations = 0
        fc_psi_ok = 0

        for c in bad_set:
            for j in range(2, n - 2):
                if c[j - 1] == 2 and c[j] == 1 and c[j + 1] == 1:
                    # B5 fires: c[j] = 1 → 0
                    lst = list(c)
                    lst[j] = 0
                    succ = tuple(lst)
                    if succ not in bad_set:
                        continue

                    total_b5 += 1
                    fc_c = fc(c)
                    fc_s = fc(succ)
                    psi_c = psi(c, n)
                    psi_s = psi(succ, n)

                    # Lexicographic: (fc, -Ψ) should decrease
                    # Wait, (fc, Ψ) should decrease lex
                    if (fc_s, psi_s) < (fc_c, psi_c):
                        fc_psi_ok += 1
                    else:
                        fc_psi_violations += 1

        v = "✓" if fc_psi_violations == 0 else "✗"
        print(f"  n={nv}: {total_b5} B5, "
              f"(fc,Ψ) decreases: {fc_psi_ok}, "
              f"violations: {fc_psi_violations}  {v}")

    # ── PART 2: Does ΔΨ compensate Δfc at B5? ──
    print("\n\nPART 2: ΔΨ at B5 Transitions")
    print("-" * 65)

    for nv in range(5, 12):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500_000:
            break
        ms, fs_orig = build_system(nv)
        n = nv
        result = verify_system(ms, fs_orig)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        dpsi_values = []
        for c in bad_set:
            for j in range(2, n - 2):
                if c[j - 1] == 2 and c[j] == 1 and c[j + 1] == 1:
                    lst = list(c)
                    lst[j] = 0
                    succ = tuple(lst)
                    if succ not in bad_set:
                        continue
                    psi_c = psi(c, n)
                    psi_s = psi(succ, n)
                    dpsi_values.append(psi_s - psi_c)

        if dpsi_values:
            print(f"  n={nv}: ΔΨ range [{min(dpsi_values):+d}, "
                  f"{max(dpsi_values):+d}]  "
                  f"avg={sum(dpsi_values)/len(dpsi_values):+.1f}")

    # ── PART 3: Full potential check for ORIGINAL system ──
    print("\n\nPART 3: (fc, Ψ) on ALL transitions (Original System)")
    print("-" * 65)

    for nv in range(5, 13):
        prod = 4 * 3 ** (nv - 2)
        if prod > 500_000:
            break
        ms, fs_orig = build_system(nv)
        n = nv
        result = verify_system(ms, fs_orig)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        total = 0
        violations = 0
        viol_dfc = {}

        for c in bad_set:
            fc_c = fc(c)
            psi_c = psi(c, n)
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = fs_orig[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        total += 1
                        fc_s = fc(succ)
                        psi_s = psi(succ, n)
                        if (fc_s, psi_s) >= (fc_c, psi_c):
                            violations += 1
                            dfc = fc_s - fc_c
                            viol_dfc[dfc] = viol_dfc.get(dfc, 0) + 1

        v = "✓" if violations == 0 else "✗"
        vd_str = ", ".join(f"Δfc={k}:{v}" for k, v in sorted(viol_dfc.items()))
        print(f"  n={nv}: {total} edges, {violations} violations  {v}")
        if viol_dfc:
            print(f"    breakdown: {vd_str}")

    # ── PART 4: Try modified Ψ ──
    print("\n\nPART 4: Modified Potential Search")
    print("-" * 65)
    print("  Trying Ψ variants that handle B5...")

    # Modified Ψ: add a penalty for stuck-at-0 positions
    def psi_mod(c, n, alpha=1):
        """Ψ + α × (number of j where c[j]=0 and c[j-1]=2)."""
        base = psi(c, n)
        penalty = 0
        for j in range(2, n - 2):  # only mid positions
            if c[j] == 0 and c[j - 1] == 2:
                penalty += 1
        return base + alpha * penalty

    for alpha in [1, 2, 3, 5, 10, 20]:
        # Check (fc, Ψ_mod) on original system at n=5
        nv = 5
        ms, fs_orig = build_system(nv)
        n = nv
        result = verify_system(ms, fs_orig)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        violations = 0
        total = 0
        for c in bad_set:
            fc_c = fc(c)
            psi_c = psi_mod(c, n, alpha)
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = fs_orig[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        total += 1
                        fc_s = fc(succ)
                        psi_s = psi_mod(succ, n, alpha)
                        if (fc_s, psi_s) >= (fc_c, psi_c):
                            violations += 1

        print(f"  α={alpha}: n=5, {violations}/{total} violations "
              f"{'✓' if violations == 0 else ''}")

    # Try scalar potential: α·fc + Ψ
    print("\n  Trying scalar α·fc + Ψ:")
    for alpha in range(1, 30):
        nv = 5
        ms, fs_orig = build_system(nv)
        n = nv
        result = verify_system(ms, fs_orig)
        good_set = result['good_configs']
        all_configs = list(cartesian(*(range(m) for m in ms)))
        bad_set = set(c for c in all_configs if c not in good_set)

        violations = 0
        total = 0
        for c in bad_set:
            phi_c = alpha * fc(c) + psi(c, n)
            for i in range(n):
                Li = c[(i - 1) % n]
                Si = c[i]
                Ri = c[(i + 1) % n]
                out = fs_orig[i](Li, Si, Ri)
                if out != Si:
                    lst = list(c)
                    lst[i] = out
                    succ = tuple(lst)
                    if succ in bad_set:
                        total += 1
                        phi_s = alpha * fc(succ) + psi(succ, n)
                        if phi_s >= phi_c:
                            violations += 1

        if violations == 0:
            # Verify at n=6,7
            ok_all = True
            for nv2 in [6, 7, 8]:
                ms2, fs2 = build_system(nv2)
                n2 = nv2
                result2 = verify_system(ms2, fs2)
                good2 = result2['good_configs']
                ac2 = list(cartesian(*(range(m) for m in ms2)))
                bad2 = set(c for c in ac2 if c not in good2)

                for c in bad2:
                    phi_c = alpha * fc(c) + psi(c, n2)
                    for i in range(n2):
                        Li = c[(i - 1) % n2]
                        Si = c[i]
                        Ri = c[(i + 1) % n2]
                        out = fs2[i](Li, Si, Ri)
                        if out != Si:
                            lst = list(c)
                            lst[i] = out
                            succ = tuple(lst)
                            if succ in bad2:
                                phi_s = alpha * fc(succ) + psi(succ, n2)
                                if phi_s >= phi_c:
                                    ok_all = False
                                    break
                    if not ok_all:
                        break
                if not ok_all:
                    break

            status = "✓ (also n=6,7,8)" if ok_all else "✓ n=5 only"
            print(f"  α={alpha}: {status}")
            if ok_all:
                break
        else:
            pass  # skip printing all failures

    sys.stdout.flush()


if __name__ == "__main__":
    main()
