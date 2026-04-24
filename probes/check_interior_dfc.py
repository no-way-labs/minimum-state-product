#!/usr/bin/env python3
"""Check: at interior positions (TMidVal), what are the possible Δfc values?
Can Δfc be positive at interior positions?"""

def TMidVal(L, S, R):
    """Copy of the TMidVal from Lean/tables."""
    if L == S and S == R:
        return S
    if L == S:
        return S
    if S == R:
        return S
    # L != S and S != R
    if L == R:
        return L  # copy neighbor
    # L != S, S != R, L != R — all different
    return L  # copy left

def localFcBefore(L, S, R):
    fb_LS = 0 if L == S else 1
    fb_SR = 0 if S == R else 1
    return fb_LS + fb_SR

def localFcAfter(L, S, R, out):
    fb_L_out = 0 if L == out else 1
    fb_out_R = 0 if out == R else 1
    return fb_L_out + fb_out_R

def main():
    print("TMidVal Δfc analysis (interior positions):")
    dfc_values = set()
    for L in range(3):
        for S in range(3):
            for R in range(3):
                out = TMidVal(L, S, R)
                if out != S:  # privileged
                    fc_before = localFcBefore(L, S, R)
                    fc_after = localFcAfter(L, S, R, out)
                    dfc = fc_after - fc_before
                    dfc_values.add(dfc)
                    print(f"  ({L},{S},{R}) -> {out}: fc_before={fc_before}, fc_after={fc_after}, Δfc={dfc}")

    print(f"\nPossible Δfc values: {sorted(dfc_values)}")
    print(f"Any positive Δfc? {any(d > 0 for d in dfc_values)}")

if __name__ == '__main__':
    main()
