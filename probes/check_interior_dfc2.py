#!/usr/bin/env python3
"""Check ALL interior (TMidVal) transitions including Δfc=0"""

def TMidVal(L, S, R):
    if L == S and S == R: return S
    if L == S: return S
    if S == R: return S
    if L == R: return L
    return L

def localFcBefore(L, S, R):
    return (0 if L == S else 1) + (0 if S == R else 1)

def localFcAfter(L, S, R, out):
    return (0 if L == out else 1) + (0 if out == R else 1)

def main():
    print("ALL TMidVal transitions (including identity):")
    all_entries = []
    for L in range(3):
        for S in range(3):
            for R in range(3):
                out = TMidVal(L, S, R)
                fc_before = localFcBefore(L, S, R)
                fc_after = localFcAfter(L, S, R, out)
                dfc = fc_after - fc_before
                priv = "PRIV" if out != S else "iden"
                all_entries.append((L, S, R, out, dfc, priv))

    # Show all privileged
    print("\nPrivileged transitions:")
    dfc_set = set()
    for L, S, R, out, dfc, priv in all_entries:
        if priv == "PRIV":
            dfc_set.add(dfc)
            print(f"  ({L},{S},{R})->{out}: Δfc={dfc}")

    print(f"\nΔfc values for privileged interior: {sorted(dfc_set)}")
    print(f"Δfc ≤ 0 for ALL: {all(d <= 0 for d in dfc_set)}")

    hop = [(L,S,R,out) for L,S,R,out,dfc,p in all_entries if p=="PRIV" and dfc==0]
    neg = [(L,S,R,out) for L,S,R,out,dfc,p in all_entries if p=="PRIV" and dfc<0]
    print(f"\nHop (Δfc=0): {len(hop)} entries: {hop}")
    print(f"Neg (Δfc<0): {len(neg)} entries")

if __name__ == '__main__':
    main()
