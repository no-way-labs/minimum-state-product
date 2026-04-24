#!/usr/bin/env python3
"""Check interior Δfc with CORRECT TMidVal from Lean tables"""

TMidTable = {
    (0,0,0):0, (0,0,1):0, (0,0,2):0,
    (0,1,0):0, (0,1,1):1, (0,1,2):0,
    (0,2,0):0, (0,2,1):2, (0,2,2):0,
    (1,0,0):1, (1,0,1):1, (1,0,2):1,
    (1,1,0):1, (1,1,1):1, (1,1,2):2,
    (1,2,0):0, (1,2,1):1, (1,2,2):2,
    (2,0,0):0, (2,0,1):0, (2,0,2):2,
    (2,1,0):1, (2,1,1):2, (2,1,2):2,
    (2,2,0):0, (2,2,1):2, (2,2,2):2,
}

def TMidVal(L, S, R):
    return TMidTable.get((L, S, R), 0)

def localFcBefore(L, S, R):
    return (0 if L == S else 1) + (0 if S == R else 1)

def localFcAfter(L, S, R, out):
    return (0 if L == out else 1) + (0 if out == R else 1)

print("ALL TMidVal privileged transitions:")
dfc_set = set()
hop = []
neg = []
for L in range(3):
    for S in range(3):
        for R in range(3):
            out = TMidVal(L, S, R)
            if out != S:
                fb = localFcBefore(L, S, R)
                fa = localFcAfter(L, S, R, out)
                dfc = fa - fb
                dfc_set.add(dfc)
                print(f"  ({L},{S},{R})->{out}: Δfc={dfc}")
                if dfc == 0:
                    hop.append((L,S,R,out))
                else:
                    neg.append((L,S,R,out,dfc))

print(f"\nΔfc values: {sorted(dfc_set)}")
print(f"Hop (Δfc=0): {hop}")
print(f"Neg (Δfc<0): {[(L,S,R,out,d) for L,S,R,out,d in neg]}")
print(f"\nΔfc ≤ 0 for ALL interior privileged: {all(d <= 0 for d in dfc_set)}")
