#!/usr/bin/env python3
"""Debug: is edge (52,4) in fc_nondec_edges?"""

def encode(c0, c1, c2, cN3, cN2, cN1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cN3) * 3 + cN2) * 2 + cN1

def TMidVal(L,S,R):
    t={(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R),0)

def delta_fc(L, S, R, S_new):
    return ((1 if L != S_new else 0) - (1 if L != S else 0) +
            (1 if S_new != R else 0) - (1 if S != R else 0))

# Check: encode(0,0,2,2,2,0) = ?
print(f'encode(0,0,2,2,2,0) = {encode(0,0,2,2,2,0)}')
print(f'encode(0,0,0,2,2,0) = {encode(0,0,0,2,2,0)}')

# Check P2 at (c0=0,c1=0,c2=2,cN3=2,cN2=2,cN1=0):
for c3 in range(3):
    nc2 = TMidVal(0, 2, c3)
    if nc2 != 2:
        d = delta_fc(0, 2, c3, nc2)
        se2 = encode(0, 0, nc2, 2, 2, 0)
        print(f'  c3={c3}: nc2={nc2}, delta={d}, se2={se2}')
        print(f'  Edge: (52, {se2}), nondec: {d >= 0}')

# The ACTUAL n=5 config: c=(0,0,2,2,0), 6-tuple is:
# c[0]=0, c[1]=0, c[2]=2, c[n-3]=c[2]=2, c[n-2]=c[3]=2, c[n-1]=c[4]=0
# So 6-tuple = (0,0,2,2,2,0) ← encode = 52
# After move at pos 2: c'=(0,0,0,2,0), 6-tuple = (0,0,0,0,2,0)
# c'[0]=0, c'[1]=0, c'[2]=0, c'[n-3]=c'[2]=0, c'[n-2]=c'[3]=2, c'[n-1]=c'[4]=0
# encode(0,0,0,0,2,0) = ?
print(f'\nActual n=5 target 6-tuple: encode(0,0,0,0,2,0) = {encode(0,0,0,0,2,0)}')
print(f'Reported target: 4')
print(f'encode(0,0,0,2,2,0) = {encode(0,0,0,2,2,0)}')

# AHA! At n=5, the 6-tuple overlaps:
# c[2] = c[n-3] when n=5 (both are position 2)
# So when c[2] changes from 2 to 0, BOTH c2 AND cN3 change!
# The fc-nondec code assumes they're independent.
