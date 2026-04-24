#!/usr/bin/env python3
"""Check: do B1-B4 preserve the TP invariant?
If some don't, the classification is more nuanced."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system

n = 9; ms, fs = build_system(n)

def tp(c):
    e = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    i21 = sum(1 for j in range(2,n-2) if c[j]==2 and c[(j+1)%n]==1)
    w = sum(j for j in range(2,n-2) if c[j]==2 and c[(j+1)%n] in (0,1))
    return (e, i21, w)

def move(c, pos):
    L = c[(pos-1)%n]; S = c[pos]; R = c[(pos+1)%n]
    c2 = list(c); c2[pos] = fs[pos](L, S, R); return tuple(c2)

# For each B1-B4 entry, check ALL possible configs where it fires,
# and see if TP is preserved.

anomalous = [
    ("B1", 0, 0, 0, 0),  # TBot(0,0,0)->1 at position 0; context: c[n-1]=0, c[0]=0, c[1]=0
    ("B2", 0, 1, 1, 2),  # TBot(1,1,2)->0 at position 0; context: c[n-1]=1, c[0]=1, c[1]=2
    ("B3", n-2, 1, 1, 1),  # THigh(1,1,1)->2 at position n-2; context: c[n-3]=1, c[n-2]=1, c[n-1]=1
    ("B4", n-1, 2, 0, 0),  # TTop(2,0,0)->1 at position n-1; context: c[n-2]=2, c[n-1]=0, c[0]=0
]

N = 1
for m in ms: N *= m

def idx_to_config(idx):
    c = []
    for m in reversed(ms):
        c.append(idx % m); idx //= m
    return tuple(reversed(c))

for name, pos, L_val, S_val, R_val in anomalous:
    tp_preserved = 0
    tp_broken = 0
    tp_changes = set()

    for idx in range(N):
        c = idx_to_config(idx)
        # Check if this config has the right context for this anomalous entry
        L_pos = (pos - 1) % n
        R_pos = (pos + 1) % n
        if c[L_pos] == L_val and c[pos] == S_val and c[R_pos] == R_val:
            c2 = move(c, pos)
            t1 = tp(c)
            t2 = tp(c2)
            if t1 == t2:
                tp_preserved += 1
            else:
                tp_broken += 1
                delta = (t2[0]-t1[0], t2[1]-t1[1], t2[2]-t1[2])
                tp_changes.add(delta)

    print(f"{name} at position {pos}: TPreserved={tp_preserved}, TBroken={tp_broken}")
    if tp_changes:
        print(f"  TP changes: {tp_changes}")
    print()
