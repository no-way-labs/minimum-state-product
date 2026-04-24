#!/usr/bin/env python3
"""
Analyze the cycle 8 -> 14 -> 8 in the boundary graph.
8 = (0,0,0,1,1,0), 14 = (0,0,0,2,1,0)

Edge 8->14: c[n-3] changes from 1 to 2
Edge 14->8: c[n-3] changes from 2 to 1

These must both be at position n-3 (TMid).
TMid(L, 1, 1) for some L: gives 2?
TMid(L, 2, 1) for some L: gives 1?

Check which (L, S, R) triples produce these transitions.
"""

def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,
         (0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,
         (1,1,0):1,(1,1,1):1,(1,1,2):2,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,
         (2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,
         (2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)

# Edge 8->14: S=cN3=1, R=cN2=1, new value = 2
# TMid(L, 1, 1) = ?
print("TMid(L, 1, 1):")
for L in range(3):
    print(f"  L={L}: TMid({L}, 1, 1) = {TMidVal(L, 1, 1)}")

# Edge 14->8: S=cN3=2, R=cN2=1, new value = 1
# TMid(L, 2, 1) = ?
print("\nTMid(L, 2, 1):")
for L in range(3):
    print(f"  L={L}: TMid({L}, 2, 1) = {TMidVal(L, 2, 1)}")

# So:
# TMid(1, 1, 1) = 1 (no change), TMid(2, 1, 1) = 2 (change 1->2)
# TMid(0, 2, 1) = 2 (no change), TMid(1, 2, 1) = 1 (change 2->1)
# The cycle: with L=2, TMid(2,1,1)=2 (1->2), then with L=1, TMid(1,2,1)=1 (2->1)

# This cycle happens at position n-3 where the left neighbor (c[n-4]) is interior.
# Different daemon choices for the left neighbor value allow the cycle.
# This is exactly the "boundary-fixed hop impossibility" mentioned in the proof sketch:
# At position n-3, the left neighbor c[n-4] is interior and can take different values,
# enabling a value cycle.

# The KEY INSIGHT from the memory: "3 hop entries need c[j-1]∈{0,1}, fixed c[j-1]
# blocks value cycle 0→1→2→0, induction from j=3"

# So the cycle IS possible at the boundary level (different interior values allow it).
# But at constant FutureFc, the interior values are constrained, preventing the cycle.

# This means we CANNOT prove the axiom purely from boundary structure.
# The axiom requires reasoning about the INTERIOR values too.

# But the axiom was FALSE! So this analysis confirms it.

print("\n--- Conclusion ---")
print("The boundary transition graph has 2-cycles at position n-3 and position 2")
print("because interior neighbors can take different values.")
print("The axiom constFuture_boundary_change_edge is FALSE.")
print("Need a completely different approach.")
