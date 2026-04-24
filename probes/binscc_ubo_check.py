#!/usr/bin/env python3
"""binscc_ubo_check.py — Check UBO claim against M_5=96 witness.

The M_5=96 witness has ms=[2,2,2,3,4] with consecutive binary at 0,1,2.
UBO claims: for 3 consecutive binary, EVERY good cycle has overlap at P1.
If the witness cycle has NO overlap at P1, UBO is wrong.
"""

import sys
sys.path.insert(0, '.')
from verifier import verify_system

# M_5=96 witness from product96_result.txt
ms = [2, 2, 2, 3, 4]
n = 5

# Build transition functions from the result file
tables = [
    # f[0]: L∈{0..3} (m4=4), S∈{0,1} (m0=2), R∈{0,1} (m1=2)
    {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,
     (1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
     (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0,
     (3,0,0):0,(3,0,1):0,(3,1,0):0,(3,1,1):0},
    # f[1]: L∈{0,1} (m0=2), S∈{0,1} (m1=2), R∈{0,1} (m2=2)
    {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,
     (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1},
    # f[2]: L∈{0,1} (m1=2), S∈{0,1} (m2=2), R∈{0,1,2} (m3=3)
    {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):1,(0,1,1):0,(0,1,2):1,
     (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0},
    # f[3]: L∈{0,1} (m2=2), S∈{0,1,2} (m3=3), R∈{0,1,2,3} (m4=4)
    {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,0,3):0,
     (0,1,0):1,(0,1,1):2,(0,1,2):1,(0,1,3):0,
     (0,2,0):0,(0,2,1):2,(0,2,2):2,(0,2,3):2,
     (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,
     (1,1,0):1,(1,1,1):1,(1,1,2):1,(1,1,3):1,
     (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):1},
    # f[4]: L∈{0,1,2} (m3=3), S∈{0,1,2,3} (m4=4), R∈{0,1} (m0=2)
    {(0,0,0):0,(0,0,1):0,(0,1,0):2,(0,1,1):1,(0,2,0):2,(0,2,1):2,(0,3,0):0,(0,3,1):1,
     (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):0,(1,3,0):3,(1,3,1):0,
     (2,0,0):0,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):3,(2,2,1):0,(2,3,0):3,(2,3,1):0},
]

fs = []
for table in tables:
    def make_f(t):
        def f(L, S, R):
            return t[(L, S, R)]
        return f
    fs.append(make_f(table))

# Verify the system
print("=" * 70)
print("M_5=96 WITNESS VERIFICATION")
print("=" * 70)
print(f"ms = {ms}, product = {2*2*2*3*4}")
print(f"Binary positions: 0, 1, 2 (CONSECUTIVE)")
print()

result = verify_system(ms, fs, verbose=True)
print(f"VALID: {result['valid']}")
if result['valid']:
    print(f"Cycle length: {result['cycle_length']}")
print()

# Now check overlap at P1 (middle of consecutive binary triple)
good_cycle = [(0,0,0,0,0),(1,0,0,0,0),(1,1,0,0,0),(1,1,1,0,0),
              (1,1,1,1,0),(1,1,1,1,1),(0,1,1,1,1),(0,0,1,1,1),
              (0,0,0,1,1),(0,0,0,2,1),(0,0,1,2,1),(0,0,1,0,1),
              (0,0,1,0,2),(0,0,1,2,2),(0,0,1,2,3),(0,0,1,1,3),
              (0,0,0,1,3),(0,0,0,0,3)]

print("=" * 70)
print("OVERLAP CHECK AT P1 (middle of consecutive binary)")
print("=" * 70)

ell = len(good_cycle)
movers = []
for idx in range(ell):
    c = good_cycle[idx]
    c_next = good_cycle[(idx + 1) % ell]
    diffs = [j for j in range(n) if c[j] != c_next[j]]
    movers.append(diffs[0] if len(diffs) == 1 else -1)

print(f"Mover sequence: {movers}")
print()

# Check P1 overlap
for p in range(n):
    mover_ctx = set()
    nonmover_ctx = set()
    for idx in range(ell):
        c = good_cycle[idx]
        ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
        if movers[idx] == p:
            mover_ctx.add(ctx)
        else:
            nonmover_ctx.add(ctx)

    overlap = mover_ctx & nonmover_ctx
    status = "OVERLAP" if overlap else "NO OVERLAP"
    print(f"P{p} (m={ms[p]}): mover_ctx={mover_ctx}")
    print(f"{'':11}nonmover_ctx={nonmover_ctx}")
    print(f"{'':11}overlap={overlap} → {status}")
    print()

# Check: does the cube walk at (c0,c1,c2) visit all 8 vertices?
cube_vertices = set()
for c in good_cycle:
    cube_vertices.add((c[0], c[1], c[2]))
print(f"Cube walk (c0,c1,c2) visits {len(cube_vertices)}/8 vertices: {sorted(cube_vertices)}")
missing = set((a,b,c) for a in range(2) for b in range(2) for c in range(2)) - cube_vertices
print(f"Missing vertices: {sorted(missing)}")

print()
print("=" * 70)
print("CONCLUSION")
print("=" * 70)
print(f"""
The M_5=96 witness has ms=[2,2,2,3,4] with CONSECUTIVE binary at 0,1,2.
Binary P1 (middle of triple) has mover/nonmover overlap: {'YES' if (mover_ctx & nonmover_ctx) else 'NO'}

If NO: UBO ("Universal Binary Overlap") is WRONG for arbitrary good cycles.
The claim "3 consecutive binary → every good cycle has P1 overlap" is false.

UBO may still hold for:
- Cycles that visit all 8 cube vertices
- Uniform sweep cycles
- Cycles with specific structural properties

But NOT for all good cycles unconditionally.
""")
