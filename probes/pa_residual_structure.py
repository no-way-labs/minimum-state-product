"""Understand residual sweep structure at n=9 ms=(2,3,3,2,3,3,2,3,3).

For each residual sample, find fc per proc and walker dynamics.
"""
import sys
sys.setrecursionlimit(20000)
from collections import Counter

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

# Use the known sample
SAMPLE = (0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1)
fc = Counter(SAMPLE)
print(f"Mover word: {SAMPLE}")
print(f"Fire counts: {dict(fc)}")
print()
# Per-proc firing structure
for p in range(N):
    fs = [k for k in range(CL) if SAMPLE[k] == p]
    print(f"p{p} (m={MS[p]}): fires at {fs} (fc={len(fs)})")
print()
# Walker dynamics: position of mover over time
# Track which "side" (left or right) the next mover is
transitions = []
for k in range(CL):
    cur = SAMPLE[k]; nxt = SAMPLE[(k+1)%CL]
    if nxt == left(cur): transitions.append('L')
    elif nxt == right(cur): transitions.append('R')
    elif nxt == cur: transitions.append('S')
    else: transitions.append('?')
print(f"walker transitions: {''.join(transitions)}")

# Turning points: count L/R/S
tc = Counter(transitions)
print(f"  L={tc['L']} R={tc['R']} S={tc['S']}  (cw-ccw = {tc['R']-tc['L']})")
# |disp| check
print(f"  total disp = {tc['R']-tc['L']}  (should be ±2n = ±18)")

# Look for the "wave" structure: is there a pivot where the walker changes direction?
print()
# Compute actual walker positions
walker = [SAMPLE[0]]
for k in range(1, CL+1):
    walker.append(SAMPLE[k % CL])
print(f"walker positions: {walker[:CL]}")

# Find bounces: pairs where walker goes forward then backward or vice versa
bounces = []
for k in range(CL):
    a, b, c = SAMPLE[k], SAMPLE[(k+1)%CL], SAMPLE[(k+2)%CL]
    if (b == right(a) and c == left(b)) or (b == left(a) and c == right(b)):
        bounces.append(k)
print(f"bounces at: {bounces}")
