#!/usr/bin/env python3
"""Check: does TMid(2,1,1)->0 preserve the TP invariant?
If NOT, then within constant-TP, all interior moves are copy-neighbor,
and the paper's (fc, Psi) argument works WITHOUT Phi_full."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'claude'))
from cup2_theorem import build_system

n = 9; ms, fs = build_system(n)

print(f"TMid(2,1,1) = {fs[4](2,1,1)}")
print()

# TMid(2,1,1)->0 at position j with context L=2,S=1,R=1
# Before: c[j-1]=2, c[j]=1, c[j+1]=1
# After:  c[j-1]=2, c[j]=0, c[j+1]=1
# Int21 at j-1: (c[j-1]=2, c[j]=1) -> 1. After: (c[j-1]=2, c[j]=0) -> 0.
# Delta Int21 = -1 -> NOT TP-preserving
print("TMid(2,1,1)->0 analysis:")
print("  Before: c[j-1]=2, c[j]=1, c[j+1]=1")
print("  Int21 at j-1: (2,1) -> contributes 1")
print("  After:  c[j-1]=2, c[j]=0, c[j+1]=1")
print("  Int21 at j-1: (2,0) -> contributes 0")
print("  Delta Int21 = -1 -> NOT TP-preserving!")
print()

# Check ALL TMid entries: which are privileged + non-copy-neighbor?
print("All TMid privileged entries:")
for L in range(3):
    for S in range(3):
        for R in range(3):
            out = fs[4](L, S, R)
            if out != S:  # privileged
                is_copy = (out == L or out == R)
                tag = "COPY" if is_copy else "ANOMALOUS"
                print(f"  TMid({L},{S},{R})->{out}  {{L,R}}={{{L},{R}}}  {tag}")
print()

# Count ALL privileged entries across all 5 tables
copy_count = 0
anom_count = 0
anom_list = []

# TBot: L in {0,1}, S in {0,1}, R in {0,1,2}
for L in range(2):
    for S in range(2):
        for R in range(3):
            out = fs[0](L, S, R)
            if out != S:
                if out == L or out == R:
                    copy_count += 1
                else:
                    anom_count += 1
                    anom_list.append(f"TBot({L},{S},{R})->{out}")

# TLow: L in {0,1}, S in {0,1,2}, R in {0,1,2}
for L in range(2):
    for S in range(3):
        for R in range(3):
            out = fs[1](L, S, R)
            if out != S:
                if out == L or out == R:
                    copy_count += 1
                else:
                    anom_count += 1
                    anom_list.append(f"TLow({L},{S},{R})->{out}")

# TMid: L,S,R in {0,1,2}
for L in range(3):
    for S in range(3):
        for R in range(3):
            out = fs[4](L, S, R)
            if out != S:
                if out == L or out == R:
                    copy_count += 1
                else:
                    anom_count += 1
                    anom_list.append(f"TMid({L},{S},{R})->{out}")

# THigh: L in {0,1,2}, S in {0,1,2}, R in {0,1}
for L in range(3):
    for S in range(3):
        for R in range(2):
            out = fs[n-2](L, S, R)
            if out != S:
                if out == L or out == R:
                    copy_count += 1
                else:
                    anom_count += 1
                    anom_list.append(f"THigh({L},{S},{R})->{out}")

# TTop: L in {0,1,2}, S in {0,1}, R in {0,1}
for L in range(3):
    for S in range(2):
        for R in range(2):
            out = fs[n-1](L, S, R)
            if out != S:
                if out == L or out == R:
                    copy_count += 1
                else:
                    anom_count += 1
                    anom_list.append(f"TTop({L},{S},{R})->{out}")

print(f"Total privileged: {copy_count + anom_count}")
print(f"Copy-neighbor: {copy_count}")
print(f"Anomalous: {anom_count}")
for a in anom_list:
    print(f"  {a}")
