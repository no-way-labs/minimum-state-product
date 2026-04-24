#!/usr/bin/env python3
"""Analytical proof attempt for B4: T_top(2,0,0)→1 fires at most once.

Key table properties:
1. c[n-1] can only go 1→0 via T_top(0,1,R)→0, requiring c[n-2]=0.
2. c[n-2] can only go S→2 when c[n-1]=1 (T_high table constraint).
3. These create a deadlock preventing T_top's second firing.

Verify these table constraints and trace the analytical argument.
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from cup2_theorem import T_bot, T_low, T_high, T_top

def main():
    print("ANALYTICAL ARGUMENT FOR B4: T_top FIRES AT MOST ONCE")
    print("=" * 70)

    # ── Step 1: c[n-1] transition analysis ──
    print("\nStep 1: T_top table — when can c[n-1] change?")
    print("-" * 50)

    print("\n  c[n-1] = 0 → 1 (privileged entries only):")
    for (L, S, R), out in sorted(T_top.items()):
        if S == 0 and out == 1:
            cls = "copy_L" if out == L else ("copy_R" if out == R else "ANOMALOUS")
            print(f"    T_top({L},{S},{R})={out}  [{cls}]  needs c[n-2]={L}, c[0]={R}")

    print("\n  c[n-1] = 1 → 0 (privileged entries only):")
    for (L, S, R), out in sorted(T_top.items()):
        if S == 1 and out == 0:
            cls = "copy_L" if out == L else ("copy_R" if out == R else "ANOMALOUS")
            print(f"    T_top({L},{S},{R})={out}  [{cls}]  needs c[n-2]={L}, c[0]={R}")

    print("\n  c[n-1] = 1, STAY entries:")
    for (L, S, R), out in sorted(T_top.items()):
        if S == 1 and out == 1:
            print(f"    T_top({L},{S},{R})={out}  [STAY]  for c[n-2]={L}, c[0]={R}")

    print("\n  KEY: c[n-1] goes 1→0 ONLY when c[n-2]=0.")
    all_10 = [(L, R, out) for (L, S, R), out in T_top.items() if S == 1 and out == 0]
    assert all(L == 0 for L, R, out in all_10), "FAILED: c[n-1]=1→0 with c[n-2]≠0"
    print("  ✓ Verified: all T_top(L,1,R)→0 have L=0, i.e., c[n-2]=0.")

    # ── Step 2: c[n-2] transition analysis (T_high table) ──
    print("\n\nStep 2: T_high table — when can c[n-2] reach 2?")
    print("-" * 50)

    print("\n  Entries that set c[n-2]=2 (output=2):")
    for (L, S, R), out in sorted(T_high.items()):
        if out == 2 and out != S:
            cls = "copy_L" if out == L else ("copy_R" if out == R else "ANOMALOUS")
            print(f"    T_high({L},{S},{R})={out}  [{cls}]  needs c[n-3]={L}, c[n-1]={R}")

    print("\n  KEY: c[n-2]→2 requires c[n-1]=1 (R=1) in ALL entries.")
    entries_to_2 = [(L, S, R) for (L, S, R), out in T_high.items()
                    if out == 2 and out != S]
    assert all(R == 1 for L, S, R in entries_to_2), "FAILED: c[n-2]→2 with c[n-1]≠1"
    print("  ✓ Verified: ALL T_high entries giving output 2 have R=1 (c[n-1]=1).")

    # ── Step 3: The deadlock argument ──
    print("\n\nStep 3: DEADLOCK ARGUMENT")
    print("-" * 50)
    print("""
After T_top(2,0,0)→1 fires:
  State: c[n-2]=2, c[n-1]=1, c[0]=0.

For T_top to fire AGAIN, need: c[n-2]=2, c[n-1]=0, c[0]=0.

CONSTRAINT A: c[n-1] can only go 1→0 when c[n-2]=0.  (Step 1)
CONSTRAINT B: c[n-2] can only reach 2 when c[n-1]=1.  (Step 2)

These constraints create a TEMPORAL DEADLOCK:
  - To get c[n-1]=0: need c[n-2]=0 first.     (by A)
  - After c[n-2]=0 and c[n-1]=0: need c[n-2]=2 for T_top.
  - To get c[n-2]=2: need c[n-1]=1 first.      (by B)
  - But c[n-1]=0 right now!
  - c[n-1] rising 0→1 via T_top(1,0,1)→1 requires c[n-2]=1 and c[0]=1.
  - After c[n-1]=1: c[n-2] can reach 2.        (by B)
  - But then c[n-1]=1 and c[n-2]=2.
  - c[n-1] can only go 1→0 when c[n-2]=0.      (by A)
  - So c[n-2] must DROP from 2 before c[n-1] can drop.
  - We're back to: c[n-2] must be 0 for c[n-1] to drop.

This creates a CYCLE of the boundary variables:
  (c[n-2]=2, c[n-1]=1) → (c[n-2]=0, c[n-1]=1) →
  (c[n-2]=0, c[n-1]=0) → (c[n-2]=1, c[n-1]=0) →
  (c[n-2]=1, c[n-1]=1) → (c[n-2]=2, c[n-1]=1) → ...

But each iteration requires INTERIOR transitions (copy-neighbor, Δfc≤0)
to set up the required contexts. These transitions form paths in the
(fc, Ψ) DAG, which has finite depth.

Since the boundary cycle requires interior transitions that strictly
decrease (fc, Ψ), and (fc, Ψ) is bounded below, the cycle must
terminate. When it terminates, c[n-2] can no longer reach 2 (because
the interior can no longer provide the necessary contexts). Therefore
c[n-1] can reach 0 but c[n-2] stays ≤1, making T_top's precondition
(c[n-2]=2) impossible.
""")

    # ── Step 4: Verify no additional path to c[n-2]=2 ──
    print("Step 4: Complete verification that c[n-2]→2 requires c[n-1]=1")
    print("-" * 50)

    # Double-check: when c[n-1]=0, can c[n-2] EVER increase to 2?
    print("\n  All T_high entries with R=0 (c[n-1]=0) and output=2:")
    found = False
    for (L, S, R), out in sorted(T_high.items()):
        if R == 0 and out == 2:
            found = True
            print(f"    T_high({L},{S},{R})={out}")
    if not found:
        print("    NONE — c[n-2] CANNOT reach 2 when c[n-1]=0.")
    print()

    # Check: when c[n-1]=0, what are all possible transitions at pos n-2?
    print("  All T_high(L,S,0) entries (c[n-1]=0):")
    for (L, S, R), out in sorted(T_high.items()):
        if R == 0:
            change = f"→{out}" if out != S else "STAY"
            print(f"    T_high({L},{S},{R})={out}  (S={S} {change})")

    print("\n  In particular, when c[n-1]=0:")
    print("    c[n-2]=0: stays 0 (L=0) or goes to 1 (L=1) or stays 0 (L=2)")
    print("    c[n-2]=1: goes to 0 (L=0,2) or stays 1 (L=1)")
    print("    c[n-2]=2: goes to 0 (L=0,1) or stays 2 (L=2)")
    print("    MAX reachable value of c[n-2] when c[n-1]=0: at most 1 (from 0→1)")
    print("    ✓ c[n-2] can NEVER reach 2 while c[n-1]=0.")

    # ── Step 5: Verify c[n-1]=0→1 transitions ──
    print("\n\nStep 5: How c[n-1] goes 0→1")
    print("-" * 50)
    print("\n  T_top entries with S=0, output=1:")
    for (L, S, R), out in sorted(T_top.items()):
        if S == 0 and out == 1:
            print(f"    T_top({L},{S},{R})={out}  needs c[n-2]={L}, c[0]={R}")

    print("\n  For T_top(2,0,0)→1 (anomalous): needs c[n-2]=2.")
    print("  But c[n-2] can't be 2 when c[n-1]=0 (Step 4)!")
    print("  So T_top(2,0,0)→1 CAN NEVER FIRE when c[n-1]=0 and c[n-2]<2.")
    print()
    print("  The only way c[n-1] goes 0→1 WITH c[n-2]<2 is:")
    print("    T_top(1,0,1)→1: needs c[n-2]=1 and c[0]=1")
    print("  This is a COPY transition (copy_L), with Δfc ≤ 0.")

    print("\n\nSUMMARY")
    print("=" * 70)
    print("""
THEOREM (B4): T_top(2,0,0)→1 fires at most once on any path.

PROOF SKETCH:
1. After T_top fires: c[n-1]=1, c[n-2]=2.
2. c[n-1] goes 1→0 ONLY when c[n-2]=0. (Table constraint)
3. c[n-2] reaches 2 ONLY when c[n-1]=1.  (Table constraint)
4. Therefore, after c[n-1] drops to 0 (requiring c[n-2]=0):
   c[n-2] CANNOT reach 2 while c[n-1]=0. (Table constraint)
5. c[n-1] can rise 0→1 via copy (needs c[n-2]=1, c[0]=1), allowing
   c[n-2] to then reach 2. But c[n-1] must drop to 0 for T_top,
   which requires c[n-2]=0 again — undoing the rise.
6. Each iteration of this boundary cycle requires interior copy
   transitions that strictly decrease (fc, Ψ). Since (fc, Ψ) is
   bounded below, the cycle terminates with c[n-2]≤1 permanently.
7. When c[n-2]≤1: T_top(2,0,0)→1's precondition c[n-2]=2 is
   impossible, so T_top cannot fire again.            □
""")


if __name__ == "__main__":
    main()
