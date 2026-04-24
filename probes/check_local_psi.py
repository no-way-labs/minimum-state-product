#!/usr/bin/env python3
"""Check local psi changes for ALL position types.
Local psi = psiWeight at positions adjacent to the mover.
If local psi ALWAYS decreases, then global Psi = sum of local psi also always decreases."""

def TBotVal(L,S,R):
    t = {(0,0,0):1,(0,0,1):1,(0,0,2):0,(0,1,0):1,(0,1,1):1,(0,1,2):1,(1,0,0):0,(1,0,1):1,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):0}
    return t.get((L,S,R), 0)
def TLowVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2}
    return t.get((L,S,R), 0)
def TMidVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):0,(1,0,0):1,(1,0,1):1,(1,0,2):1,(1,1,0):1,(1,1,1):1,(1,1,2):2,(1,2,0):0,(1,2,1):1,(1,2,2):2,(2,0,0):0,(2,0,1):0,(2,0,2):2,(2,1,0):1,(2,1,1):2,(2,1,2):2,(2,2,0):0,(2,2,1):2,(2,2,2):2}
    return t.get((L,S,R), 0)
def THighVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):2,(1,2,0):0,(1,2,1):2,(2,0,0):0,(2,0,1):2,(2,1,0):0,(2,1,1):2,(2,2,0):2,(2,2,1):2}
    return t.get((L,S,R), 0)
def TTopVal(L,S,R):
    t = {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1}
    return t.get((L,S,R), 0)

def frontierTypeVal(a, b):
    if a == b: return 0
    return (b + 3 - a) % 3

def W1(n, j):
    if j + 1 == n: return 0
    if j + 2 == n: return 1
    return j + 1

def W2(n, j):
    if j + 1 == n: return 0
    if j == 0: return n - 1
    return n - 1 - j

def psiWeight(n, j, a, b):
    if a == b: return 0
    if frontierTypeVal(a, b) == 1: return W1(n, j)
    return W2(n, j)

def frontierBit(a, b):
    return 0 if a == b else 1

def localPsiBefore(n, j, LL, L, S, R, RR):
    """Psi at positions j-1 and j (the two edges affected by firing at position j)."""
    # Edge at position j-1: between c[j-1]=L and c[j]=S
    # Edge at position j: between c[j]=S and c[j+1]=R
    psi_left = psiWeight(n, (j-1)%n, L, S)
    psi_right = psiWeight(n, j, S, R)
    return psi_left + psi_right

def localPsiAfter(n, j, LL, L, S_new, R, RR):
    """Psi at positions j-1 and j after S changes to S_new."""
    psi_left = psiWeight(n, (j-1)%n, L, S_new)
    psi_right = psiWeight(n, j, S_new, R)
    return psi_left + psi_right

def localFcBefore(L, S, R):
    return frontierBit(L, S) + frontierBit(S, R)

def localFcAfter(L, S_new, R):
    return frontierBit(L, S_new) + frontierBit(S_new, R)

# Check ALL transitions for TMid (the most common position type)
print("TMid transitions: all (L, S, R) where TMidVal(L,S,R) != S")
print("="*80)

n = 20  # Use a large n so weights are generic
for L in range(3):
    for S in range(3):
        for R in range(3):
            S_new = TMidVal(L, S, R)
            if S_new == S:
                continue
            old_fc = localFcBefore(L, S, R)
            new_fc = localFcAfter(L, S_new, R)
            fc_dir = "=" if new_fc == old_fc else ("+" if new_fc > old_fc else "-")

            # Check local psi for a generic interior position j
            j = 10  # generic middle position
            old_psi = localPsiBefore(n, j, 0, L, S, R, 0)
            new_psi = localPsiAfter(n, j, 0, L, S_new, R, 0)
            psi_dir = "=" if new_psi == old_psi else ("+" if new_psi > old_psi else "-")

            print(f"  TMid({L},{S},{R})={S_new}: localFc {old_fc}->{new_fc} ({fc_dir}), localPsi {old_psi}->{new_psi} ({psi_dir})")

print()
print("TBot transitions:")
for L in range(2):
    for S in range(2):
        for R in range(3):
            S_new = TBotVal(L, S, R)
            if S_new == S:
                continue
            old_fc = localFcBefore(L, S, R)
            new_fc = localFcAfter(L, S_new, R)
            fc_dir = "=" if new_fc == old_fc else ("+" if new_fc > old_fc else "-")
            j = 0
            old_psi = localPsiBefore(n, j, 0, L, S, R, 0)
            new_psi = localPsiAfter(n, j, 0, L, S_new, R, 0)
            psi_dir = "=" if new_psi == old_psi else ("+" if new_psi > old_psi else "-")
            print(f"  TBot({L},{S},{R})={S_new}: localFc {old_fc}->{new_fc} ({fc_dir}), localPsi {old_psi}->{new_psi} ({psi_dir})")

print()
print("TLow transitions:")
for L in range(2):
    for S in range(3):
        for R in range(3):
            S_new = TLowVal(L, S, R)
            if S_new == S:
                continue
            old_fc = localFcBefore(L, S, R)
            new_fc = localFcAfter(L, S_new, R)
            fc_dir = "=" if new_fc == old_fc else ("+" if new_fc > old_fc else "-")
            j = 1
            old_psi = localPsiBefore(n, j, 0, L, S, R, 0)
            new_psi = localPsiAfter(n, j, 0, L, S_new, R, 0)
            psi_dir = "=" if new_psi == old_psi else ("+" if new_psi > old_psi else "-")
            print(f"  TLow({L},{S},{R})={S_new}: localFc {old_fc}->{new_fc} ({fc_dir}), localPsi {old_psi}->{new_psi} ({psi_dir})")

print()
print("THigh transitions:")
for L in range(3):
    for S in range(3):
        for R in range(2):
            S_new = THighVal(L, S, R)
            if S_new == S:
                continue
            old_fc = localFcBefore(L, S, R)
            new_fc = localFcAfter(L, S_new, R)
            fc_dir = "=" if new_fc == old_fc else ("+" if new_fc > old_fc else "-")
            j = n - 2
            old_psi = localPsiBefore(n, j, 0, L, S, R, 0)
            new_psi = localPsiAfter(n, j, 0, L, S_new, R, 0)
            psi_dir = "=" if new_psi == old_psi else ("+" if new_psi > old_psi else "-")
            print(f"  THigh({L},{S},{R})={S_new}: localFc {old_fc}->{new_fc} ({fc_dir}), localPsi {old_psi}->{new_psi} ({psi_dir})")

print()
print("TTop transitions:")
for L in range(3):
    for S in range(2):
        for R in range(2):
            S_new = TTopVal(L, S, R)
            if S_new == S:
                continue
            old_fc = localFcBefore(L, S, R)
            new_fc = localFcAfter(L, S_new, R)
            fc_dir = "=" if new_fc == old_fc else ("+" if new_fc > old_fc else "-")
            j = n - 1
            old_psi = localPsiBefore(n, j, 0, L, S, R, 0)
            new_psi = localPsiAfter(n, j, 0, L, S_new, R, 0)
            psi_dir = "=" if new_psi == old_psi else ("+" if new_psi > old_psi else "-")
            print(f"  TTop({L},{S},{R})={S_new}: localFc {old_fc}->{new_fc} ({fc_dir}), localPsi {old_psi}->{new_psi} ({psi_dir})")

# Summary: count how many transitions have local psi increase vs decrease
print("\n" + "="*80)
print("SUMMARY: transitions with localPsi increase (for generic middle position)")
tables = [
    ("TMid", TMidVal, range(3), range(3), range(3), 10),
    ("TBot", TBotVal, range(2), range(2), range(3), 0),
    ("TLow", TLowVal, range(2), range(3), range(3), 1),
    ("THigh", THighVal, range(3), range(3), range(2), n-2),
    ("TTop", TTopVal, range(3), range(2), range(2), n-1),
]
for name, func, Lr, Sr, Rr, j in tables:
    inc_count = 0
    dec_count = 0
    eq_count = 0
    total = 0
    for L in Lr:
        for S in Sr:
            for R in Rr:
                S_new = func(L, S, R)
                if S_new == S:
                    continue
                total += 1
                old_psi = localPsiBefore(n, j, 0, L, S, R, 0)
                new_psi = localPsiAfter(n, j, 0, L, S_new, R, 0)
                if new_psi > old_psi:
                    inc_count += 1
                elif new_psi < old_psi:
                    dec_count += 1
                else:
                    eq_count += 1
    print(f"  {name}: {total} trans, localPsi↑:{inc_count}, =:{eq_count}, ↓:{dec_count}")
