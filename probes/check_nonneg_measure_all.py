#!/usr/bin/env python3
"""Check if the REAL nonneg measure (n-fc, Psi) Lex-decreases on ALL bad steps,
not just fc-nondecreasing ones. If yes, cup2BadStepNonneg_wf already handles
everything and we don't need the CF/drop split at all."""

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

def get_ms(n):
    ms = [3]*n; ms[0] = 2; ms[n-1] = 2; return ms

def get_trans(n, i, L, S, R):
    if i == 0: return TBotVal(L, S, R)
    if i == 1: return TLowVal(L, S, R)
    if i == n-1: return TTopVal(L, S, R)
    if i == n-2: return THighVal(L, S, R)
    return TMidVal(L, S, R)

# Real CUP-2 definitions from CopyDAG.lean
def frontierBitVal(a, b):
    return 0 if a == b else 1

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

def psiWeightVal(n, j, a, b):
    if a == b: return 0
    if frontierTypeVal(a, b) == 1:
        return W1(n, j)
    return W2(n, j)

def fc(config, n):
    total = 0
    for j in range(n):
        a = config[j]
        b = config[(j+1) % n]
        total += frontierBitVal(a, b)
    return total

def psi(config, n):
    total = 0
    for j in range(n):
        a = config[j]
        b = config[(j+1) % n]
        total += psiWeightVal(n, j, a, b)
    return total

def nonneg_measure(config, n):
    """Returns (n - fc, psi) as a Lex pair."""
    return (n - fc(config, n), psi(config, n))

def fire(config, n, i):
    ms = get_ms(n)
    L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S: return None
    new_config = list(config); new_config[i] = new_S
    return tuple(new_config)

def lex_lt(a, b):
    """a <_lex b (strictly less)"""
    if a[0] < b[0]: return True
    if a[0] == b[0] and a[1] < b[1]: return True
    return False

for n in [5, 6, 7, 8, 9, 10]:
    print(f"\nn={n}:")
    ms = get_ms(n)
    from itertools import product as iproduct
    ranges = [range(m) for m in ms]

    violations = 0
    total = 0
    for config in iproduct(*ranges):
        old_m = nonneg_measure(config, n)
        for i in range(n):
            new_config = fire(config, n, i)
            if new_config is None:
                continue
            total += 1
            new_m = nonneg_measure(new_config, n)
            if not lex_lt(new_m, old_m):
                violations += 1
                if violations <= 5:
                    old_fc_val = fc(config, n)
                    new_fc_val = fc(new_config, n)
                    print(f"  VIOLATION: {config} fire {i}, fc {old_fc_val}->{new_fc_val}")
                    print(f"    measure: ({old_m[0]},{old_m[1]}) -> ({new_m[0]},{new_m[1]})")

    print(f"  Total privileged steps: {total}, violations: {violations}")
    if violations == 0:
        print(f"  *** (n-fc, Psi) Lex-decreases on ALL steps! ***")
