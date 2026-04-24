#!/usr/bin/env python3
"""Check if Psi strictly decreases on EVERY privileged step.
If yes, cup2Psi alone is a decreasing Nat measure and WF is trivial."""

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
    if frontierTypeVal(a, b) == 1: return W1(n, j)
    return W2(n, j)

def psi(config, n):
    return sum(psiWeightVal(n, j, config[j], config[(j+1)%n]) for j in range(n))

def fc(config, n):
    return sum(1 for j in range(n) if config[j] != config[(j+1)%n])

def fire(config, n, i):
    L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S: return None
    return tuple(list(config[:i]) + [new_S] + list(config[i+1:]))

for n in [5, 6, 7, 8, 9, 10]:
    ms = get_ms(n)
    from itertools import product as iproduct

    psi_increase = 0
    psi_equal = 0
    psi_decrease = 0
    total = 0

    for config in iproduct(*[range(m) for m in ms]):
        old_psi = psi(config, n)
        for i in range(n):
            new_config = fire(config, n, i)
            if new_config is None:
                continue
            total += 1
            new_psi = psi(new_config, n)
            if new_psi > old_psi:
                psi_increase += 1
                if psi_increase <= 3 and n == 5:
                    print(f"  PSI INCREASE n={n}: {config} fire {i}")
                    print(f"    psi: {old_psi} -> {new_psi}, fc: {fc(config,n)} -> {fc(new_config,n)}")
            elif new_psi == old_psi:
                psi_equal += 1
            else:
                psi_decrease += 1

    print(f"n={n}: {total} steps. Psi increase: {psi_increase}, equal: {psi_equal}, decrease: {psi_decrease}")
    if psi_increase == 0 and psi_equal == 0:
        print(f"  *** Psi STRICTLY DECREASES on ALL steps! ***")
    elif psi_increase == 0:
        print(f"  *** Psi NON-INCREASING on all steps (but {psi_equal} with equal) ***")
