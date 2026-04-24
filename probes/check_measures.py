#!/usr/bin/env python3
"""Check various candidate measures for ALL bad steps (not just nonneg).
Goal: find a single measure that strictly decreases on every bad step."""

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
    ms = [3]*n
    ms[0] = 2; ms[n-1] = 2
    return ms

def get_trans(n, i, L, S, R):
    if i == 0: return TBotVal(L, S, R)
    if i == 1: return TLowVal(L, S, R)
    if i == n-1: return TTopVal(L, S, R)
    if i == n-2: return THighVal(L, S, R)
    return TMidVal(L, S, R)

def frontier_bit(L, S, R):
    return 1 if (S != L and S != R) else 0

def fc(config, n):
    total = 0
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        total += frontier_bit(L, S, R)
    return total

def psi_term(n, i, L, S, R):
    """Psi contribution at position i — needs actual definition from CopyDAG"""
    # Psi = sum of psiTerm. From CopyDAG, psiTerm involves frontier bit * weight.
    # Let me use the definition: psiTerm = n * frontierBit + copyLRweight
    # Actually I need the exact definition. Let me just check (n-fc, psi) where
    # psi is any reasonable sum.
    # For now, let me check (fc, n-fc, psi) with various psi definitions.
    # Let me use: psi = sum of (n - i) * frontier_bit at each position
    fb = frontier_bit(L, S, R)
    return (n - i) * fb

def psi(config, n):
    total = 0
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        total += psi_term(n, i, L, S, R)
    return total

def fire(config, n, i):
    ms = get_ms(n)
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S:
        return None
    new_config = list(config)
    new_config[i] = new_S
    return tuple(new_config)

def check_measure(n, measure_fn, name):
    """Check if measure_fn strictly decreases on every privileged step"""
    ms = get_ms(n)
    from itertools import product
    ranges = [range(m) for m in ms]

    violations = 0
    total = 0
    for config in product(*ranges):
        old_m = measure_fn(config, n)
        for i in range(n):
            new_config = fire(config, n, i)
            if new_config is None:
                continue
            total += 1
            new_m = measure_fn(new_config, n)
            if new_m >= old_m:
                violations += 1
                if violations <= 3:
                    print(f"    VIOLATION: {config} fire {i} -> {new_config}")
                    print(f"      measure: {old_m} -> {new_m}")

    print(f"  {name}: {violations}/{total} violations")
    return violations

# Try various single-Nat measures
for n in [5, 6, 7]:
    print(f"\nn={n}:")

    # Measure 1: fc * big + psi (handles fc-drop, nonneg with fc preserved)
    def m1(c, n):
        return fc(c,n) * 1000 + psi(c,n)
    check_measure(n, m1, "fc*1000 + psi")

    # Measure 2: (n-fc) * big + psi (handles nonneg)
    def m2(c, n):
        return (n - fc(c,n)) * 1000 + psi(c,n)
    check_measure(n, m2, "(n-fc)*1000 + psi")

    # Measure 3: Just psi
    check_measure(n, lambda c,n: psi(c,n), "psi alone")

    # Measure 4: fc + psi
    check_measure(n, lambda c,n: fc(c,n) + psi(c,n), "fc + psi")

    # Measure 5: Sum of values
    check_measure(n, lambda c,n: sum(c), "sum of values")

    # Measure 6: sum of c[i] * (n-i)
    check_measure(n, lambda c,n: sum(c[i]*(n-i) for i in range(n)), "weighted sum")

    # Measure 7: fc * n + psi + sum_vals
    check_measure(n, lambda c,n: fc(c,n)*n*10 + psi(c,n) + sum(c), "fc*10n + psi + sum")
