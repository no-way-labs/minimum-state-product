#!/usr/bin/env python3
"""Check: among fc-DECREASING steps, does Psi always decrease?
If yes, then we can use:
- For nonneg (fc nondecreasing): (n-fc, Psi) Lex-decreases (already proved)
- For fc-decreasing: (fc, Psi) reverse-Lex decreases (fc drops, or fc same but Psi drops)
  Wait, fc-decreasing means fc STRICTLY drops. So (fc) itself is a decreasing Nat.
  But if Psi also always decreases on fc-decreasing steps, we could just use Psi!

The real question: does every fc-decreasing step decrease Psi?
If yes: use the measure Psi for fc-dec steps, and (n-fc, Psi) for nonneg steps.
Combined: Prod.Lex((n-fc)*K + Psi, something) might work.
Actually if Psi decreases on ALL steps, we'd be done. We already know it increases on some.
Key check: does Psi ever increase on fc-DECREASING steps specifically?"""

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

for n in range(5, 13):
    ms = get_ms(n)
    from itertools import product as iproduct

    fcdec_psi_increase = 0
    fcdec_psi_equal = 0
    fcdec_psi_decrease = 0
    fcinc_psi_increase = 0
    fcinc_psi_decrease = 0
    fceq_psi_increase = 0
    total_fcdec = 0
    total_fcinc = 0
    total_fceq = 0

    for config in iproduct(*[range(m) for m in ms]):
        old_psi = psi(config, n)
        old_fc = fc(config, n)
        for i in range(n):
            new_config = fire(config, n, i)
            if new_config is None:
                continue
            new_psi = psi(new_config, n)
            new_fc = fc(new_config, n)

            if new_fc < old_fc:  # fc-decreasing
                total_fcdec += 1
                if new_psi > old_psi:
                    fcdec_psi_increase += 1
                    if fcdec_psi_increase <= 2 and n == 5:
                        print(f"  FCDEC PSI INCREASE n={n}: {config} fire {i}")
                        print(f"    fc: {old_fc}->{new_fc}, psi: {old_psi}->{new_psi}")
                elif new_psi == old_psi:
                    fcdec_psi_equal += 1
                else:
                    fcdec_psi_decrease += 1
            elif new_fc > old_fc:  # fc-increasing
                total_fcinc += 1
                if new_psi > old_psi:
                    fcinc_psi_increase += 1
                else:
                    fcinc_psi_decrease += 1
            else:  # fc-preserving
                total_fceq += 1
                if new_psi > old_psi:
                    fceq_psi_increase += 1

    print(f"n={n}:")
    print(f"  fc-dec: {total_fcdec} (psi↑:{fcdec_psi_increase}, psi=:{fcdec_psi_equal}, psi↓:{fcdec_psi_decrease})")
    print(f"  fc-inc: {total_fcinc} (psi↑:{fcinc_psi_increase}, psi↓:{fcinc_psi_decrease})")
    print(f"  fc-eq:  {total_fceq} (psi↑:{fceq_psi_increase})")
    if fcdec_psi_increase == 0 and fcdec_psi_equal == 0:
        print(f"  *** Psi STRICTLY DECREASES on ALL fc-decreasing steps! ***")
    elif fcdec_psi_increase == 0:
        print(f"  *** Psi non-increasing on fc-decreasing steps ***")
