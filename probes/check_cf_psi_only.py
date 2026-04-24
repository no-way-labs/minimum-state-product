#!/usr/bin/env python3
"""Check Psi behavior specifically on CF steps (constant-FutureFc bad steps).
Key question: does Psi decrease on ALL CF steps? Or just fc-preserving ones?"""

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

def build_good_set(n):
    config = tuple([0] * n)
    good = {config}
    cur = list(config)
    for phase in range(3):
        rng = range(n) if phase % 2 == 0 else range(n-1, -1, -1)
        for i in rng:
            new = fire(tuple(cur), n, i)
            if new is not None:
                cur = list(new)
                good.add(tuple(cur))
    return good

def compute_future_fc(n, good_set):
    ms = get_ms(n)
    from itertools import product as iproduct
    all_configs = list(iproduct(*[range(m) for m in ms]))
    bad_configs = [c for c in all_configs if c not in good_set]
    bad_set = set(bad_configs)

    # Build adjacency (bad->bad only)
    adj = {}
    for c in bad_configs:
        adj[c] = []
        for i in range(n):
            new = fire(c, n, i)
            if new is not None and new in bad_set:
                adj[c].append(new)

    # Bellman-Ford: FutureFc = max reachable fc
    ff = {c: fc(c, n) for c in bad_configs}
    changed = True
    iters = 0
    while changed:
        changed = False
        iters += 1
        for c in bad_configs:
            for s in adj[c]:
                if ff[s] > ff[c]:
                    ff[c] = ff[s]
                    changed = True
        if iters > len(bad_configs):
            break
    return ff, bad_set

for n in range(5, 13):
    print(f"\n{'='*60}")
    print(f"n={n}")
    good_set = build_good_set(n)
    ff, bad_set = compute_future_fc(n, good_set)

    from itertools import product as iproduct

    # Check Psi on CF steps broken down by fc direction
    cf_fceq_psi_inc = 0
    cf_fceq_psi_dec = 0
    cf_fceq_psi_eq = 0
    cf_fcinc_psi_inc = 0
    cf_fcinc_psi_dec = 0
    cf_fcinc_psi_eq = 0
    cf_fcdec_psi_inc = 0
    cf_fcdec_psi_dec = 0
    cf_fcdec_psi_eq = 0
    total_cf = 0
    total_drop = 0

    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] < ff[c]:
                total_drop += 1
                continue
            # CF step (ff preserved)
            total_cf += 1
            old_fc = fc(c, n)
            new_fc = fc(new, n)
            old_psi = psi(c, n)
            new_psi = psi(new, n)

            if new_fc == old_fc:
                if new_psi > old_psi: cf_fceq_psi_inc += 1
                elif new_psi < old_psi: cf_fceq_psi_dec += 1
                else: cf_fceq_psi_eq += 1
            elif new_fc > old_fc:
                if new_psi > old_psi: cf_fcinc_psi_inc += 1
                elif new_psi < old_psi: cf_fcinc_psi_dec += 1
                else: cf_fcinc_psi_eq += 1
            else:  # fc decreasing
                if new_psi > old_psi: cf_fcdec_psi_inc += 1
                elif new_psi < old_psi: cf_fcdec_psi_dec += 1
                else: cf_fcdec_psi_eq += 1

    total_cf_fceq = cf_fceq_psi_inc + cf_fceq_psi_dec + cf_fceq_psi_eq
    total_cf_fcinc = cf_fcinc_psi_inc + cf_fcinc_psi_dec + cf_fcinc_psi_eq
    total_cf_fcdec = cf_fcdec_psi_inc + cf_fcdec_psi_dec + cf_fcdec_psi_eq

    print(f"  CF steps: {total_cf}, Drop steps: {total_drop}")
    print(f"  CF fc=0: {total_cf_fceq} (psi↑:{cf_fceq_psi_inc}, =:{cf_fceq_psi_eq}, ↓:{cf_fceq_psi_dec})")
    print(f"  CF fc>0: {total_cf_fcinc} (psi↑:{cf_fcinc_psi_inc}, =:{cf_fcinc_psi_eq}, ↓:{cf_fcinc_psi_dec})")
    print(f"  CF fc<0: {total_cf_fcdec} (psi↑:{cf_fcdec_psi_inc}, =:{cf_fcdec_psi_eq}, ↓:{cf_fcdec_psi_dec})")

    # Check if (n-fc, Psi) Lex decreases on ALL CF steps
    nonneg_viol = 0
    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] < ff[c]:
                continue
            old_m = (n - fc(c,n), psi(c,n))
            new_m = (n - fc(new,n), psi(new,n))
            if not (new_m < old_m):
                nonneg_viol += 1
    print(f"  (n-fc, Psi) Lex violations on CF: {nonneg_viol}")

    # Check if Psi alone decreases on ALL CF steps
    psi_viol = 0
    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] < ff[c]:
                continue
            if psi(new,n) >= psi(c,n):
                psi_viol += 1
    print(f"  Psi violations on CF: {psi_viol}")

    if psi_viol == 0:
        print(f"  *** Psi STRICTLY DECREASES on ALL CF steps! ***")
    if nonneg_viol == 0:
        print(f"  *** (n-fc, Psi) Lex DECREASES on ALL CF steps! ***")
