#!/usr/bin/env python3
"""KEY CHECK: Do CF boundary transitions always appear in the 617-edge DAG?
If yes, the original proof approach (6-tuple rank for boundary + Psi for interior) works.
The previous check_sixtuple_psi2.py tested ALL bad steps, not CF specifically."""

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

sixStateRankVals = [14, 15, 5, 16, 9, 0, 13, 14, 12, 3, 14, 2, 5, 6, 5, 0, 10, 1, 8, 9, 1, 10, 1, 0, 7, 8, 6, 3, 3, 2, 1, 2, 1, 0, 2, 1, 15, 16, 6, 17, 10, 1, 14, 15, 13, 4, 15, 3, 6, 7, 6, 1, 11, 2, 18, 7, 9, 8, 13, 2, 17, 6, 16, 5, 18, 4, 9, 2, 9, 2, 14, 3, 17, 6, 8, 7, 12, 1, 16, 5, 15, 4, 17, 3, 8, 1, 8, 1, 13, 2, 16, 5, 7, 6, 11, 0, 15, 4, 14, 3, 16, 2, 7, 0, 7, 0, 12, 1, 17, 5, 8, 6, 1, 0, 16, 4, 15, 3, 3, 2, 8, 0, 8, 0, 2, 1, 18, 6, 9, 7, 2, 1, 17, 5, 16, 4, 14, 3, 9, 1, 9, 1, 13, 2, 16, 17, 7, 18, 11, 2, 15, 16, 14, 5, 16, 4, 7, 8, 7, 2, 12, 3, 13, 22, 4, 23, 8, 7, 12, 21, 11, 10, 13, 9, 4, 13, 4, 7, 9, 8, 7, 10, 0, 11, 0, 1, 6, 9, 5, 4, 2, 3, 0, 3, 0, 1, 1, 2, 14, 23, 5, 24, 9, 8, 13, 22, 12, 11, 14, 10, 5, 14, 5, 8, 10, 9, 12, 21, 3, 22, 7, 6, 11, 20, 10, 9, 12, 8, 3, 12, 3, 6, 8, 7, 11, 20, 2, 21, 6, 5, 10, 19, 9, 8, 11, 7, 2, 11, 2, 5, 7, 6, 10, 19, 1, 20, 5, 4, 9, 18, 8, 7, 10, 6, 1, 10, 1, 4, 6, 5, 7, 8, 0, 9, 2, 1, 6, 7, 5, 4, 7, 3, 0, 1, 0, 1, 3, 2, 8, 9, 1, 10, 3, 2, 7, 8, 6, 5, 8, 4, 1, 2, 1, 2, 4, 3, 9, 18, 0, 19, 4, 3, 8, 17, 7, 6, 9, 5, 0, 9, 0, 3, 5, 4]

def get_ms(n):
    ms = [3]*n; ms[0] = 2; ms[n-1] = 2; return ms

def get_trans(n, i, L, S, R):
    if i == 0: return TBotVal(L, S, R)
    if i == 1: return TLowVal(L, S, R)
    if i == n-1: return TTopVal(L, S, R)
    if i == n-2: return THighVal(L, S, R)
    return TMidVal(L, S, R)

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
    if frontierTypeVal(a, b) == 1: return W1(n, j)
    return W2(n, j)

def fc(config, n):
    return sum(frontierBitVal(config[j], config[(j+1)%n]) for j in range(n))

def psi(config, n):
    return sum(psiWeightVal(n, j, config[j], config[(j+1)%n]) for j in range(n))

def fire(config, n, i):
    L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S: return None
    new_config = list(config); new_config[i] = new_S
    return tuple(new_config)

def encode6(c0, c1, c2, cn3, cn2, cn1):
    return ((((c0 * 3 + c1) * 3 + c2) * 3 + cn3) * 3 + cn2) * 2 + cn1

def get_6tuple(config, n):
    return (config[0], config[1], config[2], config[n-3], config[n-2], config[n-1])

def six_rank(config, n):
    t = get_6tuple(config, n)
    return sixStateRankVals[encode6(*t)]

def is_boundary_pos(n, i):
    return i <= 2 or i >= n-3

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
    adj = {}
    for c in bad_configs:
        adj[c] = []
        for i in range(n):
            new = fire(c, n, i)
            if new is not None and new in bad_set:
                adj[c].append(new)
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

for n in [9, 10, 11, 12]:
    print(f"\n{'='*60}")
    print(f"n={n}")
    good_set = build_good_set(n)
    ff, bad_set = compute_future_fc(n, good_set)

    from itertools import product as iproduct

    # Check CF boundary transitions against 617-edge rank
    cf_boundary_rank_ok = 0
    cf_boundary_rank_fail = 0
    cf_interior_psi_ok = 0
    cf_interior_psi_fail = 0
    cf_interior_psi_eq = 0

    # Also check: does Psi always decrease on interior CF steps?
    cf_total = 0

    fail_examples = []

    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] < ff[c]:
                continue  # drop step, not CF
            cf_total += 1

            if is_boundary_pos(n, i):
                old_sr = six_rank(c, n)
                new_sr = six_rank(new, n)
                if new_sr < old_sr:
                    cf_boundary_rank_ok += 1
                else:
                    cf_boundary_rank_fail += 1
                    if len(fail_examples) < 3:
                        fail_examples.append((c, i, new, old_sr, new_sr))
            else:
                old_psi = psi(c, n)
                new_psi = psi(new, n)
                if new_psi < old_psi:
                    cf_interior_psi_ok += 1
                elif new_psi == old_psi:
                    cf_interior_psi_eq += 1
                else:
                    cf_interior_psi_fail += 1

    print(f"  CF steps: {cf_total}")
    print(f"  CF boundary: rank↓ {cf_boundary_rank_ok}, rank fail {cf_boundary_rank_fail}")
    print(f"  CF interior: psi↓ {cf_interior_psi_ok}, psi= {cf_interior_psi_eq}, psi↑ {cf_interior_psi_fail}")

    for c, i, new, osr, nsr in fail_examples:
        old_6 = get_6tuple(c, n)
        new_6 = get_6tuple(new, n)
        print(f"    FAIL: pos {i}, 6t {old_6}->{new_6}, rank {osr}->{nsr}")
        print(f"      fc: {fc(c,n)}->{fc(new,n)}, psi: {psi(c,n)}->{psi(new,n)}")

    if cf_boundary_rank_fail == 0 and cf_interior_psi_fail == 0 and cf_interior_psi_eq == 0:
        print(f"  *** PROOF WORKS: 6-tuple rank (boundary) + Psi (interior) for ALL CF steps! ***")
