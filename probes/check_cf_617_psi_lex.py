#!/usr/bin/env python3
"""KEY CHECK: Does Prod.Lex(617-rank, Psi) decrease on ALL CF steps?
- Interior CF: 6-tuple unchanged, so 617-rank unchanged. Psi must decrease.
- Boundary CF with 617-rank decrease: first component drops → Lex drops.
- Boundary CF with 617-rank unchanged or increase: need Psi to decrease.

If this works, we have our proof: Prod.Lex(FutureFc, Prod.Lex(sixStateRank, Psi))"""

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
    return sum(1 for j in range(n) if config[j] != config[(j+1)%n])

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

for n in range(5, 14):
    print(f"\n{'='*60}")
    print(f"n={n}")
    good_set = build_good_set(n)
    ff, bad_set = compute_future_fc(n, good_set)

    # Check Prod.Lex(617-rank, Psi) on ALL CF steps
    lex_ok = 0
    lex_fail = 0
    fail_details = []

    # Also separate: boundary vs interior
    int_psi_fail = 0
    bnd_rank_down_psi_any = 0
    bnd_rank_same_psi_down = 0
    bnd_rank_same_psi_fail = 0
    bnd_rank_up_psi_down = 0
    bnd_rank_up_psi_fail = 0

    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] != ff[c]:
                continue

            old_sr = six_rank(c, n)
            new_sr = six_rank(new, n)
            old_psi = psi(c, n)
            new_psi = psi(new, n)

            # Prod.Lex(sixStateRank, Psi) decreases if:
            # new_sr < old_sr, OR (new_sr == old_sr AND new_psi < old_psi)
            if new_sr < old_sr:
                lex_ok += 1
                bnd_rank_down_psi_any += 1
            elif new_sr == old_sr and new_psi < old_psi:
                lex_ok += 1
                if is_boundary_pos(n, i):
                    bnd_rank_same_psi_down += 1
            elif new_sr == old_sr and new_psi >= old_psi:
                lex_fail += 1
                if is_boundary_pos(n, i):
                    bnd_rank_same_psi_fail += 1
                else:
                    int_psi_fail += 1
                if len(fail_details) < 5:
                    fail_details.append((c, i, new, old_sr, new_sr, old_psi, new_psi,
                                        fc(c,n), fc(new,n)))
            else:  # new_sr > old_sr
                if new_psi < old_psi:
                    bnd_rank_up_psi_down += 1
                    lex_fail += 1  # rank increased, even though Psi dropped
                else:
                    bnd_rank_up_psi_fail += 1
                    lex_fail += 1
                if len(fail_details) < 5:
                    fail_details.append((c, i, new, old_sr, new_sr, old_psi, new_psi,
                                        fc(c,n), fc(new,n)))

    total = lex_ok + lex_fail
    print(f"  CF steps: {total}")
    print(f"  Lex(617-rank, Psi) OK: {lex_ok}, FAIL: {lex_fail}")
    print(f"    rank↓: {bnd_rank_down_psi_any}")
    print(f"    rank=, psi↓: {bnd_rank_same_psi_down}")
    print(f"    rank=, psi fail: {bnd_rank_same_psi_fail} (boundary: {bnd_rank_same_psi_fail - int_psi_fail}, interior: {int_psi_fail})")
    print(f"    rank↑, psi↓: {bnd_rank_up_psi_down}")
    print(f"    rank↑, psi fail: {bnd_rank_up_psi_fail}")

    if lex_fail == 0:
        print(f"  *** Prod.Lex(617-rank, Psi) WORKS for ALL CF steps! ***")

    for c, i, new, osr, nsr, op, np, ofc, nfc in fail_details[:3]:
        print(f"    FAIL: pos {i}, rank {osr}->{nsr}, psi {op}->{np}, fc {ofc}->{nfc}")
        print(f"      6t: {get_6tuple(c,n)} -> {get_6tuple(new,n)}")
