#!/usr/bin/env python3
"""Check Prod.Lex(sixStateRank, Psi) for BAD steps only, using the 617-edge DAG rank."""

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
    ms = get_ms(n)
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
    idx = encode6(*t)
    return sixStateRankVals[idx]

def is_boundary_pos(n, i):
    return i <= 2 or i >= n-3

def build_good_set_bfs(n):
    """Build good cycle configs."""
    config = tuple([0] * n)
    visited = {config}
    frontier = [config]
    # Do sweeps: UP, DOWN, UP (the three-phase wavefront)
    for phase in range(3):
        if phase % 2 == 0:
            for i in range(n):
                c = frontier[-1] if frontier else config
                new = fire(c, n, i)
                if new is not None:
                    visited.add(new)
                    frontier.append(new)
        else:
            for i in range(n-1, -1, -1):
                c = frontier[-1] if frontier else config
                new = fire(c, n, i)
                if new is not None:
                    visited.add(new)
                    frontier.append(new)
    return visited

for n in [9, 10, 11]:
    print(f"\n{'='*60}")
    print(f"n={n}")
    ms = get_ms(n)
    good_set = build_good_set_bfs(n)
    print(f"  Good configs: {len(good_set)}")

    from itertools import product as iproduct

    # Check Prod.Lex(sixStateRank, (n-fc, Psi)) for BAD steps
    # (both source and target must be bad)
    boundary_rank_viol = 0
    interior_nonneg_viol = 0
    total_bad = 0
    total_boundary_bad = 0
    total_interior_bad = 0

    for config in iproduct(*[range(m) for m in ms]):
        if config in good_set:
            continue
        for i in range(n):
            new_config = fire(config, n, i)
            if new_config is None:
                continue
            if new_config in good_set:
                continue
            # Bad step
            total_bad += 1

            old_sr = six_rank(config, n)
            new_sr = six_rank(new_config, n)

            if is_boundary_pos(n, i):
                total_boundary_bad += 1
                # Boundary: need sixStateRank to decrease
                if new_sr >= old_sr:
                    boundary_rank_viol += 1
                    if boundary_rank_viol <= 3:
                        print(f"  BOUNDARY: pos {i}, {config} -> {new_config}")
                        print(f"    rank: {old_sr} -> {new_sr}")
            else:
                total_interior_bad += 1
                # Interior: sixStateRank preserved (verify), need Psi or something to decrease
                if new_sr != old_sr:
                    print(f"  WARNING: interior fire changed 6-tuple rank! pos {i}")
                    continue

                # Check various measures for interior:
                old_fc = fc(config, n)
                new_fc = fc(new_config, n)
                old_psi = psi(config, n)
                new_psi = psi(new_config, n)
                old_nonneg = (n - old_fc, old_psi)
                new_nonneg = (n - new_fc, new_psi)

                # Check if nonneg measure Lex-decreases
                if not (new_nonneg < old_nonneg):
                    interior_nonneg_viol += 1
                    if interior_nonneg_viol <= 5:
                        print(f"  INTERIOR: pos {i}, {config}")
                        print(f"    fc: {old_fc}->{new_fc}, psi: {old_psi}->{new_psi}")
                        print(f"    nonneg: {old_nonneg} -> {new_nonneg}")

    print(f"\n  Bad steps: {total_bad}")
    print(f"  Boundary bad: {total_boundary_bad}, rank violations: {boundary_rank_viol}")
    print(f"  Interior bad: {total_interior_bad}, nonneg violations: {interior_nonneg_viol}")

    if boundary_rank_viol == 0 and interior_nonneg_viol == 0:
        print(f"  *** Prod.Lex(sixStateRank, (n-fc, Psi)) works for ALL bad steps! ***")
