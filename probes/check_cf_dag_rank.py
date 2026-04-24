#!/usr/bin/env python3
"""Compute the actual CF DAG rank for each n.
The CF DAG rank = longest path in the CF subgraph.
Check if it matches 7n-30.
Also decompose the rank to understand its structure."""

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

def fc(config, n):
    return sum(1 for j in range(n) if config[j] != config[(j+1)%n])

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

def fire(config, n, i):
    L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S: return None
    new_config = list(config); new_config[i] = new_S
    return tuple(new_config)

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

from collections import Counter

for n in range(5, 14):
    print(f"\n{'='*60}")
    print(f"n={n}")
    good_set = build_good_set(n)
    ff, bad_set = compute_future_fc(n, good_set)

    # Build CF adjacency
    cf_adj = {}
    cf_configs = set()
    for c in bad_set:
        for i in range(n):
            new = fire(c, n, i)
            if new is None or new not in bad_set:
                continue
            if ff[new] != ff[c]:
                continue
            cf_configs.add(c)
            cf_configs.add(new)
            cf_adj.setdefault(c, []).append(new)
    for c in cf_configs:
        cf_adj.setdefault(c, [])

    # Compute DAG rank via topological sort
    in_deg = {c: 0 for c in cf_configs}
    for c in cf_configs:
        for s in cf_adj.get(c, []):
            if s in in_deg:
                in_deg[s] += 1

    from collections import deque
    queue = deque([c for c in cf_configs if in_deg[c] == 0])
    rank = {c: 0 for c in cf_configs}
    processed = 0
    while queue:
        c = queue.popleft()
        processed += 1
        for s in cf_adj.get(c, []):
            rank[s] = max(rank[s], rank[c] + 1)
            in_deg[s] -= 1
            if in_deg[s] == 0:
                queue.append(s)

    has_cycle = processed < len(cf_configs)
    max_rank = max(rank.values()) if rank else 0

    print(f"  CF configs: {len(cf_configs)}, processed: {processed}")
    if has_cycle:
        print(f"  *** CF DAG HAS CYCLE! ({len(cf_configs) - processed} in cycles) ***")
    else:
        print(f"  CF is a DAG! Max rank: {max_rank}")
        print(f"  7n-30 = {7*n - 30}")

        # Rank distribution
        rank_dist = Counter(rank.values())
        print(f"  Rank distribution: {sorted(rank_dist.items())[:10]}...")

        # Check: what is the rank function's relationship to (fc, Psi)?
        # For configs at max rank
        max_rank_configs = [c for c in cf_configs if rank[c] == max_rank]
        if max_rank_configs:
            c = max_rank_configs[0]
            print(f"  Max rank config example: fc={fc(c,n)}, psi={psi(c,n)}, ff={ff[c]}")

        # Check: rank vs Psi
        # Is rank always ≤ Psi? Or related?
        rank_gt_psi = sum(1 for c in cf_configs if rank[c] > psi(c, n))
        print(f"  Configs with rank > Psi: {rank_gt_psi}")

        # Check: does rank always = some function of (Psi, fc)?
        # Group by (Psi, fc) and see if rank is determined
        psi_fc_to_ranks = {}
        for c in cf_configs:
            key = (psi(c, n), fc(c, n))
            psi_fc_to_ranks.setdefault(key, set()).add(rank[c])
        multi_rank = {k: v for k, v in psi_fc_to_ranks.items() if len(v) > 1}
        print(f"  (Psi, fc) pairs with multiple ranks: {len(multi_rank)}/{len(psi_fc_to_ranks)}")
