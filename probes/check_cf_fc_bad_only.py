#!/usr/bin/env python3
"""Check if fc decreases on bad steps (non-good configs only).
If fc is non-decreasing on all bad steps, then CF ⊆ nonneg trivially."""

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

def frontier_bit(L, S, R):
    return 1 if (S != L and S != R) else 0

def fc(config, n):
    return sum(frontier_bit(config[(i-1)%n], config[i], config[(i+1)%n]) for i in range(n))

def fire(config, n, i):
    L = config[(i-1) % n]; S = config[i]; R = config[(i+1) % n]
    new_S = get_trans(n, i, L, S, R)
    if new_S == S: return None
    new_config = list(config); new_config[i] = new_S
    return tuple(new_config)

def build_good_cycle(n):
    """Build good cycle via the three-phase wavefront construction."""
    ms = get_ms(n)
    # Start with all-zeros config
    config = [0] * n
    good_configs = set()
    good_configs.add(tuple(config))

    # Phase 1: UP sweep (positions 0,1,...,n-1)
    for i in range(n):
        new = fire(tuple(config), n, i)
        if new is not None:
            config = list(new)
            good_configs.add(tuple(config))

    # Phase 2: DOWN sweep (positions n-1,n-2,...,0)
    for i in range(n-1, -1, -1):
        new = fire(tuple(config), n, i)
        if new is not None:
            config = list(new)
            good_configs.add(tuple(config))

    # Phase 3: UP sweep again
    for i in range(n):
        new = fire(tuple(config), n, i)
        if new is not None:
            config = list(new)
            good_configs.add(tuple(config))

    return good_configs

def build_good_set_bfs(n):
    """Build good configs by following the system until reaching a cycle."""
    ms = get_ms(n)
    from itertools import product as iproduct

    # Actually, let me compute the good cycle more carefully.
    # The good cycle for CUP-2 has length 3n-2.
    # Instead of constructing it, let me just compute which configs reach fc=0.
    # Good configs are on the good cycle. For simplicity, let me compute the
    # cycle by simulation from all-zeros.

    config = tuple([0] * n)
    cycle = [config]
    visited = {config}

    # Do sweeps: UP, DOWN, UP
    for phase in range(3):
        if phase % 2 == 0:  # UP
            for i in range(n):
                new = fire(tuple(cycle[-1]), n, i)
                if new is not None and new not in visited:
                    cycle.append(new)
                    visited.add(new)
        else:  # DOWN
            for i in range(n-1, -1, -1):
                new = fire(tuple(cycle[-1]), n, i)
                if new is not None and new not in visited:
                    cycle.append(new)
                    visited.add(new)

    return visited

def compute_future_fc(n, good_set):
    """Compute FutureFc for each config via BFS/DFS on bad steps."""
    ms = get_ms(n)
    from itertools import product as iproduct

    all_configs = list(iproduct(*[range(m) for m in ms]))
    bad_configs = [c for c in all_configs if c not in good_set]

    # For each bad config, find max fc reachable via bad steps
    # Use iterative approach: compute reachable sets

    # Build adjacency: c -> successors via bad steps
    adj = {}
    for c in bad_configs:
        adj[c] = []
        for i in range(n):
            new = fire(c, n, i)
            if new is not None and new not in good_set:
                adj[c].append(new)

    # For each config, compute max reachable fc via DFS
    future_fc = {}

    def get_future_fc(c, visiting=None):
        if c in future_fc:
            return future_fc[c]
        if visiting is None:
            visiting = set()
        if c in visiting:
            return fc(c, n)  # cycle, just return own fc
        visiting.add(c)
        max_fc = fc(c, n)
        for s in adj.get(c, []):
            max_fc = max(max_fc, get_future_fc(s, visiting))
        visiting.discard(c)
        future_fc[c] = max_fc
        return max_fc

    import sys
    sys.setrecursionlimit(100000)
    for c in bad_configs:
        get_future_fc(c)

    return future_fc

for n in [5, 6, 7, 8, 9]:
    print(f"\n{'='*60}")
    print(f"n={n}")
    ms = get_ms(n)
    good_set = build_good_set_bfs(n)
    print(f"  Good configs: {len(good_set)}")

    future_fc = compute_future_fc(n, good_set)

    # Now check: for bad steps that preserve FutureFc (CF steps),
    # does fc always stay nondecreasing?
    fc_dec_cf = 0
    fc_inc_cf = 0
    fc_eq_cf = 0
    total_cf = 0
    total_bad = 0

    from itertools import product as iproduct
    all_configs = list(iproduct(*[range(m) for m in ms]))

    for c in all_configs:
        if c in good_set:
            continue
        for i in range(n):
            new = fire(c, n, i)
            if new is None:
                continue
            if new in good_set:
                continue
            # This is a bad step: both c and new are bad, and new is a successor of c
            total_bad += 1

            ff_old = future_fc.get(c, 0)
            ff_new = future_fc.get(new, 0)

            if ff_new == ff_old:  # CF step
                total_cf += 1
                fc_old = fc(c, n)
                fc_new = fc(new, n)
                if fc_new < fc_old:
                    fc_dec_cf += 1
                    if fc_dec_cf <= 3:
                        print(f"  CF FC-DECREASE: {c} fire {i} -> {new}, fc {fc_old}->{fc_new}, FF={ff_old}")
                elif fc_new > fc_old:
                    fc_inc_cf += 1
                else:
                    fc_eq_cf += 1

    print(f"  Bad steps: {total_bad}, CF steps: {total_cf}")
    print(f"  CF fc-decrease: {fc_dec_cf}")
    print(f"  CF fc-preserved: {fc_eq_cf}")
    print(f"  CF fc-increase: {fc_inc_cf}")

    if fc_dec_cf == 0:
        print(f"  *** ALL CF steps are fc-nondecreasing! CF ⊆ nonneg ***")
