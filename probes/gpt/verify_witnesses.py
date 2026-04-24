"""Self-contained verifier for self-stabilizing token ring witnesses.

Checks all five Dijkstra properties:
  1. Liveness: every configuration has at least one privileged processor
  2. Mutual exclusion: every good configuration has exactly one privileged processor
  3. Closure: every move from a good configuration leads to another good configuration
  4. Convergence: no bad configuration cycle exists
  5. Fairness: every cycle through good configurations includes a move by each processor

Usage: python3 verify_witnesses.py

No dependencies beyond Python 3.8+.
"""

from itertools import product as cartesian


def verify(name, state_counts, rules):
    n = len(state_counts)
    P = 1
    for m in state_counts:
        P *= m

    # Build all configurations
    configs = list(cartesian(*(range(m) for m in state_counts)))

    # For each configuration, find privileged processors
    def privileged(cfg):
        priv = []
        for i in range(n):
            L = cfg[(i - 1) % n]
            S = cfg[i]
            R = cfg[(i + 1) % n]
            if rules[i][(L, S, R)] != S:
                priv.append(i)
        return priv

    def move(cfg, proc):
        L = cfg[(proc - 1) % n]
        S = cfg[proc]
        R = cfg[(proc + 1) % n]
        new_S = rules[proc][(L, S, R)]
        lst = list(cfg)
        lst[proc] = new_S
        return tuple(lst)

    # 1. Liveness
    for cfg in configs:
        if not privileged(cfg):
            print(f"  FAIL liveness: {cfg} has no privileged processor")
            return False

    # Find good configurations: look for a Hamiltonian cycle in the
    # single-privileged subgraph
    single_priv = {}
    for cfg in configs:
        priv = privileged(cfg)
        if len(priv) == 1:
            nxt = move(cfg, priv[0])
            single_priv[cfg] = (nxt, priv[0])

    # Find cycles among single-privileged configs
    good_cycle = None
    visited_global = set()
    for start in single_priv:
        if start in visited_global:
            continue
        path = []
        movers = []
        visited = {}
        cur = start
        while cur in single_priv and cur not in visited:
            visited[cur] = len(path)
            visited_global.add(cur)
            path.append(cur)
            nxt, mover = single_priv[cur]
            movers.append(mover)
            cur = nxt
        if cur in visited:
            cycle_start = visited[cur]
            good_cycle = path[cycle_start:]
            good_movers = movers[cycle_start:]
            break

    if good_cycle is None:
        print("  FAIL: no good cycle found")
        return False

    good_set = set(good_cycle)

    # 2. Mutual exclusion
    for cfg in good_set:
        priv = privileged(cfg)
        if len(priv) != 1:
            print(f"  FAIL mutual exclusion: {cfg} has {len(priv)} privileged")
            return False

    # 3. Closure
    for cfg in good_set:
        priv = privileged(cfg)
        nxt = move(cfg, priv[0])
        if nxt not in good_set:
            print(f"  FAIL closure: {cfg} -> {nxt} leaves good set")
            return False

    # 4. Convergence: check no bad configuration cycle exists
    bad_configs = [cfg for cfg in configs if cfg not in good_set]
    # Build the bad-to-bad move graph and check for cycles
    # A bad config can move to any successor via any privileged processor
    # We need to check that no matter how the daemon chooses, we eventually
    # reach a good config. Equivalently: in the subgraph restricted to bad
    # configs, there is no strongly connected component reachable from any
    # bad config that has no exit to a good config.
    # Simpler: iteratively remove bad configs that have ALL successors
    # leading to good configs or already-removed bad configs.
    bad_set = set(bad_configs)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for cfg in bad_set:
            priv = privileged(cfg)
            all_exit = True
            for p in priv:
                nxt = move(cfg, p)
                if nxt in bad_set:
                    all_exit = False
                    break
            if all_exit:
                to_remove.add(cfg)
        if to_remove:
            bad_set -= to_remove
            changed = True

    if bad_set:
        print(f"  FAIL convergence: {len(bad_set)} bad configs in cycles")
        return False

    # 5. Fairness: every processor moves in the good cycle
    movers_seen = set(good_movers)
    if movers_seen != set(range(n)):
        missing = set(range(n)) - movers_seen
        print(f"  FAIL fairness: processors {missing} never move in good cycle")
        return False

    print(f"  PASS  product={P}  good_cycle_length={len(good_cycle)}  "
          f"total_configs={len(configs)}  bad_configs={len(configs)-len(good_cycle)}")
    return True


# === WITNESSES ===

def witness_n5():
    # M_5 = 96, state counts (2,2,2,3,4)
    return (2, 2, 2, 3, 4), (
        {(0,0,0):1,(0,0,1):1,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0,(3,0,0):0,(3,0,1):0,(3,1,0):0,(3,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):0,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):1,(0,1,1):0,(0,1,2):1,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):0},
        {(0,0,0):0,(0,0,1):1,(0,0,2):1,(0,0,3):0,(0,1,0):2,(0,1,1):2,(0,1,2):2,(0,1,3):0,
         (0,2,0):2,(0,2,1):2,(0,2,2):2,(0,2,3):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):0,(1,1,3):1,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):2,(0,1,1):2,(0,2,0):2,(0,2,1):2,(0,3,0):0,(0,3,1):0,
         (1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,(1,2,0):0,(1,2,1):0,(1,3,0):3,(1,3,1):0,
         (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1,(2,2,0):3,(2,2,1):2,(2,3,0):3,(2,3,1):0},
    )

def witness_n6():
    # M_6 = 288, state counts (2,2,2,4,3,3)
    return (2, 2, 2, 4, 3, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):0,(0,1,1):1,(0,1,2):0,(0,1,3):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):1,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):1,(1,1,3):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):2,(0,1,1):3,(0,1,2):1,(0,2,0):2,(0,2,1):2,(0,2,2):1,
         (0,3,0):2,(0,3,1):0,(0,3,2):3,
         (1,0,0):1,(1,0,1):2,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0,(1,2,0):3,(1,2,1):2,(1,2,2):2,
         (1,3,0):3,(1,3,1):0,(1,3,2):0},
        {(0,0,0):0,(0,0,1):2,(0,0,2):0,(0,1,0):1,(0,1,1):2,(0,1,2):0,(0,2,0):0,(0,2,1):2,(0,2,2):2,
         (1,0,0):0,(1,0,1):2,(1,0,2):0,(1,1,0):0,(1,1,1):0,(1,1,2):0,(1,2,0):0,(1,2,1):2,(1,2,2):2,
         (2,0,0):0,(2,0,1):1,(2,0,2):1,(2,1,0):2,(2,1,1):1,(2,1,2):2,(2,2,0):2,(2,2,1):2,(2,2,2):2,
         (3,0,0):1,(3,0,1):0,(3,0,2):0,(3,1,0):1,(3,1,1):0,(3,1,2):1,(3,2,0):0,(3,2,1):0,(3,2,2):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):1,(1,2,0):2,(1,2,1):0,
         (2,0,0):1,(2,0,1):1,(2,1,0):1,(2,1,1):1,(2,2,0):2,(2,2,1):0},
    )

def witness_n7():
    # M_7 <= 864, state counts (3,2,2,2,3,4,3)
    return (3, 2, 2, 2, 3, 4, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):2,(0,1,1):0,(0,2,0):2,(0,2,1):2,
         (1,0,0):1,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):2,(1,2,1):2,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):1,(2,2,0):2,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):0,(1,1,1):0,
         (2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):0,(1,0,0):1,(1,0,1):0,(1,1,0):1,(1,1,1):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,
         (0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):2,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):0,(1,1,3):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):2},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):3,(0,1,1):1,(0,1,2):1,
         (0,2,0):2,(0,2,1):0,(0,2,2):1,(0,3,0):3,(0,3,1):0,(0,3,2):1,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):1,
         (2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):1,(2,1,2):2,
         (2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):2,(0,1,2):1,(0,2,0):0,(0,2,1):2,(0,2,2):0,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):1,(1,1,2):0,(1,2,0):1,(1,2,1):0,(1,2,2):0,
         (2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):0,(2,1,1):0,(2,1,2):2,(2,2,0):0,(2,2,1):0,(2,2,2):2,
         (3,0,0):2,(3,0,1):0,(3,0,2):1,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):2,(3,2,1):0,(3,2,2):0},
    )

def witness_n8():
    # M_8 <= 2592, state counts (2,2,3,4,3,3,2,3)
    return (2, 2, 3, 4, 3, 3, 2, 3), (
        {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,
         (2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,
         (1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
        {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,
         (0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,
         (1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,
         (0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,
         (1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,
         (2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,
         (2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
        {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,
         (1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,
         (2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,
         (3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,
         (1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,
         (2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
        {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,
         (1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,
         (2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
        {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,
         (1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
    )


if __name__ == "__main__":
    witnesses = [
        ("n=5, M_5=96", witness_n5),
        ("n=6, M_6=288", witness_n6),
        ("n=7, M_7<=864", witness_n7),
        ("n=8, M_8<=2592", witness_n8),
    ]
    all_ok = True
    for name, wfn in witnesses:
        sc, rules = wfn()
        print(f"{name}, state_counts={sc}:")
        ok = verify(name, sc, rules)
        if not ok:
            all_ok = False
    print()
    if all_ok:
        print("All witnesses verified.")
    else:
        print("SOME WITNESSES FAILED.")
