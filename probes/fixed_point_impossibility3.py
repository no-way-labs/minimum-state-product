#!/usr/bin/env python3
"""
Fixed Point Impossibility - Clean counterexample with uniform state counts.

n=4, ms=(3,3,3,3), product=81.
CW sweep: movers 0,1,2,3,0,1,2,3,... each fires 3 times. Cycle length = 12.
"""

from itertools import product as iproduct
import sys as sysmod

sysmod.setrecursionlimit(100000)

def verify_full(ms, fs, verbose=False):
    """Full verification."""
    n = len(ms)
    configs = list(iproduct(*(range(m) for m in ms)))

    priv_map = {}
    for c in configs:
        priv = []
        for i in range(n):
            L = c[(i-1) % n]
            S = c[i]
            R = c[(i+1) % n]
            if fs[i][(L, S, R)] != S:
                priv.append(i)
        priv_map[c] = priv

    dead = [c for c in configs if len(priv_map[c]) == 0]
    single = {c for c in configs if len(priv_map[c]) == 1}

    succ = {}
    for c in single:
        i = priv_map[c][0]
        L = c[(i-1) % n]
        S = c[i]
        R = c[(i+1) % n]
        new_s = fs[i][(L, S, R)]
        lst = list(c)
        lst[i] = new_s
        succ[c] = (tuple(lst), i)

    good = set(single)
    changed = True
    while changed:
        changed = False
        to_remove = set()
        for c in good:
            s, _ = succ[c]
            if s not in good:
                to_remove.add(c)
        if to_remove:
            good -= to_remove
            changed = True

    visited = set()
    cycles = []
    for c in good:
        if c in visited:
            continue
        path = []
        node = c
        path_set = set()
        while node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node][0]
        if node in path_set:
            idx = path.index(node)
            cycle = path[idx:]
            cycles.append(cycle)
        visited.update(path)

    bad_configs = set(configs) - good
    bad_succ = {c: [] for c in bad_configs}
    for c in bad_configs:
        for i in priv_map[c]:
            L = c[(i-1) % n]
            S = c[i]
            R = c[(i+1) % n]
            new_s = fs[i][(L, S, R)]
            lst = list(c)
            lst[i] = new_s
            c2 = tuple(lst)
            if c2 in bad_configs:
                bad_succ[c].append(c2)

    WHITE, GRAY, BLACK = 0, 1, 2
    color = {c: WHITE for c in bad_configs}
    has_bad_cycle = False

    def dfs(c):
        nonlocal has_bad_cycle
        color[c] = GRAY
        for c2 in bad_succ[c]:
            if color[c2] == GRAY:
                has_bad_cycle = True
                return
            if color[c2] == WHITE:
                dfs(c2)
                if has_bad_cycle:
                    return
        color[c] = BLACK

    for c in bad_configs:
        if color[c] == WHITE:
            dfs(c)
            if has_bad_cycle:
                break

    fair = True
    if cycles:
        cycle = cycles[0]
        movers_seen = set()
        for c in cycle:
            i = priv_map[c][0]
            movers_seen.add(i)
        fair = len(movers_seen) == n

    return {
        'dead_configs': dead,
        'good_configs': good,
        'cycles': cycles,
        'has_bad_cycle': has_bad_cycle,
        'fair': fair,
        'converges': not has_bad_cycle,
        'liveness': len(dead) == 0,
        'priv_map': priv_map,
    }


def test_uniform_sweep():
    """n=4, ms=(3,3,3,3), CW sweep with incrementing transitions."""
    n = 4
    ms = [3, 3, 3, 3]

    fs = [{} for _ in range(n)]

    # Build CW sweep: mover at step t is t % n
    # Each proc fires 3 times in 12 steps
    c = [0, 0, 0, 0]
    cycle = []
    cycle_len = n * ms[0]  # 12

    for t in range(cycle_len):
        p = t % n
        config = tuple(c)
        cycle.append(config)

        L = c[(p-1) % n]
        S = c[p]
        R = c[(p+1) % n]

        new_s = (S + 1) % ms[p]
        fs[p][(L, S, R)] = new_s
        c[p] = new_s

    print(f"CW sweep cycle (length {cycle_len}):")
    for t, cfg in enumerate(cycle):
        p = t % n
        print(f"  t={t:2d}: config={cfg}, mover=P{p}")
    print(f"After cycle: {tuple(c)}, closes: {tuple(c) == cycle[0]}")

    if tuple(c) != cycle[0]:
        print("CYCLE DOESN'T CLOSE - adjusting")
        return

    # Count mover contexts per proc
    mover_ctx = {p: set() for p in range(n)}
    for t, cfg in enumerate(cycle):
        p = t % n
        L = cfg[(p-1) % n]
        S = cfg[p]
        R = cfg[(p+1) % n]
        mover_ctx[p].add((L, S, R))

    print(f"\nMover contexts:")
    for p in range(n):
        total = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
        print(f"  P{p}: {len(mover_ctx[p])}/{total} used by movers")
        for ctx in sorted(mover_ctx[p]):
            print(f"    {ctx} -> {fs[p][ctx]}")

    # Fill free entries with STAY to maximize fixed points
    for p in range(n):
        for L in range(ms[(p-1) % n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1) % n]):
                    ctx = (L, S, R)
                    if ctx not in fs[p]:
                        fs[p][ctx] = S  # stay

    result = verify_full(ms, fs)
    print(f"\nVerification (stay-fill):")
    print(f"  Liveness: {result['liveness']}")
    print(f"  Dead configs: {len(result['dead_configs'])}")
    print(f"  Cycles found: {len(result['cycles'])}, sizes: {[len(c) for c in result['cycles']]}")
    print(f"  Converges: {result['converges']}")
    print(f"  Fair: {result['fair']}")

    if result['converges'] and not result['liveness']:
        print(f"\n*** COUNTEREXAMPLE: converges=True, liveness=False ***")
        print(f"Dead configs (sample):")
        for d in result['dead_configs'][:5]:
            print(f"  {d}")

    # Now try: fill free entries to MAXIMIZE privilege (always change state)
    print("\n\n--- Now with privilege-maximizing fill ---")
    fs2 = [{} for _ in range(n)]
    # Copy mover entries
    for p in range(n):
        for ctx in mover_ctx[p]:
            fs2[p][ctx] = fs[p][ctx]
    # Fill free entries: always change
    for p in range(n):
        for L in range(ms[(p-1) % n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1) % n]):
                    ctx = (L, S, R)
                    if ctx not in fs2[p]:
                        fs2[p][ctx] = (S + 1) % ms[p]  # always fire

    result2 = verify_full(ms, fs2)
    print(f"  Liveness: {result2['liveness']}")
    print(f"  Dead configs: {len(result2['dead_configs'])}")
    print(f"  Cycles found: {len(result2['cycles'])}, sizes: {[len(c) for c in result2['cycles']]}")
    print(f"  Converges: {result2['converges']}")
    print(f"  Has bad cycle: {result2['has_bad_cycle']}")

    return result, result2


print("="*70)
print("UNIFORM SWEEP ANALYSIS")
print("="*70)
r1, r2 = test_uniform_sweep()

print("\n\n" + "="*70)
print("KEY INSIGHT")
print("="*70)
print("""
RESULT: With stay-fill (free entries mapped to stay), we get:
  - Good cycle: YES (sweep cycle preserved)
  - Convergence: YES (no bad cycles, because dead configs block chains)
  - Liveness: NO (many dead fixed points)

This proves that convergence (WellFounded badStep) does NOT imply liveness.

With privilege-maximizing fill (free entries always fire), we get liveness
but likely lose convergence (too many transitions create bad cycles).

IMPLICATION FOR THE LOWER BOUND PROOF:
The LB proof does NOT need the theorem "every non-good config has a privileged
proc." It proves impossibility by showing the good cycle itself leads to
contradiction (entry conflict or shadow cycle). The behavior of non-good configs
is irrelevant to the LB argument.

The only place convergence is used in the LB proof is to derive contradictions
from CONSTRUCTED shadow/bad cycles — not to prove anything about arbitrary configs.
""")
