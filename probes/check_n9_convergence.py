#!/usr/bin/env python3
"""
CRITICAL CHECK: Do the n=9 EC-free cycles come from convergent systems?

If YES → our theorem is false (or definitions differ)
If NO → EC-free cycles create non-convergent systems, and we prove nonconvergence
"""
from itertools import product as iproduct
from collections import Counter, deque

n = 9
ms = [2,3,3,2,3,3,2,3,3]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

# Find EC-free cycles
results = []
def dfs(word, fc, config):
    if len(word) > 26: return
    if len(word) >= 24 and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
            if len(results) >= 100: return
        return
    if len(results) >= 100: return
    remaining = 26 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        if len(results) >= 100: return
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    if len(results) >= 100: break
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

print(f"Found {len(results)} cycles")

# Find EC-free ones
def has_ec(word):
    ell = len(word)
    configs = [list(start)]
    for i in range(ell):
        c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs.append(c)
    for p in range(n):
        m_ctx, n_ctx = set(), set()
        for s in range(ell):
            ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: return True
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: return True
                n_ctx.add(ctx)
    return False

ec_free = [w for w in results if not has_ec(w)]
print(f"EC-free cycles: {len(ec_free)}")

if not ec_free:
    print("All cycles have EC! No need for convergence check.")
    exit()

# For each EC-free cycle: build the system and check convergence
# Build transition functions from the cycle's mover/nonmover constraints
print(f"\nChecking convergence for first {min(5, len(ec_free))} EC-free cycles...")

all_configs_list = list(iproduct(*(range(m) for m in ms)))
cidx = {c: i for i, c in enumerate(all_configs_list)}
total_configs = len(all_configs_list)

for idx, word in enumerate(ec_free[:5]):
    ell = len(word)
    configs = [list(start)]
    for i in range(ell):
        c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        configs.append(c)

    # Build transition rules from cycle
    rules = {}
    for p in range(n):
        rules[p] = {}
        for s in range(ell):
            ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
            if word[s] == p:
                # Mover: f(L,S,R) != S
                rules[p][ctx] = configs[s+1][p]  # the actual new value
            else:
                # Nonmover: f(L,S,R) = S
                rules[p][ctx] = configs[s][p]

        # Fill unseen contexts with identity (f = S)
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    if (L, S, R) not in rules[p]:
                        rules[p][(L, S, R)] = S

    # Determine good configs (some proc is privileged)
    good_set = set()
    cycle_configs = set(tuple(configs[s]) for s in range(ell))
    for ci, c in enumerate(all_configs_list):
        for p in range(n):
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if rules[p][ctx] != c[p]:
                good_set.add(ci)
                break

    bad_set = set(range(total_configs)) - good_set

    # Build successor graph for bad configs
    # From each bad config: find all privileged procs, compute successors
    bad_succs = {}
    for ci in bad_set:
        c = all_configs_list[ci]
        succs = []
        for p in range(n):
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if rules[p][ctx] != c[p]:
                nc = list(c)
                nc[p] = rules[p][ctx]
                nci = cidx[tuple(nc)]
                if nci in bad_set:  # successor is also bad
                    succs.append(nci)
        bad_succs[ci] = succs

    # Check for cycles in bad subgraph (= non-convergence)
    # Use DFS to find cycles
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {ci: WHITE for ci in bad_set}
    has_bad_cycle = False

    for start_ci in bad_set:
        if color[start_ci] != WHITE: continue
        stack = [(start_ci, False)]
        while stack and not has_bad_cycle:
            ci, processed = stack.pop()
            if processed:
                color[ci] = BLACK
                continue
            if color[ci] == GRAY:
                has_bad_cycle = True
                break
            if color[ci] == BLACK:
                continue
            color[ci] = GRAY
            stack.append((ci, True))
            for nci in bad_succs.get(ci, []):
                if color.get(nci, WHITE) == GRAY:
                    has_bad_cycle = True
                    break
                if color.get(nci, WHITE) == WHITE:
                    stack.append((nci, False))

    print(f"\nCycle {idx}: len={ell}, fc={dict(Counter(word))}")
    print(f"  Good configs: {len(good_set)}/{total_configs}")
    print(f"  Bad configs: {len(bad_set)}")
    print(f"  Cycle configs in good: {len(cycle_configs & good_set)}/{len(cycle_configs)}")
    print(f"  Bad cycle exists: {has_bad_cycle}")
    if has_bad_cycle:
        print(f"  *** SYSTEM DOES NOT CONVERGE ***")
    else:
        # Even no bad cycle doesn't mean convergent — need to check
        # that all bad configs can reach good configs
        can_reach_good = set()
        for ci in bad_set:
            if any(nci in good_set for nci in bad_succs.get(ci, [])):
                # This bad config can reach good in one step? No — succs only has bad successors
                pass
        # Actually: check if any bad config has NO successor at all (deadlock)
        # or if the bad graph has a sink component
        deadlocked = [ci for ci in bad_set if not bad_succs.get(ci, [])]
        # But: no bad successors means ALL successors are good (convergent from this config)
        # A bad config with only good successors = one step to good = fine
        # The problem is bad configs whose ALL successors are also bad AND form a cycle
        print(f"  Bad configs with all-bad successors: {sum(1 for ci in bad_set if len(bad_succs.get(ci,[])) > 0)}")
        print(f"  Bad configs that can reach good in 1 step: {len(bad_set) - sum(1 for ci in bad_set if len(bad_succs.get(ci,[])) > 0)}")
        if not has_bad_cycle:
            print(f"  *** No bad cycle → system MIGHT converge ***")
