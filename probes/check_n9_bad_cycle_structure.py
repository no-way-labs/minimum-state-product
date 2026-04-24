#!/usr/bin/env python3
"""
DERISKING:
1. What does the bad cycle look like? Is it a shadow of the good cycle?
2. Try multiple completion strategies — do ALL produce bad cycles?
"""
from itertools import product as iproduct
from collections import Counter, deque

n = 9
ms = [2,3,3,2,3,3,2,3,3]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

# Find EC-free cycle (reuse from before)
results = []
def dfs(word, fc, config):
    if len(word) > 26: return
    if len(word) >= 24 and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
            if len(results) >= 10: return
        return
    if len(results) >= 10: return
    remaining = 26 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        if len(results) >= 10: return
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    if len(results) >= 10: break
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

def has_ec(word):
    ell = len(word)
    cfgs = [list(start)]
    for i in range(ell):
        c = list(cfgs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
        cfgs.append(c)
    for p in range(n):
        m_ctx, n_ctx = set(), set()
        for s in range(ell):
            ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx: return True
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx: return True
                n_ctx.add(ctx)
    return False

ec_free = [w for w in results if not has_ec(w)]
word = ec_free[0]
ell = len(word)

configs = [list(start)]
for i in range(ell):
    c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
    configs.append(c)

cycle_set = set(tuple(configs[s]) for s in range(ell))
config_list = [tuple(configs[s]) for s in range(ell)]

# Build fixed constraints
fixed = {}
for p in range(n):
    for s in range(ell):
        ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
        if word[s] == p:
            fixed[(p, *ctx)] = configs[s+1][p]
        else:
            fixed[(p, *ctx)] = configs[s][p]

# Collect free contexts per proc
free_ctxs = {}
for p in range(n):
    free_ctxs[p] = []
    for L in range(ms[(p-1)%n]):
        for S in range(ms[p]):
            for R in range(ms[(p+1)%n]):
                if (p, L, S, R) not in fixed:
                    free_ctxs[p].append((L, S, R))

all_configs_list = list(iproduct(*(range(m) for m in ms)))
cidx = {c: i for i, c in enumerate(all_configs_list)}
total = len(all_configs_list)

def build_rules(completion_strategy):
    """Build rules with given completion strategy for free contexts."""
    rules = {}
    for p in range(n):
        rules[p] = {}
        for L in range(ms[(p-1)%n]):
            for S in range(ms[p]):
                for R in range(ms[(p+1)%n]):
                    key = (p, L, S, R)
                    if key in fixed:
                        rules[p][(L,S,R)] = fixed[key]
                    else:
                        rules[p][(L,S,R)] = completion_strategy(p, L, S, R)
    return rules

def find_bad_cycle(rules):
    """Find a cycle in non-legitimate configs. Return cycle or None."""
    non_legit = set()
    for ci, c in enumerate(all_configs_list):
        if tuple(c) in cycle_set: continue
        non_legit.add(ci)

    # Build successor graph
    nl_succs = {}
    for ci in non_legit:
        c = all_configs_list[ci]
        succs = set()
        for p in range(n):
            ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
            if rules[p][ctx] != c[p]:
                nc = list(c); nc[p] = rules[p][ctx]
                nci = cidx[tuple(nc)]
                if nci in non_legit:
                    succs.add(nci)
        nl_succs[ci] = succs

    # Find a cycle using DFS
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {ci: WHITE for ci in non_legit}
    parent = {}
    cycle_node = None

    for start_ci in non_legit:
        if color[start_ci] != WHITE: continue
        stack = [(start_ci, iter(nl_succs.get(start_ci, set())))]
        color[start_ci] = GRAY
        while stack:
            ci, it = stack[-1]
            try:
                nci = next(it)
                if color.get(nci, WHITE) == GRAY:
                    # Found cycle — extract it
                    cycle_configs = [nci]
                    cur = ci
                    while cur != nci:
                        cycle_configs.append(cur)
                        # Find parent
                        for prev_ci, prev_it in reversed(stack):
                            if prev_ci != cur:
                                continue
                            break
                        # Walk back through stack
                        found = False
                        for j in range(len(stack)-1, -1, -1):
                            if stack[j][0] == cur:
                                if j > 0:
                                    cur = stack[j-1][0]
                                found = True
                                break
                        if not found or cur == nci:
                            break
                    return cycle_configs
                elif color.get(nci, WHITE) == WHITE:
                    color[nci] = GRAY
                    stack.append((nci, iter(nl_succs.get(nci, set()))))
            except StopIteration:
                color[ci] = BLACK
                stack.pop()

    return None

def check_deadlocks(rules):
    count = 0
    for c in all_configs_list:
        if tuple(c) in cycle_set: continue
        has_priv = any(rules[p][(c[(p-1)%n], c[p], c[(p+1)%n])] != c[p] for p in range(n))
        if not has_priv: count += 1
    return count

# STRATEGY 1: Good-targeting (+1 mod m)
print("Strategy 1: Good-targeting (+1 mod m)")
rules1 = build_rules(lambda p, L, S, R: (S + 1) % ms[p])
dl1 = check_deadlocks(rules1)
bc1 = find_bad_cycle(rules1)
print(f"  Deadlocks: {dl1}, Bad cycle: {'YES' if bc1 else 'NO'}")
if bc1:
    print(f"  Bad cycle length: {len(bc1)}")
    print(f"  Bad cycle configs: {[all_configs_list[ci] for ci in bc1[:3]]}...")

# STRATEGY 2: Good-targeting (-1 mod m)
print("\nStrategy 2: Good-targeting (-1 mod m)")
rules2 = build_rules(lambda p, L, S, R: (S - 1) % ms[p])
dl2 = check_deadlocks(rules2)
bc2 = find_bad_cycle(rules2)
print(f"  Deadlocks: {dl2}, Bad cycle: {'YES' if bc2 else 'NO'}")

# STRATEGY 3: Copy-left (f = L)
print("\nStrategy 3: Copy-left (f = L)")
rules3 = build_rules(lambda p, L, S, R: L % ms[p])
dl3 = check_deadlocks(rules3)
bc3 = find_bad_cycle(rules3)
print(f"  Deadlocks: {dl3}, Bad cycle: {'YES' if bc3 else 'NO'}")

# STRATEGY 4: Copy-right (f = R)
print("\nStrategy 4: Copy-right (f = R)")
rules4 = build_rules(lambda p, L, S, R: R % ms[p])
dl4 = check_deadlocks(rules4)
bc4 = find_bad_cycle(rules4)
print(f"  Deadlocks: {dl4}, Bad cycle: {'YES' if bc4 else 'NO'}")

# STRATEGY 5: Mixed — try to avoid both deadlocks and bad cycles
# For each free context: choose value that makes the most configs reach legit
print("\nStrategy 5: Random completions (sample 20)")
import random
random.seed(42)
any_converges = False
for trial in range(20):
    def random_completion(p, L, S, R):
        opts = [v for v in range(ms[p]) if v != S]
        return random.choice(opts) if opts else S
    rules_r = build_rules(random_completion)
    dl = check_deadlocks(rules_r)
    if dl > 0:
        continue  # has deadlocks, skip
    bc = find_bad_cycle(rules_r)
    if not bc:
        any_converges = True
        print(f"  Trial {trial}: NO deadlocks, NO bad cycle → CONVERGES!")
        break

if not any_converges:
    print(f"  All 20 trials: either deadlocks or bad cycles")
    print(f"  *** Strong evidence: NO completion converges ***")

# ANALYSIS: what does the bad cycle look like?
print("\n" + "=" * 60)
print("BAD CYCLE STRUCTURE ANALYSIS")
print("=" * 60)
if bc1:
    # Is the bad cycle a phase-shift of the good cycle?
    bad_configs_set = set(all_configs_list[ci] for ci in bc1)
    overlap = bad_configs_set & cycle_set
    print(f"Bad cycle length: {len(bc1)}")
    print(f"Overlap with good cycle: {len(overlap)}")
    print(f"Bad cycle configs (first 5):")
    for ci in bc1[:5]:
        c = all_configs_list[ci]
        # Check: is this a "shifted" version of a good cycle config?
        print(f"  {c}")

    # Check: is bad cycle a rotation/shift of good cycle?
    good_as_set = set(config_list)
    print(f"\nGood cycle configs (first 5):")
    for c in config_list[:5]:
        print(f"  {c}")

    # Check component-wise shift
    print(f"\nDifference pattern (bad - good):")
    if len(bc1) == ell:
        for i in range(min(5, len(bc1))):
            bc_c = all_configs_list[bc1[i]]
            gc_c = config_list[i]
            diff = tuple((bc_c[p] - gc_c[p]) % ms[p] for p in range(n))
            print(f"  {diff}")
