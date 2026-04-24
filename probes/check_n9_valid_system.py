#!/usr/bin/env python3
"""
VERIFY: Is the EC-free n=9 system actually a valid self-stabilizing system?

Checks:
1. Transition function is well-defined (no conflicts)
2. Good cycle configs are all legitimate (some proc privileged in each)
3. From every non-legitimate config, some proc is privileged
4. Every execution eventually reaches a legitimate config (convergence)
"""
from itertools import product as iproduct
from collections import Counter

n = 9
ms = [2,3,3,2,3,3,2,3,3]
start = tuple(0 for _ in range(n))
ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

# Find an EC-free cycle
results = []
def dfs(word, fc, config):
    if len(word) > 26: return
    if len(word) >= 24 and config == start:
        if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
            results.append(tuple(word))
            if len(results) >= 50: return
        return
    if len(results) >= 50: return
    remaining = 26 - len(word)
    needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
    if needed > remaining: return
    last = word[-1]
    for nxt in ring_adj[last]:
        if len(results) >= 50: return
        word.append(nxt)
        nf = list(fc); nf[nxt] += 1
        nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
        dfs(word, nf, tuple(nc))
        word.pop()

for p in range(n):
    if len(results) >= 50: break
    first = list(start); first[p] = (first[p]+1) % ms[p]
    dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

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
print(f"Found {len(ec_free)} EC-free cycles")

if not ec_free:
    print("No EC-free cycles found")
    exit()

word = ec_free[0]
ell = len(word)
print(f"Using cycle: len={ell}, word={word}")

# Build configs
configs = [list(start)]
for i in range(ell):
    c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
    configs.append(c)

# CHECK 1: cycle closes
print(f"\nCheck 1 - Cycle closes: {tuple(configs[0]) == tuple(configs[ell])}")

# CHECK 2: distinct configs
config_tuples = [tuple(configs[s]) for s in range(ell)]
print(f"Check 2 - Distinct configs: {len(set(config_tuples)) == ell} ({len(set(config_tuples))}/{ell})")

# Build transition function from cycle
rules = {}
for p in range(n):
    rules[p] = {}
    for s in range(ell):
        ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
        new_val = configs[s+1][p] if word[s] == p else configs[s][p]
        if ctx in rules[p]:
            if rules[p][ctx] != new_val:
                print(f"  CONFLICT at proc {p}, ctx={ctx}: {rules[p][ctx]} vs {new_val}")
        rules[p][ctx] = new_val

    # Fill unseen
    for L in range(ms[(p-1)%n]):
        for S in range(ms[p]):
            for R in range(ms[(p+1)%n]):
                if (L,S,R) not in rules[p]:
                    rules[p][(L,S,R)] = S  # identity

# CHECK 3: no transition function conflicts
print(f"Check 3 - No TF conflicts: True (EC-free guarantees this)")

# CHECK 4: legitimate configs = cycle configs
# A config is legitimate if NO proc is privileged (stable)
# Wait — in Dijkstra's model, legitimate = some SPECIFIC condition.
# In our model: legitimate configs are the ones in the good cycle.
# A config is privileged at proc p if f_p(L,S,R) != S.

# Count privileged procs per config
all_configs_list = list(iproduct(*(range(m) for m in ms)))
cidx = {c: i for i, c in enumerate(all_configs_list)}

cycle_set = set(config_tuples)
legit_count = 0
nonlegit_with_priv = 0
nonlegit_no_priv = 0
legit_with_exactly_one_priv = 0

for ci, c in enumerate(all_configs_list):
    privs = []
    for p in range(n):
        ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
        if rules[p][ctx] != c[p]:
            privs.append(p)

    if tuple(c) in cycle_set:
        legit_count += 1
        if len(privs) != 1:
            print(f"  WARNING: legit config {c} has {len(privs)} privileged procs: {privs}")
        else:
            legit_with_exactly_one_priv += 1
    else:
        if len(privs) > 0:
            nonlegit_with_priv += 1
        else:
            nonlegit_no_priv += 1
            print(f"  DEADLOCK: non-legit config {c} has 0 privileged procs!")

print(f"\nCheck 4 - Legitimate configs: {legit_count}")
print(f"  Legit with exactly 1 privileged: {legit_with_exactly_one_priv}")
print(f"  Non-legit with ≥1 privileged: {nonlegit_with_priv}")
print(f"  Non-legit DEADLOCKED (0 priv): {nonlegit_no_priv}")

# CHECK 5: from every non-legit config, can we reach legit?
# Use BFS on the full transition graph
print(f"\nCheck 5 - Convergence from every non-legit config:")

# For convergence: under ANY daemon (any choice of privileged proc),
# the system must reach legit.
# WellFounded(badStep) means: no infinite sequence of non-legit transitions.
# This is equivalent to: the non-legit configs form a DAG (no cycles).

# Check for cycles in non-legit configs
non_legit_set = set(range(len(all_configs_list))) - set(cidx[c] for c in cycle_set)

# Build successor graph for non-legit
nl_succs = {}
for ci in non_legit_set:
    c = all_configs_list[ci]
    succs_nl = []
    for p in range(n):
        ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
        if rules[p][ctx] != c[p]:
            nc = list(c); nc[p] = rules[p][ctx]
            nci = cidx[tuple(nc)]
            if nci in non_legit_set:
                succs_nl.append(nci)
    nl_succs[ci] = succs_nl

# DFS cycle detection
WHITE, GRAY, BLACK = 0, 1, 2
color = {ci: WHITE for ci in non_legit_set}
has_nl_cycle = False
for start_ci in non_legit_set:
    if color[start_ci] != WHITE: continue
    stack = [(start_ci, iter(nl_succs.get(start_ci, [])))]
    color[start_ci] = GRAY
    while stack:
        ci, it = stack[-1]
        try:
            nci = next(it)
            if color[nci] == GRAY:
                has_nl_cycle = True
                break
            elif color[nci] == WHITE:
                color[nci] = GRAY
                stack.append((nci, iter(nl_succs.get(nci, []))))
        except StopIteration:
            color[ci] = BLACK
            stack.pop()
    if has_nl_cycle: break

print(f"  Non-legit cycle exists: {has_nl_cycle}")
if has_nl_cycle:
    print(f"  *** SYSTEM DOES NOT CONVERGE (has bad cycle) ***")
else:
    print(f"  *** NON-LEGIT CONFIGS FORM A DAG → SYSTEM CONVERGES ***")
    print(f"  *** THIS IS A VALID SELF-STABILIZING SYSTEM ***")
    print(f"  *** Product = {2**3 * 3**6} < {4 * 3**7} = 4·3^7 ***")
    print(f"  *** THIS WOULD CONTRADICT M_9 = 8748 IF CORRECT ***")

# FINAL CHECK: is this actually a token ring? Does it satisfy Dijkstra's constraints?
print(f"\nCheck 6 - Token ring property:")
print(f"  Each legit config has exactly 1 privileged proc: {legit_with_exactly_one_priv == legit_count}")
print(f"  Non-legit configs have ≥1 privileged: {nonlegit_no_priv == 0}")
if legit_with_exactly_one_priv == legit_count and nonlegit_no_priv == 0:
    print(f"  *** VALID TOKEN RING ***")
