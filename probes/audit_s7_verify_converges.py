"""Session 7: Verify whether the residual cycle + default rule satisfies
Lean's `converges sys gc := WellFounded (badStep sys gc)`.

If yes, my construction is a counterexample to the LB theorem.
If no, the theorem is consistent and there's some other angle I missed.

Procedure:
1. Pick a residual cycle, build its rule (default no-fire on unobserved).
2. Enumerate ALL configs in state space.
3. For each non-gc config, list all possible "next" configs (via any privileged proc).
4. Build the transition graph on non-gc configs.
5. Check for cycles in this graph (non-determinism allowed).
6. WellFounded badStep ↔ no cycles in the non-gc subgraph.
"""
from itertools import product

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

# Residual sample from earlier output:
SAMPLE = (0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1)

def build_configs(word, ms, n):
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    return configs[:-1]

def build_rule(word, ms, n):
    """Per-proc rule from observed mover/non-mover triples; default no-fire."""
    CL = len(word)
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    configs = configs[:-1]

    rule = {p: {} for p in range(n)}
    for k in range(CL):
        cfg_k = configs[k]
        mover = word[k]
        for p in range(n):
            lp = left(p, n); rp = right(p, n)
            ctx = (cfg_k[lp], cfg_k[p], cfg_k[rp])
            if p == mover:
                next_state = (cfg_k[p] + 1) % ms[p]
                rule[p][ctx] = next_state
            else:
                if ctx not in rule[p]:
                    rule[p][ctx] = cfg_k[p]  # no fire
    return rule, configs

def get_priv(rule, cfg, n):
    privs = []
    for p in range(n):
        lp = left(p, n); rp = right(p, n)
        ctx = (cfg[lp], cfg[p], cfg[rp])
        if ctx in rule[p] and rule[p][ctx] != cfg[p]:
            privs.append(p)
    return privs

def step_with(rule, cfg, p, n):
    lp = left(p, n); rp = right(p, n)
    ctx = (cfg[lp], cfg[p], cfg[rp])
    new = list(cfg)
    new[p] = rule[p][ctx]
    return tuple(new)

print(f"Building rule for sample residual cycle...")
rule, gc_configs = build_rule(list(SAMPLE), MS, N)
gc_set = set(gc_configs)
print(f"GC has {len(gc_set)} configs")
print(f"Rule has {sum(len(rule[p]) for p in range(N))} entries total")

# Enumerate full state space
state_space = list(product(*[range(m) for m in MS]))
total_states = len(state_space)
print(f"Full state space: {total_states} configs")

non_gc = [c for c in state_space if c not in gc_set]
print(f"Non-gc configs: {len(non_gc)}")

# Categorize each non-gc config
stuck = 0          # 0 priv procs
unique_priv = 0    # 1 priv proc
multi_priv = 0     # 2+ priv procs

# Build transition graph: c → list of c' (via any priv proc)
# Restrict to non-gc subgraph
adj = {}
for c in non_gc:
    privs = get_priv(rule, c, N)
    if not privs:
        stuck += 1
        adj[c] = []
        continue
    if len(privs) == 1:
        unique_priv += 1
    else:
        multi_priv += 1
    nexts = []
    for p in privs:
        c_next = step_with(rule, c, p, N)
        if c_next not in gc_set:  # only edges within non-gc
            nexts.append(c_next)
    adj[c] = nexts

print(f"\nNon-gc config breakdown:")
print(f"  stuck (0 priv):     {stuck}")
print(f"  unique priv (1):    {unique_priv}")
print(f"  multi priv (2+):    {multi_priv}")

# Check for cycles in the non-gc subgraph using DFS
print("\nSearching for cycles in non-gc transition subgraph...")
WHITE, GRAY, BLACK = 0, 1, 2
color = {c: WHITE for c in non_gc}
cycle_found = None

def dfs(c, path):
    global cycle_found
    if cycle_found: return
    color[c] = GRAY
    path.append(c)
    for nxt in adj.get(c, []):
        if color[nxt] == GRAY:
            idx = path.index(nxt)
            cycle_found = path[idx:]
            return
        if color[nxt] == WHITE:
            dfs(nxt, path)
            if cycle_found: return
    path.pop()
    color[c] = BLACK

import sys
sys.setrecursionlimit(20000)
for c in non_gc:
    if cycle_found: break
    if color[c] == WHITE:
        dfs(c, [])

if cycle_found is None:
    print("  NO CYCLE in non-gc subgraph.")
    print("  → WellFounded badStep is TRUE.")
    print("  → This (sys, gc) satisfies Lean's `converges`.")
    print()
    print("  IMPLICATION: The residual cycle + default rule extension")
    print("  is a valid Lean (sys, gc) pair satisfying `converges sys gc`.")
    print("  Combined with sub-threshold (product=5832 < 8748), this would")
    print("  be a COUNTEREXAMPLE to the Lean LB theorem")
    print("  `subThreshold → ¬valid` IF it's not ruled out by some other")
    print("  hypothesis or by GoodCycle's constraints.")
else:
    print(f"  CYCLE FOUND of length {len(cycle_found)}.")
    print(f"  → WellFounded badStep is FALSE.")
    print(f"  → BadCycleData exists, closing Sorry #2 in principle.")
    print(f"  First 5 configs: {cycle_found[:5]}")
