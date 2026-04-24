"""Session 7: Is the bad cycle UNIVERSAL across rule extensions?

For Sorry #2 to be closable via BadCycleData, every rule function that
realizes the residual gc as a GoodCycle must have a bad cycle in non-gc.

Test: try several different rule extensions for a sample residual cycle:
  (a) Default no-fire on unobserved triples
  (b) Default fire (toward state 0) on unobserved
  (c) Random fire choices on unobserved
  (d) Specifically tuned rule that tries to avoid bad cycles

For each, check whether a bad cycle exists in non-gc.

If all extensions have bad cycles → universal → BadCycleData is constructible → Sorry #2 closes.
If some extension has no bad cycle → not universal → need different approach.
"""
from itertools import product
import random
import sys

random.seed(2026)
sys.setrecursionlimit(20000)

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

SAMPLE = (0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1)

def build_rule_observed(word, ms, n):
    """Build rule with only observed triples set; unobserved left as None.
    Returns: rule dict with observed entries only."""
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
                rule[p][ctx] = (cfg_k[p] + 1) % ms[p]
            else:
                if ctx not in rule[p]:
                    rule[p][ctx] = cfg_k[p]
    return rule, configs

def all_triples(p, ms, n):
    lp = left(p, n); rp = right(p, n)
    for L in range(ms[lp]):
        for S in range(ms[p]):
            for R in range(ms[rp]):
                yield (L, S, R)

def extend_rule(rule_obs, ms, n, strategy='no_fire'):
    """Extend rule_obs to all triples per the chosen strategy."""
    rule = {p: dict(rule_obs[p]) for p in range(n)}
    for p in range(n):
        for ctx in all_triples(p, ms, n):
            if ctx not in rule[p]:
                if strategy == 'no_fire':
                    rule[p][ctx] = ctx[1]  # state stays
                elif strategy == 'fire_to_zero':
                    rule[p][ctx] = 0 if ctx[1] != 0 else (1 % ms[p])
                elif strategy == 'fire_inc':
                    rule[p][ctx] = (ctx[1] + 1) % ms[p]
                elif strategy == 'random':
                    rule[p][ctx] = random.randint(0, ms[p] - 1)
                else:
                    raise ValueError(strategy)
    return rule

def get_priv(rule, cfg, n):
    privs = []
    for p in range(n):
        lp = left(p, n); rp = right(p, n)
        ctx = (cfg[lp], cfg[p], cfg[rp])
        if rule[p][ctx] != cfg[p]:
            privs.append(p)
    return privs

def step_with(rule, cfg, p, n):
    lp = left(p, n); rp = right(p, n)
    ctx = (cfg[lp], cfg[p], cfg[rp])
    new = list(cfg)
    new[p] = rule[p][ctx]
    return tuple(new)

def has_bad_cycle(rule, gc_set, ms, n):
    state_space = list(product(*[range(m) for m in ms]))
    non_gc = [c for c in state_space if c not in gc_set]
    adj = {}
    for c in non_gc:
        privs = get_priv(rule, c, n)
        nexts = []
        for p in privs:
            c_next = step_with(rule, c, p, n)
            if c_next not in gc_set:
                nexts.append(c_next)
        adj[c] = nexts
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {c: WHITE for c in non_gc}
    cycle = [None]
    def dfs(c, path):
        if cycle[0]: return
        color[c] = GRAY
        path.append(c)
        for nxt in adj.get(c, []):
            if color[nxt] == GRAY:
                idx = path.index(nxt)
                cycle[0] = path[idx:]
                return
            if color[nxt] == WHITE:
                dfs(nxt, path)
                if cycle[0]: return
        path.pop()
        color[c] = BLACK
    for c in non_gc:
        if cycle[0]: break
        if color[c] == WHITE:
            dfs(c, [])
    return cycle[0]

def is_valid_rule_for_gc(rule, gc_configs, word, ms, n):
    """Verify the extended rule still makes gc a valid GoodCycle:
    at each gc config, exactly the cycle's mover is privileged."""
    for k in range(len(word)):
        cfg = gc_configs[k]
        mover = word[k]
        privs = get_priv(rule, cfg, n)
        if privs != [mover]:
            return False, k, privs
    return True, None, None

# Build observed rule
rule_obs, gc_configs = build_rule_observed(list(SAMPLE), MS, N)
gc_set = set(gc_configs)
print(f"GC: {len(gc_set)} configs")
print(f"Observed entries per proc: {[len(rule_obs[p]) for p in range(N)]}")

# Try several extensions
strategies = ['no_fire', 'fire_to_zero', 'fire_inc']
for strat in strategies:
    rule = extend_rule(rule_obs, MS, N, strategy=strat)
    valid, k, privs = is_valid_rule_for_gc(rule, gc_configs, list(SAMPLE), MS, N)
    if not valid:
        print(f"\n{strat:15s}: INVALID — at step {k}, privs={privs}, expected [{SAMPLE[k]}]")
        continue
    bad = has_bad_cycle(rule, gc_set, MS, N)
    if bad is None:
        print(f"\n{strat:15s}: NO bad cycle (would be a counterexample candidate)")
    else:
        print(f"\n{strat:15s}: BAD CYCLE found, length {len(bad)}")

# Random extensions
print("\nTrying random extensions...")
random_results = {'bad_found': 0, 'no_bad': 0, 'invalid': 0}
for trial in range(10):
    rule = extend_rule(rule_obs, MS, N, strategy='random')
    valid, _, _ = is_valid_rule_for_gc(rule, gc_configs, list(SAMPLE), MS, N)
    if not valid:
        random_results['invalid'] += 1
        continue
    bad = has_bad_cycle(rule, gc_set, MS, N)
    if bad is None:
        random_results['no_bad'] += 1
    else:
        random_results['bad_found'] += 1
print(f"Random trials: {random_results}")
