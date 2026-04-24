"""Session 7: Stress-test the bad-cycle universality claim.

For Sorry #2's BadCycleData approach to work, we need: for every residual
cycle gc and every rule extension realizing gc, some bad cycle exists in
non-gc.

Test:
  - 5 different residual cycles (samples covering different fire patterns)
  - For each, 100 random rule extensions
  - Check whether bad cycle exists in each (sys, gc) pair

If 500/500 have bad cycles → confidence high → commit to Lean construction
If even 1 has no bad cycle → counterexample → plan changes
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

def enumerate_residual(ms, n, cl, cap=10):
    fire_target = list(ms)
    results = []

    def winding_diff(word):
        CL = len(word)
        cw = sum(1 for k in range(CL) if word[(k+1)%CL] == right(word[k], n))
        ccw = sum(1 for k in range(CL) if word[(k+1)%CL] == left(word[k], n))
        return abs(cw - ccw)

    def has_provider_interval(word, ms, n):
        CL = len(word)
        fc = [0] * n
        for m in word: fc[m] += 1
        for i in range(n):
            if fc[i] < 2: continue
            li = left(i, n); ri = right(i, n)
            if ms[li] != 2 and ms[ri] != 2: continue
            fs = [k for k in range(CL) if word[k] == i]
            for idx in range(len(fs)):
                a1 = fs[idx]
                a2 = fs[(idx+1) % len(fs)]
                if a2 <= a1: a2 += CL
                if a2 - a1 < 2: continue
                lc = 0; rc = 0
                for k_raw in range(a2 - 1, a1, -1):
                    k = k_raw % CL
                    m = word[k]
                    if m == i: continue
                    if m == li: lc += 1
                    if m == ri: rc += 1
                    lo = (lc == 0) or (ms[li] == 2 and lc % 2 == 0 and lc >= 2)
                    ro = (rc == 0) or (ms[ri] == 2 and rc % 2 == 0 and rc >= 2)
                    if lo and ro and m != i and (lc > 0 or rc > 0):
                        return True
        return False

    def build_configs(word, ms, n):
        cfg = [0]*n
        configs = [tuple(cfg)]
        for m in word:
            cfg[m] = (cfg[m] + 1) % ms[m]
            configs.append(tuple(cfg))
        return configs[:-1]

    def has_any_ec(word, configs, n):
        for p in range(n):
            mov, non = set(), set()
            lp = left(p, n); rp = right(p, n)
            for k in range(len(word)):
                cfg = configs[k]
                ctx = (cfg[lp], cfg[p], cfg[rp])
                if word[k] == p: mov.add(ctx)
                else: non.add(ctx)
            if mov & non: return True
        return False

    def dfs(word, fc, config, start_config):
        if len(results) >= cap: return
        if len(word) == cl:
            if config != start_config: return
            if fc != fire_target: return
            cfg = list(start_config)
            seen = {tuple(cfg)}
            for m in word:
                cfg[m] = (cfg[m] + 1) % ms[m]
                t = tuple(cfg)
                if t in seen and t != start_config: return
                seen.add(t)
            if tuple(cfg) != start_config: return
            wd = tuple(word)
            if winding_diff(wd) != 18: return
            if has_provider_interval(wd, ms, n): return
            cfgs = build_configs(list(wd), ms, n)
            if has_any_ec(list(wd), cfgs, n): return
            results.append(wd)
            return
        remaining = cl - len(word)
        needed = sum(max(0, fire_target[p] - fc[p]) for p in range(n))
        if needed > remaining: return
        last = word[-1]
        for nxt in (left(last, n), last, right(last, n)):
            if fc[nxt] + 1 > fire_target[nxt]: continue
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            word.append(nxt)
            fc[nxt] += 1
            dfs(word, fc, tuple(new_config), start_config)
            word.pop()
            fc[nxt] -= 1
    start = tuple([0]*n)
    for p_start in range(n):
        if len(results) >= cap: break
        c = list(start); c[p_start] = (c[p_start] + 1) % ms[p_start]
        fc = [0]*n; fc[p_start] = 1
        dfs([p_start], fc, tuple(c), start)
    return results

def build_rule_observed(word, ms, n):
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

def random_extend(rule_obs, ms, n):
    rule = {p: dict(rule_obs[p]) for p in range(n)}
    for p in range(n):
        for ctx in all_triples(p, ms, n):
            if ctx not in rule[p]:
                rule[p][ctx] = random.randint(0, ms[p] - 1)
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

def is_valid_rule_for_gc(rule, gc_configs, word, n):
    for k in range(len(word)):
        cfg = gc_configs[k]
        mover = word[k]
        privs = get_priv(rule, cfg, n)
        if privs != [mover]:
            return False
    return True

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
    found = [False]
    def dfs(c, on_stack):
        if found[0]: return
        color[c] = GRAY
        on_stack[c] = True
        for nxt in adj.get(c, []):
            if found[0]: return
            if color[nxt] == GRAY and on_stack.get(nxt, False):
                found[0] = True
                return
            if color[nxt] == WHITE:
                dfs(nxt, on_stack)
                if found[0]: return
        on_stack[c] = False
        color[c] = BLACK
    for c in non_gc:
        if found[0]: break
        if color[c] == WHITE:
            dfs(c, {})
    return found[0]

print("Enumerating residual samples...")
samples = enumerate_residual(MS, N, 24, cap=5)
print(f"Found {len(samples)} samples\n")

EXTENSIONS_PER_SAMPLE = 100
total_trials = 0
total_with_bad = 0
total_invalid = 0
total_no_bad = 0
counterexamples = []

for s_idx, w in enumerate(samples):
    rule_obs, gc_configs = build_rule_observed(list(w), MS, N)
    gc_set = set(gc_configs)
    sample_valid = 0
    sample_bad = 0
    sample_no_bad = 0
    for trial in range(EXTENSIONS_PER_SAMPLE):
        rule = random_extend(rule_obs, MS, N)
        if not is_valid_rule_for_gc(rule, gc_configs, list(w), N):
            total_invalid += 1
            continue
        sample_valid += 1
        total_trials += 1
        if has_bad_cycle(rule, gc_set, MS, N):
            total_with_bad += 1
            sample_bad += 1
        else:
            total_no_bad += 1
            sample_no_bad += 1
            if len(counterexamples) < 3:
                counterexamples.append((s_idx, trial))
    print(f"Sample {s_idx+1}: valid={sample_valid}, bad={sample_bad}, no_bad={sample_no_bad}")

print(f"\nTotal trials: {total_trials} valid, {total_invalid} invalid")
print(f"With bad cycle: {total_with_bad}")
print(f"No bad cycle:   {total_no_bad}")
if counterexamples:
    print(f"Counterexamples: {counterexamples[:3]}")
    print("→ universality FAILS — need different approach for Sorry #2")
else:
    print("→ universality holds across stress test → BadCycleData path is viable")
