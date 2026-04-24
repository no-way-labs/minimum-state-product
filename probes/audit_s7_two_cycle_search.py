"""Test: does a length-2 bad cycle (c ↔ c') always exist in the rule's
non-gc subgraph for residual cycles?

A length-2 bad cycle is two configs c, c' both not in gc, with:
  - p privileged at c, c' = move(c, p)
  - p' privileged at c', c = move(c', p')

If yes for all residual cycles + all rule extensions, the Lean construction
is much simpler than a general cycle search.
"""
from itertools import product
import random
import sys
sys.setrecursionlimit(20000)

random.seed(2026)
N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def enumerate_residual(ms, n, cl, cap):
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

def find_2_cycle(rule, gc_set, ms, n):
    """Look for c, c' both not in gc, with c→c'→c via privileged moves."""
    state_space = list(product(*[range(m) for m in ms]))
    for c in state_space:
        if c in gc_set: continue
        privs = get_priv(rule, c, n)
        for p in privs:
            c_prime = step_with(rule, c, p, n)
            if c_prime in gc_set: continue
            if c_prime == c: continue  # 1-cycle (self-loop), not 2-cycle
            # Check if c_prime → c via some priv proc
            privs2 = get_priv(rule, c_prime, n)
            for p2 in privs2:
                if step_with(rule, c_prime, p2, n) == c:
                    return (c, c_prime, p, p2)
    return None

print("Enumerating residual samples...")
samples = enumerate_residual(MS, N, 24, cap=5)
print(f"Found {len(samples)} samples\n")

EXTENSIONS_PER_SAMPLE = 20
total_with_2cycle = 0
total_without = 0

for s_idx, w in enumerate(samples):
    rule_obs, gc_configs = build_rule_observed(list(w), MS, N)
    gc_set = set(gc_configs)
    has_2cycle = 0
    no_2cycle = 0
    for trial in range(EXTENSIONS_PER_SAMPLE):
        rule = random_extend(rule_obs, MS, N)
        if not is_valid_rule_for_gc(rule, gc_configs, list(w), N):
            continue
        result = find_2_cycle(rule, gc_set, MS, N)
        if result is not None:
            has_2cycle += 1
        else:
            no_2cycle += 1
    print(f"Sample {s_idx+1}: with 2-cycle = {has_2cycle}, without = {no_2cycle}")
    total_with_2cycle += has_2cycle
    total_without += no_2cycle

print(f"\nTotal: with 2-cycle = {total_with_2cycle}, without = {total_without}")
if total_without == 0:
    print("→ Length-2 bad cycle is UNIVERSAL → simpler Lean construction viable")
else:
    print(f"→ Length-2 bad cycles not universal ({total_without} counterexamples)")
