"""Session 7: For one residual cycle, try to construct a BadCycleData.

A BadCycleData is a second orbit of privileged moves disjoint from gc. If
such a second orbit exists for the rule system that realizes a residual gc,
then GlobalObstruction.shadowTrap → ¬converges → False. This closes the
residual case via the existing Lean Obstruction interface.

Approach:
1. Pick a sample residual cycle.
2. Build its rule function (per-proc fire-or-not table over observed triples).
3. For unobserved triples, try various "free" choices.
4. For each rule, enumerate orbits in the full state space.
5. Check if any orbit is disjoint from gc and is a closed privileged cycle.
"""
from collections import Counter
from itertools import product

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]

def left(p, n=N): return (p - 1) % n
def right(p, n=N): return (p + 1) % n

def build_configs(word, ms, n):
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    return configs[:-1]

def enumerate_gc_residual(ms, n, cl, cap=10):
    """Enumerate residual cycles, stop after finding `cap` of them."""
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
            # check residual: |winding|=18, no provider, no EC
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

def build_rule_from_cycle(word, ms, n):
    """Construct a per-proc rule function (LSR triple → next state)
    that exactly realizes the cycle. Unobserved triples → no fire (default)."""
    CL = len(word)
    cfg = [0]*n
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % ms[m]
        configs.append(tuple(cfg))
    configs = configs[:-1]  # length CL

    rule = {p: {} for p in range(n)}
    for p in range(n):
        lp = left(p, n); rp = right(p, n)
        for k in range(CL):
            cfg_k = configs[k]
            ctx = (cfg_k[lp], cfg_k[p], cfg_k[rp])
            if word[k] == p:
                # mover at this step → fire
                next_state = (cfg_k[p] + 1) % ms[p]
                rule[p][ctx] = next_state
            else:
                # non-mover → no fire (next state = current)
                if ctx not in rule[p]:
                    rule[p][ctx] = cfg_k[p]
    return rule, configs

def is_privileged(rule, p, cfg, ms, n):
    lp = left(p, n); rp = right(p, n)
    ctx = (cfg[lp], cfg[p], cfg[rp])
    if ctx not in rule[p]:
        return False  # default no-fire for unobserved triples
    return rule[p][ctx] != cfg[p]

def get_privileged_procs(rule, cfg, ms, n):
    return [p for p in range(n) if is_privileged(rule, p, cfg, ms, n)]

def step(rule, cfg, p, ms, n):
    lp = left(p, n); rp = right(p, n)
    ctx = (cfg[lp], cfg[p], cfg[rp])
    new = list(cfg)
    new[p] = rule[p][ctx]
    return tuple(new)

def find_bad_cycle(rule, gc_configs, ms, n, max_cycle_len=50):
    """Look for a closed cycle of privileged moves disjoint from gc_configs.
    Brute force from various starting points."""
    gc_set = set(gc_configs)
    state_space_size = 1
    for m in ms: state_space_size *= m
    if state_space_size > 100000:
        return None  # too big

    visited_global = set()
    # Try every config not in gc as a starting point
    for cfg in product(*[range(m) for m in ms]):
        if cfg in gc_set or cfg in visited_global:
            continue
        # Walk forward as long as there's a unique privileged proc
        path = []
        cur = cfg
        path_set = set()
        while True:
            if cur in path_set:
                # Found a cycle (not necessarily disjoint from gc, but path so far is a cycle)
                idx = path.index(cur)
                cycle = path[idx:]
                if all(c not in gc_set for c in cycle):
                    return cycle
                break
            if cur in gc_set:
                break  # path led into gc
            privs = get_privileged_procs(rule, cur, ms, n)
            if len(privs) != 1:
                break  # stuck (0 privs) or ambiguous (multiple — would need tiebreaker)
            path.append(cur)
            path_set.add(cur)
            cur = step(rule, cur, privs[0], ms, n)
            if len(path) > max_cycle_len:
                break
        for c in path:
            visited_global.add(c)
    return None

# Find some residual samples
print("Finding residual samples...")
samples = enumerate_gc_residual(MS, N, 24, cap=5)
print(f"Found {len(samples)} samples")

for i, w in enumerate(samples):
    print(f"\nSample {i+1}: {w}")
    rule, gc_configs = build_rule_from_cycle(list(w), MS, N)
    print(f"  Rule has {sum(len(rule[p]) for p in range(N))} entries across {N} procs")
    print(f"  GC configs: {len(gc_configs)}")
    bad = find_bad_cycle(rule, gc_configs, MS, N)
    if bad is None:
        print(f"  Bad cycle search: NOT FOUND (no second orbit under default rule)")
    else:
        print(f"  Bad cycle FOUND: length {len(bad)}, disjoint from gc")
        print(f"    First 3 configs: {bad[:3]}")
