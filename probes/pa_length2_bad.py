"""Find length-2 bad cycles in the gc-determined subgraph.

A length-2 cycle is (c, c', p, p') with:
  - c ≠ c' both non-gc
  - (p, c[p-1], c[p], c[p+1]) in mover_triples (forced to change)
  - move_p(c) = c'
  - (p', c'[p'-1], c'[p'], c'[p'+1]) in mover_triples
  - move_{p'}(c') = c

For length-2, we need c[p'] = some value that, after moving, gives c.
Since moves increment (mod m), this requires m_p = 2 and m_{p'} = 2 (simplest)
or more complex structure.
"""
import sys
sys.setrecursionlimit(30000)
from itertools import product as iproduct

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

def enumerate_residual(cap):
    fire_target = list(MS)
    results = []
    def winding_diff(word):
        CL_ = len(word)
        cw = sum(1 for k in range(CL_) if word[(k+1)%CL_] == right(word[k]))
        ccw = sum(1 for k in range(CL_) if word[(k+1)%CL_] == left(word[k]))
        return abs(cw - ccw)
    def has_provider_interval(word):
        CL_ = len(word)
        fc = [0] * N
        for m in word: fc[m] += 1
        for i in range(N):
            if fc[i] < 2: continue
            li = left(i); ri = right(i)
            if MS[li] != 2 and MS[ri] != 2: continue
            fs = [k for k in range(CL_) if word[k] == i]
            for idx in range(len(fs)):
                a1 = fs[idx]; a2 = fs[(idx+1) % len(fs)]
                if a2 <= a1: a2 += CL_
                if a2 - a1 < 2: continue
                lc = 0; rc = 0
                for k_raw in range(a2 - 1, a1, -1):
                    k = k_raw % CL_
                    m = word[k]
                    if m == i: continue
                    if m == li: lc += 1
                    if m == ri: rc += 1
                    lo = (lc == 0) or (MS[li] == 2 and lc % 2 == 0 and lc >= 2)
                    ro = (rc == 0) or (MS[ri] == 2 and rc % 2 == 0 and rc >= 2)
                    if lo and ro and m != i and (lc > 0 or rc > 0):
                        return True
        return False
    def has_any_ec(word, configs):
        for p in range(N):
            mov, non = set(), set()
            lp = left(p); rp = right(p)
            for k in range(len(word)):
                cfg = configs[k]
                ctx = (cfg[lp], cfg[p], cfg[rp])
                if word[k] == p: mov.add(ctx)
                else: non.add(ctx)
            if mov & non: return True
        return False
    def build_configs(word):
        cfg = [0]*N
        configs = [tuple(cfg)]
        for m in word:
            cfg[m] = (cfg[m] + 1) % MS[m]
            configs.append(tuple(cfg))
        return configs[:-1]
    def dfs(word, fc, config, start_config):
        if len(results) >= cap: return
        if len(word) == CL:
            if config != start_config: return
            if fc != fire_target: return
            cfg = list(start_config)
            seen = {tuple(cfg)}
            for m in word:
                cfg[m] = (cfg[m] + 1) % MS[m]
                t = tuple(cfg)
                if t in seen and t != start_config: return
                seen.add(t)
            if tuple(cfg) != start_config: return
            wd = tuple(word)
            if winding_diff(wd) != 18: return
            if has_provider_interval(wd): return
            cfgs = build_configs(list(wd))
            if has_any_ec(list(wd), cfgs): return
            results.append(wd)
            return
        remaining = CL - len(word)
        needed = sum(max(0, fire_target[p] - fc[p]) for p in range(N))
        if needed > remaining: return
        last = word[-1]
        for nxt in (left(last), last, right(last)):
            if fc[nxt] + 1 > fire_target[nxt]: continue
            new_config = list(config)
            new_config[nxt] = (new_config[nxt] + 1) % MS[nxt]
            word.append(nxt)
            fc[nxt] += 1
            dfs(word, fc, tuple(new_config), start_config)
            word.pop()
            fc[nxt] -= 1
    start = tuple([0]*N)
    for p_start in range(N):
        if len(results) >= cap: break
        c = list(start); c[p_start] = (c[p_start] + 1) % MS[p_start]
        fc = [0]*N; fc[p_start] = 1
        dfs([p_start], fc, tuple(c), start)
    return results

def find_length2_bad(w):
    cfg = [0]*N
    gc_configs = [tuple(cfg)]
    for m in w:
        cfg[m] = (cfg[m] + 1) % MS[m]
        gc_configs.append(tuple(cfg))
    gc_configs = gc_configs[:-1]
    gc_set = set(gc_configs)
    mover_triples = {}
    for k, p in enumerate(w):
        cfg = gc_configs[k]
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        mover_triples[(p, L, S, R)] = (S + 1) % MS[p]
    # For length 2: need c, c' non-gc with c → c' → c
    # c[p'] value v, after apply p' get c'[p'] = v'
    # then at c', we need p applied to get c (move on p): c[p] = (c'[p] + 1) % m_p, i.e., c'[p] = c[p] - 1 mod m_p.
    # So the only way c -> c' -> c in 2 steps is: p≠p' (different procs). c and c' differ at both p and p'.
    # Then move at c on p gives c' (so c'[p] = c[p] + 1 mod m_p, with c'[q]=c[q] for q≠p).
    # But we also want c[p'] → c'[p'] via move at p' on c'. That requires c'[p'] ≠ c[p'], contradiction.
    # So: length-2 "c -> c' -> c" is IMPOSSIBLE in a single-proc-move system. The length must be ≥ 2·m_p for each proc involved. Actually the minimum closed walk needs each proc to increment through its full cycle.
    # So length-2 bad cycles don't exist in this token-ring model!!
    return None

print("NOTE: A length-2 cycle in the 'move' semantics is impossible because")
print("each move increments ONE proc by 1 mod m_p. To return to c in 2 steps")
print("we'd need two procs to each return their values, but only one fires per step.")
print("→ minimum cycle length ≥ 2·lcm({m_p involved}) ≥ 4.")
print()
print("Actually minimum: to return to c we need cumulative fc[p] % m_p == 0 for all p.")
print("Smallest: one proc fires m_p times. So length m_p = 2 (binary) or 3 (ternary).")
print()

# Instead, test minimum-length cycles
def find_min_cycle(w):
    cfg = [0]*N
    gc_configs = [tuple(cfg)]
    for m in w:
        cfg[m] = (cfg[m] + 1) % MS[m]
        gc_configs.append(tuple(cfg))
    gc_configs = gc_configs[:-1]
    gc_set = set(gc_configs)
    mover_triples = {}
    for k, p in enumerate(w):
        cfg = gc_configs[k]
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        mover_triples[(p, L, S, R)] = (S + 1) % MS[p]
    all_configs = list(iproduct(*[range(m) for m in MS]))
    non_gc = [c for c in all_configs if c not in gc_set]
    non_gc_set = set(non_gc)
    edges = {}
    for c in non_gc:
        lst = []
        for p in range(N):
            L, S, R = c[left(p)], c[p], c[right(p)]
            key = (p, L, S, R)
            if key in mover_triples:
                Snew = mover_triples[key]
                if Snew != S:
                    new_c = list(c)
                    new_c[p] = Snew
                    new_c = tuple(new_c)
                    if new_c in non_gc_set:
                        lst.append(new_c)
        edges[c] = lst
    # BFS for shortest cycle
    best = None
    for start in non_gc:
        dist = {start: 0}
        parent = {start: None}
        from collections import deque
        q = deque([start])
        while q:
            u = q.popleft()
            for v in edges.get(u, []):
                if v == start:
                    cyc_len = dist[u] + 1
                    if best is None or cyc_len < best:
                        best = cyc_len
                    break
                if v not in dist:
                    dist[v] = dist[u] + 1
                    parent[v] = u
                    if best is not None and dist[v] >= best: continue
                    q.append(v)
            if best == 2: break
        if best == 2: break
    return best

samples = enumerate_residual(cap=20)
min_lens = []
for i, w in enumerate(samples):
    m = find_min_cycle(w)
    min_lens.append(m)
    print(f"sample {i}: min cycle len = {m}")
