"""Look at the STRUCTURAL properties of bad cycles found in the gc-determined
non-gc subgraph. For the 20 samples, find a length-24 cycle, then compute:
- mover word
- fc
- winding (cw, ccw)
- relationship to gc configs (which subset of gc configs is hit after forcing?)
- common "invariant" across all bad cycles
"""
import sys
sys.setrecursionlimit(30000)
from itertools import product as iproduct
from collections import Counter

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

def find_bad_cycle(w):
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
    non_gc_set = set(all_configs) - gc_set
    edges = {}
    for c in non_gc_set:
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
                        lst.append((new_c, p))
        edges[c] = lst
    # Find any cycle via SCC
    index = {}; lowlink = {}; on_stack = {}; stack = []
    idx_counter = [0]; sccs = []
    def strongconnect(v):
        work = [(v, 0)]
        while work:
            v, pi = work[-1]
            if v not in index:
                index[v] = idx_counter[0]
                lowlink[v] = idx_counter[0]
                idx_counter[0] += 1
                stack.append(v)
                on_stack[v] = True
            neighbors = [c2 for (c2, _) in edges.get(v, [])]
            if pi < len(neighbors):
                work[-1] = (v, pi+1)
                wnode = neighbors[pi]
                if wnode not in index:
                    work.append((wnode, 0))
                elif on_stack.get(wnode):
                    lowlink[v] = min(lowlink[v], index[wnode])
            else:
                if lowlink[v] == index[v]:
                    scc = []
                    while True:
                        wnode = stack.pop()
                        on_stack[wnode] = False
                        scc.append(wnode)
                        if wnode == v: break
                    sccs.append(scc)
                work.pop()
                if work:
                    u = work[-1][0]
                    lowlink[u] = min(lowlink[u], lowlink[v])
    for c in non_gc_set:
        if c not in index:
            strongconnect(c)
    # DFS within smallest non-trivial SCC to find an actual cycle
    for s in sorted(sccs, key=len):
        if len(s) == 1:
            if not any(e2 == s[0] for (e2,_) in edges.get(s[0], [])):
                continue
        s_set = set(s)
        start = s[0]
        # DFS with tracking to find a cycle starting at start
        path = []
        visited_in_path = {}
        def dfs2(node):
            if node in visited_in_path:
                return path[visited_in_path[node]:]
            visited_in_path[node] = len(path)
            for (nxt, p) in edges.get(node, []):
                if nxt not in s_set: continue
                path.append((node, p))
                res = dfs2(nxt)
                if res is not None: return res
                path.pop()
            del visited_in_path[node]
            return None
        result = dfs2(start)
        if result: return result, gc_configs, gc_set, mover_triples
    return None, gc_configs, gc_set, mover_triples

samples = enumerate_residual(cap=5)
for i, w in enumerate(samples):
    print(f"=== sample {i} ===")
    print(f"gc word: {w}")
    result, gc_configs, gc_set, mover_triples = find_bad_cycle(w)
    if result is None:
        print("  no bad cycle"); continue
    bad_word = tuple(p for (_, p) in result)
    bad_configs = [c for (c, _) in result]
    bad_len = len(bad_word)
    fc = Counter(bad_word)
    cw = sum(1 for k in range(bad_len) if bad_word[(k+1)%bad_len] == right(bad_word[k]))
    ccw = sum(1 for k in range(bad_len) if bad_word[(k+1)%bad_len] == left(bad_word[k]))
    stay = bad_len - cw - ccw
    print(f"bad cycle: len={bad_len}, fc={dict(fc)}, cw={cw}, ccw={ccw}, stay={stay}")

    # For each bad config, find the gc step k* such that bad_cfg matches gc[k*] at all ternary procs
    # AND shows the binary flip pattern
    bin_procs = [p for p in range(N) if MS[p]==2]
    ter_procs = [p for p in range(N) if MS[p]>2]
    print(f"  matching gc configs by ternary projection:")
    for k, bc in enumerate(bad_configs[:24]):
        ter_proj = tuple(bc[p] for p in ter_procs)
        matches = []
        for j, gc in enumerate(gc_configs):
            if all(gc[p] == bc[p] for p in ter_procs):
                matches.append(j)
        bin_vals = [bc[p] for p in bin_procs]
        gc_bin_at_matches = [[gc_configs[j][p] for p in bin_procs] for j in matches[:3]]
        print(f"  bad[{k:2d}] bin={bin_vals} ter_match_gc_idx={matches[:4]} gc_bin_at_matches={gc_bin_at_matches}")
    break
