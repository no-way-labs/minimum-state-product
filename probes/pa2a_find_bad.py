"""PA-2a: Find bad cycles across many residual samples. For each sample,
extract *all* length-24 cycles in H(gc)\gc starting from a canonical seed.
Look for structural relationship between bad cycle mover word and gc word.

Key questions:
- Is there a clean transform bad_word = T(gc_word)?
- Does the bad cycle correspond to a specific shift/flip of gc configs?
- Can we characterize the bad cycle via *mover-triple reuse* rules?

Outputs a CSV-like table of invariants per sample for pattern recognition.
"""
import sys
sys.setrecursionlimit(30000)
from itertools import product as iproduct
from collections import Counter, defaultdict

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24
BIN_PROCS = [p for p in range(N) if MS[p] == 2]  # [0, 3, 6]
TER_PROCS = [p for p in range(N) if MS[p] > 2]   # [1,2,4,5,7,8]

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

# Residual enumerator (copied from pa_universal_scc)
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


def build_gc_configs(w):
    cfg = [0]*N
    gc_configs = [tuple(cfg)]
    for m in w:
        cfg[m] = (cfg[m] + 1) % MS[m]
        gc_configs.append(tuple(cfg))
    return gc_configs[:-1]


def build_mover_triples(w, gc_configs):
    """Returns dict (p, L, S, R) -> S' (= (S+1)%MS[p])."""
    mover_triples = {}
    for k, p in enumerate(w):
        cfg = gc_configs[k]
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        mover_triples[(p, L, S, R)] = (S + 1) % MS[p]
    return mover_triples


def build_edges(mover_triples, gc_set):
    """Forward edges c -> (c', p) valid in H(gc)."""
    all_configs = list(iproduct(*[range(m) for m in MS]))
    edges = {}
    for c in all_configs:
        if c in gc_set: continue
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
                    if new_c not in gc_set:
                        lst.append((new_c, p))
        edges[c] = lst
    return edges


def find_shortest_cycle_from(start, edges):
    """Shortest simple cycle starting/ending at start using BFS-like DP."""
    from collections import deque
    # BFS from start, but track paths; return first time we reach start
    # via length >= 1. Since branching is low, we use DFS with bound.
    # We'll do iterative DFS for shortest cycle up to length cap.
    best = None
    stack = [(start, [start])]
    cap = 30
    def dfs(node, path, visited):
        nonlocal best
        if best and len(path) >= len(best): return
        for (nxt, p) in edges.get(node, []):
            if nxt == start and len(path) >= 2:
                cand = path[:]
                if best is None or len(cand) < len(best):
                    best = cand
                continue
            if nxt in visited: continue
            if len(path) >= cap: continue
            visited.add(nxt)
            path.append(nxt)
            dfs(nxt, path, visited)
            path.pop()
            visited.remove(nxt)
    dfs(start, [start], {start})
    return best


def find_any_24_cycle(edges):
    """Find one length-24 cycle anywhere in non-gc subgraph via DFS."""
    seen_globally = set()
    for start in edges:
        if start in seen_globally: continue
        # DFS bounded to depth 24, looking for return
        visited = {start: 0}
        result = [None]
        def dfs(node, depth):
            if result[0] is not None: return
            for (nxt, p) in edges.get(node, []):
                if nxt == start and depth + 1 == 24:
                    result[0] = [start] + [None]  # placeholder
                    return
                if nxt in visited: continue
                if depth + 1 >= 24: continue
                visited[nxt] = depth + 1
                dfs(nxt, depth + 1)
                if result[0] is not None: return
                del visited[nxt]
        dfs(start, 0)
        if result[0] is not None:
            return start
        seen_globally.add(start)
    return None


def find_bad_cycle_from_scc(edges, gc_set):
    """Use Tarjan to find SCCs, pick one and extract any cycle in it.
    Return list of (cfg, proc) pairs cycling through."""
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
    for c in edges:
        if c not in index:
            strongconnect(c)
    nontriv = [s for s in sccs if len(s) > 1 or any(e2 == s[0] for (e2,_) in edges.get(s[0], []))]
    if not nontriv: return None
    # Pick the largest SCC (usually length-24 cycles lie in big SCCs)
    s = max(nontriv, key=len)
    s_set = set(s)
    # Try to find a simple cycle of length exactly 24 starting from any node in SCC
    for start in s:
        path = [(start, None)]
        visited = {start}
        found = [None]
        def dfs(node, depth):
            if found[0] is not None: return
            for (nxt, p) in edges.get(node, []):
                if nxt not in s_set: continue
                if nxt == start and depth + 1 == 24:
                    found[0] = path + [(start, p)]
                    return
                if nxt in visited: continue
                if depth + 1 >= 24: continue
                visited.add(nxt)
                path.append((nxt, p))
                dfs(nxt, depth + 1)
                if found[0] is not None: return
                path.pop()
                visited.remove(nxt)
        dfs(start, 0)
        if found[0] is not None:
            return found[0]  # [(c0, None), (c1, p0), ..., (c0, p23)]
    # Fall back: any simple cycle in SCC (length may vary)
    for start in s[:20]:
        path = [(start, None)]
        visited = {start}
        found = [None]
        def dfs2(node, depth):
            if found[0] is not None: return
            for (nxt, p) in edges.get(node, []):
                if nxt not in s_set: continue
                if nxt == start and depth + 1 >= 2:
                    found[0] = path + [(start, p)]
                    return
                if nxt in visited: continue
                if depth + 1 >= 30: continue
                visited.add(nxt)
                path.append((nxt, p))
                dfs2(nxt, depth + 1)
                if found[0] is not None: return
                path.pop()
                visited.remove(nxt)
        dfs2(start, 0)
        if found[0] is not None:
            return found[0]
    return None


def analyze_sample(w, verbose=False):
    gc_configs = build_gc_configs(w)
    gc_set = set(gc_configs)
    mover_triples = build_mover_triples(w, gc_configs)
    edges = build_edges(mover_triples, gc_set)
    cyc = find_bad_cycle_from_scc(edges, gc_set)
    if cyc is None: return None
    # cyc = [(c0, None), (c1, p0), (c2, p1), ..., (cL, p_{L-1})]
    # with cL = c0
    bad_configs = [c for (c, _) in cyc[:-1]]
    bad_word = [p for (_, p) in cyc[1:]]
    return {
        'gc_word': w,
        'gc_configs': gc_configs,
        'bad_configs': bad_configs,
        'bad_word': bad_word,
        'bad_len': len(bad_word),
    }


if __name__ == '__main__':
    import os
    samples = enumerate_residual(cap=30)
    print(f"Found {len(samples)} residuals")
    # Analyze first 20
    data = []
    for i, w in enumerate(samples[:20]):
        r = analyze_sample(w)
        if r is None:
            print(f"Sample {i}: NO CYCLE"); continue
        print(f"Sample {i}: bad_len={r['bad_len']}, gc_word={''.join(str(x) for x in w)}")
        print(f"           bad_word={''.join(str(x) for x in r['bad_word'])}")
        data.append(r)
    # Save data to pickle-like tsv
    import json
    out = []
    for r in data:
        out.append({
            'gc_word': list(r['gc_word']),
            'gc_configs': [list(c) for c in r['gc_configs']],
            'bad_configs': [list(c) for c in r['bad_configs']],
            'bad_word': r['bad_word'],
        })
    out_path = os.environ.get('PA2A_OUT', '/tmp/probes/pa2a_samples.json')
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, 'w') as f:
        json.dump(out, f)
    print(f"Saved {len(out)} samples")
