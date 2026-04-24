"""Both gc and bad use the same 24 mover triples (as a multiset, with each
triple appearing exactly once per sample: all 24 are distinct).
So there is a well-defined permutation sigma: gc_step_index -> bad_step_index
such that the triple fired at step sigma(k) in bad equals the triple fired
at step k in gc.

Scan sigma across samples — is it a universal permutation? Or does it depend
on gc?

Also: the bad cycle need not be unique. There may be MANY valid bad cycles.
We want at least ONE consistent formula.

Strategy: enumerate length-24 simple cycles in the gc-determined subgraph,
for each compute sigma, and look at the space of sigmas. Is there a
"canonical" sigma that always exists?
"""
import sys
sys.setrecursionlimit(50000)
from itertools import product as iproduct
from collections import Counter

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples, build_edges

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24
BIN_PROCS = [0, 3, 6]
TER_PROCS = [1, 2, 4, 5, 7, 8]

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N


def triple_at(configs, word, k):
    c = configs[k]
    p = word[k]
    return (p, c[left(p)], c[p], c[right(p)])


def find_one_bad_cycle(edges):
    """DFS-based: find one simple length-24 cycle. Iterative, bounded."""
    for start in edges:
        if not edges.get(start): continue
        visited = {start}
        path = [(start, None)]
        found = [None]
        def dfs(node, depth):
            if found[0] is not None: return
            for (nxt, p) in edges.get(node, []):
                if nxt == start and depth + 1 == 24:
                    found[0] = list(path) + [(start, p)]
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
            return found[0]
    return None


def analyze_sigma(w, bad_cyc):
    gc_configs = build_gc_configs(w)
    gc_trips = [triple_at(gc_configs, list(w), k) for k in range(CL)]
    # bad_cyc: [(c0, None), (c1, p0), ..., (c24=c0, p23)]
    bad_configs = [c for (c, _) in bad_cyc[:-1]]
    bad_word = [p for (_, p) in bad_cyc[1:]]
    bad_trips = [triple_at(bad_configs, bad_word, k) for k in range(CL)]
    # Find sigma: gc_trips[k] = bad_trips[sigma(k)]
    # (Since all 24 triples distinct)
    trip_to_bad_idx = {t: i for i, t in enumerate(bad_trips)}
    sigma = []
    for k in range(CL):
        if gc_trips[k] not in trip_to_bad_idx:
            return None
        sigma.append(trip_to_bad_idx[gc_trips[k]])
    return sigma, gc_trips, bad_trips


def main():
    samples = enumerate_residual(cap=20)
    print(f"Enumerated {len(samples)} residuals")
    for si, w in enumerate(samples):
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        edges = build_edges(mover_triples, gc_set)
        cyc = find_one_bad_cycle(edges)
        if cyc is None:
            print(f"sample {si}: no cycle"); continue
        r = analyze_sigma(w, cyc)
        if r is None:
            print(f"sample {si}: sigma not well-defined"); continue
        sigma, gc_trips, bad_trips = r
        print(f"sample {si}: gc_word={''.join(str(x) for x in w)}")
        print(f"  sigma = {sigma}")
        # Compute the word positions (not triples) for bad
        bad_word = [t[0] for t in bad_trips]
        print(f"  bad_word = {''.join(str(x) for x in bad_word)}")
        gc_word = list(w)
        # Is sigma a simple thing like "k + 12 mod 24" applied twice?
        # Check sigma(sigma(k)) == k (involution?)
        is_involution = all(sigma[sigma[k]] == k for k in range(CL))
        # Fixed points
        fp = [k for k in range(CL) if sigma[k] == k]
        print(f"  involution: {is_involution}, fixed points: {fp}")
        # Cycle structure of sigma
        visited = [False] * CL
        cycles_sig = []
        for k in range(CL):
            if visited[k]: continue
            cyc_s = []
            j = k
            while not visited[j]:
                visited[j] = True
                cyc_s.append(j)
                j = sigma[j]
            cycles_sig.append(cyc_s)
        lens = sorted([len(c) for c in cycles_sig])
        print(f"  sigma cycle lengths: {lens}")
        print()


if __name__ == '__main__':
    main()
