"""Compare mover-triple multiset usage between gc and its bad cycles.
Also: the bad cycle config positions at each fire — do they form
any recognizable pattern?

Additional: for each bad config, find its "closest gc config" by Hamming,
and record the delta pattern. Do these deltas cluster?
"""
import sys
sys.setrecursionlimit(50000)
from itertools import product as iproduct
from collections import Counter

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples, build_edges, find_bad_cycle_from_scc

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24
BIN_PROCS = [0, 3, 6]
TER_PROCS = [1, 2, 4, 5, 7, 8]

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

def cycle_triples(configs, word):
    """Returns list of (p, L, S, R, S') triples used at each step."""
    L = len(word)
    trips = []
    for k in range(L):
        c = configs[k]
        p = word[k]
        trips.append((p, c[left(p)], c[p], c[right(p)]))
    return trips


def cycle_stats(configs, word):
    L = len(word)
    cw = sum(1 for k in range(L) if word[(k+1)%L] == right(word[k]))
    ccw = sum(1 for k in range(L) if word[(k+1)%L] == left(word[k]))
    stay = L - cw - ccw
    fc = Counter(word)
    return cw, ccw, stay, dict(fc)


def hamming(c1, c2):
    return sum(1 for a, b in zip(c1, c2) if a != b)


def main():
    samples = enumerate_residual(cap=5)
    for si, w in enumerate(samples):
        print(f"=== sample {si}: gc_word={''.join(str(x) for x in w)} ===")
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        gc_trips = set(cycle_triples(gc_configs, list(w)))
        mover_triples = build_mover_triples(w, gc_configs)
        print(f"  gc triples: {len(gc_trips)}")
        cw, ccw, stay, fc = cycle_stats(gc_configs, list(w))
        print(f"  gc stats: cw={cw}, ccw={ccw}, stay={stay}, fc={fc}")

        edges = build_edges(mover_triples, gc_set)
        cyc = find_bad_cycle_from_scc(edges, gc_set)
        if cyc is None: continue
        bad_configs = [c for (c, _) in cyc[:-1]]
        bad_word = [p for (_, p) in cyc[1:]]
        bad_trips = set(cycle_triples(bad_configs, bad_word))
        cw_b, ccw_b, stay_b, fc_b = cycle_stats(bad_configs, bad_word)
        print(f"  bad stats: cw={cw_b}, ccw={ccw_b}, stay={stay_b}, fc={fc_b}")
        print(f"  bad triples: {len(bad_trips)}, shared with gc: {len(bad_trips & gc_trips)}")

        # Per-proc triple overlap
        for p in range(N):
            gc_p = [t for t in gc_trips if t[0] == p]
            bad_p = [t for t in bad_trips if t[0] == p]
            shared = [t for t in bad_p if t in gc_trips]
            print(f"    p={p}: gc={len(gc_p)}, bad={len(bad_p)}, shared={len(shared)}")

        # For each bad config, find closest gc config
        deltas = []
        for k, bc in enumerate(bad_configs):
            best_j = 0; best_h = 100
            for j, gc in enumerate(gc_configs):
                h = hamming(bc, gc)
                if h < best_h:
                    best_h = h; best_j = j
            deltas.append((k, best_j, best_h))
        print(f"  closest-gc distances: {[d[2] for d in deltas]}")
        print(f"  closest-gc indices:  {[d[1] for d in deltas]}")
        # Check: is the set of closest gc indices consecutive mod 24?
        idxs = sorted(set(d[1] for d in deltas))
        print(f"  unique closest gc indices: {idxs}")
        print()


if __name__ == '__main__':
    main()
