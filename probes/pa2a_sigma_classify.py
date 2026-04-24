"""Classify the sigmas across all residuals. How many distinct sigmas?
Do they correlate with gc word structure?"""
import sys
sys.setrecursionlimit(50000)
from collections import Counter, defaultdict

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples, build_edges
from pa2a_perm_analysis import find_one_bad_cycle, analyze_sigma

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24


def main():
    samples = enumerate_residual(cap=200)
    print(f"{len(samples)} residuals")
    sigmas_seen = Counter()
    per_sample = []
    for si, w in enumerate(samples):
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        edges = build_edges(mover_triples, gc_set)
        cyc = find_one_bad_cycle(edges)
        if cyc is None:
            per_sample.append((si, w, None))
            continue
        r = analyze_sigma(w, cyc)
        if r is None:
            per_sample.append((si, w, None))
            continue
        sigma, gc_trips, bad_trips = r
        sigmas_seen[tuple(sigma)] += 1
        per_sample.append((si, w, sigma))
    print(f"Distinct sigmas: {len(sigmas_seen)}")
    for sig, cnt in sigmas_seen.most_common(20):
        print(f"  count={cnt}: {list(sig)}")


if __name__ == '__main__':
    main()
