"""Search for a "canonical" construction: simple, parameter-free rule that
produces a bad cycle from gc.

Candidate constructions (all must be checked for validity):
C1: Start at a flipped proc-0 seed; greedy fire using gc's triples (always
    pick proc = gc_word[k] if valid; else try other procs).
C2: Greedy: from any non-gc config, always fire the lowest-proc valid
    triple until we close.
C3: Take bad cycle as gc's word rotated by d, starting at different seed;
    tweak at collisions.

Main focus: try to find a **seed config** and **word** such that running
the word from the seed produces a valid bad cycle.

If sigma exists, then bad_word[j] = gc_word[τ(j)] where τ = σ^{-1}.
Let's extract a short "rule" for τ per sample and see if the rules are
parametrized by O(1) integers.
"""
import sys
sys.setrecursionlimit(50000)
from collections import defaultdict

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples, build_edges
from pa2a_perm_analysis import find_one_bad_cycle, analyze_sigma

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24


def sigma_to_desc(sigma):
    """Describe sigma as: identity on some range, with a few points moved."""
    # Find inverse tau: tau[j] = the k with sigma[k] = j
    tau = [0]*CL
    for k, v in enumerate(sigma):
        tau[v] = k
    return tau


def find_binary_fires(w):
    """Positions of binary (proc 0, 3, 6) fires in gc_word."""
    return {p: [k for k, m in enumerate(w) if m == p] for p in [0, 3, 6]}


def main():
    samples = enumerate_residual(cap=40)
    for si, w in enumerate(samples[:20]):
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        edges = build_edges(mover_triples, gc_set)
        cyc = find_one_bad_cycle(edges)
        if cyc is None: continue
        r = analyze_sigma(w, cyc)
        if r is None: continue
        sigma, _, _ = r
        tau = sigma_to_desc(sigma)
        bin_fires = find_binary_fires(w)
        print(f"Sample {si}: gc_word={''.join(str(x) for x in w)}")
        print(f"  binary fires: p0@{bin_fires[0]}, p3@{bin_fires[3]}, p6@{bin_fires[6]}")
        print(f"  tau={tau}")
        # Find the "deltas" — tau[j] - j mod 24
        deltas = [(tau[j] - j) % CL for j in range(CL)]
        print(f"  deltas={deltas}")
        # Find positions where tau[j] != j (what's moved)
        moved = [(j, tau[j]) for j in range(CL) if tau[j] != j]
        print(f"  moved pairs (j, tau[j]): {moved}")
        print()


if __name__ == '__main__':
    main()
