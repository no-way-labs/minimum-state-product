"""Key finding from triple_structure: bad cycles reuse the same 24 mover
triples as gc (same multiset, same per-proc counts). So bad is a
*reordering* of the 24 mover events.

Strategy: search for a bad cycle by **permuting gc's word** with simple
structural transformations and checking validity.

For each transformation T, the transformed word w' generates a bad cycle
starting from some start_config if:
  - Starting at start_config, executing w' visits configs c_0, c_1, ..., c_{24}=c_0
  - All configs disjoint from gc_configs
  - Every fire w'[k] at c_k has triple (p, L, S, R) ∈ M(gc) and target (S+1) mod m_p

Transformations to try:
  T1: shift (rotate): w'[k] = w[(k+d) mod 24] starting at gc_configs[d] — this is gc itself, skip
  T2: reverse: w'[k] = w[CL-1-k]  (with appropriate start)
  T3: swap_halves: w'[k] = w[(k+12) mod 24]
  T4: reverse_half1_keep_half2, etc.
  T5: block-reverse each ternary "chunk"
  T6: **Apply gc's word starting at a different config not in gc_configs**

T6 is particularly interesting: if we start at some seed config c* ∉ gc
and execute gc's word step-by-step, each fire needs a valid mover triple.
Does there exist a c* such that all 24 steps of executing w work?

More general: search for `(w', start_config)` such that executing w' from
start produces a length-24 cycle using gc's triples only.
"""
import sys
sys.setrecursionlimit(50000)
from itertools import product as iproduct, permutations
from collections import Counter

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24
BIN_PROCS = [0, 3, 6]
TER_PROCS = [1, 2, 4, 5, 7, 8]

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N


def try_execute_word(word, start_cfg, mover_triples, gc_set):
    """Simulate executing the word from start. Returns list of configs if valid
    cycle, else None.
    'valid' = every fire uses a triple in mover_triples (so the target is the
    forced increment), all intermediate configs are not in gc_set, and the
    final config equals start.
    """
    configs = [start_cfg]
    cfg = list(start_cfg)
    for p in word:
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        key = (p, L, S, R)
        if key not in mover_triples:
            return None
        Snew = mover_triples[key]
        if Snew == S: return None
        cfg[p] = Snew
        nxt = tuple(cfg)
        if len(configs) < len(word) and nxt in gc_set:
            return None
        configs.append(nxt)
    if tuple(cfg) != start_cfg:
        return None
    # All intermediate configs must be non-gc
    for c in configs[:-1]:
        if c in gc_set: return None
    # Simple cycle (distinct)
    if len(set(configs[:-1])) != len(configs[:-1]):
        return None
    return configs[:-1]


def sweep_starts(word, mover_triples, gc_set, all_configs):
    """For a given word, enumerate all possible start configs and check if any yields a valid bad cycle."""
    hits = []
    for c in all_configs:
        if c in gc_set: continue
        r = try_execute_word(word, c, mover_triples, gc_set)
        if r is not None:
            hits.append((c, r))
    return hits


def main():
    samples = enumerate_residual(cap=10)
    all_configs = list(iproduct(*[range(m) for m in MS]))
    print(f"Enumerated {len(samples)} residuals, {len(all_configs)} total configs")

    for si, w in enumerate(samples[:3]):
        print(f"\n=== sample {si}: gc_word={''.join(str(x) for x in w)} ===")
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        # Verify gc is a cycle using only its own mover triples
        r = try_execute_word(list(w), (0,)*N, mover_triples, set())  # no gc filter
        print(f"  gc re-executable from (0,...,0): {r is not None}")

        # T2: reverse
        rev = list(reversed(w))
        hits = sweep_starts(rev, mover_triples, gc_set, all_configs)
        print(f"  reverse: {len(hits)} valid start configs")

        # T3: half-swap
        swap = list(w[12:] + w[:12])
        hits = sweep_starts(swap, mover_triples, gc_set, all_configs)
        print(f"  halves swapped: {len(hits)} valid starts")

        # T4: try shifting w and starting at various configs (searches for ANY word = w rotation with different start)
        for d in range(CL):
            rot = list(w[d:] + w[:d])
            hits = sweep_starts(rot, mover_triples, gc_set, all_configs)
            if hits:
                print(f"  shift d={d}: {len(hits)} valid starts")

        # T6: execute w from all starts
        hits = sweep_starts(list(w), mover_triples, gc_set, all_configs)
        print(f"  w itself (all starts): {len(hits)} valid starts, gc is one of them: {any(h[0] == (0,)*N for h in hits)}")


if __name__ == '__main__':
    main()
