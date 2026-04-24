"""Can a simpler signature (just the p0 gap, or p0+p3+p6 gaps) determine
a valid parameter tuple? Find the minimum sufficient signature."""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples
from pa2a_formula_family import try_execute_word, candidate_seed
from pa2a_formula_stats import generate_candidate_taus_with_params

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24


def main():
    samples = enumerate_residual(cap=500)
    # For each sample, find ALL valid param tuples
    sample_valid = []
    for si, w in enumerate(samples):
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        valid = set()
        for tau, params in generate_candidate_taus_with_params(w, 0):
            bad_word = [w[tau[j]] for j in range(CL)]
            seed = candidate_seed(w, tau, 0)
            if seed in gc_set: continue
            r = try_execute_word(bad_word, seed, mover_triples, gc_set)
            if r is not None:
                valid.add(params)
        # Signature = all 6 binary fire positions
        p0 = tuple(k for k in range(CL) if w[k] == 0)
        p3 = tuple(k for k in range(CL) if w[k] == 3)
        p6 = tuple(k for k in range(CL) if w[k] == 6)
        sig_full = (p0, p3, p6)
        sig_p0 = p0
        sig_pgap = (p0[1] - p0[0],)
        sample_valid.append((si, w, sig_full, sig_p0, sig_pgap, valid))

    # Global intersection over ALL samples
    global_intersect = None
    for (si, w, _, _, _, valid) in sample_valid:
        if global_intersect is None:
            global_intersect = set(valid)
        else:
            global_intersect &= valid
    print(f"Globally-universal params (work on all 500 samples): {len(global_intersect) if global_intersect else 0}")

    # By p0 positions
    from collections import defaultdict
    by_p0 = defaultdict(list)
    for (si, w, _, sig_p0, _, valid) in sample_valid:
        by_p0[sig_p0].append(valid)
    print(f"\nBy p0 positions: {len(by_p0)} classes")
    consistent_by_p0 = 0
    for sig, vs in by_p0.items():
        inter = vs[0]
        for v in vs[1:]:
            inter = inter & v
        if inter:
            consistent_by_p0 += 1
    print(f"  classes with non-empty intersection: {consistent_by_p0}")

    # By gap only
    by_gap = defaultdict(list)
    for (si, w, _, _, sig_gap, valid) in sample_valid:
        by_gap[sig_gap].append(valid)
    print(f"\nBy gap only: {len(by_gap)} classes")
    for sig, vs in by_gap.items():
        inter = vs[0]
        for v in vs[1:]:
            inter = inter & v
        print(f"  gap={sig[0]}: {len(vs)} samples, intersection size={len(inter) if inter else 0}")


if __name__ == '__main__':
    main()
