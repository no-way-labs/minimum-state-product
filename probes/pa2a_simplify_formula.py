"""Try to reduce the 7-case table to a 2- or 3-case formula.
Also: check if a single parameter tuple covers multiple gaps."""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples
from pa2a_formula_family import try_execute_word, candidate_seed
from pa2a_formula_stats import generate_candidate_taus_with_params

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24


def main():
    samples = enumerate_residual(cap=5184)
    # Which single param tuple covers the most gaps?
    # For each param tuple, count gaps it works on and samples it works on
    from collections import defaultdict
    param_success = defaultdict(lambda: {'total': 0, 'by_gap': defaultdict(int)})
    for si, w in enumerate(samples):
        p0 = [k for k in range(CL) if w[k] == 0]
        gap = p0[1] - p0[0]
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        for tau, params in generate_candidate_taus_with_params(w, 0):
            bad_word = [w[tau[j]] for j in range(CL)]
            seed = candidate_seed(w, tau, 0)
            if seed in gc_set: continue
            r = try_execute_word(bad_word, seed, mover_triples, gc_set)
            if r is not None:
                param_success[params]['total'] += 1
                param_success[params]['by_gap'][gap] += 1

    # Report: params that work for the most gaps
    ranked = sorted(param_success.items(), key=lambda x: (-len(x[1]['by_gap']), -x[1]['total']))
    print("Top params by gap coverage:")
    for p, info in ranked[:20]:
        print(f"  {p}: total={info['total']}, gaps={dict(info['by_gap'])}")


if __name__ == '__main__':
    main()
