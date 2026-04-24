"""Run the extended formula family and capture which (a_start, a_end, b_start, b_end, tail_size)
parameter combinations actually succeed. Do we need all 200 parameter tuples?"""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples
from pa2a_formula_family import try_execute_word, candidate_seed

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24
BIN_PROCS = [0, 3, 6]


def left(p): return (p - 1) % N
def right(p): return (p + 1) % N


def generate_candidate_taus_with_params(w, p_star):
    fires_p = [k for k in range(CL) if w[k] == p_star]
    if len(fires_p) != 2: return []
    pi1, pi2 = fires_p
    gap = (pi2 - pi1) % CL
    if gap < 4 or gap > CL - 4: return []
    results = []
    for a_start in [2, 3, 4]:
        for a_end in range(a_start + 3, min(gap, 12)):
            for b_start in range(gap + 1, min(gap + 5, CL)):
                for b_end in range(b_start + 1, min(b_start + 5, CL)):
                    for tail_size in [1, 2, 3]:
                        try:
                            tau_r = []
                            tau_r += list(range(a_start, a_end))
                            tau_r += list(range(b_start, b_end))
                            tau_r += [0]
                            c_block = [k for k in range(a_end, gap)]
                            tau_r += c_block
                            d_block = [k for k in range(b_end, CL - tail_size) if k != gap]
                            tau_r += d_block
                            low_tail = list(range(1, a_start))
                            tau_r += low_tail
                            tau_r += [gap]
                            tail_block = [k for k in range(CL - tail_size, CL)]
                            tau_r += tail_block
                            if len(tau_r) != CL: continue
                            if sorted(tau_r) != list(range(CL)): continue
                            tau = [(t + pi1) % CL for t in tau_r]
                            params = (a_start, a_end, b_start, b_end, tail_size)
                            results.append((tau, params))
                        except Exception:
                            pass
    return results


def main():
    samples = enumerate_residual(cap=500)
    print(f"Testing {len(samples)} samples\n")
    success_params = {}
    total_valid = 0
    best_first_params = {}
    from collections import Counter
    first_success_counter = Counter()
    for si, w in enumerate(samples):
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        p_star = 0
        taus_params = generate_candidate_taus_with_params(w, p_star)
        valid_params = []
        first = None
        for tau, params in taus_params:
            bad_word = [w[tau[j]] for j in range(CL)]
            seed = candidate_seed(w, tau, p_star)
            if seed in gc_set: continue
            r = try_execute_word(bad_word, seed, mover_triples, gc_set)
            if r is not None:
                valid_params.append(params)
                if first is None:
                    first = params
        if valid_params:
            total_valid += 1
            if first is not None:
                first_success_counter[first] += 1
        else:
            print(f"sample {si}: NO valid tau (gap?)")
    print(f"\nTotal valid: {total_valid}/{len(samples)}")
    print(f"\nFirst-success param distribution:")
    for p, c in first_success_counter.most_common(30):
        print(f"  {p}: {c}")


if __name__ == '__main__':
    main()
