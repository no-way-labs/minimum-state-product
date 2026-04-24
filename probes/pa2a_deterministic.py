"""Find a deterministic rule: parameters = f(gc_word), where f is simple.
For each sample, record which parameter tuple is the "first that works" in a
fixed enumeration order. Check if the mapping is consistent.
"""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples
from pa2a_formula_family import try_execute_word, candidate_seed
from pa2a_formula_stats import generate_candidate_taus_with_params

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24


def gc_signature(w):
    """Features of gc that might determine the parameters."""
    p0 = [k for k in range(CL) if w[k] == 0]
    p3 = [k for k in range(CL) if w[k] == 3]
    p6 = [k for k in range(CL) if w[k] == 6]
    return (tuple(p0), tuple(p3), tuple(p6))


def find_valid_params(w, gc_set, mover_triples, p_star=0):
    """Return list of valid parameter tuples for this gc."""
    valid = []
    taus_params = generate_candidate_taus_with_params(w, p_star)
    for tau, params in taus_params:
        bad_word = [w[tau[j]] for j in range(CL)]
        seed = candidate_seed(w, tau, p_star)
        if seed in gc_set: continue
        r = try_execute_word(bad_word, seed, mover_triples, gc_set)
        if r is not None:
            valid.append(params)
    return valid


def main():
    samples = enumerate_residual(cap=500)
    # Check if signature determines param choice
    sig_to_params = {}
    for si, w in enumerate(samples):
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        valid = find_valid_params(w, gc_set, mover_triples)
        if not valid: continue
        sig = gc_signature(w)
        if sig not in sig_to_params:
            sig_to_params[sig] = []
        sig_to_params[sig].append(valid)
    # For each signature, is the first-valid param deterministic across samples with that sig?
    n_sigs = len(sig_to_params)
    consistent = 0
    inconsistent = 0
    for sig, valid_lists in sig_to_params.items():
        firsts = set(vl[0] for vl in valid_lists)
        if len(firsts) == 1:
            consistent += 1
        else:
            inconsistent += 1
    print(f"Signatures: {n_sigs}, consistent first-valid: {consistent}, inconsistent: {inconsistent}")
    # Also: can we find a parameter tuple that works universally for a given sig?
    # Intersection of valid_lists for each sig
    universal_per_sig = 0
    for sig, valid_lists in sig_to_params.items():
        sets = [set(vl) for vl in valid_lists]
        intersect = sets[0]
        for s in sets[1:]:
            intersect &= s
        if intersect:
            universal_per_sig += 1
    print(f"Sigs with a universal parameter: {universal_per_sig}/{n_sigs}")


if __name__ == '__main__':
    main()
