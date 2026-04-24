"""Compute a canonical parameter tuple per gap value, and verify the
resulting formula works on all 500 samples."""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples
from pa2a_formula_family import try_execute_word, candidate_seed
from pa2a_formula_stats import generate_candidate_taus_with_params

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24


def main():
    samples = enumerate_residual(cap=2000)
    from collections import defaultdict
    by_gap = defaultdict(list)  # gap -> list of (sample_idx, w, valid_params)
    for si, w in enumerate(samples):
        p0 = [k for k in range(CL) if w[k] == 0]
        gap = p0[1] - p0[0]
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
        by_gap[gap].append((si, w, valid))

    canonical_per_gap = {}
    for gap in sorted(by_gap):
        vs = by_gap[gap]
        inter = vs[0][2]
        for (_, _, v) in vs[1:]:
            inter = inter & v
        print(f"\ngap={gap}: {len(vs)} samples, intersection size={len(inter)}")
        if inter:
            chosen = min(inter)  # lex-min for determinism
            canonical_per_gap[gap] = chosen
            print(f"  canonical params = {chosen}")

    # Now verify that using canonical_per_gap[gap] works for all samples
    total = 0
    valid_count = 0
    for si, w in enumerate(samples):
        p0 = [k for k in range(CL) if w[k] == 0]
        gap = p0[1] - p0[0]
        if gap not in canonical_per_gap:
            continue
        params = canonical_per_gap[gap]
        # Generate tau with these params
        taus_params = generate_candidate_taus_with_params(w, 0)
        match = [(tau, p) for (tau, p) in taus_params if p == params]
        if not match:
            print(f"sample {si}: no tau matching canonical params {params}")
            continue
        tau, _ = match[0]
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        bad_word = [w[tau[j]] for j in range(CL)]
        seed = candidate_seed(w, tau, 0)
        if seed in gc_set: continue
        r = try_execute_word(bad_word, seed, mover_triples, gc_set)
        total += 1
        if r is not None:
            valid_count += 1
    print(f"\nCanonical per-gap formula: {valid_count}/{total} samples")
    print(f"\nCanonical table:")
    for gap, params in sorted(canonical_per_gap.items()):
        print(f"  gap={gap}: {params}")


if __name__ == '__main__':
    main()
