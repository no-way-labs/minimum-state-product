"""Debug failures of formula family."""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples, build_edges
from pa2a_perm_analysis import find_one_bad_cycle, analyze_sigma
from pa2a_formula_family import generate_candidate_taus, candidate_seed, try_execute_word

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24
BIN_PROCS = [0, 3, 6]


def main():
    samples = enumerate_residual(cap=200)
    for si in [129, 130, 131, 132, 100, 150]:
        if si >= len(samples): continue
        w = samples[si]
        print(f"=== Sample {si}: gc_word={''.join(str(x) for x in w)} ===")
        for p in BIN_PROCS:
            fires = [k for k in range(CL) if w[k] == p]
            print(f"  p={p} fires @ {fires}")
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        edges = build_edges(mover_triples, gc_set)
        cyc = find_one_bad_cycle(edges)
        if cyc is None:
            print("  NO BAD CYCLE exists at all!"); continue
        r = analyze_sigma(w, cyc)
        if r is None: continue
        sigma, _, _ = r
        tau_true = [0]*CL
        for k, v in enumerate(sigma):
            tau_true[v] = k
        print(f"  actual tau = {tau_true}")
        # Try formula T for each p_star
        for p_star in BIN_PROCS:
            taus = generate_candidate_taus(w, p_star)
            print(f"  p_star={p_star}: {len(taus)} candidate taus generated")
            for ti, tau in enumerate(taus):
                bad_word = [w[tau[j]] for j in range(CL)]
                seed = candidate_seed(w, tau, p_star)
                if seed in gc_set:
                    print(f"    tau[{ti}]: seed in gc")
                    continue
                r2 = try_execute_word(bad_word, seed, mover_triples, gc_set)
                status = "OK" if r2 is not None else "FAIL"
                print(f"    tau[{ti}] = {tau}  {status}")
        print()


if __name__ == '__main__':
    main()
