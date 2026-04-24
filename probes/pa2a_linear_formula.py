"""Test a clean linear formula:
  a_start = gap - 7
  a_end = gap - 4
  b_start = gap + 1
  b_end = gap + 4
  tail_size = 3
Works for gap in {9,10,11}?
Also test variants to cover gap 12-15."""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples
from pa2a_formula_family import try_execute_word, candidate_seed

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24


def build_tau(pi1, gap, params):
    a_start, a_end, b_start, b_end, tail_size = params
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
    if len(tau_r) != CL: return None
    if sorted(tau_r) != list(range(CL)): return None
    tau = [(t + pi1) % CL for t in tau_r]
    return tau


def test_formula(samples, param_fn, p_star=0):
    ok = 0
    fail = 0
    per_gap = {}
    for si, w in enumerate(samples):
        p0 = [k for k in range(CL) if w[k] == p_star]
        if len(p0) != 2: continue
        pi1, pi2 = p0
        gap = pi2 - pi1
        params = param_fn(gap)
        if params is None:
            per_gap.setdefault(gap, [0,0])[1] += 1
            fail += 1
            continue
        tau = build_tau(pi1, gap, params)
        if tau is None:
            per_gap.setdefault(gap, [0,0])[1] += 1
            fail += 1
            continue
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        bad_word = [w[tau[j]] for j in range(CL)]
        seed = candidate_seed(w, tau, p_star)
        if seed in gc_set:
            per_gap.setdefault(gap, [0,0])[1] += 1
            fail += 1
            continue
        r = try_execute_word(bad_word, seed, mover_triples, gc_set)
        if r is not None:
            ok += 1
            per_gap.setdefault(gap, [0,0])[0] += 1
        else:
            fail += 1
            per_gap.setdefault(gap, [0,0])[1] += 1
    return ok, fail, per_gap


def formula_v1(gap):
    # Linear for gap 9..15
    if 9 <= gap <= 11:
        return (gap - 7, gap - 4, gap + 1, gap + 4, 3)
    if 12 <= gap <= 13:
        return (4, gap - 3, gap + 1, gap + 4, 3)
    if gap == 14:
        return (4, 7, 15, 17, 2)
    if gap == 15:
        return (4, 7, 16, 17, 1)
    return None


def formula_v2(gap):
    # Lookup table from pa2a_canonical_by_gap
    table = {
        9: (2, 5, 10, 13, 3),
        10: (3, 6, 11, 14, 3),
        11: (4, 7, 12, 15, 3),
        12: (4, 8, 13, 16, 3),
        13: (4, 9, 14, 17, 3),
        14: (4, 7, 15, 17, 2),
        15: (4, 7, 16, 17, 1),
    }
    return table.get(gap)


if __name__ == '__main__':
    samples = enumerate_residual(cap=10000)
    print(f"{len(samples)} samples")
    ok, fail, pg = test_formula(samples, formula_v1)
    print(f"Formula v1 (linear): {ok}/{ok+fail}  per-gap: {pg}")
    ok, fail, pg = test_formula(samples, formula_v2)
    print(f"Formula v2 (table):  {ok}/{ok+fail}  per-gap: {pg}")
