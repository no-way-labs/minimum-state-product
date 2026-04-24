"""Final verification: the bad-cycle formula produces a valid BadCycleData
equivalent for all 5184 residual samples.

Properties to verify:
  1. bad_word uses only triples in M(gc).
  2. Executing bad_word from seed returns to seed (closed cycle).
  3. All 24 configs visited are distinct (simple cycle).
  4. All 24 configs visited are disjoint from gc_configs.
  5. Each mover step has Snew != S (proper fire).
"""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples
from pa2a_formula_family import candidate_seed

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24


def left(p): return (p - 1) % N
def right(p): return (p + 1) % N


TABLE = {
    9:  (2, 5, 10, 13, 3),
    10: (3, 6, 11, 14, 3),
    11: (4, 7, 12, 15, 3),
    12: (4, 8, 13, 16, 3),
    13: (4, 9, 14, 17, 3),
    14: (4, 7, 15, 17, 2),
    15: (4, 7, 16, 17, 1),
}


def build_tau(pi1, gap, params):
    a_start, a_end, b_start, b_end, tail_size = params
    tau_r = []
    tau_r += list(range(a_start, a_end))           # Block A
    tau_r += list(range(b_start, b_end))            # Block B
    tau_r += [0]                                    # proc 0 fire #1 deferred
    tau_r += [k for k in range(a_end, gap)]         # Block C (middle)
    tau_r += [k for k in range(b_end, CL - tail_size) if k != gap]  # Block D
    tau_r += list(range(1, a_start))                # low tail
    tau_r += [gap]                                  # proc 0 fire #2 deferred
    tau_r += list(range(CL - tail_size, CL))        # trailing tail
    assert len(tau_r) == CL
    assert sorted(tau_r) == list(range(CL))
    tau = [(t + pi1) % CL for t in tau_r]
    return tau


def verify_sample(w, verbose=False):
    p0 = [k for k in range(CL) if w[k] == 0]
    assert len(p0) == 2
    pi1, pi2 = p0
    gap = pi2 - pi1
    if gap not in TABLE:
        return False, f"gap {gap} not in table"
    params = TABLE[gap]
    tau = build_tau(pi1, gap, params)

    gc_configs = build_gc_configs(w)
    gc_set = set(gc_configs)
    mover_triples = build_mover_triples(w, gc_configs)
    bad_word = [w[tau[j]] for j in range(CL)]

    # Seed
    seed = list(gc_configs[(pi1 + params[0]) % CL])
    seed[0] = 1 - seed[0]
    seed = tuple(seed)
    if seed in gc_set:
        return False, "seed in gc"
    # This is equivalent to candidate_seed; let's verify
    alt_seed = candidate_seed(w, tau, 0)
    assert alt_seed == seed, f"seed mismatch {alt_seed} vs {seed}"

    # Execute
    configs = [seed]
    cfg = list(seed)
    for k, p in enumerate(bad_word):
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        key = (p, L, S, R)
        if key not in mover_triples:
            return False, f"step {k}: no triple {key}"
        Snew = mover_triples[key]
        if Snew == S:
            return False, f"step {k}: no-op fire"
        cfg[p] = Snew
        nxt = tuple(cfg)
        if k + 1 < len(bad_word) and nxt in gc_set:
            return False, f"step {k}: lands in gc"
        configs.append(nxt)

    if tuple(cfg) != seed:
        return False, f"not closed"
    cfg_set = set(configs[:-1])
    if len(cfg_set) != CL:
        return False, "not simple"
    # Double-check disjointness
    if cfg_set & gc_set:
        return False, "overlaps gc"
    return True, "OK"


def main():
    samples = enumerate_residual(cap=10000)
    total = len(samples)
    ok = 0
    failures = []
    for si, w in enumerate(samples):
        good, msg = verify_sample(w)
        if good:
            ok += 1
        else:
            failures.append((si, w, msg))
    print(f"Verification: {ok}/{total}")
    if failures:
        print(f"Failures ({len(failures)}):")
        for si, w, msg in failures[:5]:
            print(f"  sample {si}: {''.join(str(x) for x in w)} -> {msg}")


if __name__ == '__main__':
    main()
