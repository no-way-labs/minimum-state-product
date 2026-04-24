"""Test formula T:

Given gc with proc-0 fires at π1 < π2, define:

tau = [2,3,4,5,6,7, π2+1,π2+2,π2+3, 0, 8..π2-1, π2+4..22, 1, π2, 23]

bad_word[j] = gc_word[tau[j]]
bad_cfg[0] = gc_cfg[2] with proc 0 flipped

Check: starting at bad_cfg[0] and executing bad_word gives a closed walk
disjoint from gc.

Restriction: requires π1 = 0 (probably true after relabeling), and 9 ≤ π2 ≤ 11 (roughly).
"""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N


def try_execute_word(word, start_cfg, mover_triples, gc_set):
    """Simulate execution: each step must use mover_triples, not land in gc_set.
    Returns configs list if valid cycle, else None."""
    configs = [start_cfg]
    cfg = list(start_cfg)
    for k, p in enumerate(word):
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        key = (p, L, S, R)
        if key not in mover_triples:
            return None, f"step {k}: no triple {key}"
        Snew = mover_triples[key]
        if Snew == S:
            return None, f"step {k}: Snew == S"
        cfg[p] = Snew
        nxt = tuple(cfg)
        if k + 1 < len(word) and nxt in gc_set:
            return None, f"step {k}: lands in gc {nxt}"
        configs.append(nxt)
    if tuple(cfg) != start_cfg:
        return None, f"not closed: {tuple(cfg)} != {start_cfg}"
    if len(set(configs[:-1])) != len(configs[:-1]):
        return None, f"not simple"
    return configs[:-1], "OK"


def formula_T(w):
    """Return tau for formula T, or None if inapplicable."""
    w = list(w)
    pi_0 = [k for k in range(CL) if w[k] == 0]
    if len(pi_0) != 2: return None
    pi1, pi2 = pi_0
    if pi1 != 0: return None  # require canonical
    if not (9 <= pi2 <= 12): return None
    tau = []
    tau += [2, 3, 4, 5, 6, 7]
    tau += [pi2+1, pi2+2, pi2+3]
    tau += [0]
    tau += list(range(8, pi2))  # 8..pi2-1
    tau += list(range(pi2+4, 23))  # pi2+4..22
    tau += [1]
    tau += [pi2]
    tau += [23]
    assert len(tau) == CL, f"len(tau)={len(tau)} for pi2={pi2}, tau={tau}"
    assert sorted(tau) == list(range(CL)), f"tau not a permutation: {sorted(tau)}"
    return tau


def main():
    samples = enumerate_residual(cap=200)
    total = len(samples)
    passed = 0
    failed_reasons = {}
    for si, w in enumerate(samples):
        tau = formula_T(w)
        if tau is None:
            failed_reasons['no_tau'] = failed_reasons.get('no_tau', 0) + 1
            continue
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        bad_word = [w[tau[j]] for j in range(CL)]
        # Seed: gc_cfg[2] with proc 0 flipped
        seed = list(gc_configs[2])
        seed[0] = 1 - seed[0]
        seed = tuple(seed)
        if seed in gc_set:
            failed_reasons['seed_in_gc'] = failed_reasons.get('seed_in_gc', 0) + 1
            continue
        r, msg = try_execute_word(bad_word, seed, mover_triples, gc_set)
        if r is not None:
            passed += 1
        else:
            failed_reasons[msg[:40]] = failed_reasons.get(msg[:40], 0) + 1
            if si < 5:
                print(f"sample {si}: gc_word={''.join(str(x) for x in w)} pi2={[k for k in range(CL) if w[k]==0][1]}")
                print(f"   bad_word={''.join(str(x) for x in bad_word)}")
                print(f"   seed={seed}")
                print(f"   msg={msg}")
    print(f"\nFormula T: {passed}/{total} samples valid")
    print(f"Failure reasons: {failed_reasons}")


if __name__ == '__main__':
    main()
