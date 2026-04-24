"""A small parameterized family of bad-cycle candidates. For each sample,
test all candidates and see if at least one works.

Candidate: For each binary proc p* ∈ {0, 3, 6}:
  Let π1 < π2 be gc's p*-fire positions.
  Let s = seed = gc_cfg[(π1+2) mod 24] with p* toggled.
  Let τ be the "delay p*'s fires" reorder:
     bad plays gc[π1+2..π2-1] first, then gc[π2+1..*], then defers gc[π1] and
     gc[π2] to near the end.
  Actually, we try multiple structured variants of τ.

Approach:
  - For each p*, rotate the ring so that p* becomes "proc 0," apply
    formula T with careful handling of tail, check.
  - If any p* works, count success.
"""
import sys
sys.setrecursionlimit(50000)

from pa2a_find_bad import enumerate_residual, build_gc_configs, build_mover_triples

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24
BIN_PROCS = [0, 3, 6]


def left(p): return (p - 1) % N
def right(p): return (p + 1) % N


def try_execute_word(word, start_cfg, mover_triples, gc_set):
    configs = [start_cfg]
    cfg = list(start_cfg)
    for k, p in enumerate(word):
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        key = (p, L, S, R)
        if key not in mover_triples: return None
        Snew = mover_triples[key]
        if Snew == S: return None
        cfg[p] = Snew
        nxt = tuple(cfg)
        if k + 1 < len(word) and nxt in gc_set: return None
        configs.append(nxt)
    if tuple(cfg) != start_cfg: return None
    if len(set(configs[:-1])) != len(configs[:-1]): return None
    return configs[:-1]


def generate_candidate_taus(w, p_star):
    """Given gc word w and chosen binary proc p_star, generate candidate taus."""
    fires_p = [k for k in range(CL) if w[k] == p_star]
    if len(fires_p) != 2: return []
    pi1, pi2 = fires_p
    gap = (pi2 - pi1) % CL
    # To keep things simple, we operate in a "rotated" frame where pi1 = 0.
    # Define rotation: new_pos = (k - pi1) mod CL
    # We construct tau in the rotated frame, then un-rotate.

    # Require gap be reasonable
    if gap < 4 or gap > CL - 4: return []

    # In rotated frame: pi1' = 0, pi2' = gap.
    # Candidate tau (in rotated frame): similar to formula T.
    # Try several "delay" lengths.
    results = []
    # Parameters:
    # a_start: where Block A starts (default 2)
    # a_len: length of A
    # b_len: length of B (fires immediately after pi2)
    # mid_start: where middle block starts (between A and pi1)
    # tail_size: trailing fixed block
    # The form: [A_block, B_block, 0, C_block, D_block, low_tail, gap, tail_block]
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
                            # C block: positions between a_end and gap, excluding pi2
                            c_block = [k for k in range(a_end, gap)]
                            tau_r += c_block
                            # D block: positions between b_end and CL-tail_size, excluding gap
                            d_block = [k for k in range(b_end, CL - tail_size) if k != gap]
                            tau_r += d_block
                            # low_tail: positions 1..a_start-1
                            low_tail = list(range(1, a_start))
                            tau_r += low_tail
                            tau_r += [gap]
                            # tail: [CL - tail_size .. CL - 1] excluding any already used
                            tail_block = [k for k in range(CL - tail_size, CL)]
                            tau_r += tail_block
                            if len(tau_r) != CL: continue
                            if sorted(tau_r) != list(range(CL)): continue
                            tau = [(t + pi1) % CL for t in tau_r]
                            results.append(tau)
                        except Exception:
                            pass
    return results


def candidate_seed(w, tau, p_star):
    """The first fire in bad corresponds to gc[tau[0]]. The config before
    that fire must match the pre-config of gc[tau[0]] with p_star flipped.
    """
    gc_configs_w = []
    cfg = [0]*N
    gc_configs_w.append(tuple(cfg))
    for m in w:
        cfg[m] = (cfg[m] + 1) % MS[m]
        gc_configs_w.append(tuple(cfg))
    gc_configs_w = gc_configs_w[:-1]
    # seed = pre-config of gc[tau[0]] in gc, with p_star toggled
    pre = list(gc_configs_w[tau[0]])
    pre[p_star] = 1 - pre[p_star]
    return tuple(pre)


def main():
    samples = enumerate_residual(cap=200)
    total = len(samples)
    passed = 0
    passed_p_counts = {0: 0, 3: 0, 6: 0}
    example_failures = []
    for si, w in enumerate(samples):
        gc_configs = build_gc_configs(w)
        gc_set = set(gc_configs)
        mover_triples = build_mover_triples(w, gc_configs)
        found = False
        for p_star in BIN_PROCS:
            taus = generate_candidate_taus(w, p_star)
            for tau in taus:
                bad_word = [w[tau[j]] for j in range(CL)]
                seed = candidate_seed(w, tau, p_star)
                if seed in gc_set: continue
                r = try_execute_word(bad_word, seed, mover_triples, gc_set)
                if r is not None:
                    found = True
                    passed_p_counts[p_star] += 1
                    break
            if found: break
        if found:
            passed += 1
        elif len(example_failures) < 3:
            example_failures.append(si)
    print(f"\nFormula family: {passed}/{total} samples valid")
    print(f"By p_star: {passed_p_counts}")
    print(f"Example failures: {example_failures}")


if __name__ == '__main__':
    main()
