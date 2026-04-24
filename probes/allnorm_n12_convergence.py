"""
Convergence check for all-tight allNormalForm good cycles at n=12.

Ring: (2,2,3,2,2,3,2,2,3,2,2,3), 4 ternary pivots at {2,5,8,11}.
Binary transitions: context-dependent f_p(L,S,R) -> {0,1}.
Ternary transition: shared function f_t(L,S,R) with L,R in {0,1}, S in {0,1,2}, f_t != S.

RESULT (verified exhaustively, 335s):
  All 4092 closable ternary functions produce UNIVERSAL binary context overlap.
  Every single good cycle (across all functions, all starting configs) has ALL 8
  binary processors seeing the same (L,S,R) context as both mover and non-mover.
  This means no binary function f_p can satisfy both f_p(L,S,R) != S (mover)
  and f_p(L,S,R) = S (non-mover) for the same context. STRUCTURAL OBSTRUCTION.

  ANSWER: NO. None of the 4092 ternary functions produce convergent systems.
  The all-tight allNormalForm pattern at n=12 is fundamentally incompatible
  with self-stabilization, regardless of binary function choice.

Method: For each closable ternary function, iterate over all 20736 configs.
For each fixed point of the 24-step cycle map T (i.e., T(c)=c), trace the cycle
and record (L,S,R) contexts seen by each binary proc at mover vs non-mover steps.
If mover_contexts intersect nonmover_contexts at ANY binary proc, that cycle has
"overlap" and no consistent binary function exists for it.

Result: 0 overlap-free cycles out of millions checked. Minimum overlap = 8 procs
(i.e., ALL binary procs have overlap in EVERY cycle of EVERY function).
"""

from itertools import product as iter_product
from collections import defaultdict
import time

n = 12
m_vals = [2,2,3,2,2,3,2,2,3,2,2,3]
ternary_positions = {2, 5, 8, 11}
binary_procs = [0, 1, 3, 4, 6, 7, 9, 10]
mover_seq = [2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 1, 9, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 1, 9]

# Ternary function setup
ternary_inputs = []
ternary_valid_outputs = []
for L in range(2):
    for S in range(3):
        for R in range(2):
            ternary_inputs.append((L, S, R))
            ternary_valid_outputs.append([v for v in range(3) if v != S])

def make_ternary_func(choices):
    return {inp: out for inp, out in zip(ternary_inputs, choices)}

# Generate all configs
all_configs = []
for bvals in iter_product(range(2), repeat=8):
    for tvals in iter_product(range(3), repeat=4):
        config = [0]*n
        for i, pos in enumerate(binary_procs):
            config[pos] = bvals[i]
        for i, pos in enumerate([2,5,8,11]):
            config[pos] = tvals[i]
        all_configs.append(tuple(config))

total_configs = len(all_configs)

def check_overlap_for_func(ternary_func):
    """
    For a given ternary function, check all fixed-point configs (good cycles).
    Returns (total_fp, overlap_free_count, min_overlap_procs).
    """
    total_fp = 0
    overlap_free = 0
    min_overlap = n

    for c_start in all_configs:
        cc = list(c_start)
        failed = False
        for step in range(24):
            p = mover_seq[step]
            L, S, R = cc[(p-1)%n], cc[p], cc[(p+1)%n]
            if p in ternary_positions:
                new_val = ternary_func[(L, S, R)]
                if new_val == S:
                    failed = True
                    break
                cc[p] = new_val
            else:
                cc[p] = 1 - S
        if failed or tuple(cc) != c_start:
            continue

        total_fp += 1

        # Check overlap
        c = list(c_start)
        b_mover = defaultdict(set)
        b_nonmover = defaultdict(set)

        for step in range(24):
            p = mover_seq[step]
            for q in binary_procs:
                Lq, Sq, Rq = c[(q-1)%n], c[q], c[(q+1)%n]
                if q == p:
                    b_mover[q].add((Lq, Sq, Rq))
                else:
                    b_nonmover[q].add((Lq, Sq, Rq))

            L, S, R = c[(p-1)%n], c[p], c[(p+1)%n]
            if p in ternary_positions:
                c[p] = ternary_func[(L, S, R)]
            else:
                c[p] = 1 - S

        overlap_procs = sum(1 for q in binary_procs if b_mover[q] & b_nonmover[q])
        if overlap_procs == 0:
            overlap_free += 1
        min_overlap = min(min_overlap, overlap_procs)

    return total_fp, overlap_free, min_overlap


if __name__ == '__main__':
    print(f"Total configs: {total_configs}")
    print("=" * 70)
    print("Universal overlap check for all 4092 closable ternary functions")
    print(f"Ring: {tuple(m_vals)}, Cycle length: 24")
    print("=" * 70)

    closable = 0
    any_overlap_free = 0
    min_overlap_global = n

    t0 = time.time()

    for idx, choices in enumerate(iter_product(*ternary_valid_outputs)):
        func = make_ternary_func(choices)

        # Quick closability check
        has_fp = False
        for c in all_configs:
            cc = list(c)
            failed = False
            for step in range(24):
                p = mover_seq[step]
                L, S, R = cc[(p-1)%n], cc[p], cc[(p+1)%n]
                if p in ternary_positions:
                    nv = func[(L, S, R)]
                    if nv == S:
                        failed = True
                        break
                    cc[p] = nv
                else:
                    cc[p] = 1 - S
            if not failed and tuple(cc) == c:
                has_fp = True
                break

        if not has_fp:
            continue

        closable += 1
        fp_count, of_count, min_ov = check_overlap_for_func(func)
        if of_count > 0:
            any_overlap_free += 1
            print(f"  OVERLAP-FREE! func {idx}: {of_count}/{fp_count} cycles")
        min_overlap_global = min(min_overlap_global, min_ov)

        if closable % 200 == 0:
            elapsed = time.time() - t0
            rate = closable / elapsed
            est = (4092 - closable) / rate if rate > 0 else 0
            print(f"  Progress: {closable}/~4092, overlap-free: {any_overlap_free}, "
                  f"min_overlap: {min_overlap_global}, "
                  f"elapsed {elapsed:.1f}s, ETA {est:.0f}s", flush=True)

    elapsed = time.time() - t0

    print(f"\n{'='*70}")
    print(f"RESULTS:")
    print(f"  Total ternary functions: 4096")
    print(f"  Closable: {closable}")
    print(f"  Functions with overlap-free cycle: {any_overlap_free}")
    print(f"  Min overlap procs (all cycles, all funcs): {min_overlap_global}")
    print(f"  Time: {elapsed:.1f}s")
    print(f"{'='*70}")

    if any_overlap_free == 0:
        print(f"\nDEFINITIVE: NO convergent systems exist.")
        print(f"All {closable} closable functions have UNIVERSAL overlap at all 8 binary procs.")
    else:
        print(f"\n{any_overlap_free} functions have overlap-free cycles -- candidates for convergence.")
