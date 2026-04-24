"""Test: does flipping all 3 binary procs give a valid bad cycle?

For residual gc, define shadow_cfg[k] = gc[k] with all binary flipped 0<->1.
Check:
- shadow configs are not in gc
- shadow moves work (same mover as gc[k], with local triples matching gc mover triples)
- cycle closes

If YES: we have a clean shadow construction analogous to CIC Expl 3.
"""
import sys
sys.setrecursionlimit(30000)
from itertools import product as iproduct

N = 9
MS = [2, 3, 3, 2, 3, 3, 2, 3, 3]
CL = 24

def left(p): return (p - 1) % N
def right(p): return (p + 1) % N

BIN = [p for p in range(N) if MS[p] == 2]  # [0, 3, 6]

SAMPLE = (0, 8, 7, 6, 5, 4, 3, 2, 1, 0, 8, 7, 8, 7, 6, 5, 4, 5, 4, 3, 2, 1, 2, 1)

def flip_all_binary(cfg):
    new = list(cfg)
    for p in BIN:
        new[p] = 1 - cfg[p]
    return tuple(new)

def flip_one_binary(cfg, p):
    new = list(cfg)
    new[p] = 1 - cfg[p]
    return tuple(new)

def build_configs(word):
    cfg = [0]*N
    configs = [tuple(cfg)]
    for m in word:
        cfg[m] = (cfg[m] + 1) % MS[m]
        configs.append(tuple(cfg))
    return configs[:-1]

def analyze(word):
    gc_configs = build_configs(list(word))
    gc_set = set(gc_configs)
    mover_triples = {}
    for k, p in enumerate(word):
        cfg = gc_configs[k]
        L, S, R = cfg[left(p)], cfg[p], cfg[right(p)]
        mover_triples[(p, L, S, R)] = (S + 1) % MS[p]
    # Option A: flip all binary
    print("=== OPTION A: flip all binary procs (0,3,6) ===")
    shadow_A = [flip_all_binary(c) for c in gc_configs]
    print(f"  shadow[0] = {shadow_A[0]}")
    in_gc = sum(1 for c in shadow_A if c in gc_set)
    print(f"  shadow configs in gc: {in_gc}/{len(shadow_A)}")
    # Verify mover triples
    valid = 0
    invalid_examples = []
    for k in range(len(shadow_A)):
        mover = word[k]
        c = shadow_A[k]
        L, S, R = c[left(mover)], c[mover], c[right(mover)]
        key = (mover, L, S, R)
        if key in mover_triples:
            Snew = mover_triples[key]
            # Check the next config matches
            if Snew != S:
                new_c = list(c); new_c[mover] = Snew
                if tuple(new_c) == shadow_A[(k+1) % len(shadow_A)]:
                    valid += 1
                else:
                    invalid_examples.append((k, tuple(new_c), shadow_A[(k+1)%len(shadow_A)]))
            else:
                invalid_examples.append((k, "S_new==S", None))
        else:
            invalid_examples.append((k, "triple missing", (mover, L, S, R)))
    print(f"  valid steps: {valid}/{len(shadow_A)}")
    if invalid_examples:
        print(f"  first invalid: {invalid_examples[0]}")

    # Option B: flip proc 0 only
    print("\n=== OPTION B: flip proc 0 only ===")
    shadow_B = [flip_one_binary(c, 0) for c in gc_configs]
    in_gc = sum(1 for c in shadow_B if c in gc_set)
    print(f"  shadow configs in gc: {in_gc}/{len(shadow_B)}")
    valid = 0
    invalid_examples = []
    for k in range(len(shadow_B)):
        mover = word[k]
        c = shadow_B[k]
        L, S, R = c[left(mover)], c[mover], c[right(mover)]
        key = (mover, L, S, R)
        if key in mover_triples:
            Snew = mover_triples[key]
            if Snew != S:
                new_c = list(c); new_c[mover] = Snew
                if tuple(new_c) == shadow_B[(k+1) % len(shadow_B)]:
                    valid += 1
                else:
                    invalid_examples.append((k, 'diff', tuple(new_c), shadow_B[(k+1)%len(shadow_B)]))
            else:
                invalid_examples.append((k, 'no-move'))
        else:
            invalid_examples.append((k, 'miss', (mover, L, S, R)))
    print(f"  valid steps: {valid}/{len(shadow_B)}")
    if invalid_examples:
        print(f"  first invalid: {invalid_examples[0]}")

analyze(SAMPLE)
