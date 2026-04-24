#!/usr/bin/env python3
"""
RA12: Check if good cycles exist for the asymmetric placements by
using a different approach: enumerate ALL configurations reachable
from the all-zeros config and check for cycles.

A good cycle is a cycle in the configuration graph where each config
has a unique successor (determined by transition function).

For ms=(2,3,...), the config space is small: product(ms) = 5832.
We can enumerate the directed graph and look for cycles.

But we need to know the transition function. Instead, let's enumerate
all possible good cycles more directly.

Approach: A good cycle of length L visits L distinct configs, each
with a defined mover. The mover is the processor that changes state.
The cycle must return to the starting config.

For small config spaces, we can check: what is the set of possible
good-cycle-compatible mover sequences (words)?

Actually, the fundamental constraint is simpler:
- A good cycle with ms has length L = k * lcm(ms) / gcd factors...
  No. L must satisfy fc[p] = k_p * ms[p] for some positive integers k_p.
  The minimum is k_p = 1 for all p, giving L = sum(ms).

The ring walk constraint (each step to adjacent proc) is SEPARATE from
the config-space constraint.

Wait -- the ring walk constraint IS the mover constraint. In Dijkstra's
model, the mover at each step is determined by the scheduler. But for
self-stabilization, we need: for each config, exactly one processor has
privilege (is enabled). So the mover at step t is determined by config[t].

The "mover word" is the sequence of movers. For a good cycle, this must be:
1. A ring walk (each consecutive mover is adjacent on the ring)
   -- NO! This is NOT a constraint. The mover can be ANY processor.

Actually, let me re-read the model. In the self-stabilizing token ring:
- Each processor p has state c[p] in {0, ..., ms[p]-1}
- Processor p has privilege (can fire) when f_p(c[p-1], c[p], c[p+1]) != c[p]
- When p fires: c[p] := f_p(c[p-1], c[p], c[p+1])
- A good cycle: sequence of configs where exactly one proc has privilege,
  they fire, and eventually return to the start.

The mover sequence does NOT need to be a ring walk!
Each step, ANY processor can be the one with privilege.
The ring walk constraint is a SEPARATE requirement for certain proof techniques.

So for the EC analysis, I should enumerate ALL mover sequences (not just ring walks).
But the search space is huge: 9^24 possible mover sequences.

However, the key observation is: entry conflict is about the transition
function being inconsistent. If the mover sequence is NOT a ring walk,
the cycle might still have EC.

Let me think about what cycles actually exist.

For ms=[2,3,2,3,2,3,3,3,3] (binary at 0,2,4), product = 5832.
A good cycle visits 5832 configs or fewer.

Let me check: can we build a valid system with this ms vector?
Use the verifier!
"""

import sys
sys.path.insert(0, './claude')

# Import the core verifier
import importlib.util
spec = importlib.util.spec_from_file_location("verifier",
    "./probes/verifier.py")

# Actually, let's just do a direct check.
# The question is: does a self-stabilizing token ring exist with
# ms = [2,3,2,3,2,3,3,3,3] (product 5832 < 8748)?

# The theorem says NO (M_9 = 8748). But the PROOF of this uses
# different techniques for different cases.

# For the lower bound proof, we need to show that no valid system exists.
# Entry conflict is ONE mechanism. Shadow cycles, overlap, etc. are others.

# Let me check: for the ASYMMETRIC placements with 0 walks,
# are there non-walk good cycles?

# For a good cycle of minimum length sum(ms) = 24:
# - Each proc fires exactly ms[p] times
# - Each proc's state cycles through 0 -> f1 -> f2 -> ... -> 0
# - The mover sequence determines which proc fires at each step

# The mover sequence can be ANY sequence of length 24 where fc[p] = ms[p].
# It does NOT need to be a ring walk.

# Let me enumerate good cycles with arbitrary mover sequences
# (not just ring walks) and check EC.

from itertools import product as iproduct
from collections import Counter
import time


def make_ms(n, binary_positions):
    ms = [3] * n
    for b in binary_positions:
        ms[b] = 2
    return ms


def enumerate_state_sequences(m, k):
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(tuple(seq))
            return
        for nv in range(m):
            if nv != seq[-1]:
                if remaining == 1 and nv != 0:
                    continue
                seq.append(nv)
                dfs(seq, remaining - 1)
                seq.pop()
    dfs([0], k)
    return seqs


def enumerate_mover_sequences(n, target_fc, max_count=10000):
    """Enumerate mover sequences where fc[p] = target_fc[p].
    NO ring-walk constraint. Order matters."""
    L = sum(target_fc)
    results = []

    # Use backtracking
    def dfs(seq, fc):
        if len(results) >= max_count:
            return
        if len(seq) == L:
            results.append(tuple(seq))
            return
        remaining = L - len(seq)
        for p in range(n):
            if fc[p] < target_fc[p]:
                fc[p] += 1
                seq.append(p)
                dfs(seq, fc)
                seq.pop()
                fc[p] -= 1

    dfs([], [0] * n)
    return results


def check_cycle_ec(word, n, ms):
    """Check if any state-seq combo gives EC-free cycle for this word."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
    sl = [proc_seqs[p] for p in range(n)]

    total = 0
    ec_free = 0

    for combo in iproduct(*sl):
        ss = {p: combo[p] for p in range(n)}
        fcc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:L])) != L:
            continue
        total += 1
        good = configs[:L]

        has_conflict = False
        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            mc = set()
            nc = set()
            for t in range(L):
                ctx = (good[t][Lp], good[t][j], good[t][Rp])
                if word[t] == j:
                    nv = good[(t + 1) % L][j]
                    if nv != ctx[1]:
                        mc.add(ctx)
                else:
                    nc.add(ctx)
            if mc & nc:
                has_conflict = True
                break
        if not has_conflict:
            ec_free += 1

    return total, ec_free


def main():
    n = 9

    print("=" * 70)
    print("RA12: Good cycle existence (non-walk) for asymmetric placements")
    print("=" * 70)

    # Key insight: mover sequences are NOT restricted to ring walks.
    # A mover sequence is just any sequence where fc[p] = target for each p.

    # The number of such sequences of length 24 with fc = [2,3,2,3,2,3,3,3,3]
    # is 24! / (2! * 3! * 2! * 3! * 2! * 3! * 3! * 3! * 3!) which is huge.
    # We can't enumerate all of them.

    # HOWEVER: the state-sequence approach works differently.
    # For each processor, the state sequence (s_0, s_1, ..., s_{fc[p]}) is fixed.
    # The mover sequence determines which processor fires at each step.
    # The CONFIGS at each step are determined by the combo of state sequences
    # AND the mover word.

    # For a fixed combo (state sequences for all procs), the configs are
    # determined by the mover word. Two different mover words with the same
    # fc vector can give different config sequences.

    # But for EC checking, we only need: does there exist a mover word
    # AND state-seq combo such that the cycle is valid AND EC-free?

    # With minimum fc (fc[p] = ms[p]), the state sequences are very constrained:
    # Binary: only (0,1,0). Ternary: (0,1,2,0) or (0,2,1,0).
    # So combos = 2^6 = 64.

    # For each combo, the configs are determined by the word.
    # But different words give different config sequences.

    # Let me check: for a FIXED combo of state sequences, how many distinct
    # words give valid distinct-config cycles?

    # With incrementing transitions only (all state seqs = (0,1,2,0)),
    # any word gives a valid cycle (configs are determined).
    # The distinctness constraint is: all 24 configs must be different.
    # This is the key constraint.

    # Let's enumerate a RANDOM sample of mover sequences and check.
    import random
    random.seed(42)

    placements = [
        ((0, 2, 4), "(2,2,5)"),
        ((0, 2, 5), "(2,3,4)"),
        ((0, 2, 6), "(2,4,3)"),
        ((0, 3, 6), "(3,3,3)"),
    ]

    for pos, label in placements:
        ms = make_ms(n, pos)
        print(f"\nPlacement {label}: pos={pos}, ms={ms}")

        target_fc = [ms[p] for p in range(n)]
        L = sum(target_fc)

        # Generate random mover sequences
        sample_size = 10000
        valid_count = 0
        ec_free_count = 0
        total_checked = 0

        t0 = time.time()
        for _ in range(sample_size):
            # Generate random permutation with right fc
            word = []
            for p in range(n):
                word.extend([p] * target_fc[p])
            random.shuffle(word)
            word = tuple(word)

            # Check with all inc/dec combos
            proc_seqs = {p: enumerate_state_sequences(ms[p], ms[p])
                        for p in range(n)}
            sl = [proc_seqs[p] for p in range(n)]

            for combo in iproduct(*sl):
                ss = {p: combo[p] for p in range(n)}
                fcc = [0] * n
                configs = [tuple(ss[p][0] for p in range(n))]
                for t in range(L):
                    fcc[word[t]] += 1
                    configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
                if configs[-1] != configs[0]:
                    continue
                if len(set(configs[:L])) != L:
                    continue

                valid_count += 1
                good = configs[:L]

                has_conflict = False
                for j in range(n):
                    Lp = (j - 1) % n
                    Rp = (j + 1) % n
                    mc = set()
                    nc = set()
                    for t in range(L):
                        ctx = (good[t][Lp], good[t][j], good[t][Rp])
                        if word[t] == j:
                            nv = good[(t + 1) % L][j]
                            if nv != ctx[1]:
                                mc.add(ctx)
                        else:
                            nc.add(ctx)
                    if mc & nc:
                        has_conflict = True
                        break
                if not has_conflict:
                    ec_free_count += 1

            total_checked += 1

        t1 = time.time()
        print(f"  Sampled {sample_size} mover sequences, {t1-t0:.1f}s")
        print(f"  Valid cycles found: {valid_count}")
        print(f"  EC-free cycles: {ec_free_count}")

    # More important: check the RING-WALK CONSTRAINT.
    # For self-stabilization, the mover at each step is determined by the
    # config, not by adjacency. So the mover sequence is not necessarily
    # a ring walk.
    #
    # BUT: for the good cycle to be compatible with the ring topology,
    # we need each processor's transition to depend only on its neighbors.
    # This means: the mover at each step can be ANY processor (not just
    # adjacent to the previous mover).
    #
    # The key constraint for EC is: for processor j, the context (L,S,R)
    # at mover steps vs non-mover steps. This depends on the config
    # sequence, which depends on the mover word.
    #
    # So the RIGHT question is: for a given ms vector, does there exist
    # ANY mover word (not just ring walks) such that the resulting cycle
    # is EC-free?


if __name__ == "__main__":
    main()
