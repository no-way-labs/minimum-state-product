#!/usr/bin/env python3
"""
Collective Pigeonhole Proof Investigation.

CONJECTURE: For a ring with n >= 9, >= 3 binary processors, sub-threshold product
(< 4*3^(n-2)), the collective context constraints across all binary processors
force an entry conflict at some binary processor.

APPROACH:
  Part 1: Enumerate all fc=2 walks (mover words) at n=9 with 3 binary at {0,1,2}.
  Part 2: For each walk, for each state-sequence combo:
          - Build the good cycle configs
          - At each binary proc, collect mover and nonmover contexts
          - Check: can all 3 binary procs be simultaneously EC-free?
  Part 3: Analyze the cross-constraints (when b1 fires, what are the nonmover
           contexts at b2 and b3?)
  Part 4: Identify the pigeonhole mechanism.
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys


def enumerate_fc2_walks(n):
    """Enumerate all fc=2 mover words on C_n (ring), up to rotation."""
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == 2 * n:
            nxt = path[0]
            if abs(pos - nxt) == 1 or abs(pos - nxt) == n - 1:
                if all(f == 2 for f in fc):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < 2:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)
    unique = set()
    result = []
    for w in walks:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def is_sweep(word, n):
    L = len(word)
    dirs = [(word[(i + 1) % L] - word[i]) % n for i in range(L)]
    return all(d == 1 for d in dirs) or all(d == n - 1 for d in dirs)


def enumerate_state_sequences(m, k):
    """Enumerate all state sequences of length k+1 starting and ending at 0,
    where consecutive entries differ, over Z_m."""
    seqs = []
    def dfs(seq, remaining):
        if remaining == 0:
            if seq[-1] == 0:
                seqs.append(list(seq))
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


def build_good_cycle(word, n, ms, combo):
    """Build good cycle configs from mover word and state-sequence combo.
    Returns list of configs or None if invalid."""
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]


def analyze_collective_ec(word, n, ms, binary_procs):
    """For a given word, check ALL state-sequence combos.
    For each valid combo, check if ALL binary procs are EC-free simultaneously.
    Returns detailed analysis."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    proc_seqs = {}
    for p in range(n):
        proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])

    sl = [proc_seqs[p] for p in range(n)]

    total_valid = 0
    total_all_ec_free = 0  # combos where ALL binary procs are EC-free
    total_some_ec = 0      # combos where at least one binary has EC

    ec_free_examples = []
    per_proc_ec_free = {b: 0 for b in binary_procs}

    for combo in iproduct(*sl):
        good = build_good_cycle(word, n, ms, combo)
        if good is None:
            continue
        total_valid += 1

        # For each binary proc, check EC
        all_binary_ec_free = True
        for b in binary_procs:
            mover_ctx = set()
            nonmover_ctx = set()
            for t in range(L):
                c = good[t]
                Lp = (b - 1) % n
                Rp = (b + 1) % n
                ctx = (c[Lp], c[b], c[Rp])
                if word[t] == b:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)

            overlap = mover_ctx & nonmover_ctx
            if overlap:
                all_binary_ec_free = False
            else:
                per_proc_ec_free[b] += 1

        if all_binary_ec_free:
            total_all_ec_free += 1
            if len(ec_free_examples) < 3:
                ec_free_examples.append(combo)
        else:
            total_some_ec += 1

    return {
        'total_valid': total_valid,
        'all_ec_free': total_all_ec_free,
        'some_ec': total_some_ec,
        'per_proc_ec_free': per_proc_ec_free,
        'examples': ec_free_examples,
    }


def analyze_cross_constraints(word, n, ms, binary_procs):
    """Analyze the cross-constraints between binary procs.
    When b1 fires at step t, what are the nonmover contexts at b2, b3?"""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    proc_seqs = {}
    for p in range(n):
        proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])

    sl = [proc_seqs[p] for p in range(n)]

    # Collect cross-constraint patterns
    cross_patterns = []

    for combo in iproduct(*sl):
        good = build_good_cycle(word, n, ms, combo)
        if good is None:
            continue

        # For each binary, record mover and nonmover contexts
        info = {}
        for b in binary_procs:
            mover_steps = []
            mover_ctx = []
            nonmover_ctx = []
            for t in range(L):
                c = good[t]
                Lp = (b - 1) % n
                Rp = (b + 1) % n
                ctx = (c[Lp], c[b], c[Rp])
                if word[t] == b:
                    mover_steps.append(t)
                    mover_ctx.append(ctx)
                else:
                    nonmover_ctx.append(ctx)
            info[b] = {
                'mover_steps': mover_steps,
                'mover_ctx': mover_ctx,
                'nonmover_ctx_set': set(nonmover_ctx),
                'mover_ctx_set': set(mover_ctx),
            }

        # Cross-constraint: when b1 fires, what's the context at b2, b3?
        cross = {}
        for b in binary_procs:
            for t in info[b]['mover_steps']:
                c = good[t]
                for b2 in binary_procs:
                    if b2 != b:
                        Lp2 = (b2 - 1) % n
                        Rp2 = (b2 + 1) % n
                        ctx2 = (c[Lp2], c[b2], c[Rp2])
                        if (b, b2) not in cross:
                            cross[(b, b2)] = []
                        cross[(b, b2)].append(ctx2)

        cross_patterns.append((info, cross))
        if len(cross_patterns) >= 100:
            break

    return cross_patterns


def main():
    print("=" * 80)
    print("COLLECTIVE PIGEONHOLE PROOF INVESTIGATION")
    print("=" * 80)

    # Start with n=5 (small, fast) to understand the structure
    for n in [5, 6, 7]:
        ms = [2, 2, 2] + [3] * (n - 3)
        binary_procs = [0, 1, 2]
        CL = 2 * n
        product = 1
        for m in ms:
            product *= m
        threshold = 4 * (3 ** (n - 2))

        print(f"\n{'='*70}")
        print(f"n = {n}, ms = {ms}, product = {product}, threshold = {threshold}")
        print(f"CL = {CL}, context space per binary = 3x2x3 = 18")
        print(f"{'='*70}")

        walks = enumerate_fc2_walks(n)
        non_sweep = [w for w in walks if not is_sweep(w, n)]
        print(f"Total fc=2 walks: {len(walks)}, non-sweep: {len(non_sweep)}")

        total_words_all_ec = 0
        total_words_some_free = 0

        for i, w in enumerate(non_sweep):
            result = analyze_collective_ec(w, n, ms, binary_procs)
            tv = result['total_valid']
            aef = result['all_ec_free']

            if aef > 0:
                total_words_some_free += 1
                print(f"  Word {i}: {w}")
                print(f"    Valid combos: {tv}, ALL-binary-EC-free: {aef}")
                print(f"    Per-proc EC-free: {result['per_proc_ec_free']}")
            else:
                total_words_all_ec += 1

        print(f"\nSUMMARY n={n}:")
        print(f"  Words ALL killed (every combo has EC at some binary): "
              f"{total_words_all_ec}/{len(non_sweep)}")
        print(f"  Words with some EC-free combo: "
              f"{total_words_some_free}/{len(non_sweep)}")

        if total_words_some_free > 0:
            print("\n  *** COLLECTIVE PIGEONHOLE DOES NOT SUFFICE AT n={n} ***")
            print("  Analyzing cross-constraints on first example...")
            # Find first word with EC-free combo
            for w in non_sweep:
                result = analyze_collective_ec(w, n, ms, binary_procs)
                if result['all_ec_free'] > 0:
                    print(f"    Word: {w}")
                    # Get detailed cross-constraint analysis
                    cross = analyze_cross_constraints(w, n, ms, binary_procs)
                    if cross:
                        info, cx = cross[0]
                        for b in binary_procs:
                            print(f"    Proc {b}: mover_ctx = {info[b]['mover_ctx_set']}, "
                                  f"nonmover_ctx = {info[b]['nonmover_ctx_set']}")
                            print(f"      |mover| = {len(info[b]['mover_ctx_set'])}, "
                                  f"|nonmover| = {len(info[b]['nonmover_ctx_set'])}")
                    break
        else:
            print(f"\n  >>> COLLECTIVE PIGEONHOLE WORKS AT n={n} <<<")


if __name__ == '__main__':
    main()
