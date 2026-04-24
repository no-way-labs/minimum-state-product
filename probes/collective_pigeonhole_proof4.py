#!/usr/bin/env python3
"""
Collective Pigeonhole Part 4: The real mechanism.

FINDING: Binary procs are NOT where EC happens. Ternary procs
are forced into EC by the V-word structure.

NEW QUESTION: Can we make a COLLECTIVE argument that spans ALL procs?
Or even just: does SOME proc always have EC, regardless of word?

Actually, the existing proof already handles this:
- Sweep words -> shadow cycle
- Non-sweep words -> Palindromic Entry Conflict (at ternary interior procs)

Let me verify: for EVERY non-sweep fc=2 word, does some proc have EC?
This checks whether "entry conflict somewhere" is universal,
even if "entry conflict at a binary proc" is not.
"""

from itertools import product as iproduct
from collections import Counter


def enumerate_fc2_walks(n):
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


def check_ec_anywhere(word, n, ms):
    """For ALL state-sequence combos, check if SOME proc has EC.
    Return (total_valid, total_with_ec, min_ec_count, surviving_combos)."""
    L = len(word)
    fc = Counter(word)

    proc_seqs = {}
    for p in range(n):
        proc_seqs[p] = enumerate_state_sequences(ms[p], fc.get(p, 0))
    sl = [proc_seqs[p] for p in range(n)]

    total_valid = 0
    total_with_ec = 0
    min_ec_count = n + 1  # min number of procs with EC across combos
    survivors = []  # combos with NO EC at any proc

    for combo in iproduct(*sl):
        good = build_good_cycle(word, n, ms, combo)
        if good is None:
            continue
        total_valid += 1

        ec_count = 0
        ec_at = []
        for j in range(n):
            mover_ctx = set()
            nonmover_ctx = set()
            for t in range(L):
                c = good[t]
                ctx = (c[(j-1)%n], c[j], c[(j+1)%n])
                if word[t] == j:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)
            if mover_ctx & nonmover_ctx:
                ec_count += 1
                ec_at.append(j)

        if ec_count > 0:
            total_with_ec += 1
        else:
            survivors.append(combo)

        min_ec_count = min(min_ec_count, ec_count)

    return total_valid, total_with_ec, min_ec_count, survivors


def main():
    print("=" * 80)
    print("UNIVERSAL EC: Does SOME proc always have EC for non-sweep words?")
    print("=" * 80)

    for n in [5, 6, 7, 8, 9]:
        ms = [2, 2, 2] + [3] * (n - 3)
        print(f"\n{'='*70}")
        print(f"n = {n}, ms = {ms}")
        print(f"{'='*70}")

        walks = enumerate_fc2_walks(n)
        non_sweep = [w for w in walks if not is_sweep(w, n)]
        print(f"Non-sweep fc=2 words: {len(non_sweep)}")

        all_killed = True
        for w in non_sweep:
            tv, tec, mec, surv = check_ec_anywhere(w, n, ms)
            if surv:
                all_killed = False
                print(f"  SURVIVOR: word={w}")
                print(f"    valid={tv}, with_EC={tec}, min_EC={mec}, "
                      f"no_EC_anywhere={len(surv)}")
                # Show first survivor
                combo = surv[0]
                good = build_good_cycle(w, n, ms, combo)
                print(f"    Combo: {[list(combo[p]) for p in range(n)]}")
                for j in range(n):
                    mctx = set()
                    nctx = set()
                    for t in range(len(w)):
                        c = good[t]
                        ctx = (c[(j-1)%n], c[j], c[(j+1)%n])
                        if w[t] == j:
                            mctx.add(ctx)
                        else:
                            nctx.add(ctx)
                    print(f"      Proc {j}: mover={mctx}, nonmover={nctx}, "
                          f"overlap={mctx & nctx}")
            else:
                if n <= 7:
                    print(f"  word={w}: all {tv} combos have EC somewhere (min {mec} procs)")

        if all_killed:
            print(f"\n>>> ALL non-sweep words killed: some proc has EC in every combo <<<")
        else:
            print(f"\n*** SOME words survive with NO EC at any proc ***")

    # Also check: what about non-binary-at-endpoints architectures?
    print("\n" + "=" * 80)
    print("NON-CONSECUTIVE BINARY (alternating)")
    print("=" * 80)
    for n in [5, 6, 7]:
        # Binary at 0, 2, 4
        ms_alt = [3] * n
        bin_positions = list(range(0, n, 2))[:3]
        for b in bin_positions:
            ms_alt[b] = 2
        print(f"\nn={n}, ms={ms_alt}, binary at {bin_positions}")

        walks = enumerate_fc2_walks(n)
        non_sweep = [w for w in walks if not is_sweep(w, n)]
        print(f"Non-sweep fc=2 words: {len(non_sweep)}")

        survivors = 0
        for w in non_sweep:
            tv, tec, mec, surv = check_ec_anywhere(w, n, ms_alt)
            if surv:
                survivors += 1
                if survivors <= 2:
                    print(f"  SURVIVOR: word={w}, {len(surv)}/{tv} combos")
        print(f"  Survivors: {survivors}/{len(non_sweep)}")


if __name__ == '__main__':
    main()
