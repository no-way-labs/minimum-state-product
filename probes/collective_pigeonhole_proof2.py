#!/usr/bin/env python3
"""
Collective Pigeonhole Part 2: Deep analysis of the survivor.

The V-word [0,1,0,n-1,...,2,1,2,...,n-1] survives collective EC.
Analyze its structure and check n=8,9.
Also: does this word survive OTHER obstruction methods (shadow, etc)?
"""

from itertools import product as iproduct
from collections import Counter, defaultdict
import sys


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


def deep_analysis(n, ms, binary_procs):
    """Deep analysis of ALL words at given n."""
    print(f"\n{'='*70}")
    print(f"n = {n}, ms = {ms}")
    print(f"{'='*70}")

    walks = enumerate_fc2_walks(n)
    non_sweep = [w for w in walks if not is_sweep(w, n)]
    print(f"Total fc=2 walks: {len(walks)}, non-sweep: {len(non_sweep)}")

    ec_free_words = []

    for i, w in enumerate(non_sweep):
        L = len(w)
        fc = [0] * n
        for p in w:
            fc[p] += 1
        proc_seqs = {}
        for p in range(n):
            proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])
        sl = [proc_seqs[p] for p in range(n)]

        total_valid = 0
        all_ec_free = 0
        ec_free_details = []

        for combo in iproduct(*sl):
            good = build_good_cycle(w, n, ms, combo)
            if good is None:
                continue
            total_valid += 1

            all_binary_free = True
            proc_details = {}
            for b in binary_procs:
                mover_ctx = set()
                nonmover_ctx = set()
                mover_steps = []
                for t in range(L):
                    c = good[t]
                    Lp = (b - 1) % n
                    Rp = (b + 1) % n
                    ctx = (c[Lp], c[b], c[Rp])
                    if w[t] == b:
                        mover_ctx.add(ctx)
                        mover_steps.append(t)
                    else:
                        nonmover_ctx.add(ctx)
                overlap = mover_ctx & nonmover_ctx
                if overlap:
                    all_binary_free = False
                proc_details[b] = {
                    'mover': mover_ctx,
                    'nonmover': nonmover_ctx,
                    'steps': mover_steps,
                }

            if all_binary_free:
                all_ec_free += 1
                if len(ec_free_details) < 2:
                    ec_free_details.append((combo, proc_details, good))

        if all_ec_free > 0:
            ec_free_words.append((w, all_ec_free, total_valid, ec_free_details))

    if not ec_free_words:
        print(">>> ALL non-sweep words killed by collective EC! <<<")
        return True
    else:
        print(f"SURVIVORS: {len(ec_free_words)}/{len(non_sweep)} words have EC-free combos")
        for w, aef, tv, details in ec_free_words:
            print(f"\n  Word: {w}")
            print(f"    EC-free: {aef}/{tv} combos")
            if details:
                combo, pd, good = details[0]
                print(f"    Example combo (state seqs): {[list(combo[p]) for p in range(n)]}")
                L = len(w)
                print(f"    Good cycle configs:")
                for t in range(L):
                    mover = w[t]
                    print(f"      t={t:2d}: config={good[t]} mover={mover}")

                # Analyze the word structure
                dirs = []
                for t in range(L):
                    d = (w[(t+1) % L] - w[t]) % n
                    if d > n // 2:
                        d -= n
                    dirs.append(d)
                print(f"    Directions: {dirs}")

                # Check context utilization
                for b in binary_procs:
                    m = pd[b]['mover']
                    nm = pd[b]['nonmover']
                    total_used = len(m | nm)
                    print(f"    Proc {b}: |mover|={len(m)}, |nonmover|={len(nm)}, "
                          f"total_contexts_used={total_used}/18, "
                          f"disjoint={len(m & nm) == 0}")

                # Cross-constraint analysis
                print(f"\n    CROSS-CONSTRAINTS:")
                for b in binary_procs:
                    for t in pd[b]['steps']:
                        c = good[t]
                        print(f"      When proc {b} fires at step {t}:")
                        for b2 in binary_procs:
                            if b2 != b:
                                Lp2 = (b2 - 1) % n
                                Rp2 = (b2 + 1) % n
                                ctx2 = (c[Lp2], c[b2], c[Rp2])
                                in_mover = ctx2 in pd[b2]['mover']
                                in_nonmover = ctx2 in pd[b2]['nonmover']
                                print(f"        proc {b2} ctx = {ctx2}, "
                                      f"in_mover={in_mover}, in_nonmover={in_nonmover}")

        return False


def main():
    print("COLLECTIVE PIGEONHOLE: DEEP ANALYSIS")
    print("=" * 80)

    for n in [5, 6, 7, 8]:
        ms = [2, 2, 2] + [3] * (n - 3)
        binary_procs = [0, 1, 2]
        deep_analysis(n, ms, binary_procs)

    # Construct the V-word directly for n=9 and check
    print("\n" + "=" * 80)
    print("DIRECT V-WORD CHECK AT n=9")
    print("=" * 80)
    n = 9
    ms = [2, 2, 2] + [3] * 6
    binary_procs = [0, 1, 2]
    # V-word: 0,1,0,8,7,6,5,4,3,2,1,2,3,4,5,6,7,8
    v_word = [0, 1, 0] + list(range(n-1, 1, -1)) + list(range(1, n))
    print(f"V-word: {v_word}, length={len(v_word)}")
    assert len(v_word) == 2 * n, f"Length {len(v_word)} != {2*n}"
    # Verify fc=2 for all
    fc = Counter(v_word)
    print(f"Fire counts: {dict(fc)}")

    L = len(v_word)
    proc_seqs = {}
    for p in range(n):
        proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])
    sl = [proc_seqs[p] for p in range(n)]

    print(f"State seq counts: {[len(sl[p]) for p in range(n)]}")
    total_combos = 1
    for p in range(n):
        total_combos *= len(sl[p])
    print(f"Total combos to check: {total_combos}")

    total_valid = 0
    all_ec_free = 0

    for combo in iproduct(*sl):
        good = build_good_cycle(v_word, n, ms, combo)
        if good is None:
            continue
        total_valid += 1

        all_binary_free = True
        for b in binary_procs:
            mover_ctx = set()
            nonmover_ctx = set()
            for t in range(L):
                c = good[t]
                Lp = (b - 1) % n
                Rp = (b + 1) % n
                ctx = (c[Lp], c[b], c[Rp])
                if v_word[t] == b:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)
            if mover_ctx & nonmover_ctx:
                all_binary_free = False
                break

        if all_binary_free:
            all_ec_free += 1
            if all_ec_free <= 2:
                print(f"  EC-free combo found! combo={[list(combo[p]) for p in range(n)]}")
                # Show details
                for b in binary_procs:
                    mover_ctx = set()
                    nonmover_ctx = set()
                    for t in range(L):
                        c = good[t]
                        Lp = (b - 1) % n
                        Rp = (b + 1) % n
                        ctx = (c[Lp], c[b], c[Rp])
                        if v_word[t] == b:
                            mover_ctx.add(ctx)
                        else:
                            nonmover_ctx.add(ctx)
                    print(f"    Proc {b}: mover={mover_ctx}, nonmover={nonmover_ctx}, "
                          f"used={len(mover_ctx|nonmover_ctx)}/18")

    print(f"\nV-word at n=9: valid={total_valid}, all-binary-EC-free={all_ec_free}")
    if all_ec_free > 0:
        print(">>> COLLECTIVE PIGEONHOLE FAILS AT n=9 <<<")
    else:
        print(">>> COLLECTIVE PIGEONHOLE WORKS FOR V-WORD AT n=9 <<<")


if __name__ == '__main__':
    main()
