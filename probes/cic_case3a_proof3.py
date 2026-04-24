#!/usr/bin/env python3
"""
CIC Exploration 14c: Full entry-conflict check for Case 3a.

For each non-sweep word and each state-sequence combo:
Check if ANY proc has a mover/non-mover context overlap (entry conflict).
If every combo has at least one conflict, the word is killed.
"""

from itertools import product as iproduct
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


def check_entry_conflicts(word, n, ms):
    """For ALL state-sequence combos, check if every combo has
    at least one entry conflict (mover/non-mover overlap)."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    proc_seqs = {}
    for p in range(n):
        proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])

    sl = [proc_seqs[p] for p in range(n)]

    total_valid = 0
    total_conflict = 0
    conflict_free = []

    for combo in iproduct(*sl):
        ss = {p: combo[p] for p in range(n)}

        # Build good cycle configs
        fcc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:L])) != L:
            continue

        total_valid += 1
        good = configs[:L]

        # Collect all mover entries and non-mover entries
        mover_entries = {}  # (proc, L, S, R) -> new_val
        nonmover_entries = {}  # (proc, L, S, R) -> set of S values

        for t in range(L):
            c = good[t]
            cn = good[(t + 1) % L]
            mover = word[t]

            for j in range(n):
                Lp = (j - 1) % n
                Rp = (j + 1) % n
                key = (j, c[Lp], c[j], c[Rp])

                if j == mover:
                    # Mover: state changes
                    mover_entries[key] = cn[j]
                else:
                    # Non-mover: state preserved (identity)
                    if key not in nonmover_entries:
                        nonmover_entries[key] = set()
                    nonmover_entries[key].add(c[j])

        # Check conflicts
        has_conflict = False
        for key in mover_entries:
            if key in nonmover_entries:
                mval = mover_entries[key]
                _, _, s, _ = key
                if mval != s:
                    has_conflict = True
                    break

        if has_conflict:
            total_conflict += 1
        else:
            conflict_free.append(combo)

    return total_valid, total_conflict, conflict_free


def main():
    print("CIC Exploration 14c: Full Entry-Conflict Check")
    print("=" * 70)

    # PART 1: Check all non-sweep words, all combos
    print("\nPART 1: Entry Conflicts (All Combos)")
    print("-" * 70)

    for n in range(5, 11):
        walks = enumerate_fc2_walks(n) if n <= 10 else []
        non_sweep = [w for w in walks if not is_sweep(w, n)]
        ms = [2, 2, 2] + [3] * (n - 3)

        all_killed = True
        for w in non_sweep:
            tv, tc, cf = check_entry_conflicts(w, n, ms)
            if tc < tv:
                all_killed = False
                print(f"  n={n} word={w}: {tc}/{tv} have conflict, "
                      f"{tv - tc} CONFLICT-FREE!")
                # Show which combo is conflict-free
                if cf:
                    combo = cf[0]
                    ss = {p: combo[p] for p in range(n)}
                    print(f"    Conflict-free combo: "
                          f"{[list(combo[p]) for p in range(n)]}")

        if all_killed and non_sweep:
            print(f"  n={n}: ALL {len(non_sweep)} non-sweep words killed "
                  f"by entry conflict ✓")

    # PART 2: Also check quaternary multiset
    print("\n\nPART 2: Quaternary Multiset {2^3, 4, 3^(n-4)}")
    print("-" * 70)

    for n in range(6, 10):
        walks = enumerate_fc2_walks(n)
        non_sweep = [w for w in walks if not is_sweep(w, n)]

        for qpos in [3]:
            ms = [2, 2, 2] + [3] * (n - 3)
            ms[qpos] = 4

            all_killed = True
            for w in non_sweep:
                tv, tc, cf = check_entry_conflicts(w, n, ms)
                if tc < tv:
                    all_killed = False
                    print(f"  n={n} qpos={qpos} word={w[:6]}...: "
                          f"{tc}/{tv} conflict, {tv-tc} FREE!")

            if all_killed and non_sweep:
                print(f"  n={n} qpos={qpos}: ALL killed ✓")

    # PART 3: Detailed conflict analysis for escape words
    print("\n\nPART 3: Which Proc Has Conflict?")
    print("-" * 70)

    for n in [7, 9]:
        walks = enumerate_fc2_walks(n)
        non_sweep = [w for w in walks if not is_sweep(w, n)]
        ms = [2, 2, 2] + [3] * (n - 3)

        for w in non_sweep:
            L = len(w)
            fc = [0] * n
            for p in w:
                fc[p] += 1

            proc_seqs = {}
            for p in range(n):
                proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])
            sl = [proc_seqs[p] for p in range(n)]

            conflict_procs = {}

            for combo in iproduct(*sl):
                ss = {p: combo[p] for p in range(n)}
                fcc = [0] * n
                configs = [tuple(ss[p][0] for p in range(n))]
                for t in range(L):
                    fcc[w[t]] += 1
                    configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
                if configs[-1] != configs[0]:
                    continue
                if len(set(configs[:L])) != L:
                    continue

                good = configs[:L]

                # Find ALL conflict procs
                mover_e = {}
                nonmover_e = {}
                for t in range(L):
                    c = good[t]
                    cn = good[(t + 1) % L]
                    mover = w[t]
                    for j in range(n):
                        key = (j, c[(j-1)%n], c[j], c[(j+1)%n])
                        if j == mover:
                            mover_e[key] = cn[j]
                        else:
                            if key not in nonmover_e:
                                nonmover_e[key] = set()
                            nonmover_e[key].add(c[j])

                cprocs = set()
                for key in mover_e:
                    if key in nonmover_e:
                        _, _, s, _ = key
                        if mover_e[key] != s:
                            cprocs.add(key[0])

                key2 = frozenset(cprocs)
                if key2 not in conflict_procs:
                    conflict_procs[key2] = 0
                conflict_procs[key2] += 1

            print(f"  n={n} word={w}:")
            for procs, count in sorted(conflict_procs.items()):
                plist = sorted(procs) if procs else "NONE"
                print(f"    conflict at {plist}: {count} combos")

    # PART 4: For the "hard" words (turnaround at 0), what ternary
    # neighbor state causes the conflict?
    print("\n\nPART 4: Ternary-Dependent Conflicts")
    print("-" * 70)

    for n in [9]:
        # The "hard" word: turnaround at 0
        w = [0,1,2,3,4,5,6,7,8,0,8,7,6,5,4,3,2,1]
        L = len(w)
        ms = [2, 2, 2] + [3] * (n - 3)

        fc = [0] * n
        for p in w:
            fc[p] += 1

        proc_seqs = {}
        for p in range(n):
            proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])
        sl = [proc_seqs[p] for p in range(n)]

        for combo in iproduct(*sl):
            ss = {p: combo[p] for p in range(n)}
            fcc = [0] * n
            configs = [tuple(ss[p][0] for p in range(n))]
            for t in range(L):
                fcc[w[t]] += 1
                configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
            if configs[-1] != configs[0]:
                continue
            if len(set(configs[:L])) != L:
                continue

            good = configs[:L]

            # Find conflict entries
            mover_e = {}
            nonmover_e = {}
            for t in range(L):
                c = good[t]
                cn = good[(t + 1) % L]
                mover = w[t]
                for j in range(n):
                    key = (j, c[(j-1)%n], c[j], c[(j+1)%n])
                    if j == mover:
                        mover_e[key] = (cn[j], t)
                    else:
                        if key not in nonmover_e:
                            nonmover_e[key] = []
                        nonmover_e[key].append(t)

            print(f"  Combo: {[list(combo[p]) for p in range(n)]}")
            for key in mover_e:
                if key in nonmover_e:
                    j, l, s, r = key
                    mval, mt = mover_e[key]
                    if mval != s:
                        nmt = nonmover_e[key]
                        print(f"    P{j}: f({j},{l},{s},{r})={mval}(mover@{mt})"
                              f" vs ={s}(nonmover@{nmt})")
            break  # just first combo

    sys.stdout.flush()


if __name__ == "__main__":
    main()
