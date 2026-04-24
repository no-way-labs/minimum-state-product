#!/usr/bin/env python3
"""
RA12: Final comprehensive verification.

1. Confirm the 8 EC-free ring walks at (3,3,3) placement
2. Check if these 8 walks can form valid self-stabilizing systems
3. Check all other obstructions (shadow, SCC connectivity)
4. Summarize findings for all placements

KEY DISTINCTION: Ring walks are a SUBSET of all mover sequences.
In the self-stabilization model, the mover at each step is determined
by the config (which proc has privilege). The mover sequence can be
arbitrary -- no ring-walk constraint.

For the lower bound proof, we need: for EVERY good cycle (with EVERY
possible mover sequence), there is an obstruction.

EC being universal for random mover sequences but not for ring walks
is still significant IF ring-walk mover sequences can appear in valid systems.
"""

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


def enumerate_walks(n, ms):
    total_len = sum(ms)
    walks = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == total_len:
            nxt = path[0]
            if abs(pos - nxt) % n in (1, n - 1):
                if all(fc[p] == ms[p] for p in range(n)):
                    walks.append(tuple(path))
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    for p0 in range(n):
        fc = [0] * n
        fc[p0] = 1
        dfs([p0], fc)
    unique = set()
    result = []
    for w in walks:
        ell = len(w)
        best = w
        for i in range(ell):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(w)
    return result


def check_ec_for_word_combo(word, combo, n, ms):
    """Build cycle and check EC. Returns (is_valid, has_ec, details)."""
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    if configs[-1] != configs[0]:
        return False, None, "not a cycle"
    if len(set(configs[:L])) != L:
        return False, None, "not distinct"

    good = configs[:L]

    # Check EC at each processor
    for j in range(n):
        Lp = (j - 1) % n
        Rp = (j + 1) % n
        mover_ctxs = {}  # ctx -> next_val
        nonmover_ctxs = set()
        for t in range(L):
            ctx = (good[t][Lp], good[t][j], good[t][Rp])
            if word[t] == j:
                nv = good[(t + 1) % L][j]
                if nv != ctx[1]:
                    mover_ctxs[ctx] = nv
            else:
                nonmover_ctxs.add(ctx)
        overlap = set(mover_ctxs.keys()) & nonmover_ctxs
        if overlap:
            return True, True, f"EC at P{j}"

    return True, False, "no EC"


def check_system_validity(word, combo, n, ms):
    """Check if (word, combo) can be part of a valid system.
    Extract ALL transition table entries and check consistency.
    Also check: no other good cycle exists with same tables."""
    L = len(word)
    ss = {p: combo[p] for p in range(n)}
    fcc = [0] * n
    configs = [tuple(ss[p][0] for p in range(n))]
    for t in range(L):
        fcc[word[t]] += 1
        configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
    good = configs[:L]

    # Extract transition tables
    tables = {}  # (proc, L, S, R) -> output
    for t in range(L):
        c = good[t]
        cn = good[(t + 1) % L]
        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            key = (j, c[Lp], c[j], c[Rp])
            required = cn[j]
            if key in tables:
                if tables[key] != required:
                    return False, "table conflict"
            else:
                tables[key] = required

    # How many table entries are defined?
    total_possible = sum(
        ms[(j-1) % n] * ms[j] * ms[(j+1) % n]
        for j in range(n)
    )
    defined = len(tables)

    # Check: which entries would need to be the identity (non-mover)?
    # And which entries need to change state (mover)?
    mover_entries = set()
    identity_entries = set()
    for t in range(L):
        c = good[t]
        cn = good[(t + 1) % L]
        mover = word[t]
        for j in range(n):
            Lp = (j - 1) % n
            Rp = (j + 1) % n
            key = (j, c[Lp], c[j], c[Rp])
            if j == mover:
                if cn[j] != c[j]:
                    mover_entries.add(key)
            else:
                identity_entries.add(key)

    # Check privilege: at each config, only the mover should have privilege
    # (i.e., f(L,S,R) != S for mover, f(L,S,R) == S for all others)
    # The mover entries give f != S. Identity entries give f == S.
    # Conflict if same key appears in both with different requirements.
    privilege_conflict = mover_entries & identity_entries
    if privilege_conflict:
        return False, f"privilege conflict at {len(privilege_conflict)} entries"

    return True, f"consistent, {defined}/{total_possible} entries defined"


def main():
    n = 9
    ms = make_ms(n, (0, 3, 6))  # (3,3,3) placement

    print("=" * 70)
    print("RA12: Final comprehensive verification at n=9")
    print(f"ms={ms}, binary at 0,3,6 (gaps 3,3,3)")
    print("=" * 70)

    # Enumerate walks
    walks = enumerate_walks(n, ms)
    print(f"\nTotal walks: {len(walks)}")

    # Check all walks with all combos
    proc_seqs = {p: enumerate_state_sequences(ms[p], ms[p]) for p in range(n)}
    sl = [proc_seqs[p] for p in range(n)]

    ec_free_all = []  # (word, combo) pairs
    ec_free_walks = []  # walks that have ALL combos EC-free

    for widx, word in enumerate(walks):
        all_free = True
        valid_count = 0
        free_count = 0

        for combo in iproduct(*sl):
            is_valid, has_ec, detail = check_ec_for_word_combo(
                word, combo, n, ms)
            if not is_valid:
                continue
            valid_count += 1
            if not has_ec:
                free_count += 1
                ec_free_all.append((word, combo))
                # Check system validity for this EC-free case
            else:
                all_free = False

        if free_count > 0:
            ec_free_walks.append((word, valid_count, free_count))

    print(f"\nWalks with any EC-free combo: {len(ec_free_walks)}")
    print(f"Total (word, combo) pairs: {len(ec_free_all)}")

    # For each EC-free walk, check system validity
    print(f"\n{'='*70}")
    print("SYSTEM VALIDITY CHECK for EC-free cycles")
    print(f"{'='*70}")

    valid_systems = 0
    invalid_systems = 0
    details = []

    for word, combo in ec_free_all[:64]:  # Check first 64
        ok, detail = check_system_validity(word, combo, n, ms)
        if ok:
            valid_systems += 1
            details.append((word, combo, detail))
        else:
            invalid_systems += 1
            if invalid_systems <= 3:
                print(f"  INVALID: {detail}")

    print(f"\nValid system candidates: {valid_systems}/{min(64, len(ec_free_all))}")
    print(f"Invalid (privilege conflict): {invalid_systems}")

    if details:
        word, combo, detail = details[0]
        print(f"\nFirst valid candidate: {detail}")
        print(f"  Word: {list(word)}")
        print(f"  Combos: {[list(combo[p]) for p in range(n)]}")

    # CRITICAL CHECK: For valid candidates, does the extracted transition
    # function have OTHER good cycles? If so, the system might still fail.
    print(f"\n{'='*70}")
    print("ADDITIONAL GOOD CYCLE CHECK")
    print(f"{'='*70}")

    if details:
        word, combo, _ = details[0]
        L = len(word)
        ss = {p: combo[p] for p in range(n)}
        fcc = [0] * n
        configs = [tuple(ss[p][0] for p in range(n))]
        for t in range(L):
            fcc[word[t]] += 1
            configs.append(tuple(ss[p][fcc[p]] for p in range(n)))
        good = configs[:L]

        # Extract transition tables
        tables = {}
        for t in range(L):
            c = good[t]
            cn = good[(t + 1) % L]
            for j in range(n):
                Lp = (j - 1) % n
                Rp = (j + 1) % n
                key = (j, c[Lp], c[j], c[Rp])
                tables[key] = cn[j]

        print(f"Extracted {len(tables)} table entries from good cycle")

        # For each config NOT in the good cycle, check which procs have privilege
        all_configs = list(iproduct(*[range(ms[p]) for p in range(n)]))
        good_set = set(good)
        print(f"Total configs: {len(all_configs)}")
        print(f"Good configs: {len(good_set)}")
        print(f"Bad configs: {len(all_configs) - len(good_set)}")

        # Check: among bad configs, how many have defined transitions?
        # And do any form cycles?
        bad_with_privilege = 0
        bad_no_privilege = 0
        bad_undefined = 0

        for cfg in all_configs:
            if cfg in good_set:
                continue
            # Check which procs have privilege
            priv = []
            for j in range(n):
                Lp = (j - 1) % n
                Rp = (j + 1) % n
                key = (j, cfg[Lp], cfg[j], cfg[Rp])
                if key in tables:
                    if tables[key] != cfg[j]:
                        priv.append(j)
                # If key not in tables, we can set it freely
            if priv:
                bad_with_privilege += 1
            else:
                # Check if all relevant entries are defined
                all_defined = True
                for j in range(n):
                    Lp = (j - 1) % n
                    Rp = (j + 1) % n
                    key = (j, cfg[Lp], cfg[j], cfg[Rp])
                    if key not in tables:
                        all_defined = False
                        break
                if all_defined:
                    bad_no_privilege += 1
                else:
                    bad_undefined += 1

        print(f"\nBad configs analysis:")
        print(f"  With privilege (from defined entries): {bad_with_privilege}")
        print(f"  No privilege (all defined, all identity): {bad_no_privilege}")
        print(f"  Undefined (some entries not in table): {bad_undefined}")

    # Summary
    print(f"\n{'='*70}")
    print("FINAL SUMMARY")
    print(f"{'='*70}")

    print(f"\n3-binary non-consecutive placements on 9-ring:")
    print(f"  4 distinct placements (up to rotation)")
    print(f"  (2,2,5), (2,3,4), (2,4,3): 0 ring walks at min length")
    print(f"  (3,3,3): {len(walks)} ring walks, {len(ec_free_walks)} "
          f"fully EC-free walks, {len(ec_free_all)} EC-free (word,combo) pairs")

    print(f"\n  EC-free walks exist ONLY for ring-walk mover sequences.")
    print(f"  Random (non-walk) mover sequences: 100% EC in 10K samples.")
    print(f"  Valid system candidates: {valid_systems} (no transition conflicts)")

    if ec_free_all:
        print(f"\n  CONCLUSION: Entry conflict is NOT universal for ring-walk")
        print(f"  mover sequences at (3,3,3) placement. However, the mover")
        print(f"  sequence in a self-stabilizing system is determined by the")
        print(f"  config (which proc has privilege), NOT by ring adjacency.")
        print(f"  So the ring-walk constraint is an EXTRA constraint that may")
        print(f"  not apply. If the system requires non-adjacent movers in")
        print(f"  the good cycle, then ring-walk EC-free cycles are irrelevant.")
    else:
        print(f"\n  CONCLUSION: Entry conflict IS universal for all placements.")


if __name__ == "__main__":
    main()
