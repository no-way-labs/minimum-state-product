#!/usr/bin/env python3
"""
RA6: Rigorous verification of the CF cycle at n=9, ms=[2,3,3,2,3,3,2,3,3].

Word: [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0]
CL=24, fc=[2,3,3,2,3,3,2,3,3]

This is a "double-wiggle sweep": first half wiggles backward with bounces,
second half sweeps backward cleanly.

Verify:
1. Is this really a valid good cycle? (distinct configs, closure)
2. Is it really EC-free with incrementing?
3. Is it EC-free with ALL possible transitions?
4. What about fc=ms words — are those also CF?
5. Characterize the word structure precisely.
6. Does this invalidate the "3-arc obstruction holds for mixed"?
"""
from itertools import product as iproduct
from collections import defaultdict


def enumerate_state_sequences(m, k):
    """All sequences of length k+1 starting and ending at 0,
    consecutive values different, in {0,...,m-1}."""
    if k == 0:
        return [[0]]
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


def check_ec_full(word, ms, n):
    """Check EC for ALL valid state-sequence combos.
    Returns (total_valid, total_ec, total_cf, cf_examples)."""
    L = len(word)
    fc = [0]*n
    for p in word:
        fc[p] += 1

    proc_seqs = {p: enumerate_state_sequences(ms[p], fc[p]) for p in range(n)}
    total_combos = 1
    for p in range(n):
        total_combos *= len(proc_seqs[p])

    print(f"    State sequences per proc: {[len(proc_seqs[p]) for p in range(n)]}")
    print(f"    Total combos: {total_combos}")

    total_valid = 0
    total_ec = 0
    total_cf = 0
    cf_examples = []

    for combo in iproduct(*(proc_seqs[p] for p in range(n))):
        ss = {p: combo[p] for p in range(n)}
        fcc = [0]*n
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

        mover_triples = defaultdict(set)
        nonmover_triples = defaultdict(set)
        for t in range(L):
            c = good[t]
            mover = word[t]
            for j in range(n):
                Lp = (j-1)%n; Rp = (j+1)%n
                triple = (c[Lp], c[j], c[Rp])
                if j == mover:
                    mover_triples[j].add(triple)
                else:
                    nonmover_triples[j].add(triple)

        has_ec = False
        for j in range(n):
            if mover_triples[j] & nonmover_triples[j]:
                has_ec = True
                break

        if has_ec:
            total_ec += 1
        else:
            total_cf += 1
            if len(cf_examples) < 3:
                cf_examples.append(combo)

    return total_valid, total_ec, total_cf, cf_examples


def main():
    print("RA6: Rigorous CF Verification")
    print("=" * 70)

    n = 9
    ms = [2,3,3,2,3,3,2,3,3]

    # The word found
    word = [8,7,8,7,6,5,4,5,4,3,2,1,2,1,0,8,7,6,5,4,3,2,1,0]
    L = len(word)

    print(f"n={n}, ms={ms}")
    print(f"Word: {word}")
    print(f"CL={L}")

    # Verify ring-adjacency
    for i in range(L):
        nxt = word[(i+1)%L]
        cur = word[i]
        if abs(cur - nxt) % n not in (1, n-1):
            print(f"  NOT RING-ADJACENT at step {i}: {cur}->{nxt}")
            return
    print("Ring-adjacency: VERIFIED")

    # Fire counts
    fc = [0]*n
    for p in word:
        fc[p] += 1
    print(f"Fire counts: {fc}")
    print(f"fc == ms: {fc == ms}")
    print(f"hfull: {all(f > 0 for f in fc)}")

    # Direction pattern
    dirs = []
    for i in range(L):
        d = (word[(i+1)%L] - word[i]) % n
        dirs.append('+' if d == 1 else '-')
    print(f"Directions: {''.join(dirs)}")

    # Structural description
    print(f"\n--- Word Structure ---")
    print(f"Phase 1 (steps 0-13): wiggly backward sweep with bounces at 8,7 / 5,4 / 2,1")
    print(f"Phase 2 (steps 14-23): clean backward sweep 0->8->7->...->0")
    print(f"Each ternary pair (8,7), (5,4), (2,1) gets an extra bounce")
    print(f"Binary procs (0,3,6) fire exactly 2 times")

    # === Full verification with all transitions ===
    print(f"\n--- Full EC Check (all transitions) ---")
    tv, te, tc, cf_ex = check_ec_full(word, ms, n)
    print(f"  Valid combos: {tv}")
    print(f"  With EC: {te}")
    print(f"  Conflict-free: {tc}")
    print(f"  CF rate: {100*tc/tv:.1f}%")

    if tc > 0:
        print(f"\n  *** CONFIRMED: {tc} conflict-free cycles exist ***")
        print(f"  *** This is a TRUE counterexample to universal EC ***")
        print(f"  *** for ring-adjacent hfull cycles on mixed rings ***")
    else:
        print(f"  All transitions have EC. The incrementing CF was an artifact.")

    # Also check the rotation [3,2,3,3,2,3,3,2,3]
    print(f"\n--- Also check rotation ms=[3,2,3,3,2,3,3,2,3] ---")
    ms2 = [3,2,3,3,2,3,3,2,3]
    # Corresponding word: rotate positions
    # Original: binary at {0,3,6}. Rotation: binary at {1,4,7}
    # The analogous word would shift all positions by 1
    word2 = [(p+1)%n for p in word]
    print(f"  Rotated word: {word2}")

    # Verify
    for i in range(L):
        nxt = word2[(i+1)%L]
        cur = word2[i]
        if abs(cur - nxt) % n not in (1, n-1):
            print(f"  NOT ring-adjacent at step {i}: {cur}->{nxt}")
            break
    else:
        fc2 = [0]*n
        for p in word2:
            fc2[p] += 1
        if fc2 == ms2:
            print(f"  fc matches ms2: YES")
            tv2, te2, tc2, _ = check_ec_full(word2, ms2, n)
            print(f"  Valid: {tv2}, EC: {te2}, CF: {tc2}")
        else:
            print(f"  fc={fc2} does NOT match ms2={ms2}")

    # === Key question: what multisets have CF and which don't? ===
    print(f"\n--- Why [2,3,2,3,2,3,3,3,3] has NO CF but [2,3,3,2,3,3,2,3,3] does ---")
    print(f"  [2,3,2,3,2,3,3,3,3]: binary at {{0,2,4}}, gap=2 between binaries")
    print(f"  [2,3,3,2,3,3,2,3,3]: binary at {{0,3,6}}, gap=3 between binaries")
    print(f"  The gap-3 arrangement allows the wiggle-sweep pattern to form")
    print(f"  between consecutive pairs of ternary procs, creating enough triple")
    print(f"  diversity to avoid mover/nonmover overlap.")
    print()
    print(f"  With gap-2 (alternating), there's only 1 ternary between binaries,")
    print(f"  so the wiggle has nowhere to go -- the bounce must cross a binary proc,")
    print(f"  which constrains the triple space severely.")

    print("\nDone.")


if __name__ == "__main__":
    main()
