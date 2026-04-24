#!/usr/bin/env python3
"""
RA6: Analyze the conflict-free cycles found at n=6, ms=[2,3,3,2,3,3].

Questions:
1. What do these cycles look like?
2. Are they sweep-like or non-sweep?
3. Which 3-arcs have >=2 ternary? Do those arcs avoid EC specifically?
4. Is the product AT threshold (not sub-threshold)?
"""
from itertools import product as iproduct
from collections import defaultdict

def enumerate_ring_adj_words(n, ms, max_cl):
    results = []
    min_fires = sum(ms)
    def dfs(word, fc, steps):
        if steps > max_cl:
            return
        if steps >= min_fires:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                if abs(word[-1] - word[0]) % n in (1, n-1):
                    results.append(tuple(word))
                    return
        remaining = max_cl - steps
        needed = sum(max(0, ms[p] - fc[p]) if fc[p] == 0 or fc[p] % ms[p] != 0
                      else 0 for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            fc[nxt] += 1
            word.append(nxt)
            dfs(word, fc, steps + 1)
            word.pop()
            fc[nxt] -= 1
    for start in range(n):
        fc = [0] * n
        fc[start] = 1
        dfs([start], fc, 1)
    unique = set()
    result = []
    for w in results:
        L = len(w)
        best = w
        for i in range(L):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result

def enumerate_state_sequences(m, k):
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

def analyze_word(word, ms, n):
    """Detailed analysis of a single word."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    # Directions
    dirs = []
    for i in range(L):
        d = (word[(i+1)%L] - word[i]) % n
        if d == 1:
            dirs.append('+')
        elif d == n-1:
            dirs.append('-')
        else:
            dirs.append('?')

    is_sweep = all(d == '+' for d in dirs) or all(d == '-' for d in dirs)
    dir_str = ''.join(dirs)

    return fc, dir_str, is_sweep

def main():
    print("RA6: Conflict-Free Cycle Analysis")
    print("=" * 70)

    n = 6
    ms = [2,3,3,2,3,3]
    prod = 1
    for m in ms:
        prod *= m
    print(f"ms={ms}, n={n}, product={prod}, threshold={4*3**(n-2)}")
    print(f"Binary procs: {[p for p in range(n) if ms[p]==2]} (positions 0,3)")
    print(f"Are binary procs adjacent? {abs(0-3) in (1, n-1)}")
    print()

    max_cl = sum(ms) + 6
    words = enumerate_ring_adj_words(n, ms, max_cl)
    print(f"Total words: {len(words)}")

    # Find conflict-free
    cf_words = []
    for word in words:
        L = len(word)
        fc_w = [0]*n
        for p in word:
            fc_w[p] += 1
        proc_seqs = {p: enumerate_state_sequences(ms[p], fc_w[p]) for p in range(n)}

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

            if not has_ec:
                cf_words.append((word, combo, good))

    print(f"\nConflict-free cycles: {len(cf_words)}")
    print()

    for idx, (word, combo, good) in enumerate(cf_words[:8]):
        L = len(word)
        fc, dir_str, is_sweep = analyze_word(word, ms, n)
        print(f"--- CF Cycle {idx+1} ---")
        print(f"  Word: {word}")
        print(f"  CL={L}, fc={fc}")
        print(f"  Directions: {dir_str}  Sweep: {is_sweep}")

        # Show configs
        for t in range(min(L, 20)):
            c = good[t]
            mover = word[t]
            print(f"    t={t:2d}: config={c}, mover={mover} (m={ms[mover]})")

        # Check 3-arc content
        print(f"  3-arc analysis:")
        for start in range(n):
            arc = [(start+k)%n for k in range(3)]
            arc_ms = [ms[p] for p in arc]
            n_ternary = sum(1 for m in arc_ms if m >= 3)
            # Check if all 3 procs fire (always true since hfull)
            print(f"    Arc {arc}: ms={arc_ms}, ternary_count={n_ternary}")

        # Verify non-consecutive binary
        binary_pos = [p for p in range(n) if ms[p] == 2]
        consec = False
        for i in range(len(binary_pos)):
            for j in range(i+1, len(binary_pos)):
                if abs(binary_pos[i] - binary_pos[j]) % n in (1, n-1):
                    consec = True
        print(f"  Binary positions: {binary_pos}, consecutive: {consec}")
        print()

    # Key question: these exist at threshold. What about strictly sub-threshold?
    print("=" * 70)
    print("KEY OBSERVATION:")
    print(f"  Product = {prod}, threshold = {4*3**(n-2)}")
    print(f"  Product {'<' if prod < 4*3**(n-2) else '=' if prod == 4*3**(n-2) else '>'} threshold")
    print(f"  Our theorem requires STRICT sub-threshold (product < threshold)")
    if prod >= 4*3**(n-2):
        print(f"  These CF cycles exist AT threshold — NOT a counterexample to sub-threshold claim")

    # Now check: for ms with only 2 binary, product must be >= threshold
    print(f"\n  ms={ms} has {sum(1 for m in ms if m==2)} binary procs")
    print(f"  With 2 binary: min product = 2^2 * 3^{n-2} = {4*3**(n-2)} = threshold")
    print(f"  So 2-binary multisets are ALWAYS at threshold, never sub-threshold!")
    print(f"  Sub-threshold requires >= 3 binary procs")

if __name__ == "__main__":
    main()
