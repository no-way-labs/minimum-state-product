#!/usr/bin/env python3
"""
RA12: Analytical proof sketch + verification of the Binary-Pair Phase Theorem.

THEOREM (Binary-Pair Phase): In any ZW good cycle with >=3 binary, all fc>=2,
some fc>=3, sub-threshold product, n>=5:

There exists a binary proc b with two binary neighbors such that b has a phase
where one binary neighbor fires 0 and the other binary neighbor fires 2 (all its fires).

PROOF SKETCH:
1. Binary procs fire exactly 2 times each (only valid even fc for m=2).
2. >=3 binary implies >=3 consecutive binary on ring (since non-binary <=2 for sub-threshold,
   and >=3 binary of n procs). Actually NOT necessarily consecutive.
   But: >=3 binary out of n procs. For n>=5 with at most n-3 non-binary, we have
   at most n-3 gaps. With >=3 binary, by pigeonhole >=2 binary are adjacent.
   Actually with >=3 binary out of n=5: 3 binary, 2 ternary. The ternary procs
   split the ring into at most 2 arcs. With 3 binary distributed among <=2 arcs,
   at least one arc has >=2 consecutive binary.

   More generally: with >=3 binary and <=2 ternary, at least 2 binary are
   consecutive (no ternary between them). Pick such a pair b, b' (adjacent binary).

3. b has 2 phases. b' fires 2 times distributed across b's phases.
   Case A: b' fires 1 in each phase -> 1-1 split, neither phase is one-sided >=2
   Case B: b' fires 2 in one phase, 0 in the other -> the 2-fire phase has K=2 from b'

4. For Case B: the other neighbor of b fires some amount. If J=0 in the 2-fire
   phase, done: (0,2) with binary b'. If J>0, the other phase has (J',0) where
   J' is possibly >=2.

   Actually, let me re-examine. If b' fires both in one phase of b, and the
   other neighbor fires 0 in that phase, we have (0, 2) - DONE.

5. The key question: in Case A (1-1 split), does some OTHER pair provide the
   provider? Or can Case A be ruled out?

6. CLAIM: if ALL consecutive binary pairs have 1-1 splits, the walk is a pure
   sweep. But ZW cycles are not sweeps if fc>=3 exists (sweep has all fc=2
   for n>=5, or exactly fc=n/n = 1 per proc for winding number 1).

   Actually: sweeps have fc=2 for each proc when L=2n (bounce). For ZW (winding 0),
   the walk goes CW and CCW equally. The turnaround points create the fc>=3 procs.
   At turnaround, the walk reverses, firing the turnaround proc (ternary, fc=3)
   multiple times in a row (like ...3, 4, 3... in the example).

   The turnaround creates consecutive fires of the same pair: e.g., word = ...3,4,3,4,3...
   These are ternary procs firing alternately. The binary chain on the other side
   sees the walk pass through CW once and CCW once.

7. CONCRETE ARGUMENT for >= 3 consecutive binary (say procs 0,1,2 all binary):
   In a ZW walk, the walk traverses 0-1-2 in one direction, then later 2-1-0
   in the other. Consider proc 1 (middle binary, both neighbors binary).

   Fire step 1 of proc 1: walk passes 0->1->2 or 2->1->0.
   Fire step 2 of proc 1: walk passes in the OPPOSITE direction.

   Phase 1 (between fire 2 and fire 1): walk goes one way.
   Phase 2 (between fire 1 and fire 2): walk goes the other way.

   In Phase 1 (CW traversal): mover sequence is ...0, 1, 2... or contains 0->1.
     So proc 0 fires in this phase (the step right before proc 1 fires).
     And proc 2 fires right after (in the NEXT phase).
     Wait: proc 1 fires at the end of the phase. The step before is 0 or 2.

   Actually the issue is more subtle. Let me just verify the claim computationally.

Actually, let me verify a sharper claim: when >=3 consecutive binary exist,
the MIDDLE binary proc always provides.
"""

import time
from itertools import permutations
from collections import Counter


def compute_winding(word, n):
    L = len(word)
    cw = ccw = 0
    for i in range(L):
        diff = (word[(i + 1) % L] - word[i]) % n
        if diff == 1:
            cw += 1
        elif diff == n - 1:
            ccw += 1
    return cw, ccw


def analyze_phases(word, n, q):
    L = len(word)
    left_q = (q - 1) % n
    right_q = (q + 1) % n
    fire_steps = [t for t in range(L) if word[t] == q]
    fc_q = len(fire_steps)
    if fc_q == 0:
        return []
    phases = []
    for idx in range(fc_q):
        s = fire_steps[idx]
        a = fire_steps[(idx - 1) % fc_q]
        J = K = 0
        t = (a + 1) % L
        while t != s:
            if word[t] == left_q:
                J += 1
            if word[t] == right_q:
                K += 1
            t = (t + 1) % L
        phases.append((J, K))
    return phases


def _enumerate_walks_dfs(n, length, ms):
    results = []
    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == length:
            diff = (path[0] - pos) % n
            if diff != 1 and diff != n - 1:
                return
            if any(f < 2 for f in fc):
                return
            if all(f <= 2 for f in fc):
                return
            cw, ccw = compute_winding(path, n)
            if cw == 0 or cw != ccw:
                return
            results.append(tuple(path))
            return
        remaining = length - step
        unfired = sum(1 for f in fc if f < 2)
        if unfired > remaining:
            return
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] >= ms[nxt] and ms[nxt] == 2:
                continue
            if fc[nxt] >= 2 * ms[nxt]:
                continue
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
    for w in results:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))
    return result


def generate_subthreshold_multisets(n, threshold):
    results = []
    max_state = min(threshold // (2 ** (n - 1)) + 1, 10)
    def gen(pos, min_val, current, prod):
        if pos == n:
            if prod < threshold:
                num_bin = sum(1 for m in current if m == 2)
                if num_bin >= 3:
                    results.append(tuple(current))
            return
        remaining = n - pos
        for m in range(max(2, min_val), max_state + 1):
            new_prod = prod * m
            if new_prod >= threshold:
                break
            if remaining > 1 and new_prod * (2 ** (remaining - 1)) >= threshold:
                if m > 2:
                    break
            gen(pos + 1, m, current + [m], new_prod)
    gen(0, 2, [], 1)
    return results


def get_all_ring_placements(sorted_ms, n):
    seen = set()
    results = []
    for perm in set(permutations(sorted_ms)):
        best = perm
        for i in range(n):
            rot = perm[i:] + perm[:i]
            if rot < best:
                best = rot
        rev = perm[::-1]
        for i in range(n):
            rot = rev[i:] + rev[:i]
            if rot < best:
                best = rot
        if best not in seen:
            seen.add(best)
            results.append(list(best))
    return results


def find_consecutive_binary_triples(ms, n):
    """Find all triples (a, b, c) where b is binary with both neighbors binary."""
    triples = []
    for b in range(n):
        if ms[b] != 2:
            continue
        a = (b - 1) % n
        c = (b + 1) % n
        if ms[a] == 2 and ms[c] == 2:
            triples.append((a, b, c))
    return triples


def main():
    print("RA12: Analytical Proof Verification")
    print("=" * 70)

    # Check: does the MIDDLE binary of a consecutive triple always provide?
    print("\n=== Check: Middle-binary provider ===")

    for n in [5, 7, 9]:
        print(f"\n  n = {n}")
        t0 = time.time()
        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        total_words = 0
        middle_provides = 0
        middle_fails = 0
        has_triple = 0
        no_triple = 0
        fails = []

        for sorted_ms in sorted_multisets:
            if time.time() - t0 > 60:
                print("  TIME LIMIT")
                break

            placements = get_all_ring_placements(sorted_ms, n)
            for ms in placements:
                triples = find_consecutive_binary_triples(ms, n)

                max_len = min(sum(ms), 4 * n)
                min_len = 2 * n + 1

                for cycle_len in range(min_len, max_len + 1):
                    walks = _enumerate_walks_dfs(n, cycle_len, ms)
                    for w in walks:
                        fc = [0] * n
                        for p in w:
                            fc[p] += 1

                        total_words += 1

                        if not triples:
                            no_triple += 1
                            continue
                        has_triple += 1

                        # Check if any middle binary provides
                        found = False
                        for a, b, c in triples:
                            phases = analyze_phases(w, n, b)
                            for J, K in phases:
                                if J == 0 and K >= 2:  # a silent, c fires >=2
                                    found = True
                                    break
                                if K == 0 and J >= 2:  # c silent, a fires >=2
                                    found = True
                                    break
                            if found:
                                break

                        if found:
                            middle_provides += 1
                        else:
                            middle_fails += 1
                            if len(fails) < 5:
                                fails.append({
                                    'ms': list(ms), 'word': list(w), 'fc': list(fc),
                                    'triples': triples
                                })

        elapsed = time.time() - t0
        print(f"    Words: {total_words}, elapsed: {elapsed:.1f}s")
        print(f"    Has consecutive triple: {has_triple}")
        print(f"    No consecutive triple: {no_triple}")
        print(f"    Middle provides: {middle_provides}/{has_triple}")
        print(f"    Middle fails: {middle_fails}/{has_triple}")
        if fails:
            print(f"    FAILURES:")
            for f in fails[:3]:
                print(f"      ms={f['ms']}, word={f['word']}, fc={f['fc']}")
                print(f"      triples={f['triples']}")
                for a, b, c in f['triples']:
                    phases = analyze_phases(f['word'], len(f['ms']), b)
                    print(f"        b={b}: phases={phases}")

    # Check: do all placements have a consecutive binary triple?
    print("\n\n=== Check: Consecutive binary triple existence ===")
    for n in [5, 7, 9]:
        threshold = 4 * (3 ** (n - 2))
        sorted_multisets = generate_subthreshold_multisets(n, threshold)

        total_placements = 0
        has_triple = 0
        no_triple_placements = []

        for sorted_ms in sorted_multisets:
            placements = get_all_ring_placements(sorted_ms, n)
            for ms in placements:
                total_placements += 1
                triples = find_consecutive_binary_triples(ms, n)
                if triples:
                    has_triple += 1
                else:
                    if len(no_triple_placements) < 5:
                        no_triple_placements.append(list(ms))

        print(f"  n={n}: {has_triple}/{total_placements} placements have triple")
        if no_triple_placements:
            print(f"    Without triple: {no_triple_placements}")


if __name__ == "__main__":
    main()
