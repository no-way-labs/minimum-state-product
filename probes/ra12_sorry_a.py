#!/usr/bin/env python3
"""
RA12 Sorry A: consecutive binary + zero-winding → False

Investigate: at n=9 with 3 consecutive binary and sub-threshold product,
generate zero-winding good cycles and check:
1. How common are they?
2. For cycles with global min gap = 1: what is the EC mechanism?
3. Can palindromic EC be called without going through global dispatch?

Key insight from the Lean code: the gap=1 sub-case means two opposite-direction
crossings at the same edge are temporally adjacent (separated by 1 step).
This creates an extremely tight constraint on the transition function.
"""

import sys
from itertools import product as iproduct
from collections import defaultdict


def make_ring_system(n, ms):
    """Build all configs, privilege sets, transitions for a ring system."""
    from itertools import product as iprod
    configs = list(iprod(*(range(m) for m in ms)))
    return configs


def enumerate_gc_walks(n, L):
    """Enumerate all mover words of length L on Z_n (closed walks)."""
    # For efficiency, only enumerate walks that return to start
    walks = []
    def dfs(path, fc):
        if len(path) == L:
            # Check closure: last step goes back to start
            nxt_pos = path[0]
            last_pos = path[-1]
            if abs(last_pos - nxt_pos) == 1 or abs(last_pos - nxt_pos) == n - 1:
                walks.append(tuple(path))
            return
        pos = path[-1]
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < 3:  # allow up to 3 firings per proc
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)
    return walks


def step_dir(word, t, n):
    """Direction of step t: CW = +1, CCW = -1."""
    L = len(word)
    curr = word[t]
    nxt = word[(t + 1) % L]
    d = (nxt - curr) % n
    if d == 1:
        return 1  # CW
    elif d == n - 1:
        return -1  # CCW
    return 0


def winding_number(word, n):
    """Net winding: sum of directions."""
    L = len(word)
    total = 0
    for t in range(L):
        total += step_dir(word, t, n)
    return total


def cw_count(word, n):
    """Count CW steps."""
    return sum(1 for t in range(len(word)) if step_dir(word, t, n) == 1)


def ccw_count(word, n):
    """Count CCW steps."""
    return sum(1 for t in range(len(word)) if step_dir(word, t, n) == -1)


def edge_crossings(word, n):
    """For each edge p (from p to right(p)), list (time, direction) crossings."""
    L = len(word)
    crossings = defaultdict(list)
    for t in range(L):
        d = step_dir(word, t, n)
        if d == 1:
            # CW: crosses edge (word[t], word[t]+1) = edge word[t]
            crossings[word[t]].append((t, 'cw'))
        elif d == -1:
            # CCW: crosses edge (word[t]-1, word[t]) = edge (word[t]-1) % n
            crossings[(word[t] - 1) % n].append((t, 'ccw'))
    return crossings


def find_opposite_pairs(crossings):
    """Find all opposite-direction pairs at each edge, with their gaps."""
    pairs = []
    for edge, cross_list in crossings.items():
        cw_times = sorted([t for t, d in cross_list if d == 'cw'])
        ccw_times = sorted([t for t, d in cross_list if d == 'ccw'])
        for a in cw_times:
            for b in ccw_times:
                if a < b:
                    pairs.append((edge, a, b, b - a, 'cw-ccw'))
                elif b < a:
                    pairs.append((edge, b, a, a - b, 'ccw-cw'))
    return pairs


def global_min_gap(pairs):
    """Find the minimum gap among all opposite pairs."""
    if not pairs:
        return None
    return min(pairs, key=lambda x: x[3])


def has_3_consecutive_binary(ms, n):
    """Check if there are 3 consecutive binary processors."""
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return True, i
    return False, -1


def check_entry_conflict_at_gap1(word, n, ms, edge, a, b):
    """
    At a gap-1 opposite pair: steps a and b are adjacent (b = a+1).
    Step a crosses edge e in one direction, step b crosses in the other.

    For a CW-CCW pair at edge e:
    - Step a: mover = word[a], moves CW (word[a] -> word[a]+1 = right(word[a]))
    - Step b: mover = word[b], moves CCW (word[b] -> word[b]-1 = left(word[b]))

    Since gap=1 (b=a+1), at step a+1 the config is the RESULT of step a's move.
    """
    L = len(word)
    gap = b - a

    info = {
        'edge': edge,
        'a': a,
        'b': b,
        'gap': gap,
        'mover_a': word[a],
        'dir_a': step_dir(word, a, n),
        'mover_b': word[b],
        'dir_b': step_dir(word, b, n),
    }

    if gap == 1:
        # Steps a and a+1: the config at step a+1 is the result of moving at step a.
        # Mover at step a is p_a = word[a], mover at step a+1 is p_b = word[b].
        # The config values are:
        #   c_{a+1}[j] = c_a[j] for j != p_a
        #   c_{a+1}[p_a] = f_{p_a}(c_a[left(p_a)], c_a[p_a], c_a[right(p_a)])
        #
        # p_b is privileged at c_{a+1}, meaning:
        #   f_{p_b}(c_{a+1}[left(p_b)], c_{a+1}[p_b], c_{a+1}[right(p_b)]) != c_{a+1}[p_b]
        #
        # If p_a and p_b are adjacent (which they must be since both cross the same edge
        # in opposite directions in consecutive steps), then one of p_b's neighbors IS p_a.
        #
        # ENTRY CONFLICT MECHANISM:
        # At step a, p_a fires (it's the mover). The non-mover p_b sees context
        #   (c_a[left(p_b)], c_a[p_b], c_a[right(p_b)])
        # and since p_b is NOT firing: f_{p_b}(context) should equal c_a[p_b].
        #
        # At step a+1 = b, p_b fires (it's the mover). The mover p_b sees context
        #   (c_{a+1}[left(p_b)], c_{a+1}[p_b], c_{a+1}[right(p_b)])
        # and since p_b IS firing: f_{p_b}(context) != c_{a+1}[p_b].
        #
        # If p_a is NOT a neighbor of p_b: both contexts are identical!
        #   c_{a+1}[j] = c_a[j] for j != p_a, and p_a not in {left(p_b), p_b, right(p_b)}
        #   → same (L, S, R) → f must be both = S and != S. CONTRADICTION.
        #
        # But p_a IS a neighbor of p_b (they cross the same edge). So the contexts differ
        # at exactly the position where p_a sits (which is a neighbor of p_b).
        # The difference is: c_a[p_a] → f_{p_a}(c_a[left(p_a)], c_a[p_a], c_a[right(p_a)]).
        #
        # For BINARY p_a: the new value is 1 - c_a[p_a] (only option since m=2).
        # So the context changes at exactly one neighbor position.
        #
        # EC still possible if p_b is binary: p_b has only 2 states.
        # With the (L,S,R) changed at one neighbor, there are limited options.

        info['mechanism'] = 'gap1_adjacent_fire'
        info['p_a_is_left_of_p_b'] = (word[a] == (word[b] - 1) % n)
        info['p_a_is_right_of_p_b'] = (word[a] == (word[b] + 1) % n)

    return info


def enumerate_state_sequences(m, k):
    """All state sequences of length k+1 starting and ending at 0, with consecutive values different."""
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


def check_full_entry_conflict(word, n, ms):
    """Check ALL state-sequence combos for entry conflict. Return (total_valid, total_ec, ec_procs)."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    # For each proc, enumerate valid state sequences
    proc_seqs = {}
    for p in range(n):
        if fc[p] == 0:
            proc_seqs[p] = [[0]]  # never fires, stays at 0
        else:
            proc_seqs[p] = enumerate_state_sequences(ms[p], fc[p])

    sl = [proc_seqs[p] for p in range(n)]

    total_valid = 0
    total_ec = 0
    ec_procs_all = None

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
        total_valid += 1
        good = configs[:L]

        # Check entry conflict
        mover_entries = {}
        nonmover_entries = {}
        for t in range(L):
            c = good[t]
            cn = good[(t + 1) % L]
            mover = word[t]
            for j in range(n):
                key = (j, c[(j-1) % n], c[j], c[(j+1) % n])
                if j == mover:
                    mover_entries[key] = cn[j]
                else:
                    if key not in nonmover_entries:
                        nonmover_entries[key] = set()
                    nonmover_entries[key].add(c[j])

        cprocs = set()
        for key in mover_entries:
            if key in nonmover_entries:
                _, _, s, _ = key
                if mover_entries[key] != s:
                    cprocs.add(key[0])

        if cprocs:
            total_ec += 1
        if ec_procs_all is None:
            ec_procs_all = cprocs
        else:
            ec_procs_all &= cprocs

    return total_valid, total_ec, ec_procs_all


def main():
    print("=" * 70)
    print("RA12 Sorry A: Consecutive Binary + Zero-Winding Investigation")
    print("=" * 70)

    # Use small n first for tractability
    for n in [5, 6, 7]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        # Sub-threshold multisets with 3 consecutive binary
        # Product < 4 * 3^(n-2)
        threshold = 4 * (3 ** (n - 2))
        print(f"Threshold: {threshold}")

        # Generate candidate multisets
        # At least 3 binary (m=2), rest ternary (m=3) or higher
        # With 3 consecutive binary at positions 0,1,2
        candidates = []
        if n == 5:
            # ms with 3 binary at 0,1,2 and product < threshold=108
            # Options: (2,2,2,3,3)=36, (2,2,2,3,4)=48, (2,2,2,3,5)=60, etc.
            for m3 in range(2, 10):
                for m4 in range(2, 10):
                    ms = [2, 2, 2, m3, m4]
                    prod = 1
                    for m in ms:
                        prod *= m
                    if prod < threshold and sum(1 for m in ms if m == 2) >= 3:
                        candidates.append(ms)
        elif n == 6:
            for m3 in range(2, 6):
                for m4 in range(2, 6):
                    for m5 in range(2, 6):
                        ms = [2, 2, 2, m3, m4, m5]
                        prod = 1
                        for m in ms:
                            prod *= m
                        if prod < threshold and sum(1 for m in ms if m == 2) >= 3:
                            candidates.append(ms)
        elif n == 7:
            # Only try the simplest case
            for m3 in range(2, 5):
                for m4 in range(2, 5):
                    for m5 in range(2, 5):
                        for m6 in range(2, 5):
                            ms = [2, 2, 2, m3, m4, m5, m6]
                            prod = 1
                            for m in ms:
                                prod *= m
                            if prod < threshold and sum(1 for m in ms if m == 2) >= 3:
                                candidates.append(ms)

        print(f"Sub-threshold multisets with 3 consec binary: {len(candidates)}")

        # For each multiset, generate zero-winding fc=2 walks and check
        # Use the simplest multiset
        if not candidates:
            continue

        # Sort by product, pick smallest
        candidates.sort(key=lambda ms: (sum(ms), max(ms)))
        ms = candidates[0]
        prod = 1
        for m in ms:
            prod *= m
        print(f"Using ms = {ms}, product = {prod}")

        # Enumerate ALL fc=2 closed walks (good cycle mover words)
        # A good cycle has length L = sum of fire counts
        # For fc=2: L = 2n
        L = 2 * n
        print(f"Enumerating fc=2 walks of length {L}...")

        walks = []
        def dfs(path, fc):
            if len(path) == L:
                nxt_pos = path[0]
                last_pos = path[-1]
                d = (nxt_pos - last_pos) % n
                if d == 1 or d == n - 1:
                    if all(f == 2 for f in fc):
                        walks.append(tuple(path))
                return
            pos = path[-1]
            for d_step in [1, -1]:
                nxt = (pos + d_step) % n
                if fc[nxt] < 2:
                    fc[nxt] += 1
                    path.append(nxt)
                    dfs(path, fc)
                    path.pop()
                    fc[nxt] -= 1
        fc = [0] * n
        fc[0] = 1
        dfs([0], fc)

        # Deduplicate by rotation
        unique = set()
        deduped = []
        for w in walks:
            best = w
            for i in range(len(w)):
                rot = w[i:] + w[:i]
                if rot < best:
                    best = rot
            if best not in unique:
                unique.add(best)
                deduped.append(list(best))

        print(f"Total fc=2 walks: {len(walks)}, unique (up to rotation): {len(deduped)}")

        # Classify by winding
        zw_walks = []
        for w in deduped:
            wn = winding_number(w, n)
            if wn == 0:
                cw_c = cw_count(w, n)
                if cw_c > 0:
                    zw_walks.append(w)

        print(f"Zero-winding walks with CW > 0: {len(zw_walks)}")

        # For each zero-winding walk, find opposite pairs and global min gap
        gap1_count = 0
        gap1_walks = []
        gap_dist = defaultdict(int)

        for w in zw_walks:
            crossings = edge_crossings(w, n)
            pairs = find_opposite_pairs(crossings)
            if pairs:
                mg = global_min_gap(pairs)
                gap_dist[mg[3]] += 1
                if mg[3] == 1:
                    gap1_count += 1
                    gap1_walks.append((w, mg))

        print(f"\nGlobal min gap distribution:")
        for gap, count in sorted(gap_dist.items()):
            print(f"  gap={gap}: {count} walks")
        print(f"Gap=1 walks: {gap1_count}")

        # For gap=1 walks: check EC mechanism
        print(f"\nAnalyzing gap=1 walks (first 5):")
        for w, mg in gap1_walks[:5]:
            edge, a, b, gap, pair_type = mg
            info = check_entry_conflict_at_gap1(w, n, ms, edge, a, b)
            print(f"  word = {w}")
            print(f"  min pair: edge={edge}, steps=({a},{b}), type={pair_type}")
            print(f"  movers: step {a}→proc {info['mover_a']}, step {b}→proc {info['mover_b']}")
            print(f"  p_a is {'LEFT' if info['p_a_is_left_of_p_b'] else 'RIGHT' if info['p_a_is_right_of_p_b'] else 'NEITHER'} of p_b")

            # Check: is the gap-1 edge at a binary boundary?
            right_of_edge = (edge + 1) % n
            print(f"  edge {edge}→{right_of_edge}: binary(edge)={ms[edge]==2}, binary(right)={ms[right_of_edge]==2}")

        # Full entry conflict check on gap=1 walks
        if gap1_walks and n <= 6:
            print(f"\nFull EC check on ALL gap=1 walks (n={n}, ms={ms}):")
            all_ec = True
            for w, mg in gap1_walks:
                tv, tec, ecprocs = check_full_entry_conflict(w, n, ms)
                if tv == 0:
                    continue
                if tec < tv:
                    print(f"  FAIL: word={w}, valid={tv}, ec={tec}")
                    all_ec = False
                else:
                    pass  # all have EC
            if all_ec:
                print(f"  ALL gap=1 walks have EC (100%)")

        # Check: does EVERY zero-winding walk have EC? (not just gap=1)
        if zw_walks and n <= 6:
            print(f"\nFull EC check on ALL zero-winding walks (n={n}, ms={ms}):")
            all_ec = True
            fail_count = 0
            for w in zw_walks:
                tv, tec, ecprocs = check_full_entry_conflict(w, n, ms)
                if tv == 0:
                    continue
                if tec < tv:
                    fail_count += 1
                    if fail_count <= 3:
                        print(f"  FAIL: word={w}, valid={tv}, ec={tec}")
                    all_ec = False
            if all_ec:
                print(f"  ALL zero-winding walks have EC (100%)")
            else:
                print(f"  {fail_count} walks lack universal EC")

    # KEY INVESTIGATION: Gap=1 → what's the direct EC argument?
    print(f"\n{'='*70}")
    print("KEY ANALYSIS: Gap=1 Entry Conflict Mechanism")
    print("="*70)
    print("""
When the global min gap = 1 at edge e:
- Step a: mover p_a crosses edge e in direction d
- Step a+1: mover p_b crosses edge e in direction -d

Since gap = 1, steps are consecutive. p_a and p_b must be adjacent
(they share edge e). So p_b is a neighbor of p_a.

At step a: p_b is a non-mover. Its context is (L, S, R) where one of
L or R is c_a[p_a] (p_a's current value, BEFORE firing).

At step a+1: p_b is the mover. Its context is (L', S, R') where
the position that was p_a now has p_a's NEW value (after firing).

For BINARY p_a: the new value is 1 - old_value. So the context changed
at exactly one position.

For p_b: at step a, f(L,S,R) = S (non-mover).
         at step a+1, f(L',S,R') != S (mover).

If p_a is left(p_b): L' = f_{p_a}(context) != L (since p_a fired).
  So f(L,S,R)=S and f(L',S,R)!=S. Different L, different output.
  NO DIRECT CONTRADICTION from this alone.

If p_a is right(p_b): R' = f_{p_a}(context) != R.
  So f(L,S,R)=S and f(L,S,R')!=S. Different R, different output.
  Again, no DIRECT contradiction.

BUT: there are OTHER non-mover observations at these same steps!
At step a, EVERY other proc j != p_a is a non-mover observing its context.
At step a+1, EVERY other proc j != p_b is a non-mover.

The gap-1 pair creates a VERY tight temporal constraint. If there's ANOTHER
step nearby where p_b fires again or p_a fires again, we can chain observations.

CRUCIAL: With binary p_a, the value change is deterministic (0↔1).
After p_a fires at step a, c_{a+1}[p_a] = 1 - c_a[p_a].
If p_a fires AGAIN at some step c: c_{c+1}[p_a] = 1 - c_c[p_a] = ...
With fc(p_a) = 2 (binary fires exactly twice), the two firings swap the value twice,
returning to the original.

PALINDROMIC ARGUMENT: In a zero-winding fc=2 walk with gap=1, the walk
makes a "turnaround" at the gap-1 pair. The palindromic structure means
the CW non-mover context at some interior proc j equals the CCW mover
context at j, creating f(ctx) = S AND f(ctx) != S.

This is EXACTLY the Palindromic Entry Conflict from Palindromic.lean.
The gap=1 sub-case doesn't need a different mechanism — it's a SPECIAL CASE
of palindromic EC where the turnaround happens at the global min gap edge.
""")

    # Verify: for gap=1 walks, check if the palindromic EC mechanism fires
    print("Verifying palindromic EC on gap=1 walks at n=5:")
    n = 5
    ms = [2, 2, 2, 3, 3]
    L = 2 * n
    walks2 = []
    def dfs2(path, fc):
        if len(path) == L:
            nxt_pos = path[0]
            last_pos = path[-1]
            d = (nxt_pos - last_pos) % n
            if d == 1 or d == n - 1:
                if all(f == 2 for f in fc):
                    walks2.append(tuple(path))
            return
        pos = path[-1]
        for d_step in [1, -1]:
            nxt = (pos + d_step) % n
            if fc[nxt] < 2:
                fc[nxt] += 1
                path.append(nxt)
                dfs2(path, fc)
                path.pop()
                fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs2([0], fc)

    unique2 = set()
    deduped2 = []
    for w in walks2:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique2:
            unique2.add(best)
            deduped2.append(list(best))

    zw2 = [w for w in deduped2 if winding_number(w, n) == 0 and cw_count(w, n) > 0]

    for w in zw2[:3]:
        crossings = edge_crossings(w, n)
        pairs = find_opposite_pairs(crossings)
        mg = global_min_gap(pairs)
        print(f"\n  word = {w}")
        print(f"  winding = {winding_number(w, n)}, CW = {cw_count(w, n)}, CCW = {ccw_count(w, n)}")
        print(f"  global min gap: edge={mg[0]}, steps=({mg[1]},{mg[2]}), gap={mg[3]}, type={mg[4]}")

        # Show the palindromic structure
        for t in range(len(w)):
            d = step_dir(w, t, n)
            d_str = "CW" if d == 1 else "CCW" if d == -1 else "??"
            print(f"    step {t}: proc {w[t]} fires {d_str}")

    print("\nDONE")


if __name__ == "__main__":
    main()
