#!/usr/bin/env python3
"""
RA12 Sorry B: non-consecutive binary + zero-winding → False

Investigate: at n=5..9 with >=3 non-consecutive binary and sub-threshold product,
generate zero-winding good cycles and check:
1. Do they always have entry conflict?
2. What EC mechanism covers them?
3. Does procMinGap suffice?
4. Can zero-winding + non-consecutive + binary boundary → EC directly?
"""

from itertools import product as iproduct
from collections import defaultdict


def step_dir(word, t, n):
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
    return sum(step_dir(word, t, n) for t in range(len(word)))


def cw_count(word, n):
    return sum(1 for t in range(len(word)) if step_dir(word, t, n) == 1)


def has_3_consecutive_binary(ms, n):
    for i in range(n):
        if ms[i] == 2 and ms[(i+1) % n] == 2 and ms[(i+2) % n] == 2:
            return True
    return False


def has_ge3_binary(ms):
    return sum(1 for m in ms if m == 2) >= 3


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


def check_full_entry_conflict(word, n, ms):
    """Check ALL combos for entry conflict. Return (total_valid, total_ec, ec_procs_intersection)."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    proc_seqs = {}
    for p in range(n):
        if fc[p] == 0:
            proc_seqs[p] = [[0]]
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


def edge_crossings(word, n):
    L = len(word)
    crossings = defaultdict(list)
    for t in range(L):
        d = step_dir(word, t, n)
        if d == 1:
            crossings[word[t]].append((t, 'cw'))
        elif d == -1:
            crossings[(word[t] - 1) % n].append((t, 'ccw'))
    return crossings


def find_opposite_pairs(crossings):
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


def proc_min_gap(crossings, n, ms, proc):
    """For a binary proc p, find the minimum gap between opposite crossings
    at either adjacent edge."""
    # Edges adjacent to proc p: edge (p-1, p) = edge (p-1)%n, and edge (p, p+1) = edge p
    edges = [(proc - 1) % n, proc]
    min_gap = float('inf')
    min_info = None
    for e in edges:
        if e not in crossings:
            continue
        cw_times = sorted([t for t, d in crossings[e] if d == 'cw'])
        ccw_times = sorted([t for t, d in crossings[e] if d == 'ccw'])
        for a in cw_times:
            for b in ccw_times:
                gap = abs(b - a)
                if gap > 0 and gap < min_gap:
                    min_gap = gap
                    min_info = (e, a, b, gap)
    return min_gap, min_info


def main():
    print("=" * 70)
    print("RA12 Sorry B: Non-Consecutive Binary + Zero-Winding Investigation")
    print("=" * 70)

    for n in [5, 6, 7]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        threshold = 4 * (3 ** (n - 2))
        print(f"Threshold: {threshold}")

        # Generate sub-threshold multisets with >=3 binary but NO 3 consecutive
        candidates = []
        if n == 5:
            for combo in iproduct(range(2, 10), repeat=n):
                ms = list(combo)
                prod = 1
                for m in ms:
                    prod *= m
                if prod < threshold and has_ge3_binary(ms) and not has_3_consecutive_binary(ms, n):
                    # Normalize: sort of rotations
                    candidates.append(tuple(ms))
        elif n == 6:
            for combo in iproduct(range(2, 6), repeat=n):
                ms = list(combo)
                prod = 1
                for m in ms:
                    prod *= m
                if prod < threshold and has_ge3_binary(ms) and not has_3_consecutive_binary(ms, n):
                    candidates.append(tuple(ms))
        elif n == 7:
            for combo in iproduct(range(2, 4), repeat=n):
                ms = list(combo)
                prod = 1
                for m in ms:
                    prod *= m
                if prod < threshold and has_ge3_binary(ms) and not has_3_consecutive_binary(ms, n):
                    candidates.append(tuple(ms))

        # Deduplicate by rotation
        unique_ms = set()
        deduped_ms = []
        for ms in candidates:
            best = ms
            for i in range(n):
                rot = ms[i:] + ms[:i]
                if rot < best:
                    best = rot
            if best not in unique_ms:
                unique_ms.add(best)
                deduped_ms.append(list(best))

        print(f"Non-consecutive sub-threshold multisets: {len(deduped_ms)}")
        if not deduped_ms:
            print("  (none found)")
            continue

        # For n=5: non-consecutive with >=3 binary means binary procs are separated
        # e.g., ms = [2, 3, 2, 3, 2] — binary at 0, 2, 4 (alternating)
        # With 5 procs, 3 binary, non-consecutive: exactly alternating pattern

        # Pick simplest
        deduped_ms.sort(key=lambda ms: (sum(ms), max(ms)))
        ms = deduped_ms[0]
        prod = 1
        for m in ms:
            prod *= m
        print(f"Using ms = {ms}, product = {prod}")

        binary_pos = [i for i in range(n) if ms[i] == 2]
        print(f"Binary positions: {binary_pos}")

        # Enumerate fc=2 walks
        L = 2 * n
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

        print(f"Total fc=2 walks: {len(walks)}, unique: {len(deduped)}")

        zw_walks = [w for w in deduped if winding_number(w, n) == 0 and cw_count(w, n) > 0]
        print(f"Zero-winding walks with CW > 0: {len(zw_walks)}")

        if not zw_walks:
            continue

        # Analyze edge crossings and gaps for each ZW walk
        gap_dist = defaultdict(int)
        binary_edge_gap_dist = defaultdict(int)

        for w in zw_walks:
            crossings = edge_crossings(w, n)
            pairs = find_opposite_pairs(crossings)
            if pairs:
                mg = min(pairs, key=lambda x: x[3])
                gap_dist[mg[3]] += 1

            # Check min gap at binary proc boundaries
            for bp in binary_pos:
                mg_bp, info = proc_min_gap(crossings, n, ms, bp)
                if info:
                    binary_edge_gap_dist[mg_bp] += 1

        print(f"\nGlobal min gap distribution:")
        for gap, count in sorted(gap_dist.items()):
            print(f"  gap={gap}: {count} walks")

        print(f"\nBinary proc min gap distribution:")
        for gap, count in sorted(binary_edge_gap_dist.items()):
            print(f"  gap={gap}: {count} (proc, walk) pairs")

        # Full EC check
        if n <= 6:
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
                        print(f"  FAIL: word={w}, valid={tv}, ec={tec}, ec_procs={ecprocs}")
                    all_ec = False
            if all_ec:
                print(f"  ALL zero-winding walks have EC (100%)")
            else:
                print(f"  {fail_count} walks lack universal EC")

        # Show walk structure for first few
        print(f"\nZero-winding walks (first 5):")
        for w in zw_walks[:5]:
            crossings = edge_crossings(w, n)
            print(f"\n  word = {w}")
            for t in range(len(w)):
                d = step_dir(w, t, n)
                d_str = "CW" if d == 1 else "CCW"
                print(f"    step {t}: proc {w[t]} fires {d_str}")

            # Which edges are crossed?
            for e in sorted(crossings.keys()):
                cw_t = [t for t, d in crossings[e] if d == 'cw']
                ccw_t = [t for t, d in crossings[e] if d == 'ccw']
                right_e = (e + 1) % n
                bin_label = f"[B-B]" if ms[e] == 2 and ms[right_e] == 2 else \
                            f"[B-T]" if ms[e] == 2 else \
                            f"[T-B]" if ms[right_e] == 2 else "[T-T]"
                print(f"    edge {e}→{right_e} {bin_label}: CW@{cw_t}, CCW@{ccw_t}")

    # KEY INVESTIGATION: procMinGap for non-consecutive binary
    print(f"\n{'='*70}")
    print("KEY ANALYSIS: ProcMinGap for Non-Consecutive Binary")
    print("="*70)

    print("""
For non-consecutive binary, the key structures are:
- Binary procs are isolated (no two adjacent)
- Each binary proc p has ternary neighbors left(p) and right(p)
- Edge crossings at binary boundaries: edge (p-1,p) and (p, p+1)

Zero-winding means cwMoveCountAt(q) = ccwMoveCountAt(right(q)) for all q.
So every crossed edge is crossed in BOTH directions.

With >=3 binary and no-safe: every binary proc has at least one adjacent
edge crossed (otherwise it and its neighbors form a safe region).

For each binary proc p with a crossed adjacent edge e:
- The edge has both CW and CCW crossings
- The minimum gap between opposite crossings at this edge gives the
  procMinGap for p

ProcMinGap handles gap >= 2: this gives a MinGapArc with >=1 interior
step, and BAFArcAdj + binary endpoint → entry conflict.

Gap = 1 at a binary boundary of a non-consecutive binary proc:
- Step a: mover p_a crosses edge e (one direction)
- Step a+1: mover p_b crosses edge e (opposite direction)
- p_a and p_b are adjacent, one of them is binary
- The binary proc is p (the non-consecutive binary proc)

CRUCIAL OBSERVATION: In the non-consecutive case, p has ternary neighbors.
If p = p_a (binary fires CW): next mover p_b = right(p) is ternary.
  At step a, right(p) is non-mover with some context (L,S,R).
  At step a+1, right(p) fires with context (L',S,R) where L' = new value of p.
  Since p is binary: L' = 1 - L. So contexts differ in L.
  f(L,S,R) = S (non-mover) and f(1-L,S,R) != S (mover).
  NOT a direct EC at right(p) — different L values.

  But: proc left(p) is ternary and didn't fire at steps a or a+1 (it's not
  adjacent to edge e). So left(p) sees the SAME context at both steps.
  Wait — that's only true if no proc between left(p) and p fires at step a.
  Since p fires at step a, and p is adjacent to left(p), left(p)'s right
  neighbor IS p. So left(p) sees p's OLD value at step a (as non-mover)
  and p's NEW value at step a+1 (if left(p) is still non-mover).

  Hmm, this is getting circular. Let me check computationally.
""")

    # Focused check: at n=5, ms=[2,3,2,3,2], all ZW walks
    n = 5
    ms = [2, 3, 2, 3, 2]
    L = 10
    print(f"\nFocused: n={n}, ms={ms}")

    walks = []
    def dfs3(path, fc):
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
                dfs3(path, fc)
                path.pop()
                fc[nxt] -= 1
    fc = [0] * n
    fc[0] = 1
    dfs3([0], fc)

    unique3 = set()
    deduped3 = []
    for w in walks:
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique3:
            unique3.add(best)
            deduped3.append(list(best))

    zw3 = [w for w in deduped3 if winding_number(w, n) == 0 and cw_count(w, n) > 0]
    print(f"Zero-winding walks: {len(zw3)}")

    for w in zw3:
        crossings = edge_crossings(w, n)
        pairs = find_opposite_pairs(crossings)
        mg = min(pairs, key=lambda x: x[3]) if pairs else None

        tv, tec, ecprocs = check_full_entry_conflict(w, n, ms)
        print(f"\n  word = {w}, winding=0, CW={cw_count(w,n)}")
        print(f"  global min gap = {mg[3] if mg else 'N/A'}, edge = {mg[0] if mg else 'N/A'}")
        print(f"  valid combos = {tv}, EC = {tec}, EC procs = {ecprocs}")

        # Show which procs have EC and at what context
        if tv > 0 and ecprocs:
            # Pick one combo and show the conflict
            fc_check = [0] * n
            for p in w:
                fc_check[p] += 1
            proc_seqs = {}
            for p in range(n):
                if fc_check[p] == 0:
                    proc_seqs[p] = [[0]]
                else:
                    proc_seqs[p] = enumerate_state_sequences(ms[p], fc_check[p])
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
                mover_entries = {}
                nonmover_entries = {}
                for t in range(L):
                    c = good[t]
                    cn = good[(t + 1) % L]
                    mover = w[t]
                    for j in range(n):
                        key = (j, c[(j-1) % n], c[j], c[(j+1) % n])
                        if j == mover:
                            mover_entries[key] = cn[j]
                        else:
                            if key not in nonmover_entries:
                                nonmover_entries[key] = set()
                            nonmover_entries[key].add(c[j])

                for key in mover_entries:
                    if key in nonmover_entries:
                        j, l, s, r = key
                        if mover_entries[key] != s and j in ecprocs:
                            print(f"    EC at proc {j}: ctx=({l},{s},{r}), mover→{mover_entries[key]}, nonmover→{s}, ms[{j}]={ms[j]}")
                break  # one example suffices

    # Check: does procMinGap (gap >= 2) handle everything?
    print(f"\n{'='*70}")
    print("ProcMinGap coverage check")
    print("="*70)

    for n_check in [5, 6]:
        if n_check == 5:
            ms_check = [2, 3, 2, 3, 2]
        else:
            ms_check = [2, 3, 2, 3, 2, 3]
        L_check = 2 * n_check
        threshold_check = 4 * (3 ** (n_check - 2))
        prod_check = 1
        for m in ms_check:
            prod_check *= m
        print(f"\nn={n_check}, ms={ms_check}, product={prod_check}, threshold={threshold_check}")

        walks_check = []
        def dfs4(path, fc):
            if len(path) == L_check:
                nxt = path[0]
                last = path[-1]
                d = (nxt - last) % n_check
                if d == 1 or d == n_check - 1:
                    if all(f == 2 for f in fc):
                        walks_check.append(tuple(path))
                return
            pos = path[-1]
            for ds in [1, -1]:
                nxt = (pos + ds) % n_check
                if fc[nxt] < 2:
                    fc[nxt] += 1
                    path.append(nxt)
                    dfs4(path, fc)
                    path.pop()
                    fc[nxt] -= 1
        fc = [0] * n_check
        fc[0] = 1
        dfs4([0], fc)

        unique4 = set()
        deduped4 = []
        for w in walks_check:
            best = w
            for i in range(len(w)):
                rot = w[i:] + w[:i]
                if rot < best:
                    best = rot
            if best not in unique4:
                unique4.add(best)
                deduped4.append(list(best))

        zw4 = [w for w in deduped4 if winding_number(w, n_check) == 0 and cw_count(w, n_check) > 0]
        print(f"Zero-winding walks: {len(zw4)}")

        gap1_at_binary = 0
        gap2plus_at_binary = 0
        no_binary_crossing = 0
        binary_pos_check = [i for i in range(n_check) if ms_check[i] == 2]

        for w in zw4:
            crossings = edge_crossings(w, n_check)
            has_gap1_binary = False
            has_gap2_binary = False

            for bp in binary_pos_check:
                mg, info = proc_min_gap(crossings, n_check, ms_check, bp)
                if info is None:
                    continue
                if mg == 1:
                    has_gap1_binary = True
                elif mg >= 2:
                    has_gap2_binary = True

            if has_gap1_binary:
                gap1_at_binary += 1
            elif has_gap2_binary:
                gap2plus_at_binary += 1
            else:
                no_binary_crossing += 1

        print(f"  gap>=2 at some binary proc: {gap2plus_at_binary} (handled by procMinGap)")
        print(f"  gap=1 at ALL binary crossings: {gap1_at_binary}")
        print(f"  no binary crossing: {no_binary_crossing}")

    print("\nDONE")


if __name__ == "__main__":
    main()
