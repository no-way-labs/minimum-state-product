#!/usr/bin/env python3
"""
CIC Exploration 14: Case 3a — 3 Consecutive Binary, Non-Sweep Cycles.

For ms = [2,2,2,3,...,3] (3 consecutive binary at {0,1,2}):
- Sweep cycles killed by Shadow Cycle Mirror Theorem
- Need to kill non-sweep cycles

Key constraint: binary fire counts must be EVEN.
A wiggle at any edge adjacent to binary makes that binary's fc odd → FORBIDDEN.
So wiggles can only occur deep in the ternary segment.

Main non-sweep type: "back-and-forth" (winding number 0).
"""

from itertools import product as iproduct
import sys


def make_baf_word(n):
    """Back-and-forth word: 0,1,...,n-1,n-2,...,1,0,n-1."""
    return list(range(n)) + list(range(n - 2, 0, -1)) + [0, n - 1]


def make_sweep_word(n):
    """Standard CW sweep: 0,1,...,n-1,0,1,...,n-1."""
    return list(range(n)) * 2


def enumerate_fc2_walks(n, max_len=None):
    """Enumerate all closed walks on C_n with fc=2 for every vertex."""
    if max_len is None:
        max_len = 2 * n
    walks = []

    def dfs(path, fc):
        pos = path[-1]
        step = len(path)
        if step == max_len:
            # Check closure: next position should be path[0]
            nxt = path[0]
            if abs(pos - nxt) == 1 or abs(pos - nxt) == n - 1:
                if all(f == 2 for f in fc):
                    walks.append(tuple(path))
            return
        remaining = max_len - step
        # Prune: remaining must be enough for unvisited vertices
        deficit = sum(1 for f in fc if f < 2)
        # Each unvisited vertex needs at least 1 more visit
        # (very loose bound, but helps)
        for d in [1, -1]:
            nxt = (pos + d) % n
            if fc[nxt] < 2:
                fc[nxt] += 1
                path.append(nxt)
                dfs(path, fc)
                path.pop()
                fc[nxt] -= 1

    # Start at 0 to reduce rotational redundancy
    fc = [0] * n
    fc[0] = 1
    dfs([0], fc)

    # Deduplicate by rotation
    unique = set()
    result = []
    for w in walks:
        # Find canonical rotation
        best = w
        for i in range(len(w)):
            rot = w[i:] + w[:i]
            if rot < best:
                best = rot
        if best not in unique:
            unique.add(best)
            result.append(list(best))

    return result


def compute_waterfall(word, n):
    L = len(word)
    g = [[0] * (L + 1) for _ in range(n)]
    for t in range(L):
        for j in range(n):
            g[j][t + 1] = g[j][t]
        g[word[t]][t + 1] = g[word[t]][t] + 1
    return g


def enumerate_state_sequences(n, ms, fire_counts):
    proc_sequences = {}
    for p in range(n):
        m = ms[p]
        k = fire_counts[p]
        seqs = []

        def dfs_seq(seq, remaining, m_val=m, out=seqs):
            if remaining == 0:
                if seq[-1] == 0:
                    out.append(list(seq))
                return
            current = seq[-1]
            for nv in range(m_val):
                if nv != current:
                    if remaining == 1 and nv != 0:
                        continue
                    seq.append(nv)
                    dfs_seq(seq, remaining - 1, m_val, out)
                    seq.pop()

        dfs_seq([0], k)
        proc_sequences[p] = seqs
    return proc_sequences


def check_shadow(word, n, ms):
    """Check if ALL valid state-sequence combos produce shadow cycles."""
    L = len(word)
    fc = [0] * n
    for p in word:
        fc[p] += 1

    g = compute_waterfall(word, n)
    proc_seqs = enumerate_state_sequences(n, ms, fc)
    sl = [proc_seqs[p] for p in range(n)]

    total_valid = 0
    total_shadow = 0

    for combo in iproduct(*sl):
        ss = {p: combo[p] for p in range(n)}

        # Build good cycle
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
        good_set = set(good)

        # Extract mover entries
        me = {}
        for t in range(L):
            c = good[t]
            cn = good[(t + 1) % L]
            m = word[t]
            key = (m, c[(m - 1) % n], c[m], c[(m + 1) % n])
            me[key] = cn[m]

        # Check MNU
        mnu_keys = set()
        mnu_ok = True
        for t in range(L):
            c = good[t]
            m = word[t]
            key = (m, c[(m - 1) % n], c[m], c[(m + 1) % n])
            if key in mnu_keys:
                mnu_ok = False
                break
            mnu_keys.add(key)

        # Find shadow via SCC trace
        all_cfgs = list(iproduct(*[range(m) for m in ms]))
        non_good = [c for c in all_cfgs if c not in good_set]

        found_shadow = False
        for start in non_good:
            config = start
            path = [config]
            visited = {config: 0}
            movers = []

            for step_i in range(L + 50):
                forced = []
                for j in range(n):
                    key = (j, config[(j - 1) % n], config[j],
                           config[(j + 1) % n])
                    if key in me and me[key] != config[j]:
                        forced.append((j, me[key]))
                if not forced:
                    break

                moved = False
                for proc, new_val in forced:
                    nc = list(config)
                    nc[proc] = new_val
                    nc = tuple(nc)
                    if nc not in good_set:
                        movers.append(proc)
                        config = nc
                        path.append(config)
                        if config in visited:
                            cs = visited[config]
                            cycle_len = len(movers[cs:])
                            if cycle_len == L:
                                shadow = path[cs:-1]
                                # Check 5 properties
                                p3 = len(set(shadow)) == L
                                p4 = len(set(shadow) & good_set) == 0
                                p5 = True
                                for tt in range(L):
                                    sc = shadow[tt]
                                    for jj in range(n):
                                        kk = (jj, sc[(jj - 1) % n],
                                              sc[jj], sc[(jj + 1) % n])
                                        if kk in me and me[kk] != sc[jj]:
                                            ncc = list(sc)
                                            ncc[jj] = me[kk]
                                            if tuple(ncc) in good_set:
                                                p5 = False
                                if p3 and p4 and p5:
                                    found_shadow = True
                                    break
                        visited[config] = step_i + 1
                        moved = True
                        break
                if found_shadow:
                    break
                if not moved:
                    break
            if found_shadow:
                break

        if found_shadow:
            total_shadow += 1

    return total_valid, total_shadow


def main():
    print("CIC Exploration 14: Case 3a — 3 Consecutive Binary")
    print("=" * 70)

    # PART 1: Fire count parity constraint
    print("\nPART 1: Binary Fire Count Parity")
    print("-" * 70)
    print("""
  For 3 consecutive binary at {0,1,2} with fc[j] even:
  A wiggle at edge (j,j+1) adds 1 to both fc[j] and fc[j+1].
  If j or j+1 is binary, this makes fc odd → INVALID.

  Affected edges: (n-1,0), (0,1), (1,2), (2,3) — all 4 boundary edges.
  So wiggles can ONLY occur at edges (k,k+1) with k ∈ {3,...,n-2}.
  (Deep in the ternary segment.)
""")

    # PART 2: Enumerate non-sweep fc=2 words
    print("PART 2: Non-Sweep Words with fc=2")
    print("-" * 70)

    for n in range(5, 10):
        walks = enumerate_fc2_walks(n)
        # Classify
        sweep = make_sweep_word(n)
        sweep_rev = list(range(n - 1, -1, -1)) * 2
        # Canonical forms of sweep
        sweep_rotations = set()
        for i in range(2 * n):
            sweep_rotations.add(tuple(sweep[i:] + sweep[:i]))
            sweep_rotations.add(tuple(sweep_rev[i:] + sweep_rev[:i]))

        non_sweep = [w for w in walks if tuple(w) not in sweep_rotations]

        # Check if back-and-forth is among them
        baf = make_baf_word(n)
        baf_canon = baf
        for i in range(len(baf)):
            rot = tuple(baf[i:] + baf[:i])
            if rot < tuple(baf_canon):
                baf_canon = list(rot)

        baf_found = any(tuple(w) == tuple(baf_canon)
                        for w in non_sweep)

        print(f"  n={n}: {len(walks)} total fc=2 words, "
              f"{len(non_sweep)} non-sweep"
              f"{' (includes BAF)' if baf_found else ''}")

        if n <= 7:
            for w in non_sweep[:5]:
                print(f"    {w}")

    # PART 3: Shadow check for back-and-forth words
    print("\n\nPART 3: Shadow Check for Back-and-Forth Words")
    print("-" * 70)

    for n in range(5, 12):
        w = make_baf_word(n)
        L = len(w)
        ms = [2, 2, 2] + [3] * (n - 3)

        if n <= 9:
            total_v, total_s = check_shadow(w, n, ms)
            tag = '✓' if total_s == total_v and total_v > 0 else '✗'
            print(f"  n={n}: BAF word {w}")
            print(f"    L={L}, {total_v} valid combos, "
                  f"{total_s} with shadow {tag}")
        else:
            # Just report the word
            print(f"  n={n}: BAF word (L={L})")

    # PART 4: Shadow check for ALL non-sweep words at small n
    print("\n\nPART 4: All Non-Sweep Words (n=5..8)")
    print("-" * 70)

    for n in range(5, 9):
        walks = enumerate_fc2_walks(n)
        sweep = make_sweep_word(n)
        sweep_rev = list(range(n - 1, -1, -1)) * 2
        sweep_rotations = set()
        for i in range(2 * n):
            sweep_rotations.add(tuple(sweep[i:] + sweep[:i]))
            sweep_rotations.add(tuple(sweep_rev[i:] + sweep_rev[:i]))

        non_sweep = [w for w in walks if tuple(w) not in sweep_rotations]
        ms = [2, 2, 2] + [3] * (n - 3)

        all_killed = True
        for w in non_sweep:
            total_v, total_s = check_shadow(w, n, ms)
            if total_v > 0 and total_s < total_v:
                all_killed = False
                print(f"  n={n} word={w}: SURVIVES "
                      f"({total_s}/{total_v})")

        if all_killed:
            total_ns = len(non_sweep)
            print(f"  n={n}: ALL {total_ns} non-sweep words killed by shadow ✓")

    # PART 5: Also check the quaternary multiset {2^3, 4, 3^(n-4)}
    print("\n\nPART 5: Quaternary Multiset {2^3, 4, 3^(n-4)}")
    print("-" * 70)

    for n in range(6, 10):
        w = make_baf_word(n)
        # Quaternary at position 3 (first non-binary)
        ms = [2, 2, 2, 4] + [3] * (n - 4)

        total_v, total_s = check_shadow(w, n, ms)
        tag = '✓' if total_s == total_v and total_v > 0 else '✗'
        print(f"  n={n} ms={ms}: BAF {total_s}/{total_v} {tag}")

        if n <= 7:
            # Also quaternary at other positions
            for qpos in range(4, n):
                ms2 = [2, 2, 2] + [3] * (n - 3)
                ms2[qpos] = 4
                tv, ts = check_shadow(w, n, ms2)
                tag2 = '✓' if ts == tv and tv > 0 else '✗'
                print(f"    qpos={qpos} ms={ms2}: {ts}/{tv} {tag2}")

    # PART 6: Check MNU specifically
    print("\n\nPART 6: MNU Analysis for Back-and-Forth Words")
    print("-" * 70)

    for n in range(5, 12):
        w = make_baf_word(n)
        L = len(w)
        ms = [2, 2, 2] + [3] * (n - 3)

        fc = [0] * n
        for p in w:
            fc[p] += 1

        g = compute_waterfall(w, n)
        proc_seqs = enumerate_state_sequences(n, ms, fc)
        sl = [proc_seqs[p] for p in range(n)]

        total_valid = 0
        mnu_pass = 0

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

            total_valid += 1
            good = configs[:L]

            # Check MNU
            seen = set()
            ok = True
            for t in range(L):
                c = good[t]
                m = w[t]
                key = (m, c[(m - 1) % n], c[m], c[(m + 1) % n])
                if key in seen:
                    ok = False
                    break
                seen.add(key)
            if ok:
                mnu_pass += 1

        tag = '✓' if mnu_pass == total_valid and total_valid > 0 else '✗'
        print(f"  n={n}: MNU {mnu_pass}/{total_valid} {tag}")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
