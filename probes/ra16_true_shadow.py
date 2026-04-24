#!/usr/bin/env python3
"""
RA16f: True shadow cycle analysis using the PROVED MNU+Escape framework.

The existing proved shadow theorem says:
1. For UNIFORM sweeps with >=3 binary (no 3 consecutive), shadow cycle exists
   of length 2n (paired configs).
2. Shadow uses a specific permutation sigma.
3. MNU at every position + disjointness + escape => obstruction.

But these no-EC cycles are NOT uniform sweeps -- they have turnarounds.
Let me check:
(a) What is the cycle structure? (How many turnarounds? What pattern?)
(b) Does the PROVED shadow cycle theorem from CIC apply to these words?
(c) If not, what alternative mechanism blocks them?

Actually wait -- I need to reconsider what "sweep" means more carefully.
The displacement is -2n (at n=7) or -2n (at n=9), which means the token
goes around the ring twice. But the word has turnarounds (stutters).

From CIC Expl 12-15: the WIGGLE shadow cycle handles single-wiggle words.
Let me check if these no-EC words are single-wiggle.

Alternatively: the existing "shadow_general_n.py" proves shadow for uniform
sweeps. The "cic_wiggle_shadow_proof5.py" proves shadow for wiggle words.

Let me characterize these words precisely.
"""
from itertools import combinations
from collections import Counter
import time


def total_displacement(word, n):
    disp = 0
    L = len(word)
    for i in range(L):
        nxt = word[(i + 1) % L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            disp += 1
        elif diff == n - 1:
            disp -= 1
        else:
            return None
    return disp


def has_3_consecutive_binary(ms):
    n = len(ms)
    for i in range(n):
        if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
            return True
    return False


def enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=120):
    target_cl = sum(ms)
    results = []
    t0 = time.time()
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    def dfs(word, fc):
        if time.time() - t0 > timeout: return
        if len(results) >= max_results: return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n-1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1
    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results: break
        fc = [0]*n
        fc[start] = 1
        if fc[start] <= ms[start]:
            dfs([start], fc)
    return results


def canonicalize(word):
    L = len(word)
    best = word
    for i in range(L):
        rot = word[i:] + word[:i]
        if rot < best:
            best = rot
    return best


def build_configs_all_trans(word, ms, n):
    L = len(word)
    wl = list(word)
    bins = {p for p in range(n) if ms[p] == 2}
    ternary = [p for p in range(n) if ms[p] == 3]
    n_tern = len(ternary)
    results = []
    for trans_bits in range(1 << n_tern):
        trans_dir = {}
        for p in bins:
            trans_dir[p] = 1
        for idx, p in enumerate(ternary):
            trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1
        configs = [[0]*n]
        for t in range(L):
            c = list(configs[-1])
            p = wl[t]
            c[p] = (c[p] + trans_dir[p]) % ms[p]
            configs.append(c)
        if configs[-1] != configs[0]:
            continue
        config_set = set(tuple(c) for c in configs[:L])
        if len(config_set) != L:
            continue
        results.append((trans_dir.copy(), [tuple(c) for c in configs[:L]]))
    return results


def has_any_ec(word, configs, ms, n):
    L = len(word)
    for j in range(n):
        mt = set()
        nmt = set()
        for t in range(L):
            c = configs[t]
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if word[t] == j:
                mt.add(triple)
            else:
                nmt.add(triple)
        if mt & nmt:
            return True
    return False


def classify_word(word, n):
    """Classify mover word structure."""
    L = len(word)
    # Direction at each step
    dirs = []
    for i in range(L):
        nxt = word[(i+1)%L]
        cur = word[i]
        diff = (nxt - cur) % n
        if diff == 1:
            dirs.append(+1)
        elif diff == n-1:
            dirs.append(-1)
        else:
            dirs.append(0)

    # Find runs of same direction
    runs = []
    i = 0
    while i < L:
        d = dirs[i]
        count = 1
        while i + count < L and dirs[(i + count) % L] == d:
            count += 1
        runs.append((d, count))
        i += count

    # Count turnarounds
    turnarounds = 0
    for i in range(len(runs)):
        if runs[i][0] != runs[(i+1)%len(runs)][0]:
            turnarounds += 1

    # Is it a uniform sweep? (exactly 2 runs: one CW, one CCW)
    uniform = (len(runs) == 2 and
               set(r[0] for r in runs) == {1, -1})

    # Is it a single-wiggle? (4 runs: CW, CCW stutter, CW stutter, CCW)
    # or some specific pattern
    is_wiggle = (len(runs) == 4 or len(runs) == 6)

    return {
        'runs': runs,
        'n_runs': len(runs),
        'turnarounds': turnarounds,
        'uniform': uniform,
        'is_wiggle': is_wiggle,
        'displacement': total_displacement(list(word), n),
    }


def check_mnu_full(word, configs, ms, n):
    """Check full MNU: at each proc, mover triples disjoint from non-mover triples.
    This is equivalent to checking that there's NO entry conflict.
    Returns True if MNU holds (no EC)."""
    L = len(word)
    for j in range(n):
        mt = set()
        nmt = set()
        for t in range(L):
            c = configs[t]
            triple = (c[(j-1)%n], c[j], c[(j+1)%n])
            if word[t] == j:
                mt.add(triple)
            else:
                nmt.add(triple)
        if mt & nmt:
            return False  # MNU fails
    return True  # MNU holds


def check_waterfall_forced_entries(word, configs, ms, n):
    """
    Check whether forced entries from the waterfall structure produce an EC.

    Waterfall: the shadow cycle construction forces certain entries in the
    transition table. If two forced entries at the same (L,S,R) require
    different outputs, that's a contradiction.

    For the proved shadow theorem, the key is:
    - Each config c in the good cycle determines f_p(L,S,R) for the mover p
    - Shadow config c' = sigma(c) determines f_p(L',S',R') for the mover
    - If (L,S,R) = (L',S',R') but the required output differs: contradiction

    Let me check: for each binary proc b, what entries are forced?
    When b fires: f_b(L,S,R) = S' (where S' = (S+1) mod 2)
    When b doesn't fire: f_b(L,S,R) = S (stays same)
    These are the EC entries. Since MNU holds, they don't conflict.

    But the SHADOW forces ADDITIONAL entries. If we shift config c by
    flipping two binary procs b1, b2: the shadow config c' has different
    values at b1 and b2. At the shadow, the mover p fires with context
    that includes b1 or b2's flipped value. This adds NEW entries to
    f_p's table. If any new entry conflicts with an existing one: contradiction.

    This is the SHADOW ENTRY CONFLICT: the combined good + shadow cycles
    force conflicting transition table entries, even though the good cycle
    alone has no EC.
    """
    L = len(word)
    bins = sorted(p for p in range(n) if ms[p] == 2)
    config_set = set(configs)

    # Find the best non-adjacent pair
    best_pair = None
    for i in range(len(bins)):
        for j in range(i+1, len(bins)):
            b1, b2 = bins[i], bins[j]
            if abs(b1-b2) % n in (1, n-1):
                continue
            offset_map = {b1: 1, b2: 1}
            shadow = []
            for c in configs:
                sc = list(c)
                for p2 in offset_map:
                    sc[p2] = (sc[p2] + 1) % ms[p2]
                shadow.append(tuple(sc))
            shadow_set = set(shadow)
            if len(shadow_set & config_set) == 0 and len(shadow_set) == L:
                best_pair = (b1, b2)
                break
        if best_pair:
            break

    if not best_pair:
        return None, "no_pair"

    b1, b2 = best_pair
    offset_map = {b1: 1, b2: 1}
    shadow = []
    for c in configs:
        sc = list(c)
        for p2 in offset_map:
            sc[p2] = (sc[p2] + 1) % ms[p2]
        shadow.append(tuple(sc))

    # Collect ALL transition table entries from good cycle + shadow
    # For each proc j: entries is a dict (L,S,R) -> set of required outputs
    entries = {j: {} for j in range(n)}

    # Good cycle entries
    for t in range(L):
        p = word[t]
        c = configs[t]
        c_next = configs[(t+1)%L]
        lsr = (c[(p-1)%n], c[p], c[(p+1)%n])
        out = c_next[p]
        if lsr not in entries[p]:
            entries[p][lsr] = set()
        entries[p][lsr].add(('good_mover', out))

        # Non-mover entries: f_j(L,S,R) = S for all j != p
        for j in range(n):
            if j == p:
                continue
            lsr_j = (c[(j-1)%n], c[j], c[(j+1)%n])
            if lsr_j not in entries[j]:
                entries[j][lsr_j] = set()
            entries[j][lsr_j].add(('good_nonmover', c[j]))

    # Shadow cycle entries (same mover word, shifted configs)
    for t in range(L):
        p = word[t]
        sc = shadow[t]
        sc_next = shadow[(t+1)%L]
        lsr = (sc[(p-1)%n], sc[p], sc[(p+1)%n])
        out = sc_next[p]
        if lsr not in entries[p]:
            entries[p][lsr] = set()
        entries[p][lsr].add(('shadow_mover', out))

        for j in range(n):
            if j == p:
                continue
            lsr_j = (sc[(j-1)%n], sc[j], sc[(j+1)%n])
            if lsr_j not in entries[j]:
                entries[j][lsr_j] = set()
            entries[j][lsr_j].add(('shadow_nonmover', sc[j]))

    # Check for conflicts
    conflicts = []
    for j in range(n):
        for lsr, entry_set in entries[j].items():
            required_outputs = set()
            for label, out in entry_set:
                required_outputs.add(out)
            if len(required_outputs) > 1:
                conflicts.append((j, lsr, entry_set))

    return conflicts, best_pair


def main():
    print("RA16f: True Shadow Analysis")
    print("="*70)

    for n in [7, 9]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n = {n}")
        print(f"{'='*70}")

        seen = set()
        all_cases = []
        for nb in range(3, n+1):
            nt = n - nb
            prod = (2**nb) * (3**nt)
            if prod >= threshold:
                continue
            for bin_combo in combinations(range(n), nb):
                bins_set = set(bin_combo)
                ms = [2 if p in bins_set else 3 for p in range(n)]
                if has_3_consecutive_binary(ms):
                    continue
                product = 1
                for m in ms:
                    product *= m
                if product >= threshold:
                    continue
                ms_rotations = [tuple(ms[(r+i)%n] for i in range(n)) for r in range(n)]
                canon_ms = min(ms_rotations)
                if canon_ms not in seen:
                    seen.add(canon_ms)
                    all_cases.append((canon_ms, ms))

        noec_total = 0
        shadow_ec_found = 0
        shadow_ec_not_found = 0
        conflict_proc_types = Counter()

        for canon_ms, ms in all_cases:
            max_len = sum(ms)
            words = enumerate_words_dfs(n, ms, max_len, max_results=50000, timeout=90)
            unique_words = {}
            for w in words:
                c = canonicalize(w)
                if c not in unique_words:
                    unique_words[c] = w

            sweep_words = [w for w in unique_words.values()
                           if total_displacement(list(w), n) is not None
                           and abs(total_displacement(list(w), n)) >= 2*n]

            if not sweep_words:
                continue

            bins = sorted(p for p in range(n) if ms[p] == 2)

            for w in sweep_words:
                # Classify word structure
                wclass = classify_word(w, n)

                for trans_dir, configs in build_configs_all_trans(w, ms, n):
                    if has_any_ec(w, configs, ms, n):
                        continue

                    noec_total += 1

                    # Check waterfall forced entries
                    conflicts, pair = check_waterfall_forced_entries(w, configs, ms, n)

                    if conflicts:
                        shadow_ec_found += 1
                        # Classify conflict procs
                        for j, lsr, entry_set in conflicts:
                            if ms[j] == 2:
                                conflict_proc_types['binary'] += 1
                            else:
                                conflict_proc_types['ternary'] += 1

                        if shadow_ec_found <= 5:
                            print(f"\n  Shadow EC found: ms={list(ms)}, "
                                  f"pair={pair}, word_structure={wclass['n_runs']} runs")
                            print(f"    word={list(w)}")
                            print(f"    {len(conflicts)} conflict(s):")
                            for j, lsr, entry_set in conflicts[:5]:
                                ptype = 'B' if ms[j] == 2 else 'T'
                                print(f"      proc {j} ({ptype}): (L,S,R)={lsr} -> "
                                      f"{sorted(entry_set)}")
                    else:
                        shadow_ec_not_found += 1
                        if shadow_ec_not_found <= 3:
                            print(f"\n  NO shadow EC: ms={list(ms)}, pair={pair}")
                            print(f"    word={list(w)}, trans={trans_dir}")

        print(f"\n{'='*70}")
        print(f"SHADOW EC SUMMARY for n={n}")
        print(f"{'='*70}")
        print(f"Total no-EC cycles: {noec_total}")
        print(f"  Shadow EC found (good+shadow conflict): {shadow_ec_found}")
        print(f"  No shadow EC: {shadow_ec_not_found}")
        print(f"  Conflict proc types: {dict(conflict_proc_types)}")
        if shadow_ec_not_found == 0 and noec_total > 0:
            print(f"\n  *** UNIVERSAL: Shadow EC (good+shadow table conflict) blocks "
                  f"ALL no-EC sweep non-consec cycles ***")


if __name__ == '__main__':
    main()
