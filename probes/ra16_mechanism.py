#!/usr/bin/env python3
"""
RA16g: Precise mechanism characterization.

PROVED: Every sweep non-consecutive cycle is blocked by either:
(1) Direct EC (entry conflict within the good cycle alone), OR
(2) Shadow EC (flipping a non-adjacent pair of binary procs creates a
    disjoint shadow that CONFLICTS with the good cycle's transition table)

For (2), the shadow EC pattern at the binary procs is ALWAYS:
  proc b: (L,S,R)=(0,0,0) -> good_mover: 1, shadow_nonmover: 0 (CONFLICT)
  proc b: (L,S,R)=(0,1,0) -> good_nonmover: 1, shadow_mover: 0 (CONFLICT)
  proc b: (L,S,R)=(1,1,1) -> good_mover: 0, shadow_nonmover: 1 (CONFLICT)
  proc b: (L,S,R)=(1,0,1) -> good_nonmover: 0, shadow_mover: 1 (CONFLICT)

This is a symmetric "flip" pattern: the shift swaps the mover/non-mover
roles of the binary proc at these four contexts.

Let me verify:
1. Is this always at one of the SHIFTED binary procs?
2. Is the conflict always these exact 4 triples?
3. What causes it structurally?
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


def analyze_shadow_ec_detail(word, configs, ms, n, b1, b2):
    """Detailed analysis of shadow EC at shifted binary pair (b1, b2)."""
    L = len(word)
    offset_map = {b1: 1, b2: 1}
    shadow = []
    for c in configs:
        sc = list(c)
        for p in offset_map:
            sc[p] = (sc[p] + 1) % ms[p]
        shadow.append(tuple(sc))

    # Collect entries
    entries = {}
    for j in range(n):
        entries[j] = {}

    for t in range(L):
        p = word[t]
        c = configs[t]
        c_next = configs[(t+1)%L]
        lsr = (c[(p-1)%n], c[p], c[(p+1)%n])
        if lsr not in entries[p]:
            entries[p][lsr] = []
        entries[p][lsr].append(('G_mover', c_next[p], t))

        for j in range(n):
            if j == p:
                continue
            lsr_j = (c[(j-1)%n], c[j], c[(j+1)%n])
            if lsr_j not in entries[j]:
                entries[j][lsr_j] = []
            entries[j][lsr_j].append(('G_nonmover', c[j], t))

    for t in range(L):
        p = word[t]
        sc = shadow[t]
        sc_next = shadow[(t+1)%L]
        lsr = (sc[(p-1)%n], sc[p], sc[(p+1)%n])
        if lsr not in entries[p]:
            entries[p][lsr] = []
        entries[p][lsr].append(('S_mover', sc_next[p], t))

        for j in range(n):
            if j == p:
                continue
            lsr_j = (sc[(j-1)%n], sc[j], sc[(j+1)%n])
            if lsr_j not in entries[j]:
                entries[j][lsr_j] = []
            entries[j][lsr_j].append(('S_nonmover', sc[j], t))

    # Find conflicts and characterize
    conflicts_by_proc = {}
    for j in range(n):
        proc_conflicts = []
        for lsr, entry_list in entries[j].items():
            outputs = set(e[1] for e in entry_list)
            if len(outputs) > 1:
                # Conflict! Characterize it
                good_entries = [(role, val, t) for role, val, t in entry_list if role.startswith('G')]
                shadow_entries = [(role, val, t) for role, val, t in entry_list if role.startswith('S')]
                proc_conflicts.append({
                    'lsr': lsr,
                    'good': good_entries,
                    'shadow': shadow_entries,
                })
        if proc_conflicts:
            conflicts_by_proc[j] = proc_conflicts

    return conflicts_by_proc


def main():
    print("RA16g: Mechanism Characterization")
    print("="*70)

    for n in [7]:
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

        noec_count = 0
        binary_conflict_pattern = Counter()
        ternary_conflict_pattern = Counter()
        conflict_at_shifted = 0
        conflict_at_unshifted = 0

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
                for trans_dir, configs in build_configs_all_trans(w, ms, n):
                    if has_any_ec(w, configs, ms, n):
                        continue

                    noec_count += 1
                    config_set = set(configs)
                    L = len(w)

                    # Find working non-adjacent pair
                    for i in range(len(bins)):
                        for j in range(i+1, len(bins)):
                            b1, b2 = bins[i], bins[j]
                            if abs(b1-b2) % n in (1, n-1):
                                continue
                            offset_map = {b1: 1, b2: 1}
                            shadow = []
                            for c in configs:
                                sc = list(c)
                                for p in offset_map:
                                    sc[p] = (sc[p] + 1) % 2
                                shadow.append(tuple(sc))
                            shadow_set = set(shadow)
                            if len(shadow_set & config_set) == 0 and len(shadow_set) == L:
                                # Analyze conflict
                                detail = analyze_shadow_ec_detail(w, configs, ms, n, b1, b2)

                                # Count conflicts at shifted vs unshifted procs
                                shifted = {b1, b2}
                                for proc_j, confs in detail.items():
                                    for conf in confs:
                                        if proc_j in shifted:
                                            conflict_at_shifted += 1
                                        else:
                                            conflict_at_unshifted += 1

                                        # Pattern of the conflict
                                        lsr = conf['lsr']
                                        if ms[proc_j] == 2:
                                            binary_conflict_pattern[lsr] += 1
                                        else:
                                            ternary_conflict_pattern[lsr] += 1

                                # Print first 2 detailed
                                if noec_count <= 2:
                                    print(f"\n  Detail #{noec_count}: ms={list(ms)}, "
                                          f"shift=({b1},{b2}), trans={trans_dir}")
                                    for proc_j in sorted(detail.keys()):
                                        ptype = 'B' if ms[proc_j] == 2 else 'T'
                                        shifted_mark = '*' if proc_j in {b1,b2} else ' '
                                        print(f"    proc {proc_j}{shifted_mark} ({ptype}):")
                                        for conf in detail[proc_j]:
                                            print(f"      (L,S,R)={conf['lsr']}")
                                            for role, val, t in conf['good']:
                                                print(f"        {role}: output={val} at step {t}")
                                            for role, val, t in conf['shadow']:
                                                print(f"        {role}: output={val} at step {t}")

                                break
                        else:
                            continue
                        break

        print(f"\n{'='*70}")
        print(f"MECHANISM DETAIL for n={n}")
        print(f"{'='*70}")
        print(f"Total no-EC cycles analyzed: {noec_count}")
        print(f"Conflicts at shifted binary procs: {conflict_at_shifted}")
        print(f"Conflicts at unshifted procs: {conflict_at_unshifted}")
        print(f"\nBinary conflict patterns (L,S,R):")
        for lsr, cnt in sorted(binary_conflict_pattern.items(), key=lambda x: -x[1]):
            print(f"  {lsr}: {cnt}")
        print(f"\nTernary conflict patterns (L,S,R):")
        for lsr, cnt in sorted(ternary_conflict_pattern.items(), key=lambda x: -x[1]):
            print(f"  {lsr}: {cnt}")


if __name__ == '__main__':
    main()
