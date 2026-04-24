#!/usr/bin/env python3
"""
RA16 FINAL: Complete verification + structural explanation.

THEOREM: Every sweep cycle with non-consecutive binary at sub-threshold
product is blocked. The mechanism is:

(A) Direct EC: the good cycle alone has entry conflict. (Most cycles.)
(B) Shadow EC: for no-EC cycles, flipping a non-adjacent pair of binary
    procs creates a disjoint shadow whose transition table entries
    conflict with the good cycle's entries.

The Shadow EC mechanism works because:
1. Binary proc b fires twice (fc=2) in a sweep, at steps s1 and s2.
2. At step s1: context (L,S,R) with S=0, b fires -> S becomes 1
3. At step s2: context (L',S',R') with S'=1, b fires -> S becomes 0
4. Shifting b flips S at every step: s1 sees S=1, s2 sees S=0
5. The shifted step s1 has context (L,1,R) and the GOOD step s2 has
   context (L',1,R'). If L=L' and R=R': shadow nonmover at s2 sees
   same context as good mover at s2, but requires f_b = 1 (nonmover)
   vs f_b -> 0 (mover). CONFLICT.

This happens when two non-adjacent binary procs are shifted: both
shifts affect the other proc's neighbor context. The non-adjacency
ensures neither shifted proc is the other's direct neighbor, so the
shift only affects TERNARY neighbors' contexts, not the binary procs'
own L,R contexts.

Wait -- actually the binary procs' L,R values DON'T change because
the shifted procs are non-adjacent. But the binary proc's S value
DOES change. So the shifted binary proc sees (L, 1-S, R) instead of
(L, S, R). This means:
- Good: f_b(L, 0, R) = 1 (at step s1, fires 0->1)
- Shadow: f_b(L, 1, R) must also fire (because shadow uses same mover word)
  So f_b(L, 1, R) = 0 (fires 1->0)
- But: somewhere in the good cycle, b is NON-mover with context (L, 1, R)
  At those steps: f_b(L, 1, R) = 1 (stays at 1, non-mover)
- CONFLICT: f_b(L, 1, R) can't be both 0 and 1.

This is THE mechanism. It requires: the context (L, 1, R) appearing
at b as both mover (in shadow) and non-mover (in good).

Let me verify this precise characterization.
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


def verify_binary_flip_mechanism(word, configs, ms, n, b):
    """Verify the precise binary flip EC mechanism at proc b.

    Claim: if b has fc=2, the two mover contexts are (L1,0,R1) and (L2,1,R2).
    After flipping, the shadow mover contexts become (L1,1,R1) and (L2,0,R2).
    If (L1,1,R1) appears as a good non-mover context at b: CONFLICT.
    If (L2,0,R2) appears as a good non-mover context at b: CONFLICT.
    """
    L = len(word)
    b_steps = [t for t in range(L) if word[t] == b]

    if len(b_steps) != 2:
        return {'fc': len(b_steps), 'applies': False}

    # Mover contexts (what b sees when it fires)
    mover_contexts = []
    for t in b_steps:
        c = configs[t]
        ctx = (c[(b-1)%n], c[b], c[(b+1)%n])
        mover_contexts.append(ctx)

    # After flip: S component changes (0<->1)
    flipped_mover_contexts = []
    for L_val, S_val, R_val in mover_contexts:
        flipped_mover_contexts.append((L_val, 1-S_val, R_val))

    # Non-mover contexts at b
    nonmover_contexts = set()
    for t in range(L):
        if word[t] != b:
            c = configs[t]
            ctx = (c[(b-1)%n], c[b], c[(b+1)%n])
            nonmover_contexts.add(ctx)

    # Check: do flipped mover contexts appear in non-mover?
    conflicts = []
    for i, fmc in enumerate(flipped_mover_contexts):
        if fmc in nonmover_contexts:
            conflicts.append({
                'original_mover_ctx': mover_contexts[i],
                'flipped_ctx': fmc,
                'step': b_steps[i],
            })

    return {
        'fc': 2,
        'applies': True,
        'mover_contexts': mover_contexts,
        'flipped_mover_contexts': flipped_mover_contexts,
        'nonmover_contexts': nonmover_contexts,
        'conflicts': conflicts,
    }


def main():
    print("RA16 FINAL: Complete Verification + Binary Flip EC Mechanism")
    print("="*70)

    grand_total_sweeps = 0
    grand_direct_ec = 0
    grand_noec = 0
    grand_shadow_ec = 0
    grand_binary_flip_ec = 0
    grand_no_obstruction = 0

    for n in [5, 7, 9]:
        threshold = 4 * (3 ** (n - 2))
        print(f"\n{'='*70}")
        print(f"n = {n}, threshold = {threshold}")
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

        total_sweeps = 0
        direct_ec = 0
        noec = 0
        shadow_ec_via_pair = 0
        binary_flip_ec = 0
        no_obstruction = 0

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
                    total_sweeps += 1
                    L = len(w)

                    if has_any_ec(w, configs, ms, n):
                        direct_ec += 1
                        continue

                    noec += 1

                    # Try non-adjacent binary pair shift for shadow EC
                    found_shadow = False
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
                            config_set = set(configs)
                            shadow_set = set(shadow)
                            if len(shadow_set & config_set) == 0 and len(shadow_set) == L:
                                # Check if shadow table conflicts with good table
                                has_conflict = False
                                entries = {}
                                for jj in range(n):
                                    entries[jj] = {}
                                for t in range(L):
                                    p = w[t]
                                    c = configs[t]
                                    c_next = configs[(t+1)%L]
                                    lsr = (c[(p-1)%n], c[p], c[(p+1)%n])
                                    if lsr not in entries[p]:
                                        entries[p][lsr] = set()
                                    entries[p][lsr].add(c_next[p])
                                    for jj in range(n):
                                        if jj != p:
                                            lsr_j = (c[(jj-1)%n], c[jj], c[(jj+1)%n])
                                            if lsr_j not in entries[jj]:
                                                entries[jj][lsr_j] = set()
                                            entries[jj][lsr_j].add(c[jj])
                                for t in range(L):
                                    p = w[t]
                                    sc = shadow[t]
                                    sc_next = shadow[(t+1)%L]
                                    lsr = (sc[(p-1)%n], sc[p], sc[(p+1)%n])
                                    if lsr not in entries[p]:
                                        entries[p][lsr] = set()
                                    entries[p][lsr].add(sc_next[p])
                                    for jj in range(n):
                                        if jj != p:
                                            lsr_j = (sc[(jj-1)%n], sc[jj], sc[(jj+1)%n])
                                            if lsr_j not in entries[jj]:
                                                entries[jj][lsr_j] = set()
                                            entries[jj][lsr_j].add(sc[jj])
                                for jj in range(n):
                                    for lsr, outs in entries[jj].items():
                                        if len(outs) > 1:
                                            has_conflict = True
                                            break
                                    if has_conflict:
                                        break

                                if has_conflict:
                                    shadow_ec_via_pair += 1
                                    found_shadow = True

                                    # Check binary flip mechanism
                                    for b in [b1, b2]:
                                        res = verify_binary_flip_mechanism(
                                            w, configs, ms, n, b)
                                        if res['applies'] and res['conflicts']:
                                            binary_flip_ec += 1
                                            break
                                    break
                        if found_shadow:
                            break

                    if not found_shadow:
                        no_obstruction += 1
                        print(f"  NO OBSTRUCTION: ms={list(ms)}, word={list(w)}")

        print(f"\nResults for n={n}:")
        print(f"  Total sweep cycles (all ms, all trans): {total_sweeps}")
        print(f"  Direct EC: {direct_ec}")
        print(f"  No direct EC: {noec}")
        print(f"    Shadow EC (pair shift): {shadow_ec_via_pair}")
        print(f"    Binary Flip EC mechanism: {binary_flip_ec}")
        print(f"    No obstruction found: {no_obstruction}")

        grand_total_sweeps += total_sweeps
        grand_direct_ec += direct_ec
        grand_noec += noec
        grand_shadow_ec += shadow_ec_via_pair
        grand_binary_flip_ec += binary_flip_ec
        grand_no_obstruction += no_obstruction

    print(f"\n{'='*70}")
    print(f"GRAND TOTAL ACROSS ALL n")
    print(f"{'='*70}")
    print(f"Total sweep cycles: {grand_total_sweeps}")
    print(f"  Direct EC: {grand_direct_ec} ({100*grand_direct_ec/max(1,grand_total_sweeps):.1f}%)")
    print(f"  No direct EC: {grand_noec} ({100*grand_noec/max(1,grand_total_sweeps):.1f}%)")
    if grand_noec > 0:
        print(f"    Shadow EC: {grand_shadow_ec} ({100*grand_shadow_ec/max(1,grand_noec):.1f}%)")
        print(f"    Binary Flip EC: {grand_binary_flip_ec} ({100*grand_binary_flip_ec/max(1,grand_noec):.1f}%)")
    print(f"  No obstruction: {grand_no_obstruction}")

    if grand_no_obstruction == 0 and grand_total_sweeps > 0:
        print(f"\n  *** ALL {grand_total_sweeps} sweep cycles blocked ***")
        print(f"  Mechanism split:")
        print(f"    Route 1 (Direct EC): {grand_direct_ec} cycles")
        print(f"    Route 2 (Shadow EC via non-adj binary pair flip): {grand_shadow_ec} cycles")
        print(f"      of which Binary Flip EC applies: {grand_binary_flip_ec}")


if __name__ == '__main__':
    main()
