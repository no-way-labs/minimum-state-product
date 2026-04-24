#!/usr/bin/env python3
"""
RA16e: Shadow trap mechanism analysis.

FINDING: For no-EC sweep cycles with non-consecutive binary:
- Flipping 1 binary: overlap=4 (not disjoint)
- Flipping 2 non-adjacent binary: disjoint + distinct (SHADOW WORKS)
- Flipping all 3: also disjoint
- Shadow cycle itself has no EC either

The shadow produces 2L configs using L good configs. If ALL 2L configs
must be distinct good configs, but total state space has <4*3^{n-2} configs,
this gives the contradiction.

KEY QUESTION: We need TWO things for the shadow argument:
(A) Shadow configs are disjoint from good configs (CHECKED: yes)
(B) Shadow configs would need to BE good (have exactly 1 privileged proc)
    but they CAN'T all be good (pigeonhole or structural reason)

Actually, the standard shadow cycle argument says:
- Good cycle has L configs
- Shadow cycle has L configs (disjoint from good)
- Both cycles need L configs from the total state space
- So state space needs >= 2L configs
- But L = sum(ms), so need state space >= 2*sum(ms)
- For sweep: L = 2*sum(ms)/... hmm, that's not quite right

Let me think about this differently. The shadow trap says:
The shadow configs must ALL be non-good. If any shadow config were good,
then the system has two separate good cycles, which means the system
can't converge (configs in one cycle never reach the other).

Wait, actually the argument is more subtle. Let me check:
- Can the shadow configs even be in a SECOND good cycle?
- Does the mover word for the shadow cycle use the SAME transition functions?

If the same transition functions are used, and the shadow cycle is a valid
cycle, then:
- Config c is good (in the main cycle) => f_p(L,S,R) != S when p is mover
- Shadow config c' = shift(c) is in the shadow cycle
- At step t: mover p fires on c', the context (L',S',R') is shifted from (L,S,R)
- If the shift only affects procs NOT adjacent to p: (L',S',R') = (L,S,R)
- Then f_p(L,S,R) != S means p IS privileged at c'
- So shadow configs would also have exactly 1 privileged proc
- This would make the shadow a SECOND good cycle
- But two good cycles means convergence fails (can't reach one from the other)

So: the obstruction is that the transition functions can't support both cycles.
The shadow cycle FORCES a contradiction with the transition function.

Let me verify: at the shadow configs, the mover contexts match the original
(because the shifted procs are non-adjacent to the mover). So the shadow
IS a valid cycle under the same transition functions. Having two disjoint
good cycles means ANY system built from this mover word + transition functions
fails convergence. The argument doesn't need EC at all!

Let me verify this computationally.
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


def shadow_with_offset(configs, ms, n, offset_map):
    shadow = []
    for c in configs:
        sc = list(c)
        for p in range(n):
            sc[p] = (sc[p] + offset_map.get(p, 0)) % ms[p]
        shadow.append(tuple(sc))
    return shadow


def verify_shadow_is_valid_cycle(word, configs, shadow_configs, ms, n, trans_dir, shifted_bins):
    """Verify that the shadow cycle is a valid good cycle under the same transitions.

    At each step t: mover = word[t]
    - Original: config = configs[t], mover fires, next = configs[(t+1)%L]
    - Shadow:   config = shadow_configs[t], check if mover is privileged,
                and that firing gives shadow_configs[(t+1)%L]

    The mover at step t fires proc p = word[t].
    Original context: (configs[t][(p-1)%n], configs[t][p], configs[t][(p+1)%n])
    Shadow context:   (shadow_configs[t][(p-1)%n], shadow_configs[t][p], shadow_configs[t][(p+1)%n])

    If shifted_bins are all non-adjacent to p, then L,R are unchanged.
    S is unchanged if p is not in shifted_bins.
    If p IS in shifted_bins: S changes, which could change privileged status.
    """
    L = len(word)
    issues = []

    for t in range(L):
        p = word[t]

        # Original context at proc p
        orig_L = configs[t][(p-1)%n]
        orig_S = configs[t][p]
        orig_R = configs[t][(p+1)%n]

        # Shadow context at proc p
        shad_L = shadow_configs[t][(p-1)%n]
        shad_S = shadow_configs[t][p]
        shad_R = shadow_configs[t][(p+1)%n]

        # Check if context changed
        context_same = (orig_L == shad_L and orig_S == shad_S and orig_R == shad_R)

        # Which of (p-1, p, p+1) are in shifted_bins?
        p_shifted = p in shifted_bins
        L_shifted = (p-1)%n in shifted_bins
        R_shifted = (p+1)%n in shifted_bins

        # The transition function: f_p(L,S,R) -> S'
        # Original: f_p(orig_L, orig_S, orig_R) = next_S != orig_S (privileged)
        # Shadow:   f_p(shad_L, shad_S, shad_R) should also != shad_S

        # If context is the same as original, then:
        #   f_p(L,S,R) = f_p(orig_L, orig_S, orig_R) = next_S != orig_S
        #   Since orig_S = shad_S (if p not shifted), then f_p != shad_S. Privileged.

        # But if p IS shifted: orig_S = 0, shad_S = 1 (or vice versa).
        #   f_p(L,S,R) = orig_next_S. If L,R unchanged:
        #   f_p(L, shad_S, R) might equal shad_S (= 1-orig_S = 1-orig_S)
        #   unless the transition function is different at shad_S.

        # Key: for the shadow to be a valid cycle, we need:
        #   At each step, the mover p fires and produces shadow_configs[(t+1)%L][p]

        # Check: does applying trans_dir at p with shadow context give correct next?
        expected_next = shadow_configs[(t+1)%L][p]
        actual_next = (shad_S + trans_dir[p]) % ms[p]

        if actual_next != expected_next:
            issues.append(('next_mismatch', t, p, shad_S, actual_next, expected_next))

        # Check: is the mover actually privileged? (f_p(L,S,R) != S)
        if actual_next == shad_S:
            issues.append(('not_privileged', t, p, shad_S))

        # Check: are non-movers NOT privileged?
        for q in range(n):
            if q == p:
                continue
            q_L = shadow_configs[t][(q-1)%n]
            q_S = shadow_configs[t][q]
            q_R = shadow_configs[t][(q+1)%n]
            q_next = (q_S + trans_dir[q]) % ms[q]
            if q_next != q_S:
                issues.append(('extra_privileged', t, q, q_S, q_next))

    return issues


def main():
    print("RA16e: Shadow Trap Mechanism")
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

        total_noec = 0
        valid_shadow = 0
        invalid_shadow = 0
        issue_types = Counter()

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

                    total_noec += 1

                    # Find a working non-adjacent pair
                    config_set = set(configs)
                    L = len(w)

                    best_pair = None
                    for i in range(len(bins)):
                        for j in range(i+1, len(bins)):
                            b1, b2 = bins[i], bins[j]
                            # Check non-adjacent
                            if abs(b1-b2) % n in (1, n-1):
                                continue
                            offset_map = {b1: 1, b2: 1}
                            shadow = shadow_with_offset(configs, ms, n, offset_map)
                            shadow_set = set(shadow)
                            if len(shadow_set & config_set) == 0 and len(shadow_set) == L:
                                best_pair = (b1, b2)
                                break
                        if best_pair:
                            break

                    if not best_pair:
                        # Try all-3 shift
                        offset_map = {b: 1 for b in bins}
                        shadow = shadow_with_offset(configs, ms, n, offset_map)
                        shadow_set = set(shadow)
                        if len(shadow_set & config_set) == 0 and len(shadow_set) == L:
                            best_pair = tuple(bins)

                    if not best_pair:
                        print(f"  NO WORKING SHIFT for ms={list(ms)}, word={list(w)}")
                        continue

                    shifted_bins = set(best_pair)
                    offset_map = {b: 1 for b in shifted_bins}
                    shadow = shadow_with_offset(configs, ms, n, offset_map)

                    # Verify shadow is a valid cycle
                    issues = verify_shadow_is_valid_cycle(
                        w, configs, shadow, ms, n, trans_dir, shifted_bins)

                    if not issues:
                        valid_shadow += 1
                    else:
                        invalid_shadow += 1
                        for issue in issues:
                            issue_types[issue[0]] += 1

                        if invalid_shadow <= 3:
                            print(f"\n  Shadow issues for ms={list(ms)}, "
                                  f"shift={sorted(shifted_bins)}:")
                            for issue in issues[:10]:
                                print(f"    {issue}")

        print(f"\n{'='*70}")
        print(f"SHADOW TRAP VERIFICATION for n={n}")
        print(f"{'='*70}")
        print(f"Total no-EC cycles: {total_noec}")
        print(f"  Shadow IS valid second good cycle: {valid_shadow}")
        print(f"  Shadow has issues: {invalid_shadow}")
        print(f"  Issue types: {dict(issue_types)}")

        if valid_shadow == total_noec and total_noec > 0:
            print(f"\n  *** SHADOW TRAP WORKS: shifting a non-adjacent pair of binary "
                  f"procs produces a SECOND valid good cycle, forcing convergence failure. ***")
            print(f"  This means: no valid system can have this good cycle, because")
            print(f"  the shadow cycle is also good under the same transition functions.")


if __name__ == '__main__':
    main()
