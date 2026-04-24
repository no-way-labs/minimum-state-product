#!/usr/bin/env python3
"""
RA16h: WHY does the Binary Flip EC always work?

Precise mechanism:
  Binary proc b has fc=2. It fires at steps s1 (value 0->1) and s2 (value 1->0).
  After flipping b: shadow fires at s1 (value 1->0) and s2 (value 0->1).

  Key: the FLIPPED mover context at s1 is (L1, 1, R1) and at s2 is (L2, 0, R2).
  In the GOOD cycle, there are steps where b is non-mover with value 1 (between
  the two fires) and with value 0 (before first fire / after second fire).

  Conflict at b: the flipped mover context (L1, 1, R1) matches some good
  non-mover context (L', 1, R') with L1=L', R1=R'.

  WHY does this match happen? Because:
  - b fires at step s1: mover context is (L1, 0, R1)
  - At step s1+1 (next step): b is non-mover, its value is NOW 1 (just fired)
  - The mover at step s1+1 is word[s1+1] = neighbor of b (say b+1)
  - Non-mover context at step s1+1: (configs[s1+1][(b-1)%n], 1, configs[s1+1][(b+1)%n])
  - But configs[s1+1][(b-1)%n] = L1 (b-1 didn't fire at step s1, so same as step s1)
  - And configs[s1+1][(b+1)%n] might differ from R1 (if b+1 fired at step s1... but
    b fired at step s1, so b+1 didn't fire at s1. At step s1+1, b+1 fires.
    So at step s1+1, before b+1 fires: configs[s1+1][(b+1)%n] = R1 still.)

  Wait, configs[t] is the config BEFORE step t's mover fires. So:
  configs[s1] has b at value 0.
  At step s1, b fires: b goes from 0 to 1.
  configs[s1+1] has b at value 1.
  configs[s1+1][(b-1)%n] = same as configs[s1][(b-1)%n] = L1 (b-1 didn't fire)
  configs[s1+1][(b+1)%n] = same as configs[s1][(b+1)%n] = R1 (b+1 didn't fire)

  So: non-mover context at b at step s1+1 is (L1, 1, R1).
  Flipped mover context at s1 is (L1, 1, R1).
  THEY MATCH!

  This means: the flipped mover at step s1 sees exactly (L1, 1, R1),
  and the good non-mover at step s1+1 also sees (L1, 1, R1).
  The good non-mover requires f_b(L1, 1, R1) = 1 (stay).
  The flipped mover requires f_b(L1, 1, R1) -> 0 (fire 1->0).
  CONFLICT!

  Similarly at step s2: flipped mover sees (L2, 0, R2),
  good non-mover at step s2+1 sees (L2, 0, R2). Conflict.

  THIS IS THE MECHANISM. It's purely structural:
  "The step right after a binary proc fires always has the same
   L,R neighbors (because the firing only changes S, not L or R),
   so the flipped shadow mover context matches the good non-mover context."

  But wait -- this mechanism depends on the shifted binary b's neighbors
  NOT being other shifted binary procs (otherwise L or R would also flip).
  This is why we need NON-ADJACENT pairs: the shift at b1 doesn't
  affect b's neighbors, so the L,R values stay the same.

  The non-adjacency is ESSENTIAL: if b1 and b2 are adjacent, flipping
  both would change the L or R value at b1, breaking the match.

  Let me verify this precisely.
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


def verify_adjacent_step_mechanism(word, configs, ms, n, b, shifted_bins):
    """Verify the precise 'adjacent step' mechanism.

    For binary b with fc=2, firing at steps s1 and s2:
    - At step s1: b fires, config goes from (L1, 0, R1) to (L1, 1, R1)
    - At step s1+1: b is non-mover, sees context (L1, 1, R1)
      (because neither b-1 nor b+1 was the mover at step s1; b was)
    - Shadow at step s1: b sees (L1_shifted, 1, R1_shifted)
    - If b-1 and b+1 are NOT in shifted_bins: L1_shifted=L1, R1_shifted=R1
    - So shadow mover at s1 sees (L1, 1, R1) = good nonmover at s1+1
    - CONFLICT: f_b(L1,1,R1) must be both 0 (shadow fires) and 1 (good stays)
    """
    L = len(word)
    b_steps = sorted(t for t in range(L) if word[t] == b)
    if len(b_steps) != 2:
        return False, f"fc={len(b_steps)} != 2"

    # Check that b's neighbors are NOT in shifted_bins
    b_left = (b-1) % n
    b_right = (b+1) % n
    if b_left in shifted_bins or b_right in shifted_bins:
        return False, "neighbor shifted"

    results = []
    for s in b_steps:
        s_next = (s + 1) % L

        # Step s: b fires
        mover_ctx = (configs[s][(b-1)%n], configs[s][b], configs[s][(b+1)%n])
        # Step s+1: b is non-mover (the next step has a DIFFERENT mover)
        # Verify: word[s_next] != b
        assert word[s_next] != b, f"word[{s_next}] = {word[s_next]} = b = {b}"

        nonmover_ctx = (configs[s_next][(b-1)%n], configs[s_next][b], configs[s_next][(b+1)%n])

        # The flipped version: S component flips
        flipped_mover_ctx = (mover_ctx[0], 1 - mover_ctx[1], mover_ctx[2])

        # Key check: flipped_mover_ctx == nonmover_ctx?
        match = (flipped_mover_ctx == nonmover_ctx)

        results.append({
            'step': s,
            'mover_ctx': mover_ctx,
            'flipped_mover_ctx': flipped_mover_ctx,
            'nonmover_ctx_at_next': nonmover_ctx,
            'match': match,
        })

    all_match = all(r['match'] for r in results)
    return all_match, results


def main():
    print("RA16h: Adjacent Step Mechanism Verification")
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
        mechanism_works = 0
        mechanism_fails = 0

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

                    # Find non-adjacent pair
                    found = False
                    for i in range(len(bins)):
                        for j in range(i+1, len(bins)):
                            b1, b2 = bins[i], bins[j]
                            if abs(b1-b2) % n in (1, n-1):
                                continue

                            shifted_bins = {b1, b2}
                            # Check mechanism at EACH shifted binary
                            works_at_b1, detail1 = verify_adjacent_step_mechanism(
                                w, configs, ms, n, b1, shifted_bins)
                            works_at_b2, detail2 = verify_adjacent_step_mechanism(
                                w, configs, ms, n, b2, shifted_bins)

                            if works_at_b1 or works_at_b2:
                                mechanism_works += 1
                                found = True

                                if total_noec <= 3:
                                    print(f"\n  Example #{total_noec}: ms={list(ms)}, "
                                          f"shift=({b1},{b2})")
                                    print(f"    word={list(w)}")
                                    if works_at_b1 and isinstance(detail1, list):
                                        print(f"    Mechanism at b={b1}:")
                                        for d in detail1:
                                            print(f"      step {d['step']}: "
                                                  f"mover_ctx={d['mover_ctx']} "
                                                  f"-> flipped={d['flipped_mover_ctx']} "
                                                  f"matches nonmover@{d['step']+1}="
                                                  f"{d['nonmover_ctx_at_next']}: {d['match']}")
                                    if works_at_b2 and isinstance(detail2, list):
                                        print(f"    Mechanism at b={b2}:")
                                        for d in detail2:
                                            print(f"      step {d['step']}: "
                                                  f"mover_ctx={d['mover_ctx']} "
                                                  f"-> flipped={d['flipped_mover_ctx']} "
                                                  f"matches nonmover@{d['step']+1}="
                                                  f"{d['nonmover_ctx_at_next']}: {d['match']}")
                                break
                            else:
                                # Try other pairs
                                pass
                        if found:
                            break

                    if not found:
                        mechanism_fails += 1
                        if mechanism_fails <= 3:
                            print(f"\n  MECHANISM FAILS: ms={list(ms)}, word={list(w)}")
                            for i in range(len(bins)):
                                for j in range(i+1, len(bins)):
                                    b1, b2 = bins[i], bins[j]
                                    if abs(b1-b2) % n in (1, n-1):
                                        continue
                                    shifted_bins = {b1, b2}
                                    _, d1 = verify_adjacent_step_mechanism(
                                        w, configs, ms, n, b1, shifted_bins)
                                    _, d2 = verify_adjacent_step_mechanism(
                                        w, configs, ms, n, b2, shifted_bins)
                                    print(f"    pair ({b1},{b2}): b1 detail={d1}, b2 detail={d2}")

        print(f"\n{'='*70}")
        print(f"ADJACENT STEP MECHANISM for n={n}")
        print(f"{'='*70}")
        print(f"Total no-EC cycles: {total_noec}")
        print(f"  Adjacent step mechanism works: {mechanism_works}")
        print(f"  Mechanism fails: {mechanism_fails}")
        if mechanism_fails == 0 and total_noec > 0:
            print(f"\n  *** ADJACENT STEP MECHANISM IS UNIVERSAL ***")
            print(f"  For each cycle: pick non-adjacent pair (b1, b2).")
            print(f"  At shifted binary b (one of b1, b2):")
            print(f"    Step s (b fires): ctx = (L, S, R)")
            print(f"    Step s+1 (b non-mover): ctx = (L, 1-S, R) [same L,R because b fired]")
            print(f"    Flipped mover at s sees (L, 1-S, R) = non-mover at s+1.")
            print(f"    f_b must output 1-S (fire) AND S (stay). Contradiction.")


if __name__ == '__main__':
    main()
