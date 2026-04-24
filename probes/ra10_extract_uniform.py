#!/usr/bin/env python3
"""
RA10g: Extract uniform 2n sub-walk from sweep + check shadow applicability.

The sweep cycles have wiggles: CCW-CW pairs that add 2 steps but no displacement.
If we remove these pairs, we get a uniform CW walk of length 2n.

Question: Can the shadow cycle theorem be applied to the extracted 2n-walk,
giving a shadow that contradicts convergence of the ORIGINAL system?

The extraction works at the MOVER WORD level. The configs differ.
We need to check if the shadow construction works on the original configs,
not the extracted configs.

Actually, let me think about this differently.
The shadow construction needs: WaterfallCycle (length 2n, waterfall form).
The original cycle does NOT have waterfall form (it has length 3n-k).

Better approach: prove that sweep + ≥3 binary → ¬converges by showing
that the system has a second good cycle (the shadow). This second cycle
uses the SAME system (same transition function), different config sequence.

The key: the transition function is already determined by the original cycle.
Under this transition function, does a second good cycle exist?

For MNU cycles: the shadow cycle theorem says YES (for uniform sweeps).
For wiggle cycles: the wiggle shadow theorem says YES (for wiggle words).

Let me check: our sweep cycles have MNU. Does MNU + sweep → shadow?
"""
from collections import defaultdict
from itertools import combinations, product as iproduct
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


def enumerate_words_dfs(n, ms, max_results=5000, timeout=60):
    target_cl = sum(ms)
    results = []
    t0 = time.time()

    def dfs(word, fc):
        if time.time() - t0 > timeout or len(results) >= max_results:
            return
        if len(word) == target_cl:
            if all(fc[p] == ms[p] for p in range(n)):
                diff = (word[0] - word[-1]) % n
                if diff in (1, n - 1):
                    results.append(tuple(word))
            return
        remaining = target_cl - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n))
        if needed > remaining:
            return
        last = word[-1]
        for nxt in [(last + 1) % n, (last - 1) % n]:
            if fc[nxt] < ms[nxt]:
                fc[nxt] += 1
                word.append(nxt)
                dfs(word, fc)
                word.pop()
                fc[nxt] -= 1

    for start in range(n):
        if time.time() - t0 > timeout or len(results) >= max_results:
            break
        fc = [0] * n
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


def build_configs(word, n, ms, trans_dir):
    """Build configs from word + transition directions."""
    L = len(word)
    configs = [[0] * n]
    for t in range(L):
        c = list(configs[-1])
        p = word[t]
        c[p] = (c[p] + trans_dir[p]) % ms[p]
        configs.append(c)
    if configs[-1] != configs[0]:
        return None
    if len(set(tuple(c) for c in configs[:L])) != L:
        return None
    return configs[:L]


def extract_uniform_subwalk(word, n):
    """Remove wiggle pairs (CCW followed by CW back) to get uniform walk.
    Returns the indices of steps to KEEP."""
    L = len(word)
    wl = list(word)

    # Identify CCW steps
    steps = []
    for i in range(L):
        nxt = wl[(i + 1) % L]
        cur = wl[i]
        diff = (nxt - cur) % n
        d = 1 if diff == 1 else -1
        steps.append(d)

    # Each CCW step at position i means: step i goes from wl[i] to wl[i]-1 mod n.
    # The NEXT step (i+1) goes back: from wl[i]-1 to wl[i] (CW).
    # Removing both gives a walk that skips from wl[i] directly to wl[(i+2)%L].
    # But wl[i] = wl[(i+2)%L] (since we went back and forth).
    # So the removed steps don't change the walk endpoints.

    # Find pairs to remove: CCW at i, CW at i+1 (the bounce-back)
    remove = set()
    for i in range(L):
        if steps[i] == -1 and steps[(i + 1) % L] == 1:
            remove.add(i)
            remove.add((i + 1) % L)

    keep = [i for i in range(L) if i not in remove]
    return keep


def construct_shadow_configs(n, ms, configs, word, keep_indices):
    """Try to construct shadow configs for the 2n uniform sub-walk.

    The shadow construction for waterfall cycles:
    shadow config s_j has s_j[i] = v_i if i NOT in active interval of j,
    else s_j[i] = 0.

    This is complementary to the original waterfall:
    orig g_j[i] = v_i if i IN active interval, else 0.

    For our configs: can we construct a "shadow" set of configs that:
    1. Has the same length as the original cycle
    2. Forms a valid good cycle under the same transition
    3. Is disjoint from the original configs?

    Actually, let's just check the simpler question:
    Does the shadow construction from the Shadow Cycle Mirror Theorem
    produce valid, disjoint configs?

    The shadow construction:
    - For each config g_j in the original cycle
    - Shadow s_j[i] = 0 if g_j[i] ≠ 0, else s_j[i] = highVal[i]
    - (Complement the waterfall pattern)
    """
    L = len(configs)
    # Compute highVal for each proc: the non-zero value in the cycle
    highVal = [None] * n
    for p in range(n):
        vals = set(configs[t][p] for t in range(L))
        non_zero = [v for v in vals if v != 0]
        if len(non_zero) == 1:
            highVal[p] = non_zero[0]
        elif len(non_zero) == 0:
            highVal[p] = 1  # shouldn't happen
        else:
            highVal[p] = non_zero[0]  # multiple non-zero; take first

    # For binary procs: values are {0, 1}, highVal = 1.
    # For ternary procs with inc: values are {0, 1, 2}, highVal could be 1 or 2.

    # Try shadow: complement each value
    shadow_configs = []
    for t in range(L):
        sc = [0] * n
        for p in range(n):
            if configs[t][p] == 0:
                sc[p] = highVal[p]
            else:
                sc[p] = 0
        shadow_configs.append(tuple(sc))

    # Check disjointness
    orig_set = set(tuple(c) for c in configs)
    shadow_set = set(shadow_configs)
    disjoint = len(orig_set & shadow_set) == 0
    distinct = len(shadow_set) == L

    return shadow_configs, disjoint, distinct


def main():
    print("RA10g: Extract Uniform Sub-walk & Shadow Construction")
    print("=" * 70)

    for n_test, bin_combo in [(7, (0, 1, 4)), (9, (0, 3, 6)), (9, (1, 4, 7))]:
        bins_set = set(bin_combo)
        ms = [2 if p in bins_set else 3 for p in range(n_test)]
        print(f"\nn={n_test}, ms={ms}, bins={list(bin_combo)}")

        words = enumerate_words_dfs(n_test, ms, max_results=100, timeout=10)
        unique = {}
        for w in words:
            c = canonicalize(w)
            if c not in unique:
                unique[c] = w

        sweep_words = [w for w in unique.values()
                       if total_displacement(list(w), n_test) is not None
                       and abs(total_displacement(list(w), n_test)) >= 2 * n_test]

        for w in sweep_words[:1]:
            wl = list(w)
            L = len(wl)
            disp = total_displacement(wl, n_test)
            print(f"\n  word={wl}")
            print(f"  L={L}, disp={disp}")

            # Extract uniform sub-walk
            keep = extract_uniform_subwalk(wl, n_test)
            uniform_word = [wl[i] for i in keep]
            print(f"  Kept {len(keep)} of {L} steps: {keep}")
            print(f"  Uniform word: {uniform_word}")
            print(f"  Uniform disp: {total_displacement(uniform_word, n_test)}")

            # Check: is uniform word actually uniform?
            all_cw = all((uniform_word[(i+1)%len(uniform_word)] - uniform_word[i]) % n_test == 1
                         for i in range(len(uniform_word)))
            print(f"  All CW: {all_cw}")

            # Build configs for ALL transition combos
            ternary = [p for p in range(n_test) if ms[p] == 3]
            found_valid = False

            for trans_bits in range(1 << len(ternary)):
                trans_dir = {p: 1 for p in bins_set}
                for idx, p in enumerate(ternary):
                    trans_dir[p] = 1 if not ((trans_bits >> idx) & 1) else -1

                configs = build_configs(wl, n_test, ms, trans_dir)
                if configs is None:
                    continue

                if not found_valid:
                    found_valid = True
                    print(f"\n  trans_dir={trans_dir}")

                    # Try shadow construction
                    shadow, disjoint, distinct = construct_shadow_configs(
                        n_test, ms, configs, wl, keep)
                    print(f"  Shadow disjoint: {disjoint}")
                    print(f"  Shadow distinct: {distinct} ({len(set(shadow))} unique of {L})")

                    if disjoint and distinct:
                        print(f"  >>> SHADOW WORKS! Two disjoint good cycles → ¬converges <<<")
                    else:
                        # Try simple binary complement
                        print(f"  Shadow doesn't work with simple complement.")
                        print(f"  Try binary-only complement...")

                        # Only flip binary proc values
                        shadow2 = []
                        for t in range(L):
                            sc = list(configs[t])
                            for p in bins_set:
                                sc[p] = 1 - sc[p]  # flip binary
                            shadow2.append(tuple(sc))

                        orig_set = set(tuple(c) for c in configs)
                        shadow2_set = set(shadow2)
                        disj2 = len(orig_set & shadow2_set) == 0
                        dist2 = len(shadow2_set) == L
                        print(f"  Binary-flip shadow disjoint: {disj2}")
                        print(f"  Binary-flip shadow distinct: {dist2} ({len(shadow2_set)} unique)")

                        # Check if shadow configs form a valid cycle under same transitions
                        # i.e., applying the same mover word to shadow configs produces
                        # the same sequence
                        valid_shadow = True
                        for t in range(L):
                            p = wl[t]
                            sc = list(shadow2[t])
                            ctx = (sc[(p-1)%n_test], sc[p], sc[(p+1)%n_test])
                            new_val = (sc[p] + trans_dir[p]) % ms[p]
                            expected = shadow2[(t+1) % L][p]
                            if new_val != expected:
                                valid_shadow = False
                                break
                        print(f"  Binary-flip shadow valid cycle: {valid_shadow}")

                    # Let's also try: build ALL 2^(binary_count) config complements
                    # and check which give disjoint valid cycles
                    print(f"\n  Searching for disjoint companion cycles...")
                    bin_list = sorted(bins_set)
                    n_bin = len(bin_list)

                    for flip_bits in range(1, 1 << n_bin):
                        companion = []
                        for t in range(L):
                            sc = list(configs[t])
                            for idx, p in enumerate(bin_list):
                                if (flip_bits >> idx) & 1:
                                    sc[p] = 1 - sc[p]
                            companion.append(tuple(sc))

                        orig_set = set(tuple(c) for c in configs)
                        comp_set = set(companion)
                        if len(orig_set & comp_set) == 0 and len(comp_set) == L:
                            # Check if companion is valid cycle
                            valid = True
                            for t in range(L):
                                p = wl[t]
                                sc = list(companion[t])
                                new_val = (sc[p] + trans_dir[p]) % ms[p]
                                if new_val != companion[(t+1)%L][p]:
                                    valid = False
                                    break
                                # Also check non-movers don't change
                                for q in range(n_test):
                                    if q != p:
                                        if companion[t][q] != companion[(t+1)%L][q]:
                                            valid = False
                                            break
                                if not valid:
                                    break

                            flipped = [bin_list[idx] for idx in range(n_bin) if (flip_bits >> idx) & 1]
                            if valid:
                                print(f"    Flip {flipped}: VALID disjoint cycle!")
                            elif len(orig_set & comp_set) == 0:
                                pass  # disjoint but not valid

                    break  # just first valid transition combo


if __name__ == '__main__':
    main()
