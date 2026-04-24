#!/usr/bin/env python3
"""binscc_shadow_structure.py — What IS the shadow? Closed-form relationship.

For the 24 overlap-free cycles at n=5 ms=(2,2,2,3,3):
- Good cycle visits 12 configs
- Shadow cycle visits 12 configs
- What's the map between them?

Hypothesis: shadow = complement/flip/shift of good cycle.
"""

from itertools import product as iproduct
from collections import Counter
import sys


def enumerate_mover_words_smart(ms, n, max_length):
    ring_adj = {}
    for p in range(n):
        ring_adj[p] = [(p-1) % n, (p+1) % n]
    results = []
    start_config = tuple(0 for _ in range(n))
    def dfs(word, fire_counts, current_config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and current_config == start_config:
            fair = all(fire_counts[p] > 0 and fire_counts[p] % ms[p] == 0
                       for p in range(n))
            if fair:
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fire_counts[p]) for p in range(n)
                     if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            new_config = list(current_config)
            new_config[nxt] = (new_config[nxt] + 1) % ms[nxt]
            new_config = tuple(new_config)
            new_counts = list(fire_counts)
            new_counts[nxt] += 1
            word.append(nxt)
            dfs(word, new_counts, new_config)
            word.pop()
    for p in range(n):
        first = list(start_config)
        first[p] = (first[p] + 1) % ms[p]
        first = tuple(first)
        dfs([p], [1 if i == p else 0 for i in range(n)], first)
    return results


def find_shadow(ms, n, configs_cycle, mover_word):
    """Find the shadow cycle and return its configs and movers."""
    ell = len(mover_word)

    # Build determined entries
    required = {}
    for i in range(ell):
        c = configs_cycle[i]
        c_next = configs_cycle[(i+1) % ell]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        if len(diffs) != 1:
            return None
        mover = diffs[0]
        Li = c[(mover-1)%n]; Si = c[mover]; Ri = c[(mover+1)%n]
        S_new = c_next[mover]
        key = (mover, Li, Si, Ri)
        if key in required and required[key] != S_new:
            return None  # conflict
        required[key] = S_new
        for j in range(n):
            if j != mover:
                Lj = c[(j-1)%n]; Sj = c[j]; Rj = c[(j+1)%n]
                key2 = (j, Lj, Sj, Rj)
                if key2 in required and required[key2] != Sj:
                    return None  # conflict
                required[key2] = Sj

    # Find shadow cycle
    good_set = set(configs_cycle)
    all_configs = list(iproduct(*[range(m) for m in ms]))
    non_good = [c for c in all_configs if c not in good_set]

    for start in non_good:
        config = start
        visited = {}
        path = []
        for step in range(300):
            if config in good_set:
                break
            if config in visited:
                cycle_start = visited[config]
                shadow_configs = path[cycle_start:]

                # Find shadow movers
                shadow_movers = []
                for i in range(len(shadow_configs)):
                    c = shadow_configs[i]
                    c_next = shadow_configs[(i+1) % len(shadow_configs)]
                    for j in range(n):
                        if c[j] != c_next[j]:
                            shadow_movers.append(j)
                            break

                return shadow_configs, shadow_movers
            visited[config] = step
            path.append(config)
            forced = []
            for j in range(n):
                Lj = config[(j-1)%n]; Sj = config[j]; Rj = config[(j+1)%n]
                key = (j, Lj, Sj, Rj)
                if key in required and required[key] != Sj:
                    forced.append((j, required[key]))
            if not forced:
                break
            moved = False
            for proc, new_val in forced:
                new_config = list(config)
                new_config[proc] = new_val
                new_config = tuple(new_config)
                if new_config not in good_set:
                    config = new_config
                    moved = True
                    break
            if not moved:
                break

    return None


def main():
    n = 5
    ms = [2, 2, 2, 3, 3]
    print("=" * 70)
    print(f"SHADOW STRUCTURE ANALYSIS: n={n} ms={tuple(ms)}")
    print("=" * 70)

    max_len = 3 * n + 6
    words = enumerate_mover_words_smart(ms, n, max_len)

    # Find overlap-free, P1-free cycles
    target_cycles = []
    for word in words:
        ell = len(word)
        configs = [tuple(0 for _ in range(n))]
        for i in range(ell):
            p = word[i]
            c = list(configs[-1])
            c[p] = (c[p] + 1) % ms[p]
            configs.append(tuple(c))
        if configs[-1] != configs[0]:
            continue
        if len(set(configs[:ell])) != ell:
            continue
        fire_counts = [0] * n
        for p in word:
            fire_counts[p] += 1
        valid = True
        for p in range(n):
            if fire_counts[p] == 0 or fire_counts[p] % ms[p] != 0:
                valid = False
                break
        if not valid:
            continue
        for i in range(ell):
            p1 = word[i]
            p2 = word[(i+1) % ell]
            diff = abs(p1 - p2)
            if diff != 1 and diff != n - 1:
                valid = False
                break
        if not valid:
            continue

        # P1 overlap check
        p1_mover = set()
        p1_nonmover = set()
        for i in range(ell):
            v = (configs[i][0], configs[i][1], configs[i][2])
            if word[i] == 1:
                p1_mover.add(v)
            else:
                p1_nonmover.add(v)
        if p1_mover & p1_nonmover:
            continue

        # Full overlap check
        any_overlap = False
        for p in range(n):
            mover_ctx = set()
            nonmover_ctx = set()
            for i in range(ell):
                c = configs[i]
                ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
                if word[i] == p:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)
            if mover_ctx & nonmover_ctx:
                any_overlap = True
                break
        if any_overlap:
            continue

        target_cycles.append((word, configs[:ell]))

    print(f"\n{len(target_cycles)} fully overlap-free, P1-free cycles")

    # Analyze each shadow
    for idx, (word, good_configs) in enumerate(target_cycles[:6]):
        result = find_shadow(ms, n, good_configs, word)
        if result is None:
            print(f"\nCycle {idx}: {word} — NO SHADOW (unexpected!)")
            continue

        shadow_configs, shadow_movers = result
        ell = len(word)

        print(f"\nCycle {idx}: {word}")
        print(f"  Good cycle ({ell} configs):")
        for i, c in enumerate(good_configs):
            print(f"    {i:2d}: {c}  mover={word[i]}")

        print(f"  Shadow cycle ({len(shadow_configs)} configs):")
        for i, c in enumerate(shadow_configs):
            print(f"    {i:2d}: {c}  mover={shadow_movers[i]}")

        # Find transformation between good and shadow
        print(f"\n  Config-level relationships:")

        # Check: is shadow a constant shift of good?
        for shift_vec in iproduct(*[range(m) for m in ms]):
            shifted = [tuple((g[j] + shift_vec[j]) % ms[j] for j in range(n))
                       for g in good_configs]
            if set(shifted) == set(shadow_configs):
                print(f"  ★ Shadow = good + {shift_vec} (mod ms)!")
                # Find the permutation
                shadow_set = list(shadow_configs)
                for i, s in enumerate(shifted):
                    shadow_idx = shadow_set.index(s)
                    if i < 4:
                        print(f"    good[{i}]={good_configs[i]} + {shift_vec} = {s} = shadow[{shadow_idx}]")
                break
        else:
            # Check componentwise transformations
            print(f"  No simple additive shift found")

            # Check: per-component relationship
            good_set = set(good_configs)
            shadow_set = set(shadow_configs)

            # For each component, what values appear?
            for j in range(n):
                g_vals = sorted(set(c[j] for c in good_configs))
                s_vals = sorted(set(c[j] for c in shadow_configs))
                print(f"    Component {j} (m={ms[j]}): good={g_vals}, shadow={s_vals}")

        # Check mover word relationship
        good_mover = tuple(word)
        shadow_mover = tuple(shadow_movers)
        print(f"\n  Mover words:")
        print(f"    Good:   {good_mover}")
        print(f"    Shadow: {shadow_mover}")

        # Check if shadow mover is a rotation or permutation of good mover
        for rot in range(ell):
            rotated = tuple(good_mover[(i + rot) % ell] for i in range(ell))
            if rotated == shadow_mover:
                print(f"    ★ Shadow mover = rotation by {rot} of good mover!")
                break
        else:
            # Check if there's a processor permutation
            # I.e., σ such that shadow_mover[i] = σ(good_mover[(i+rot)%ell])
            for rot in range(ell):
                rotated_good = [good_mover[(i + rot) % ell] for i in range(ell)]
                # Find σ from rotated_good to shadow_mover
                sigma = {}
                consistent = True
                for i in range(ell):
                    g = rotated_good[i]
                    s = shadow_mover[i]
                    if g in sigma:
                        if sigma[g] != s:
                            consistent = False
                            break
                    else:
                        sigma[g] = s
                if consistent and len(set(sigma.values())) == len(sigma):
                    print(f"    ★ Shadow mover = σ(rotation by {rot} of good mover)")
                    print(f"      σ = {sigma}")
                    break
            else:
                print(f"    No simple rotation/permutation relationship found")

    sys.stdout.flush()


if __name__ == "__main__":
    main()
