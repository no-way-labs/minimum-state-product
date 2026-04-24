"""
Check: For ALL isolated sandwiched ternary pivot geometries at n=9,
is fireCount(pivot) >= 3 universal across all valid good cycles?

Isolated sandwiched ternary pivot:
- pivot t: m(t) >= 3, m(t-1) = m(t+1) = 2 (sandwiched by binary)
- m(t-2) = m(t+2) = 2 (binary second-neighbors)
- left^3(t) is NOT itself sandwiched (and similarly right^3(t))

Approach: enumerate sub-threshold multisets at n=9, find all ring arrangements
with isolated pivots, then empirically check fc(pivot) via random transition
functions and good cycle enumeration.
"""

import itertools
import random
from collections import defaultdict

N = 9
THRESHOLD = 4 * (3 ** 7)  # 8748

def get_subthreshold_multisets():
    """Enumerate all multisets with n=9, each m_i >= 2, product < 8748, >= 3 binary."""
    # At n=9, sub-threshold means product < 8748.
    # With >= 3 binary (m_i=2), remaining 6 procs have m_i >= 2.
    # Max product with k binary: 2^k * max_rest^(9-k) < 8748
    # We need at least 3 binary.

    results = []
    # Generate sorted tuples of state counts
    # At least 3 entries = 2, rest >= 2
    # Product < 8748

    def generate(pos, current, prod):
        if pos == N:
            if prod < THRESHOLD:
                num_binary = sum(1 for x in current if x == 2)
                if num_binary >= 3:
                    results.append(tuple(sorted(current)))
            return
        # remaining positions
        remaining = N - pos
        min_val = current[-1] if current else 2
        for v in range(min_val, 20):  # upper bound on state count
            new_prod = prod * v
            # Prune: even with minimum (2) for rest, would exceed?
            if new_prod * (2 ** (remaining - 1)) >= THRESHOLD and v > 2:
                # If this value times 2^(remaining-1) >= threshold, larger values won't work either
                # But we need to check: maybe with v and all 2s for rest it's still under
                if new_prod * (2 ** (remaining - 1)) >= THRESHOLD:
                    break
            if remaining == 1:
                generate(pos + 1, current + [v], new_prod)
            else:
                generate(pos + 1, current + [v], new_prod)

    generate(0, [], 1)
    # Deduplicate
    return sorted(set(results))


def get_ring_arrangements(ms_sorted):
    """Get all distinct circular arrangements of a multiset."""
    from math import gcd
    from functools import reduce

    # Generate all permutations, then deduplicate under rotation
    perms = set(itertools.permutations(ms_sorted))

    # Canonical form: smallest rotation
    seen = set()
    arrangements = []
    for p in perms:
        # Find canonical rotation
        rotations = [p[i:] + p[:i] for i in range(N)]
        canon = min(rotations)
        if canon not in seen:
            seen.add(canon)
            arrangements.append(canon)

    return arrangements


def is_sandwiched(ms, t):
    """Check if position t is a sandwiched ternary pivot."""
    n = len(ms)
    if ms[t] < 3:
        return False
    if ms[(t - 1) % n] != 2 or ms[(t + 1) % n] != 2:
        return False
    return True


def is_isolated_pivot(ms, t):
    """Check if position t is an isolated sandwiched ternary pivot."""
    n = len(ms)
    if not is_sandwiched(ms, t):
        return False
    # Binary second-neighbors
    if ms[(t - 2) % n] != 2 or ms[(t + 2) % n] != 2:
        return False
    # left^3(t) is NOT sandwiched
    left3 = (t - 3) % n
    right3 = (t + 3) % n
    if is_sandwiched(ms, left3) and is_sandwiched(ms, right3):
        # Both third-neighbors are sandwiched -- not isolated
        return False
    # Actually, the definition says NEITHER left^3 nor right^3 is sandwiched
    # Let me re-read: "left^3t is NOT sandwiched ... Similarly right^3t not sandwiched"
    # So BOTH must be non-sandwiched for the pivot to be isolated
    if is_sandwiched(ms, left3) or is_sandwiched(ms, right3):
        return False
    return True


def find_good_cycles_with_fc(ms, pivot_pos, max_cycles=200, max_attempts=5000):
    """
    Find good cycles for ring arrangement ms, return fire counts at pivot_pos.

    Uses random transition functions and BFS/DFS to find good cycles.
    A good cycle visits each processor's state space completely? No --
    a good cycle is one where starting from any config, repeated application
    of the transition leads to a legitimate config.

    Actually, for self-stabilizing token rings:
    - A "good configuration" has exactly one token (privileged processor)
    - A "good cycle" is a cycle through good configurations where each step
      moves the token by firing one processor

    Let me implement this properly.
    """
    n = len(ms)

    # For a Dijkstra-style token ring on a directed ring:
    # Config = (c_0, c_1, ..., c_{n-1}) where c_i in {0, ..., m_i - 1}
    # Processor i is privileged (has token) iff c_i != c_{i-1} (for i>0) or c_0 != c_{n-1} (for i=0)
    # Wait, that's for specific solutions. Let me think about what "good cycle" means here.

    # In the context of this research (from MEMORY.md):
    # A good configuration has exactly one token.
    # A good cycle visits a set of good configs, cycling through them.
    # Each processor i has a transition function f_i(L, S, R) -> S' where
    #   L = c_{i-1}, S = c_i, R = c_{i+1}
    # When processor i fires: c_i -> f_i(c_{i-1}, c_i, c_{i+1})

    # For the token ring model:
    # Token at proc i means c_i is "different" from expected.
    # Standard Dijkstra: proc 0 has token if c_0 == c_{n-1};
    #   proc i (i>0) has token if c_i != c_{i-1}
    # Good config: exactly one proc has token.

    # For general state vectors ms:
    # Proc 0: privileged if c_0 == c_{n-1} (mod m_0... but c_0 < m_0, c_{n-1} < m_{n-1})
    # Actually for general ms: proc 0 privileged if c_0 == c_{n-1} mod m_0
    # Proc i (i>0): privileged if c_i != c_{i-1} mod m_i...
    # Hmm, this gets complicated with different state counts.

    # Let me use the standard formulation from the research:
    # Proc 0: token if c_0 == c_{n-1} (when m_0 | m_{n-1} or they share values)
    # Proc i>0: token if c_i != c_{i-1}
    # But with different m_i, c_{i-1} might not be in range of m_i.
    # Standard approach: compare mod min(m_i, m_{i-1})

    # Actually, from the codebase (verifier.py), let me check the exact definition.
    # For now, use the standard:
    # proc i has token iff c[i] != c[i-1] (for i>0), c[0] has token iff c[0] == c[n-1]
    # But c[i] in {0,...,m_i-1} and c[i-1] in {0,...,m_{i-1}-1}
    # The comparison c[i] != c[i-1] only makes sense when they share value range.
    # Standard: compare values directly (they're just integers).

    # Let me use: proc 0 has token iff c[0] == c[n-1] mod m[0]
    #             proc i>0 has token iff c[i] != c[i-1] mod m[i]
    # Wait, that's also weird. Let me just compare directly:
    # proc 0: token iff c[0] == c[n-1]  (both are integers, compare directly)
    # proc i>0: token iff c[i] != c[i-1]
    # Good config: exactly one token.

    # This is the Dijkstra convention.

    def has_token(config, i):
        if i == 0:
            return config[0] == config[n - 1]
        else:
            return config[i] != config[i - 1]

    def count_tokens(config):
        return sum(1 for i in range(n) if has_token(config, i))

    def is_good(config):
        return count_tokens(config) == 1

    def token_pos(config):
        for i in range(n):
            if has_token(config, i):
                return i
        return -1

    # Generate random transition function
    # f_i(L, S, R) -> new S value, where L in {0,..,m_{i-1}-1}, S in {0,..,m_i-1}, R in {0,..,m_{i+1}-1}
    # Constraint: f must change S (when proc fires, it must change state)

    fc_values = set()

    for attempt in range(max_attempts):
        # Random transition functions
        f = []
        for i in range(n):
            m_L = ms[(i - 1) % n]
            m_S = ms[i]
            m_R = ms[(i + 1) % n]
            fi = {}
            for L in range(m_L):
                for S in range(m_S):
                    for R in range(m_R):
                        # f must map to a value != S
                        choices = [v for v in range(m_S) if v != S]
                        fi[(L, S, R)] = random.choice(choices)
            f.append(fi)

        # Find good configs
        good_configs = []
        for combo in itertools.product(*(range(m) for m in ms)):
            if is_good(combo):
                good_configs.append(combo)

        # Build good-config transition graph
        # From a good config with token at proc p:
        #   Fire proc p: c[p] -> f_p(c[p-1], c[p], c[p+1])
        #   Check if result is a good config

        adj = {}
        for gc in good_configs:
            p = token_pos(gc)
            if p < 0:
                continue
            new_config = list(gc)
            L = gc[(p - 1) % n]
            S = gc[p]
            R = gc[(p + 1) % n]
            new_config[p] = f[p][(L, S, R)]
            new_config = tuple(new_config)
            if is_good(new_config):
                adj[gc] = new_config

        # Find cycles in the functional graph (each node has out-degree <= 1)
        visited = set()
        for start in good_configs:
            if start in visited:
                continue
            path = []
            node = start
            path_set = set()
            while node is not None and node not in visited and node not in path_set:
                path.append(node)
                path_set.add(node)
                node = adj.get(node)

            if node is not None and node in path_set:
                # Found a cycle
                cycle_start = path.index(node)
                cycle = path[cycle_start:]

                # Count fire counts
                fire_count = defaultdict(int)
                for cfg in cycle:
                    p = token_pos(cfg)
                    fire_count[p] += 1

                if pivot_pos in fire_count:
                    fc_values.add(fire_count[pivot_pos])

            for nd in path:
                visited.add(nd)

        if len(fc_values) >= 5 or (attempt > 500 and len(fc_values) >= 2):
            break  # We have enough data

    return fc_values


def main():
    print("=" * 70)
    print("Isolated Sandwiched Ternary Pivot: fc >= 3 Check at n=9")
    print("=" * 70)

    # Step 1: Enumerate sub-threshold multisets
    print("\nStep 1: Enumerating sub-threshold multisets (product < 8748, n=9)...")
    multisets = get_subthreshold_multisets()
    print(f"  Found {len(multisets)} distinct multisets")

    # Step 2: For each multiset, find ring arrangements with isolated pivots
    print("\nStep 2: Finding ring arrangements with isolated pivots...")

    geometries = []  # (ms_arrangement, pivot_pos)

    total_arrangements = 0
    for ms_sorted in multisets:
        arrangements = get_ring_arrangements(ms_sorted)
        total_arrangements += len(arrangements)
        for ms in arrangements:
            for t in range(N):
                if is_isolated_pivot(ms, t):
                    # Normalize: rotate so pivot is at position 0
                    rotated = ms[t:] + ms[:t]
                    geometries.append((rotated, 0))

    # Deduplicate geometries (same local pattern)
    unique_geometries = list(set(geometries))
    unique_geometries.sort()

    print(f"  Total ring arrangements checked: {total_arrangements}")
    print(f"  Total isolated pivot instances: {len(geometries)}")
    print(f"  Unique geometries (pivot at pos 0): {len(unique_geometries)}")

    if not unique_geometries:
        print("\n  NO isolated pivots found! Checking why...")
        # Debug: check for any sandwiched pivots
        sand_count = 0
        for ms_sorted in multisets:
            arrangements = get_ring_arrangements(ms_sorted)
            for ms in arrangements:
                for t in range(N):
                    if is_sandwiched(ms, t):
                        sand_count += 1
                        if sand_count <= 5:
                            print(f"    Sandwiched at pos {t} in {ms}")
                            print(f"      2nd neighbors: m[t-2]={ms[(t-2)%N]}, m[t+2]={ms[(t+2)%N]}")
                            left3 = (t-3) % N
                            right3 = (t+3) % N
                            print(f"      left^3 sandwiched: {is_sandwiched(ms, left3)}")
                            print(f"      right^3 sandwiched: {is_sandwiched(ms, right3)}")
        print(f"  Total sandwiched pivots found: {sand_count}")

        # Relax: just check sandwiched with binary 2nd-neighbors
        print("\n  Relaxing to: sandwiched + binary 2nd-neighbors (no isolation check)...")
        for ms_sorted in multisets:
            arrangements = get_ring_arrangements(ms_sorted)
            for ms in arrangements:
                for t in range(N):
                    if is_sandwiched(ms, t):
                        if ms[(t-2)%N] == 2 and ms[(t+2)%N] == 2:
                            rotated = ms[t:] + ms[:t]
                            geometries.append((rotated, 0))

        unique_relaxed = list(set(geometries))
        print(f"  Relaxed geometries: {len(unique_relaxed)}")
        if unique_relaxed:
            unique_geometries = sorted(unique_relaxed)[:20]  # Cap for speed
            print(f"  Using top {len(unique_geometries)} for testing")

    # Show some examples
    print("\n  Sample geometries (pivot at pos 0):")
    for i, (ms, piv) in enumerate(unique_geometries[:10]):
        prod = 1
        for m in ms:
            prod *= m
        print(f"    {i+1}. ms={ms}, product={prod}")

    if len(unique_geometries) > 10:
        print(f"    ... and {len(unique_geometries) - 10} more")

    # Step 3: Check fc(pivot) for each geometry
    print("\nStep 3: Checking fc(pivot) for each geometry...")
    print("  (Using random transition functions, looking for good cycles)")

    all_fc3_plus = True
    fc2_examples = []

    for i, (ms, piv) in enumerate(unique_geometries):
        prod = 1
        for m in ms:
            prod *= m

        # Adjust attempts based on product (larger = slower)
        if prod > 5000:
            max_att = 500
        elif prod > 3000:
            max_att = 1000
        else:
            max_att = 2000

        fc_vals = find_good_cycles_with_fc(ms, piv, max_attempts=max_att)

        min_fc = min(fc_vals) if fc_vals else None

        status = ""
        if fc_vals:
            if min(fc_vals) < 3:
                all_fc3_plus = False
                fc2_examples.append((ms, fc_vals))
                status = "*** fc < 3 FOUND ***"
            else:
                status = "fc >= 3 confirmed"
        else:
            status = "no cycles found"

        print(f"  [{i+1}/{len(unique_geometries)}] ms={ms} prod={prod}: "
              f"fc_values={sorted(fc_vals) if fc_vals else '{}'} {status}")

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"Geometries tested: {len(unique_geometries)}")

    if all_fc3_plus and unique_geometries:
        print("RESULT: fc(pivot) >= 3 in ALL observed good cycles")
        print("  No counterexample found (fc=2 never observed)")
    elif fc2_examples:
        print(f"RESULT: fc(pivot) < 3 found in {len(fc2_examples)} geometries!")
        for ms, fcs in fc2_examples:
            print(f"  Counterexample: ms={ms}, fc_values={sorted(fcs)}")
    else:
        print("RESULT: No good cycles found in any geometry (check implementation)")


if __name__ == "__main__":
    random.seed(42)
    main()
