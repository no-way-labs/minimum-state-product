"""
Information-Theoretic Analysis of Self-Stabilizing Token Ring Threshold

Investigates whether M_n = 4·3^(n-2) (n≥9) / 32·3^(n-4) (n=5..8) has a
Shannon-capacity interpretation.

Parts:
1. Table capacity measurement
2. Self-stabilization probability via random sampling
3. Fan-out analysis (configs per local pattern)
4. Capacity per processor type
5. Entropy of privilege structure
"""

import math
import itertools
import random
from collections import defaultdict
from typing import List, Tuple

random.seed(42)

# ============================================================
# Part 1: Table Capacity
# ============================================================

def table_capacity(ms):
    """Compute total table capacity in bits for state vector ms."""
    n = len(ms)
    total_bits = 0
    total_entries = 0
    per_proc = []
    for i in range(n):
        L_size = ms[(i-1) % n]
        S_size = ms[i]
        R_size = ms[(i+1) % n]
        entries = L_size * S_size * R_size
        bits_per_entry = math.log2(S_size)
        bits = entries * bits_per_entry
        total_bits += bits
        total_entries += entries
        per_proc.append((entries, bits_per_entry, bits))
    return total_bits, total_entries, per_proc

def log2_total_functions(ms):
    """log2 of the total number of possible transition function combinations."""
    n = len(ms)
    total_log = 0
    for i in range(n):
        L_size = ms[(i-1) % n]
        S_size = ms[i]
        R_size = ms[(i+1) % n]
        entries = L_size * S_size * R_size
        total_log += entries * math.log2(S_size)
    return total_log

def product(ms):
    p = 1
    for m in ms:
        p *= m
    return p


# ============================================================
# Part 2: Random self-stabilization sampling
# ============================================================

def random_transition_table(m_L, m_S, m_R):
    """Generate a random transition table for proc with given neighbor sizes."""
    table = {}
    for L in range(m_L):
        for S in range(m_S):
            for R in range(m_R):
                table[(L, S, R)] = random.randint(0, m_S - 1)
    return table

def make_table_func(table):
    """Convert table dict to callable."""
    def f(L, S, R):
        return table[(L, S, R)]
    return f

def check_self_stabilizing(ms, fs):
    """
    Quick check of self-stabilization properties.
    Returns (is_valid, info_dict).
    """
    n = len(ms)
    P = product(ms)

    # Generate all configs
    configs = list(itertools.product(*(range(m) for m in ms)))

    # Compute privilege sets
    priv_map = {}
    for c in configs:
        priv = []
        for i in range(n):
            L = c[(i-1) % n]
            S = c[i]
            R = c[(i+1) % n]
            if fs[i](L, S, R) != S:
                priv.append(i)
        priv_map[c] = priv

    # Liveness: every config has at least one privileged proc
    dead = [c for c in configs if len(priv_map[c]) == 0]
    if dead:
        return False, {'fail': 'liveness', 'dead': len(dead)}

    # Good configs: exactly one privileged proc
    good = set(c for c in configs if len(priv_map[c]) == 1)
    if not good:
        return False, {'fail': 'no_good_configs'}

    # Closure: moves from good configs stay in good configs
    for c in good:
        p = priv_map[c][0]
        c2 = list(c)
        L = c[(p-1) % n]
        S = c[p]
        R = c[(p+1) % n]
        c2[p] = fs[p](L, S, R)
        c2 = tuple(c2)
        if c2 not in good:
            return False, {'fail': 'closure'}

    # Convergence: no cycle of bad configs
    bad = set(c for c in configs if c not in good)
    # Build successor graph for bad configs (check all possible moves)
    # If any bad SCC exists, convergence fails
    # Use iterative reachability: repeatedly remove bad configs that can reach good
    can_reach_good = set()
    frontier = set()

    # Bad configs adjacent to good configs
    for c in bad:
        for p in priv_map[c]:
            c2 = list(c)
            L = c[(p-1) % n]
            S = c[p]
            R = c[(p+1) % n]
            c2[p] = fs[p](L, S, R)
            c2 = tuple(c2)
            if c2 in good:
                can_reach_good.add(c)
                frontier.add(c)
                break

    # BFS backwards: find all bad configs that can reach good
    # Actually, we need forward: for each bad config, check if ALL daemon choices
    # eventually reach good. This is harder — need to check no bad cycle exists.

    # Simpler: check if there's a cycle in the bad config graph under ALL moves
    # A config is "stuck" if some daemon choice keeps it in bad forever
    # Convergence requires: for every bad config, EVERY daemon strategy reaches good

    # Use attractor computation:
    # Level 0: good configs
    # Level k+1: bad configs where EVERY move leads to level ≤ k

    levels = {c: 0 for c in good}
    remaining = set(bad)
    changed = True
    level = 1

    while changed and remaining:
        changed = False
        new_level = set()
        for c in remaining:
            all_reach = True
            for p in priv_map[c]:
                c2 = list(c)
                L = c[(p-1) % n]
                S = c[p]
                R = c[(p+1) % n]
                c2[p] = fs[p](L, S, R)
                c2 = tuple(c2)
                if c2 not in levels:
                    all_reach = False
                    break
            if all_reach:
                new_level.add(c)
                changed = True
        for c in new_level:
            levels[c] = level
            remaining.remove(c)
        level += 1

    if remaining:
        return False, {'fail': 'convergence', 'stuck': len(remaining), 'good': len(good)}

    # Check good cycle visits all processors (fairness)
    # Build good cycle
    good_graph = {}
    for c in good:
        p = priv_map[c][0]
        c2 = list(c)
        L = c[(p-1) % n]
        S = c[p]
        R = c[(p+1) % n]
        c2[p] = fs[p](L, S, R)
        good_graph[c] = (tuple(c2), p)

    # Follow the cycle
    start = next(iter(good))
    visited_procs = set()
    c = start
    for _ in range(len(good) + 1):
        c_next, p = good_graph[c]
        visited_procs.add(p)
        c = c_next
        if c == start:
            break

    if len(visited_procs) < n:
        return False, {'fail': 'fairness', 'visited': len(visited_procs)}

    return True, {'good': len(good), 'levels': level - 1}


def sample_self_stabilization_rate(ms, num_samples=1000):
    """Sample random transition functions and check self-stabilization rate."""
    n = len(ms)
    valid_count = 0
    fail_counts = defaultdict(int)

    for _ in range(num_samples):
        tables = []
        funcs = []
        for i in range(n):
            t = random_transition_table(ms[(i-1)%n], ms[i], ms[(i+1)%n])
            tables.append(t)
            funcs.append(make_table_func(t))

        is_valid, info = check_self_stabilizing(ms, funcs)
        if is_valid:
            valid_count += 1
        else:
            fail_counts[info.get('fail', 'unknown')] += 1

    rate = valid_count / num_samples
    return rate, valid_count, fail_counts


# ============================================================
# Part 3: Fan-out analysis
# ============================================================

def fanout_analysis(ms):
    """Compute fan-out (configs per local pattern) for each processor."""
    n = len(ms)
    P = product(ms)
    fanouts = []
    for i in range(n):
        local_size = ms[(i-1)%n] * ms[i] * ms[(i+1)%n]
        fanout = P / local_size
        fanouts.append(fanout)
    return fanouts


# ============================================================
# Part 4: Entropy of privilege structure
# ============================================================

def privilege_entropy(ms, num_samples=2000):
    """
    For random transition functions, compute:
    - Expected number of privileged procs per config
    - Variance of privilege count
    - Fraction of configs that are "good" (exactly 1 privileged)
    """
    n = len(ms)
    P = product(ms)
    configs = list(itertools.product(*(range(m) for m in ms)))

    results = []
    for _ in range(num_samples):
        tables = []
        funcs = []
        for i in range(n):
            t = random_transition_table(ms[(i-1)%n], ms[i], ms[(i+1)%n])
            tables.append(t)
            funcs.append(make_table_func(t))

        priv_counts = []
        good_count = 0
        for c in configs:
            count = 0
            for i in range(n):
                L = c[(i-1)%n]
                S = c[i]
                R = c[(i+1)%n]
                if funcs[i](L, S, R) != S:
                    count += 1
            priv_counts.append(count)
            if count == 1:
                good_count += 1

        avg_priv = sum(priv_counts) / len(priv_counts)
        results.append((avg_priv, good_count / P))

    avg_priv_mean = sum(r[0] for r in results) / len(results)
    good_frac_mean = sum(r[1] for r in results) / len(results)
    return avg_priv_mean, good_frac_mean


# ============================================================
# Part 5: Information content of convergence routing
# ============================================================

def routing_info_estimate(ms, num_samples=200):
    """
    Estimate routing information by checking how constrained tables are
    for valid systems.

    For each config, the routing choice is: which proc fires?
    For bad configs with k privileged procs, the daemon has k choices.
    Total routing space = product of k_c over bad configs.
    But we need ALL choices to converge, so the actual routing must work
    for the WORST daemon.

    Lower bound on routing info: number of bad configs × log2(expected_priv)
    (each bad config needs at least enough info to guarantee progress)
    """
    n = len(ms)
    P = product(ms)

    # Expected privilege probability per proc
    # For proc i with m_i states, prob(privileged) = 1 - 1/m_i
    # (random table maps (L,S,R) to uniform in {0,...,m_i-1}, prob = S)
    expected_priv_per_proc = [1 - 1/ms[i] for i in range(n)]
    expected_total_priv = sum(expected_priv_per_proc)
    expected_good_frac = 1  # hard to compute exactly

    # For the privilege probability: P(f(L,S,R) = S) = 1/m_i
    # So P(f(L,S,R) != S) = (m_i-1)/m_i
    # For a config to be good (exactly 1 privileged):
    # Sum over i of P(only i privileged) = Sum_i [(m_i-1)/m_i * Prod_{j!=i} 1/m_j]

    good_prob = 0
    for i in range(n):
        p = (ms[i]-1)/ms[i]
        for j in range(n):
            if j != i:
                p *= 1/ms[j]
        good_prob += p

    expected_good = P * good_prob
    expected_bad = P - expected_good

    # Minimum information to specify a convergence routing:
    # For each bad config, we need to specify at least that one move leads to progress
    # The minimum is related to the number of distinct "strategies" that work

    # Crude lower bound: each bad config has O(n) choices → need to select right one
    # routing_info ≈ expected_bad × log2(n)  [very rough]

    routing_bits_crude = expected_bad * math.log2(max(2, n))

    return {
        'expected_priv': expected_total_priv,
        'expected_good': expected_good,
        'expected_bad': expected_bad,
        'good_prob': good_prob,
        'routing_bits_crude': routing_bits_crude,
    }


# ============================================================
# Main Analysis
# ============================================================

def analyze_multiset(ms, label="", sample_ss=True, num_ss_samples=500):
    """Full analysis for one multiset."""
    ms = list(ms)
    n = len(ms)
    P = product(ms)

    # Part 1: Table capacity
    cap_bits, total_entries, per_proc = table_capacity(ms)
    log2_funcs = log2_total_functions(ms)

    # Part 3: Fan-out
    fanouts = fanout_analysis(ms)
    avg_fanout = sum(fanouts) / len(fanouts)
    max_fanout = max(fanouts)

    # Part 5: Routing info estimate
    routing = routing_info_estimate(ms)

    print(f"\n{'='*60}")
    print(f"Multiset: {ms}  (n={n}, P={P}) {label}")
    print(f"{'='*60}")

    print(f"\n--- Table Capacity ---")
    print(f"  Total entries:     {total_entries}")
    print(f"  Total capacity:    {cap_bits:.1f} bits")
    print(f"  log2(#functions):  {log2_funcs:.1f}")
    for i, (ent, bpe, b) in enumerate(per_proc):
        print(f"    Proc {i} (m={ms[i]}): {ent} entries × {bpe:.3f} bits = {b:.1f} bits")

    print(f"\n--- Fan-out (configs per local pattern) ---")
    for i, f in enumerate(fanouts):
        local = ms[(i-1)%n] * ms[i] * ms[(i+1)%n]
        print(f"    Proc {i}: {P}/{local} = {f:.1f}")
    print(f"  Average fan-out: {avg_fanout:.1f}")
    print(f"  Max fan-out:     {max_fanout:.1f}")

    print(f"\n--- Privilege/Routing Estimates ---")
    print(f"  E[#privileged]:   {routing['expected_priv']:.2f}")
    print(f"  E[#good configs]: {routing['expected_good']:.1f} ({routing['good_prob']*100:.2f}%)")
    print(f"  E[#bad configs]:  {routing['expected_bad']:.1f}")
    print(f"  Routing info (crude LB): {routing['routing_bits_crude']:.1f} bits")
    print(f"  Capacity / Routing:      {cap_bits / max(1, routing['routing_bits_crude']):.3f}")

    # Part 2: Self-stabilization sampling
    ss_rate = None
    if sample_ss and P <= 500:  # Only feasible for small products
        print(f"\n--- Self-Stabilization Sampling ({num_ss_samples} samples) ---")
        rate, valid, fails = sample_self_stabilization_rate(ms, num_ss_samples)
        ss_rate = rate
        if rate > 0:
            info_bits = -math.log2(rate) if rate > 0 else float('inf')
        else:
            info_bits = float('inf')
        print(f"  Valid systems:     {valid}/{num_ss_samples} = {rate*100:.4f}%")
        print(f"  Info content:      {info_bits:.1f} bits" if info_bits < float('inf') else f"  Info content:      >inf (0 valid)")
        print(f"  Failure breakdown: {dict(fails)}")
        if info_bits < float('inf'):
            print(f"  Capacity/Info:     {cap_bits / info_bits:.3f}")
    elif sample_ss:
        print(f"\n  [Self-stabilization sampling skipped: P={P} too large]")

    return {
        'ms': ms, 'n': n, 'P': P,
        'cap_bits': cap_bits, 'total_entries': total_entries,
        'fanouts': fanouts, 'avg_fanout': avg_fanout,
        'routing': routing, 'ss_rate': ss_rate,
    }


print("="*60)
print("INFORMATION-THEORETIC ANALYSIS OF TOKEN RING THRESHOLD")
print("="*60)

# ============================================================
# n=3: Small enough for exhaustive
# ============================================================
print("\n\n" + "#"*60)
print("# n=3")
print("#"*60)

n3_multisets = [
    ([2,2,2], "product=8, below threshold"),
    ([2,2,3], "product=12"),
    ([2,3,3], "product=18"),
    ([3,3,3], "product=27, Dijkstra Sol3"),
]

for ms, label in n3_multisets:
    analyze_multiset(ms, label, sample_ss=True, num_ss_samples=2000)


# ============================================================
# n=4: feasible for sampling
# ============================================================
print("\n\n" + "#"*60)
print("# n=4")
print("#"*60)

n4_multisets = [
    ([2,2,2,2], "product=16"),
    ([2,2,2,3], "product=24"),
    ([2,2,3,3], "product=36 = threshold 4·3^2"),
    ([2,3,3,3], "product=54"),
    ([3,3,3,3], "product=81, Dijkstra Sol3"),
]

for ms, label in n4_multisets:
    analyze_multiset(ms, label, sample_ss=True, num_ss_samples=2000)


# ============================================================
# n=5: the key test case
# ============================================================
print("\n\n" + "#"*60)
print("# n=5 (M_5 = 96)")
print("#"*60)

n5_multisets = [
    ([2,2,2,2,2], "product=32, well below"),
    ([2,2,2,2,3], "product=48"),
    ([2,2,2,3,3], "product=72"),
    ([2,2,2,3,4], "product=96 = M_5 (THRESHOLD)"),
    ([2,2,3,3,3], "product=108"),
    ([2,3,3,3,3], "product=162"),
    ([3,3,3,3,3], "product=243, Dijkstra Sol3"),
]

for ms, label in n5_multisets:
    feasible = product(ms) <= 300
    analyze_multiset(ms, label, sample_ss=feasible, num_ss_samples=1000 if feasible else 0)


# ============================================================
# Summary table
# ============================================================
print("\n\n" + "="*60)
print("SUMMARY TABLE")
print("="*60)

print(f"\n{'n':>2} {'ms':>20} {'P':>6} {'Cap(bits)':>10} {'Entries':>8} "
      f"{'AvgFanout':>10} {'E[good]':>8} {'Cap/Route':>10}")
print("-" * 90)

all_multisets = []
for n_val, ms_list in [(3, n3_multisets), (4, n4_multisets), (5, n5_multisets)]:
    for ms, label in ms_list:
        ms_l = list(ms)
        P = product(ms_l)
        cap, entries, _ = table_capacity(ms_l)
        fanouts = fanout_analysis(ms_l)
        avg_fo = sum(fanouts)/len(fanouts)
        routing = routing_info_estimate(ms_l)
        ratio = cap / max(1, routing['routing_bits_crude'])
        print(f"{n_val:>2} {str(ms_l):>20} {P:>6} {cap:>10.1f} {entries:>8} "
              f"{avg_fo:>10.1f} {routing['expected_good']:>8.1f} {ratio:>10.3f}")
        all_multisets.append((n_val, ms_l, P, cap, routing, avg_fo))


# ============================================================
# Part 6: Capacity ratio at threshold
# ============================================================
print("\n\n" + "="*60)
print("CAPACITY RATIO AT THRESHOLD vs n")
print("="*60)

print(f"\n{'n':>3} {'Threshold':>10} {'Cap(bits)':>10} {'E[bad]':>10} "
      f"{'Route(crude)':>12} {'Cap/Route':>10} {'bits/config':>12}")
print("-" * 80)

for n_val in range(3, 12):
    if n_val <= 4:
        threshold = 4 * 3**(n_val - 2)
    elif n_val <= 8:
        threshold = 32 * 3**(n_val - 4)
    else:
        threshold = 4 * 3**(n_val - 2)

    # At threshold: ms = (2,3,3,...,3,2) or similar
    # Use ms=(2,3,3,...,3) for simplicity (product = 2·3^(n-1))
    # Actually let's use the known threshold multiset
    if n_val == 3:
        ms_t = [3,3,3]  # product=27
    elif n_val == 4:
        ms_t = [2,2,3,3]  # product=36
    elif n_val == 5:
        ms_t = [2,2,2,3,4]  # product=96
    elif n_val == 6:
        ms_t = [2,2,2,3,3,4]  # product=288? let me check
        # M_6 = 32·3^2 = 288. ms=(2,2,2,3,3,4) → 2·2·2·3·3·4=288. Yes.
        ms_t = [2,2,2,3,3,4] if product([2,2,2,3,3,4]) == 288 else [2]*3 + [3]*2 + [4]
    elif n_val == 7:
        ms_t = [2,2,2,3,3,3,4]  # 2^3·3^3·4 = 8·27·4 = 864 = 32·3^3
    elif n_val == 8:
        ms_t = [2,2,2,3,3,3,3,4]  # 2^3·3^4·4 = 8·81·4 = 2592 = 32·3^4
    else:
        # n>=9: threshold = 4·3^(n-2), use ms=(2,3,...,3,2)
        ms_t = [2] + [3]*(n_val-2) + [2]

    P = product(ms_t)
    cap, entries, _ = table_capacity(ms_t)
    routing = routing_info_estimate(ms_t)
    ratio = cap / max(1, routing['routing_bits_crude'])
    bits_per_config = cap / P

    print(f"{n_val:>3} {threshold:>10} {cap:>10.1f} {routing['expected_bad']:>10.1f} "
          f"{routing['routing_bits_crude']:>12.1f} {ratio:>10.3f} {bits_per_config:>12.4f}")


# ============================================================
# Part 7: Sub-threshold vs at-threshold comparison (n=5)
# ============================================================
print("\n\n" + "="*60)
print("DETAILED n=5 COMPARISON: SUB-THRESHOLD vs THRESHOLD")
print("="*60)

for ms_label in [
    ([2,2,2,2,3], "P=48, sub-threshold"),
    ([2,2,2,3,3], "P=72, sub-threshold"),
    ([2,2,2,3,4], "P=96 = M_5, AT threshold"),
    ([2,2,3,3,3], "P=108, above threshold"),
    ([3,3,3,3,3], "P=243, well above"),
]:
    ms, label = ms_label
    P = product(ms)
    cap, entries, per_proc = table_capacity(ms)
    fanouts = fanout_analysis(ms)
    routing = routing_info_estimate(ms)

    # Bits per config
    bits_per_config = cap / P

    # Bits per bad config
    bits_per_bad = cap / max(1, routing['expected_bad'])

    # "Channel rate" = table capacity / configs that need routing

    print(f"\n  {ms} ({label})")
    print(f"    Capacity:          {cap:.1f} bits")
    print(f"    Configs:           {P}")
    print(f"    E[good]:           {routing['expected_good']:.1f}")
    print(f"    E[bad]:            {routing['expected_bad']:.1f}")
    print(f"    Bits/config:       {bits_per_config:.4f}")
    print(f"    Bits/bad_config:   {bits_per_bad:.4f}")
    print(f"    Avg fanout:        {sum(fanouts)/len(fanouts):.1f}")

    # Key ratio: how many bits of table capacity per bit of routing info
    print(f"    Cap/Routing:       {cap / max(1, routing['routing_bits_crude']):.4f}")


# ============================================================
# Part 8: The REAL bottleneck — table entries vs configs
# ============================================================
print("\n\n" + "="*60)
print("TABLE ENTRIES vs CONFIG SPACE")
print("="*60)

print(f"\n{'n':>3} {'P':>8} {'Entries':>8} {'Entries/P':>10} {'unique_3tuples':>15} {'Coverage':>10}")
print("-" * 65)

for n_val in range(3, 12):
    if n_val <= 4:
        threshold = 4 * 3**(n_val - 2)
    elif n_val <= 8:
        threshold = 32 * 3**(n_val - 4)
    else:
        threshold = 4 * 3**(n_val - 2)

    if n_val == 3: ms_t = [3,3,3]
    elif n_val == 4: ms_t = [2,2,3,3]
    elif n_val == 5: ms_t = [2,2,2,3,4]
    elif n_val == 6: ms_t = [2,2,2,3,3,4]
    elif n_val == 7: ms_t = [2,2,2,3,3,3,4]
    elif n_val == 8: ms_t = [2,2,2,3,3,3,3,4]
    else: ms_t = [2] + [3]*(n_val-2) + [2]

    P = product(ms_t)
    cap, entries, _ = table_capacity(ms_t)

    # Total unique 3-tuples across all procs
    unique_3tuples = sum(ms_t[(i-1)%n_val] * ms_t[i] * ms_t[(i+1)%n_val] for i in range(n_val))

    # Each 3-tuple "covers" P/(L*S*R) configs
    # Total coverage = sum of coverages = n*P (each config counted n times, once per proc)
    coverage = entries / P  # entries = unique_3tuples

    print(f"{n_val:>3} {P:>8} {entries:>8} {coverage:>10.4f} {unique_3tuples:>15} {n_val:>10}")


# ============================================================
# Part 9: Per-proc "capacity density" = bits / (configs covered)
# ============================================================
print("\n\n" + "="*60)
print("CAPACITY DENSITY: bits per config-coverage, n=5")
print("="*60)

for ms_label in [
    ([2,2,2,2,3], "P=48"),
    ([2,2,2,3,3], "P=72"),
    ([2,2,2,3,4], "P=96"),
    ([2,2,3,3,3], "P=108"),
    ([3,3,3,3,3], "P=243"),
]:
    ms, label = ms_label
    P = product(ms)
    n = len(ms)
    cap, entries, per_proc = table_capacity(ms)

    print(f"\n  {ms} ({label})")
    total_density = 0
    for i in range(n):
        ent, bpe, bits = per_proc[i]
        fanout = P / (ms[(i-1)%n] * ms[i] * ms[(i+1)%n])
        # Each table entry for this proc "covers" fanout configs
        # But each entry provides bpe bits of info
        # Density = bits_per_entry / fanout = info contributed per config
        density = bpe / fanout
        total_density += density * ent  # total bits / P effectively
        print(f"    Proc {i} (m={ms[i]}): {ent} entries, fanout={fanout:.0f}, "
              f"bits/entry={bpe:.3f}, density={density:.6f} bits/config")

    # Total density = sum over all procs of (capacity / fanout) per entry
    # = sum_i entries_i * bits_per_entry_i / (P / local_i)
    # = sum_i entries_i * bpe_i * local_i / P ... no that's wrong
    # Actually: total_density = (sum_i bits_i) / P × n ... hmm
    # Let's just compute total cap / P
    print(f"    Total capacity / P = {cap/P:.4f} bits/config")
    print(f"    Total capacity / (P × n) = {cap/(P*n):.6f} bits/config/proc")
