#!/usr/bin/env python3
"""clb_triple_capacity.py — Analyze triple capacity constraints for lower bounds.

For each processor in a good cycle, the set of (L,S,R) triples at mover-positions
must be disjoint from the set at non-mover positions. This limits how many
cycle positions can exist.

Key question: do 2 binary processors create unavoidable capacity violations?
"""

import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from itertools import product as cartesian
from verifier import verify_system

# ============================================================
# Part 1: Build Sol 3 v1 systems and analyze triple usage
# ============================================================

def sol3_v1_rules(ms, n):
    """Sol 3 v1 adaptation."""
    def make_bottom(m0):
        def f(L, S, R):
            if (S + 1) % m0 == R % m0:
                return (S - 1) % m0
            return S
        return f
    def make_top(m_top):
        def f(L, S, R):
            if L % m_top == R % m_top and (L % m_top + 1) % m_top != S:
                return (L % m_top + 1) % m_top
            return S
        return f
    def make_middle(m_i):
        def f(L, S, R):
            if (S + 1) % m_i == L % m_i:
                return L % m_i
            if (S + 1) % m_i == R % m_i:
                return R % m_i
            return S
        return f
    fs = [make_bottom(ms[0])]
    for i in range(1, n - 1):
        fs.append(make_middle(ms[i]))
    fs.append(make_top(ms[n - 1]))
    return fs


def analyze_good_cycle(ms, fs, n):
    """Analyze triple usage in the good cycle."""
    result = verify_system(list(ms), fs)
    if not result.get('valid'):
        return None

    cycle = result['cycle']
    cycle_len = len(cycle)

    # Find mover at each position
    movers = []
    for idx in range(cycle_len):
        c = cycle[idx]
        c_next = cycle[(idx + 1) % cycle_len]
        diffs = [j for j in range(n) if c[j] != c_next[j]]
        assert len(diffs) == 1, f"Multiple movers at step {idx}"
        movers.append(diffs[0])

    # For each processor, collect mover and non-mover triples
    analysis = {}
    for p in range(n):
        mover_triples = set()
        nonmover_triples = set()
        for idx in range(cycle_len):
            c = cycle[idx]
            triple = (c[(p-1)%n], c[p], c[(p+1)%n])
            if movers[idx] == p:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)

        capacity = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
        overlap = mover_triples & nonmover_triples

        analysis[p] = {
            'ms': ms[p],
            'capacity': capacity,
            'mover_triples': len(mover_triples),
            'nonmover_triples': len(nonmover_triples),
            'total_used': len(mover_triples | nonmover_triples),
            'overlap': len(overlap),  # should be 0
            'mover_count': sum(1 for m in movers if m == p),
            'mover_triple_list': sorted(mover_triples),
            'nonmover_triple_list': sorted(nonmover_triples),
        }

    return {
        'cycle_len': cycle_len,
        'movers': movers,
        'analysis': analysis,
        'cycle': cycle,
    }


def print_analysis(name, ms, result):
    """Print triple capacity analysis."""
    if result is None:
        print(f"\n{name}: INVALID SYSTEM")
        return

    n = len(ms)
    print(f"\n{'='*70}")
    print(f"{name}")
    print(f"ms={ms}, product={eval('*'.join(str(m) for m in ms))}")
    print(f"Good cycle length: {result['cycle_len']}")
    print(f"Mover sequence: {result['movers']}")
    print(f"{'='*70}")

    for p in range(n):
        a = result['analysis'][p]
        usage_pct = a['total_used'] / a['capacity'] * 100
        print(f"  P{p} (m={a['ms']}): capacity={a['capacity']}, "
              f"mover={a['mover_triples']}/{a['mover_count']}moves, "
              f"nonmover={a['nonmover_triples']}, "
              f"total={a['total_used']}/{a['capacity']} ({usage_pct:.0f}%), "
              f"overlap={a['overlap']}")


# ============================================================
# Part 2: Run analysis on working and failing systems
# ============================================================

print("PART 1: WORKING WITNESSES — Triple capacity analysis")
print("=" * 70)

# Working witness: n=9, ms=(2,3,3,3,3,3,3,3,3), product 13122
n = 9
ms_work = (2, 3, 3, 3, 3, 3, 3, 3, 3)
fs_work = sol3_v1_rules(list(ms_work), n)
r_work = analyze_good_cycle(ms_work, fs_work, n)
print_analysis("Working: Sol3 v1 at product 13122", ms_work, r_work)

# Working witness: n=5, ms=(2,2,2,3,4), product 96
n5 = 5
ms_n5 = (2, 2, 2, 3, 4)
fs_n5 = sol3_v1_rules(list(ms_n5), n5)
r_n5 = analyze_good_cycle(ms_n5, fs_n5, n5)
# This might not be the right rules for n=5 — let me try the actual n=5 witness
# Actually Sol3 v1 may work at n=5 too
if r_n5:
    print_analysis("Working: Sol3 v1 at n=5, product 96", ms_n5, r_n5)
else:
    print(f"\nSol3 v1 not valid at n=5 ms={ms_n5}")

# Working: all ternary n=9
ms_all3 = (3,) * 9
fs_all3 = sol3_v1_rules(list(ms_all3), 9)
r_all3 = analyze_good_cycle(ms_all3, fs_all3, 9)
print_analysis("Working: Sol3 original at (3^9), product 19683", ms_all3, r_all3)

# ============================================================
# Part 3: Build bounce cycles for 2-binary and analyze
# ============================================================

print("\n\nPART 2: BOUNCE CYCLE CONSTRUCTION + TRIPLE ANALYSIS")
print("=" * 70)

def build_bounce_cycle(ms, n, nb_val=1):
    """Build a simple down-up bounce cycle."""
    config = [0] * n
    cycle = [tuple(config)]
    visited = {tuple(config)}

    # Pattern: down sweep n-1,...,0 then up sweep 1,...,n-1
    base = list(range(n-1, -1, -1)) + list(range(1, n))

    for repeats in range(1, 5):
        config = [0] * n
        cycle = [tuple(config)]
        visited = {tuple(config)}
        full_movers = base * repeats

        for step, mover in enumerate(full_movers):
            config = list(cycle[-1])
            new_val = (config[mover] + 1) % ms[mover]
            config[mover] = new_val
            new_config = tuple(config)

            if new_config in visited and new_config != cycle[0]:
                break

            if new_config == cycle[0]:
                return cycle, full_movers[:step+1]

            visited.add(new_config)
            cycle.append(new_config)

    return None, None


def analyze_bounce_cycle(ms, cycle, movers_seq, n):
    """Analyze triple usage in a bounce cycle (not necessarily a valid system)."""
    cycle_len = len(cycle)

    analysis = {}
    for p in range(n):
        mover_triples = set()
        nonmover_triples = set()
        for idx in range(cycle_len):
            c = cycle[idx]
            triple = (c[(p-1)%n], c[p], c[(p+1)%n])
            if movers_seq[idx] == p:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)

        capacity = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
        overlap = mover_triples & nonmover_triples

        analysis[p] = {
            'ms': ms[p],
            'capacity': capacity,
            'mover_triples': len(mover_triples),
            'nonmover_triples': len(nonmover_triples),
            'total_used': len(mover_triples | nonmover_triples),
            'overlap': len(overlap),
            'mover_count': sum(1 for m in movers_seq if m == p),
        }

    return analysis


# Build bounce cycles for various multisets
test_cases = [
    ((3,)*9, "all ternary"),
    ((2,3,3,3,3,3,3,3,3), "1 binary"),
    ((2,2,3,3,3,3,3,3,3), "2 binary adj"),
    ((2,3,2,3,3,3,3,3,3), "2 binary sep=2"),
    ((2,3,3,2,3,3,3,3,3), "2 binary sep=3"),
    ((2,3,3,3,2,3,3,3,3), "2 binary sep=4"),
    ((2,2,2,3,3,3,3,3,3), "3 binary"),
]

for ms, desc in test_cases:
    n = len(ms)
    cycle, movers = build_bounce_cycle(ms, n)
    if cycle is None:
        print(f"\n{desc} ms={ms}: No bounce cycle found")
        continue

    prod = 1
    for m in ms:
        prod *= m

    analysis = analyze_bounce_cycle(ms, cycle, movers, n)
    print(f"\n{desc} ms={ms}, product={prod}, cycle_len={len(cycle)}")

    for p in range(n):
        a = analysis[p]
        usage = a['total_used'] / a['capacity'] * 100
        print(f"  P{p} (m={a['ms']}): cap={a['capacity']}, "
              f"mover={a['mover_triples']}/{a['mover_count']}moves, "
              f"nonmover={a['nonmover_triples']}, "
              f"used={a['total_used']}/{a['capacity']} ({usage:.0f}%), "
              f"ovlp={a['overlap']}")

    if any(analysis[p]['overlap'] > 0 for p in range(n)):
        print("  *** TRIPLE OVERLAP DETECTED — mutual exclusion impossible! ***")


# ============================================================
# Part 4: Information content analysis
# ============================================================

print("\n\nPART 3: INFORMATION CONTENT — How much does each processor encode?")
print("=" * 70)

if r_work:
    cycle = r_work['cycle']
    cycle_len = len(cycle)
    n = 9
    ms = ms_work

    print(f"\nWorking witness: ms={ms}, cycle_len={cycle_len}")

    for p in range(n):
        # How many distinct states does p take in the cycle?
        states_used = set(c[p] for c in cycle)
        # How many distinct (L,S,R) triples?
        triples_used = set((c[(p-1)%n], c[p], c[(p+1)%n]) for c in cycle)
        # How many distinct (L,R) pairs (context)?
        contexts = set((c[(p-1)%n], c[(p+1)%n]) for c in cycle)

        print(f"  P{p} (m={ms[p]}): states={states_used}, "
              f"#triples={len(triples_used)}/{ms[(p-1)%n]*ms[p]*ms[(p+1)%n]}, "
              f"#contexts={len(contexts)}/{ms[(p-1)%n]*ms[(p+1)%n]}")


# ============================================================
# Part 5: The "binary pair projection" analysis
# ============================================================

print("\n\nPART 4: BINARY PAIR PROJECTION")
print("=" * 70)
print("For 2-binary systems, project good cycle onto the binary pair.")
print("Count how many cycle positions map to each projected state.")

for ms, desc in test_cases:
    n = len(ms)
    cycle, movers = build_bounce_cycle(ms, n)
    if cycle is None:
        continue

    bin_positions = [i for i in range(n) if ms[i] == 2]
    if len(bin_positions) < 2:
        continue

    prod = 1
    for m in ms:
        prod *= m

    # Project onto binary pair
    b1, b2 = bin_positions[0], bin_positions[1]
    projection = {}
    for idx, c in enumerate(cycle):
        key = (c[b1], c[b2])
        if key not in projection:
            projection[key] = []
        projection[key].append(idx)

    print(f"\n{desc} ms={ms}, product={prod}, cycle_len={len(cycle)}")
    print(f"  Binary positions: {b1}, {b2}")
    for key in sorted(projection):
        positions = projection[key]
        mover_at = [movers[i] for i in positions]
        print(f"  ({key[0]},{key[1]}): {len(positions)} positions, "
              f"movers={mover_at}")

    # Check: positions with same binary projection but different movers
    # These must be distinguished by NON-binary processor context
    collisions = 0
    for key, positions in projection.items():
        mover_set = set(movers[i] for i in positions)
        if len(mover_set) > 1:
            collisions += len(positions) - 1
    print(f"  Collision positions (same binary state, different movers): {collisions}")
