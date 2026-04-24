#!/usr/bin/env python3
"""Route B: Can a long-arc walk exist in a ¬EC good cycle at n=9?

Strategy: Try to CONSTRUCT a ¬EC cycle with a mixed phase at n=9.
If we can't construct one after exhaustive attempts, that's strong evidence.
If we CAN construct one, that disproves the approach.

Also: enumerate properties of ¬EC cycles found at n=9.
- What are the phase structures?
- What is the max consecutive-adjacent walk length avoiding t?
- What processor firing patterns occur?

Key insight: under ¬EC, for binary processor p, the boundary triple
at p at mover steps and non-mover steps partition the triple space.
Binary p has at most m_L × 2 × m_R triples total.
So |mover_triples| + |non_mover_triples| ≤ m_L × 2 × m_R.
Each mover step's triple is in mover_triples, each non-mover step's
in non_mover_triples. Triples CAN repeat within mover/non-mover sets.
"""
import random
from itertools import product as iterproduct
from collections import Counter

random.seed(123)

def ring_dist(a, b, n):
    return min((a - b) % n, (b - a) % n)

def has_entry_conflict(configs, movers, n, ms):
    CL = len(configs)
    for p in range(n):
        mover_triples = set()
        nonmover_triples = set()
        for k in range(CL):
            L = configs[k][(p-1)%n]
            S = configs[k][p]
            R = configs[k][(p+1)%n]
            triple = (L, S, R)
            if movers[k] == p:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)
        if mover_triples & nonmover_triples:
            return True
    return False

def analyze_noec_cycle(configs, movers, n, ms):
    """Detailed analysis of a ¬EC cycle."""
    CL = len(movers)
    info = {
        'CL': CL,
        'fire_counts': {},
        'all_adj': True,
        'phases': [],
        'mixed_phases': 0,
    }

    for p in range(n):
        info['fire_counts'][p] = sum(1 for m in movers if m == p)

    for k in range(CL):
        if ring_dist(movers[k], movers[(k+1) % CL], n) > 1:
            info['all_adj'] = False

    # Analyze phases for each ternary processor with binary neighbors
    for t in range(n):
        lt, rt = (t-1)%n, (t+1)%n
        if ms[t] < 3 or ms[lt] != 2 or ms[rt] != 2:
            continue
        fires = [k for k in range(CL) if movers[k] == t]
        F = len(fires)
        if F < 1:
            continue
        for idx in range(F):
            s = fires[idx]
            prev = fires[(idx-1) % F]
            if prev < s:
                pm = movers[prev+1:s]
            else:
                pm = movers[prev+1:] + movers[:s]
            J = sum(1 for m in pm if m == lt)
            K = sum(1 for m in pm if m == rt)
            phase_data = {
                't': t, 'J': J, 'K': K,
                'len': len(pm),
                'movers': pm[:20],
                'distinct_movers': len(set(pm)),
            }
            info['phases'].append(phase_data)
            if J >= 1 and K >= 1:
                info['mixed_phases'] += 1

    return info

def search_noec_cycles(n, ms, num_trials=3000000):
    noec_cycles = []

    for trial in range(num_trials):
        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        history = [config]
        history_movers = []
        config_to_step = {config: 0}

        for step in range(5000):
            privs = [i for i in range(n)
                     if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
            if not privs:
                break
            p = random.choice(privs)
            nc = list(config)
            nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
            config = tuple(nc)

            if config in config_to_step:
                cs = config_to_step[config]
                cycle_configs = history[cs:]
                cycle_movers = history_movers[cs:] + [p]
                CL = len(cycle_configs)

                if CL >= n:
                    ec = has_entry_conflict(cycle_configs, cycle_movers, n, ms)
                    if not ec:
                        info = analyze_noec_cycle(cycle_configs, cycle_movers, n, ms)
                        noec_cycles.append(info)
                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

        if trial % 500000 == 499999:
            print(f"  ... {trial+1} trials, {len(noec_cycles)} ¬EC cycles found")

    return noec_cycles

# Main analysis
print("=" * 70)
print("Route B: Long-arc analysis at n=9")
print("=" * 70)

multisets = [
    [2,2,2,3,3,3,3,3,3],  # 3 consecutive binary
    [2,3,2,3,2,3,3,3,3],  # 3 non-consecutive binary
    [3,2,3,2,3,3,3,2,3],  # 3 non-consecutive binary (different arrangement)
]

for ms in multisets:
    n = len(ms)
    print(f"\nn={n} ms={ms}")
    cycles = search_noec_cycles(n, ms, 3000000)
    print(f"  Total ¬EC cycles: {len(cycles)}")

    if cycles:
        mixed_total = sum(c['mixed_phases'] for c in cycles)
        print(f"  Total mixed phases across all cycles: {mixed_total}")

        # Summarize phase structures
        jk_counts = Counter()
        for c in cycles:
            for p in c['phases']:
                jk_counts[(p['J'], p['K'])] += 1

        print(f"  Phase (J,K) distribution:")
        for (j,k), cnt in sorted(jk_counts.items()):
            label = "MIXED" if j>=1 and k>=1 else ""
            print(f"    J={j}, K={k}: {cnt} {label}")

        # Show details of first few cycles
        for i, c in enumerate(cycles[:5]):
            print(f"\n  Cycle {i}: CL={c['CL']}, all_adj={c['all_adj']}")
            print(f"    fire_counts: {dict(c['fire_counts'])}")
            for p in c['phases']:
                label = "***MIXED***" if p['J']>=1 and p['K']>=1 else ""
                print(f"    phase t={p['t']}: J={p['J']} K={p['K']} len={p['len']} distinct={p['distinct_movers']} {label}")
                if p['movers']:
                    print(f"      movers: {p['movers']}")

# Also check: what fraction of fire-count budget does a long arc use?
print("\n\nLong-arc budget analysis:")
for ms in multisets:
    n = len(ms)
    product = 1
    for m in ms:
        product *= m
    print(f"  ms={ms}: product={product}, n-2={n-2}")
    print(f"    Long arc per phase: {n-2} movers (+ t-fire = {n-1} per phase)")
    print(f"    With fc(t)=2: {2*(n-1)} fires = {2*(n-1)*100/product:.1f}% of product")
    print(f"    With fc(t)=3: {3*(n-1)} fires = {3*(n-1)*100/product:.1f}% of product")
