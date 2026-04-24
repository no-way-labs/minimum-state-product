"""
Entry conflict analysis for isolated sandwiched ternary pivot at n=9.
ms = (3,3,2,2,3,2,2,3,3), pivot at position 4.

Positions:
  0=ternary, 1=ternary, 2=binary, 3=binary, 4=ternary(pivot),
  5=binary, 6=binary, 7=ternary, 8=ternary

Naming:
  left t = 3, right t = 5
  left²t = 2, right²t = 6
  left³t = 1 (ternary, non-sandwiched)
"""

import random
from itertools import product as iterproduct
from collections import defaultdict

random.seed(42)

ms = (3, 3, 2, 2, 3, 2, 2, 3, 3)
n = len(ms)
PIVOT = 4

def random_transition(ms, n):
    """Random transition function: f[p][(L, S, R)] -> new value for p."""
    f = []
    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n
        table = {}
        for L in range(ms[lp]):
            for S in range(ms[p]):
                for R in range(ms[rp]):
                    table[(L, S, R)] = random.randint(0, ms[p] - 1)
        f.append(table)
    return f

def apply_move(config, p, f):
    """Apply transition at processor p, return new config."""
    c = list(config)
    lp = (p - 1) % n
    rp = (p + 1) % n
    ctx = (c[lp], c[p], c[rp])
    c[p] = f[p][ctx]
    return tuple(c)

def find_good_cycles(f, max_starts=500, max_steps=2000):
    """Find good cycles via central daemon from random starts."""
    cycles = []
    seen_cycle_sets = set()

    total_configs = 1
    for m in ms:
        total_configs *= m

    for _ in range(max_starts):
        config = tuple(random.randint(0, ms[p] - 1) for p in range(n))

        # Run until cycle or timeout
        history = [config]
        config_to_step = {config: 0}

        for step in range(1, max_steps):
            # Central daemon: pick a random enabled processor
            # For finding good cycles, try all possible movers
            # Actually, let's do deterministic: try each processor in order
            # Better: random mover selection
            p = random.randint(0, n - 1)
            new_config = apply_move(config, p, f)

            if new_config in config_to_step:
                cycle_start = config_to_step[new_config]
                cycle_configs = history[cycle_start:]
                cycle_key = frozenset(enumerate(cycle_configs))

                # Check if it's a good cycle (every config appears exactly once in cycle)
                if len(set(cycle_configs)) == len(cycle_configs):
                    # Reconstruct movers
                    movers = []
                    for i in range(len(cycle_configs)):
                        c1 = cycle_configs[i]
                        c2 = cycle_configs[(i + 1) % len(cycle_configs)]
                        # Find which processor changed
                        mover = None
                        for q in range(n):
                            if c1[q] != c2[q]:
                                if mover is not None:
                                    mover = None  # multiple changed - not single mover
                                    break
                                mover = q
                        if mover is None:
                            break
                        movers.append(mover)

                    if len(movers) == len(cycle_configs):
                        cycle_id = frozenset(cycle_configs)
                        if cycle_id not in seen_cycle_sets:
                            seen_cycle_sets.add(cycle_id)
                            cycles.append((cycle_configs, movers))
                break

            history.append(new_config)
            config_to_step[new_config] = step
            config = new_config

    return cycles

def find_good_cycles_systematic(f, max_cycles=200):
    """Find good cycles by systematic BFS from each config."""
    cycles = []
    seen = set()

    # Generate all configs
    all_configs = list(iterproduct(*[range(m) for m in ms]))
    random.shuffle(all_configs)

    for start in all_configs[:1000]:
        start = tuple(start)
        # Try random walks
        for _ in range(5):
            config = start
            history = [config]
            config_to_step = {config: 0}

            for step in range(1, 500):
                p = random.randint(0, n - 1)
                new_config = apply_move(config, p, f)

                if new_config == config:
                    # No change, try different mover
                    config = new_config
                    continue

                if new_config in config_to_step:
                    cs = config_to_step[new_config]
                    cycle_configs = history[cs:]

                    if len(set(cycle_configs)) == len(cycle_configs) and len(cycle_configs) >= n:
                        movers = []
                        ok = True
                        for i in range(len(cycle_configs)):
                            c1 = cycle_configs[i]
                            c2 = cycle_configs[(i + 1) % len(cycle_configs)]
                            mover = None
                            for q in range(n):
                                if c1[q] != c2[q]:
                                    if mover is not None:
                                        ok = False
                                        break
                                    mover = q
                            if not ok or mover is None:
                                ok = False
                                break
                            movers.append(mover)

                        if ok:
                            cid = frozenset(cycle_configs)
                            if cid not in seen:
                                seen.add(cid)
                                cycles.append((cycle_configs, movers))
                                if len(cycles) >= max_cycles:
                                    return cycles
                    break

                history.append(new_config)
                config_to_step[new_config] = step
                config = new_config

    return cycles

def fire_count(movers, p):
    return sum(1 for m in movers if m == p)

def find_entry_conflicts(cycle_configs, movers):
    """Find all entry conflicts in a cycle.
    EC at processor q between steps k1, k2:
      - moverAt(k1) = q
      - moverAt(k2) != q
      - config(k1)[left q] = config(k2)[left q]
      - config(k1)[q] = config(k2)[q]
      - config(k1)[right q] = config(k2)[right q]
    """
    L = len(cycle_configs)
    ecs = []  # (q, k1, k2)

    for q in range(n):
        lq = (q - 1) % n
        rq = (q + 1) % n

        # Collect mover steps and non-mover steps for q
        mover_steps = [k for k in range(L) if movers[k] == q]
        nonmover_steps = [k for k in range(L) if movers[k] != q]

        # For each mover step, check against all non-mover steps
        for k1 in mover_steps:
            c1 = cycle_configs[k1]
            triple1 = (c1[lq], c1[q], c1[rq])
            for k2 in nonmover_steps:
                c2 = cycle_configs[k2]
                triple2 = (c2[lq], c2[q], c2[rq])
                if triple1 == triple2:
                    ecs.append((q, k1, k2))

    return ecs

def has_tight_pattern(cycle_configs, movers):
    """Check if pos 2 fires immediately before pos 3 in some segment.
    'Tight left²t -> left t pattern': pos 2 fires at step k, pos 3 fires at step k+1.
    """
    L = len(movers)
    for k in range(L):
        if movers[k] == 2 and movers[(k + 1) % L] == 3:
            return True
    return False

def analyze_ec_source_at_pos2(cycle_configs, movers, ecs_at_2):
    """For ECs at pos 2, check if they come from config[pos 1] revisiting within a pos2-phase."""
    L = len(cycle_configs)
    results = []

    for (q, k1, k2) in ecs_at_2:
        assert q == 2
        c1 = cycle_configs[k1]
        c2 = cycle_configs[k2]
        # Triple: (config[1], config[2], config[3])
        triple = (c1[1], c1[2], c1[3])

        # Find the "phase" of pos 2 that k1 belongs to
        # A phase: consecutive segment where pos 2 doesn't fire between firings
        # k1 is a mover step for pos 2
        # k2 is a non-mover step

        # Check: is k2 in the same "phase" as k1?
        # i.e., between two consecutive firings of pos 2 that bracket k1

        # Find all firing steps of pos 2
        fire_steps = sorted([k for k in range(L) if movers[k] == 2])

        # Find which phase k1 is in
        idx = fire_steps.index(k1)
        phase_start = k1
        if idx + 1 < len(fire_steps):
            phase_end = fire_steps[idx + 1]
        else:
            phase_end = fire_steps[0] + L  # wrap around

        # Is k2 in [phase_start, phase_end)?
        k2_adj = k2 if k2 >= phase_start else k2 + L
        in_phase = phase_start <= k2_adj < phase_end

        # What's the mover at k2?
        mover_at_k2 = movers[k2]

        # Does config[1] (left³t) at k2 equal config[1] at k1?
        # (This is already implied by the EC triple match, since pos 1 is left of pos 2)
        pos1_same = (c1[1] == c2[1])

        results.append({
            'k1': k1, 'k2': k2,
            'triple': triple,
            'mover_at_k2': mover_at_k2,
            'in_same_phase': in_phase,
            'pos1_revisit': pos1_same,
        })

    return results

# Main analysis
print("=" * 70)
print("Entry Conflict Analysis: Sandwiched Ternary Pivot at n=9")
print("ms =", ms)
print("Pivot = position 4 (ternary)")
print("=" * 70)

NUM_TRIALS = 200
total_cycles = 0
fc2_cycles = 0
tight_cycles = 0
ec_by_proc = defaultdict(int)  # proc -> count of cycles with EC at that proc
ec_count_by_proc = defaultdict(int)  # proc -> total EC count
cycles_with_ec_at_2 = 0
ec_at_2_details = []

# Track: for tight cycles, which procs have EC
tight_ec_by_proc = defaultdict(int)
tight_ec_count_by_proc = defaultdict(int)
tight_total_ecs = 0

# Also track EC source analysis
ec_source_stats = defaultdict(int)

for trial in range(NUM_TRIALS):
    random.seed(trial * 137 + 42)
    f = random_transition(ms, n)

    cycles = find_good_cycles_systematic(f, max_cycles=50)

    for (cc, movers) in cycles:
        total_cycles += 1

        fc_pivot = fire_count(movers, PIVOT)
        if fc_pivot != 2:
            continue
        fc2_cycles += 1

        tight = has_tight_pattern(cc, movers)
        if not tight:
            continue
        tight_cycles += 1

        # Find all ECs
        ecs = find_entry_conflicts(cc, movers)

        # Classify by processor
        procs_with_ec = set()
        for (q, k1, k2) in ecs:
            ec_count_by_proc[q] += 1
            tight_ec_count_by_proc[q] += 1
            procs_with_ec.add(q)

        for q in procs_with_ec:
            ec_by_proc[q] += 1
            tight_ec_by_proc[q] += 1

        tight_total_ecs += len(ecs)

        # Specifically check pos 2
        ecs_at_2 = [(q, k1, k2) for (q, k1, k2) in ecs if q == 2]
        if ecs_at_2:
            cycles_with_ec_at_2 += 1
            # Analyze source
            details = analyze_ec_source_at_pos2(cc, movers, ecs_at_2)
            for d in details:
                key = f"mover={d['mover_at_k2']},in_phase={d['in_same_phase']}"
                ec_source_stats[key] += 1
            ec_at_2_details.extend(details)

print(f"\nTotal cycles found: {total_cycles}")
print(f"Cycles with fc(pivot=4) = 2: {fc2_cycles}")
print(f"Tight cycles (pos2 fires immediately before pos3): {tight_cycles}")
print()

if tight_cycles == 0:
    print("No tight cycles found. Trying with more trials...")
else:
    print("=" * 50)
    print("EC DISTRIBUTION IN TIGHT CYCLES")
    print("=" * 50)
    print(f"\nTotal ECs across all tight cycles: {tight_total_ecs}")
    print(f"\nBy processor (count of tight cycles with EC at proc):")
    pos_names = {
        0: "pos0 (left⁴t, ternary)",
        1: "pos1 (left³t, ternary)",
        2: "pos2 (left²t, binary)",
        3: "pos3 (left t, binary)",
        4: "pos4 (PIVOT, ternary)",
        5: "pos5 (right t, binary)",
        6: "pos6 (right²t, binary)",
        7: "pos7 (right³t, ternary)",
        8: "pos8 (right⁴t, ternary)",
    }
    for q in range(n):
        count = tight_ec_by_proc.get(q, 0)
        total = tight_ec_count_by_proc.get(q, 0)
        pct = 100.0 * count / tight_cycles if tight_cycles > 0 else 0
        print(f"  {pos_names[q]:35s}: {count:4d}/{tight_cycles} cycles ({pct:5.1f}%), {total:5d} total ECs")

    print(f"\nCycles with EC at left²t (pos 2): {cycles_with_ec_at_2}/{tight_cycles}"
          f" ({100.0*cycles_with_ec_at_2/tight_cycles:.1f}%)")

    print("\n" + "=" * 50)
    print("EC SOURCE ANALYSIS AT POS 2 (left²t)")
    print("=" * 50)
    if ec_source_stats:
        print("\nEC at pos2: non-mover step classification:")
        for key, count in sorted(ec_source_stats.items(), key=lambda x: -x[1]):
            print(f"  {key}: {count}")

        # More detailed: what's the mover at the non-mover step?
        mover_dist = defaultdict(int)
        in_phase_count = 0
        out_phase_count = 0
        for d in ec_at_2_details:
            mover_dist[d['mover_at_k2']] += 1
            if d['in_same_phase']:
                in_phase_count += 1
            else:
                out_phase_count += 1

        print(f"\nMover at the non-mover step (k2) of pos2 EC:")
        for m, c in sorted(mover_dist.items(), key=lambda x: -x[1]):
            print(f"  Mover = {pos_names[m]}: {c}")

        print(f"\nIn same pos2-phase: {in_phase_count}")
        print(f"In different pos2-phase: {out_phase_count}")
    else:
        print("No ECs at pos 2 found.")

# Now let's also look at a few examples in detail
print("\n" + "=" * 50)
print("DETAILED EXAMPLES")
print("=" * 50)

example_count = 0
for trial in range(NUM_TRIALS):
    if example_count >= 3:
        break
    random.seed(trial * 137 + 42)
    f = random_transition(ms, n)
    cycles = find_good_cycles_systematic(f, max_cycles=50)

    for (cc, movers) in cycles:
        if example_count >= 3:
            break
        fc_pivot = fire_count(movers, PIVOT)
        if fc_pivot != 2:
            continue
        if not has_tight_pattern(cc, movers):
            continue

        ecs = find_entry_conflicts(cc, movers)
        if not ecs:
            continue

        example_count += 1
        print(f"\n--- Example {example_count} (trial={trial}) ---")
        print(f"Cycle length: {len(cc)}")
        print(f"Fire counts: {[fire_count(movers, p) for p in range(n)]}")

        # Show mover sequence
        print(f"Mover sequence: {movers}")

        # Show tight pattern location
        L = len(movers)
        for k in range(L):
            if movers[k] == 2 and movers[(k+1) % L] == 3:
                print(f"  Tight: pos2 fires at step {k}, pos3 fires at step {k+1}")

        # Show ECs
        print(f"Entry conflicts ({len(ecs)}):")
        for (q, k1, k2) in ecs:
            c1 = cc[k1]
            c2 = cc[k2]
            lq = (q-1) % n
            rq = (q+1) % n
            print(f"  EC at proc {q} ({pos_names[q].split('(')[1].rstrip(')')}):")
            print(f"    k1={k1} (mover=pos{movers[k1]}={q}), k2={k2} (mover=pos{movers[k2]})")
            print(f"    Triple (L,S,R) = ({c1[lq]},{c1[q]},{c1[rq]})")
            if q == 2:
                print(f"    ** This is EC at left²t! **")
                print(f"    config[left³t=pos1] at k1: {c1[1]}, at k2: {c2[1]} (same={c1[1]==c2[1]})")
                print(f"    Mover at k2: pos{movers[k2]} ({pos_names[movers[k2]].split('(')[1].rstrip(')')})")
