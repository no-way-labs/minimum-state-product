"""
RA12: Investigate sorry 5 — odd-parity residual for consecutive binary isolated firings.

Setup:
- 3 consecutive binary processors at positions {i, i+1, i+2}
- p = i+1 (middle binary) has isolated firings (no two consecutive)
- MinFiringGap for p has gap >= 2
- Even parity case: CLOSED by IsolatedParityEC
- Odd parity residual: at least one neighbor has odd prefix fire count change in gap

Questions:
1. How many good cycles fall into the odd-parity residual?
2. Do they all have entry conflict?
3. Where is the EC?
4. Is this case vacuous at n >= 9?
"""

import itertools
from collections import defaultdict

def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))

def privileged_set(config, fs, ms):
    n = len(ms)
    priv = []
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv

def apply_move(config, i, fs, ms):
    n = len(ms)
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    new_s = fs[i](L, S, R)
    lst = list(config)
    lst[i] = new_s
    return tuple(lst)

def find_good_cycles(ms, fs):
    """Find all good cycles for a system."""
    configs = all_configs(ms)
    single_priv = {}
    for c in configs:
        p = privileged_set(c, fs, ms)
        if len(p) == 1:
            single_priv[c] = p[0]

    # Build successor map on single-priv configs
    succ = {}
    for c, p in single_priv.items():
        s = apply_move(c, p, fs, ms)
        if s in single_priv:
            succ[c] = s

    # Find cycles
    visited = set()
    cycles = []
    for start in succ:
        if start in visited:
            continue
        path = []
        cur = start
        path_set = set()
        while cur in succ and cur not in path_set and cur not in visited:
            path.append(cur)
            path_set.add(cur)
            cur = succ[cur]
        if cur in path_set:
            idx = path.index(cur)
            cycle = path[idx:]
            cycles.append(cycle)
            visited.update(cycle)
        visited.update(path)

    return cycles, single_priv

def has_entry_conflict(cycle, single_priv, ms):
    """Check if cycle has entry conflict. Return (bool, location_proc, details)."""
    n = len(ms)
    L = len(cycle)

    # For each proc, collect mover and non-mover contexts
    for p in range(n):
        mover_contexts = set()
        nonmover_contexts = set()
        for idx, c in enumerate(cycle):
            mover = single_priv[c]
            left = c[(p-1) % n]
            self_val = c[p]
            right = c[(p+1) % n]
            ctx = (left, self_val, right)
            if mover == p:
                mover_contexts.add(ctx)
            else:
                nonmover_contexts.add(ctx)

        overlap = mover_contexts & nonmover_contexts
        if overlap:
            return True, p, overlap

    return False, None, None

def get_mover_sequence(cycle, single_priv):
    """Get sequence of movers for a cycle."""
    return [single_priv[c] for c in cycle]

def analyze_isolated_firings(cycle, single_priv, p, ms):
    """
    For processor p in cycle:
    - Check if all firings are isolated (no two consecutive)
    - Find MinFiringGap
    - Check neighbor parity in the gap
    Returns dict with analysis.
    """
    n = len(ms)
    movers = get_mover_sequence(cycle, single_priv)
    L = len(movers)

    # Find firing steps of p
    fire_steps = [k for k in range(L) if movers[k] == p]
    fc = len(fire_steps)

    if fc < 2:
        return {'fc': fc, 'isolated': True, 'skip': True}

    # Check isolation
    isolated = True
    for k in range(len(fire_steps)):
        next_step = (fire_steps[k] + 1) % L
        if movers[next_step] == p:
            isolated = False
            break

    if not isolated:
        return {'fc': fc, 'isolated': False}

    # Find all consecutive firing pairs and their gaps
    pairs = []
    for k in range(len(fire_steps)):
        a = fire_steps[k]
        b = fire_steps[(k+1) % len(fire_steps)]
        if b > a:
            gap = b - a
        else:
            gap = (L - a) + b  # wrap around
        pairs.append((a, b, gap))

    # MinFiringGap: smallest gap (non-wrapping pairs only for simplicity,
    # but we also check wrapping)
    min_gap = min(g for _, _, g in pairs)
    min_pair = [(a, b, g) for a, b, g in pairs if g == min_gap][0]

    if min_gap < 2:
        return {'fc': fc, 'isolated': True, 'min_gap': min_gap, 'skip': True}

    a_step, b_step, gap = min_pair

    # Count neighbor fires in (a, b) exclusive — i.e., steps a+1, a+2, ..., b-1
    left_p = (p - 1) % n
    right_p = (p + 1) % n

    left_fires = 0
    right_fires = 0
    for k in range(a_step + 1, a_step + gap):
        step = k % L
        if movers[step] == left_p:
            left_fires += 1
        if movers[step] == right_p:
            right_fires += 1

    left_parity = left_fires % 2
    right_parity = right_fires % 2

    return {
        'fc': fc,
        'isolated': True,
        'min_gap': min_gap,
        'gap_pair': (a_step, b_step),
        'left_fires_in_gap': left_fires,
        'right_fires_in_gap': right_fires,
        'left_parity': left_parity,  # 0 = even, 1 = odd
        'right_parity': right_parity,
        'both_even': left_parity == 0 and right_parity == 0,
        'odd_residual': left_parity == 1 or right_parity == 1,
    }

def generate_normalform_transitions(ms):
    """Generate incrementing (normal form) transition functions."""
    n = len(ms)
    fs = []
    for i in range(n):
        m = ms[i]
        def f(L, S, R, m=m):
            return (S + 1) % m
        fs.append(f)
    return fs

def generate_all_binary_transitions(ms, binary_positions):
    """Generate all possible transition functions.
    Binary procs: only inc (0->1->0) and dec (1->0->1) = same for binary.
    For binary, there's only one non-identity transition: flip. So normalForm is the only option.
    Ternary procs: inc (0->1->2->0) or dec (0->2->1->0).
    """
    n = len(ms)
    ternary_positions = [i for i in range(n) if i not in binary_positions]

    # For each ternary proc, two options: inc or dec
    for combo in itertools.product([0, 1], repeat=len(ternary_positions)):
        fs = [None] * n
        for i in binary_positions:
            def f(L, S, R, m=ms[i]):
                return (S + 1) % m
            fs[i] = f
        for idx, i in enumerate(ternary_positions):
            if combo[idx] == 0:  # inc
                def f(L, S, R, m=ms[i]):
                    return (S + 1) % m
                fs[i] = f
            else:  # dec
                def f(L, S, R, m=ms[i]):
                    return (S + m - 1) % m
                fs[i] = f
        yield fs

def run_investigation():
    print("=" * 70)
    print("SORRY 5 INVESTIGATION: Odd-parity residual for consecutive binary")
    print("=" * 70)

    # Test cases: n=5, 7, 9 with 3 consecutive binary, sub-threshold
    # Sub-threshold: product < 4 * 3^(n-2)
    test_cases = [
        # n=5: threshold = 4*3^3 = 108. Sub-threshold multisets with >=3 binary:
        # ms with 3+ binary, product < 108
        # 3 binary + 2 ternary: 2^3 * 3^2 = 72 < 108 ✓
        (5, [2, 2, 2, 3, 3]),
        # n=7: threshold = 4*3^5 = 972.
        # 3 binary + 4 ternary: 2^3 * 3^4 = 648 < 972 ✓
        (7, [2, 2, 2, 3, 3, 3, 3]),
    ]

    for n, ms in test_cases:
        threshold = 4 * (3 ** (n - 2))
        product = 1
        for m in ms:
            product *= m
        print(f"\n{'='*60}")
        print(f"n={n}, ms={ms}, product={product}, threshold={threshold}")
        print(f"{'='*60}")

        # Binary positions: first 3 are consecutive binary
        binary_pos = [i for i in range(n) if ms[i] == 2]
        consec_binary_start = None
        for i in range(n):
            if ms[i] == 2 and ms[(i+1)%n] == 2 and ms[(i+2)%n] == 2:
                consec_binary_start = i
                break

        if consec_binary_start is None:
            print("No 3 consecutive binary found!")
            continue

        i = consec_binary_start
        ri = (i + 1) % n  # middle binary
        rri = (i + 2) % n
        print(f"3 consecutive binary at positions {i}, {ri}, {rri}")
        print(f"Middle proc (ri) = {ri}")

        total_cycles = 0
        total_isolated = 0
        total_odd_residual = 0
        total_odd_with_ec = 0
        odd_ec_locations = defaultdict(int)
        odd_no_ec = []

        # Try all transition function combos
        trans_count = 0
        for fs in generate_all_binary_transitions(ms, binary_pos):
            trans_count += 1
            cycles, sp = find_good_cycles(ms, fs)

            for cycle in cycles:
                total_cycles += 1
                movers = get_mover_sequence(cycle, sp)

                # Check if ri has isolated firings with fc >= 2
                analysis = analyze_isolated_firings(cycle, sp, ri, ms)

                if analysis.get('skip') or not analysis['isolated']:
                    continue

                total_isolated += 1

                if analysis.get('odd_residual'):
                    total_odd_residual += 1

                    # Check EC
                    has_ec, ec_proc, ec_ctx = has_entry_conflict(cycle, sp, ms)
                    if has_ec:
                        total_odd_with_ec += 1
                        # Classify location
                        if ec_proc == i:
                            odd_ec_locations['left_binary (i)'] += 1
                        elif ec_proc == ri:
                            odd_ec_locations['middle_binary (ri)'] += 1
                        elif ec_proc == rri:
                            odd_ec_locations['right_binary (rri)'] += 1
                        elif ms[ec_proc] == 3:
                            odd_ec_locations['ternary'] += 1
                        else:
                            odd_ec_locations[f'other(proc={ec_proc})'] += 1
                    else:
                        odd_no_ec.append({
                            'cycle_len': len(cycle),
                            'movers': movers[:20],
                            'analysis': analysis,
                        })

        print(f"\nTransition combos tested: {trans_count}")
        print(f"Total good cycles found: {total_cycles}")
        print(f"Cycles with ri isolated (fc>=2, gap>=2): {total_isolated}")
        print(f"Odd-parity residual cycles: {total_odd_residual}")
        print(f"Odd-parity with EC: {total_odd_with_ec}")
        print(f"Odd-parity WITHOUT EC: {len(odd_no_ec)}")
        if odd_ec_locations:
            print(f"\nEC locations for odd-parity:")
            for loc, cnt in sorted(odd_ec_locations.items()):
                print(f"  {loc}: {cnt}")
        if odd_no_ec:
            print(f"\n*** WARNING: {len(odd_no_ec)} cycles without EC! ***")
            for info in odd_no_ec[:5]:
                print(f"  len={info['cycle_len']}, movers={info['movers']}")
                print(f"  analysis={info['analysis']}")

    # Part 4: Check if odd-parity case arises at n=9
    print(f"\n{'='*60}")
    print("PART 4: Does odd-parity residual arise at n=9?")
    print(f"{'='*60}")

    n = 9
    # 3 binary + 6 ternary: 2^3 * 3^6 = 5832, threshold = 4*3^7 = 8748
    ms = [2, 2, 2, 3, 3, 3, 3, 3, 3]
    threshold = 4 * (3 ** (n - 2))
    product = 1
    for m in ms:
        product *= m
    print(f"n={n}, ms={ms}, product={product}, threshold={threshold}")

    binary_pos = [0, 1, 2]
    i, ri, rri = 0, 1, 2

    total_cycles_n9 = 0
    total_isolated_n9 = 0
    total_odd_n9 = 0
    total_odd_ec_n9 = 0
    odd_no_ec_n9 = []

    # At n=9 with 6 ternary procs, 2^6 = 64 transition combos
    trans_count = 0
    for fs in generate_all_binary_transitions(ms, binary_pos):
        trans_count += 1
        if trans_count % 16 == 0:
            print(f"  Progress: {trans_count}/64 combos...")
        cycles, sp = find_good_cycles(ms, fs)

        for cycle in cycles:
            total_cycles_n9 += 1
            analysis = analyze_isolated_firings(cycle, sp, ri, ms)

            if analysis.get('skip') or not analysis['isolated']:
                continue

            total_isolated_n9 += 1

            if analysis.get('odd_residual'):
                total_odd_n9 += 1
                has_ec, ec_proc, _ = has_entry_conflict(cycle, sp, ms)
                if has_ec:
                    total_odd_ec_n9 += 1
                else:
                    odd_no_ec_n9.append(len(cycle))

    print(f"\nn=9 results:")
    print(f"  Transition combos tested: {trans_count}")
    print(f"  Total good cycles: {total_cycles_n9}")
    print(f"  Isolated firings at ri: {total_isolated_n9}")
    print(f"  Odd-parity residual: {total_odd_n9}")
    print(f"  Odd-parity with EC: {total_odd_ec_n9}")
    print(f"  Odd-parity WITHOUT EC: {len(odd_no_ec_n9)}")

    if total_odd_n9 == 0:
        print(f"\n*** THE ODD-PARITY CASE IS VACUOUS AT n=9! ***")
        print("The sorry can potentially be closed by showing the case is vacuous for n >= 9.")

    # Part 2b: Deeper look at odd-parity cycles at n=5
    print(f"\n{'='*60}")
    print("PART 2b: Detailed odd-parity analysis at n=5")
    print(f"{'='*60}")

    ms5 = [2, 2, 2, 3, 3]
    binary_pos5 = [0, 1, 2]
    n5 = 5
    ri5 = 1

    odd_details = []
    for fs in generate_all_binary_transitions(ms5, binary_pos5):
        cycles, sp = find_good_cycles(ms5, fs)
        for cycle in cycles:
            analysis = analyze_isolated_firings(cycle, sp, ri5, ms5)
            if analysis.get('skip') or not analysis['isolated']:
                continue
            if analysis.get('odd_residual'):
                movers = get_mover_sequence(cycle, sp)
                has_ec, ec_proc, ec_ctx = has_entry_conflict(cycle, sp, ms5)

                # Detailed: check EC at each proc separately
                ec_by_proc = {}
                for p in range(n5):
                    mover_ctx = set()
                    nonmover_ctx = set()
                    for idx, c in enumerate(cycle):
                        m = sp[c]
                        left = c[(p-1) % n5]
                        self_val = c[p]
                        right = c[(p+1) % n5]
                        ctx = (left, self_val, right)
                        if m == p:
                            mover_ctx.add(ctx)
                        else:
                            nonmover_ctx.add(ctx)
                    overlap = mover_ctx & nonmover_ctx
                    if overlap:
                        ec_by_proc[p] = overlap

                odd_details.append({
                    'cycle_len': len(cycle),
                    'movers': movers,
                    'left_fires': analysis['left_fires_in_gap'],
                    'right_fires': analysis['right_fires_in_gap'],
                    'left_par': analysis['left_parity'],
                    'right_par': analysis['right_parity'],
                    'gap': analysis['min_gap'],
                    'ec_procs': list(ec_by_proc.keys()),
                    'has_ec': has_ec,
                })

    print(f"Total odd-parity cycles at n=5: {len(odd_details)}")
    if odd_details:
        # Summarize
        ec_proc_dist = defaultdict(int)
        for d in odd_details:
            for p in d['ec_procs']:
                ec_proc_dist[p] += 1

        print(f"EC location distribution:")
        for p in range(n5):
            ptype = "binary" if ms5[p] == 2 else "ternary"
            print(f"  proc {p} ({ptype}): {ec_proc_dist.get(p, 0)} cycles")

        # Show a few examples
        print(f"\nFirst 5 examples:")
        for d in odd_details[:5]:
            print(f"  len={d['cycle_len']}, gap={d['gap']}, "
                  f"L_fires={d['left_fires']}(par={d['left_par']}), "
                  f"R_fires={d['right_fires']}(par={d['right_par']}), "
                  f"EC_at={d['ec_procs']}")
            print(f"    movers={d['movers']}")

        # Check: is there a pattern?
        all_have_ec = all(d['has_ec'] for d in odd_details)
        print(f"\nAll odd-parity cycles have EC: {all_have_ec}")

        # What parity combos appear?
        parity_combos = defaultdict(int)
        for d in odd_details:
            combo = (d['left_par'], d['right_par'])
            parity_combos[combo] += 1
        print(f"\nParity combos (left, right):")
        for combo, cnt in sorted(parity_combos.items()):
            print(f"  {combo}: {cnt}")

    # Additional: check different placements of 3 consecutive binary at n=5
    print(f"\n{'='*60}")
    print("PART 2c: All rotations of binary placement at n=5")
    print(f"{'='*60}")

    rotations = [
        [2, 2, 2, 3, 3],
        [3, 2, 2, 2, 3],
        [3, 3, 2, 2, 2],
        [2, 3, 3, 2, 2],
        [2, 2, 3, 3, 2],
    ]

    for ms_rot in rotations:
        n = 5
        # Find consecutive triple
        for start in range(n):
            if ms_rot[start] == 2 and ms_rot[(start+1)%n] == 2 and ms_rot[(start+2)%n] == 2:
                i_r = start
                ri_r = (start+1) % n
                rri_r = (start+2) % n
                break

        binary_pos_r = [j for j in range(n) if ms_rot[j] == 2]

        odd_count = 0
        odd_ec_count = 0
        for fs in generate_all_binary_transitions(ms_rot, binary_pos_r):
            cycles, sp = find_good_cycles(ms_rot, fs)
            for cycle in cycles:
                analysis = analyze_isolated_firings(cycle, sp, ri_r, ms_rot)
                if analysis.get('skip') or not analysis['isolated']:
                    continue
                if analysis.get('odd_residual'):
                    odd_count += 1
                    has_ec, _, _ = has_entry_conflict(cycle, sp, ms_rot)
                    if has_ec:
                        odd_ec_count += 1

        print(f"ms={ms_rot}: odd_residual={odd_count}, with_EC={odd_ec_count}, "
              f"without_EC={odd_count - odd_ec_count}")


if __name__ == '__main__':
    run_investigation()
