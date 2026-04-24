#!/usr/bin/env python3
"""
RA13 Part 4: Clean analysis with correct ZW definition.

The winding number of a mover walk on Z_n:
  Sum over steps of signed_step, where signed_step = shortest displacement on ring.
  If sum = 0, it's zero winding.

But wait — this is not the same as winding number in the topological sense.
The winding number of a closed walk on a circle:
  Lift the walk to Z (universal cover). Start at 0.
  At each step, move by the signed displacement (choosing the short way).
  The winding number = final position / n.

For a cycle of movers p_0, p_1, ..., p_{L-1} (cyclic):
  displacement_i = (p_i - p_{i-1}) mod n, interpreted as the signed shortest path.
  total = sum of displacements.
  winding = total / n.

But the shortest path on Z_n is ambiguous when the displacement = n/2.
For odd n, no ambiguity. For even n, only when |diff| = n/2.

Let me use: displacement = ((diff + n//2) % n) - n//2 for odd n.
For n=5: diff of 3 → 3-5 = -2 (CCW by 2). diff of 2 → 2 (CW by 2). diff of 4 → -1.

Actually, standard: for diff in {0,...,n-1}, the signed displacement is:
  diff if diff ≤ n/2, else diff - n.
So for n=5: diff 0→0, 1→1, 2→2, 3→-2, 4→-1.

ALSO: I need to be more careful. The "mover walk" in the Lean formalization:
- cwStepCount = number of steps where mover increases (mod n)
  i.e., p_{i} = (p_{i-1} + 1) % n
- ccwStepCount = same but p_i = (p_{i-1} - 1) % n
- stayStepCount = p_i = p_{i-1}
- totalDisplacement = cwStepCount - ccwStepCount

For ZW: cwStepCount = ccwStepCount.

Wait, this is MUCH more restrictive than winding = 0!
cwStep means the mover moves EXACTLY one position clockwise from previous mover.
Not an arbitrary displacement.

Let me re-read the problem statement:
"Zero winding: totalDisplacement = 0, cwStepCount = ccwStepCount"

And cwStepCount counts steps where mover goes +1 (CW), ccwStepCount counts -1 (CCW).
Steps where |displacement| ≥ 2 are... what? They're neither CW nor CCW in this counting?

Hmm, let me check what Lean defines. The totalDisplacement probably counts +1 for CW,
-1 for CCW, and 0 for stay/jump. So ZW just means: number of +1 steps = number of -1 steps.

Actually, re-reading: "cwStepCount > 0: at least one CW step". This suggests steps are
classified as CW (+1), CCW (-1), or other (stay, jump). ZW = cwCount = ccwCount.

Let me implement this correctly.
"""

from itertools import product as iterproduct, permutations
from collections import defaultdict
import random

random.seed(42)


def classify_step(prev_mover, curr_mover, n):
    """Classify a step as CW (+1), CCW (-1), stay (0), or jump (None)."""
    diff = (curr_mover - prev_mover) % n
    if diff == 1:
        return 'cw'
    elif diff == n - 1:
        return 'ccw'
    elif diff == 0:
        return 'stay'
    else:
        return 'jump'


def build_config_graph(ms):
    n = len(ms)
    all_configs = list(iterproduct(*[range(m) for m in ms]))
    adj = defaultdict(list)
    for c in all_configs:
        for p in range(n):
            for v in range(ms[p]):
                if v != c[p]:
                    c2 = list(c)
                    c2[p] = v
                    adj[c].append((tuple(c2), p))
    return all_configs, adj


def find_cycles_comprehensive(ms, num_samples=200000, max_steps=80):
    """Find cycles with detailed step classification."""
    n = len(ms)
    P = 1
    for m in ms:
        P *= m
    if P > 3000:
        return []

    all_configs, adj = build_config_graph(ms)
    unique = {}

    for _ in range(num_samples):
        config = random.choice(all_configs)
        visited = {config: 0}
        path = [config]
        movers = []

        for step in range(1, max_steps):
            neighbors = adj[config]
            if not neighbors:
                break
            config, p = random.choice(neighbors)
            movers.append(p)

            if config in visited:
                cs = visited[config]
                cc = path[cs:]
                cm = movers[cs:]
                L = len(cm)
                if L < 2 * n:
                    break

                fc = defaultdict(int)
                for m in cm:
                    fc[m] += 1
                if len(fc) < n or min(fc.values()) < 2:
                    break

                # Classify steps
                cw = ccw = stay = jump = 0
                for i in range(L):
                    s = classify_step(cm[i-1], cm[i], n)
                    if s == 'cw': cw += 1
                    elif s == 'ccw': ccw += 1
                    elif s == 'stay': stay += 1
                    else: jump += 1

                # ZW = cw == ccw AND cw > 0
                if cw != ccw or cw == 0:
                    break

                if max(fc.values()) < 3:
                    break

                key = (cc[0], tuple(cm))
                if key not in unique:
                    unique[key] = {
                        'configs': cc,
                        'movers': cm,
                        'fc': dict(fc),
                        'length': L,
                        'cw': cw, 'ccw': ccw, 'stay': stay, 'jump': jump,
                    }
                break

            visited[config] = step
            path.append(config)

    return list(unique.values())


def analyze_phases(cycle_info, ms):
    n = len(ms)
    movers = cycle_info['movers']
    fc = cycle_info['fc']
    L = len(movers)
    results = {}

    for q in range(n):
        if fc.get(q, 0) < 3:
            continue

        fire_pos = [i for i, m in enumerate(movers) if m == q]
        left_q = (q - 1) % n
        right_q = (q + 1) % n

        phases = []
        for phase_idx in range(len(fire_pos)):
            start = fire_pos[phase_idx]
            end = fire_pos[(phase_idx + 1) % len(fire_pos)]
            J = K = 0
            pos = (start + 1) % L
            while pos != end:
                if movers[pos] == left_q: J += 1
                if movers[pos] == right_q: K += 1
                pos = (pos + 1) % L
            phases.append((J, K))

        results[q] = {
            'fc': fc[q],
            'ms_q': ms[q],
            'ms_left': ms[left_q],
            'ms_right': ms[right_q],
            'phases': phases,
            'is_binary': ms[q] == 2,
            'left_is_binary': ms[left_q] == 2,
            'right_is_binary': ms[right_q] == 2,
        }

    return results


def check_entry_conflict(cycle_info, ms):
    n = len(ms)
    configs = cycle_info['configs']
    movers = cycle_info['movers']
    L = len(movers)
    for p in range(n):
        mc = set(); nc = set()
        left = (p - 1) % n; right = (p + 1) % n
        for i in range(L):
            c = configs[i]
            ctx = (c[left], c[p], c[right])
            if movers[i] == p: mc.add(ctx)
            else: nc.add(ctx)
        if mc & nc:
            return True, p
    return False, None


def is_dispatchable(J, K):
    if J == 0 or K == 0:
        return True
    if J % 2 == 0 and K % 2 == 0:
        return True
    return False


def main():
    print("=" * 70)
    print("RA13 Part 4: Correct ZW (cw=ccw, cw>0) + Phase Analysis")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n{'='*60}")
        print(f"n = {n}, threshold = {4 * 3**(n-2)}")
        print(f"{'='*60}")

        threshold = 4 * 3 ** (n - 2)
        multisets = []
        def gen_ms(pos, current, prod, ms_list=multisets, nn=n, thr=threshold):
            if pos == nn:
                if prod < thr and sum(1 for x in current if x == 2) >= 3:
                    ms_list.append(tuple(current))
                return
            for m in range(2, min(thr // max(prod, 1) + 1, 20)):
                new_prod = prod * m
                if new_prod >= thr:
                    break
                if current and m < current[-1]:
                    continue
                gen_ms(pos + 1, current + [m], new_prod)
        gen_ms(0, [], 1)

        print(f"Sub-threshold multisets with ≥3 binary: {len(multisets)}")

        total_cycles = 0
        total_ec = 0
        total_has_dispatchable = 0
        total_no_dispatchable = 0
        binary_fc3_count = 0  # fc≥3 at binary (must be ≥4, even)
        ternary_fc3_count = 0
        pigeonhole_direct = 0  # Some neighbor fc < fc(q) at fc≥3 proc
        all_phases_odd_odd = 0  # All phases at fc≥3 proc have both J,K odd

        # Track: CAN both neighbors have fc ≥ fc(q) where q is fc≥3?
        both_neighbors_high = 0

        non_disp_examples = []

        for ms_sorted in multisets:
            P = 1
            for m in ms_sorted:
                P *= m
            if P > 2000:
                continue

            seen = set()
            pc = 0
            for perm in permutations(ms_sorted):
                if perm in seen:
                    continue
                seen.add(perm)
                pc += 1
                if pc > (30 if n == 5 else 15):
                    break

                ms = perm
                cycles = find_cycles_comprehensive(ms,
                    num_samples=(300000 if n == 5 else 150000),
                    max_steps=(80 if n == 5 else 120))

                for cyc in cycles:
                    pi = analyze_phases(cyc, ms)
                    if not pi:
                        continue
                    total_cycles += 1

                    has_ec, _ = check_entry_conflict(cyc, ms)
                    if has_ec:
                        total_ec += 1

                    # Check each fc≥3 proc
                    any_disp = False
                    for q, info in pi.items():
                        if info['is_binary']:
                            binary_fc3_count += 1
                        else:
                            ternary_fc3_count += 1

                        fc_q = info['fc']
                        left_q = (q - 1) % n
                        right_q = (q + 1) % n
                        fc_left = cyc['fc'].get(left_q, 0)
                        fc_right = cyc['fc'].get(right_q, 0)

                        if fc_left < fc_q or fc_right < fc_q:
                            pigeonhole_direct += 1
                        else:
                            both_neighbors_high += 1

                        # Check if any phase at q is dispatchable
                        for J, K in info['phases']:
                            if is_dispatchable(J, K):
                                any_disp = True
                                break

                        # Check if all phases odd-odd
                        if all(J % 2 == 1 and K % 2 == 1 for J, K in info['phases']):
                            all_phases_odd_odd += 1

                    if any_disp:
                        total_has_dispatchable += 1
                    else:
                        total_no_dispatchable += 1
                        if len(non_disp_examples) < 10:
                            non_disp_examples.append({
                                'ms': ms, 'fc': cyc['fc'], 'length': cyc['length'],
                                'phase_info': pi, 'has_ec': has_ec,
                                'cw': cyc['cw'], 'ccw': cyc['ccw'],
                                'stay': cyc['stay'], 'jump': cyc['jump'],
                            })

        print(f"\nZW cycles (cw=ccw>0) with fc≥3: {total_cycles}")
        print(f"  Entry conflict: {total_ec}/{total_cycles}")
        print(f"  Has dispatchable phase: {total_has_dispatchable}")
        print(f"  No dispatchable phase: {total_no_dispatchable}")
        print(f"\nfc≥3 proc stats:")
        print(f"  At binary: {binary_fc3_count}")
        print(f"  At ternary+: {ternary_fc3_count}")
        print(f"  Pigeonhole works (neighbor fc < fc_q): {pigeonhole_direct}")
        print(f"  Both neighbors fc ≥ fc_q: {both_neighbors_high}")
        print(f"  All phases odd-odd: {all_phases_odd_odd}")

        if non_disp_examples:
            print(f"\n  NON-DISPATCHABLE examples:")
            for ex in non_disp_examples[:5]:
                print(f"    ms={ex['ms']}, CL={ex['length']}, fc={ex['fc']}")
                print(f"    cw={ex['cw']}, ccw={ex['ccw']}, stay={ex['stay']}, jump={ex['jump']}")
                print(f"    has_ec={ex['has_ec']}")
                for q, info in ex['phase_info'].items():
                    lq = (q-1) % n; rq = (q+1) % n
                    print(f"      q={q}: fc={info['fc']}, ms[q]={info['ms_q']}, "
                          f"L_fc={ex['fc'].get(lq,0)}, R_fc={ex['fc'].get(rq,0)}")
                    print(f"        phases: {info['phases']}")
        else:
            print(f"\n  ALL ZW fc≥3 cycles have a dispatchable phase!")


if __name__ == '__main__':
    main()
