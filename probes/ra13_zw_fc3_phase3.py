#!/usr/bin/env python3
"""
RA13 Part 3: Extended analysis.

1. n=7 with random sampling (exhaustive too expensive)
2. Deeper analysis of WHY dispatchable always works
3. The key question: does fc≥3 + ZW + binary neighbor ALWAYS give dispatchable?
4. Pigeonhole argument analysis
"""

from itertools import product as iterproduct, permutations
from collections import defaultdict
import random
import sys

random.seed(42)


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


def find_zw_cycles_random(ms, adj, all_configs, num_samples=100000, max_steps=100):
    n = len(ms)
    unique_cycles = {}

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
                cycle_configs = path[cs:]
                cycle_movers = movers[cs:]
                L = len(cycle_movers)

                if L < 2 * n:
                    break

                fc = defaultdict(int)
                for m in cycle_movers:
                    fc[m] += 1
                if len(fc) < n or min(fc.values()) < 2:
                    break

                # ZW check
                cw = 0; ccw = 0
                for i in range(L):
                    d = cycle_movers[i] - cycle_movers[i-1]
                    if d > n // 2: ccw += 1
                    elif d < -(n // 2): cw += 1
                if cw != ccw:
                    break

                if max(fc.values()) < 3:
                    break

                key = (cycle_configs[0], tuple(cycle_movers))
                if key not in unique_cycles:
                    unique_cycles[key] = {
                        'configs': cycle_configs,
                        'movers': cycle_movers,
                        'fc': dict(fc),
                        'length': L,
                    }
                break

            visited[config] = step
            path.append(config)

    return list(unique_cycles.values())


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
            'left_is_binary': ms[left_q] == 2,
            'right_is_binary': ms[right_q] == 2,
            'is_binary': ms[q] == 2,
        }

    return results


def check_entry_conflict(cycle_info, ms):
    n = len(ms)
    configs = cycle_info['configs']
    movers = cycle_info['movers']
    L = len(movers)

    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        left = (p - 1) % n
        right = (p + 1) % n
        for i in range(L):
            c = configs[i]
            ctx = (c[left], c[p], c[right])
            if movers[i] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            return True, p
    return False, None


def is_any_phase_dispatchable(phases):
    for J, K in phases:
        if J == 0 and K == 0: return True, 'both-silent'
        if J % 2 == 0 and K % 2 == 0: return True, 'even-even'
        if J == 0: return True, f'zero-left({J},{K})'
        if K == 0: return True, f'zero-right({J},{K})'
    return False, None


def pigeonhole_analysis(phases, fc_left, fc_right, fc_q):
    """
    Analyze the pigeonhole argument.
    We have fc_q phases. Sum of J's = fc_left, sum of K's = fc_right.
    Can ALL phases have J≥1 AND K≥1?
    That requires fc_left ≥ fc_q AND fc_right ≥ fc_q.
    So if fc_left < fc_q or fc_right < fc_q, some phase has J=0 or K=0 → dispatchable.
    """
    need_all_nonzero = (fc_left >= fc_q and fc_right >= fc_q)
    return not need_all_nonzero  # True = pigeonhole guarantees dispatchable


def main():
    print("=" * 70)
    print("RA13 Part 3: Pigeonhole + Phase Dispatch Analysis")
    print("=" * 70)

    # PART 1: Pigeonhole argument
    print("\n--- PIGEONHOLE ARGUMENT ---")
    print("If proc q has fc(q) ≥ 3 and neighbor p has fc(p) = 2:")
    print("  Then 2 fires of p distributed over fc(q) ≥ 3 phases.")
    print("  At least fc(q) - 2 ≥ 1 phases have 0 fires from that neighbor.")
    print("  If J=0 in some phase: that phase is dispatchable (zero-left).")
    print("  Zero-left means (0, K) for some K.")
    print("  If K=0 too → both-silent → dispatchable.")
    print("  If K≥1 → one-sided or traversal → dispatchable.")
    print()
    print("So: fc(q) ≥ 3 + some neighbor with fc = 2 → ALWAYS dispatchable.")
    print()
    print("Key question: can ALL neighbors of the fc≥3 proc also have fc ≥ 3?")
    print("If fc ≥ 2 for all and fc ≥ 3 for some q, can both neighbors of q also be ≥ 3?")
    print()

    # PART 2: Check at n=5
    for n in [5, 7]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        threshold = 4 * 3 ** (n - 2)
        multisets = []
        def gen_ms(pos, current, prod, multisets=multisets, n=n, threshold=threshold):
            if pos == n:
                if prod < threshold and sum(1 for x in current if x == 2) >= 3:
                    multisets.append(tuple(current))
                return
            for m in range(2, min(threshold // max(prod, 1) + 1, 20)):
                new_prod = prod * m
                if new_prod >= threshold:
                    break
                if current and m < current[-1]:
                    continue
                gen_ms(pos + 1, current + [m], new_prod)
        gen_ms(0, [], 1)

        print(f"Multisets: {len(multisets)}")

        total_zw_fc3 = 0
        pigeonhole_works = 0
        pigeonhole_fails = 0
        all_neighbors_fc3 = 0
        still_dispatchable_despite_no_pigeonhole = 0
        has_ec_count = 0

        # Track: when pigeonhole fails (both neighbors fc≥3), what happens?
        pigeonhole_fail_details = []

        for ms_sorted in multisets:
            P = 1
            for m in ms_sorted:
                P *= m
            if P > 2000:
                continue

            seen = set()
            perm_count = 0
            for perm in permutations(ms_sorted):
                if perm in seen:
                    continue
                seen.add(perm)
                perm_count += 1
                if perm_count > 20:
                    break

                ms = perm
                all_configs, adj = build_config_graph(ms)

                if n == 5:
                    cycles = find_zw_cycles_random(ms, adj, all_configs,
                                                    num_samples=200000, max_steps=80)
                else:
                    cycles = find_zw_cycles_random(ms, adj, all_configs,
                                                    num_samples=100000, max_steps=120)

                for cyc in cycles:
                    phase_info = analyze_phases(cyc, ms)
                    if not phase_info:
                        continue

                    total_zw_fc3 += 1
                    has_ec, _ = check_entry_conflict(cyc, ms)
                    if has_ec:
                        has_ec_count += 1

                    # For each fc≥3 proc, check pigeonhole
                    cycle_pigeonhole_works = False
                    cycle_all_neighbors_fc3 = False
                    cycle_dispatchable = False

                    for q, info in phase_info.items():
                        fc_q = info['fc']
                        left_q = (q - 1) % n
                        right_q = (q + 1) % n
                        fc_left = cyc['fc'].get(left_q, 0)
                        fc_right = cyc['fc'].get(right_q, 0)

                        if fc_left < fc_q or fc_right < fc_q:
                            cycle_pigeonhole_works = True
                        if fc_left >= 3 and fc_right >= 3:
                            cycle_all_neighbors_fc3 = True

                        disp, reason = is_any_phase_dispatchable(info['phases'])
                        if disp:
                            cycle_dispatchable = True

                    if cycle_pigeonhole_works:
                        pigeonhole_works += 1
                    else:
                        pigeonhole_fails += 1

                    if cycle_all_neighbors_fc3:
                        all_neighbors_fc3 += 1

                    if cycle_dispatchable:
                        if not cycle_pigeonhole_works:
                            still_dispatchable_despite_no_pigeonhole += 1
                    else:
                        if len(pigeonhole_fail_details) < 10:
                            pigeonhole_fail_details.append({
                                'ms': ms,
                                'fc': cyc['fc'],
                                'length': cyc['length'],
                                'phase_info': phase_info,
                                'has_ec': has_ec,
                            })

        print(f"\nTotal ZW cycles with fc≥3: {total_zw_fc3}")
        print(f"  Has entry conflict: {has_ec_count}/{total_zw_fc3}")
        print(f"  Pigeonhole works (some neighbor fc < fc_q): {pigeonhole_works}")
        print(f"  Pigeonhole fails (both neighbors fc ≥ fc_q): {pigeonhole_fails}")
        print(f"  Both neighbors also fc≥3: {all_neighbors_fc3}")
        print(f"  Dispatchable despite pigeonhole failure: {still_dispatchable_despite_no_pigeonhole}")

        if pigeonhole_fail_details:
            print(f"\n  Non-dispatchable despite all attempts:")
            for ex in pigeonhole_fail_details[:5]:
                print(f"    ms={ex['ms']}, CL={ex['length']}, fc={ex['fc']}")
                for q, info in ex['phase_info'].items():
                    print(f"      q={q}: fc={info['fc']}, phases={info['phases']}, "
                          f"L_fc={ex['fc'].get((q-1)%len(ex['ms']),0)}, "
                          f"R_fc={ex['fc'].get((q+1)%len(ex['ms']),0)}")

    # PART 3: Theoretical analysis
    print("\n" + "=" * 60)
    print("THEORETICAL ANALYSIS")
    print("=" * 60)
    print()
    print("Claim: In a ZW good cycle with ≥3 binary, sub-threshold,")
    print("n≥9, if some q has fc(q) ≥ 3, then q has a dispatchable phase.")
    print()
    print("Proof sketch:")
    print("  CL = sum(fc) ≥ 2n + 1 (since some fc ≥ 3, rest ≥ 2)")
    print("  Let q have fc ≥ 3. Let left = fc(q-1), right = fc(q+1).")
    print("  q has fc(q) phases. Sum of J's = left, sum of K's = right.")
    print()
    print("  Case 1: left < fc(q) or right < fc(q).")
    print("    Pigeonhole: some phase has J=0 or K=0 → dispatchable.")
    print()
    print("  Case 2: left ≥ fc(q) AND right ≥ fc(q).")
    print("    Both neighbors fire ≥ fc(q) ≥ 3 times.")
    print("    Total left+right ≥ 2*fc(q) ≥ 6, distributed over fc(q) phases.")
    print("    Average per phase: (left+right)/fc(q) ≥ 2.")
    print("    Some phase has J+K ≥ 2.")
    print("    But we need J=0 or K=0 or both even...")
    print()
    print("  The question: can we have fc(q) phases all with J≥1, K≥1, J+K odd?")
    print("  Parity: sum of all J = left (even/odd). sum of all K = right.")
    print("  If left is even: even number of odd-J phases.")
    print("  If we need all J≥1, at most fc(q) phases with J=1.")
    print("  If left = 3, fc(q) = 3: could have J=(1,1,1). All odd.")
    print("  If right = 3: K=(1,1,1). All odd. Then phases are (1,1),(1,1),(1,1).")
    print("  This IS the non-dispatchable case!")
    print()
    print("  But: fc(left) = 3, fc(q) = 3, fc(right) = 3.")
    print("  CL ≥ 3*3 = 9 just for these 3 procs, but also n-3 others with fc≥2.")
    print("  CL ≥ 9 + 2(n-3) = 2n+3.")
    print()
    print("  KEY CONSTRAINT: binary procs have EVEN fc.")
    print("  If q is binary: fc(q) is even, so fc(q) ≥ 4.")
    print("  If left(q) is binary: left is even, so left ≥ 2.")
    print("    With fc(q)=3, left=2: pigeonhole → some J=0 → dispatchable!")
    print("  If left(q) is binary: left even ≥ 2 < fc(q)=3 → PIGEONHOLE WORKS!")
    print()
    print("  So: the only problematic case is fc(q)≥3 at ternary q with")
    print("  BOTH neighbors also ternary+ with fc ≥ fc(q).")
    print("  But: with ≥3 binary procs, every ternary has a binary within distance...")
    print("  No, that's not guaranteed. Example: (2,2,2,3,3,3,3,3,3) at n=9.")
    print("  Proc 4 (ternary) has neighbors 3 (ternary) and 5 (ternary).")
    print()
    print("  NEW APPROACH: Use the binary neighbor constraint differently.")
    print("  With ≥3 binary, if q is ternary with both ternary neighbors,")
    print("  then q is in a 'ternary run'. But there are ≥3 binary procs,")
    print("  so the ternary runs are separated. The binary procs all have fc even.")
    print("  At a binary proc with fc=2: its neighbors get fc(binary)=2 fires")
    print("  from it, distributed across their phases.")
    print()
    print("  WAIT — the pigeonhole needs to apply at the fc≥3 proc,")
    print("  not at the binary proc. The binary's neighbor info matters.")


if __name__ == '__main__':
    main()
