#!/usr/bin/env python3
"""
Follow-up: sharper MTR EC analysis.

Key findings from round 1:
- 100% of MTR cycles have EC (good!)
- No single UNIVERSAL processor position
- EC at pivot (dist=0) ~84% of cycles
- EC at dist=+/-2 is most common count-wise (29.7%)
- Binary procs get 59% of ECs, ternary 41%

New questions:
1. Does tight_LL bias EC to the LEFT, tight_RR to the RIGHT?
2. Is the EC always at dist=-2 when tight_LL? At dist=+2 when tight_RR?
3. Do ALL MTR cycles have EC at the ternary pivot itself?
4. Minimal: what's the SMALLEST set of positions that covers all MTR cycles?
"""

import random
from itertools import product as iterproduct
from collections import defaultdict, Counter
import time

def random_transition(ms, n, rng):
    f = []
    for p in range(n):
        lp = (p - 1) % n
        rp = (p + 1) % n
        table = {}
        for L in range(ms[lp]):
            for S in range(ms[p]):
                for R in range(ms[rp]):
                    table[(L, S, R)] = rng.randint(0, ms[p] - 1)
        f.append(table)
    return f

def apply_move(config, p, f, n):
    c = list(config)
    lp = (p - 1) % n
    rp = (p + 1) % n
    c[p] = f[p][(c[lp], c[p], c[rp])]
    return tuple(c)

def find_cycles_random(ms, n, f, max_cycles=500, rng=None):
    if rng is None:
        rng = random.Random(42)
    configs_list = list(iterproduct(*[range(m) for m in ms]))
    total = len(configs_list)
    cycles = []
    seen = set()
    for trial in range(min(total * 5, 30000)):
        start = configs_list[rng.randint(0, total - 1)]
        config = start
        history = [config]
        config_to_step = {config: 0}
        for step in range(1, 600):
            p = rng.randint(0, n - 1)
            nc = apply_move(config, p, f, n)
            if nc == config:
                continue
            if nc in config_to_step:
                cs = config_to_step[nc]
                cc = history[cs:]
                if len(cc) >= n and len(set(cc)) == len(cc):
                    movers = []
                    ok = True
                    for i in range(len(cc)):
                        c1 = cc[i]
                        c2 = cc[(i + 1) % len(cc)]
                        mv = None
                        for q in range(n):
                            if c1[q] != c2[q]:
                                if mv is not None:
                                    ok = False; break
                                mv = q
                        if not ok or mv is None:
                            ok = False; break
                        movers.append(mv)
                    if ok:
                        cid = frozenset(cc)
                        if cid not in seen:
                            seen.add(cid)
                            cycles.append((list(cc), movers))
                            if len(cycles) >= max_cycles:
                                return cycles
                break
            history.append(nc)
            config_to_step[nc] = step
            config = nc
    return cycles

def find_sandwiched_pivots(ms, n):
    return [t for t in range(n) if ms[t] >= 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

def get_phases(movers, t):
    L = len(movers)
    fire_steps = [k for k in range(L) if movers[k] == t]
    if len(fire_steps) < 2:
        return []
    phases = []
    for idx in range(len(fire_steps)):
        start = fire_steps[idx]
        end = fire_steps[(idx + 1) % len(fire_steps)]
        interior = []
        k = (start + 1) % L
        while k != end:
            interior.append(k)
            k = (k + 1) % L
        phases.append((start, interior))
    return phases

def classify_phase(movers, t, fire_step, interior, n):
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n
    L = len(movers)
    J = sum(1 for k in interior if movers[k] == lt)
    K = sum(1 for k in interior if movers[k] == rt)
    tight_LL = False
    tight_RR = False
    for k in interior:
        if movers[k] == llt:
            k_succ = (k + 1) % L
            if movers[k_succ] == lt:
                tight_LL = True
        if movers[k] == rrt:
            k_succ = (k + 1) % L
            if movers[k_succ] == rt:
                tight_RR = True
    return {'J': J, 'K': K, 'tight_LL': tight_LL, 'tight_RR': tight_RR}

def is_mtr(info):
    return info['J'] == 1 and info['K'] == 1 and (info['tight_LL'] or info['tight_RR'])

def find_all_ec_procs(cycle, movers, ms, n):
    """Return set of procs that have entry conflict."""
    ec_procs = set()
    L = len(cycle)
    for i in range(n):
        mover_triples = set()
        nonmover_triples = set()
        for k in range(L):
            lp = (i - 1) % n
            rp = (i + 1) % n
            triple = (cycle[k][lp], cycle[k][i], cycle[k][rp])
            if movers[k] == i:
                mover_triples.add(triple)
            else:
                nonmover_triples.add(triple)
        if mover_triples & nonmover_triples:
            ec_procs.add(i)
    return ec_procs

def ring_distance(i, t, n):
    d1 = (i - t) % n
    d2 = (t - i) % n
    return d1 if d1 <= d2 else -d2

# ─────────────────────── main ───────────────────────

if __name__ == '__main__':
    t0 = time.time()
    n = 9

    ms_configs = [
        [2, 2, 3, 2, 2, 3, 2, 2, 3],
        [3, 2, 2, 3, 2, 2, 3, 2, 2],
        [2, 3, 2, 2, 3, 2, 2, 3, 2],
    ]

    for ms in ms_configs:
        pivots = find_sandwiched_pivots(ms, n)
        print(f"\n{'='*70}")
        print(f"ms={ms}, pivots={pivots}")
        print(f"{'='*70}")

        # Track per-MTR-instance: which relative positions have EC?
        # Separately for tight_LL only, tight_RR only, both
        stats = {
            'LL_only': {'total': 0, 'ec_at_dist': Counter(), 'per_cycle_ec_dists': []},
            'RR_only': {'total': 0, 'ec_at_dist': Counter(), 'per_cycle_ec_dists': []},
            'both':    {'total': 0, 'ec_at_dist': Counter(), 'per_cycle_ec_dists': []},
        }

        # Universal check: does EVERY cycle have EC at dist=-2 or +2?
        all_have_ec_at_pm2 = True
        all_have_ec_at_pivot = True
        total_mtr = 0
        no_ec_count = 0

        # Minimum covering set analysis
        position_presence = []  # list of sets of relative EC positions

        rng = random.Random(54321)
        for trial in range(300):
            f = random_transition(ms, n, rng)
            cycles = find_cycles_random(ms, n, f, max_cycles=200, rng=rng)

            for (cc, word) in cycles:
                ec_procs = find_all_ec_procs(cc, word, ms, n)

                for t in pivots:
                    phases = get_phases(word, t)
                    for (fs, interior) in phases:
                        info = classify_phase(word, t, fs, interior, n)
                        if not is_mtr(info):
                            continue

                        total_mtr += 1
                        # Relative EC positions
                        rel_ec = set()
                        for i in ec_procs:
                            rel_ec.add(ring_distance(i, t, n))

                        if not rel_ec:
                            no_ec_count += 1

                        position_presence.append(rel_ec)

                        if 0 not in rel_ec:
                            all_have_ec_at_pivot = False
                        if -2 not in rel_ec and 2 not in rel_ec:
                            all_have_ec_at_pm2 = False

                        # Classify by tight type
                        if info['tight_LL'] and info['tight_RR']:
                            key = 'both'
                        elif info['tight_LL']:
                            key = 'LL_only'
                        else:
                            key = 'RR_only'

                        stats[key]['total'] += 1
                        for d in rel_ec:
                            stats[key]['ec_at_dist'][d] += 1
                        stats[key]['per_cycle_ec_dists'].append(rel_ec)

        print(f"\nTotal MTR instances: {total_mtr}")
        print(f"MTR with NO EC: {no_ec_count}")
        print(f"All have EC at pivot (dist=0)? {all_have_ec_at_pivot}")
        print(f"All have EC at dist=+/-2? {all_have_ec_at_pm2}")

        # Per tight-type analysis
        for key in ['LL_only', 'RR_only', 'both']:
            s = stats[key]
            if s['total'] == 0:
                continue
            print(f"\n--- {key}: {s['total']} instances ---")

            # Frequency of each position having EC
            for d in sorted(s['ec_at_dist'].keys()):
                cnt = s['ec_at_dist'][d]
                pct = 100.0 * cnt / s['total']
                print(f"  dist={d:+d}: {cnt:4d}/{s['total']} = {pct:5.1f}%")

            # Check: specific universal positions?
            universal = None
            for rel_set in s['per_cycle_ec_dists']:
                if universal is None:
                    universal = rel_set.copy()
                else:
                    universal &= rel_set
            print(f"  Universal EC position (in ALL cycles): {universal if universal else 'NONE'}")

            # Check: for LL_only, is dist=-2 always there?
            if key == 'LL_only':
                has_neg2 = sum(1 for r in s['per_cycle_ec_dists'] if -2 in r)
                print(f"  Has EC at dist=-2 (left^2): {has_neg2}/{s['total']} = {100.0*has_neg2/s['total']:.1f}%")
                has_neg1 = sum(1 for r in s['per_cycle_ec_dists'] if -1 in r)
                print(f"  Has EC at dist=-1 (left):   {has_neg1}/{s['total']} = {100.0*has_neg1/s['total']:.1f}%")
            if key == 'RR_only':
                has_pos2 = sum(1 for r in s['per_cycle_ec_dists'] if 2 in r)
                print(f"  Has EC at dist=+2 (right^2): {has_pos2}/{s['total']} = {100.0*has_pos2/s['total']:.1f}%")
                has_pos1 = sum(1 for r in s['per_cycle_ec_dists'] if 1 in r)
                print(f"  Has EC at dist=+1 (right):   {has_pos1}/{s['total']} = {100.0*has_pos1/s['total']:.1f}%")

        # Greedy minimum covering set
        print(f"\n--- Greedy minimum covering set ---")
        uncovered = list(range(len(position_presence)))
        cover = []
        all_positions = set()
        for s in position_presence:
            all_positions |= s

        while uncovered:
            best_pos = None
            best_count = 0
            for d in all_positions:
                cnt = sum(1 for idx in uncovered if d in position_presence[idx])
                if cnt > best_count:
                    best_count = cnt
                    best_pos = d
            if best_pos is None or best_count == 0:
                print(f"  Cannot cover {len(uncovered)} cycles!")
                break
            cover.append((best_pos, best_count))
            uncovered = [idx for idx in uncovered if best_pos not in position_presence[idx]]
            print(f"  Add dist={best_pos:+d}: covers {best_count}, remaining uncovered: {len(uncovered)}")

        # Check coverage with just {-2, 0, +2}
        covered_by_m2_0_p2 = sum(1 for s in position_presence if s & {-2, 0, 2})
        print(f"\n  Coverage by {{-2, 0, +2}}: {covered_by_m2_0_p2}/{total_mtr} = {100.0*covered_by_m2_0_p2/total_mtr:.1f}%")
        covered_by_m1_0_p1 = sum(1 for s in position_presence if s & {-1, 0, 1})
        print(f"  Coverage by {{-1, 0, +1}}: {covered_by_m1_0_p1}/{total_mtr} = {100.0*covered_by_m1_0_p1/total_mtr:.1f}%")
        covered_by_any_neighbor = sum(1 for s in position_presence if s & {-2, -1, 0, 1, 2})
        print(f"  Coverage by {{-2,-1,0,+1,+2}}: {covered_by_any_neighbor}/{total_mtr} = {100.0*covered_by_any_neighbor/total_mtr:.1f}%")

    print(f"\nTotal time: {time.time() - t0:.1f}s")
