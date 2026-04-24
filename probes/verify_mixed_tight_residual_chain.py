"""
Verify the MixedTightResidual 6-lemma domino chain computationally.

Three checks:
  C1 (Propagation): MTR at pivot t => MTR at adjacent pivot t' = right^3(t)
  C2 (Order flip): The shared binary pair fires in opposite order at t vs t'
  C3 (Even-k half-cycle overlap): After k/2 steps, boundary triple repeats => EC

Strategy: enumerate ALL good cycles by exhaustive graph search on the full
transition graph for small state spaces. Use state vectors with multiple
sandwiched ternary pivots and products near the sub-threshold boundary.
"""

import random
from itertools import product as iterproduct
from collections import defaultdict, deque
import time
import sys

# ─────────────────────── core helpers ───────────────────────

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


def all_configs(ms):
    return list(iterproduct(*[range(m) for m in ms]))


def find_all_good_cycles_exhaustive(ms, n, f, max_cycles=5000):
    """Find ALL good cycles by building the full transition graph and finding cycles.
    For each config, try each processor as mover. Build directed graph.
    Then find all simple cycles using DFS."""
    configs = all_configs(ms)
    total = len(configs)

    # Build successor map: config -> list of (new_config, mover)
    succ = {}
    for c in configs:
        succs = []
        for p in range(n):
            nc = apply_move(c, p, f, n)
            if nc != c:  # only actual moves
                succs.append((nc, p))
        succ[c] = succs

    # Find cycles via random walks from many starting points (exhaustive BFS is too slow)
    # Instead: for each config, do DFS with limited depth
    cycles = []
    seen_cycle_ids = set()

    # Method: long random walks, collect all cycles found
    rng = random.Random(12345)
    for start_idx in range(min(total, 2000)):
        start = configs[start_idx] if start_idx < total else configs[rng.randint(0, total - 1)]
        # Multiple random walks from this start
        for walk in range(10):
            config = start
            history = [config]
            config_to_step = {config: 0}
            for step in range(1, 500):
                nbrs = succ[config]
                if not nbrs:
                    break
                nc, mover = nbrs[rng.randint(0, len(nbrs) - 1)]
                if nc in config_to_step:
                    cs = config_to_step[nc]
                    cc = history[cs:]
                    if len(cc) >= n:
                        # Extract movers
                        movers = []
                        ok = True
                        for i in range(len(cc)):
                            c1 = cc[i]
                            c2_idx = (i + 1) % len(cc)
                            c2 = cc[c2_idx] if c2_idx > 0 else nc
                            if i == len(cc) - 1:
                                c2 = nc  # the config we reconnected to
                            mv = None
                            for q in range(n):
                                if c1[q] != c2[q]:
                                    if mv is not None:
                                        ok = False
                                        break
                                    mv = q
                            if not ok or mv is None:
                                ok = False
                                break
                            movers.append(mv)
                        if ok:
                            cid = frozenset(cc)
                            if cid not in seen_cycle_ids:
                                seen_cycle_ids.add(cid)
                                cycles.append((list(cc), movers))
                                if len(cycles) >= max_cycles:
                                    return cycles
                    break
                history.append(nc)
                config_to_step[nc] = step
                config = nc

    return cycles


def find_cycles_aggressive(ms, n, f, max_cycles=2000):
    """Aggressive cycle finding: multiple strategies."""
    cycles = []
    seen = set()

    configs = all_configs(ms)
    total = len(configs)

    # Strategy 1: random walks with random mover
    rng = random.Random(42)
    for trial in range(min(total * 3, 20000)):
        start = configs[rng.randint(0, total - 1)]
        config = start
        history = [config]
        config_to_step = {config: 0}
        for step in range(1, 800):
            # Try random mover
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

    # Strategy 2: deterministic "round-robin" mover selection
    for start in configs[:min(total, 3000)]:
        config = start
        history = [config]
        config_to_step = {config: 0}
        mover_idx = 0
        for step in range(1, 300):
            p = mover_idx % n
            mover_idx += 1
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


# ─────────────────────── phase / MTR analysis ───────────────────────

def find_sandwiched_pivots(ms, n):
    pivots = []
    for t in range(n):
        lt = (t - 1) % n
        rt = (t + 1) % n
        if ms[t] >= 3 and ms[lt] == 2 and ms[rt] == 2:
            pivots.append(t)
    return pivots


def get_phases(movers, t):
    """Return phases at pivot t: list of (fire_step, interior_steps)."""
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

    L_fires = [k for k in interior if movers[k] == lt]
    R_fires = [k for k in interior if movers[k] == rt]
    LL_fires = [k for k in interior if movers[k] == llt]
    RR_fires = [k for k in interior if movers[k] == rrt]

    return {
        'J': J, 'K': K,
        'tight_LL': tight_LL, 'tight_RR': tight_RR,
        'L_fires': L_fires, 'R_fires': R_fires,
        'LL_fires': LL_fires, 'RR_fires': RR_fires,
    }


def is_mtr(info):
    return info['J'] == 1 and info['K'] == 1 and (info['tight_LL'] or info['tight_RR'])


# ─────────────────────── Check implementations ───────────────────────

def check_propagation_one(cc, movers, ms, n, pivots, t, fire_step, interior, info):
    """Check propagation from one MTR phase at pivot t."""
    L = len(movers)
    results = []

    for direction in ['right', 'left']:
        if direction == 'right' and not info['tight_RR']:
            continue
        if direction == 'left' and not info['tight_LL']:
            continue

        if direction == 'right':
            t_prime = (t + 3) % n
            # The R-fire in this phase = left^2(t') fire
            shared_fire = info['R_fires'][0]
        else:
            t_prime = (t - 3) % n
            # The L-fire in this phase = right^2(t') fire
            shared_fire = info['L_fires'][0]

        if t_prime not in pivots:
            results.append({'dir': direction, 'tp': t_prime, 'result': 'not_pivot'})
            continue

        # Find t''s phase containing shared_fire
        phases_tp = get_phases(movers, t_prime)
        found = None
        for (fs_tp, int_tp) in phases_tp:
            if shared_fire in int_tp:
                info_tp = classify_phase(movers, t_prime, fs_tp, int_tp, n)
                found = (fs_tp, int_tp, info_tp)
                break

        if found is None:
            results.append({'dir': direction, 'tp': t_prime, 'result': 'not_in_interior'})
            continue

        if is_mtr(found[2]):
            results.append({'dir': direction, 'tp': t_prime, 'result': 'propagated', 'tp_info': found[2]})
        else:
            results.append({'dir': direction, 'tp': t_prime, 'result': 'not_mtr', 'tp_info': found[2]})

    return results


def check_order_flip_one(cc, movers, ms, n, t, info, t_prime, direction):
    """Check order flip between MTR at t and propagated MTR at t'."""
    L = len(movers)
    rt = (t + 1) % n
    rrt = (t + 2) % n

    if direction == 'right':
        # At t: tight_RR means rrt fires before rt
        rr_step = info['RR_fires'][0]
        r_step = info['R_fires'][0]

        # Verify order within the phase interior
        # (We just need to check rr_step comes before r_step in the interior ordering)
        # Since tight_RR means rrt fires immediately before rt, rr_step < r_step (cyclically in phase)

        # At t': left t' = rrt, left^2 t' = rt
        # In t''s phase, the fires of rt and rrt should be in the interior
        r_fire = info['R_fires'][0]  # the shared fire (rt fires here)
        phases_tp = get_phases(movers, t_prime)
        for (fs_tp, int_tp) in phases_tp:
            if r_fire in int_tp:
                info_tp = classify_phase(movers, t_prime, fs_tp, int_tp, n)
                if not is_mtr(info_tp):
                    return None

                # At t': LL_fires are fires of left^2(t') = rt
                # L_fires are fires of left(t') = rrt
                if not info_tp['LL_fires'] or not info_tp['L_fires']:
                    return None

                ll_step_tp = info_tp['LL_fires'][0]  # rt fire in t' phase
                l_step_tp = info_tp['L_fires'][0]    # rrt fire in t' phase

                # Get order within interior
                int_map = {k: i for i, k in enumerate(int_tp)}
                if ll_step_tp not in int_map or l_step_tp not in int_map:
                    return None

                # At t: rrt fires before rt (tight RR → RR before R)
                # At t': rt fires before rrt? (LL' before L' where LL'=rt, L'=rrt)
                order_tp = 'rt_before_rrt' if int_map[ll_step_tp] < int_map[l_step_tp] else 'rrt_before_rt'

                flipped = (order_tp == 'rt_before_rrt')  # At t: rrt before rt. At t': rt before rrt.
                return {'flipped': flipped, 'order_t': 'rrt_before_rt', 'order_tp': order_tp}

    elif direction == 'left':
        lt = (t - 1) % n
        llt = (t - 2) % n
        # At t: tight_LL means llt fires before lt
        l_fire = info['L_fires'][0]
        phases_tp = get_phases(movers, t_prime)
        for (fs_tp, int_tp) in phases_tp:
            if l_fire in int_tp:
                info_tp = classify_phase(movers, t_prime, fs_tp, int_tp, n)
                if not is_mtr(info_tp):
                    return None
                # At t': right t' = llt, right^2 t' = lt
                if not info_tp['RR_fires'] or not info_tp['R_fires']:
                    return None
                rr_step_tp = info_tp['RR_fires'][0]  # lt fire
                r_step_tp = info_tp['R_fires'][0]     # llt fire
                int_map = {k: i for i, k in enumerate(int_tp)}
                if rr_step_tp not in int_map or r_step_tp not in int_map:
                    return None
                # At t: llt before lt. At t': lt before llt?
                order_tp = 'lt_before_llt' if int_map[rr_step_tp] < int_map[r_step_tp] else 'llt_before_lt'
                flipped = (order_tp == 'lt_before_llt')
                return {'flipped': flipped, 'order_t': 'llt_before_lt', 'order_tp': order_tp}

    return None


def find_entry_conflicts(cc, movers, n):
    """Find all entry conflicts: same boundary triple at mover vs non-mover step."""
    L = len(cc)
    ecs = []
    for q in range(n):
        lq = (q - 1) % n
        rq = (q + 1) % n
        mover_triples = {}
        nonmover_triples = {}
        for k in range(L):
            triple = (cc[k][lq], cc[k][q], cc[k][rq])
            if movers[k] == q:
                mover_triples.setdefault(triple, []).append(k)
            else:
                nonmover_triples.setdefault(triple, []).append(k)
        for tr in set(mover_triples) & set(nonmover_triples):
            for k1 in mover_triples[tr]:
                for k2 in nonmover_triples[tr]:
                    ecs.append((q, k1, k2, tr))
    return ecs


# ─────────────────────── Main analysis ───────────────────────

def run_analysis(ms, n, num_trials, label):
    print(f"\n{'='*70}")
    print(f"  {label}")
    print(f"  ms = {ms}, n = {n}")
    prod = 1
    for m in ms: prod *= m
    thresh = 4 * 3**(n-2)
    print(f"  product = {prod}, threshold = {thresh}, sub-threshold = {prod < thresh}")
    print(f"{'='*70}")

    pivots = find_sandwiched_pivots(ms, n)
    print(f"Sandwiched ternary pivots: {pivots} (k={len(pivots)})")

    total_configs = prod
    print(f"Total configs: {total_configs}")

    stats = {
        'cycles': 0, 'phases_checked': 0, 'mtr_phases': 0,
        'c1_tested': 0, 'c1_propagated': 0, 'c1_not_pivot': 0,
        'c1_not_interior': 0, 'c1_not_mtr': 0,
        'c2_tested': 0, 'c2_flipped': 0, 'c2_not_flipped': 0,
        'c3_cycles_with_ec': 0, 'c3_mtr_cycles_with_ec': 0,
        'c3_mtr_cycles_total': 0,
    }
    c1_failure_details = []
    c2_failure_details = []
    phase_type_counts = defaultdict(int)

    t0 = time.time()

    for trial in range(num_trials):
        rng = random.Random(trial * 137 + 42)
        f = random_transition(ms, n, rng)

        if total_configs <= 30000:
            cycles = find_all_good_cycles_exhaustive(ms, n, f, max_cycles=5000)
        else:
            cycles = find_cycles_aggressive(ms, n, f, max_cycles=2000)

        stats['cycles'] += len(cycles)

        for (cc, movers) in cycles:
            cycle_has_mtr = False
            cycle_has_ec = len(find_entry_conflicts(cc, movers, n)) > 0

            for t in pivots:
                phases = get_phases(movers, t)
                for (fs, interior) in phases:
                    stats['phases_checked'] += 1
                    info = classify_phase(movers, t, fs, interior, n)

                    # Track phase types
                    ptype = f"J={info['J']},K={info['K']}"
                    if info['tight_LL']: ptype += ",tLL"
                    if info['tight_RR']: ptype += ",tRR"
                    phase_type_counts[ptype] += 1

                    if not is_mtr(info):
                        continue

                    stats['mtr_phases'] += 1
                    cycle_has_mtr = True

                    # Check 1: Propagation
                    prop_results = check_propagation_one(cc, movers, ms, n, pivots, t, fs, interior, info)
                    for r in prop_results:
                        stats['c1_tested'] += 1
                        if r['result'] == 'propagated':
                            stats['c1_propagated'] += 1
                        elif r['result'] == 'not_pivot':
                            stats['c1_not_pivot'] += 1
                        elif r['result'] == 'not_in_interior':
                            stats['c1_not_interior'] += 1
                        elif r['result'] == 'not_mtr':
                            stats['c1_not_mtr'] += 1
                            if len(c1_failure_details) < 20:
                                c1_failure_details.append({
                                    'trial': trial, 'pivot': t, 'dir': r['dir'],
                                    'tp': r['tp'], 'tp_info': r.get('tp_info', {})
                                })

                    # Check 2: Order flip (for propagated pairs)
                    for r in prop_results:
                        if r['result'] == 'propagated':
                            flip = check_order_flip_one(cc, movers, ms, n, t, info, r['tp'], r['dir'])
                            if flip is not None:
                                stats['c2_tested'] += 1
                                if flip['flipped']:
                                    stats['c2_flipped'] += 1
                                else:
                                    stats['c2_not_flipped'] += 1
                                    if len(c2_failure_details) < 20:
                                        c2_failure_details.append({
                                            'trial': trial, 'pivot': t, 'dir': r['dir'],
                                            'tp': r['tp'], 'flip': flip
                                        })

            if cycle_has_mtr:
                stats['c3_mtr_cycles_total'] += 1
                if cycle_has_ec:
                    stats['c3_mtr_cycles_with_ec'] += 1
            if cycle_has_ec:
                stats['c3_cycles_with_ec'] += 1

    elapsed = time.time() - t0

    # ─── Report ───
    print(f"\nTrials: {num_trials}, Good cycles: {stats['cycles']}")
    print(f"Phases checked: {stats['phases_checked']}, MTR phases: {stats['mtr_phases']}")
    print(f"Time: {elapsed:.1f}s")

    print(f"\nPhase type distribution:")
    for ptype, count in sorted(phase_type_counts.items(), key=lambda x: -x[1]):
        print(f"  {ptype}: {count}")

    print(f"\n--- Check 1: Propagation ---")
    print(f"  Tested: {stats['c1_tested']}")
    print(f"  Propagated (MTR at t'): {stats['c1_propagated']}")
    print(f"  Adjacent not sandwiched pivot: {stats['c1_not_pivot']}")
    print(f"  Shared fire not in t' interior: {stats['c1_not_interior']}")
    print(f"  t' phase not MTR: {stats['c1_not_mtr']}")
    valid = stats['c1_tested'] - stats['c1_not_pivot']
    if valid > 0:
        print(f"  Rate (among valid adjacencies): {stats['c1_propagated']}/{valid} = {stats['c1_propagated']/valid*100:.1f}%")
    if c1_failure_details:
        print(f"  Non-MTR failure examples (first {min(10, len(c1_failure_details))}):")
        for d in c1_failure_details[:10]:
            ti = d.get('tp_info', {})
            print(f"    trial={d['trial']}, t={d['pivot']}, dir={d['dir']}, t'={d['tp']}, "
                  f"J'={ti.get('J','?')}, K'={ti.get('K','?')}, tLL'={ti.get('tight_LL','?')}, tRR'={ti.get('tight_RR','?')}")

    print(f"\n--- Check 2: Order Flip ---")
    print(f"  Tested: {stats['c2_tested']}")
    print(f"  Flipped: {stats['c2_flipped']}")
    print(f"  NOT flipped: {stats['c2_not_flipped']}")
    if stats['c2_tested'] > 0:
        print(f"  Rate: {stats['c2_flipped']}/{stats['c2_tested']} = {stats['c2_flipped']/stats['c2_tested']*100:.1f}%")
    if c2_failure_details:
        print(f"  Non-flip examples:")
        for d in c2_failure_details[:5]:
            print(f"    trial={d['trial']}, t={d['pivot']}, dir={d['dir']}, t'={d['tp']}, {d['flip']}")

    print(f"\n--- Check 3: EC in MTR cycles ---")
    print(f"  Cycles with MTR phase: {stats['c3_mtr_cycles_total']}")
    print(f"  Of those with entry conflict: {stats['c3_mtr_cycles_with_ec']}")
    if stats['c3_mtr_cycles_total'] > 0:
        print(f"  Rate: {stats['c3_mtr_cycles_with_ec']}/{stats['c3_mtr_cycles_total']} = "
              f"{stats['c3_mtr_cycles_with_ec']/stats['c3_mtr_cycles_total']*100:.1f}%")
    print(f"  (Total cycles with EC: {stats['c3_cycles_with_ec']}/{stats['cycles']})")

    print()
    return stats


# ─────────────────────── Run ───────────────────────

if __name__ == '__main__':
    print("MixedTightResidual Domino Chain Verification")
    print("=" * 70)

    # n=6, ms=(2,3,2,2,3,2) — 2 pivots, small config space (144), exhaustive
    r6 = run_analysis((2, 3, 2, 2, 3, 2), 6, num_trials=500,
                      label="n=6, ms=(2,3,2,2,3,2), 2 pivots (even)")

    # n=6, ms=(3,2,2,3,2,2) — same ring shifted
    r6b = run_analysis((3, 2, 2, 3, 2, 2), 6, num_trials=500,
                       label="n=6, ms=(3,2,2,3,2,2), 2 pivots (even)")

    # n=9, ms=(2,2,3,2,2,3,2,2,3) — 3 pivots, config space 1728
    r9 = run_analysis((2, 2, 3, 2, 2, 3, 2, 2, 3), 9, num_trials=300,
                      label="n=9, ms=(2,2,3,2,2,3,2,2,3), 3 pivots (odd)")

    # n=9, ms=(3,2,2,3,2,2,3,2,2) — shifted
    r9b = run_analysis((3, 2, 2, 3, 2, 2, 3, 2, 2), 9, num_trials=300,
                       label="n=9, ms=(3,2,2,3,2,2,3,2,2), 3 pivots (odd)")

    # n=9 with higher ternary to get longer cycles: (2,2,4,2,2,4,2,2,4)
    r9c = run_analysis((2, 2, 4, 2, 2, 4, 2, 2, 4), 9, num_trials=200,
                       label="n=9, ms=(2,2,4,2,2,4,2,2,4), 3 pivots quaternary")

    # n=12, ms=(2,2,3,2,2,3,2,2,3,2,2,3) — 4 pivots (even), config space 20736
    r12 = run_analysis((2, 2, 3, 2, 2, 3, 2, 2, 3, 2, 2, 3), 12, num_trials=100,
                       label="n=12, ms=(2,2,3,2,2,3,2,2,3,2,2,3), 4 pivots (even)")

    # ─── Grand summary ───
    print("\n" + "=" * 70)
    print("GRAND SUMMARY")
    print("=" * 70)
    all_results = [
        ("n=6 (k=2)", r6),
        ("n=6b (k=2)", r6b),
        ("n=9 (k=3)", r9),
        ("n=9b (k=3)", r9b),
        ("n=9c quat (k=3)", r9c),
        ("n=12 (k=4)", r12),
    ]
    for name, r in all_results:
        print(f"\n  {name}:")
        print(f"    Cycles={r['cycles']}, MTR phases={r['mtr_phases']}")
        v = r['c1_tested'] - r['c1_not_pivot']
        c1s = f"{r['c1_propagated']}/{v}" if v > 0 else "0/0"
        c2s = f"{r['c2_flipped']}/{r['c2_tested']}" if r['c2_tested'] > 0 else "0/0"
        c3s = f"{r['c3_mtr_cycles_with_ec']}/{r['c3_mtr_cycles_total']}" if r['c3_mtr_cycles_total'] > 0 else "0/0"
        print(f"    C1 prop: {c1s}  |  C2 flip: {c2s}  |  C3 EC-in-MTR: {c3s}")

    # ─── Detailed analysis of EC source in MTR cycles ───
    print("\n" + "=" * 70)
    print("DETAILED EC SOURCE ANALYSIS IN MTR CYCLES")
    print("=" * 70)

    # Re-run n=6 to find the 1 failure and understand EC sources
    ms6 = (2, 3, 2, 2, 3, 2)
    n6 = 6
    pivots6 = find_sandwiched_pivots(ms6, n6)
    print(f"\nAnalyzing n=6 MTR cycles for EC source...")

    ec_at_binary_count = 0
    ec_at_pivot_count = 0
    ec_at_other_count = 0
    mtr_no_ec_details = []
    mtr_ec_proc_dist = defaultdict(int)
    total_mtr_analyzed = 0

    for trial in range(500):
        rng = random.Random(trial * 137 + 42)
        f = random_transition(ms6, n6, rng)
        cycles = find_all_good_cycles_exhaustive(ms6, n6, f, max_cycles=5000)

        for (cc, movers) in cycles:
            has_mtr = False
            for t in pivots6:
                phases = get_phases(movers, t)
                for (fs, interior) in phases:
                    info = classify_phase(movers, t, fs, interior, n6)
                    if is_mtr(info):
                        has_mtr = True
                        break
                if has_mtr:
                    break

            if not has_mtr:
                continue

            total_mtr_analyzed += 1
            ecs = find_entry_conflicts(cc, movers, n6)

            if not ecs:
                mtr_no_ec_details.append({
                    'trial': trial,
                    'cycle_len': len(cc),
                    'movers': movers,
                })
                continue

            for (q, k1, k2, tr) in ecs:
                mtr_ec_proc_dist[q] += 1
                if ms6[q] == 2:
                    ec_at_binary_count += 1
                elif q in pivots6:
                    ec_at_pivot_count += 1
                else:
                    ec_at_other_count += 1

    print(f"Total MTR cycles analyzed: {total_mtr_analyzed}")
    print(f"MTR cycles WITHOUT EC: {len(mtr_no_ec_details)}")
    print(f"\nEC processor distribution in MTR cycles:")
    for q in sorted(mtr_ec_proc_dist.keys()):
        label = "binary" if ms6[q] == 2 else ("PIVOT" if q in pivots6 else "ternary")
        print(f"  proc {q} ({label}, m={ms6[q]}): {mtr_ec_proc_dist[q]} ECs")
    print(f"\nEC at binary procs: {ec_at_binary_count}")
    print(f"EC at pivot procs: {ec_at_pivot_count}")
    print(f"EC at other procs: {ec_at_other_count}")

    if mtr_no_ec_details:
        print(f"\nNo-EC MTR cycle details:")
        for d in mtr_no_ec_details[:5]:
            print(f"  trial={d['trial']}, len={d['cycle_len']}, movers={d['movers']}")

    # ─── Check: does tight pair ITSELF create the EC? ───
    print(f"\n{'='*70}")
    print("TIGHT PAIR EC SOURCE CHECK")
    print("For MTR phases, does the tight LL->L or RR->R pair directly cause EC?")
    print("=" * 70)

    tight_is_ec_source = 0
    tight_not_ec_source = 0

    for trial in range(200):
        rng = random.Random(trial * 137 + 42)
        f = random_transition(ms6, n6, rng)
        cycles = find_all_good_cycles_exhaustive(ms6, n6, f, max_cycles=2000)

        for (cc, movers) in cycles:
            for t in pivots6:
                phases = get_phases(movers, t)
                for (fs, interior) in phases:
                    info = classify_phase(movers, t, fs, interior, n6)
                    if not is_mtr(info):
                        continue

                    # For tight_RR: RR fires at step k, R fires at step k+1
                    # Check if there's an EC at R (right t) involving the R-fire step
                    rt = (t + 1) % n6
                    rrt = (t + 2) % n6
                    lrt = (rt - 1) % n6  # = t
                    rrt_of_rt = (rt + 1) % n6  # = rrt

                    if info['tight_RR'] and info['RR_fires'] and info['R_fires']:
                        rr_step = info['RR_fires'][0]
                        r_step = info['R_fires'][0]
                        # At step rr_step: movers[rr_step] = rrt, so rt is non-mover
                        # At step r_step: movers[r_step] = rt, so rt is mover
                        # EC at rt if boundary triple matches: (c[t], c[rt], c[rrt])
                        triple_rr = (cc[rr_step][lrt], cc[rr_step][rt], cc[rr_step][rrt_of_rt])
                        triple_r = (cc[r_step][lrt], cc[r_step][rt], cc[r_step][rrt_of_rt])
                        if triple_rr == triple_r:
                            tight_is_ec_source += 1
                        else:
                            tight_not_ec_source += 1

                    if info['tight_LL'] and info['LL_fires'] and info['L_fires']:
                        lt = (t - 1) % n6
                        llt = (t - 2) % n6
                        ll_step = info['LL_fires'][0]
                        l_step = info['L_fires'][0]
                        llt_of_lt = (lt - 1) % n6  # = llt
                        rlt = (lt + 1) % n6  # = t
                        triple_ll = (cc[ll_step][llt_of_lt], cc[ll_step][lt], cc[ll_step][rlt])
                        triple_l = (cc[l_step][llt_of_lt], cc[l_step][lt], cc[l_step][rlt])
                        if triple_ll == triple_l:
                            tight_is_ec_source += 1
                        else:
                            tight_not_ec_source += 1

    print(f"Tight pair IS direct EC source: {tight_is_ec_source}")
    print(f"Tight pair is NOT direct EC source: {tight_not_ec_source}")
    if tight_is_ec_source + tight_not_ec_source > 0:
        rate = tight_is_ec_source / (tight_is_ec_source + tight_not_ec_source)
        print(f"Rate: {rate*100:.1f}%")

    print("\n" + "=" * 70)
    print("VERIFICATION COMPLETE")
    print("=" * 70)
