#!/usr/bin/env python3
"""
Investigate WHERE entry conflicts occur in cycles with MixedTightResidual phases.

For good cycles that have MTR phases at some pivot t (J=1, K=1, tight LL or RR),
find ALL entry conflicts and classify by:
  - Which processor i has the conflict
  - Ring distance from i to the pivot t
  - Whether i is binary or ternary
  - Position type relative to t

Uses random transition functions + random walks to find good cycles at n=9.
"""

import random
from itertools import product as iterproduct
from collections import defaultdict, Counter
import time

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


def find_cycles_random(ms, n, f, max_cycles=500, rng=None):
    """Find good cycles via random walks."""
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

    return {
        'J': J, 'K': K,
        'tight_LL': tight_LL, 'tight_RR': tight_RR,
    }


def is_mtr(info):
    return info['J'] == 1 and info['K'] == 1 and (info['tight_LL'] or info['tight_RR'])


# ─────────────────────── EC finding ───────────────────────

def find_all_entry_conflicts(cycle, movers, ms, n):
    """Find all (k1, k2, i) where k1 is mover step at i, k2 is non-mover step at i,
    and boundary triples match."""
    ecs = []
    L = len(cycle)
    for i in range(n):
        mover_triples = {}  # triple -> list of steps
        nonmover_triples = {}
        for k in range(L):
            lp = (i - 1) % n
            rp = (i + 1) % n
            triple = (cycle[k][lp], cycle[k][i], cycle[k][rp])
            if movers[k] == i:
                mover_triples.setdefault(triple, []).append(k)
            else:
                nonmover_triples.setdefault(triple, []).append(k)
        for triple in mover_triples:
            if triple in nonmover_triples:
                for k1 in mover_triples[triple]:
                    for k2 in nonmover_triples[triple]:
                        ecs.append((k1, k2, i))
    return ecs


def ring_distance(i, t, n):
    """Signed ring distance from t to i (shortest path)."""
    d1 = (i - t) % n
    d2 = (t - i) % n
    if d1 <= d2:
        return d1
    else:
        return -d2


def ring_dist_unsigned(i, t, n):
    d1 = (i - t) % n
    d2 = (t - i) % n
    return min(d1, d2)


def position_label(i, t, n):
    """Label i's position relative to t on the ring."""
    d = ring_distance(i, t, n)
    if d == 0:
        return "t"
    prefix = "right" if d > 0 else "left"
    ad = abs(d)
    if ad == 1:
        return prefix
    return f"{prefix}^{ad}"


# ─────────────────────── main investigation ───────────────────────

def run_investigation(ms_list, n, num_trials=200, max_cycles_per_trial=200):
    print(f"\n{'='*70}")
    print(f"n={n}, state vectors: {len(ms_list)}")
    print(f"{'='*70}")

    # Global statistics
    total_mtr_cycles = 0
    total_ecs = 0
    ec_by_signed_dist = Counter()
    ec_by_unsigned_dist = Counter()
    ec_by_position = Counter()
    ec_by_proc_type = Counter()  # binary vs ternary
    ec_proc_is_pivot = 0
    ec_proc_is_binary_neighbor = 0
    mover_at_ec = Counter()
    step_gap_dist = Counter()

    # Per-pivot: which position has EC?
    ec_positions_per_pivot = defaultdict(Counter)

    for ms in ms_list:
        product_val = 1
        for m in ms:
            product_val *= m
        threshold = 4 * (3 ** (n - 2))
        if product_val >= threshold:
            continue

        pivots = find_sandwiched_pivots(ms, n)
        if not pivots:
            continue

        label = f"ms={ms}, prod={product_val}"
        print(f"\n--- {label} ---")
        print(f"  Pivots: {pivots}")

        mtr_cycles_this = 0
        ecs_this = 0
        rng = random.Random(12345)

        for trial in range(num_trials):
            f = random_transition(ms, n, rng)
            cycles = find_cycles_random(ms, n, f, max_cycles=max_cycles_per_trial, rng=rng)

            for (cc, word) in cycles:
                # Check for MTR phases
                mtr_pivots_in_cycle = []
                for t in pivots:
                    phases = get_phases(word, t)
                    for (fs, interior) in phases:
                        info = classify_phase(word, t, fs, interior, n)
                        if is_mtr(info):
                            mtr_pivots_in_cycle.append((t, fs, interior, info))

                if not mtr_pivots_in_cycle:
                    continue

                mtr_cycles_this += 1
                total_mtr_cycles += 1

                # Find ALL entry conflicts in this cycle
                ecs = find_all_entry_conflicts(cc, word, ms, n)

                if not ecs:
                    continue  # no EC in this MTR cycle (interesting if it happens)

                # For each MTR pivot in this cycle, classify each EC
                for (t, fs, interior, info) in mtr_pivots_in_cycle:
                    for (k1, k2, i) in ecs:
                        total_ecs += 1
                        ecs_this += 1

                        sd = ring_distance(i, t, n)
                        ud = ring_dist_unsigned(i, t, n)
                        pos = position_label(i, t, n)
                        ptype = "binary" if ms[i] == 2 else f"ternary({ms[i]})"

                        ec_by_signed_dist[sd] += 1
                        ec_by_unsigned_dist[ud] += 1
                        ec_by_position[pos] += 1
                        ec_by_proc_type[ptype] += 1
                        ec_positions_per_pivot[t][pos] += 1

                        if i == t:
                            ec_proc_is_pivot += 1
                        if i == (t - 1) % n or i == (t + 1) % n:
                            ec_proc_is_binary_neighbor += 1

                        # What is the mover at the EC steps?
                        mover_at_ec[f"mover_step_mover={word[k1]}"] += 1
                        mover_at_ec[f"nonmover_step_mover={word[k2]}"] += 1

                        # Step gap
                        L = len(word)
                        gap = min((k2 - k1) % L, (k1 - k2) % L)
                        step_gap_dist[gap] += 1

        print(f"  MTR cycles found: {mtr_cycles_this}")
        print(f"  Total ECs in MTR cycles: {ecs_this}")

    # ─────── Summary ───────
    print(f"\n{'='*70}")
    print(f"SUMMARY")
    print(f"{'='*70}")
    print(f"Total MTR cycles: {total_mtr_cycles}")
    print(f"Total EC instances (pivot x EC pairs): {total_ecs}")

    if total_ecs == 0:
        print("No ECs found in MTR cycles!")
        return

    print(f"\n--- EC processor signed ring distance from pivot ---")
    for d in sorted(ec_by_signed_dist.keys()):
        cnt = ec_by_signed_dist[d]
        pct = 100.0 * cnt / total_ecs
        print(f"  dist={d:+d}: {cnt:6d} ({pct:5.1f}%)")

    print(f"\n--- EC processor unsigned ring distance from pivot ---")
    for d in sorted(ec_by_unsigned_dist.keys()):
        cnt = ec_by_unsigned_dist[d]
        pct = 100.0 * cnt / total_ecs
        print(f"  dist={d}: {cnt:6d} ({pct:5.1f}%)")

    print(f"\n--- EC processor position label ---")
    for pos in sorted(ec_by_position.keys(), key=lambda x: (len(x), x)):
        cnt = ec_by_position[pos]
        pct = 100.0 * cnt / total_ecs
        print(f"  {pos:12s}: {cnt:6d} ({pct:5.1f}%)")

    print(f"\n--- EC processor type ---")
    for ptype, cnt in ec_by_proc_type.most_common():
        pct = 100.0 * cnt / total_ecs
        print(f"  {ptype:15s}: {cnt:6d} ({pct:5.1f}%)")

    print(f"\n--- EC at pivot itself: {ec_proc_is_pivot} ({100.0*ec_proc_is_pivot/total_ecs:.1f}%)")
    print(f"--- EC at binary neighbor of pivot: {ec_proc_is_binary_neighbor} ({100.0*ec_proc_is_binary_neighbor/total_ecs:.1f}%)")

    print(f"\n--- Movers at EC steps ---")
    for k, cnt in mover_at_ec.most_common(20):
        print(f"  {k}: {cnt}")

    print(f"\n--- Step gap between EC mover/non-mover steps ---")
    for gap in sorted(step_gap_dist.keys())[:20]:
        cnt = step_gap_dist[gap]
        pct = 100.0 * cnt / total_ecs
        print(f"  gap={gap:3d}: {cnt:6d} ({pct:5.1f}%)")

    # Check: is there a SPECIFIC position that ALWAYS has EC?
    print(f"\n--- Per-pivot position breakdown ---")
    for t in sorted(ec_positions_per_pivot.keys()):
        print(f"  Pivot t={t}:")
        for pos, cnt in ec_positions_per_pivot[t].most_common():
            print(f"    {pos}: {cnt}")


def run_focused_mtr_analysis(ms, n, num_trials=300, max_cycles=300):
    """Focused: for each MTR cycle, check if EVERY such cycle has EC,
    and at which SPECIFIC processor."""
    print(f"\n{'='*70}")
    print(f"FOCUSED ANALYSIS: ms={ms}, n={n}")
    print(f"{'='*70}")

    pivots = find_sandwiched_pivots(ms, n)
    print(f"Pivots: {pivots}")

    total_mtr = 0
    mtr_with_ec = 0
    mtr_without_ec = 0

    # For cycles WITH EC: which procs have it?
    ec_procs_relative = Counter()  # (signed_dist, proc_type) -> count
    # For each cycle: set of procs with EC
    all_ec_proc_sets = []

    # Track: is there a proc that has EC in EVERY MTR cycle?
    # We'll collect the set of EC procs per cycle
    universal_ec_positions = None  # intersection

    rng = random.Random(99999)
    for trial in range(num_trials):
        f = random_transition(ms, n, rng)
        cycles = find_cycles_random(ms, n, f, max_cycles=max_cycles, rng=rng)

        for (cc, word) in cycles:
            for t in pivots:
                phases = get_phases(word, t)
                for (fs, interior) in phases:
                    info = classify_phase(word, t, fs, interior, n)
                    if not is_mtr(info):
                        continue

                    total_mtr += 1
                    ecs = find_all_entry_conflicts(cc, word, ms, n)

                    if ecs:
                        mtr_with_ec += 1
                        ec_procs = set()
                        for (k1, k2, i) in ecs:
                            sd = ring_distance(i, t, n)
                            ptype = "B" if ms[i] == 2 else "T"
                            ec_procs_relative[(sd, ptype)] += 1
                            ec_procs.add((sd, ptype))
                        all_ec_proc_sets.append(ec_procs)

                        if universal_ec_positions is None:
                            universal_ec_positions = ec_procs.copy()
                        else:
                            universal_ec_positions &= ec_procs
                    else:
                        mtr_without_ec += 1
                        all_ec_proc_sets.append(set())
                        if universal_ec_positions is not None:
                            universal_ec_positions = set()

    print(f"\nTotal MTR phase instances: {total_mtr}")
    print(f"  with EC: {mtr_with_ec} ({100.0*mtr_with_ec/max(1,total_mtr):.1f}%)")
    print(f"  without EC: {mtr_without_ec}")

    if mtr_with_ec > 0:
        print(f"\n--- EC proc positions relative to pivot (signed dist, type) ---")
        for (sd, pt), cnt in sorted(ec_procs_relative.items()):
            pct = 100.0 * cnt / mtr_with_ec
            print(f"  dist={sd:+d} ({pt}): {cnt:5d} ({pct:5.1f}%)")

        print(f"\n--- Universal EC position (present in ALL MTR cycles with EC) ---")
        if universal_ec_positions:
            print(f"  YES: {universal_ec_positions}")
        else:
            print(f"  NO universal position (intersection is empty)")

        # Check: which positions appear in >=90% of cycles?
        print(f"\n--- High-frequency EC positions (>=80% of MTR-with-EC cycles) ---")
        position_freq = Counter()
        for s in all_ec_proc_sets:
            for pos in s:
                position_freq[pos] += 1
        for pos, cnt in position_freq.most_common():
            pct = 100.0 * cnt / mtr_with_ec
            if pct >= 50:
                print(f"  {pos}: {cnt}/{mtr_with_ec} = {pct:.1f}%")

    return total_mtr, mtr_with_ec, mtr_without_ec


def run_tight_pattern_detail(ms, n, num_trials=200, max_cycles=200):
    """For MTR cycles with specific tight pattern LL->L->...->RR->R:
    what is the mover at the EC step? The matching non-mover step mover?"""
    print(f"\n{'='*70}")
    print(f"TIGHT PATTERN DETAIL: ms={ms}, n={n}")
    print(f"{'='*70}")

    pivots = find_sandwiched_pivots(ms, n)
    rng = random.Random(77777)

    mover_at_conflict = Counter()
    nonmover_mover_at_conflict = Counter()
    ec_proc_detail = []

    for trial in range(num_trials):
        f = random_transition(ms, n, rng)
        cycles = find_cycles_random(ms, n, f, max_cycles=max_cycles, rng=rng)

        for (cc, word) in cycles:
            for t in pivots:
                lt = (t - 1) % n
                rt = (t + 1) % n
                llt = (t - 2) % n
                rrt = (t + 2) % n

                phases = get_phases(word, t)
                for (fs, interior) in phases:
                    info = classify_phase(word, t, fs, interior, n)
                    if not is_mtr(info):
                        continue

                    # Check tight pattern: LL immediately before L, and/or RR immediately before R
                    L = len(word)
                    tight_left = info['tight_LL']
                    tight_right = info['tight_RR']

                    ecs = find_all_entry_conflicts(cc, word, ms, n)
                    for (k1, k2, i) in ecs:
                        sd = ring_distance(i, t, n)
                        mover_at_conflict[f"ec_proc_dist={sd:+d}, mover_at_k1={word[k1]}(dist={ring_distance(word[k1],t,n):+d})"] += 1
                        nonmover_mover_at_conflict[f"ec_proc_dist={sd:+d}, mover_at_k2={word[k2]}(dist={ring_distance(word[k2],t,n):+d})"] += 1
                        ec_proc_detail.append({
                            'pivot': t,
                            'ec_proc': i,
                            'ec_dist': sd,
                            'mover_k1': word[k1],
                            'mover_k2': word[k2],
                            'tight_left': tight_left,
                            'tight_right': tight_right,
                        })

    print(f"\nTotal EC instances: {len(ec_proc_detail)}")
    if ec_proc_detail:
        print(f"\n--- Mover at EC mover-step (top 15) ---")
        for k, cnt in mover_at_conflict.most_common(15):
            print(f"  {k}: {cnt}")

        print(f"\n--- Mover at EC non-mover-step (top 15) ---")
        for k, cnt in nonmover_mover_at_conflict.most_common(15):
            print(f"  {k}: {cnt}")

        # Summarize: when tight_left, where is EC? When tight_right?
        tight_left_dists = Counter()
        tight_right_dists = Counter()
        for d in ec_proc_detail:
            if d['tight_left']:
                tight_left_dists[d['ec_dist']] += 1
            if d['tight_right']:
                tight_right_dists[d['ec_dist']] += 1

        print(f"\n--- When tight_LL (left): EC proc distance distribution ---")
        for dist, cnt in sorted(tight_left_dists.items()):
            print(f"  dist={dist:+d}: {cnt}")

        print(f"\n--- When tight_RR (right): EC proc distance distribution ---")
        for dist, cnt in sorted(tight_right_dists.items()):
            print(f"  dist={dist:+d}: {cnt}")


# ─────────────────────── main ───────────────────────

if __name__ == '__main__':
    t0 = time.time()
    n = 9

    # State vectors with sandwiched ternary pivots and sub-threshold product
    # threshold = 4 * 3^7 = 8748
    ms_list = [
        [2, 2, 3, 2, 2, 3, 2, 2, 3],  # 3 pivots at 2,5,8
        [3, 2, 2, 3, 2, 2, 3, 2, 2],  # rotated
        [2, 3, 2, 2, 3, 2, 2, 3, 2],  # another rotation
        [2, 2, 2, 3, 2, 2, 3, 2, 3],  # asymmetric
        [2, 2, 3, 2, 3, 2, 2, 3, 2],  # different spacing
    ]

    # Filter to sub-threshold
    threshold = 4 * (3 ** (n - 2))
    ms_sub = []
    for ms in ms_list:
        prod = 1
        for m in ms:
            prod *= m
        if prod < threshold:
            ms_sub.append(ms)
        else:
            print(f"Skipping ms={ms} (prod={prod} >= {threshold})")

    # Phase 1: broad investigation
    run_investigation(ms_sub, n, num_trials=150, max_cycles_per_trial=150)

    # Phase 2: focused per-state-vector
    for ms in ms_sub[:3]:
        run_focused_mtr_analysis(ms, n, num_trials=200, max_cycles=200)

    # Phase 3: tight pattern detail
    for ms in ms_sub[:2]:
        run_tight_pattern_detail(ms, n, num_trials=150, max_cycles=150)

    print(f"\nTotal time: {time.time() - t0:.1f}s")
