#!/usr/bin/env python3
"""
Anatomy of EC at left^2(t) (= LL) when MixedTightResidual has tight LL->L pair.

For each such cycle, find the EC at LL and report:
1. Which LL-mover step matches which non-mover step
2. The cycle distance between them
3. Whether the matching non-mover step is in the SAME phase or different phase
4. Whether the match is due to binary parity (even L-fires between them) or left^3(t) returning
5. Full triple decomposition at both steps

Setup: n >= 9, pivot t with m(t) >= 3, m(L) = m(R) = 2.
MTR: J=1 (one L-fire), K=1 (one R-fire) in phase.
Tight LL->L: LL fires at kLL, L fires at kLL+1.
"""

import random
from itertools import product as iterproduct
from collections import Counter, defaultdict
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
    CL = len(movers)
    fire_steps = [k for k in range(CL) if movers[k] == t]
    if len(fire_steps) < 2:
        return []
    phases = []
    for idx in range(len(fire_steps)):
        start = fire_steps[idx]
        end = fire_steps[(idx + 1) % len(fire_steps)]
        interior = []
        k = (start + 1) % CL
        while k != end:
            interior.append(k)
            k = (k + 1) % CL
        phases.append((start, interior, end))
    return phases


def classify_phase(movers, t, fire_step, interior, n):
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n
    CL = len(movers)
    J = sum(1 for k in interior if movers[k] == lt)
    K = sum(1 for k in interior if movers[k] == rt)
    tight_LL = False
    tight_RR = False
    kLL_step = None
    fL_step = None
    kRR_step = None
    fR_step = None
    for k in interior:
        if movers[k] == llt:
            k_succ = (k + 1) % CL
            if movers[k_succ] == lt:
                tight_LL = True
                kLL_step = k
                fL_step = k_succ
        if movers[k] == rrt:
            k_succ = (k + 1) % CL
            if movers[k_succ] == rt:
                tight_RR = True
                kRR_step = k
                fR_step = k_succ
    return {
        'J': J, 'K': K,
        'tight_LL': tight_LL, 'tight_RR': tight_RR,
        'kLL': kLL_step, 'fL': fL_step,
        'kRR': kRR_step, 'fR': fR_step,
    }


def is_mtr(info):
    return info['J'] == 1 and info['K'] == 1 and (info['tight_LL'] or info['tight_RR'])


def find_ec_at_proc(cycle, movers, proc, n):
    """Find all EC pairs (k1_mover, k2_nonmover) at processor proc."""
    CL = len(cycle)
    lp = (proc - 1) % n
    rp = (proc + 1) % n
    mover_triples = {}
    nonmover_triples = {}
    for k in range(CL):
        triple = (cycle[k][lp], cycle[k][proc], cycle[k][rp])
        if movers[k] == proc:
            mover_triples.setdefault(triple, []).append(k)
        else:
            nonmover_triples.setdefault(triple, []).append(k)
    pairs = []
    for triple in mover_triples:
        if triple in nonmover_triples:
            for k1 in mover_triples[triple]:
                for k2 in nonmover_triples[triple]:
                    pairs.append((k1, k2, triple))
    return pairs


def count_fires_between(movers, proc, start, end):
    """Count how many times proc fires in the cyclic interval (start, end) exclusive."""
    CL = len(movers)
    count = 0
    k = (start + 1) % CL
    while k != end:
        if movers[k] == proc:
            count += 1
        k = (k + 1) % CL
    return count


def find_phase_of_step(phases, step, CL):
    """Which phase contains a given step?"""
    for pidx, (start, interior, end) in enumerate(phases):
        if step == start:
            return pidx, 'boundary_start'
        if step == end:
            return pidx, 'boundary_end'
        for k in interior:
            if k == step:
                return pidx, 'interior'
    return -1, 'unknown'


# ─────────────────────── main ───────────────────────

if __name__ == '__main__':
    t0 = time.time()
    n = 9

    ms_configs = [
        [2, 2, 3, 2, 2, 3, 2, 2, 3],
        [3, 2, 2, 3, 2, 2, 3, 2, 2],
        [2, 3, 2, 2, 3, 2, 2, 3, 2],
    ]

    # Statistics
    total_tight_LL_phases = 0
    has_ec_at_LL = 0
    no_ec_at_LL = 0

    # Anatomy counters
    match_in_same_phase = 0
    match_in_diff_phase = 0
    match_at_kLL_step = 0  # mover step is the tight kLL itself
    match_at_other_LL_step = 0  # mover step is a different LL-firing

    # Binary parity analysis: between mover and nonmover step,
    # count fires of LL, L, left^3(t) and check parity
    L_fire_parity = Counter()  # even/odd L-fires between k1 and k2
    LL_fire_parity = Counter()
    LLL_fire_parity = Counter()

    # Distance between matching steps
    step_gap_dist = Counter()

    # Who is the mover at the non-mover step?
    nonmover_step_mover = Counter()
    nonmover_step_mover_rdist = Counter()  # relative to t

    # Triple component analysis: which components match trivially (unchanged)
    # vs match by coincidence (changed but returned)
    component_analysis = Counter()

    # Detailed examples
    examples = []

    for ms in ms_configs:
        pivots = find_sandwiched_pivots(ms, n)
        rng = random.Random(54321)

        for trial in range(400):
            f = random_transition(ms, n, rng)
            cycles = find_cycles_random(ms, n, f, max_cycles=200, rng=rng)

            for (cc, word) in cycles:
                CL = len(word)

                for t in pivots:
                    lt = (t - 1) % n
                    rt = (t + 1) % n
                    llt = (t - 2) % n  # LL
                    rrt = (t + 2) % n  # RR
                    lllt = (t - 3) % n  # LLL = left^3(t)

                    phases = get_phases(word, t)
                    for pidx, (fs, interior, end_step) in enumerate(phases):
                        info = classify_phase(word, t, fs, interior, n)
                        if not is_mtr(info) or not info['tight_LL']:
                            continue

                        total_tight_LL_phases += 1
                        kLL = info['kLL']
                        fL = info['fL']

                        # Find EC at LL
                        ec_pairs = find_ec_at_proc(cc, word, llt, n)

                        if not ec_pairs:
                            no_ec_at_LL += 1
                            if len(examples) < 5:
                                # Store a no-EC example for debugging
                                examples.append({
                                    'type': 'NO_EC',
                                    'ms': ms, 't': t, 'phase_idx': pidx,
                                    'kLL': kLL, 'fL': fL,
                                    'cycle_len': CL,
                                    'word': list(word),
                                })
                            continue

                        has_ec_at_LL += 1

                        # Analyze EACH EC pair
                        for (k1, k2, triple) in ec_pairs:
                            # k1 = LL-mover step, k2 = non-LL step
                            gap = min((k2 - k1) % CL, (k1 - k2) % CL)
                            step_gap_dist[gap] += 1

                            # Is k1 the tight kLL step?
                            if k1 == kLL:
                                match_at_kLL_step += 1
                            else:
                                match_at_other_LL_step += 1

                            # Phase membership of k2
                            p2_idx, p2_loc = find_phase_of_step(phases, k2, CL)
                            if p2_idx == pidx:
                                match_in_same_phase += 1
                            else:
                                match_in_diff_phase += 1

                            # Who moves at k2?
                            nm_mover = word[k2]
                            nonmover_step_mover[nm_mover] += 1
                            nm_rdist = ((nm_mover - t) % n)
                            if nm_rdist > n // 2:
                                nm_rdist -= n
                            nonmover_step_mover_rdist[nm_rdist] += 1

                            # Binary parity: count fires between k1 and k2
                            # (forward direction in cycle)
                            if (k2 - k1) % CL <= (k1 - k2) % CL:
                                start_interval, end_interval = k1, k2
                            else:
                                start_interval, end_interval = k2, k1

                            l_fires = count_fires_between(word, lt, start_interval, end_interval)
                            ll_fires = count_fires_between(word, llt, start_interval, end_interval)
                            lll_fires = count_fires_between(word, lllt, start_interval, end_interval)
                            L_fire_parity['even' if l_fires % 2 == 0 else 'odd'] += 1
                            LL_fire_parity['even' if ll_fires % 2 == 0 else 'odd'] += 1
                            LLL_fire_parity['even' if lll_fires % 2 == 0 else 'odd'] += 1

                            # Component analysis:
                            # triple = (config[LLL], config[LL], config[L])
                            # At k1 (LL fires): (A, B, C)
                            # At k2 (non-LL): (A', B', C') = (A, B, C)
                            # Check: did LLL change between k1 and k2? (LLL fires between them)
                            # Did L change? (L fires between them)
                            # Did LL change? (LL fires between them, must be even)
                            lll_changed = (lll_fires % (ms[lllt]) != 0)  # if non-zero fires, value may differ
                            # More precise: check actual configs
                            A1, B1, C1 = triple
                            # We know they match, so the question is WHY.
                            # "Trivial" = 0 fires of that neighbor between k1 and k2
                            # "Parity return" = even fires (binary) returning to same value
                            # "Coincidence" = fires happened but config returned anyway

                            ll_between = ll_fires
                            l_between = l_fires
                            lll_between = lll_fires

                            # LL component (binary, middle of triple)
                            if ll_between == 0:
                                ll_reason = 'zero_fires'
                            elif ll_between % 2 == 0:
                                ll_reason = 'even_return'
                            else:
                                ll_reason = 'IMPOSSIBLE'  # can't match if odd fires for binary

                            # L component (binary, right of triple)
                            if l_between == 0:
                                l_reason = 'zero_fires'
                            elif l_between % 2 == 0:
                                l_reason = 'even_return'
                            else:
                                l_reason = 'IMPOSSIBLE'

                            # LLL component (could be binary or ternary)
                            if lll_between == 0:
                                lll_reason = 'zero_fires'
                            else:
                                lll_reason = f'fires={lll_between}_returned'

                            component_analysis[(lll_reason, ll_reason, l_reason)] += 1

                            # Save first few detailed examples
                            if len(examples) < 20 and k1 == kLL:
                                examples.append({
                                    'type': 'EC',
                                    'ms': ms, 't': t, 'phase_idx': pidx,
                                    'kLL': kLL, 'fL': fL,
                                    'k1': k1, 'k2': k2, 'gap': gap,
                                    'triple': triple,
                                    'k2_mover': nm_mover,
                                    'k2_mover_rdist': nm_rdist,
                                    'k2_phase': (p2_idx, p2_loc),
                                    'L_fires_between': l_fires,
                                    'LL_fires_between': ll_fires,
                                    'LLL_fires_between': lll_fires,
                                    'reasons': (lll_reason, ll_reason, l_reason),
                                    'cycle_len': CL,
                                })

    # ─────── Report ───────
    print("=" * 70)
    print("EC AT LL (left^2 t) ANATOMY — tight LL->L in MTR phases")
    print("=" * 70)

    print(f"\nTotal tight_LL MTR phases: {total_tight_LL_phases}")
    print(f"  Has EC at LL: {has_ec_at_LL} ({100.0*has_ec_at_LL/max(1,total_tight_LL_phases):.1f}%)")
    print(f"  No EC at LL:  {no_ec_at_LL} ({100.0*no_ec_at_LL/max(1,total_tight_LL_phases):.1f}%)")

    print(f"\n--- Mover step identity ---")
    print(f"  Mover step IS the tight kLL: {match_at_kLL_step}")
    print(f"  Mover step is other LL-fire: {match_at_other_LL_step}")

    print(f"\n--- Phase membership of non-mover step ---")
    print(f"  Same phase as tight pair:  {match_in_same_phase}")
    print(f"  Different phase:           {match_in_diff_phase}")

    print(f"\n--- Step gap between mover and non-mover (cyclic min) ---")
    for gap in sorted(step_gap_dist.keys())[:20]:
        cnt = step_gap_dist[gap]
        print(f"  gap={gap:3d}: {cnt}")

    print(f"\n--- Who moves at the non-mover step? (ring dist from t) ---")
    for rdist in sorted(nonmover_step_mover_rdist.keys()):
        cnt = nonmover_step_mover_rdist[rdist]
        print(f"  dist={rdist:+d}: {cnt}")

    print(f"\n--- Binary parity between matched steps ---")
    print(f"  L fires:   {dict(L_fire_parity)}")
    print(f"  LL fires:  {dict(LL_fire_parity)}")
    print(f"  LLL fires: {dict(LLL_fire_parity)}")

    print(f"\n--- Component match reasons (LLL, LL, L) ---")
    for key, cnt in component_analysis.most_common(20):
        print(f"  {key}: {cnt}")

    print(f"\n--- Detailed examples ---")
    for i, ex in enumerate(examples[:15]):
        print(f"\n  Example {i}: type={ex['type']}")
        if ex['type'] == 'EC':
            print(f"    ms={ex['ms']}, t={ex['t']}, CL={ex['cycle_len']}")
            print(f"    kLL={ex['kLL']}, fL={ex['fL']}")
            print(f"    EC: k1={ex['k1']} (LL fires), k2={ex['k2']} (mover={ex['k2_mover']}, rdist={ex['k2_mover_rdist']:+d})")
            print(f"    gap={ex['gap']}, triple={ex['triple']}")
            print(f"    k2 phase: {ex['k2_phase']}")
            print(f"    Fires between: L={ex['L_fires_between']}, LL={ex['LL_fires_between']}, LLL={ex['LLL_fires_between']}")
            print(f"    Match reasons: {ex['reasons']}")
        else:
            print(f"    ms={ex['ms']}, t={ex['t']}, CL={ex['cycle_len']}")
            print(f"    kLL={ex['kLL']}, fL={ex['fL']}")
            # Print the full mover word around the tight pair
            w = ex['word']
            kLL = ex['kLL']
            CL = ex['cycle_len']
            context = [(k % CL, w[k % CL]) for k in range(kLL - 3, kLL + 5)]
            print(f"    Mover word context around kLL: {context}")

    print(f"\nTime: {time.time() - t0:.1f}s")
