#!/usr/bin/env python3
"""
Round 2: Deeper anatomy of EC at LL.

Key findings from round 1:
- 96.1% of tight_LL MTR phases have EC at LL
- Dominant pattern: zero_fires for ALL 3 components (3943/5604 = 70%)
- 1051 "IMPOSSIBLE" cases for LL (odd fires). This means binary ISN'T toggle!
  Actually: binary f(L,S,R) can map S -> S (no change). "Firing" means mover=LL,
  but config[LL] might not change. Let me check this.
  Wait, in a good cycle: config changes at every step. So moverAt(k) = LL means
  config[LL] DID change. For binary: 0->1 or 1->0. So odd fires MUST toggle.
  Unless... the mover count between k1 and k2 includes k1 or k2 itself?

Let me recheck: count_fires_between counts fires in (start, end) EXCLUSIVE.
If k1 < k2 and start_interval = k1: we count fires in (k1, k2) exclusive,
so we DON'T count k1 (which is an LL-mover step) or k2.
LL fires between k1 and k2 (exclusive): if odd, config[LL] toggled.
But k1 sees config BEFORE k1's firing. k2 sees config at k2.
config[LL] at k2 = config[LL] at k1 XOR (fires in [k1, k2)).
Fires in [k1, k2) = 1 (k1 itself) + fires in (k1, k2).
So config[LL] at k2 = config[LL] at k1 XOR (1 + count_between).
For match: need XOR = 0, so 1 + count_between must be even, so count_between is ODD.

AH! That's the fix. For LL (the mover at k1):
  config[LL] at k2 = config[LL] at k1 XOR (1 + LL_fires_between)
  For match: 1 + LL_fires_between = even => LL_fires_between = odd

For L (non-mover at both k1 and k2):
  config[L] at k2 = config[L] at k1 XOR (L_fires_between)
  For match: L_fires_between = even (including 0)

For LLL:
  config[LLL] at k2: depends on fires. If binary: LLL_fires_between even.
  If ternary: need to return to same value.

So the "IMPOSSIBLE" for LL was actually EXPECTED: odd fires between = correct
because of the +1 from k1's own firing.

Let me redo the analysis with correct parity logic.
Also: analyze the 39 no-EC-at-LL cases more carefully.
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
    return {
        'J': J, 'K': K,
        'tight_LL': tight_LL, 'tight_RR': tight_RR,
        'kLL': kLL_step, 'fL': fL_step,
    }


def is_mtr(info):
    return info['J'] == 1 and info['K'] == 1 and (info['tight_LL'] or info['tight_RR'])


def find_ec_at_proc(cycle, movers, proc, n):
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


def find_all_ec_procs(cycle, movers, ms, n):
    ec_procs = set()
    CL = len(cycle)
    for i in range(n):
        mover_triples = set()
        nonmover_triples = set()
        for k in range(CL):
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


def count_fires_between(movers, proc, start, end):
    """Count fires of proc in cyclic interval (start, end) exclusive of both endpoints."""
    CL = len(movers)
    count = 0
    k = (start + 1) % CL
    while k != end:
        if movers[k] == proc:
            count += 1
        k = (k + 1) % CL
    return count


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

    # Focus 1: zero_fires pattern - the non-mover step k2 is BEFORE kLL
    # with NO fires of LL, L, or LLL between them.
    # This means k2 is in the "quiet zone" before kLL where none of {LLL, LL, L} fire.

    # Focus 2: What happens in the 39 no-EC-at-LL cases?

    total_tight_LL = 0
    has_ec_at_LL = 0
    no_ec_at_LL = 0

    # For the zero_fires pattern: where is k2 relative to kLL?
    k2_before_kLL = 0  # k2 < kLL in phase ordering
    k2_after_kLL = 0

    # For zero_fires at kLL: what's the gap-1 pattern?
    # The non-mover step is the step RIGHT BEFORE kLL
    gap1_count = 0
    gap1_mover_rdist = Counter()

    # For the kLL match specifically: which step is the nearest non-mover match?
    nearest_match_gap = Counter()

    # Corrected parity analysis
    correct_parity = Counter()  # (LL_correct, L_correct, LLL_correct)

    # No-EC examples: full detail
    no_ec_examples = []

    # The key construction: at step kLL, LL fires.
    # The step JUST BEFORE kLL (call it kLL-1): what happens?
    # If mover at kLL-1 is NOT in {LLL, LL, L}: boundary triple at LL is unchanged.
    # So triple at kLL = triple at kLL-1. k1=kLL (mover), k2=kLL-1 (non-mover). EC!
    # This is the gap=1, zero_fires construction.

    # When does this FAIL?
    # When mover at kLL-1 IS in {LLL, LL, L}. Then some component changed.
    # mover at kLL-1 = LL: but LL fires at kLL. Two consecutive LL fires.
    # mover at kLL-1 = L: then L fires at kLL-1, but fL = kLL+1 (tight). So L fires at BOTH kLL-1 AND kLL+1?
    #   That means J >= 2 (L fires at least twice in phase). But J=1. Contradiction IF kLL-1 is in the phase interior.
    #   kLL-1 could be in a DIFFERENT phase though.
    # mover at kLL-1 = LLL: then config[LLL] changes at kLL-1, so triple differs.

    # Let's check: what's the mover at kLL-1 for ALL tight_LL cases?
    mover_at_kLL_minus1 = Counter()
    mover_at_kLL_minus1_rdist = Counter()

    # When mover at kLL-1 is "bad" (in {LLL, LL, L}): what about kLL-2?
    # Extend: find the longest "quiet run" before kLL
    quiet_run_length = Counter()

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
                    llt = (t - 2) % n
                    rrt = (t + 2) % n
                    lllt = (t - 3) % n

                    phases = get_phases(word, t)
                    for pidx, (fs, interior, end_step) in enumerate(phases):
                        info = classify_phase(word, t, fs, interior, n)
                        if not is_mtr(info) or not info['tight_LL']:
                            continue

                        total_tight_LL += 1
                        kLL = info['kLL']
                        fL = info['fL']

                        # Mover at step before kLL
                        prev_step = (kLL - 1) % CL
                        prev_mover = word[prev_step]
                        mover_at_kLL_minus1[prev_mover] += 1
                        pm_rdist = ring_distance(prev_mover, t, n)
                        mover_at_kLL_minus1_rdist[pm_rdist] += 1

                        # Quiet run: how many steps before kLL have mover NOT in {LLL, LL, L}?
                        bad_set = {lllt, llt, lt}
                        quiet = 0
                        k = (kLL - 1) % CL
                        while word[k] not in bad_set and quiet < CL:
                            quiet += 1
                            k = (k - 1) % CL
                        quiet_run_length[quiet] += 1

                        # EC at LL
                        ec_pairs = find_ec_at_proc(cc, word, llt, n)

                        if not ec_pairs:
                            no_ec_at_LL += 1
                            # Detailed analysis of no-EC case
                            # What's the mover at kLL-1?
                            # What are the LL-interval boundaries?
                            ll_fires_in_cycle = [k for k in range(CL) if word[k] == llt]
                            all_ec = find_all_ec_procs(cc, word, ms, n)
                            ec_rdists = sorted([ring_distance(p, t, n) for p in all_ec])
                            if len(no_ec_examples) < 10:
                                no_ec_examples.append({
                                    'ms': ms, 't': t, 'CL': CL,
                                    'kLL': kLL, 'fL': fL,
                                    'prev_mover': prev_mover, 'prev_mover_rdist': pm_rdist,
                                    'quiet_run': quiet,
                                    'll_fires_in_cycle': ll_fires_in_cycle,
                                    'ec_procs_rdists': ec_rdists,
                                    'word_around_kLL': [
                                        (k % CL, word[k % CL], ring_distance(word[k % CL], t, n))
                                        for k in range(kLL - 5, kLL + 4)
                                    ],
                                })
                            continue

                        has_ec_at_LL += 1

                        # Find the EC pair where k1 = kLL (the tight step)
                        kLL_pairs = [(k1, k2, tr) for (k1, k2, tr) in ec_pairs if k1 == kLL]
                        if kLL_pairs:
                            # Find the nearest non-mover match
                            min_gap = CL
                            for (k1, k2, tr) in kLL_pairs:
                                gap = min((k2 - k1) % CL, (k1 - k2) % CL)
                                min_gap = min(min_gap, gap)
                            nearest_match_gap[min_gap] += 1

                            # Check if gap=1 exists
                            for (k1, k2, tr) in kLL_pairs:
                                gap = min((k2 - k1) % CL, (k1 - k2) % CL)
                                if gap == 1:
                                    gap1_count += 1
                                    nm_rdist = ring_distance(word[k2], t, n)
                                    gap1_mover_rdist[nm_rdist] += 1
                                    break

    # ─────── Report ───────
    print("=" * 70)
    print("EC AT LL ANATOMY — Round 2 (corrected parity + construction)")
    print("=" * 70)

    print(f"\nTotal tight_LL MTR phases: {total_tight_LL}")
    print(f"  Has EC at LL: {has_ec_at_LL} ({100.0*has_ec_at_LL/max(1,total_tight_LL):.1f}%)")
    print(f"  No EC at LL:  {no_ec_at_LL} ({100.0*no_ec_at_LL/max(1,total_tight_LL):.1f}%)")

    print(f"\n=== THE CONSTRUCTION: gap-1 match ===")
    print(f"gap=1 matches (step before kLL): {gap1_count}/{has_ec_at_LL}")
    print(f"  Mover at gap-1 non-mover step (ring dist from t):")
    for rdist in sorted(gap1_mover_rdist.keys()):
        print(f"    dist={rdist:+d}: {gap1_mover_rdist[rdist]}")

    print(f"\n=== Nearest match gap from kLL ===")
    for gap in sorted(nearest_match_gap.keys())[:15]:
        cnt = nearest_match_gap[gap]
        pct = 100.0 * cnt / max(1, has_ec_at_LL)
        print(f"  gap={gap}: {cnt} ({pct:.1f}%)")

    print(f"\n=== Mover at step kLL-1 ===")
    print("  (Ring distance from t:)")
    for rdist in sorted(mover_at_kLL_minus1_rdist.keys()):
        cnt = mover_at_kLL_minus1_rdist[rdist]
        pct = 100.0 * cnt / max(1, total_tight_LL)
        print(f"  dist={rdist:+d}: {cnt} ({pct:.1f}%)")

    print(f"\n=== Quiet run before kLL (steps with mover NOT in {{LLL, LL, L}}) ===")
    for qr in sorted(quiet_run_length.keys())[:15]:
        cnt = quiet_run_length[qr]
        pct = 100.0 * cnt / max(1, total_tight_LL)
        print(f"  quiet_run={qr}: {cnt} ({pct:.1f}%)")

    print(f"\n=== No-EC-at-LL examples ===")
    for i, ex in enumerate(no_ec_examples):
        print(f"\n  No-EC example {i}:")
        print(f"    ms={ex['ms']}, t={ex['t']}, CL={ex['CL']}")
        print(f"    kLL={ex['kLL']}, fL={ex['fL']}")
        print(f"    prev_mover rdist={ex['prev_mover_rdist']:+d}, quiet_run={ex['quiet_run']}")
        print(f"    LL fires in cycle: {ex['ll_fires_in_cycle']} ({len(ex['ll_fires_in_cycle'])} fires)")
        print(f"    EC procs (rdist from t): {ex['ec_procs_rdists']}")
        print(f"    Word around kLL: step, mover, mover_rdist:")
        for (step, mover, mrdist) in ex['word_around_kLL']:
            marker = " <<< kLL" if step == ex['kLL'] else (" <<< fL" if step == ex['fL'] else "")
            print(f"      step {step:3d}: mover rdist={mrdist:+d}{marker}")

    print(f"\nTime: {time.time() - t0:.1f}s")
