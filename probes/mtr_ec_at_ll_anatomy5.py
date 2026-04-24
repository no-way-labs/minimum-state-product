#!/usr/bin/env python3
"""
Round 5: Final characterization.

From Round 4:
- Generalized gap-1 (backwards scan): 989/991 = 99.8%.
- 2 failures. Need to understand them.
- Also: the generalized scan finds EC at SOME proc. But which proc exactly?
  And does that proc always have EC?

The CLEAN construction:
  Starting from the tight pair (kLL, kLL+1) = (LL fires, L fires),
  scan backwards: kLL, kLL-1, kLL-2, ...
  At each step k, check: does mover(k-1) share a boundary with mover(k)?
  i.e., is mover(k-1) in {left(mover(k)), mover(k), right(mover(k))}?
  If NO: gap-1 EC at mover(k), between steps k (mover) and k-1 (non-mover).
  If YES: continue scanning backwards.

  The scan terminates when it finds a gap OR wraps around the whole cycle.
  Wrap-around means EVERY consecutive pair of movers shares a boundary:
  the mover word forms a "path on the ring" going backwards.

  For n=9 with CL ~ 10-25: a wrap-around requires CL consecutive
  adjacent movers. This creates a very constrained word.

Let me:
1. For the 2 generalized-gap-1 failures: print the FULL mover word.
2. For ALL cases: verify that the proc found by the gap-1 scan actually has EC.
3. Count: how often does the gap-1 construction give EC at LL specifically?
"""

import random
from itertools import product as iterproduct
from collections import Counter
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
    llt = (t - 2) % n
    rrt = (t + 2) % n
    CL = len(movers)
    J = sum(1 for k in interior if movers[k] == lt)
    K = sum(1 for k in interior if movers[k] == (t+1)%n)
    tight_LL = False
    kLL_step = None
    fL_step = None
    for k in interior:
        if movers[k] == llt:
            k_succ = (k + 1) % CL
            if movers[k_succ] == lt:
                tight_LL = True
                kLL_step = k
                fL_step = k_succ
    tight_RR = False
    for k in interior:
        if movers[k] == rrt:
            k_succ = (k + 1) % CL
            if movers[k_succ] == (t+1)%n:
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
    mover_triples = set()
    nonmover_triples = set()
    for k in range(CL):
        triple = (cycle[k][lp], cycle[k][proc], cycle[k][rp])
        if movers[k] == proc:
            mover_triples.add(triple)
        else:
            nonmover_triples.add(triple)
    return bool(mover_triples & nonmover_triples)


def ring_distance(i, t, n):
    d1 = (i - t) % n
    d2 = (t - i) % n
    return d1 if d1 <= d2 else -d2


if __name__ == '__main__':
    t0 = time.time()
    n = 9

    ms_configs = [
        [2, 2, 3, 2, 2, 3, 2, 2, 3],
        [3, 2, 2, 3, 2, 2, 3, 2, 2],
        [2, 3, 2, 2, 3, 2, 2, 3, 2],
    ]

    total = 0
    gap1_ec_proc_rdist = Counter()
    gap1_ec_confirmed = 0
    gap1_ec_not_confirmed = 0
    gap1_at_LL = 0
    gap1_not_found = 0

    wrap_around_details = []

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
                    llt = (t - 2) % n

                    phases = get_phases(word, t)
                    for pidx, (fs, interior, end_step) in enumerate(phases):
                        info = classify_phase(word, t, fs, interior, n)
                        if not is_mtr(info) or not info['tight_LL']:
                            continue

                        total += 1
                        kLL = info['kLL']

                        # Generalized backwards scan
                        found = False
                        ec_proc = None
                        ec_step = None
                        k = kLL
                        for depth in range(CL):
                            pk = (k - 1) % CL
                            p = word[k]
                            pm = word[pk]
                            bad = {(p - 1) % n, p, (p + 1) % n}
                            if pm not in bad:
                                # Gap-1 EC at proc p between steps k (mover) and pk (non-mover)
                                ec_proc = p
                                ec_step = k
                                found = True
                                break
                            k = pk

                        if found:
                            rdist = ring_distance(ec_proc, t, n)
                            gap1_ec_proc_rdist[rdist] += 1
                            if ec_proc == llt:
                                gap1_at_LL += 1

                            # Verify EC at this proc
                            if find_ec_at_proc(cc, word, ec_proc, n):
                                gap1_ec_confirmed += 1
                            else:
                                gap1_ec_not_confirmed += 1
                        else:
                            gap1_not_found += 1
                            # Print full mover word for wrap-around cases
                            if len(wrap_around_details) < 5:
                                word_rdists = [ring_distance(word[k], t, n) for k in range(CL)]
                                wrap_around_details.append({
                                    'ms': ms, 't': t, 'CL': CL,
                                    'kLL': kLL,
                                    'word_rdists': word_rdists,
                                    'word': list(word),
                                })

    print("=" * 70)
    print("GAP-1 EC CONSTRUCTION — FINAL")
    print("=" * 70)

    print(f"\nTotal tight_LL MTR phases: {total}")
    print(f"Gap-1 found: {total - gap1_not_found} ({100.0*(total-gap1_not_found)/total:.1f}%)")
    print(f"Gap-1 NOT found (wrap-around): {gap1_not_found} ({100.0*gap1_not_found/total:.2f}%)")

    print(f"\n=== Gap-1 EC proc (ring dist from t) ===")
    for rdist in sorted(gap1_ec_proc_rdist.keys()):
        cnt = gap1_ec_proc_rdist[rdist]
        pct = 100.0 * cnt / max(1, total)
        print(f"  dist={rdist:+d}: {cnt} ({pct:.1f}%)")

    print(f"\n  EC at LL (dist=-2): {gap1_at_LL} ({100.0*gap1_at_LL/max(1,total):.1f}%)")

    print(f"\n=== EC confirmation ===")
    print(f"  Confirmed: {gap1_ec_confirmed}")
    print(f"  Not confirmed: {gap1_ec_not_confirmed}")

    if wrap_around_details:
        print(f"\n=== Wrap-around cases (full mover word) ===")
        for i, d in enumerate(wrap_around_details):
            print(f"\n  Case {i}: ms={d['ms']}, t={d['t']}, CL={d['CL']}, kLL={d['kLL']}")
            print(f"    Mover word (rdist from t): {d['word_rdists']}")
            print(f"    Mover word (proc IDs): {d['word']}")
            # Check: every consecutive pair is adjacent
            wrds = d['word_rdists']
            consec_adj = []
            for j in range(d['CL']):
                a = d['word'][j]
                b = d['word'][(j+1) % d['CL']]
                diff = abs((a - b + n) % n)
                adj = (diff <= 1 or diff >= n - 1)
                consec_adj.append(adj)
            print(f"    All consecutive movers adjacent? {all(consec_adj)}")
            # Show where adjacency holds/fails
            for j in range(d['CL']):
                a = d['word'][j]
                b = d['word'][(j+1) % d['CL']]
                diff = min((a - b) % n, (b - a) % n)
                print(f"      step {j:2d}: mover rdist={wrds[j]:+d}, next={wrds[(j+1)%d['CL']]:+d}, gap={diff}")

    print(f"\nTime: {time.time() - t0:.1f}s")
