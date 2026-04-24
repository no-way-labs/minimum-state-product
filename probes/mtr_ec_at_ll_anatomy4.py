#!/usr/bin/env python3
"""
Round 4: Precise domino chain EC construction.

The construction:
  Tight LL->L pair: step kLL has mover LL, step kLL+1 has mover L.
  Read mover word backwards from kLL: kLL, kLL-1, kLL-2, ...
  A "leftward chain" extends as long as each predecessor fires the LEFT
  neighbor of the current mover.

  The chain terminates at the first break. At the break:
  - The last chain member (processor p) fires at step k.
  - The predecessor step k-1 has mover q where q != left(p).
  - If q is NOT in {left(p), p, right(p)}: boundary triple at p unchanged.
    EC at p via gap-1 (step k vs step k-1).
  - If q = p: self-consecutive. The gap-1 STILL gives EC at p IF step k-1
    is a NON-MOVER context for p... but wait, q = p means mover at k-1 IS p.
    So k-1 is a MOVER step for p, not non-mover. NO gap-1 EC.
  - If q = right(p): boundary triple at p changes (config[right(p)] changed
    at step k-1). NO gap-1 EC.

  For the 2 failures: chain ended but predecessor was the terminator's left
  neighbor that we already accounted for, OR a self/right neighbor.

  NEW: extend the gap-1 check to include checking step k-2 as well.
  Also: check the RIGHTWARD chain from fL (the L-fire).

  Actually, let me just check: for the 2 failures, where IS the EC?
  Also: verify the full "leftward domino with gap-1" gives EC at SOME
  processor for 100% of tight_LL cases.
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
    rt = (t + 1) % n
    llt = (t - 2) % n
    rrt = (t + 2) % n
    CL = len(movers)
    J = sum(1 for k in interior if movers[k] == lt)
    K = sum(1 for k in interior if movers[k] == rt)
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
    mover_triples = set()
    nonmover_triples = set()
    for k in range(CL):
        triple = (cycle[k][lp], cycle[k][proc], cycle[k][rp])
        if movers[k] == proc:
            mover_triples.add(triple)
        else:
            nonmover_triples.add(triple)
    return bool(mover_triples & nonmover_triples)


def find_all_ec_procs(cycle, movers, ms, n):
    ec_procs = set()
    CL = len(cycle)
    for i in range(n):
        if find_ec_at_proc(cycle, movers, i, n):
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

    total = 0

    # Strategy A: leftward chain from kLL, gap-1 at terminator
    # Strategy B: if A fails (predecessor of terminator is self or right-neighbor),
    #   look at gap-2 (the step 2 before the terminator)
    # Strategy C: look at the rightward chain from fL

    # Track outcomes
    strat_a_success = 0
    strat_a_fail = 0
    strat_a_fail_reason = Counter()

    # For failures: what's the predecessor mover relationship?
    fail_pred_relationship = Counter()

    # For the 2 specific failures from round 3: full context
    failure_details = []

    # Also: check generalized gap-1 on the ENTIRE backwards run
    # For EVERY step k in the cycle: if mover(k) = p and mover(k-1) != p and
    # mover(k-1) not in {left(p), right(p)}: EC at p via gap-1.
    # Check: is this ALWAYS true somewhere in the tight pair's backwards run?
    generalized_gap1_found = 0
    generalized_gap1_not_found = 0

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

                        # Trace leftward chain
                        chain = [llt]
                        chain_steps = [kLL]
                        current_proc = llt
                        k = (kLL - 1) % CL
                        while True:
                            expected_left = (current_proc - 1) % n
                            if word[k] == expected_left:
                                chain.append(expected_left)
                                chain_steps.append(k)
                                current_proc = expected_left
                                k = (k - 1) % CL
                                if len(chain) > n:
                                    break
                            else:
                                break

                        # Chain terminator: chain[-1] at chain_steps[-1]
                        term_proc = chain[-1]
                        term_step = chain_steps[-1]
                        pred_step = (term_step - 1) % CL
                        pred_mover = word[pred_step]

                        # For gap-1 at terminator: need pred_mover not in
                        # {left(term_proc), term_proc, right(term_proc)}
                        bad_set = {(term_proc - 1) % n, term_proc, (term_proc + 1) % n}

                        if pred_mover not in bad_set:
                            strat_a_success += 1
                        else:
                            strat_a_fail += 1
                            if pred_mover == term_proc:
                                rel = 'self'
                            elif pred_mover == (term_proc - 1) % n:
                                rel = 'left'
                            else:
                                rel = 'right'
                            strat_a_fail_reason[rel] += 1
                            fail_pred_relationship[rel] += 1

                            # Full detail for failures
                            if len(failure_details) < 20:
                                all_ec = find_all_ec_procs(cc, word, ms, n)
                                ec_rdists = sorted([ring_distance(p, t, n) for p in all_ec])

                                # Extended context: 8 steps before chain end
                                ctx = []
                                for ck in range(term_step - 8, term_step + 4):
                                    s = ck % CL
                                    m = word[s]
                                    mrd = ring_distance(m, t, n)
                                    in_chain = s in chain_steps
                                    ctx.append((s, m, mrd, in_chain))

                                failure_details.append({
                                    'ms': ms, 't': t, 'CL': CL,
                                    'chain': [ring_distance(p, t, n) for p in chain],
                                    'chain_steps': chain_steps,
                                    'term_rdist': ring_distance(term_proc, t, n),
                                    'pred_rel': rel,
                                    'ec_rdists': ec_rdists,
                                    'context': ctx,
                                })

                        # Generalized gap-1: scan backwards from kLL+1 (including fL)
                        # looking for ANY step k where mover(k) = p and
                        # mover(k-1) not in {left(p), p, right(p)}
                        found_gen = False
                        # The tight pair gives us: fL (mover=L) at kLL+1.
                        # Step before fL = kLL (mover=LL). Is LL in {LLL, L, left(L)}?
                        # left(L) = LL. So LL IS in {left(L), L, right(L)} where L = left(t).
                        # left(L) = LL, L = L, right(L) = t. Bad set = {LL, L, t}.
                        # LL IS in the bad set. So no gap-1 EC at L from fL.

                        # Check the whole leftward chain + beyond
                        k = kLL
                        seen_procs = set()
                        for depth in range(CL):
                            p = word[k]
                            pk = (k - 1) % CL
                            pm = word[pk]
                            bad = {(p - 1) % n, p, (p + 1) % n}
                            if pm not in bad:
                                found_gen = True
                                break
                            k = pk
                            if p in seen_procs:
                                break  # cycle detected
                            seen_procs.add(p)

                        if found_gen:
                            generalized_gap1_found += 1
                        else:
                            generalized_gap1_not_found += 1

    # ─────── Report ───────
    print("=" * 70)
    print("DOMINO CHAIN EC — Round 4")
    print("=" * 70)

    print(f"\nTotal tight_LL MTR phases: {total}")

    print(f"\n=== Strategy A: leftward chain + gap-1 at terminator ===")
    print(f"  Success: {strat_a_success}/{total} = {100.0*strat_a_success/max(1,total):.1f}%")
    print(f"  Fail:    {strat_a_fail}/{total} = {100.0*strat_a_fail/max(1,total):.1f}%")
    print(f"  Fail reasons: {dict(strat_a_fail_reason)}")

    print(f"\n=== Generalized gap-1 (scan backwards from kLL) ===")
    print(f"  Found:     {generalized_gap1_found}/{total} = {100.0*generalized_gap1_found/max(1,total):.1f}%")
    print(f"  Not found: {generalized_gap1_not_found}/{total} = {100.0*generalized_gap1_not_found/max(1,total):.1f}%")

    print(f"\n=== Failure details ===")
    for i, d in enumerate(failure_details[:10]):
        print(f"\n  Failure {i}:")
        print(f"    ms={d['ms']}, t={d['t']}, CL={d['CL']}")
        print(f"    Chain (rdist): {d['chain']}")
        print(f"    Term rdist: {d['term_rdist']}, pred relationship: {d['pred_rel']}")
        print(f"    EC procs (rdist): {d['ec_rdists']}")
        print(f"    Context (step, mover, mover_rdist, in_chain):")
        for (s, m, mrd, ic) in d['context']:
            marker = " <<< chain" if ic else ""
            print(f"      step {s:3d}: mover rdist={mrd:+d}{marker}")

    print(f"\nTime: {time.time() - t0:.1f}s")
