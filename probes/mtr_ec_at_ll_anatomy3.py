#!/usr/bin/env python3
"""
Round 3: Precise construction verification.

From Round 2:
- quiet_run >= 1 => EC at LL via gap-1 (the step before kLL). 830/830 = 100%.
- quiet_run = 0 (mover at kLL-1 = LLL): 161 cases.
  - 39 have NO EC at LL. All 39 have EC at LLL.
  - 122 have EC at LL via a LONGER path (gap > 1).

Questions:
1. When quiet_run=0: does the gap-1 from kLL-1 fail EXACTLY because LLL changed?
   Or can it sometimes still work (LLL fires but returns to same value)?
   If LLL is ternary: fire changes value (0->f(...) != 0 in general). Not guaranteed return.
   If LLL is binary: fire toggles. Can't return in 1 step.
   So gap-1 ALWAYS fails when mover at kLL-1 = LLL. The 122 EC-at-LL cases use gap > 1.

2. For the 122 quiet_run=0 cases with EC at LL: what's the mechanism?
   Must find a non-mover step k2 further away where the triple has returned.

3. KEY: does EC at LL OR EC at LLL ALWAYS hold? That is: is {LL, LLL} a universal
   2-position cover when tight_LL?

4. Actually, a cleaner statement: when quiet_run >= 1, EC at LL (gap-1).
   When quiet_run = 0 (mover at kLL-1 = LLL), what about EC at LLL instead?
   At step kLL-1: LLL fires. At step kLL: LL fires.
   Boundary triple at LLL = (config[left^4 t], config[LLL], config[LL]).
   Step kLL-1: mover = LLL. Triple = (A, B, C).
   Step kLL: mover = LL != LLL. Triple = (A, B', C) where B' = new config[LLL] after firing.
   B' != B (LLL just fired). So the triple at kLL differs from kLL-1 at position LLL. NO match.

   But kLL-2: what's the mover? If mover at kLL-2 is NOT in {left^4 t, LLL, LL}:
   then triple at LLL at kLL-2 = triple at LLL at kLL-1. EC at LLL between kLL-1 (mover)
   and kLL-2 (non-mover).

   This is the SAME gap-1 construction but shifted one position left!

5. So the full construction: try gap-1 at LL (compare kLL with kLL-1).
   If fails (mover at kLL-1 in {LLL, LL, L}): the only possibility is LLL (since
   the tight pair already placed LL at kLL and L at kLL+1).
   Then try gap-1 at LLL (compare kLL-1 with kLL-2).
   If fails: mover at kLL-2 in {left^4 t, LLL, LL}.
   Continue: domino chain going left!

Let me verify this domino chain hypothesis computationally.
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

    total_tight_LL = 0

    # The domino chain: starting from the tight pair LL->L at steps kLL, kLL+1,
    # read the mover word BACKWARDS from kLL:
    # step kLL: mover = LL
    # step kLL-1: mover = ?
    # step kLL-2: mover = ?
    # ...
    # The "chain" = sequence of movers going backwards.
    # EC at some processor p happens when: p fires at some step k, and the step k-1
    # has mover NOT in {left(p), p, right(p)}. Then gap-1 gives EC at p.
    #
    # Starting from kLL: mover = LL. The gap-1 EC at LL needs mover at kLL-1 NOT in {LLL, LL, L}.
    # If mover at kLL-1 = LLL (the problematic case): then the gap-1 EC at LLL needs
    # mover at kLL-2 NOT in {left^4 t, LLL, LL}.
    #
    # The "chain" propagates leftward. At each step going back, if the mover is the
    # LEFT neighbor of the previous mover, the chain extends. Otherwise: EC at the
    # current processor.
    #
    # The chain is: kLL has mover LL. If kLL-1 has mover LLL: chain extends to LLL.
    # If kLL-2 has mover left^4(t): chain extends to left^4(t). Etc.
    # The chain stops when a gap appears (mover is not the left neighbor of previous).

    chain_length = Counter()  # how many consecutive leftward movers
    chain_terminator_rdist = Counter()  # where does the chain stop (EC location)
    chain_ec_found = Counter()  # EC at chain terminator?

    # Verify: EC at the chain terminator processor
    ec_at_chain_end = 0
    no_ec_at_chain_end = 0
    chain_details = []

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

                        total_tight_LL += 1
                        kLL = info['kLL']

                        # Trace the leftward chain
                        # Start: mover at kLL = LL = left^2(t)
                        chain = [llt]  # processors in the chain
                        chain_steps = [kLL]
                        current_proc = llt
                        k = (kLL - 1) % CL
                        depth = 0
                        while depth < n:
                            expected_left = (current_proc - 1) % n
                            if word[k] == expected_left:
                                chain.append(expected_left)
                                chain_steps.append(k)
                                current_proc = expected_left
                                k = (k - 1) % CL
                                depth += 1
                            else:
                                break

                        clen = len(chain)
                        chain_length[clen] += 1

                        # The EC should be at chain[-1] (the last processor that fired)
                        # via gap-1 with the step before it
                        ec_proc = chain[-1]
                        ec_rdist = ring_distance(ec_proc, t, n)
                        chain_terminator_rdist[ec_rdist] += 1

                        # Check: does ec_proc actually have EC?
                        has_ec = find_ec_at_proc(cc, word, ec_proc, n)
                        if has_ec:
                            ec_at_chain_end += 1
                        else:
                            no_ec_at_chain_end += 1
                            if len(chain_details) < 20:
                                # More detail for debugging
                                context_steps = []
                                for ck in range(chain_steps[-1] - 3, chain_steps[-1] + 4):
                                    s = ck % CL
                                    context_steps.append((s, word[s], ring_distance(word[s], t, n)))
                                chain_details.append({
                                    'ms': ms, 't': t, 'CL': CL,
                                    'chain_procs': [ring_distance(p, t, n) for p in chain],
                                    'chain_steps': chain_steps,
                                    'ec_proc_rdist': ec_rdist,
                                    'context': context_steps,
                                })

    # ─────── Report ───────
    print("=" * 70)
    print("DOMINO CHAIN VERIFICATION")
    print("=" * 70)

    print(f"\nTotal tight_LL MTR phases: {total_tight_LL}")

    print(f"\n=== Chain length (# of consecutive leftward movers ending at kLL) ===")
    for clen in sorted(chain_length.keys()):
        cnt = chain_length[clen]
        pct = 100.0 * cnt / max(1, total_tight_LL)
        print(f"  chain_len={clen}: {cnt} ({pct:.1f}%)")

    print(f"\n=== Chain terminator (EC location, ring dist from t) ===")
    for rdist in sorted(chain_terminator_rdist.keys()):
        cnt = chain_terminator_rdist[rdist]
        pct = 100.0 * cnt / max(1, total_tight_LL)
        print(f"  dist={rdist:+d}: {cnt} ({pct:.1f}%)")

    print(f"\n=== EC at chain terminator ===")
    print(f"  EC found:     {ec_at_chain_end} ({100.0*ec_at_chain_end/max(1,total_tight_LL):.1f}%)")
    print(f"  EC NOT found: {no_ec_at_chain_end} ({100.0*no_ec_at_chain_end/max(1,total_tight_LL):.1f}%)")

    if chain_details:
        print(f"\n=== No-EC-at-chain-end examples ===")
        for i, d in enumerate(chain_details[:10]):
            print(f"\n  Example {i}:")
            print(f"    ms={d['ms']}, t={d['t']}, CL={d['CL']}")
            print(f"    Chain (rdist from t): {d['chain_procs']}")
            print(f"    Chain steps: {d['chain_steps']}")
            print(f"    EC proc rdist: {d['ec_proc_rdist']}")
            print(f"    Context around chain end:")
            for (s, m, mrd) in d['context']:
                marker = ""
                if s in d['chain_steps']:
                    marker = " <<< chain"
                print(f"      step {s:3d}: mover rdist={mrd:+d}{marker}")

    print(f"\nTime: {time.time() - t0:.1f}s")
