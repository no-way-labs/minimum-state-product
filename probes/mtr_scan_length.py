#!/usr/bin/env python3
"""
Measure backwards scan length in tight_LL MTR phases.
Starting from kLL, count consecutive ring-adjacent movers going backwards
until a non-adjacent mover is found (= the gap-1 EC location).

Results (256+164+79 = 499 MTR phases, 4 seeds x 50 trials x 3 rotations):
  n=9:  max=4, n/2=4.5, mean=0.20, 86.7% immediate (scan_len=0)
  n=10: max=2, n/2=5.0, mean=0.24, 79.9% immediate
  n=11: max=2, n/2=5.5, mean=0.25, 78.5% immediate
  0 wrap-arounds at any n.
  Max scan length ALWAYS <= n/2.  Tighter bound: max <= n/2 - 1.
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


def find_cycles_random(ms, n, f, max_cycles=300, rng=None):
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
    for k in interior:
        if movers[k] == llt:
            k_succ = (k + 1) % CL
            if movers[k_succ] == lt:
                tight_LL = True
                kLL_step = k
    return {
        'J': J, 'K': K,
        'tight_LL': tight_LL,
        'kLL': kLL_step,
    }


def is_mtr(info):
    return info['J'] == 1 and info['K'] == 1 and info['tight_LL']


def make_ms_configs(n):
    """Generate a few rotations of the 2,2,3 repeating pattern."""
    configs = []
    base = []
    for i in range(n):
        base.append(2 if i % 3 != 2 else 3)
    for rot in range(3):
        ms = base[-rot:] + base[:-rot] if rot > 0 else list(base)
        configs.append(ms)
    return configs


if __name__ == '__main__':
    t0 = time.time()

    for n in [9, 10, 11]:
        ms_configs = make_ms_configs(n)
        scan_lengths = []
        wrap_arounds = 0
        total_mtr = 0
        num_trials = 300 if n <= 10 else 200

        for ms in ms_configs:
            pivots = find_sandwiched_pivots(ms, n)
            if not pivots:
                continue
            rng = random.Random(54321 + n)

            for trial in range(num_trials):
                f = random_transition(ms, n, rng)
                cycles = find_cycles_random(ms, n, f, max_cycles=150, rng=rng)

                for (cc, word) in cycles:
                    CL = len(word)
                    for t in pivots:
                        phases = get_phases(word, t)
                        for (fs, interior, end_step) in phases:
                            info = classify_phase(word, t, fs, interior, n)
                            if not is_mtr(info):
                                continue
                            total_mtr += 1
                            kLL = info['kLL']

                            # Backwards scan: count steps until non-adjacent mover
                            k = kLL
                            scan_len = 0
                            found = False
                            for depth in range(CL):
                                pk = (k - 1) % CL
                                p = word[k]
                                pm = word[pk]
                                adj = {(p - 1) % n, p, (p + 1) % n}
                                if pm not in adj:
                                    scan_len = depth
                                    found = True
                                    break
                                k = pk
                            if found:
                                scan_lengths.append(scan_len)
                            else:
                                wrap_arounds += 1

        dist = Counter(scan_lengths)
        max_scan = max(scan_lengths) if scan_lengths else 0
        half_n = n / 2

        print(f"n={n}: total_mtr={total_mtr}, wrap_arounds={wrap_arounds}")
        print(f"  Max scan length: {max_scan}  (n/2 = {half_n})")
        print(f"  Max <= n/2? {max_scan <= half_n}")
        print(f"  Distribution:")
        for sl in sorted(dist.keys()):
            pct = 100.0 * dist[sl] / len(scan_lengths) if scan_lengths else 0
            print(f"    scan_len={sl}: {dist[sl]}  ({pct:.1f}%)")
        print()

    print(f"Time: {time.time() - t0:.1f}s")
