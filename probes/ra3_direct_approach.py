#!/usr/bin/env python3
"""
DIRECT APPROACH: Since mk_ec can't close the sorry within a single phase,
the sorry must be closed by showing mixed phases CANNOT EXIST in the first place.

Wait -- let me re-read the Lean code more carefully. The sorrys at lines 1012,
1077, 1121 are inside the proof of h_phase_le1, which shows J+K ≤ 1 per phase.
They're NOT trying to show mixed phases don't exist -- they're trying to show
that mixed phases produce EC (which contradicts ¬EC).

But I showed that the full-ring-walk phase doesn't produce local EC.
So how can this sorry be closed?

OPTIONS:
1. The sorry case (left³(t) fires in [a, fLL)) is actually IMPOSSIBLE.
   Maybe gap1_ec already prevents this pattern.
2. EC comes from a different part of the cycle (cross-phase).
3. The entire proof strategy is wrong and needs restructuring.

Let me check option 1 more carefully.

The sorry case at line 1077 requires:
  (a) fR = a (R fires first)
  (b) fL > a (L fires later)
  (c) LL fires in [a, fL)
  (d) Last LL fire adjacent to fL (LL at fL-1)
  (e) First LL fire at fLL
  (f) left³(t) fires in [a, fLL)

Under ¬EC: all consecutive movers ring-adjacent.

The movers from step a to fLL-1 must be ring-adjacent.
moverAt(a) = R.
Between a and fLL: no LL (first LL is fLL), no L (first L is fL > fLL).
So movers in [a, fLL) are ∉ {L, LL, t}.

The movers must be ring-adjacent. Starting from R(=rt):
  moverAt(a) = R
  moverAt(a+1) adj to R, ∉ {L, LL, t} possible: R, RR, or... wait,
  self-repeat is possible if R fires again.

Actually, can R fire multiple times? R is binary (m=2). In the phase,
R fires at step a. It could fire again later (toggling back).

But if R fires twice consecutively: moverAt(a)=R, moverAt(a+1)=R.
Adjacent? dist(R,R)=0, which is ≤1 if we consider self-adjacency.
gap1_ec: moverAt(k) ∉ {left(moverAt(k-1)), moverAt(k-1), right(moverAt(k-1))}.
Wait, gap1_ec gives EC if moverAt(k) is NOT in {left(p), p, right(p)} where
p = moverAt(k-1). So moverAt(k) ∈ {left(p), p, right(p)} under ¬EC.
Self-repeat: moverAt(k) = moverAt(k-1). Allowed by gap1_ec.

So R could fire at step a, then fire again at step a+1 (toggleing back
to original value). But that would mean the config at step a+2 equals
the config at step a (since only R changed and changed back). But all
configs must be distinct! So R can't fire twice consecutively.

More generally: a processor p can't fire twice in a row (would create
a repeat config). What about firing with one step gap? p fires, q fires,
p fires. Config at step 0 → p changes → q changes → p changes back?
Not necessarily back: p's transition depends on neighbors, which may
have changed.

OK this is complex. Let me check computationally whether the sorry case
(condition f above) can actually hold.
"""

import random
from collections import defaultdict

random.seed(42)

def check_sorry_realizable(n, ms, t, num_trials=5000000):
    """
    Check if the exact sorry case can occur:
    In a ¬EC good cycle with a ternary phase at t where:
    - fR = a (first mover in phase is R)
    - fL > a (L fires later)
    - LL fires in [a, fL), with last LL adjacent to fL (wmax=fL-1)
    - left³t fires in [a, first_LL_fire)
    """
    lt = (t - 1) % n
    rt = (t + 1) % n
    llt = (t - 2) % n
    l3t = (t - 3) % n
    rrt = (t + 2) % n

    stats = defaultdict(int)
    sorry_examples = []

    for trial in range(num_trials):
        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        config = tuple(random.randint(0, ms[i]-1) for i in range(n))
        history = [config]
        history_movers = []
        config_to_step = {config: 0}

        for step in range(5000):
            privs = [i for i in range(n)
                     if sys_f[i][(config[(i-1)%n], config[i], config[(i+1)%n])] != config[i]]
            if not privs:
                break
            p = random.choice(privs)
            nc = list(config)
            nc[p] = sys_f[p][(config[(p-1)%n], config[p], config[(p+1)%n])]
            config = tuple(nc)

            if config in config_to_step:
                cs = config_to_step[config]
                cycle_configs = history[cs:]
                cycle_movers = history_movers[cs:] + [p]
                CL = len(cycle_configs)

                if CL >= 2 * n:
                    stats['cycles'] += 1

                    # Check all-adj
                    all_adj = all(
                        min((cycle_movers[k] - cycle_movers[(k+1)%CL]) % n,
                            (cycle_movers[(k+1)%CL] - cycle_movers[k]) % n) <= 1
                        for k in range(CL))
                    if not all_adj:
                        stats['nonadj'] += 1
                        break

                    # Check ¬EC
                    has_ec = False
                    for p2 in range(n):
                        mt_set = set()
                        nmt_set = set()
                        for k in range(CL):
                            tr = (cycle_configs[k][(p2-1)%n], cycle_configs[k][p2], cycle_configs[k][(p2+1)%n])
                            if cycle_movers[k] == p2:
                                mt_set.add(tr)
                            else:
                                nmt_set.add(tr)
                        if mt_set & nmt_set:
                            has_ec = True
                            break
                    if has_ec:
                        stats['ec'] += 1
                        break

                    stats['noec'] += 1

                    # Check for sorry-2 case at t
                    t_fires = [k for k in range(CL) if cycle_movers[k] == t]
                    if not t_fires:
                        break

                    for idx in range(len(t_fires)):
                        s_step = t_fires[idx]
                        prev_t = t_fires[(idx-1) % len(t_fires)]
                        a_step = (prev_t + 1) % CL

                        # Check: moverAt(a) = rt
                        if cycle_movers[a_step] != rt:
                            continue
                        stats['fR_eq_a'] += 1

                        # Find fL (first lt fire after a, before s)
                        fL = None
                        k = (a_step + 1) % CL
                        while k != s_step:
                            if cycle_movers[k] == lt:
                                fL = k
                                break
                            k = (k + 1) % CL

                        if fL is None:
                            continue
                        stats['fL_gt_a'] += 1

                        # Check: LL fires in [a, fL)
                        LL_fires = []
                        k = a_step
                        while k != fL:
                            if cycle_movers[k] == llt:
                                LL_fires.append(k)
                            k = (k + 1) % CL

                        if not LL_fires:
                            continue
                        stats['LL_in_interval'] += 1

                        # Check: last LL at fL-1
                        last_LL = LL_fires[-1]
                        fL_prev = (fL - 1) % CL
                        if last_LL != fL_prev:
                            stats['LL_has_gap'] += 1
                            continue
                        stats['LL_adjacent_to_fL'] += 1

                        # Find first LL
                        first_LL = LL_fires[0]

                        # Check: left³t fires in [a, first_LL)
                        has_l3t = False
                        k = a_step
                        while k != first_LL:
                            if cycle_movers[k] == l3t:
                                has_l3t = True
                                break
                            k = (k + 1) % CL

                        if has_l3t:
                            stats['sorry2'] += 1
                            sorry_examples.append((cycle_configs, cycle_movers, a_step, s_step, fL, first_LL))
                            if len(sorry_examples) >= 20:
                                return stats, sorry_examples

                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

        if trial % 1000000 == 999999:
            print(f"  Trial {trial+1}: {dict(stats)}")

    return stats, sorry_examples


def main():
    configs = [
        (5, [2, 3, 2, 3, 3], 1),
        (6, [2, 3, 2, 3, 3, 3], 1),
        (7, [2, 3, 2, 3, 3, 3, 3], 1),
        (9, [2, 3, 2, 3, 2, 3, 3, 3, 3], 1),
    ]

    for n, ms, t in configs:
        print(f"\n=== n={n}, ms={ms}, t={t} ===")
        stats, examples = check_sorry_realizable(n, ms, t, num_trials=3000000)
        print(f"Stats: {dict(stats)}")
        print(f"Sorry-2 examples: {len(examples)}")

        if examples:
            for i, (configs0, movers, a, s, fL, fLL) in enumerate(examples[:3]):
                CL = len(configs0)
                print(f"\n  Example {i+1}: CL={CL}")
                print(f"    a={a}, s={s}, fL={fL}, first_LL={fLL}")
                # Show phase movers
                phase = []
                k = a
                while k != s:
                    phase.append(movers[k])
                    k = (k + 1) % CL
                print(f"    Phase movers: {phase}")
                print(f"    Full cycle movers: {movers}")


if __name__ == '__main__':
    main()
