#!/usr/bin/env python3
"""
Investigate the GLOBAL constraint from a full-ring-walk phase.

In the sorry case, a phase consists of a full ring walk:
  R, RR, right³t, ..., left³t, LL, L, T
Every processor fires exactly once. This gives us strong constraints
on the config at the start vs end of the phase.

Key property: after the phase, every processor has fired once.
For binary procs: value has flipped (0↔1).
For ternary procs: value has changed but direction depends on transition function.

CRITICAL OBSERVATION:
The sorry case requires n ≥ 9 and we have ≥ 3 binary processors.
In the full-ring-walk phase, each binary proc fires once (odd).
Over the full cycle, binary procs must fire even times.
So the OTHER phases must also contribute odd fires for each binary.

But the sorry case is trying to show J+K ≤ 1 for EVERY phase.
If ALL phases are sorry-type (full ring walks), then each binary fires
once per phase, times mt phases = mt total fires.
mt = fireCount(t) ≥ 3 (ternary). If mt is odd: total fires odd. But must be even.
Contradiction if mt is odd!

If mt is even: could work. But then fc(L) + fc(R) = 2*mt (each binary fires
twice per two phases, one from each side)... no, wait.

Actually in the sorry-type phase, BOTH L and R fire (mixed phase).
J ≥ 1 and K ≥ 1. If J=K=1 and each phase is sorry-type, then
fc(L) = fc(R) = mt. But they need to be even: mt must be even.
fc(L) + fc(R) = 2*mt. We need fc(L)+fc(R) ≤ fc(t) = mt. So 2*mt ≤ mt.
Contradiction for mt ≥ 1!

Wait, that's NOT the sorry case. The sorry case is about showing
mixed phases HAVE EC, so they can be ruled out. If a mixed phase
exists and has EC, then ¬EC is violated. The current code tries to show
EC exists in every mixed phase.

If the sorry proves that mixed phases always have EC, then under ¬EC,
all phases are one-sided (J=0 or K=0). Then fc(L)+fc(R) ≤ fc(t)
(each phase contributes at most 1 to fc(L)+fc(R)).

The sorry blocks this by showing that the specific case (full ring walk)
doesn't produce a LOCAL EC. The proof needs a different argument for
this case.

ALTERNATIVE APPROACH:
Instead of finding a local EC within the sorry phase, prove that the
sorry phase is IMPOSSIBLE. If the mover sequence must be a full ring walk,
what constraints does this impose on the cycle that force a GLOBAL EC?

Specifically: in the full-ring-walk phase, every step is adjacent to the next.
The movers trace a path around the entire ring. The configs at each step
are determined by the transition function applied to the moving processor.

What if we show that the full-ring-walk phase, combined with the cycle
closure constraint, forces some config to repeat? Config repetition in a
good cycle is impossible (all configs distinct).

Or: maybe the full-ring-walk forces a boundary triple collision at some
processor in a DIFFERENT phase.

Let me compute: how many distinct triples at processor t appear across
the sorry phase?
  - t doesn't fire in the phase (steps a to s-1), then fires at step s.
  - t_val is constant throughout steps a to s (it fires at s, changing it).
  - L_val changes when L fires (at step n-2 relative to phase start).
  - R_val changes when R fires (at step 0 relative to phase start).
  - So there are at most 4 distinct triples: (L0,t,R0), (L0,t,R1), (L1,t,R0), (L1,t,R1).
  - In fact: (L0,t,R0) at step a (before R fires),
    (L0,t,R1) at steps a+1 through n-3 (after R fires, before L fires),
    (L1,t,R1) at step n-2 (after L fires, this is the mover triple at t).
  - Wait: R fires at step a (first step). Before: (L0,t,R0). After: (L0,t,R1).
    L fires at step a+n-2 (= step s-1). Before: (L0,t,R1). After: (L1,t,R1).
    t fires at step s: mover triple = (L1,t,R1).
  - Non-mover triples at t: {(L0,t,R0)} (step a only) ∪ {(L0,t,R1)} (steps a+1..s-1).
  - Mover triple at t: (L1,t,R1).
  - Since L0 ≠ L1 (binary flip): (L1,t,R1) ≠ (L0,t,R0) and (L1,t,R1) ≠ (L0,t,R1).
  - NO EC at t within this phase. ✓ (Confirmed earlier.)

Now: across the FULL CYCLE, t fires mt times. Each t-fire has a mover triple.
The non-mover triples at t come from ALL steps where t doesn't fire.
EC at t: some mover triple = some non-mover triple.

In the sorry phase, t's mover triple is (L1, t_old, R1).
In other phases, t is non-mover. If some other phase has boundary at t = (L1, t_old, R1)
at a step where t doesn't fire: EC at t!

BUT: after the sorry phase, t_val changes. So t_val in the next phase is different.
The mover triple from the sorry phase used t_old. Non-mover triples in later phases
use t_new (or further changed values). So the t_val component differs.

Unless t fires again and returns to t_old. This is possible for ternary t (m≥3):
t could go through values 0→1→2→0→... and return to t_old.

INSIGHT: Over the full cycle, t returns to its original value. If t fires mt times,
it goes through mt value changes and returns. For mt = 3 (mod 3 = 0): possible.

This is getting complex. Let me try a computational approach: search for valid
systems where a full-ring-walk phase exists in a good cycle with no EC.
"""
import random
from collections import defaultdict

random.seed(42)

def find_fullwalk_phase_cycles(n, ms, t, num_trials=5000000):
    """Search for good cycles containing a full-ring-walk phase."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    stats = defaultdict(int)
    results = []

    for trial in range(num_trials):
        # Random transition function
        sys_f = {}
        for i in range(n):
            f = {}
            for L in range(ms[(i-1)%n]):
                for S in range(ms[i]):
                    for R in range(ms[(i+1)%n]):
                        f[(L, S, R)] = random.randint(0, ms[i] - 1)
            sys_f[i] = f

        # Random walk to find cycle
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

                    # Check if all consecutive movers are adjacent
                    all_adj = all(
                        min((cycle_movers[k] - cycle_movers[(k+1)%CL]) % n,
                            (cycle_movers[(k+1)%CL] - cycle_movers[k]) % n) <= 1
                        for k in range(CL))

                    if not all_adj:
                        stats['has_nonadj'] += 1
                        break

                    stats['all_adj'] += 1

                    # Check for EC
                    has_ec = False
                    for p2 in range(n):
                        mover_triples = set()
                        nonmover_triples = set()
                        for k in range(CL):
                            L_val = cycle_configs[k][(p2-1)%n]
                            S_val = cycle_configs[k][p2]
                            R_val = cycle_configs[k][(p2+1)%n]
                            triple = (L_val, S_val, R_val)
                            if cycle_movers[k] == p2:
                                mover_triples.add(triple)
                            else:
                                nonmover_triples.add(triple)
                        if mover_triples & nonmover_triples:
                            has_ec = True
                            break

                    if has_ec:
                        stats['ec'] += 1
                        break

                    stats['noec'] += 1

                    # Check for mixed phases at t
                    t_fires = [k for k in range(CL) if cycle_movers[k] == t]
                    if len(t_fires) >= 2:
                        for idx in range(len(t_fires)):
                            s_step = t_fires[idx]
                            prev_t = t_fires[(idx-1) % len(t_fires)]
                            a_step = (prev_t + 1) % CL

                            # Collect phase movers
                            phase = []
                            k = a_step
                            while k != s_step:
                                phase.append(cycle_movers[k])
                                k = (k + 1) % CL

                            has_L = lt in phase
                            has_R = rt in phase
                            if has_L and has_R:
                                stats['mixed_phase_noec'] += 1
                                # Check if it's a full ring walk
                                procs_in_phase = set(phase)
                                if len(procs_in_phase) == n - 1 and t not in procs_in_phase:
                                    stats['fullwalk_noec'] += 1
                                    results.append((cycle_configs, cycle_movers, t_fires, idx))
                                    if len(results) >= 50:
                                        return stats, results

                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

        if trial % 500000 == 499999:
            print(f"  Trial {trial+1}: {dict(stats)}")

    return stats, results


def main():
    # Try small n first
    configs_to_try = [
        (5, [2, 3, 2, 3, 3], 1),
        (5, [3, 3, 2, 3, 2], 2),
        (6, [2, 3, 2, 3, 3, 3], 1),
    ]

    for n, ms, t in configs_to_try:
        print(f"\n=== n={n}, ms={ms}, t={t} ===")
        stats, results = find_fullwalk_phase_cycles(n, ms, t, num_trials=2000000)
        print(f"Final stats: {dict(stats)}")
        print(f"Full-walk ¬EC cycles found: {len(results)}")

        if results:
            for i, (configs, movers, t_fires, idx) in enumerate(results[:3]):
                CL = len(configs)
                print(f"\n  Example {i+1}: cycle length {CL}")
                print(f"    Movers: {movers}")

                # Show the mixed phase
                s_step = t_fires[idx]
                prev_t = t_fires[(idx-1) % len(t_fires)]
                a_step = (prev_t + 1) % CL
                phase = []
                k = a_step
                while k != s_step:
                    phase.append(movers[k])
                    k = (k + 1) % CL
                print(f"    Mixed phase movers: {phase}")


if __name__ == '__main__':
    main()
