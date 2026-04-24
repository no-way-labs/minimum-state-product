#!/usr/bin/env python3
"""
Investigate: Is a full-ring-walk mixed phase IMPOSSIBLE under ¬EC for n ≥ 9?

In the sorry case (full ring walk), the mover sequence in the phase is:
  R, RR, right³t, ..., left³t, LL, L, then T fires.

Under ¬EC, this requires ALL consecutive movers to be ring-adjacent.
This is satisfied by construction (the walk steps by 1 around the ring).

But the CYCLE has multiple phases. The ¬EC constraint applies GLOBALLY.
Maybe the full-walk phase forces other phases to also be full-walks,
and this leads to a global contradiction.

ARGUMENT SKETCH:
1. In the full-walk phase, every processor fires exactly once.
2. Binary procs fire once (odd). Over the cycle, they must fire even times.
3. So in OTHER phases combined, each binary fires odd times.
4. If there's only one other phase (mt=2), that phase must have each binary
   fire odd times.
5. With 3 binary procs (from h3bin), 3 independent parity constraints.

Wait, mt = fireCount(t) ≥ 3. Let's think about mt=3 (minimum for ternary).
3 phases. Each binary fires once per full-walk phase. If ALL 3 phases
are full-walks: each binary fires 3 times (odd). Needs even total. Contradiction!

If mt = 3 and one phase is full-walk: 1 fire. Other 2 phases contribute
even total together (to make odd+even = even... no, odd+odd = even, or odd+even = odd).
Actually: binary fires 1 time in sorry phase. Total must be even.
Other 2 phases: total fires for this binary = even - 1 = odd.
One phase contributes J_i or K_i fires (this binary fires J_i or K_i times).
So sum over 2 phases = odd. Individual phases: at least one has odd fires.

But the code is trying to show J_i + K_i ≤ 1 for EACH phase. If a phase
has J_i = K_i = 0 (neither L nor R fires): L fires 0 times, R fires 0 times.
If J_i + K_i = 1: either J=1 K=0 or J=0 K=1.

With sorry phase having J=1 K=1 (mixed), total fc(L) ≥ 1, fc(R) ≥ 1.
Other phases: fc(L)_rest + fc(R)_rest = fc(L)+fc(R) - 2.
Under J+K ≤ 1 per phase: fc(L)_rest+fc(R)_rest ≤ 2 (for 2 remaining phases).
So fc(L)+fc(R) ≤ 4.

But binary parity: fc(L) even, fc(R) even. Minimum: fc(L)=2, fc(R)=2.
Total: 4. Under ≤4: fc(L)=fc(R)=2. Each contributes exactly 1 fire per phase.
3 phases: sorry has J=K=1, two others have J+K=1 each.
fc(L)=2 means L fires in sorry + one more phase = 2. ✓
fc(R)=2 means R fires in sorry + one more phase = 2. ✓

So it's STRUCTURALLY possible. The sorry case is NOT vacuously true
based on fire counts alone.

BUT: what about the third binary processor? (h3bin says ≥ 3 binary.)
With ms = [2,3,2,3,2,3,3,3,3] at n=9: binaries at 0,2,4.
In the sorry phase (full walk), all 3 binaries fire once each.
Over the cycle, each must fire even times.
mt=3: sorry phase contributes 1 fire each.
Other 2 phases contribute odd fires each (for each binary).
With J+K ≤ 1 per phase: each non-sorry phase has at most 1 fire of
L (=proc 0) and 1 fire of R (=proc 2). But binary proc 4 also fires
in the sorry phase.

Wait, proc 4 isn't L or R for t=1. It's an intermediate processor.
The J/K counting is only for L(=proc 0) and R(=proc 2).
Proc 4 fires in phases but isn't tracked by J/K.

For proc 4 (binary, m=2): fires 1 time in sorry phase, needs even total.
So other phases: odd total fires for proc 4.
In one-sided phases (J+K=1): proc 4 might fire 0 or more times.
With 2 remaining phases: proc 4 fires odd total times in them.

This doesn't immediately give a contradiction. Let me think differently.

ALTERNATIVE: The sorry case needs a full ring walk from R to L.
Under ¬EC with gap1_ec, consecutive movers must be adjacent.
The walk R→RR→...→LL→L means movers at consecutive steps WITHIN the phase
are ring-adjacent. This walk has n-1 steps (visiting n-1 processors).

For n ≥ 9: this walk visits 8 processors. The boundary triples at each
intermediate processor might be forced to repeat across different phases.

Actually, let me try a COMPLETELY DIFFERENT approach. Instead of finding EC,
maybe we can show the full-ring-walk is impossible by counting arguments.

In the full-ring-walk phase (say sorry-R: L at a, walk CCW to RR, then R):
  Step a: L fires
  Step a+1: LL fires
  Step a+2: left³t fires
  ...
  Step a+n-3: RR fires
  Step a+n-2: R fires??? No, R fires at fR which is the LAST step before T.

Wait, I got confused. Let me re-read.

Sorry 2: fR = a (R fires first, at step a), fL > a (L fires later).
Phase: step a has mover R. Then walk to L.
  a: R
  a+1: RR (adj to R)
  a+2: right³t (adj to RR)
  ...
  a+n-3: LL (adj to left³t)
  a+n-2: L (adj to LL)
  Then t fires at step s = a + n - 1.

So fL = a + n - 2. The walk covers n-1 processors in n-1 steps.

In this walk: R fires at step a, and L fires at step a+n-2.
BOTH fire. It's mixed with J=1, K=1 (minimum mixed).

Now: what about processor 4 (binary)? It fires at step a+2 (in the walk).
Its boundary triple at that step: (right³t_val, proc4_val, proc5_val).
Wait, need to identify positions.

For n=9, t=1: R=2, RR=3, right³t=4, right⁴t=5, right⁵t=6, right⁶t=7, LL=8, L=0.
Walk: 2,3,4,5,6,7,8,0, then 1.
Proc 4 (= right³t) fires at step a+2.
Its neighbors: 3 (=RR) and 5 (=right⁴t).
Boundary at step a+2: (val_3_at_a+2, val_4_at_a+2, val_5_at_a+2).
  - val_3: RR fired at step a+1, so changed. val_3 = new value.
  - val_4: hasn't fired yet. val_4 = original.
  - val_5: hasn't fired yet. val_5 = original.
Mover triple: (val_3_new, val_4_old, val_5_old).

At step a: mover is R=2. Proc 4 is non-mover. Boundary:
  (val_3_old, val_4_old, val_5_old).
EC at proc 4: (val_3_new, val_4_old, val_5_old) vs (val_3_old, val_4_old, val_5_old).
These differ iff val_3_new ≠ val_3_old. RR fired, so val_3_new ≠ val_3_old. No EC.

At step a+1: mover is RR=3. Proc 4 is non-mover. Boundary:
  (val_3_old, val_4_old, val_5_old). WAIT: at step a+1, the config is AFTER
  step a (R fired). So val_3 at step a+1 = val_3_old (RR hasn't fired yet).
  val_2 changed (R fired). But proc 4's left neighbor is proc 3, not proc 2.
  So boundary at proc 4 at step a+1: (val_3_old, val_4_old, val_5_old).

  At step a+2 (proc 4 fires): boundary = (val_3_new, val_4_old, val_5_old).
  Diff from step a+1: val_3_old vs val_3_new. Different (RR fired at a+1).

So within the phase: no EC at proc 4 between any non-mover and mover step.

ACROSS PHASES: proc 4 also fires in other phases. And it's a non-mover in
other phases too. The mover triple in this phase is (val_3_new, val_4_old, val_5_old).
If in another phase, proc 4 is non-mover with the same triple: EC.

This is a GLOBAL check. Let me actually test it.
"""

import random
from collections import defaultdict

random.seed(42)

def find_cycles_with_fullwalk(n, ms, t, num_trials=5000000):
    """Find good cycles and check for mixed full-walk phases."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    stats = defaultdict(int)
    noec_fullwalk = []

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

                    # Check all-adj + no EC
                    all_adj = all(
                        min((cycle_movers[k] - cycle_movers[(k+1)%CL]) % n,
                            (cycle_movers[(k+1)%CL] - cycle_movers[k]) % n) <= 1
                        for k in range(CL))

                    if not all_adj:
                        stats['nonadj'] += 1
                        break

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

                    # Check for full-walk mixed phases
                    t_fires = [k for k in range(CL) if cycle_movers[k] == t]
                    for idx in range(len(t_fires)):
                        s_step = t_fires[idx]
                        prev_t = t_fires[(idx-1) % len(t_fires)]
                        a_step = (prev_t + 1) % CL
                        phase = []
                        k = a_step
                        while k != s_step:
                            phase.append(cycle_movers[k])
                            k = (k + 1) % CL
                        procs = set(phase)
                        if lt in procs and rt in procs and len(procs) == n-1 and t not in procs:
                            stats['fullwalk_noec'] += 1
                            noec_fullwalk.append((cycle_configs, cycle_movers, sys_f, t_fires, idx))
                            break

                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

        if len(noec_fullwalk) >= 20:
            break

        if trial % 1000000 == 999999:
            print(f"  Trial {trial+1}: {dict(stats)}")

    return stats, noec_fullwalk


def main():
    # Test at multiple n values with sub-threshold product
    # ms with ≥3 binary, product < 4·3^(n-2)
    configs = [
        (5, [2, 3, 2, 3, 3], 1),  # product = 108, threshold = 36
        (7, [2, 3, 2, 3, 3, 3, 3], 1),  # product = 972, threshold = 324
        (9, [2, 3, 2, 3, 2, 3, 3, 3, 3], 1),  # product = 5832, threshold = 2916
    ]

    for n, ms, t in configs:
        print(f"\n=== n={n}, ms={ms}, t={t} ===")
        print(f"  Product: {1}")
        prod = 1
        for m in ms:
            prod *= m
        print(f"  Product: {prod}, threshold 4*3^{n-2} = {4 * 3**(n-2)}")

        stats, results = find_cycles_with_fullwalk(n, ms, t, num_trials=3000000)
        print(f"  Stats: {dict(stats)}")
        print(f"  Full-walk ¬EC phases: {len(results)}")

        if results:
            # Analyze first example in detail
            configs0, movers0, sys_f0, t_fires0, idx0 = results[0]
            CL = len(configs0)
            print(f"\n  First example: cycle length {CL}")
            print(f"    Movers: {movers0}")
            print(f"    t fires: {t_fires0}")

            # Show all phases
            for pi in range(len(t_fires0)):
                s_step = t_fires0[pi]
                prev_t = t_fires0[(pi-1) % len(t_fires0)]
                a_step = (prev_t + 1) % CL
                phase = []
                k = a_step
                while k != s_step:
                    phase.append(movers0[k])
                    k = (k + 1) % CL
                procs = set(phase)
                has_L = (t-1)%n in procs
                has_R = (t+1)%n in procs
                is_fullwalk = len(procs) == n-1 and t not in procs
                label = "FULLWALK" if is_fullwalk else ("mixed" if has_L and has_R else "one-sided")
                print(f"    Phase {pi}: [{a_step},{s_step}) movers={phase} [{label}]")

    # ALSO: check sub-threshold constraint
    print("\n\n=== KEY CHECK: Is the product sub-threshold? ===")
    for n, ms, t in configs:
        prod = 1
        for m in ms:
            prod *= m
        threshold = 4 * 3**(n-2)
        print(f"  n={n}: product={prod}, threshold={threshold}, sub? {prod < threshold}")
        # The sorry only matters for sub-threshold systems


if __name__ == '__main__':
    main()
