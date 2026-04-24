#!/usr/bin/env python3
"""
FINAL ANALYSIS: EC construction for the mixed-phase sorry cases.

=== SORRY 1 (line 1012): VACUOUSLY TRUE ===

Context: fL > a AND fR > a.
Proof: moverAt(a) must be ring-adjacent to moverAt(a-1) = t.
  So moverAt(a) ∈ {lt, t, rt}. Since t doesn't fire in phase: moverAt(a) ∈ {lt, rt}.
  If moverAt(a) = lt: fL = a (contradicts fL > a).
  If moverAt(a) = rt: fR = a (contradicts fR > a).
  QED.

Lean proof: apply gap1_ec to get moverAt(a) ∈ {lt, t, rt}, use phase.ht_nofire
to exclude t, then show fL=a or fR=a.

=== SORRYS 2,3 (lines 1077, 1121): THE REAL ISSUE ===

The chain extends backward: left^k(t) fires before left^(k-1)(t) for all k up
to some point. The mk_ec construction fails because at each level, the left
neighbor fires in the interval, changing the boundary triple.

=== PROPOSED FIX: Reformulate using ec_caseC_RL/LR instead of mk_ec ===

ec_caseC_RL(fR, fL): EC between R-fire (fR) and L-fire (fL) with fR < fL.
  Requires: no t, L, LL fires in [fR, fL).
  In sorry-2 context: fR = a, fL > a.
  - No t: phase condition.
  - No L: fL is first L fire, so no L before fL.
  - No LL: THIS is the case split. If LL fires: sorry.

But wait, what if we DON'T use ec_caseC_RL and instead try a DIFFERENT pair?

=== ALTERNATIVE: Use gap1_ec at an interior mover step ===

Consider the step where left³(t) fires in [a, fLL). Call it fL3.
At step fL3: mover = left³(t).
At step fL3-1: mover = some processor X.
gap1_ec says X must be ring-adjacent to left³(t).
Ring-adj to left³(t) = {left⁴(t), left²(t)}.
left²(t) = LL, which hasn't fired yet (fLL > fL3).
So X ∈ {left⁴(t), left³(t)} or X = left²(t).
But left²(t) = LL hasn't fired: X ≠ LL (unless LL fires before fL3, but fL3 < fLL = first LL fire).

Wait: X is the mover at fL3-1. What is it?
Under gap1_ec: moverAt(fL3) adj to moverAt(fL3-1). So moverAt(fL3-1) adj to left³(t).
Adjacent to left³(t): {left⁴(t), left²(t)}.
Also left³(t) itself (self-adjacent in gap1_ec).
Can moverAt(fL3-1) = left²(t) = LL? Only if LL fires at fL3-1 < fL3 < fLL.
But fLL is the FIRST LL fire. So fL3-1 < fLL → LL hasn't fired → moverAt(fL3-1) ≠ LL.
So moverAt(fL3-1) ∈ {left⁴(t), left³(t)}.

If moverAt(fL3-1) = left³(t): left³(t) fires TWICE (at fL3-1 and fL3).
But between these, the config must differ. After fL3-1: left³(t) changes.
At fL3: left³(t) fires again. The config at fL3 has left³(t) = new value,
neighbors potentially changed. Config at fL3-1 and fL3: differ only at left³(t)
(since no other processor fires between them). So configs differ. OK, possible.

If moverAt(fL3-1) = left⁴(t): we extend the chain.

The chain can continue: at each step, moverAt(k-1) ∈ {left^(i+1)(t), left^i(t)}.
Either the chain extends (left^(i+1) fires), or a processor re-fires.

=== KEY INSIGHT: RE-FIRE CREATES EC ===

If left³(t) fires twice (at fL3-1 and fL3):
  At step fL3-1: left³(t) fires. Boundary at left³(t) = (left⁴_val, l3t_val, LL_val).
  At step fL3: left³(t) fires AGAIN. Boundary = (left⁴_val, l3t_new, LL_val).
  These are MOVER triples for left³(t). Both different (l3t_val ≠ l3t_new since it fired).

  But between fL3-1 and fL3, only left³(t) fires (no other processor fires in between
  since they're consecutive steps). At step fL3-1, left³(t) is the mover.
  There's NO non-mover step for left³(t) between these two fires.

  Actually: at step fL3: the config is post-fire-at-fL3-1. left³(t) = l3t_new.
  left³(t) fires again: l3t_new changes to l3t_new2.
  This step has boundary (left⁴_val, l3t_new, LL_val). This is a mover triple.

  Now: is (left⁴_val, l3t_new, LL_val) ever a non-mover triple for left³(t)?
  At step fL3-1: boundary was (left⁴_val, l3t_val, LL_val). Mover triple.
  At ALL steps before fL3-1 in [a, fL3-1): left³(t) hasn't fired.
  So l3t at those steps = l3t_val. And left⁴ and LL haven't changed either
  (if they don't fire before fL3-1).

  The non-mover triples for left³(t) before fL3-1: all (left⁴_val, l3t_val, LL_val).
  The mover triple at fL3: (left⁴_val, l3t_new, LL_val).
  l3t_new ≠ l3t_val: NO EC.

  After fL3: left³(t) = l3t_new2. Non-mover triples have l3t = l3t_new2.
  Mover triple at fL3 had l3t = l3t_new ≠ l3t_new2. No EC.

  So re-fire does NOT create EC either.

=== ALTERNATIVE APPROACH: Use sub-threshold product bound ===

The sub-threshold condition means: product of all state sizes < 4·3^(n-2).
With ≥3 binary: product ≤ 2^3 · 3^(n-3) = 8·3^(n-3) (if exactly 3 binary,
rest ternary). For n ≥ 9: 8·3^6 = 5832 < 8748 = 4·3^7. OK, sub-threshold.

The cycle length CL ≤ product (all configs distinct).
The sorry phase has n steps (full ring walk).
With mt ≥ 3 phases (t fires ≥ 3 times), cycle ≥ 3n.
At n=9: CL ≥ 27. Product = 5832. Lots of room.

The sub-threshold doesn't directly constrain phase structure.

=== PROPOSED PROOF APPROACH ===

The sorry cases 2 and 3 can be closed by:

1. Proving that sorry 1 is vacuously true (simple Lean proof using gap1_ec).

2. For sorrys 2 and 3: Instead of trying mk_ec at deeper levels, use the
   fact that the mover sequence from step a to fL (or fR) is a CONTIGUOUS
   ring walk from rt to lt (or lt to rt). This walk visits every processor
   between rt and lt (going the long way around).

   The key lemma: if a contiguous ring walk visits a third binary processor b
   (guaranteed by h3bin + ring topology), then b fires once in this walk.
   Combined with b firing once in the phase, b's parity requires odd fires
   in other phases.

   Actually, this doesn't directly give EC. But:

3. SIMPLEST FIX: In the sorry case, we have left³(t) fires in [a, fLL).
   This means there's a contiguous chain: R, ..., left³(t), LL, L fires
   in the phase. The chain covers at least 3 processors (left³(t), LL, L)
   on the left side, plus R on the right.

   Use ec_caseC_LR(fL, fR'): EC between first L fire and LAST R fire.
   Wait, we need a SECOND R fire for this. With J=K=1 (minimum mixed):
   only one L fire and one R fire. Can't pair them differently.

   With J=1, K=1: ec_caseC_RL uses fR < fL. Requires no t, L, LL in [fR, fL).
   LL fires in [fR, fL): blocked.

   ec_caseC_LR uses fL < fR. Not applicable since fR = a < fL.

4. SIMPLEST ACTUAL FIX: Prove the sorry at line 1129 (h_sparse) DIRECTLY,
   bypassing the per-phase argument entirely. Use the fire count decomposition
   + the normalForm_gap_constraint to sum: total J+K = fc(L)+fc(R), with
   each phase contributing J+K ≥ 1 and not both even. This gives
   fc(L)+fc(R) ≥ fc(t) AND not-both-even per phase. The sparse bound
   fc(L)+fc(R) ≤ fc(t) then follows from the contradiction that
   fc(L)+fc(R) > fc(t) would force a phase with both-even J,K or J≥2,K=0.

Wait, that IS what the code tries. The issue is specifically the mixed case
(J≥1, K≥1). In this case, the code tries to show EC, but fails for the
sorry pattern.

5. ACTUAL PROPOSED FIX:

Instead of showing each mixed phase has EC, show that having ANY mixed phase
contradicts the normalForm assumption for ANOTHER phase.

Specifically: if phase i is mixed (J≥1, K≥1), then its full-ring-walk structure
forces the NEXT phase (phase i+1) to start with a specific mover pattern that
triggers a mechanism (contradicting normalForm for phase i+1).

This "cross-phase propagation" argument avoids needing EC within the mixed phase.
"""

# Let me verify the cross-phase argument computationally.
# At n=5, all mixed phases are full-ring-walks. Let me check if the
# NEXT phase in the same cycle is also mixed or triggers a mechanism.

import random
from collections import defaultdict

random.seed(42)

def find_noec_cycles_with_phases(n, ms, t, num_trials=5000000):
    """Find ¬EC all-adj cycles and analyze phase structure."""
    lt = (t - 1) % n
    rt = (t + 1) % n
    results = []
    seen = set()

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

        for step in range(3000):
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

                if CL >= n:
                    all_adj = all(
                        min((cycle_movers[k] - cycle_movers[(k+1)%CL]) % n,
                            (cycle_movers[(k+1)%CL] - cycle_movers[k]) % n) <= 1
                        for k in range(CL))
                    if not all_adj:
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
                        break

                    key = tuple(cycle_movers)
                    if key not in seen:
                        seen.add(key)
                        results.append((cycle_configs, cycle_movers, sys_f))

                break
            history.append(config)
            history_movers.append(p)
            config_to_step[config] = step + 1

    return results


def analyze_all_phases(n, ms, configs, movers, t):
    lt = (t-1) % n
    rt = (t+1) % n
    CL = len(configs)
    t_fires = [k for k in range(CL) if movers[k] == t]
    if not t_fires:
        return []

    phases = []
    for idx in range(len(t_fires)):
        s = t_fires[idx]
        prev_t = t_fires[(idx-1) % len(t_fires)]
        a = (prev_t + 1) % CL

        phase_movers = []
        k = a
        while k != s:
            phase_movers.append(movers[k])
            k = (k + 1) % CL

        J = sum(1 for m in phase_movers if m == lt)
        K = sum(1 for m in phase_movers if m == rt)

        phase_type = 'mixed' if J >= 1 and K >= 1 else ('L-only' if J >= 1 else ('R-only' if K >= 1 else 'neither'))
        phases.append({
            'a': a, 's': s, 'movers': phase_movers, 'J': J, 'K': K, 'type': phase_type
        })

    return phases


def main():
    n = 5
    ms = [2, 3, 2, 3, 3]
    t = 1

    print(f"n={n}, ms={ms}, t={t}")
    cycles = find_noec_cycles_with_phases(n, ms, t, num_trials=5000000)
    print(f"Unique ¬EC all-adj cycles: {len(cycles)}")

    print("\n=== Phase structure of all ¬EC all-adj cycles ===")
    type_combos = defaultdict(int)

    for ci, (configs, movers, sys_f) in enumerate(cycles):
        phases = analyze_all_phases(n, ms, configs, movers, t)
        if not phases:
            continue

        types = tuple(p['type'] for p in phases)
        type_combos[types] += 1

    print("\nPhase type combinations:")
    for combo, count in sorted(type_combos.items(), key=lambda x: -x[1]):
        print(f"  {combo}: {count}")

    # Look at cycles where ALL phases are mixed
    print("\n=== Cycles where ALL phases are mixed ===")
    for ci, (configs, movers, sys_f) in enumerate(cycles):
        phases = analyze_all_phases(n, ms, configs, movers, t)
        if not phases:
            continue
        if all(p['type'] == 'mixed' for p in phases):
            CL = len(configs)
            print(f"\n  Cycle {ci}: CL={CL}, movers={movers}")
            for pi, p in enumerate(phases):
                print(f"    Phase {pi}: [{p['a']},{p['s']}) J={p['J']} K={p['K']} movers={p['movers']}")

            # Check fire counts
            fc = defaultdict(int)
            for m in movers:
                fc[m] += 1
            print(f"    Fire counts: {dict(fc)}")
            for p in range(n):
                if ms[p] == 2:
                    print(f"      Binary proc {p}: fc={fc[p]} ({'even' if fc[p]%2==0 else 'ODD!'})")


if __name__ == '__main__':
    main()
