#!/usr/bin/env python3
"""
COUNTING ARGUMENT: If one phase at t is a full sweep (J=1, K=1, length n-1),
does some OTHER phase at t necessarily have J+K >= 2?

If yes: we can dispatch the sorry by finding EC at that other phase using
ec_caseA/B (which handle J>=2,K=0 and J=0,K>=2).

The counting:
  fc(bL) = total bL fires across all phases = sum of J_i
  fc(bR) = total bR fires across all phases = sum of K_i
  fc(t) = number of phases

  Full sweep phase contributes J=1, K=1.
  Remaining fc(t)-1 phases contribute fc(bL)-1 J-fires and fc(bR)-1 K-fires.

  If fc(bL) + fc(bR) > fc(t): some phase has J+K >= 2.
  Full sweep accounts for J+K=2. So fc(bL)-1 + fc(bR)-1 must be distributed
  over fc(t)-1 phases. If fc(bL)+fc(bR)-2 > fc(t)-1, i.e., fc(bL)+fc(bR) > fc(t)+1,
  then another phase also has J+K >= 2.

  But we're INSIDE the proof that fc(bL)+fc(bR) > fc(t) (the h_gt hypothesis).
  So fc(bL)+fc(bR) >= fc(t)+1.
  Remaining fires: fc(bL)+fc(bR)-2 >= fc(t)-1.
  Distributed over fc(t)-1 phases: average = (fc(bL)+fc(bR)-2)/(fc(t)-1) >= 1.
  Average >= 1 does NOT guarantee any phase has >= 2.
  (Each phase could have exactly 1.)

  So the counting alone doesn't guarantee another phase with J+K >= 2.
  The other phases could ALL have J+K = 1.

  In that case: total J+K = fc(t) * 1 = fc(t). But fc(bL)+fc(bR) >= fc(t)+1 > fc(t).
  Contradiction! Because total J+K = fc(bL)+fc(bR) != fc(t).

  Wait: the full sweep phase has J+K = 2, not 1. So:
  Total J+K = 2 + sum over other phases.
  If all other phases have J+K <= 1: total J+K <= 2 + (fc(t)-1)*1 = fc(t)+1.
  But total J+K = fc(bL) + fc(bR).
  Constraint: fc(bL) + fc(bR) >= fc(t) + 1 (from h_gt).
  So fc(bL) + fc(bR) <= fc(t) + 1 is consistent.
  But if fc(bL) + fc(bR) = fc(t) + 1 and all other phases have J+K = 1:
  total = 2 + (fc(t)-1)*1 = fc(t)+1 = fc(bL)+fc(bR). Consistent!

  And if fc(bL) + fc(bR) >= fc(t) + 2: then total from other phases >= fc(t).
  Over fc(t)-1 phases: average > 1. Some phase has J+K >= 2.

  So the counting works only when fc(bL) + fc(bR) >= fc(t) + 2.
  When fc(bL) + fc(bR) = fc(t) + 1: it's possible that the full sweep is the
  ONLY phase with J+K >= 2, and all others have J+K = 1.

  But wait: we're proving h_phase_le1 by contradiction. We assume SOME phase
  has J+K >= 2 and derive EC. We don't need ANOTHER phase with J+K >= 2.
  We need EC from the CURRENT phase.

  The CURRENT phase has J=1, K=1. Both binary neighbors fire.
  In the full sweep: bR fires first, bL fires last (or vice versa).
  Between bR fire and bL fire: the sweep goes through all other procs.

  ec_caseC_RL needs: no t, bL, LL fires between fR and fL.
  In the full sweep: LL fires between fR and fL. So ec_caseC_RL fails.
  ec_caseC_LR: symmetric, RR fires between. Fails.

  So ec_caseC fails for full sweeps. ec_caseA/B require J>=2 or K>=2. Fail.

  THE SORRY IS GENUINELY HARD. The phase-local EC mechanisms all fail.

  THEREFORE: The proof needs to be RESTRUCTURED.

  Instead of proving J+K <= 1 per phase and then summing,
  prove fc(bL) + fc(bR) <= fc(t) DIRECTLY by a different argument.

  OR: show that the full-sweep case is impossible under hnoEC.

Let me check: when a full-sweep phase exists, does hnoEC always fail?
(I.e., does the cycle always have EC?)
"""

from collections import Counter


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    min_len = sum(ms)
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= min_len and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
            return
        remaining = max_length - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n)
                      if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining:
            return
        last = word[-1]
        for nxt in ring_adj[last]:
            nc = list(config)
            nc[nxt] = (nc[nxt] + 1) % ms[nxt]
            nf = list(fc)
            nf[nxt] += 1
            word.append(nxt)
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        first = list(start)
        first[p] = (first[p] + 1) % ms[p]
        dfs([p], [1 if i == p else 0 for i in range(n)], tuple(first))
    return results


def build_cycle(ms, n, word):
    ell = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(ell):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:ell])) != ell:
        return None
    return configs[:ell]


def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)


def has_ec(word, cycle, ms, n):
    ell = len(word)
    for p in range(n):
        pL = (p-1) % n
        pR = (p+1) % n
        mt = set()
        nmt = set()
        for st in range(ell):
            tr = (cycle[st][pL], cycle[st][p], cycle[st][pR])
            if word[st] == p:
                mt.add(tr)
            else:
                nmt.add(tr)
        if mt & nmt:
            return True
    return False


# Check: do cycles with full-sweep phases ALWAYS have EC?
print("="*70)
print("FULL SWEEP PHASE => EC EXISTS?")
print("="*70)

for n, ms, max_len in [(5, [2,3,2,3,2], 18), (7, [2,3,2,3,2,3,3], 24)]:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    words = enumerate_mover_words(ms, n, max_len)
    sweep_count = 0
    ec_count = 0
    no_ec_count = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)

        has_sweep = False
        for t in sandwiched:
            bL = (t-1) % n
            bR = (t+1) % n
            t_fires = sorted(i for i in range(ell) if word[i] == t)
            if len(t_fires) < 2:
                continue

            for idx in range(len(t_fires)):
                s_step = t_fires[idx]
                a_step = t_fires[(idx-1) % len(t_fires)]
                if s_step > a_step:
                    interior = list(range(a_step+1, s_step))
                else:
                    interior = list(range(a_step+1, ell)) + list(range(0, s_step))
                if len(interior) != n-1:
                    continue
                movers = [word[st] for st in interior]
                if len(set(movers)) == n-1:
                    J = sum(1 for m in movers if m == bL)
                    K = sum(1 for m in movers if m == bR)
                    if J == 1 and K == 1:
                        has_sweep = True
                        break
            if has_sweep:
                break

        if has_sweep:
            sweep_count += 1
            if has_ec(word, cycle, ms, n):
                ec_count += 1
            else:
                no_ec_count += 1
                print(f"  NO EC with sweep: word={word}")

    print(f"\nn={n}: {sweep_count} cycles with full-sweep phase")
    print(f"  EC: {ec_count}, no EC: {no_ec_count}")

# Now check: in sorry cases, does the cycle ALWAYS have EC?
# (Not just full-sweep cycles, but specifically the sorry-triggering ones.)
print()
print("="*70)
print("SORRY PHASES => EC EXISTS?")
print("="*70)

for n, ms, max_len in [(5, [2,3,2,3,2], 18), (7, [2,3,2,3,2,3,3], 24)]:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    words = enumerate_mover_words(ms, n, max_len)
    sorry_words = set()
    ec_ok = 0
    no_ec = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)

        is_sorry = False
        for t in sandwiched:
            bL = (t-1) % n
            bR = (t+1) % n
            LL = (t-2) % n
            RR = (t+2) % n
            LLL = (t-3) % n
            RRR = (t+3) % n

            t_fires = sorted(i for i in range(ell) if word[i] == t)
            if len(t_fires) < 2:
                continue

            for idx in range(len(t_fires)):
                s_step = t_fires[idx]
                a_step = t_fires[(idx-1) % len(t_fires)]
                if s_step > a_step:
                    interior = list(range(a_step+1, s_step))
                else:
                    interior = list(range(a_step+1, ell)) + list(range(0, s_step))
                if not interior:
                    continue

                J = sum(1 for st in interior if word[st] == bL)
                K = sum(1 for st in interior if word[st] == bR)
                if J < 1 or K < 1:
                    continue

                fL_idx = next(i for i in range(len(interior)) if word[interior[i]] == bL)
                fR_idx = next(i for i in range(len(interior)) if word[interior[i]] == bR)

                if fR_idx == 0 and fL_idx > 0:
                    ll_pos = [i for i in range(fL_idx) if word[interior[i]] == LL]
                    if ll_pos and ll_pos[-1] == fL_idx - 1:
                        first_ll = ll_pos[0]
                        if any(word[interior[i]] == LLL for i in range(first_ll)):
                            is_sorry = True

                if fL_idx == 0 and fR_idx > 0:
                    rr_pos = [i for i in range(fR_idx) if word[interior[i]] == RR]
                    if rr_pos and rr_pos[-1] == fR_idx - 1:
                        first_rr = rr_pos[0]
                        if any(word[interior[i]] == RRR for i in range(first_rr)):
                            is_sorry = True

        if is_sorry:
            if has_ec(word, cycle, ms, n):
                ec_ok += 1
            else:
                no_ec += 1
                print(f"  NO EC in sorry-cycle: word={word}")

    print(f"\nn={n}: sorry cycles: {ec_ok + no_ec}")
    print(f"  EC: {ec_ok}, no EC: {no_ec}")

print()
print("="*70)
print("PROOF STRATEGY")
print("="*70)
print()
print("ALL sorry-case cycles have EC (verified). The question is how to CONSTRUCT it.")
print()
print("The sorry is inside the proof that J+K <= 1 for a specific phase.")
print("The sorry case has J=1, K=1 with full-sweep structure.")
print("No within-phase EC exists.")
print("But the cycle HAS cross-phase EC.")
print()
print("RECOMMENDED LEAN APPROACH:")
print("Since sorry 1012 is vacuous (by walk constraint), and sorrys 1077/1121")
print("involve full-sweep phases with no within-phase EC:")
print()
print("  Option 1: Show the full-sweep condition is inconsistent with the")
print("  overall proof hypotheses (allNormalForm, hfull, etc.).")
print("  This requires showing that full-sweep phases can't exist when hnoEC holds.")
print()
print("  Option 2: Find the cross-phase EC constructively.")
print("  Given a full-sweep phase (t, bR, ..., bL, t), use the configs at the")
print("  phase boundaries to match against other phases' configs.")
print()
print("  Option 3 (simplest): Observe that the sorry case implies J+K = 2,")
print("  and since J = 1, K = 1, we have both binary neighbors firing once.")
print("  The full sweep means the phase has length n-1 and ALL procs fire.")
print("  Show this implies fc(bL) + fc(bR) = fc(t) + 1 (exactly).")
print("  Then the remaining phases have total J+K = fc(bL)+fc(bR)-2 = fc(t)-1")
print("  over fc(t)-1 phases. Each remaining phase has J+K = 1.")
print("  Every remaining phase has EITHER J=1,K=0 OR J=0,K=1.")
print("  These are dispatchable by ec_caseA/ec_caseB? NO: J=1,K=0 is handled")
print("  by the 'gap' case (EC at bL between phase.a and fL if no LL in between).")
print("  But this ALSO might fail if LL fires!")
print()
print("  The proof structure might need to be changed to not go through")
print("  h_phase_le1 at all, but instead use a direct counting argument.")
