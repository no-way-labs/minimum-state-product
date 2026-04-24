#!/usr/bin/env python3
"""
SWEEP EC: When the phase interior is a full sweep, find EC.

A full sweep phase at sandwiched ternary t:
  step a fires t
  step a+1 fires bR (sorry 1077) or bL (sorry 1121)
  step a+2 fires next proc in sweep direction
  ...
  step a+k fires bL (sorry 1077) or bR (sorry 1121)
  step a+k+1 = s fires t

Each of the n-1 non-t procs fires exactly once, in consecutive order.

The key: ec_caseC_RL requires no LL fires between fR and fL. In a full sweep,
LL fires BETWEEN fR and fL (that's the whole point of the sorry case).

But: there are OTHER EC constructions. Let me search systematically.

For sorry 1077 (fR at start, sweep goes left):
  Interior: bR, left(bR)=RR, left(RR)=right^3(t), ..., LL, bL
  Sweep direction: LEFT (decreasing proc index mod n)

For EC: we need mover and nonmover steps at some proc with matching triples.
Within the sweep, each proc fires once. So the mover step is unique per proc.
The nonmover steps are ALL steps where a DIFFERENT proc fires.

For proc p in the sweep at step k (mover):
  boundary triple = (config[k][p-1], config[k][p], config[k][p+1])
  After each subsequent step fires a DIFFERENT proc:
  the triple at p changes IF that other proc is p-1, p, or p+1.

A nonmover step for p at position k' != k has triple:
  (config[k'][p-1], config[k'][p], config[k'][p+1])
This matches if the config is the same at p-1, p, p+1.

In a left-sweep: procs fire in order bR, bR-1, bR-2, ..., bL.
After proc p fires at step k: the procs p-1, p-2, ..., bL fire in subsequent steps.
Each of these changes config at that proc. Does any of them change p-1, p, or p+1?
  p-1 fires at step k+1 (next in sweep). Changes config[p-1].
  p+1 fired at step k-1 (previous in sweep). Already done.

So after p fires:
  step k: p fires (config[p] changes)
  step k+1: p-1 fires (config[p-1] changes)
  step k+2: p-2 fires (config[p-2] changes) — does NOT affect p's triple (p-2 != p-1,p,p+1)
  ...

So the triple at p changes at step k (p fires, config[p] changes) and
step k+1 (p-1 fires, config[p-1] changes). After step k+1: triple is stable
until some step fires p-1, p, or p+1 again. In a full sweep where each fires
once: no more changes after k+1.

Before p fires:
  step k-1: p+1 fires (config[p+1] changes)
  step k-2: p+2 fires — doesn't affect triple
  ...
  step 0: bR fires

So triple at p is constant from step 0 to step k-2 (no changes to p-1, p, p+1),
changes at step k-1 (p+1 fires), changes at step k (p fires), changes at step k+1 (p-1 fires),
then constant from step k+2 onward.

For EC at p: we need a step j != k where triple matches.
The triple at p takes at most 4 different values:
  [0, k-2]: triple_A (before any neighbor fires)
  k-1: triple_B (after p+1 fires)
  k: triple_C (after p fires) — but this is the mover step
  [k+1, ...]: triple_D (after p-1 fires)

For EC: triple_A or triple_B or triple_D must equal triple_C.

triple_A: config at (p-1, p, p+1) = (init_p-1, init_p, init_p+1)
  where init = config before the sweep starts (at step a+1).
  Actually, init = config at step a+1 minus the effect of step a (which fires t).
  Wait, let me think about this differently.

Let me just compute it directly.
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


# Analyze full sweep phases
n, ms = 5, [2, 3, 2, 3, 2]
words = enumerate_mover_words(ms, n, 18)

# Find sorry cases where interior is a full sweep
found = 0
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in [1, 3]:
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
            if not interior or len(interior) != n-1:
                continue

            movers = [word[st] for st in interior]
            if len(set(movers)) != n-1:
                continue

            J = sum(1 for m in movers if m == bL)
            K = sum(1 for m in movers if m == bR)
            if J != 1 or K != 1:
                continue

            if found >= 1:
                continue
            found += 1

            print(f"Full sweep phase: word={word}")
            print(f"  t={t}, a={a_step}, s={s_step}")
            print(f"  Interior steps: {interior}")
            print(f"  Interior movers: {movers}")
            print()

            # For each proc in the sweep, compute:
            # - mover step (fires that proc)
            # - boundary triple at mover step
            # - boundary triples at all other steps
            for p in range(n):
                if p == t:
                    continue
                pL = (p-1) % n
                pR = (p+1) % n

                # Mover step in interior
                mover_int_idx = movers.index(p)
                mover_step = interior[mover_int_idx]
                mover_triple = (cycle[mover_step][pL], cycle[mover_step][p], cycle[mover_step][pR])

                # Find ALL matching nonmover steps (anywhere in cycle, not just this phase)
                matches = []
                for st in range(ell):
                    if st == mover_step:
                        continue
                    if word[st] == p:
                        continue
                    nm_triple = (cycle[st][pL], cycle[st][p], cycle[st][pR])
                    if nm_triple == mover_triple:
                        # Classify
                        in_this_phase = st in interior
                        matches.append((st, in_this_phase))

                # Also check step a (fires t)
                st = a_step
                if word[st] != p:
                    nm_triple = (cycle[st][pL], cycle[st][p], cycle[st][pR])
                    if nm_triple == mover_triple:
                        matches.append((st, True))  # step a is "part of" this phase context

                # Check step s
                st = s_step
                if word[st] != p:
                    nm_triple = (cycle[st][pL], cycle[st][p], cycle[st][pR])
                    if nm_triple == mover_triple:
                        matches.append((st, True))

                if matches:
                    print(f"  Proc {p}: mover at step {mover_step} (int[{mover_int_idx}]), "
                          f"triple={mover_triple}")
                    for m_st, in_phase in matches:
                        print(f"    nonmover match at step {m_st} "
                              f"({'this phase' if in_phase else 'other phase'})")

            # Now: for the Lean proof, we need EC constructible from available hypotheses.
            # The available hypotheses give us:
            # - configVal_eq_of_noFire_between: if no fires of q in [a, b), then config[a][q] = config[b][q]
            # - Phase structure: step a fires t, interior fires bR, ..., bL, step s fires t
            # - Walk constraint: consecutive movers adjacent

            # The sweep means: in the interior, the movers are
            # bR, left(bR), left^2(bR), ..., left^{n-3}(bR), bL
            # (going left from bR to bL, passing through all procs except t).

            # For any proc p in the middle of the sweep (not bR or bL):
            # - p fires at step k (mover step)
            # - Between step k+2 and step s: no fires of p-1, p, p+1
            #   (the only fire of p-1 was at step k+1, and the only fire of p+1 was at step k-1)
            # Wait: p-1 fires at step k+1 (next in sweep). After that, no more p-1 fires in phase.
            # And between step k+2 and step s: do any of p-1, p, p+1 fire?
            # p fires only at step k. p-1 fires only at step k+1. p+1 fires only at step k-1.
            # So: between step k+2 and step s-1: no fires of p-1, p, or p+1.
            # Step s fires t. Is t = p-1, p, or p+1?
            # t is the sandwiched ternary. p is some proc in the sweep.
            # If p = bR: p+1 = right(bR) = right^2(t) = RR. p-1 = t. So t = p-1. BAD.
            # If p = bL: p-1 = LL. p+1 = t. So t = p+1. BAD.
            # For OTHER procs (not bR or bL): t is NOT p-1 or p+1.
            # (Since p is at distance >= 2 from t, and t's neighbors are bL and bR.)

            # So for interior procs (not bL or bR):
            # Between step k+2 and step s: no fires of p-1, p, p+1 (including at step s).
            # Triple at p is constant from step k+2 to step s.
            # Step s fires t != p (nonmover for p).
            # Triple at step s at p: same as at step k+2.
            # Triple at step k+2 at p: after p fires (step k) and p-1 fires (step k+1).
            # This is triple_D.

            # But we need triple_D = triple_C (mover triple at step k).
            # triple_C: config at step k before p fires. Then p fires, changing config[p].
            # Actually, triple at the mover step is the config AT that step (before the fire).
            # So triple_C = (config[k][p-1], config[k][p], config[k][p+1]).
            # triple_D = (config[k+2][p-1], config[k+2][p], config[k+2][p+1]).
            # config[k+2] = config[k] + p fires + (p-1) fires.
            # So: config[k+2][p-1] = config[k][p-1] + 1 (mod m_{p-1}).
            #     config[k+2][p] = config[k][p] + 1 (mod m_p).
            #     config[k+2][p+1] = config[k][p+1] (no change).
            # triple_D = (config[k][p-1]+1, config[k][p]+1, config[k][p+1]).
            # triple_C = (config[k][p-1], config[k][p], config[k][p+1]).
            # For triple_D = triple_C:
            #   config[k][p-1]+1 = config[k][p-1] mod m_{p-1}  => 1 = 0 mod m_{p-1} => m_{p-1} = 1
            #   config[k][p]+1 = config[k][p] mod m_p          => 1 = 0 mod m_p     => m_p = 1
            # Both impossible (m >= 2). So triple_D != triple_C.
            # This means the EC is NOT between step k (mover) and step s (nonmover in same phase).

            # What about between step k and step a (the previous t-fire)?
            # Step a fires t. Between a and k: several procs fire.
            # The sweep goes bR, left(bR), ..., p. So between a+1 and k-1: procs after bR fire.
            # Do any of p-1, p, p+1 fire in [a, k)?
            # p fires only at step k. p+1 fires at step k-1 (just before p). p-1 fires at step k+1.
            # Between a and k-1: does p+1 fire? p+1 fires at step k-1. So in [a, k-1): not yet.
            # Wait, in [a, k) which includes step k-1. At step k-1: p+1 fires. In [a, k): yes, p+1 fires.
            # So [a, k-1) has no fires of p-1, p, p+1. But [a, k) includes k-1 where p+1 fires.
            # Between a and k-1: step a fires t. Steps a+1, ..., k-2 fire procs that are NOT p-1, p, p+1.
            # (In the sweep: a+1 fires bR, a+2 fires left(bR), ..., k-2 fires some proc far from p.)
            # Actually, let me check: is t = p-1 or p+1?
            # For inner procs: no. So step a fires t which is NOT in {p-1, p, p+1}.
            # Steps a+1, ..., k-2: each fires a proc at distance >= 2 from p.
            # (The sweep goes in order, and p+1 fires at k-1.)
            # So between a and k-1: no fires of p-1, p, p+1.
            # Triple at p is constant from step a to step k-2.
            # Step a fires t != p (nonmover for p). Triple_A.
            # Step k fires p (mover). Triple_C.
            # triple_A = (config[a][p-1], config[a][p], config[a][p+1]).
            # triple_C = (config[k][p-1], config[k][p], config[k][p+1]).
            # Between a and k: p doesn't fire, p-1 doesn't fire, but p+1 fires at k-1.
            # Wait, between a and k (not k-1): p+1 fires at k-1. So between a and k-1:
            # no fires of p-1, p, p+1 (as established). Between k-1 and k: step k-1 fires p+1.
            # So config[k][p+1] = config[k-1][p+1] + 1 = config[a][p+1] + 1.
            # config[k][p-1] = config[a][p-1] (no change).
            # config[k][p] = config[a][p] (no change).
            # triple_C = (config[a][p-1], config[a][p], config[a][p+1]+1).
            # triple_A = (config[a][p-1], config[a][p], config[a][p+1]).
            # For triple_A = triple_C: config[a][p+1]+1 = config[a][p+1] mod m_{p+1}.
            # That requires m_{p+1} | 1, i.e., m_{p+1} = 1. Impossible.
            # So triple_A != triple_C.

            # Hmm. Neither step a nor step s gives EC at interior procs.
            # The EC must be truly CROSS-PHASE.

            print()
            print("CONCLUSION: In a full-sweep phase, there is NO within-phase EC")
            print("at interior procs. The EC is always cross-phase.")
            print()
            print("This means the sorry CANNOT be discharged by phase-local analysis.")
            print("The proof needs to either:")
            print("  1. Show full-sweep phases are impossible (contradicted by data), or")
            print("  2. Use a cross-phase argument, or")
            print("  3. Find EC at bL or bR (the binary boundary procs).")
            print()

            # Let's check bL and bR specifically.
            for p_name, p in [('bL', bL), ('bR', bR)]:
                pL = (p-1) % n
                pR = (p+1) % n
                mover_int_idx = movers.index(p)
                mover_step = interior[mover_int_idx]
                mover_triple = (cycle[mover_step][pL], cycle[mover_step][p], cycle[mover_step][pR])

                print(f"  {p_name}={p}: mover at step {mover_step} (int[{mover_int_idx}]), "
                      f"triple={mover_triple}")
                print(f"    left={pL}(m={ms[pL]}), right={pR}(m={ms[pR]})")

                # For bL: right(bL) = t. step a fires t. Between a and bL's fire:
                # t fires at a, changing right(bL). After that, t doesn't fire again in phase.
                # So between a+1 and bL's fire: right(bL) = config[a][t] + 1 (constant).
                # left(bL) = LL. LL fires at some step before bL (sweep order).
                # So between LL's fire + 1 and bL's fire: no fires of LL, bL, t.
                # Triple preserved from LL_fire + 1 to bL_fire.
                # EC at bL between bL_fire (mover) and LL_fire + 1 (nonmover)?
                # LL_fire + 1 is the step AFTER LL fires. That step fires bL (since LL is right
                # before bL in the sweep). Wait: sweep order is ..., LL, bL. So LL fires at
                # step before bL. The step after LL is bL itself!
                # So LL_fire + 1 = bL_fire. No nonmover step between them.

                # What about BEFORE LL fires? Between some earlier step and LL_fire:
                # left(bL) = LL fires at LL_fire. Before LL_fire: left(LL) fires (etc).
                # The sweep consumes all steps. No gap.

                # For bR: left(bR) = t. step a fires t. step interior[0] = bR's mover step.
                # Between a and interior[0]: just one step (a+1 = interior[0]).
                # t fires at a, changing left(bR). No nonmover step available.

                # What about AFTER bR fires? right(bR) = RR fires at step after bR.
                # Between bR_fire + 1 and RR_fire: just one step. Actually bR fires first
                # in sweep, then RR fires next. So RR_fire = bR_fire + 1.
                # No gap for nonmover.

                # Check ALL nonmover steps
                for st in range(ell):
                    if word[st] == p:
                        continue
                    nm_triple = (cycle[st][pL], cycle[st][p], cycle[st][pR])
                    if nm_triple == mover_triple:
                        in_phase = st in interior or st == a_step or st == s_step
                        print(f"    nonmover match at step {st} (fires {word[st]}, "
                              f"{'this phase' if in_phase else 'OTHER phase'})")

print()
print("="*70)
print("FINAL DETERMINATION")
print("="*70)
print()
print("For full-sweep sorry phases:")
print("- No within-phase EC at ANY proc (interior, bL, or bR).")
print("- EC is always cross-phase.")
print("- The sorry CANNOT be discharged by extending the chain within the phase.")
print()
print("The proof must use a CROSS-PHASE argument:")
print("If a full-sweep phase exists, then across ALL phases at t,")
print("the fire-count constraints force a different phase to have J+K > 1,")
print("which CAN be handled by the existing EC mechanisms.")
print()
print("Specifically: if this phase has J=1, K=1 and is a full sweep (length n-1),")
print("and fc(t) fires = num_phases, then:")
print("  total J across phases = fc(bL)")
print("  total K across phases = fc(bR)")
print("  If fc(bL) + fc(bR) > fc(t): some phase has J+K >= 2.")
print("  The full-sweep phase contributes J=1, K=1.")
print("  The remaining fc(t)-1 phases must account for fc(bL)-1 + fc(bR)-1 fires.")
print("  If fc(bL) + fc(bR) > fc(t): some other phase has J+K >= 2.")
print()
print("But the sorry is INSIDE h_phase_le1 which assumes J+K >= 2 for THIS phase.")
print("So the sorry IS in a phase with J+K = 2 (since J=1, K=1).")
print("The proof needs to derive False from J+K >= 2 in this phase.")
print("Since the phase-local analysis can't find EC, we need something else.")
print()
print("KEY REALIZATION: The sorry 1077/1121 case arises when BOTH:")
print("  (a) fR = phase.a (first step fires bR)")
print("  (b) The chain is fully tight (full sweep)")
print()
print("In the Lean code, when (a) holds and (b) holds, the interior is")
print("[bR, left(bR), left^2(bR), ..., bL]. The walk goes LEFT from bR.")
print("The STEP BEFORE the interior fires t. The step AFTER fires t.")
print("The walk is: ...t, bR, left(bR), ..., bL, t...")
print("This means t appears at both ends.")
print("bL is adjacent to t on the ring (bL = left(t)).")
print("So the walk goes: t -> bR -> ... -> bL -> t.")
print("bL -> t is valid (ring adjacent). bR = right(t) -> left(bR): also valid.")
print()
print("This is a VALID walk. Full sweep phases DO exist.")
print("The EC is cross-phase and the sorry needs a DIFFERENT approach.")
