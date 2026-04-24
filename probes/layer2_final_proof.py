#!/usr/bin/env python3
"""
LAYER 2 FINAL PROOF: allNormalForm_false for sandwiched ternary.

=======================================================================
THEOREM (allNormalForm_false2)
=======================================================================

Let gc be a good cycle on a ring with n >= 9, >= 3 non-consecutive binary,
sub-threshold product. Let t be a sandwiched ternary (m(left t) = m(right t) = 2,
m(t) >= 3). Assume all processors fire (hfull), fc(t) >= 2, fc(t) < |cycle|.
If every phase at t is normalForm, then hasEntryConflict gc.

=======================================================================
PROOF
=======================================================================

We assume for contradiction that no entry conflict exists (hnoEC).

PART A: Fire-count decomposition (sorry line 1129).
---------------------------------------------------------
Claim: fc(bL) + fc(bR) <= fc(t).

Proof:
  The t-firings partition the cycle into fc(t) phases. Each phase (a_i, s_i]
  is the interval between consecutive t-fires. Every step of the cycle belongs
  to exactly one phase.

  At each phase, let J_i = intervalFireCount(bL, a_i, s_i) and
  K_i = intervalFireCount(bR, a_i, s_i). Then:
    sum_i J_i = fc(bL)  and  sum_i K_i = fc(bR).
  (This is the fire-count decomposition: each bL/bR firing is counted in
  exactly one phase.)

  From h_phase_le1 (proved at line 897): each phase has J_i + K_i <= 1.
  (This follows from normalForm + the BothEven/Toggle-FR/mixed EC arguments
  already proved in AllNormalFormFalse2.)

  Therefore:
    fc(bL) + fc(bR) = sum_i (J_i + K_i) <= sum_i 1 = fc(t).  QED

  NOTE: The fire-count decomposition sum_i J_i = fc(bL) is a standard
  property of phase partitioning. It requires showing that the phases
  cover all steps and each step belongs to exactly one phase. This is
  straightforward from the definition of TernaryPhase.

PART B: Deriving EC from the exact-equality regime.
---------------------------------------------------------
From Part A: fc(bL) + fc(bR) <= fc(t).
From sparse_phase_sum_ge (PhaseExtractionBase): fc(bL) + fc(bR) >= fc(t).
  (This uses normalForm + tight-phase + hnoEC.)
Combined: fc(bL) + fc(bR) = fc(t), and each phase has J_i + K_i = 1.

So each phase is one-sided: either (1,0) or (0,1).
  (From normalForm: J=0 => K=1, and K=0 => J=1.)

Binary parity: fc(bL) is even, fc(bR) is even (binary procs fire even times).
  fc(bL) + fc(bR) = fc(t), and fc(t) = m(t) * k for some k >= 1.
  With m(t) = 3: fc(t) = 3k. fc(bL) even, fc(bR) even, sum = 3k.
  Even + even = even, but 3k is even iff k is even. So k must be even, k >= 2.
  fc(t) >= 6.

  Number of (1,0) phases = fc(bL) (each contributes 1 to bL).
  Number of (0,1) phases = fc(bR) (each contributes 1 to bR).
  Total = fc(bL) + fc(bR) = fc(t). Checks out.

  With fc(bL) >= 2 and fc(bR) >= 2: at least 2 phases of each type.

CLAIM: In this regime, EC exists.

Proof of Claim:
  Each phase has exactly 1 binary fire (bL or bR) in its interior.
  The binary fire is tight (at step a+1, from the within_phase_ec argument).
  Phase length = (number of interior steps) + 1 (for the t-fire at step s).

  Total cycle length L = sum of phase lengths.
  Each phase contributes at least 2 steps (the binary fire + the t-fire).
  So L >= 2 * fc(t) = 2 * 3k.
  But L = sum of all fire counts. With hfull (all procs fire):
    L >= fc(t) + fc(bL) + fc(bR) + sum_{other procs} fc(p)
       = fc(t) + fc(t) + sum_{other procs} fc(p)
       = 2 * fc(t) + (sum of fc for n-3 other procs)
  Each other proc fires at least once (hfull), so sum >= n-3.
  L >= 2*fc(t) + (n-3).
  With n >= 9: L >= 2*fc(t) + 6 > 2*fc(t).

  Since L > 2*fc(t) and there are fc(t) phases:
    Average phase length > 2.
    Some phase has length >= 3.

  In a phase of length >= 3 with J+K = 1 (one binary fire):
    Interior has >= 2 steps: the binary fire and at least one other step.
    The binary fire is at step a+1 (tight). Step a+2 exists.

    CASE 1: step a+2 fires some proc p with p not in {bL, bR, t, left(bL), right(bR)}.
      Actually we need p to not be in {left(t'), t', right(t')} for t' = the relevant
      neighbor... This is getting complicated.

    SIMPLER APPROACH: Context collision at t itself.

    At step a+1 (binary fire, say bL): c[bL] toggles. c[t] = v (unchanged).
    At step a+2 (some non-t fire): c[bL] unchanged (bL already fired its 1 time
    in this phase). c[bR] unchanged (bR fires 0 times in a (1,0) phase).
    c[t] = v (unchanged, t fires at step s, not a+2).

    So the boundary triple at t is: (c[bL](a+2), v, c[bR](a+2)).
    At step s: c[bL](s) = c[bL](a+2) (no more bL fires in this phase).
              c[bR](s) = c[bR](a+2) (no bR fires in this phase).
              c[t](s) = v (t hasn't fired since phase start).

    So the boundary triple at t is THE SAME at steps a+2 and s.
    Step s fires t (mover). Step a+2 does NOT fire t (nonmover).
    => EC at t.  QED

WAIT: does this actually work? Let me check computationally whether the
exact-equality regime (J+K=1 per phase) actually gives EC at t via the
phase-length > 2 argument.

The issue from earlier: the coupling analysis showed EC at t only 50%.
But that was with (2,1) and (1,2) phases too, not just (1,0) and (0,1).
In the EXACT-EQUALITY regime (J+K=1), we only have (1,0) and (0,1) phases.

Let me check: do cycles exist where ALL phases have J+K=1?
"""

from collections import Counter


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 2*n and config == start:
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


def is_normal_form(J, K):
    if J % 2 == 0 and K % 2 == 0:
        return False
    if J >= 2 and K == 0:
        return False
    if J == 0 and K >= 2:
        return False
    return True


print("=" * 70)
print("EXACT-EQUALITY REGIME: J+K=1 per phase => EC at t via long phase")
print("=" * 70)

for n, ms, label, max_len in [
    (7, [2, 3, 2, 3, 2, 3, 3], "n=7 ms=[2,3,2,3,2,3,3]", 24),
    (7, [3, 2, 3, 2, 3, 2, 3], "n=7 alternating", 24),
]:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    if not sandwiched:
        print(f"\n{label}: no sandwiched, skip")
        continue

    words = enumerate_mover_words(ms, n, max_len)

    exact_eq_count = 0
    ec_at_t_via_long = 0
    ec_at_t_any = 0
    no_ec_at_t = 0

    for word in words:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)

        for t in sandwiched:
            bL = (t - 1) % n
            bR = (t + 1) % n

            t_fires = sorted(i for i in range(ell) if word[i] == t)
            if not t_fires:
                continue

            phases = []
            for idx in range(len(t_fires)):
                s = t_fires[idx]
                a = t_fires[(idx - 1) % len(t_fires)]
                if s > a:
                    interior = list(range(a + 1, s))
                else:
                    interior = list(range(a + 1, ell)) + list(range(0, s))
                J = sum(1 for st in interior if word[st] == bL)
                K = sum(1 for st in interior if word[st] == bR)
                phases.append({'J': J, 'K': K, 'len': len(interior) + 1,
                               'a': a, 's': s, 'interior': interior})

            # Check exact-equality regime: all J+K = 1
            all_jk1 = all(ph['J'] + ph['K'] == 1 for ph in phases)
            if not all_jk1:
                continue
            exact_eq_count += 1

            # Check EC at t via the long-phase argument
            found_long_ec = False
            for ph in phases:
                if ph['len'] > 2:
                    # Phase has step a+2 which is nonmover for t
                    # and step s which is mover for t.
                    # Check: boundary triple at t matches?
                    a = ph['a']
                    s = ph['s']
                    a2 = ph['interior'][1] if len(ph['interior']) > 1 else None
                    if a2 is not None:
                        triple_a2 = (cycle[a2][bL], cycle[a2][t], cycle[a2][bR])
                        triple_s = (cycle[s][bL], cycle[s][t], cycle[s][bR])
                        if triple_a2 == triple_s and word[a2] != t:
                            found_long_ec = True
                            break

            if found_long_ec:
                ec_at_t_via_long += 1

            # Also check EC at t by brute force
            has_ec_t = False
            for sv in range(ms[t]):
                mover_lr = set()
                nonmover_lr = set()
                for i in range(ell):
                    if cycle[i][t] == sv:
                        lr = (cycle[i][bL], cycle[i][bR])
                        if word[i] == t:
                            mover_lr.add(lr)
                        else:
                            nonmover_lr.add(lr)
                if mover_lr & nonmover_lr:
                    has_ec_t = True
                    break
            if has_ec_t:
                ec_at_t_any += 1
            else:
                no_ec_at_t += 1

    print(f"\n{label}")
    print(f"  Sandwiched: {sandwiched}")
    print(f"  Exact-equality (J+K=1) instances: {exact_eq_count}")
    print(f"  EC at t via long-phase triple match: {ec_at_t_via_long}")
    print(f"  EC at t (brute force): {ec_at_t_any}")
    print(f"  No EC at t: {no_ec_at_t}")
    if exact_eq_count > 0:
        print(f"  Coverage: {100*ec_at_t_via_long/exact_eq_count:.1f}% via long-phase, "
              f"{100*ec_at_t_any/exact_eq_count:.1f}% brute force")
