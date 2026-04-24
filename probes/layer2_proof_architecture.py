#!/usr/bin/env python3
"""
COMPLETE PROOF ARCHITECTURE for allNormalForm_false2.

=================================================================
Sorry 1 (line 1012): Adjacent-chain when RR fires then RRR fires
Sorry 2 (line 1077): Adjacent-chain when LL fires then LLL fires
Sorry 3 (line 1121): Adjacent-chain when RR fires then RRR fires (symmetric)
=================================================================

These three are the SAME pattern. In a phase with J >= 1 and K >= 1:
  The first bL fire is at fL, the first bR fire is at fR.
  WLOG assume fL < fR (fL fires first).

  Between steps a and fL: no bL fires (fL is first). No t fires (phase).
  If no LL fires: EC at bL via mk_ec_left. (Already handled.)
  If LL fires: find last LL fire before fL, say wmax.
    If gap after wmax (wmax+1 < fL): EC at bL. (Already handled.)
    If no gap (wmax+1 = fL): LL fires adjacent to fL.
      Now check between a and wmax+1: if no LLL fires: EC at LL.
      If LLL fires: CHAIN CONTINUES. This is the sorry.

  Similarly for the fR < fL case with RR.

THE PROOF FOR THE CHAIN:
  The chain of adjacent fires looks like:
    step a: fires t
    step a+1: fires bL  (tight binary fire)
    step a+2: fires LL  (tight chain)
    step a+3: fires LLL (tight chain)
    ...
    step a+d: fires left^d(t)

  After step a+d, the chain ends because left^(d+1)(t) does NOT fire in [a, a+d).
  EC at left^d(t): the boundary triple at left^d(t) is the same at steps a+d-1 and a+d.
  Wait, no: step a+d fires left^d(t), and step a+d-1 fires left^(d-1)(t).
  Between a+d-1 and a+d: only one step (a+d itself). Not useful directly.

  Actually: the chain termination gives EC at the LAST chain proc.
  If left^(d+1)(t) doesn't fire in [a, a+d): the boundary triple at left^d(t)
  is constant from step a to step a+d-1 (since left^(d-1)(t) = right(left^d(t))
  fires at a+d-1, changing the R coordinate of left^d(t)).

  Hmm, this is getting complicated. Let me think about it differently.

  The chain looks like: a -> t, a+1 -> bL, a+2 -> LL, ..., a+d -> left^d(t).
  At step a: none of {left^d(t), left^(d-1)(t), left^(d+1)(t)} have fired since
  the start of this chain. So the boundary triple at left^d(t) at step a is
  some fixed value.

  At step a+d: left^d(t) fires. Between a and a+d:
    left^(d+1)(t) doesn't fire (chain terminated).
    left^d(t) doesn't fire (this is its first fire).
    left^(d-1)(t) fires at step a+(d-1).

  So the R coordinate of left^d(t) (= left^(d-1)(t) value) changes at step a+(d-1).
  The L coordinate (= left^(d+1)(t) value) doesn't change.
  The S coordinate (= left^d(t) value) doesn't change (hasn't fired yet).

  Triple at step a: (L0, S0, R0)
  Triple at step a+d-1: (L0, S0, R0') where R0' = R0 + (0 or 1) depending on
    what left^(d-1)(t) did. Actually left^(d-1)(t) fires at step a+d-1,
    incrementing its value. But we're looking at the triple at left^d(t),
    which has R = config[left^(d-1)(t)].

  At step a: config[left^(d-1)(t)] = some value R0.
  Step a+d-1 fires left^(d-1)(t), so config[left^(d-1)(t)] at step a+d = R0 + 1.
  Steps a through a+d-2: left^(d-1)(t) hasn't fired yet (first fire at a+d-1).
  So config[left^(d-1)(t)] is R0 for all steps a through a+d-1.

  Actually step a+d-1 is the firing of left^(d-1)(t). The config BEFORE this
  step has left^(d-1)(t) = R0. The config AFTER has left^(d-1)(t) = R0+1.

  So at step a+d: the config has left^(d-1)(t) = R0+1 (just fired at a+d-1).
  At step a: the config has left^(d-1)(t) = R0.

  The boundary triple at left^d(t):
    Step a: (L0, S0, R0). Nonmover (left^d(t) doesn't fire at step a).
    Step a+d: (L0, S0, R0+1). Mover (left^d(t) fires at step a+d).

  These DON'T match (R0 vs R0+1). So EC does NOT occur here.

  But wait: what about step a+d-1 (which fires left^(d-1)(t))?
  At step a+d-1: config at left^d(t) = S0 (hasn't changed).
    L = config[left^(d+1)(t)] = L0 (hasn't changed).
    R = config[left^(d-1)(t)] = R0 (hasn't changed YET -- the fire happens at step a+d-1).
    Wait: does the fire happen at the start or end of the step?

  In the good-cycle model: at step i, the mover fires. The config at step i
  is the config BEFORE the fire. The config at step i+1 is AFTER the fire.

  So: config at step a+d-1 has left^(d-1)(t) = R0 (before firing).
      config at step a+d has left^(d-1)(t) = R0+1 (after firing at step a+d-1).

  Triple at left^d(t):
    Step a: (L0, S0, R0). left^d(t) not mover.
    Step a+d-1: (L0, S0, R0). left^d(t) not mover (left^(d-1)(t) is mover).
    Step a+d: (L0, S0, R0+1). left^d(t) IS mover.

  Steps a and a+d-1 have the SAME triple (L0, S0, R0), and BOTH are nonmover.
  Step a+d has a DIFFERENT triple (L0, S0, R0+1) and IS mover.
  => NO EC at left^d(t) from this comparison.

  So the TIGHT CHAIN doesn't give EC at the chain-end proc! The proof strategy
  in AllNormalFormFalse2 is wrong for the chain case.

  BUT: the data shows EC always exists somewhere. The chain itself is impossible
  for long enough chains (it would require too many adjacent fires).

  Let me check: how long can the chain actually be?
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


# For each all-normalForm cycle, check the mixed (J>=1, K>=1) phases
# and the chain structure
n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24
sandwiched = [p for p in range(n) if ms[p] >= 3
              and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]

words = enumerate_mover_words(ms, n, max_len)

mixed_phase_count = 0
chain_lengths = Counter()

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

        all_nf = True
        for idx in range(len(t_fires)):
            s = t_fires[idx]
            a = t_fires[(idx - 1) % len(t_fires)]
            if s > a:
                interior = list(range(a + 1, s))
            else:
                interior = list(range(a + 1, ell)) + list(range(0, s))
            J = sum(1 for st in interior if word[st] == bL)
            K = sum(1 for st in interior if word[st] == bR)
            if not is_normal_form(J, K):
                all_nf = False
                break

        if not all_nf:
            continue

        # Check mixed phases (J >= 1, K >= 1)
        for idx in range(len(t_fires)):
            s = t_fires[idx]
            a = t_fires[(idx - 1) % len(t_fires)]
            if s > a:
                interior = list(range(a + 1, s))
            else:
                interior = list(range(a + 1, ell)) + list(range(0, s))
            J = sum(1 for st in interior if word[st] == bL)
            K = sum(1 for st in interior if word[st] == bR)

            if J >= 1 and K >= 1:
                mixed_phase_count += 1

                # Check chain: which binary fires first?
                first_binary = None
                for st in interior:
                    if word[st] == bL:
                        first_binary = 'L'
                        break
                    elif word[st] == bR:
                        first_binary = 'R'
                        break

                # Trace chain from the SECOND binary side
                if first_binary == 'L':
                    # fL fires first. Check chain from R side.
                    # Find fR (first R fire)
                    fL_idx = next(i for i, st in enumerate(interior) if word[st] == bL)
                    fR_idx = next(i for i, st in enumerate(interior) if word[st] == bR)

                    # Check chain between a and min(fL, fR)
                    first_fire = min(fL_idx, fR_idx)
                    # What fires between step a and the first binary fire?
                    chain = []
                    for i in range(first_fire):
                        chain.append(word[interior[i]])
                    chain_lengths[len(chain)] += 1
                else:
                    chain_lengths[0] += 1

print(f"\nn={n}, ms={ms}")
print(f"Mixed phases (J>=1, K>=1): {mixed_phase_count}")
print(f"Chain lengths before first binary fire: {dict(sorted(chain_lengths.items()))}")

# Actually, let me check something different:
# In the mixed-phase case, how does EC arise?
# The Lean code checks: fL and fR are the FIRST fires of bL and bR in [a, s).
# WLOG fL < fR. Then between a and fL: no bL. If no LL: EC.
# This is the caseC_LR approach.

# Let me check: in the mixed phases, does caseC always have a gap?
print("\n--- Mixed phase gap analysis ---")
gap_types = Counter()
ec_found_counter = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)

    for t in sandwiched:
        bL = (t - 1) % n
        bR = (t + 1) % n
        LL = (t - 2) % n
        RR = (t + 2) % n

        t_fires = sorted(i for i in range(ell) if word[i] == t)
        if not t_fires:
            continue

        all_nf = True
        for idx in range(len(t_fires)):
            s = t_fires[idx]
            a = t_fires[(idx - 1) % len(t_fires)]
            if s > a:
                inter = list(range(a + 1, s))
            else:
                inter = list(range(a + 1, ell)) + list(range(0, s))
            J = sum(1 for st in inter if word[st] == bL)
            K = sum(1 for st in inter if word[st] == bR)
            if not is_normal_form(J, K):
                all_nf = False
                break

        if not all_nf:
            continue

        for idx in range(len(t_fires)):
            s = t_fires[idx]
            a = t_fires[(idx - 1) % len(t_fires)]
            if s > a:
                inter = list(range(a + 1, s))
            else:
                inter = list(range(a + 1, ell)) + list(range(0, s))
            J = sum(1 for st in inter if word[st] == bL)
            K = sum(1 for st in inter if word[st] == bR)

            if J < 1 or K < 1:
                continue

            # Find first bL fire and first bR fire
            fL_step = next(st for st in inter if word[st] == bL)
            fR_step = next(st for st in inter if word[st] == bR)
            fL_pos = inter.index(fL_step)
            fR_pos = inter.index(fR_step)

            # Determine order
            if fL_pos < fR_pos:
                first, second = 'L', 'R'
                first_step, second_step = fL_step, fR_step
                first_pos, second_pos = fL_pos, fR_pos
                second_neighbor = LL  # Check LL between a and fL
            else:
                first, second = 'R', 'L'
                first_step, second_step = fR_step, fL_step
                first_pos, second_pos = fR_pos, fL_pos
                second_neighbor = RR

            # What fires between step a (start) and the first binary fire?
            pre_steps = inter[:first_pos]
            # Does the second-neighbor fire in this interval?
            sn_fires = [st for st in pre_steps if word[st] == second_neighbor]

            if not sn_fires:
                gap_types['no_sn'] += 1
            elif all(word[st] == second_neighbor for st in pre_steps):
                gap_types['all_sn'] += 1
            else:
                gap_types['mixed_sn'] += 1

            # What are the procs firing in pre_steps?
            pre_movers = [word[st] for st in pre_steps]
            if pre_movers:
                gap_types[f'pre_movers={sorted(set(pre_movers))}'] += 1

print(f"\nGap types in mixed phases:")
for gt, cnt in sorted(gap_types.items(), key=lambda x: -x[1]):
    print(f"  {gt}: {cnt}")
