#!/usr/bin/env python3
"""
LAYER 2 PROOF: Chain-propagation EC for all-normalForm sandwiched ternary.

=== THEOREM ===
Let sys be a system with n >= 7, >= 3 non-consecutive binary processors,
sub-threshold product. Let gc be a good cycle where all processors fire
(hfull). Let t be a sandwiched ternary proc (m(left t) = 2, m(right t) = 2,
m(t) >= 3). If every phase at t is normalForm, then hasEntryConflict gc.

=== PROOF ===

Step 1: Every phase has a "dirty" second-neighbor.
  Since all phases are normalForm and hfull ensures L > 2*fc(t), at least one
  phase has length > 2. In this long phase, the interior contains fires from
  procs other than t, bL, bR. Since the walk is on a ring, these interior fires
  include LL = left(left(t)) or RR = right(right(t)) (or procs further out).

  Actually: by the tight-phase argument (within_phase_ec_left/right), if a phase
  has no second-neighbor fires (LL or RR) and the binary fire is NOT tight
  (not at step a+1), then EC at bL or bR. So if no EC: either the binary fire
  IS tight, or LL/RR fires in the phase.

  If the binary fire is tight AND no LL/RR fires: the phase has only the one
  binary fire and the t-fire. Phase length = 2. But we showed some phase has
  length > 2. So this phase MUST have either non-tight binary fire (=> EC)
  or LL/RR fires.

  Conclusion: if no EC at bL or bR, some phase has LL or RR firing.

Step 2: Chain propagation.
  In a phase where LL fires (and the binary bL fire is tight at step a+1):
  Consider the FIRST LL fire at step fLL in the phase. Between steps a and fLL:
  - step a is the previous t-fire
  - step a+1 fires bL (tight)
  - steps a+2..fLL-1: no bL, no LL (first LL is fLL)
  - step fLL fires LL

  The boundary triple at LL = (left³t, LL, bL):
  - left³t = left(left(left(t))): call it LLL
  - LL's self value
  - bL = right(LL)

  Between step a+1 and fLL: no bL fires (first bL was at a+1, and no second bL
  in this phase since J <= 2 for normalForm). No LL fires (first LL is fLL).
  Does LLL fire? If no LLL fires: the boundary triple at LL is constant from
  a+1 to fLL. Step fLL is LL-mover, step a+1 is LL-nonmover (it fires bL, not LL).
  Same triple => EC at LL.

  If LLL fires: the chain continues to LLL's first fire, and so on.

Step 3: Chain termination.
  The chain propagates outward from t: t -> bL -> LL -> LLL -> ...
  At each step, either EC is found (if the next proc in the chain doesn't fire
  before the current proc's first fire), or the chain extends.

  The chain can extend at most until it reaches a proc at distance floor(n/2)
  from t (halfway around the ring). At that point, the chain from the RIGHT
  side of t has also extended, and the two chains meet.

  With n >= 7 and >= 3 non-consecutive binary: the chain extends through
  ternary procs (which have m >= 3, so they fire >= 3 times). The chain
  terminates when it reaches a proc p where left(p) doesn't fire in the
  relevant interval.

  KEY: The chain MUST terminate because the cycle has finitely many steps.
  At each chain extension, the interval [a, first_fire) shrinks or stays fixed.
  Eventually, either:
  (a) No further proc fires in the interval => EC at the current chain-end proc.
  (b) The chain wraps around the ring and meets the other chain => two-sided
      convergence gives EC.

  Actually, the simplest termination argument:
  The chain extends to procs p1, p2, ..., pk where pi = left^(i+1)(t).
  At each pi, the first fire fpi satisfies a < fpi < s (within the phase).
  The first fires are ordered: a < fp1 <= fp2 <= ... <= fpk < s.
  But the pi are DISTINCT procs, and each fpi is a step where moverAt(fpi) = pi.
  Since the cycle is a good cycle, all configs are distinct.
  The number of chain steps is bounded by the phase length - 2.

  When the chain reaches a proc pk = left^(k+1)(t) where left^(k+2)(t)
  does NOT fire in the interval [a, fpk): EC at pk.

  With n >= 7: the "other side" chain (from RR) proceeds similarly.
  Since the ring has n procs and the chain extends in one direction,
  after at most ceil(n/2) steps, it reaches the "far side" of the ring.
  At that point, the procs on the far side are NOT adjacent to any binary
  (since binary procs are non-consecutive with >= 3 of them on a ring of >= 7).

  Actually, the deepest the chain can go is until it reaches another binary proc.
  With non-consecutive binary: the distance between adjacent binaries is >= 2
  (each arc has >= 1 ternary). The chain from t goes through the ternary arc
  on one side, reaching the next binary proc. At that binary proc, the chain
  terminates because the binary proc fires exactly 2 times (m=2), and the
  interval contains at most 1 binary fire.

  SPECIFICALLY: if the chain reaches bL's other neighbor (left(bL) = LL, which
  is ternary), and then left(LL) is either ternary or binary.
  If left(LL) is binary (b2): the chain needs b2 to fire in the interval.
  b2 fires 2 times total. If one of those fires is in the interval: the chain
  could extend through b2 to left(b2). But left(b2) is ternary (non-consecutive).

  The chain terminates at SOME proc where the next-outward proc doesn't fire
  in the interval. With finite cycle length, this must happen.

Step 4: The definitive argument (bounded chain depth).
  Consider a phase (a, s) at sandwiched ternary t.
  Phase length P = s - a (mod L). P > 2 (from Step 1).
  The interior steps are a+1, ..., s-1. These fire P-1 procs total (not counting t).

  The chain from the LEFT side: needs step a+1 to fire bL (tight), then fLL, etc.
  Each chain step "uses" one interior step. The chain can extend at most P-2 steps.

  With P >= 3: the chain extends >= 1 step. At the first extension (LL):
  if LLL doesn't fire in [a+1, fLL): EC at LL.

  The question: can LLL ALWAYS fire in [a+1, fLL)? This requires fLL > a+2
  (gap between bL fire and LL fire, with LLL in between).

  Pattern: a fires t, a+1 fires bL, a+2 fires LLL, a+3 fires LL.
  Then the chain extends: LLLL must fire in [a+2, a+3) = empty.
  So LLLL can't fire, and EC at LLL.

  BUT: maybe a+2 fires some OTHER proc, not LLL.
  The chain argument only works when the specific next-outward proc fires.

  REVISED: the AllNormalFormFalse2 Lean code does exactly this case split.
  It checks: does LL fire in the phase? If yes: is the first LL fire at a+2
  (tight to the bL fire)? If not tight: EC. If tight: check LLL, etc.

  The chain of tight fires: a fires t, a+1 fires bL, a+2 fires LL, a+3 fires LLL, ...
  This is a sweep to the LEFT starting from t! Each step fires the next proc to the left.

  If this sweep reaches distance d from t: the phase has consumed d+1 steps from a.
  The remaining steps s-a-d-1 are the "tail" of the phase.

  In the tail: no more left-chain procs fire (the chain terminated).
  The t-fire at step s has a boundary triple that might match some tail step.

  ACTUALLY: I realize the chain termination gives EC at the chain-end proc,
  NOT at t. The AllNormalFormFalse2 proof derives `False` (which is equivalent
  to hasEntryConflict gc, since the proof is by contradiction assuming no EC).

  The chain EC works at intermediate procs. This is fine for the theorem,
  which only needs hasEntryConflict gc (at any proc).

=== COMPUTATIONAL VERIFICATION ===

For each all-normalForm cycle at a sandwiched t, verify that the chain argument
produces EC at some proc within the chain.
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


def chain_ec_check(word, cycle, ms, n, t, phase_idx, direction):
    """Check if the chain-propagation argument gives EC.
    direction: 'left' or 'right'.

    Returns (ec_found, ec_proc, chain_depth) or (False, None, depth).
    """
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n

    t_fires = sorted(i for i in range(ell) if word[i] == t)
    if not t_fires or phase_idx >= len(t_fires):
        return False, None, 0

    s = t_fires[phase_idx]
    a = t_fires[(phase_idx - 1) % len(t_fires)]

    if s > a:
        interior = list(range(a + 1, s))
    else:
        interior = list(range(a + 1, ell)) + list(range(0, s))

    if not interior:
        return False, None, 0

    # Check if first interior step fires the correct binary neighbor
    if direction == 'left':
        first_binary = bL
        step_fn = lambda p: (p - 1) % n  # go further left
    else:
        first_binary = bR
        step_fn = lambda p: (p + 1) % n  # go further right

    # Is the first step a binary fire? (tight)
    if word[interior[0]] != first_binary:
        return False, None, 0  # not tight, EC handled elsewhere

    # Chain: current_proc = first_binary, scan forward for next proc in chain
    current_proc = first_binary
    current_start = 0  # index into interior

    for depth in range(1, n):
        next_proc = step_fn(current_proc)

        # Find first fire of next_proc in interior[current_start+1:]
        found_next = False
        next_idx = None
        for idx in range(current_start + 1, len(interior)):
            if word[interior[idx]] == next_proc:
                found_next = True
                next_idx = idx
                break

        if not found_next:
            # next_proc doesn't fire in the remaining interior
            # EC at current_proc: the boundary triple at current_proc is constant
            # from interior[current_start] to the end of the relevant interval.
            # Actually need to check: is there a step between current_start and s
            # where current_proc's boundary triple matches?

            # The mover at interior[current_start] fires current_proc.
            # Any nonmover step after interior[current_start] with the same triple
            # gives EC at current_proc.

            # If there are steps between interior[current_start] and s where
            # neither current_proc, left(current_proc), nor right(current_proc) fires:
            # the boundary triple is constant, and those steps are nonmover for current_proc.

            # Check: is there such a step?
            cp_L = (current_proc - 1) % n
            cp_R = (current_proc + 1) % n

            mover_step = interior[current_start]
            # Find next step after mover_step that is NOT current_proc, cp_L, or cp_R
            for idx in range(current_start + 1, len(interior)):
                step = interior[idx]
                if word[step] not in (current_proc, cp_L, cp_R):
                    # This step has the same boundary triple as mover_step at current_proc
                    # mover_step is current_proc mover, this step is current_proc nonmover
                    # => EC at current_proc
                    return True, current_proc, depth

            # If no such step: check if step s (t-fire) is also a nonmover for current_proc
            if s < ell and word[s] != current_proc and word[s] not in (cp_L, cp_R):
                # hmm, step s fires t. Is t one of cp_L, cp_R?
                if t not in (current_proc, cp_L, cp_R):
                    return True, current_proc, depth

            return False, None, depth

        # Found next_proc at interior[next_idx].
        # Check: is it tight (next_idx == current_start + 1)?
        if next_idx > current_start + 1:
            # GAP between current_proc fire and next_proc fire
            # Interior[current_start+1] has boundary triple same as interior[next_idx]
            # (no fires of left(next_proc), next_proc, right(next_proc) between them)
            # Check this:
            np_L = (next_proc - 1) % n
            np_R = (next_proc + 1) % n
            gap_clean = True
            for idx in range(current_start + 1, next_idx):
                if word[interior[idx]] in (next_proc, np_L, np_R):
                    gap_clean = False
                    break
            if gap_clean:
                # interior[next_idx] is next_proc mover
                # interior[current_start+1] is next_proc nonmover (same triple)
                return True, next_proc, depth

        # Tight: chain extends
        current_proc = next_proc
        current_start = next_idx

    return False, None, n  # chain wrapped around (shouldn't happen)


# Test
n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24
sandwiched = [p for p in range(n) if ms[p] >= 3
              and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]

words = enumerate_mover_words(ms, n, max_len)

total_nf = 0
chain_ec = 0
no_chain_ec = 0
chain_depth_stats = Counter()

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
            phases.append((J, K))

        all_nf = all(is_normal_form(J, K) for J, K in phases)
        if not all_nf:
            continue
        total_nf += 1

        found_chain_ec = False
        for phase_idx in range(len(t_fires)):
            for direction in ['left', 'right']:
                ec, proc, depth = chain_ec_check(word, cycle, ms, n, t, phase_idx, direction)
                if ec:
                    found_chain_ec = True
                    chain_depth_stats[depth] += 1
                    break
            if found_chain_ec:
                break

        if found_chain_ec:
            chain_ec += 1
        else:
            no_chain_ec += 1
            if no_chain_ec <= 3:
                print(f"  No chain EC: word={word}, t={t}, phases={phases}")

print(f"\nn={n}, ms={ms}")
print(f"Total all-NF: {total_nf}")
print(f"Chain EC found: {chain_ec} ({100*chain_ec/max(1,total_nf):.1f}%)")
print(f"No chain EC: {no_chain_ec}")
print(f"Chain depth stats: {dict(sorted(chain_depth_stats.items()))}")
