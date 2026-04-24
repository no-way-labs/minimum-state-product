#!/usr/bin/env python3
"""
DEEP ANALYSIS: What exactly happens in all-normalForm cycles at sandwiched ternary?

Key question: what (J,K) patterns appear? What gives EC?

NormalForm = not dispatched by:
  BothEven: Even J and Even K
  Toggle-FR-L: J >= 2 and K = 0
  Toggle-FR-R: J = 0 and K >= 2

So normalForm allows: (1,0), (0,1), (1,1), (2,1), (1,2), (3,1), (1,3), (2,3), (3,2), etc.
The constraint is: at least one of J,K is odd, and zero-sided needs J or K = 1.

For the TRAVERSAL RETURN mechanism (BinSCC Expl 10):
  In a (2,1) phase: bL fires 2 times, bR fires 1 time.
  The "singleton" is bR (fires 1 time).
  If the singleton fires FIRST in the phase: EC via Traversal Return.
  "Fires first" = among all neighbor firings in the phase, the singleton fires before
  the pair side.

  Similarly (1,2) phase: singleton is bL. If bL fires first: EC.

For (1,1) phases: both sides fire once. This is a "balanced" phase.
  The single bL fire and single bR fire. Are they tight? If both are tight
  (at step a+1 and a+2, or interspersed with t): need further analysis.

For (1,0) or (0,1) phases: one-sided with single fire. By the tight argument:
  the single fire is at a+1. Phase has length >= 2.
  If length > 2: same triple at a+2 and s => EC.
  If length = 2: no intermediate step, no automatic EC from this phase alone.

The RING ALTERNATION argument (BinSCC Expl 10):
  Across ALL phases of ALL sandwiched ternary procs, the (2,1)/(1,2) phases
  have a "singleton side." The singleton side ALTERNATES at consecutive ternary.
  The walk direction determines which ternary has singleton=first => EC.

Let me check what patterns actually occur and how EC arises.
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


def check_ec_at(word, cycle, ms, n, t):
    """Check actual EC at t."""
    ell = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n
    for sv in range(ms[t]):
        mover = set()
        nonmover = set()
        for i in range(ell):
            if cycle[i][t] == sv:
                lr = (cycle[i][bL], cycle[i][bR])
                if word[i] == t:
                    mover.add(lr)
                else:
                    nonmover.add(lr)
        if mover & nonmover:
            return True
    return False


# Use the alternating ring case where all sandwiched ternary always have EC
n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24
sandwiched = [p for p in range(n) if ms[p] >= 3
              and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]

print(f"n={n}, ms={ms}, sandwiched={sandwiched}")
words = enumerate_mover_words(ms, n, max_len)

# For each all-normalForm cycle at sandwiched t, determine the EC mechanism
ec_mechanisms = Counter()
phase_pattern_combos = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    for t in sandwiched:
        ell = len(word)
        bL = (t - 1) % n
        bR = (t + 1) % n

        t_fires = [i for i in range(ell) if word[i] == t]
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

        pattern = tuple(sorted(phases))
        phase_pattern_combos[pattern] += 1

        # Check if EC exists at t
        has_ec = check_ec_at(word, cycle, ms, n, t)

        # Determine mechanism:
        # A) Some phase has length > 2 AND no second-neighbor fires
        #    AND binary fire is tight => triple match
        # B) (2,1)/(1,2) phase with singleton=first => Traversal Return
        # C) Something else

        mechanism = "unknown"
        if has_ec:
            # Check for a long phase with no LL/RR fires
            for idx in range(len(t_fires)):
                s = t_fires[idx]
                a = t_fires[(idx - 1) % len(t_fires)]
                if s > a:
                    interior = list(range(a + 1, s))
                else:
                    interior = list(range(a + 1, ell)) + list(range(0, s))

                LL = (t - 2) % n
                RR = (t + 2) % n
                J = sum(1 for st in interior if word[st] == bL)
                K = sum(1 for st in interior if word[st] == bR)
                ll_fires = sum(1 for st in interior if word[st] == LL)
                rr_fires = sum(1 for st in interior if word[st] == RR)

                if (J, K) in [(1, 0), (0, 1)]:
                    if ll_fires == 0 and rr_fires == 0 and len(interior) > 1:
                        mechanism = "one-sided-long-clean"
                        break
                elif (J, K) in [(2, 1), (1, 2)]:
                    # Check singleton=first
                    singleton = bR if J == 2 else bL
                    for st in interior:
                        if word[st] in (bL, bR):
                            if word[st] == singleton:
                                mechanism = "traversal-return"
                            else:
                                mechanism = "pair-first-(2,1)/(1,2)"
                            break
                    if mechanism != "unknown":
                        break
                elif (J, K) == (1, 1):
                    if len(interior) > 2:
                        mechanism = "balanced-long"
                        break

            if mechanism == "unknown":
                mechanism = "other-ec"

        ec_mechanisms[(tuple(sorted(phases)), mechanism)] += 1

print(f"\nPhase pattern combos (sorted):")
for pat, cnt in sorted(phase_pattern_combos.items(), key=lambda x: -x[1])[:20]:
    print(f"  {pat}: {cnt}")

print(f"\nEC mechanism by phase pattern:")
for (pat, mech), cnt in sorted(ec_mechanisms.items(), key=lambda x: -x[1])[:30]:
    print(f"  phases={pat}, mech={mech}: {cnt}")
