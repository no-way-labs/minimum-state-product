#!/usr/bin/env python3
"""
COMPLETE VERIFICATION: Does caseC (mk_ec_left/right) always work for mixed phases?

The Lean code structure for mixed (J>=1, K>=1) phases:
  1. Get first bL fire fL and first bR fire fR in [a, s)  (not (a, s))
  2. Case split: fL < fR, fL > fR, or fL = fR (impossible since left t != right t)

  Case fL < fR (line 960):
    Between a and fL: no bL (fL is first). Does LL fire?
    - If no LL in [a, fL): EC at bL via mk_ec_left.  DONE.
    - If LL fires: find last LL fire wmax in [a, fL).
      * If gap after wmax (wmax+1 < fL): EC. DONE.
      * If tight (wmax+1 = fL): chain continues to LLL. THIS IS THE SORRY.

  Case fL > fR (symmetric for right side, similar sorry).

  Case fL = a (line 1013):
    moverAt(a) = bL (the previous t-fire was at a, but fL = a means bL fires at a).
    Wait: a is the step index of the previous t-fire. fL is the FIRST bL fire
    in [a, s). But a itself is a t-fire (moverAt(a) = t), not a bL fire.
    So fL > a always? Let me re-check.

    Actually, in the Lean code, fL is obtained from exists_first_fire which
    finds k with a <= k < s and moverAt(k) = bL. Since moverAt(a) = t != bL
    (because t is ternary, bL is binary, different procs), fL > a.

    Similarly fR > a.

    So fL, fR > a. The Lean code then does:
    by_cases fL < fR or fR < fL (or fL = fR, which is impossible).

    In the fL < fR case:
    Between a and fL: steps a+1, ..., fL-1.
    If fL = a+1: the interval is empty! No LL can fire in empty interval.
    => mk_ec_left trivially applies (no LL fires). EC at bL.

    If fL > a+1: steps a+1, ..., fL-1 exist. Need to check LL fires.

    The sorry arises when LL fires tightly adjacent to fL AND LLL fires in [a, fLL).

CRITICAL QUESTION: In the actual data, does the "tight LL + LLL" case EVER occur
for the mixed phases? If not, the sorrys are vacuously true and we just need
the fire-count decomposition (sorry at 1129).
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


# Test multiple configurations
for n, ms, label, max_len in [
    (7, [2, 3, 2, 3, 2, 3, 3], "n=7 [2,3,2,3,2,3,3]", 24),
    (7, [3, 2, 3, 2, 3, 2, 3], "n=7 alternating", 24),
    (8, [2, 3, 2, 3, 2, 3, 2, 3], "n=8 alternating", 24),
]:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    if not sandwiched:
        print(f"\n{label}: no sandwiched, skip")
        continue

    words = enumerate_mover_words(ms, n, max_len)

    mixed_total = 0
    caseC_direct = 0  # no LL/RR in [a, first_binary_fire)
    caseC_gap = 0     # LL/RR fires but with gap after last
    caseC_tight_no_chain = 0  # tight LL/RR but no LLL/RRR
    caseC_chain = 0   # the sorry case: tight + LLL/RRR fires

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
            LLL = (t - 3) % n
            RRR = (t + 3) % n

            t_fires = sorted(i for i in range(ell) if word[i] == t)
            if not t_fires:
                continue

            all_nf = True
            phases_data = []
            for idx in range(len(t_fires)):
                s = t_fires[idx]
                a = t_fires[(idx - 1) % len(t_fires)]
                if s > a:
                    inter = list(range(a, s))  # [a, s) for first-fire search
                else:
                    inter = list(range(a, ell)) + list(range(0, s))
                J = sum(1 for st in inter if word[st] == bL)
                K = sum(1 for st in inter if word[st] == bR)
                if not is_normal_form(J, K):
                    all_nf = False
                    break
                phases_data.append({'a': a, 's': s, 'J': J, 'K': K, 'inter': inter})

            if not all_nf:
                continue

            for ph in phases_data:
                if ph['J'] < 1 or ph['K'] < 1:
                    continue
                mixed_total += 1

                a = ph['a']
                s = ph['s']
                inter = ph['inter']

                # First bL and bR fires in [a, s)
                fL = next((st for st in inter if word[st] == bL), None)
                fR = next((st for st in inter if word[st] == bR), None)
                assert fL is not None and fR is not None

                # Determine which fires first and the relevant second-neighbor
                if inter.index(fL) < inter.index(fR):
                    first_fire = fL
                    first_fire_pos = inter.index(fL)
                    sn = LL
                    snn = LLL
                else:
                    first_fire = fR
                    first_fire_pos = inter.index(fR)
                    sn = RR
                    snn = RRR

                # Interval between a and first fire: inter[0:first_fire_pos]
                # Note: inter[0] = a, which fires t (not bL/bR/LL/RR)
                pre_interval = inter[1:first_fire_pos]  # steps a+1 to first_fire-1

                # Does second-neighbor fire in pre_interval?
                sn_fires = [st for st in pre_interval if word[st] == sn]

                if not sn_fires:
                    caseC_direct += 1
                else:
                    # Last sn fire
                    last_sn = sn_fires[-1]
                    last_sn_pos = pre_interval.index(last_sn)
                    # Is there a gap after last sn?
                    if last_sn_pos < len(pre_interval) - 1:
                        caseC_gap += 1
                    else:
                        # Tight: last_sn is at first_fire - 1
                        # Does snn fire in [a, last_sn)?
                        pre_sn_interval = inter[1:inter.index(last_sn)]
                        snn_fires = [st for st in pre_sn_interval if word[st] == snn]
                        if not snn_fires:
                            caseC_tight_no_chain += 1
                        else:
                            caseC_chain += 1

    print(f"\n{label}")
    print(f"  Sandwiched: {sandwiched}")
    print(f"  Mixed phases (J>=1, K>=1, normalForm): {mixed_total}")
    print(f"  caseC_direct (no SN): {caseC_direct}")
    print(f"  caseC_gap (SN with gap): {caseC_gap}")
    print(f"  caseC_tight_no_chain: {caseC_tight_no_chain}")
    print(f"  caseC_chain (SORRY case): {caseC_chain}")
    if caseC_chain == 0:
        print(f"  *** SORRY CASE NEVER OCCURS -- caseC always directly applicable ***")
