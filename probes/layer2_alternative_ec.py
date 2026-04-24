#!/usr/bin/env python3
"""
ALTERNATIVE EC PROOF: For mixed normalForm phases (J>=1, K>=1),
find EC at RR or LL using a DIRECT witness without chain analysis.

From the data: EC is at bL, t, LL, RR, or further.
The most common is t (self). Can we always find EC at t or at RR?

IDEA: The walk goes through both bL and bR in the phase.
Between bL's first fire and bR's first fire (or vice versa),
the walk passes through several procs. RR fires in this interval (100% verified).

If we can find a GAP in the RR firings (a step where neither bR, RR, nor RRR fires),
that gives EC at RR.

Let me check: between the last RR fire and fR, is there a gap?
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


def find_ec_at_proc(word, cycle, ms, n, p):
    """Find EC witness at proc p."""
    ell = len(word)
    pL = (p - 1) % n
    pR = (p + 1) % n
    for sv in range(ms[p]):
        mover_steps = []
        nonmover_steps = []
        for i in range(ell):
            if cycle[i][p] == sv:
                if word[i] == p:
                    mover_steps.append(i)
                else:
                    nonmover_steps.append(i)
        for ms_ in mover_steps:
            mt = (cycle[ms_][pL], cycle[ms_][p], cycle[ms_][pR])
            for nms in nonmover_steps:
                nt = (cycle[nms][pL], cycle[nms][p], cycle[nms][pR])
                if mt == nt:
                    return ms_, nms, mt
    return None


# The key approach: for mixed normalForm phases, identify a SIMPLE
# EC witness that doesn't need chain analysis.

n, ms = 7, [2, 3, 2, 3, 2, 3, 3]
max_len = 24
sandwiched = [p for p in range(n) if ms[p] >= 3
              and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]

words = enumerate_mover_words(ms, n, max_len)

# Check: for every mixed normalForm phase, can we find EC using
# ONLY the mk_ec_left/right approach with v = step_after_last_LL/RR?
ec_via_gap_at_second_neighbor = 0
ec_not_via_gap = 0

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

        for idx in range(len(t_fires)):
            s = t_fires[idx]
            a = t_fires[(idx - 1) % len(t_fires)]
            if s > a:
                inter = list(range(a, s))
            else:
                inter = list(range(a, ell)) + list(range(0, s))
            J = sum(1 for st in inter if word[st] == bL)
            K = sum(1 for st in inter if word[st] == bR)
            if not is_normal_form(J, K) or J < 1 or K < 1:
                continue

            # Try to find EC at bR using mk_ec_right:
            # Need v < fR with no RR in [v, fR).
            fR = next(st for st in inter if word[st] == bR)
            fR_pos = inter.index(fR)

            # Find last RR fire before fR
            rr_fires_before_fR = [st for st in inter[:fR_pos] if word[st] == RR]
            if not rr_fires_before_fR:
                # No RR before fR. v = a. No RR in [a, fR).
                # mk_ec_right(a, fR): needs no t, bR, RR in [a, fR).
                # No t: ht_nofire (a <= k < s). fR < s. CHECK.
                # No bR: fR is first bR. CHECK.
                # No RR: just verified. CHECK.
                # But also need moverAt(a) != bR.
                # moverAt(a) could be bR if fR = a. But fR is in [a, s) and
                # we need a < fR (otherwise fR = a means first bR fire is at a).
                if fR_pos > 0:
                    ec_via_gap_at_second_neighbor += 1
                else:
                    # fR = a. Then first bR fire is at phase start.
                    # Use mk_ec_left instead.
                    fL = next(st for st in inter if word[st] == bL)
                    fL_pos = inter.index(fL)
                    ll_fires_before_fL = [st for st in inter[:fL_pos] if word[st] == LL]
                    if not ll_fires_before_fL and fL_pos > 0:
                        ec_via_gap_at_second_neighbor += 1
                    else:
                        ec_not_via_gap += 1
            else:
                last_rr = rr_fires_before_fR[-1]
                last_rr_pos = inter.index(last_rr)
                # Gap after last RR? Need last_rr_pos + 1 < fR_pos.
                if last_rr_pos + 1 < fR_pos:
                    # v = inter[last_rr_pos + 1]. No RR in [v, fR).
                    ec_via_gap_at_second_neighbor += 1
                else:
                    # Tight: last RR is at fR - 1. Need chain.
                    # Try the OTHER side: mk_ec_left with bL.
                    fL = next(st for st in inter if word[st] == bL)
                    fL_pos = inter.index(fL)
                    ll_fires_before_fL = [st for st in inter[:fL_pos] if word[st] == LL]
                    if not ll_fires_before_fL:
                        if fL_pos > 0:
                            ec_via_gap_at_second_neighbor += 1
                        else:
                            ec_not_via_gap += 1
                    else:
                        last_ll = ll_fires_before_fL[-1]
                        last_ll_pos = inter.index(last_ll)
                        if last_ll_pos + 1 < fL_pos:
                            ec_via_gap_at_second_neighbor += 1
                        else:
                            # Both sides tight. This is the sorry case.
                            ec_not_via_gap += 1

total = ec_via_gap_at_second_neighbor + ec_not_via_gap
print(f"n={n}, ms={ms}")
print(f"Total mixed phases: {total}")
print(f"EC via gap at 2nd neighbor: {ec_via_gap_at_second_neighbor}")
print(f"Both sides tight (sorry case): {ec_not_via_gap}")
print(f"Coverage: {100*ec_via_gap_at_second_neighbor/total:.1f}%")
