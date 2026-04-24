#!/usr/bin/env python3
"""
Verify: in mixed normalForm phases with fL < fR (bL fires first),
does RR = right(right(t)) fire in [fL, fR)?

ec_caseC_LR requires no t, bR, RR in [fL, fR). We know no t (phase) and
no bR (fR is first). Does RR fire?

Similarly, for fR < fL: does LL fire in [fR, fL)?
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


for n, ms, label, max_len in [
    (7, [2, 3, 2, 3, 2, 3, 3], "n=7", 24),
    (8, [2, 3, 2, 3, 2, 3, 2, 3], "n=8", 24),
]:
    sandwiched = [p for p in range(n) if ms[p] >= 3
                  and ms[(p-1) % n] == 2 and ms[(p+1) % n] == 2]
    if not sandwiched:
        continue

    words = enumerate_mover_words(ms, n, max_len)

    total_mixed = 0
    caseC_LR_clean = 0  # fL < fR, no RR in [fL, fR)
    caseC_LR_dirty = 0  # fL < fR, RR in [fL, fR)
    caseC_RL_clean = 0  # fR < fL, no LL in [fR, fL)
    caseC_RL_dirty = 0  # fR < fL, LL in [fR, fL)

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
                total_mixed += 1

                # Find first bL and bR fires (positions in inter)
                fL_pos = next(i for i, st in enumerate(inter) if word[st] == bL)
                fR_pos = next(i for i, st in enumerate(inter) if word[st] == bR)

                if fL_pos < fR_pos:
                    # fL fires first. Check RR in [fL, fR).
                    interval = inter[fL_pos:fR_pos]
                    rr_fires = any(word[st] == RR for st in interval)
                    if rr_fires:
                        caseC_LR_dirty += 1
                    else:
                        caseC_LR_clean += 1
                else:
                    # fR fires first. Check LL in [fR, fL).
                    interval = inter[fR_pos:fL_pos]
                    ll_fires = any(word[st] == LL for st in interval)
                    if ll_fires:
                        caseC_RL_dirty += 1
                    else:
                        caseC_RL_clean += 1

    print(f"{label}: total mixed = {total_mixed}")
    print(f"  caseC_LR clean (no RR): {caseC_LR_clean}")
    print(f"  caseC_LR dirty (RR fires): {caseC_LR_dirty}")
    print(f"  caseC_RL clean (no LL): {caseC_RL_clean}")
    print(f"  caseC_RL dirty (LL fires): {caseC_RL_dirty}")
    total_clean = caseC_LR_clean + caseC_RL_clean
    total_dirty = caseC_LR_dirty + caseC_RL_dirty
    print(f"  Total clean: {total_clean} ({100*total_clean/total_mixed:.1f}%)")
    print(f"  Total dirty: {total_dirty} ({100*total_dirty/total_mixed:.1f}%)")

    # KEY: does fL = a+1 always (first binary fires right after t)?
    first_step_is_binary = 0
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
                # Check: is the first step after a a binary fire?
                next_step = inter[1]  # inter[0] = a (fires t), inter[1] = a+1
                if word[next_step] in (bL, bR):
                    first_step_is_binary += 1

    print(f"  First step after t-fire is binary: {first_step_is_binary}/{total_mixed} ({100*first_step_is_binary/total_mixed:.1f}%)")
    print()
