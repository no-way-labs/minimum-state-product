#!/usr/bin/env python3
"""
Is every gap state decisive? (Both neighbors preserved OR one side 0 + other ≥ 2)

For each proc p with fc >= 2, each gap between consecutive firings:
  J = left neighbor fires, K = right neighbor fires
  left_mod, right_mod ∈ {2, 3}
  decisive = (J % left_mod == 0 AND K % right_mod == 0) OR (J == 0 AND K >= 2) OR (K == 0 AND J >= 2)

If EVERY gap of EVERY proc is decisive → proof is trivial.
If not → need the descent argument.
"""
from itertools import product as iproduct
from collections import Counter

def check_all_decisive(n, ms, max_len):
    start = tuple(0 for _ in range(n))
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}
    results = []
    def dfs(word, fc, config):
        if len(word) > max_len: return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                if len(results) >= 500: return
            return
        if len(results) >= 500: return
        remaining = max_len - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        last = word[-1]
        for nxt in ring_adj[last]:
            if len(results) >= 500: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()
    for p in range(n):
        if len(results) >= 500: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

    def winding(word):
        w = 0
        for i in range(len(word)):
            d = (word[(i+1)%len(word)] - word[i]) % n
            if d == 1: w += 1
            elif d == n-1: w -= 1
        return w

    zw = [w for w in results if winding(w) == 0]

    # For each cycle: is EVERY gap of EVERY proc decisive?
    all_cycles_all_decisive = 0
    some_gap_not_decisive = 0
    # For each cycle: is SOME proc's SOME gap decisive?
    all_cycles_some_decisive = 0
    no_decisive_at_all = 0

    non_decisive_sigs = set()

    for word in zw:
        ell = len(word)
        fc = Counter(word)
        cycle_all_decisive = True
        cycle_some_decisive = False

        for p in range(n):
            if fc[p] < 2: continue
            fire_steps = sorted(s for s in range(ell) if word[s] == p)
            left_p = (p-1)%n; right_p = (p+1)%n
            left_mod = ms[left_p]; right_mod = ms[right_p]

            for idx in range(len(fire_steps)):
                a = fire_steps[idx]
                s = fire_steps[(idx+1) % len(fire_steps)]
                if s <= a: s += ell
                J = sum(1 for step in range(a+1, s) if word[step%ell] == left_p)
                K = sum(1 for step in range(a+1, s) if word[step%ell] == right_p)

                both_preserved = (J % left_mod == 0) and (K % right_mod == 0)
                toggle_left = (J == 0 and K >= 2)
                toggle_right = (K == 0 and J >= 2)
                decisive = both_preserved or toggle_left or toggle_right

                if decisive:
                    cycle_some_decisive = True
                else:
                    cycle_all_decisive = False
                    # Record the non-decisive signature
                    j_cat = min(J, 3)  # 0,1,2,3+
                    k_cat = min(K, 3)
                    non_decisive_sigs.add((ms[p], left_mod, right_mod, j_cat, J%left_mod, k_cat, K%right_mod))

        if cycle_all_decisive:
            all_cycles_all_decisive += 1
        else:
            some_gap_not_decisive += 1
        if cycle_some_decisive:
            all_cycles_some_decisive += 1
        else:
            no_decisive_at_all += 1

    print(f"  ZW cycles: {len(zw)}")
    print(f"  ALL gaps decisive: {all_cycles_all_decisive} ({100*all_cycles_all_decisive/max(1,len(zw)):.0f}%)")
    print(f"  SOME gap not decisive: {some_gap_not_decisive}")
    print(f"  SOME gap decisive (per cycle): {all_cycles_some_decisive} ({100*all_cycles_some_decisive/max(1,len(zw)):.0f}%)")
    print(f"  NO decisive gap at all: {no_decisive_at_all}")

    if non_decisive_sigs:
        print(f"  Non-decisive signatures (proc_mod, L_mod, R_mod, J_cat, J%Lmod, K_cat, K%Rmod):")
        for sig in sorted(non_decisive_sigs):
            print(f"    {sig}")

for n, ms, ml, label in [
    (5, [2,3,2,3,2], 16, "n=5 alt"),
    (7, [2,3,2,3,2,3,2], 20, "n=7 alt"),
    (9, [2,3,3,2,3,3,2,3,3], 26, "n=9 non-alt"),
    (9, [2,3,3,3,2,3,3,3,2], 26, "n=9 gaps-3"),
]:
    print(f"\n{label}: n={n}, ms={ms}")
    check_all_decisive(n, ms, ml)
