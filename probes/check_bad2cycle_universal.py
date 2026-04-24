#!/usr/bin/env python3
"""
DERISK: For ALL problem-cell cycles (sweep + noEC + non-uniform),
verify that EVERY completion strategy produces a bad 2-cycle.

Also: characterize the bad 2-cycle. Is it always the same structure?
"""
from itertools import product as iproduct
from collections import Counter
import random

def check_all_completions(n, ms, label, max_len):
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

    def has_ec(word):
        ell = len(word)
        cfgs = [list(start)]
        for i in range(ell):
            c = list(cfgs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
            cfgs.append(c)
        for p in range(n):
            m_ctx, n_ctx = set(), set()
            for s in range(ell):
                ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
                if word[s] == p:
                    if ctx in n_ctx: return True
                    m_ctx.add(ctx)
                else:
                    if ctx in m_ctx: return True
                    n_ctx.add(ctx)
        return False

    # Find problem-cell cycles
    problem = [w for w in results if abs(winding(w)) >= 2*n and not has_ec(w)]
    print(f"\n{label}: {len(problem)} problem-cell cycles")

    if not problem:
        print("  No problem cycles — cell is EMPTY ✅")
        return True

    all_configs_list = list(iproduct(*(range(m) for m in ms)))
    cidx = {c: i for i, c in enumerate(all_configs_list)}

    # For each problem cycle: try 10 random completions
    all_have_bad_cycle = True
    for wi, word in enumerate(problem[:10]):
        ell = len(word)
        configs = [list(start)]
        for i in range(ell):
            c = list(configs[-1]); c[word[i]] = (c[word[i]]+1) % ms[word[i]]
            configs.append(c)
        cycle_set = set(tuple(configs[s]) for s in range(ell))

        fixed = {}
        for p in range(n):
            for s in range(ell):
                ctx = (configs[s][(p-1)%n], configs[s][p], configs[s][(p+1)%n])
                if word[s] == p:
                    fixed[(p, *ctx)] = configs[s+1][p]
                else:
                    fixed[(p, *ctx)] = configs[s][p]

        any_converges = False
        for trial in range(10):
            random.seed(trial * 1000 + wi)
            rules = {}
            for p in range(n):
                rules[p] = {}
                for L in range(ms[(p-1)%n]):
                    for S in range(ms[p]):
                        for R in range(ms[(p+1)%n]):
                            key = (p, L, S, R)
                            if key in fixed:
                                rules[p][(L,S,R)] = fixed[key]
                            else:
                                opts = [v for v in range(ms[p]) if v != S]
                                rules[p][(L,S,R)] = random.choice(opts) if opts else S

            # Check for bad cycle
            non_legit = set()
            for ci, c in enumerate(all_configs_list):
                if tuple(c) not in cycle_set:
                    non_legit.add(ci)

            has_bad = False
            # Quick check: find any 2-cycle
            for ci in list(non_legit)[:200]:
                c = all_configs_list[ci]
                for p in range(n):
                    ctx = (c[(p-1)%n], c[p], c[(p+1)%n])
                    if rules[p][ctx] != c[p]:
                        nc = list(c); nc[p] = rules[p][ctx]
                        nci = cidx[tuple(nc)]
                        if nci in non_legit:
                            # Check if nc can step back to c
                            nc_t = tuple(nc)
                            for p2 in range(n):
                                ctx2 = (nc_t[(p2-1)%n], nc_t[p2], nc_t[(p2+1)%n])
                                if rules[p2][ctx2] != nc_t[p2]:
                                    nc2 = list(nc_t); nc2[p2] = rules[p2][ctx2]
                                    if tuple(nc2) == tuple(c):
                                        has_bad = True; break
                            if has_bad: break
                if has_bad: break

            if not has_bad:
                any_converges = True

        if any_converges:
            all_have_bad_cycle = False
            print(f"  Cycle {wi}: SOME completion lacks 2-cycle! ⚠️")
        else:
            pass  # all 10 trials had bad cycles

    if all_have_bad_cycle:
        print(f"  ALL problem cycles: every completion has bad 2-cycle ✅")
    else:
        print(f"  SOME completions might converge ⚠️")

    return all_have_bad_cycle

random.seed(42)
r1 = check_all_completions(5, [2,2,2,3,3], "n=5 consecutive", 16)
r2 = check_all_completions(7, [2,2,2,3,3,3,3], "n=7 consecutive", 20)
r3 = check_all_completions(9, [2,3,3,2,3,3,2,3,3], "n=9 non-alt", 26)

print(f"\n{'='*60}")
print(f"FINAL VERDICT:")
print(f"  n=5 consec: {'✅ SAFE' if r1 else '⚠️ RISK'}")
print(f"  n=7 consec: {'✅ SAFE' if r2 else '⚠️ RISK'}")
print(f"  n=9 non-alt: {'✅ SAFE' if r3 else '⚠️ RISK'}")
