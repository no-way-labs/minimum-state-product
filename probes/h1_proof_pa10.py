#!/usr/bin/env python3
"""
Check: does EC ALWAYS occur at the sandwiched ternary t itself?
If so, the proof is much simpler.
"""
from collections import Counter
from itertools import product as iproduct

def enumerate_good_cycles(ms, n, max_length=20):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
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

def build_configs(ms, n, word):
    L = len(word)
    configs = [tuple(0 for _ in range(n))]
    for i in range(L):
        p = word[i]
        c = list(configs[-1])
        c[p] = (c[p] + 1) % ms[p]
        configs.append(tuple(c))
    if configs[-1] != configs[0]:
        return None
    if len(set(configs[:L])) != L:
        return None
    return configs[:L]

def is_wrap_adjacent(word, n):
    return abs(word[-1] - word[0]) % n in (1, n-1)

def find_phases_at_t(word, t, n):
    L = len(word)
    bL, bR = (t-1)%n, (t+1)%n
    t_steps = [s for s in range(L) if word[s] == t]
    if not t_steps:
        return []
    phases = []
    for idx in range(len(t_steps)):
        s1 = t_steps[idx]
        s2 = t_steps[(idx+1)%len(t_steps)]
        steps = []
        s = (s1+1)%L
        while s != s2:
            steps.append(s)
            s = (s+1)%L
        J = sum(1 for s in steps if word[s] == bL)
        K = sum(1 for s in steps if word[s] == bR)
        phases.append((J, K, steps))
    return phases

def has_ec_at_proc(word, configs, p, n, ms):
    L = len(word)
    pL, pR = (p-1)%n, (p+1)%n
    mover, nonmover = set(), set()
    for s in range(L):
        ctx = (configs[s][pL], configs[s][p], configs[s][pR])
        if word[s] == p:
            mover.add(ctx)
        else:
            nonmover.add(ctx)
    return bool(mover & nonmover)

n = 5
threshold = 4 * 3**(n-2)

print("="*70)
print(f"Does EC always occur at the sandwiched ternary t? (n={n})")
print("="*70)

for ms_tuple in iproduct([2,3], repeat=n):
    ms = list(ms_tuple)
    prod = 1
    for m in ms:
        prod *= m
    if prod >= threshold:
        continue
    binary = [p for p in range(n) if ms[p] == 2]
    if len(binary) < 3:
        continue
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    if not sandwiched:
        continue

    words = enumerate_good_cycles(ms, n, 20)

    total_11 = 0
    ec_at_t = 0
    ec_not_at_t = 0  # EC exists but NOT at sandwiched t

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        if not is_wrap_adjacent(word, n):
            continue

        has_11 = False
        active_t = None
        for t in sandwiched:
            phases = find_phases_at_t(word, t, n)
            if any(J==1 and K==1 for (J,K,_) in phases):
                has_11 = True
                active_t = t
                break
        if not has_11:
            continue
        total_11 += 1

        # Check EC specifically at t
        if has_ec_at_proc(word, configs, active_t, n, ms):
            ec_at_t += 1
        else:
            # EC must be elsewhere
            ec_not_at_t += 1

    if total_11 > 0:
        print(f"ms={ms}: total_11={total_11}, ec_at_t={ec_at_t}, ec_NOT_at_t={ec_not_at_t}")

# KEY QUESTION: Is EC always at t?
print("\n" + "="*70)
print("For cycles where EC is NOT at t, where IS it?")
print("="*70)

for ms_tuple in iproduct([2,3], repeat=n):
    ms = list(ms_tuple)
    prod = 1
    for m in ms:
        prod *= m
    if prod >= threshold:
        continue
    binary = [p for p in range(n) if ms[p] == 2]
    if len(binary) < 3:
        continue
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    if not sandwiched:
        continue

    words = enumerate_good_cycles(ms, n, 20)

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        if not is_wrap_adjacent(word, n):
            continue

        has_11 = False
        active_t = None
        for t in sandwiched:
            phases = find_phases_at_t(word, t, n)
            if any(J==1 and K==1 for (J,K,_) in phases):
                has_11 = True
                active_t = t
                break
        if not has_11:
            continue

        if not has_ec_at_proc(word, configs, active_t, n, ms):
            # Where IS the EC?
            ec_procs = []
            for p in range(n):
                if has_ec_at_proc(word, configs, p, n, ms):
                    ec_procs.append(p)

            L = len(word)
            fc = Counter(word)
            phases = find_phases_at_t(word, active_t, n)
            phase_nfs = [(J,K) for (J,K,_) in phases]
            print(f"ms={ms}, word={word}")
            print(f"  t={active_t}, phases={phase_nfs}, fc(t)={fc[active_t]}")
            print(f"  EC NOT at t, but at procs: {ec_procs}")
            for p in ec_procs:
                pL, pR = (p-1)%n, (p+1)%n
                mover, nonmover = set(), set()
                for s in range(L):
                    ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                    if word[s] == p:
                        mover.add(ctx)
                    else:
                        nonmover.add(ctx)
                print(f"    proc {p}: m={ms[p]}, ctx_space={ms[pL]*ms[p]*ms[pR]}, "
                      f"|mover|={len(mover)}, |nonmover|={len(nonmover)}, "
                      f"overlap={mover & nonmover}")
            break  # just one example per system
