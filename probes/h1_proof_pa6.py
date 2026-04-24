#!/usr/bin/env python3
"""
Verify the correct claim: For {2,3} state sizes only (no quaternary),
with sub-threshold product, >=3 binary, sandwiched ternary t,
if a good cycle has a (1,1) phase at t, then EC exists SOMEWHERE.

Also: understand WHERE the EC occurs. The pigeonhole argument needs
a binary proc with all-binary context (ctx_space=8).

Key structural question: with {2,3} state sizes and sandwiched ternary,
does there always exist a binary proc with all-binary neighbors?
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
    bL = (t - 1) % n
    bR = (t + 1) % n
    t_steps = [s for s in range(L) if word[s] == t]
    if not t_steps:
        return []
    phases = []
    for idx in range(len(t_steps)):
        s1 = t_steps[idx]
        s2 = t_steps[(idx + 1) % len(t_steps)]
        phase_steps = []
        s = (s1 + 1) % L
        while s != s2:
            phase_steps.append(s)
            s = (s + 1) % L
        J = sum(1 for s in phase_steps if word[s] == bL)
        K = sum(1 for s in phase_steps if word[s] == bR)
        phases.append((J, K))
    return phases

def has_11_phase(word, t, n):
    return any(J == 1 and K == 1 for (J, K) in find_phases_at_t(word, t, n))

def find_all_ec(word, configs, ms, n):
    """Return set of procs with EC."""
    L = len(word)
    ec = set()
    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        pL, pR = (p-1)%n, (p+1)%n
        for s in range(L):
            ctx = (configs[s][pL], configs[s][p], configs[s][pR])
            if word[s] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)
        if mover_ctx & nonmover_ctx:
            ec.add(p)
    return ec

# ===== Check {2,3} systems at n=5 and n=7 =====
print("="*70)
print("VERIFICATION: {2,3} state sizes, (1,1)-phase -> EC")
print("="*70)

for n in [5, 7]:
    threshold = 4 * 3**(n-2)
    print(f"\nn={n}, threshold={threshold}")

    total_11 = 0
    total_ec = 0
    total_exc = 0

    for ms_tuple in iproduct([2, 3], repeat=n):
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

        # Check structural property: binary with all-binary neighbors
        binary_allbinary = [p for p in binary
                           if ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

        max_len = 16 if n == 5 else 22
        words = enumerate_good_cycles(ms, n, max_len)

        for word in words:
            configs = build_configs(ms, n, word)
            if configs is None:
                continue
            if not is_wrap_adjacent(word, n):
                continue

            has_11 = any(has_11_phase(word, t, n) for t in sandwiched)
            if not has_11:
                continue

            total_11 += 1
            ec_procs = find_all_ec(word, configs, ms, n)
            if ec_procs:
                total_ec += 1
                # Check if EC is at an all-binary-context proc
            else:
                total_exc += 1
                print(f"  EXCEPTION: ms={ms}, word={word}")

    print(f"  Total with (1,1): {total_11}")
    print(f"  With EC: {total_ec}")
    print(f"  Exceptions: {total_exc}")

# ===== Structural analysis: does all-binary-neighbor proc always exist? =====
print("\n" + "="*70)
print("STRUCTURAL: binary with all-binary neighbors always exists?")
print("="*70)

for n in [5, 7, 9]:
    threshold = 4 * 3**(n-2)
    counter = 0
    no_allbinary = 0

    for ms_tuple in iproduct([2, 3], repeat=n):
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

        counter += 1
        binary_allbinary = [p for p in binary
                           if ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
        if not binary_allbinary:
            no_allbinary += 1
            if n <= 7:
                print(f"  n={n}: ms={ms} has NO all-binary-neighbor binary proc")

    print(f"  n={n}: {counter} systems, {no_allbinary} without all-binary-neighbor binary")

# ===== Key counting argument =====
print("\n" + "="*70)
print("COUNTING: at all-binary proc q, mover vs nonmover contexts")
print("="*70)

n = 5
for ms_tuple in iproduct([2, 3], repeat=n):
    ms = list(ms_tuple)
    prod = 1
    for m in ms:
        prod *= m
    threshold = 4 * 3**(n-2)
    if prod >= threshold:
        continue
    binary = [p for p in range(n) if ms[p] == 2]
    if len(binary) < 3:
        continue
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    if not sandwiched:
        continue

    binary_allbinary = [p for p in binary
                       if ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    if not binary_allbinary:
        continue

    words = enumerate_good_cycles(ms, n, 16)
    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        if not is_wrap_adjacent(word, n):
            continue
        has_11 = any(has_11_phase(word, t, n) for t in sandwiched)
        if not has_11:
            continue

        L = len(word)
        fc = Counter(word)
        for q in binary_allbinary:
            pL, pR = (q-1)%n, (q+1)%n
            mover_ctx = set()
            nonmover_ctx = set()
            for s in range(L):
                ctx = (configs[s][pL], configs[s][q], configs[s][pR])
                if word[s] == q:
                    mover_ctx.add(ctx)
                else:
                    nonmover_ctx.add(ctx)

            n_mover = len(mover_ctx)
            n_nonmover = len(nonmover_ctx)
            overlap = mover_ctx & nonmover_ctx

            # Report when NO overlap at q
            if not overlap and n_mover + n_nonmover <= 8:
                pass  # Expected when overlap would need > 8

        # Overall: is there overlap at SOME proc?
        ec = find_all_ec(word, configs, ms, n)
        if not ec:
            print(f"  NO EC ANYWHERE: ms={ms}, word={word}")
            for q in binary_allbinary:
                pL, pR = (q-1)%n, (q+1)%n
                mover_ctx = set()
                nonmover_ctx = set()
                for s in range(L):
                    ctx = (configs[s][pL], configs[s][q], configs[s][pR])
                    if word[s] == q:
                        mover_ctx.add(ctx)
                    else:
                        nonmover_ctx.add(ctx)
                print(f"    q={q}: |mover|={len(mover_ctx)}, |nonmover|={len(nonmover_ctx)}, "
                      f"total={len(mover_ctx)+len(nonmover_ctx)}, ctx_space=8")
