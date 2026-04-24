#!/usr/bin/env python3
"""
Fast verification for n=5 only, {2,3} state sizes.
Focus on the proof mechanism: at all-binary-context proc q,
count distinct mover vs nonmover contexts.
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

n = 5
threshold = 4 * 3**(n-2)

# Collect ALL distinct {2,3}-only systems
systems = []
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
    systems.append((ms, sandwiched))

print(f"n=5, threshold={threshold}")
print(f"Systems with >=3 binary + sandwiched ternary: {len(systems)}")
for ms, sw in systems:
    binary_allbinary = [p for p in range(n) if ms[p]==2
                       and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
    print(f"  ms={ms}, sandwiched={sw}, all-binary-ctx procs={binary_allbinary}")

print(f"\n{'='*70}")
print("DETAILED CONTEXT ANALYSIS at all-binary-context procs")
print("="*70)

grand_total_11 = 0
grand_total_ec = 0
grand_total_exc = 0

# Track min (|mover_distinct| + |nonmover_distinct|) over all-binary q
min_total_contexts = {}  # ms_tuple -> min value

for ms, sandwiched in systems:
    words = enumerate_good_cycles(ms, n, 20)
    binary_allbinary = [p for p in range(n) if ms[p]==2
                       and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]

    total_11 = 0
    ec_count = 0
    exc_count = 0

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        if not is_wrap_adjacent(word, n):
            continue

        has_11 = False
        for t in sandwiched:
            phases = find_phases_at_t(word, t, n)
            if any(J==1 and K==1 for (J,K,_) in phases):
                has_11 = True
                break
        if not has_11:
            continue

        total_11 += 1
        L = len(word)
        fc = Counter(word)

        # Check EC at all procs
        has_ec_anywhere = False
        for p in range(n):
            pL, pR = (p-1)%n, (p+1)%n
            mover, nonmover = set(), set()
            for s in range(L):
                ctx = (configs[s][pL], configs[s][p], configs[s][pR])
                if word[s] == p:
                    mover.add(ctx)
                else:
                    nonmover.add(ctx)
            if mover & nonmover:
                has_ec_anywhere = True
                break

        if has_ec_anywhere:
            ec_count += 1
        else:
            exc_count += 1

        # Context analysis at all-binary procs
        for q in binary_allbinary:
            pL, pR = (q-1)%n, (q+1)%n
            mover, nonmover = set(), set()
            for s in range(L):
                ctx = (configs[s][pL], configs[s][q], configs[s][pR])
                if word[s] == q:
                    mover.add(ctx)
                else:
                    nonmover.add(ctx)
            total_distinct = len(mover) + len(nonmover - mover)
            key = tuple(ms)
            if key not in min_total_contexts or total_distinct < min_total_contexts[key]:
                min_total_contexts[key] = total_distinct

    grand_total_11 += total_11
    grand_total_ec += ec_count
    grand_total_exc += exc_count

    print(f"\nms={ms}: {total_11} cycles with (1,1), EC={ec_count}, exc={exc_count}")

print(f"\n{'='*70}")
print(f"GRAND TOTAL: {grand_total_11} cycles, EC={grand_total_ec}, exceptions={grand_total_exc}")
print(f"{'='*70}")

# Now analyze the (1,1) phase structure more carefully for the proof
print(f"\n{'='*70}")
print("PHASE STRUCTURE ANALYSIS for the proof")
print("="*70)

# For each cycle with (1,1) phase, count how many contexts appear at
# the all-binary proc, and what the fc values are

for ms, sandwiched in systems:
    binary_allbinary = [p for p in range(n) if ms[p]==2
                       and ms[(p-1)%n]==2 and ms[(p+1)%n]==2]
    if not binary_allbinary:
        continue

    words = enumerate_good_cycles(ms, n, 20)
    print(f"\nms={ms}, all-binary procs={binary_allbinary}")

    # Collect (fc_q, L, |mover|, |nonmover|, |overlap|, phases_at_t)
    records = []
    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        if not is_wrap_adjacent(word, n):
            continue

        for t in sandwiched:
            phases = find_phases_at_t(word, t, n)
            if not any(J==1 and K==1 for (J,K,_) in phases):
                continue

            L = len(word)
            fc = Counter(word)
            phase_nfs = [(J,K) for (J,K,_) in phases]

            for q in binary_allbinary:
                pL, pR = (q-1)%n, (q+1)%n
                mover, nonmover = set(), set()
                for s in range(L):
                    ctx = (configs[s][pL], configs[s][q], configs[s][pR])
                    if word[s] == q:
                        mover.add(ctx)
                    else:
                        nonmover.add(ctx)
                overlap = mover & nonmover
                records.append((fc[q], L, len(mover), len(nonmover), len(overlap), phase_nfs))
            break  # just one sandwiched is enough

    # Summarize
    from collections import defaultdict
    by_fc = defaultdict(list)
    for (fcq, L, nm, nn, no, pnfs) in records:
        by_fc[fcq].append((L, nm, nn, no))

    for fcq in sorted(by_fc.keys()):
        entries = by_fc[fcq]
        min_nm = min(e[1] for e in entries)
        max_nm = max(e[1] for e in entries)
        min_nn = min(e[2] for e in entries)
        max_nn = max(e[2] for e in entries)
        has_overlap = sum(1 for e in entries if e[3] > 0)
        no_overlap = sum(1 for e in entries if e[3] == 0)
        print(f"  fc(q)={fcq}: {len(entries)} records, "
              f"|mover|={min_nm}..{max_nm}, |nonmover|={min_nn}..{max_nn}, "
              f"overlap={has_overlap}, no_overlap={no_overlap}")
