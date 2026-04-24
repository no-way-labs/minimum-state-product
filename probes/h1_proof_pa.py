#!/usr/bin/env python3
"""
Verification: Entry conflict for (1,1)-phase sandwiched ternary.

Claim: For n>=5, >=3 binary, sub-threshold product, if a sandwiched ternary t
has a normalForm (1,1) phase, then the good cycle has entry conflict somewhere.

We enumerate good cycles, identify (1,1) phases, and check for EC.
Also analyze WHERE the EC occurs (distance from t, context space).
"""
from itertools import product as iprod
from collections import Counter, defaultdict

def enumerate_good_cycles(ms, n, max_length=20):
    """Enumerate good cycles (mover words + config sequences)."""
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
    """Build configuration sequence from mover word."""
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

def find_phases_at_t(word, t, n):
    """Find all phases at processor t. A phase is interval between consecutive firings of t.
    Returns list of phases, each phase = (start_step, end_step, J, K)
    where J = fires of t-1, K = fires of t+1 in the phase."""
    L = len(word)
    bL = (t - 1) % n
    bR = (t + 1) % n

    # Find all steps where t fires
    t_steps = [s for s in range(L) if word[s] == t]
    if len(t_steps) == 0:
        return []

    phases = []
    for idx in range(len(t_steps)):
        s1 = t_steps[idx]
        s2 = t_steps[(idx + 1) % len(t_steps)]

        # Collect steps in the phase (between s1 and s2, exclusive of t's firings)
        phase_steps = []
        s = (s1 + 1) % L
        while s != s2:
            phase_steps.append(s)
            s = (s + 1) % L

        J = sum(1 for s in phase_steps if word[s] == bL)
        K = sum(1 for s in phase_steps if word[s] == bR)
        phases.append((s1, s2, J, K))

    return phases

def has_11_phase(word, t, n):
    """Check if t has a (1,1) normalForm phase."""
    phases = find_phases_at_t(word, t, n)
    for (s1, s2, J, K) in phases:
        if J == 1 and K == 1:
            return True
    return False

def find_entry_conflicts(word, configs, ms, n):
    """Find all processors with entry conflict. Return dict: proc -> set of conflicting contexts."""
    L = len(word)
    ec_procs = {}

    for p in range(n):
        mover_ctx = set()
        nonmover_ctx = set()
        pL = (p - 1) % n
        pR = (p + 1) % n

        for s in range(L):
            ctx = (configs[s][pL], configs[s][p], configs[s][pR])
            if word[s] == p:
                mover_ctx.add(ctx)
            else:
                nonmover_ctx.add(ctx)

        overlap = mover_ctx & nonmover_ctx
        if overlap:
            ec_procs[p] = overlap

    return ec_procs

def ring_distance(a, b, n):
    d = abs(a - b) % n
    return min(d, n - d)

# ===== MAIN VERIFICATION =====
print("=" * 70)
print("VERIFICATION: (1,1)-phase sandwiched ternary → entry conflict")
print("=" * 70)

test_cases = [
    # (n, ms, label, max_len)
    (5, [2, 2, 2, 3, 3], "n=5 ms=[2,2,2,3,3]", 18),
    (5, [2, 2, 3, 2, 3], "n=5 ms=[2,2,3,2,3]", 18),
    (5, [2, 3, 2, 3, 2], "n=5 ms=[2,3,2,3,2]", 16),
    (5, [2, 2, 2, 3, 4], "n=5 ms=[2,2,2,3,4]", 16),
    (5, [2, 2, 2, 2, 3], "n=5 ms=[2,2,2,2,3]", 16),
]

for n, ms, label, max_len in test_cases:
    prod = 1
    for m in ms:
        prod *= m
    threshold = 4 * (3 ** (n - 2))
    if prod >= threshold:
        print(f"\n{label}: product {prod} >= threshold {threshold}, SKIP")
        continue

    binary = [p for p in range(n) if ms[p] == 2]
    if len(binary) < 3:
        print(f"\n{label}: only {len(binary)} binary, SKIP")
        continue

    # Find sandwiched ternaries
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    print(f"\n{'='*60}")
    print(f"{label}: product={prod}, threshold={threshold}")
    print(f"  binary={binary}, sandwiched ternary={sandwiched}")

    words = enumerate_good_cycles(ms, n, max_len)

    total_cycles = 0
    with_11 = 0
    with_11_and_ec = 0
    with_11_no_ec = 0
    ec_location = Counter()  # (dist_from_nearest_sandwiched, is_binary, ctx_space) -> count
    ec_proc_detail = Counter()  # proc index -> count

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        total_cycles += 1

        # Check if any sandwiched ternary has (1,1) phase
        has_11 = False
        for t in sandwiched:
            if has_11_phase(word, t, n):
                has_11 = True
                break

        if not has_11:
            continue
        with_11 += 1

        # Check for EC
        ec = find_entry_conflicts(word, configs, ms, n)
        if ec:
            with_11_and_ec += 1
            for p in ec:
                dist = min(ring_distance(p, t, n) for t in sandwiched)
                ctx_space = ms[(p-1)%n] * ms[p] * ms[(p+1)%n]
                ec_location[(dist, ms[p] == 2, ctx_space)] += 1
                ec_proc_detail[p] += 1
        else:
            with_11_no_ec += 1
            print(f"  *** NO EC: word={word}, fc={Counter(word)}")

    print(f"  Total cycles: {total_cycles}")
    print(f"  With (1,1) phase: {with_11}")
    print(f"  With (1,1) + EC: {with_11_and_ec}")
    print(f"  With (1,1) + NO EC: {with_11_no_ec}")
    if with_11 > 0:
        print(f"  EC rate: {100*with_11_and_ec/with_11:.1f}%")

    print(f"  EC location breakdown (dist, is_binary, ctx_space):")
    for key, cnt in sorted(ec_location.items()):
        print(f"    dist={key[0]}, binary={key[1]}, ctx_space={key[2]}: {cnt}")

    print(f"  EC by processor:")
    for p, cnt in sorted(ec_proc_detail.items()):
        print(f"    proc {p} (m={ms[p]}, neighbors m={ms[(p-1)%n]},{ms[(p+1)%n]}): {cnt}")
