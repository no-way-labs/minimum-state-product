#!/usr/bin/env python3
"""
Key insight from exceptions: ALL have a (0,0) phase at t.
This means fc(t) = 3 (minimum for ternary to return), and the phase
pattern is [(1,1), (1,1), (0,0)] -- two (1,1) phases plus one (0,0) phase.

New hypothesis: if ALL phases at t are (1,1), then EC must hold.
With fc(t)=3, having all phases be (1,1) requires 3 phases each (1,1),
meaning bL fires 3 times and bR fires 3 times. But bL is binary,
so fc(bL) must be even (multiple of 2). fc(bL)=3 is impossible for binary!

Wait: binary just means m=2, and fc must be a multiple of m=2.
So fc(bL) ∈ {2,4,6,...}. If all 3 phases have J=1, total J=3, but
fc(bL) must be even. Contradiction: 3 is odd.

So with fc(t)=3: we can't have all three phases be (1,1).
At least one phase must have J != 1 or K != 1.

But the claim says "has a (1,1) phase" (at least one), not "all phases are (1,1)".

Let me verify: what if we restrict to cycles where ALL phases at t are (1,1)?
That's impossible with fc(t)=3 as shown above.

What if fc(t)=6? Then 6 phases, J_total = 6 (even ok for fc(bL)).
All-6 phases being (1,1) gives fc(bL)=6, fc(bR)=6. Let's check.

Actually, let me think about this differently.
The claim says "normalForm (1,1) phases" — maybe this means the phase
decomposition has a specific normal form. Let me re-read the claim.

Actually re-reading: "normalForm (1,1) phases at t" means phases where
the normalForm is (1,1). This is a property of individual phases.

The fundamental issue: having SOME (1,1) phases is not enough for EC.
What additional condition on the cycle structure forces EC?

Let me check: what is the fc(t) distribution for exception vs non-exception?
And what is the minimum-length property?
"""
from collections import Counter

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
    phases = find_phases_at_t(word, t, n)
    return any(J == 1 and K == 1 for (J, K) in phases)

def all_11_phases(word, t, n):
    phases = find_phases_at_t(word, t, n)
    return all(J == 1 and K == 1 for (J, K) in phases)

def find_entry_conflicts(word, configs, ms, n):
    L = len(word)
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
        if mover_ctx & nonmover_ctx:
            return True
    return False

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

# Test with minimum firecount condition
print("=" * 70)
print("ANALYSIS: fc(t) and phase pattern vs EC")
print("=" * 70)

for ms_label, ms in [
    ("2,2,2,2,3", [2,2,2,2,3]),
    ("2,2,3,2,4", [2,2,3,2,4]),
    ("2,2,4,2,3", [2,2,4,2,3]),
    ("2,2,3,2,3", [2,2,3,2,3]),
    ("2,3,2,3,2", [2,3,2,3,2]),
]:
    n = 5
    threshold = 4 * 3**(n-2)
    prod = 1
    for m in ms:
        prod *= m
    if prod >= threshold:
        continue

    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    if not sandwiched:
        continue

    words = enumerate_good_cycles(ms, n, 18)

    print(f"\nms={ms_label}, sandwiched={sandwiched}")

    # Categorize cycles
    stats = Counter()  # (has_11, has_00, fc_t, has_ec) -> count
    exc_details = []

    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue

        for t in sandwiched:
            phases = find_phases_at_t(word, t, n)
            has_11 = any(J == 1 and K == 1 for (J, K) in phases)
            has_00 = any(J == 0 and K == 0 for (J, K) in phases)
            fc_t = Counter(word)[t]

            if not has_11:
                continue

            has_ec = find_entry_conflicts(word, configs, ms, n)
            key = (has_00, fc_t, has_ec)
            stats[key] += 1

            if not has_ec:
                exc_details.append((word, t, phases, fc_t))

    print("  (has_00_phase, fc_t, has_ec) -> count:")
    for key in sorted(stats.keys()):
        print(f"    has_00={key[0]}, fc_t={key[1]}, EC={key[2]}: {stats[key]}")

# The key finding
print("\n" + "=" * 70)
print("KEY FINDING: Exceptions ALWAYS have (0,0) phase")
print("=" * 70)
print("If all phases at t are (1,1), then:")
print("  fc(t) = 3k for k = number of phases")
print("  fc(bL) = J_total = sum of J's = k (all phases have J=1)")
print("  fc(bR) = K_total = sum of K's = k")
print("  But fc(bL) must be even (binary): k must be even")
print("  And fc(t) = 3k where k is even: fc(t) ∈ {6, 12, ...}")
print("  This means fc(t) >= 6.")
print()

# Check: does the claim hold if we add "no (0,0) phase"?
print("Checking refined claim: (1,1) phase AND no (0,0) phase -> EC")
for ms_label, ms in [
    ("2,2,2,2,3", [2,2,2,2,3]),
    ("2,2,3,2,4", [2,2,3,2,4]),
    ("2,2,4,2,3", [2,2,4,2,3]),
    ("2,2,3,2,3", [2,2,3,2,3]),
    ("2,3,2,3,2", [2,3,2,3,2]),
]:
    n = 5
    prod = 1
    for m in ms:
        prod *= m
    if prod >= 4*3**(n-2):
        continue
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    if not sandwiched:
        continue

    words = enumerate_good_cycles(ms, n, 18)
    exc = 0
    total = 0
    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        for t in sandwiched:
            phases = find_phases_at_t(word, t, n)
            has_11 = any(J == 1 and K == 1 for (J, K) in phases)
            has_00 = any(J == 0 and K == 0 for (J, K) in phases)
            if has_11 and not has_00:
                total += 1
                if not find_entry_conflicts(word, configs, ms, n):
                    exc += 1
    print(f"  ms={ms_label}: total_with_11_no_00={total}, exceptions={exc}")

# Alternatively: check ALL phases (1,1) condition
print("\nChecking: ALL phases at t are (1,1) -> EC")
for ms_label, ms in [
    ("2,2,2,2,3", [2,2,2,2,3]),
    ("2,2,3,2,4", [2,2,3,2,4]),
    ("2,2,4,2,3", [2,2,4,2,3]),
    ("2,2,3,2,3", [2,2,3,2,3]),
    ("2,3,2,3,2", [2,3,2,3,2]),
]:
    n = 5
    prod = 1
    for m in ms:
        prod *= m
    if prod >= 4*3**(n-2):
        continue
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]
    if not sandwiched:
        continue

    words = enumerate_good_cycles(ms, n, 22)
    exc = 0
    total = 0
    for word in words:
        configs = build_configs(ms, n, word)
        if configs is None:
            continue
        for t in sandwiched:
            if all_11_phases(word, t, n):
                total += 1
                if not find_entry_conflicts(word, configs, ms, n):
                    exc += 1
                    print(f"    EXCEPTION: word={word}, fc_t={Counter(word)[t]}")
    print(f"  ms={ms_label}: total_all_11={total}, exceptions={exc}")
