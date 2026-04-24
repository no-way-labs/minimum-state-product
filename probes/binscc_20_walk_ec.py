#!/usr/bin/env python3
"""When (2,0) produces phase-level EC: what walk property forces it?

At n=6, (2,0) has 90.2% EC rate. When does it FAIL?
The failures (7200 out of 73800) — what's different about those walks?

KEY IDEA: In a phase with (J=2, K=0):
- R fixed at R₀. L toggles twice: L₀ → L̄₀ → L₀.
- Nonmover visits: depends on ordering. Always includes (L₀,R₀) and (L̄₀,R₀).
- Mover at end: L after 2 toggles = L₀. So mover = (L₀, R₀).
- Nonmover ALSO has (L₀,R₀) from the first step → EC!

Wait, does the first step always have (L₀,R₀)?
Step 0 of phase: (L₀,R₀). If this is a nonmover step → nonmover has (L₀,R₀).
Then mover = (L₀,R₀) → EC!

But what if step 0 is NOT a nonmover step? In a phase, step 0 is the first step
where c[T]=k. Can this step be the mover (T fires)?
No! The mover is the LAST step of the phase (T firing changes c[T] from k to k+1).
So step 0 is always a nonmover step!

Wait, but phase k includes steps from the previous cycle wrap. The first step of
phase k is the step AFTER the previous T-firing changed c[T] to k.
Actually, in a cycle, phase k spans from the step after c[T] became k
until the step where T fires again (changing k to k+1).
The first step of phase k is right after the transition: c[T] just became k.
This step could be T itself firing again... no, T just fired and c[T]=k now.
The next T firing would be the LAST step of THIS phase.

So the first step of phase k IS a nonmover step (T doesn't fire here).
At this step: (L,R) = (L₀, R₀) — the initial values for this phase.

With (J=2, K=0): R stays R₀ throughout. L starts at L₀.
After the 2 L-toggles: L returns to L₀.
Mover (last step): (L₀, R₀).
First step (nonmover): (L₀, R₀).
OVERLAP! EC!

So (2,0) should ALWAYS give EC! Why does n=6 have 7200 failures?

Let me investigate these failures.
"""
import time
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

# First: verify the analytical argument at n=4,5 where (2,0) IS universal
print("=" * 70)
print("(2,0) PHASE EC: ANALYTICAL ARGUMENT VERIFICATION")
print("=" * 70)

for n, ms, label, max_len in [
    (5, [2,3,2,3,2], "n=5", 16),
]:
    words = enumerate_mover_words(ms, n, max_len)
    sandwiched = [p for p in range(n) if ms[p] == 3
                  and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

    for word in words[:500]:
        cycle = build_cycle(ms, n, word)
        if cycle is None or not is_wrap_adjacent(word, n):
            continue
        ell = len(word)
        for t in sandwiched:
            bL, bR = (t-1)%n, (t+1)%n
            for k in range(3):
                steps = [s for s in range(ell) if cycle[s][t] == k]
                J = sum(1 for s in steps if word[s] == bL)
                K = sum(1 for s in steps if word[s] == bR)
                if not ((J == 2 and K == 0) or (J == 0 and K == 2)):
                    continue
                # Check the L,R values at first and last steps
                first_s = steps[0]
                last_s = steps[-1]
                first_lr = (cycle[first_s][bL], cycle[first_s][bR])
                last_lr = (cycle[last_s][bL], cycle[last_s][bR])
                # Mover is last step (T fires)
                is_mover_last = (word[last_s] == t)
                # Is first step nonmover?
                is_first_nonmover = (word[first_s] != t)

                # Check if fc[T] > 3 (multiple movers per phase)
                M = sum(1 for s in steps if word[s] == t)

                if not is_mover_last or not is_first_nonmover or M != 1:
                    print(f"  *** UNEXPECTED: {label} P{t} phase {k}: "
                          f"mover_last={is_mover_last} first_nonmover={is_first_nonmover} "
                          f"M={M} J={J} K={K}")
                    print(f"      first_lr={first_lr} last_lr={last_lr}")
                    print(f"      word[first]={word[first_s]} word[last]={word[last_s]}")
                    print(f"      steps={steps[:10]}...")
    print(f"  {label}: checked (no unexpected found = mover is always last)")

# Now check n=6 failures
print(f"\n{'='*70}")
print("n=6: (2,0) PHASE FAILURES — DETAILED ANALYSIS")
print("=" * 70)

n, ms = 6, [2,3,2,3,2,3]
t0 = time.time()
words = enumerate_mover_words(ms, n, 24)
sandwiched = [p for p in range(n) if ms[p] == 3
              and ms[(p-1)%n] == 2 and ms[(p+1)%n] == 2]

failures_20 = []  # (2,0) phase without EC
successes_20 = 0

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue
    ell = len(word)
    for t in sandwiched:
        bL, bR = (t-1)%n, (t+1)%n
        for k in range(3):
            steps = [s for s in range(ell) if cycle[s][t] == k]
            J = sum(1 for s in steps if word[s] == bL)
            K = sum(1 for s in steps if word[s] == bR)
            if not ((J == 2 and K == 0) or (J == 0 and K == 2)):
                continue
            # Check phase EC
            m_lr, nm_lr = set(), set()
            for s in steps:
                lr = (cycle[s][bL], cycle[s][bR])
                if word[s] == t:
                    m_lr.add(lr)
                else:
                    nm_lr.add(lr)
            has_ec = bool(m_lr & nm_lr)
            if has_ec:
                successes_20 += 1
            else:
                M = sum(1 for s in steps if word[s] == t)
                first_lr = (cycle[steps[0]][bL], cycle[steps[0]][bR])
                last_lr = (cycle[steps[-1]][bL], cycle[steps[-1]][bR])
                if len(failures_20) < 20:
                    # Check M, first/last step details
                    failures_20.append({
                        't': t, 'k': k, 'J': J, 'K': K, 'M': M,
                        'd': len(steps), 'first_lr': first_lr, 'last_lr': last_lr,
                        'm_lr': m_lr, 'nm_lr': nm_lr,
                        'mover_last': word[steps[-1]] == t,
                        'first_nonmover': word[steps[0]] != t,
                        'fc_t': Counter(word)[t],
                    })

elapsed = time.time() - t0
print(f"({elapsed:.1f}s)")
print(f"  (2,0) successes: {successes_20}")
print(f"  (2,0) failures: {len(failures_20)} (sample)")

if failures_20:
    print(f"\n  Failure details:")
    for f in failures_20[:10]:
        print(f"    P{f['t']} phase {f['k']}: (J,K)=({f['J']},{f['K']}) M={f['M']} d={f['d']} "
              f"fc_t={f['fc_t']}")
        print(f"      first_lr={f['first_lr']} last_lr={f['last_lr']}")
        print(f"      m_lr={f['m_lr']} nm_lr={f['nm_lr']}")
        print(f"      mover_last={f['mover_last']} first_nonmover={f['first_nonmover']}")

    # KEY: Is M > 1 the culprit?
    m_values = Counter(f['M'] for f in failures_20)
    print(f"\n  M values in failures: {dict(m_values)}")
    fc_values = Counter(f['fc_t'] for f in failures_20)
    print(f"  fc[T] values in failures: {dict(fc_values)}")
