#!/usr/bin/env python3
"""
PA Domino Exploration 2: The S-flip prevents EC at t.

Key observation from explore 1: At t-fire k, S_k = (s0+k)%2.
In phase k, t doesn't fire, so t's value is (S_k+1)%2.
At the neighbor-fire step in phase k, context at t has S = (S_k+1)%2.
This is ALWAYS different from S_k. So mover vs nonmover at t ALWAYS differ in S.

This means EC at t cannot come from the simple domino argument!
EC must arise at a DIFFERENT processor, or from additional structure.

Let me reconsider: EC is at ANY processor, not just at t.
The real question: where does EC come from in the full cycle?

Let me also reconsider whether the non-mover observation includes
steps where OTHER processors fire (not just left/right of t).
"""

# Actually, I realize the issue. The S-flip is fundamental:
# At mover steps (t fires): S = initial for that step
# At non-mover steps in the phase: S = flipped
# So S always distinguishes mover from non-mover at t.
# EC at t is IMPOSSIBLE from this argument alone!

# But EC is verified computationally at 100%. So EC must come from
# a different processor than t.

# Let me think about EC at left(t) or right(t) instead.
# These are also binary. Consider EC at left(t):
# left(t) fires in some phases and not in others.

# Actually, the key claim in the problem setup says EC always holds
# for the SYSTEM (at some proc), not specifically at t.

# Let me re-examine: what's the actual sorry in Sweep.lean?
# It's `consec_isolated_false` which concludes `False`.
# The route is: under ¬hasEntryConflict, derive False.
# hasEntryConflict is ∃ proc, overlap at that proc.

# So we need to find EC at SOME processor.
# The domino at t fails because S flips.
# But what about at left(t) or right(t)?

# At left(t) = i (binary):
# Context at left(t) = (c_{left(left(t))}, c_{left(t)}, c_t)
# When left(t) fires (mover): we know c_{left(t)}, c_t at that step.
# When left(t) doesn't fire (non-mover): we know the same triple.

# The key: c_t changes when t fires. And t fires fc(t) times.
# So the context at left(t) changes when t fires.

# Hmm, this is getting complex. Let me do a FULL simulation.

from itertools import product as iproduct, combinations
from collections import Counter

def full_simulation(n, ms, word):
    """
    Given a ring of n processors with state counts ms and a mover word,
    simulate the good cycle and check EC at every processor.
    """
    ell = len(word)
    start = tuple(0 for _ in range(n))

    # Build configs
    cfgs = [list(start)]
    for i in range(ell):
        c = list(cfgs[-1])
        c[word[i]] = (c[word[i]] + 1) % ms[word[i]]
        cfgs.append(c)

    # Verify it's a good cycle
    assert tuple(cfgs[0]) == tuple(cfgs[ell]), f"Not a cycle: {cfgs[0]} != {cfgs[ell]}"

    # Check EC at each proc
    ec_procs = []
    for p in range(n):
        m_ctx = set()
        n_ctx = set()
        found = False
        for s in range(ell):
            ctx = (cfgs[s][(p-1)%n], cfgs[s][p], cfgs[s][(p+1)%n])
            if word[s] == p:
                if ctx in n_ctx:
                    found = True
                    break
                m_ctx.add(ctx)
            else:
                if ctx in m_ctx:
                    found = True
                    break
                n_ctx.add(ctx)
        if found:
            ec_procs.append(p)

    return ec_procs

# Let me look at this from a different angle.
# The problem says the SYSTEM is sub-threshold, sweep, etc.
# We have 3 consecutive binary. Can we get EC at procs OTHER than {i, right(i), right²(i)}?

# Actually wait — maybe I should look at what the real cycles look like.
# Let me enumerate actual cycles with 3 consecutive binary at n=5.

n = 5
ms_list = [
    [2, 2, 2, 3, 3],  # binary at 0,1,2
    [3, 2, 2, 2, 3],  # binary at 1,2,3
]

for ms in ms_list:
    print(f"\n{'='*60}")
    print(f"n={n}, ms={ms}")
    print(f"{'='*60}")

    start = tuple(0 for _ in range(n))
    ring_adj = {p: [(p-1)%n, (p+1)%n] for p in range(n)}

    results = []
    def dfs(word, fc, config):
        if len(word) > 4*n: return
        if len(word) >= 2*n and config == start:
            if all(fc[p] > 0 and fc[p] % ms[p] == 0 for p in range(n)):
                results.append(tuple(word))
                if len(results) >= 5000: return
            return
        if len(results) >= 5000: return
        remaining = 4*n - len(word)
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
        if needed > remaining: return
        for nxt in range(n):
            if abs(nxt - word[-1]) % n not in [1, n-1]: continue
            if len(results) >= 5000: return
            word.append(nxt)
            nf = list(fc); nf[nxt] += 1
            nc = list(config); nc[nxt] = (nc[nxt]+1) % ms[nxt]
            dfs(word, nf, tuple(nc))
            word.pop()

    for p in range(n):
        if len(results) >= 5000: break
        first = list(start); first[p] = (first[p]+1) % ms[p]
        dfs([p], [1 if i==p else 0 for i in range(n)], tuple(first))

    print(f"Found {len(results)} good cycles")

    # For each cycle, check if it's zero-winding
    def winding(word):
        w = 0
        for i in range(len(word)):
            d = (word[(i+1)%len(word)] - word[i]) % n
            if d == 1: w += 1
            elif d == n-1: w -= 1
        return w

    zw = [w for w in results if winding(w) == 0]
    print(f"Zero-winding: {len(zw)}")

    # Find binary positions
    bin_pos = [p for p in range(n) if ms[p] == 2]
    print(f"Binary positions: {bin_pos}")

    # For the middle binary (t):
    # Find 3 consecutive binary
    consec3 = None
    for start_p in range(n):
        if all(ms[(start_p + j) % n] == 2 for j in range(3)):
            consec3 = [(start_p + j) % n for j in range(3)]
            break

    if consec3 is None:
        print("No 3 consecutive binary")
        continue

    i_pos, t_pos, r_pos = consec3
    print(f"3 consecutive binary: i={i_pos}, t={t_pos}, right²(i)={r_pos}")

    # For each zero-winding cycle, check:
    # 1. Is t isolated?
    # 2. What are the phases?
    # 3. Where is EC?
    normalform_count = 0
    ec_at_t_count = 0
    ec_elsewhere_count = 0

    for word in zw:
        ell = len(word)
        fc = Counter(word)

        # Check isolated firings at t
        t_steps = [s for s in range(ell) if word[s] == t_pos]
        if len(t_steps) < 2: continue

        isolated = True
        for s in t_steps:
            next_s = (s + 1) % ell
            prev_s = (s - 1) % ell
            if word[next_s] == t_pos or word[prev_s] == t_pos:
                isolated = False
                break
        if not isolated: continue

        # Check phases (gaps between t-fires)
        all_normalform = True
        for idx in range(len(t_steps)):
            a = t_steps[idx]
            b = t_steps[(idx + 1) % len(t_steps)]
            if b <= a: b += ell

            J = sum(1 for s in range(a+1, b) if word[s % ell] == i_pos)
            K = sum(1 for s in range(a+1, b) if word[s % ell] == r_pos)

            if J + K > 1:
                all_normalform = False
                break

        if not all_normalform: continue
        normalform_count += 1

        # Check EC
        ec_procs = full_simulation(n, ms, word)

        if t_pos in ec_procs:
            ec_at_t_count += 1
        elif len(ec_procs) > 0:
            ec_elsewhere_count += 1
        else:
            print(f"  NO EC ANYWHERE: word={word}, fc={dict(fc)}")

    print(f"NormalForm isolated cycles: {normalform_count}")
    print(f"  EC at t={t_pos}: {ec_at_t_count}")
    print(f"  EC elsewhere (not at t): {ec_elsewhere_count}")
    print(f"  No EC: {normalform_count - ec_at_t_count - ec_elsewhere_count}")
