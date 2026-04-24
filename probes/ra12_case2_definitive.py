#!/usr/bin/env python3
"""RA12 DEFINITIVE: Summary of findings and proof architecture.

MAIN FINDING:
- EC at all-binary-context processor q: FAILS for Case 2 (66% at n=7)
- EC at sandwiched ternary t (fc=3): works 99.3% (48 exceptions)
- EC at SOME processor: works 100% (universal)
- EC is ALWAYS intra-phase (cross-phase EC = 0)

PROOF MECHANISM for EC at t (fc=3):
1. Parity argument: at least 1 of 3 phases has same-side entry/exit [100% verified]
2. Same-side + multi-step: gives double same-side neighbor firing
3. Double same-side: guarantees non-neighbor nm step between [100%]
4. Non-neighbor step between double: has correct R (or L) value, EC follows

GAP: 48 exceptions where:
- Same-side phase has only 1 nm step (2-step phase)
- No non-neighbor step in same-side phase
- Other phases are cross-side (also no direct EC)
- EC exists at non-sandwiched ternary procs

Question: Is the same-side phase ALWAYS multi-step? Or can it be 2-step?

ANSWER: It CAN be 2-step. The 48 exceptions prove this.

So the proof needs TWO paths:
Path A: If any phase has >= 3 steps AND same-side -> EC at t [covers 99.3%]
Path B: All same-side phases are 2-step -> need different argument

For Path B: Let's understand the structure more carefully.
If 2 phases are 2-step: those 2 phases consume 4 steps.
The 3rd phase has L-4 steps where L = cycle length.
Since L >= 2n and n >= 5, the 3rd phase has >= 6 steps.
The 3rd phase is cross-side (entry=A, exit=B, A!=B).
It has >= 2 neighbor firings of B (including exit) and >= 1 of A (including entry).

Actually: the 3rd phase has ALL the action. Let me check if the 3rd phase
gives double same-side even though it's cross-side.
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

def has_ec_at_proc(word, cycle, ms, n, p):
    ell = len(word)
    pL = (p - 1) % n
    pR = (p + 1) % n
    mover_ctx = set()
    nonmover_ctx = set()
    for s in range(ell):
        ctx = (cycle[s][pL], cycle[s][p], cycle[s][pR])
        if word[s] == p:
            mover_ctx.add(ctx)
        else:
            nonmover_ctx.add(ctx)
    return bool(mover_ctx & nonmover_ctx)

# ===== For the 48 exceptions: big phase structure =====
print("=" * 70)
print("THE 48 EXCEPTIONS: Big phase (cross-side) structure")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

exceptions = []
for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
        if fc[t] != 3:
            continue
        if not has_ec_at_proc(word, cycle, ms, n, t):
            exceptions.append((word, t))

print(f"Total exceptions: {len(exceptions)}")

# The 48 exceptions: analyze EVERY phase
big_phase_neighbor_counts = Counter()

for word, t in exceptions:
    cycle = build_cycle(ms, n, word)
    ell = len(word)
    tL = (t - 1) % n
    tR = (t + 1) % n

    t_mover_steps = sorted([s for s in range(ell) if word[s] == t])

    for i, sm in enumerate(t_mover_steps):
        prev_sm = t_mover_steps[(i - 1) % 3]

        nm_steps = []
        s = (prev_sm + 1) % ell
        while s != sm:
            nm_steps.append(s)
            s = (s + 1) % ell

        nL = sum(1 for s in nm_steps if word[s] == tL)
        nR = sum(1 for s in nm_steps if word[s] == tR)
        nO = len(nm_steps) - nL - nR

        entry = word[nm_steps[0]] if nm_steps else None
        exit_ = word[nm_steps[-1]] if nm_steps else None
        same = entry == exit_ if nm_steps else None

        big_phase_neighbor_counts[(len(nm_steps), nL, nR, nO, same)] += 1

print("\nAll phases in exceptions (|nm|, tL, tR, other, same_side):")
for key, cnt in sorted(big_phase_neighbor_counts.items(), key=lambda x: -x[1]):
    has_double = key[1] >= 2 or key[2] >= 2
    print(f"  {key}: {cnt} {'[DOUBLE]' if has_double else ''}")

# ===== THE BIG PHASE in exceptions: does it have double same-side? =====
print("\n" + "=" * 70)
print("Big phases in exceptions: double same-side?")
print("=" * 70)

for word, t in exceptions[:5]:
    cycle = build_cycle(ms, n, word)
    ell = len(word)
    tL = (t - 1) % n
    tR = (t + 1) % n

    t_mover_steps = sorted([s for s in range(ell) if word[s] == t])

    biggest_phase = max(range(3), key=lambda i:
        (t_mover_steps[i] - t_mover_steps[(i-1)%3]) % ell)

    sm = t_mover_steps[biggest_phase]
    prev_sm = t_mover_steps[(biggest_phase - 1) % 3]

    nm_steps = []
    s = (prev_sm + 1) % ell
    while s != sm:
        nm_steps.append(s)
        s = (s + 1) % ell

    nL = sum(1 for s in nm_steps if word[s] == tL)
    nR = sum(1 for s in nm_steps if word[s] == tR)
    nO = len(nm_steps) - nL - nR

    print(f"\n  Big phase (phase {biggest_phase}): |nm|={len(nm_steps)}, tL={nL}, tR={nR}, other={nO}")

    ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])
    lr_m = (ctx_m[0], ctx_m[2])
    print(f"  Mover LR={lr_m}")

    # Show step-by-step
    for s in nm_steps:
        lr = (cycle[s][tL], cycle[s][tR])
        mtype = 'tL' if word[s] == tL else ('tR' if word[s] == tR else f'p{word[s]}')
        match = '<- MATCH!' if lr == lr_m else ''
        print(f"    s={s:2d}: LR={lr}, fires={mtype} {match}")

# ===== FINAL CHECK: Same-side MULTI-step -> EC rate =====
print("\n" + "=" * 70)
print("FINAL: Same-side AND multi-step (>= 3 steps) -> EC?")
print("=" * 70)

for n_val, ms_val, max_len_val, label in [
    (5, [2,2,2,3,2], 16, "n=5"),
    (7, [2,2,2,3,2,3,3], 24, "n=7"),
    (7, [2,2,2,3,3,2,3], 24, "n=7b"),
]:
    words = enumerate_mover_words(ms_val, n_val, max_len_val)
    sandwiched_local = [t for t in range(n_val)
                  if ms_val[t] == 3 and ms_val[(t-1)%n_val] == 2 and ms_val[(t+1)%n_val] == 2]

    has_multistep_same = 0
    multistep_same_ec = 0
    no_multistep_same = 0

    for word in words:
        cycle = build_cycle(ms_val, n_val, word)
        if cycle is None or not is_wrap_adjacent(word, n_val):
            continue

        ell = len(word)
        fc = Counter(word)

        for t in sandwiched_local:
            if fc[t] != 3:
                continue

            tL = (t - 1) % n_val
            tR = (t + 1) % n_val

            t_mover_steps = sorted([s for s in range(ell) if word[s] == t])
            if len(t_mover_steps) != 3:
                continue

            found_multistep_same = False
            for i, sm in enumerate(t_mover_steps):
                prev_sm = t_mover_steps[(i - 1) % 3]

                nm_steps = []
                s = (prev_sm + 1) % ell
                while s != sm:
                    nm_steps.append(s)
                    s = (s + 1) % ell

                if len(nm_steps) >= 2:
                    entry = word[nm_steps[0]]
                    exit_ = word[nm_steps[-1]]
                    if entry == exit_:
                        found_multistep_same = True
                        break

            if found_multistep_same:
                has_multistep_same += 1
                if has_ec_at_proc(word, cycle, ms_val, n_val, t):
                    multistep_same_ec += 1
            else:
                no_multistep_same += 1

    total = has_multistep_same + no_multistep_same
    print(f"\n{label}: total fc=3 at sandwiched t: {total}")
    print(f"  Has multi-step same-side phase: {has_multistep_same}")
    if has_multistep_same > 0:
        print(f"    EC at t: {multistep_same_ec} ({100*multistep_same_ec/has_multistep_same:.1f}%)")
    print(f"  No multi-step same-side: {no_multistep_same}")
