#!/usr/bin/env python3
"""RA12: Check when same-side entry/exit fails to give double.

Same-side but no double means: entry and exit fire the same neighbor,
but only 1 firing of that neighbor (the entry step IS the exit step).
This happens when the phase has exactly 2 steps: 1 nm + 1 mover.

The 2320 same-side-but-no-double cases at n=7 should all be 2-step phases.

Also: the 48 cycles with same-side but no EC need analysis.
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

# ===== CHECK: same-side no-double = 2-step phases =====
print("=" * 70)
print("Same-side without double: are these all 2-step phases?")
print("=" * 70)

n = 7
ms = [2, 2, 2, 3, 2, 3, 3]
max_len = 24

words = enumerate_mover_words(ms, n, max_len)
sandwiched = [t for t in range(n)
              if ms[t] == 3 and ms[(t-1)%n] == 2 and ms[(t+1)%n] == 2]

same_side_no_double_by_size = Counter()

for word in words:
    cycle = build_cycle(ms, n, word)
    if cycle is None or not is_wrap_adjacent(word, n):
        continue

    ell = len(word)
    fc = Counter(word)

    for t in sandwiched:
        if fc[t] != 3:
            continue
        tL = (t - 1) % n
        tR = (t + 1) % n

        t_mover_steps = sorted([s for s in range(ell) if word[s] == t])
        if len(t_mover_steps) != 3:
            continue

        for i, sm in enumerate(t_mover_steps):
            prev_sm = t_mover_steps[(i - 1) % 3]

            nm_steps = []
            s = (prev_sm + 1) % ell
            while s != sm:
                nm_steps.append(s)
                s = (s + 1) % ell

            if len(nm_steps) == 0:
                continue

            entry = word[nm_steps[0]]
            exit_ = word[nm_steps[-1]]

            if entry == exit_:  # same-side
                nL = sum(1 for s in nm_steps if word[s] == tL)
                nR = sum(1 for s in nm_steps if word[s] == tR)

                if nL < 2 and nR < 2:  # no double
                    same_side_no_double_by_size[len(nm_steps)] += 1

print(f"Same-side no-double phase sizes:")
for size, cnt in sorted(same_side_no_double_by_size.items()):
    print(f"  {size} nm steps: {cnt}")

# ===== THE 48 EXCEPTIONS: same-side but no EC at t =====
print("\n" + "=" * 70)
print("THE 48 EXCEPTIONS: same-side but no EC at t")
print("=" * 70)

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
        tL = (t - 1) % n
        tR = (t + 1) % n

        t_mover_steps = sorted([s for s in range(ell) if word[s] == t])
        if len(t_mover_steps) != 3:
            continue

        ec = has_ec_at_proc(word, cycle, ms, n, t)
        if ec:
            continue

        # Has same-side?
        found_same = False
        for i, sm in enumerate(t_mover_steps):
            prev_sm = t_mover_steps[(i - 1) % 3]
            entry = word[(prev_sm + 1) % ell]
            exit_ = word[(sm - 1) % ell]
            if entry == exit_:
                found_same = True
                break

        if found_same:
            exceptions.append((word, t))

print(f"Total exceptions: {len(exceptions)}")

for word, t in exceptions[:5]:
    cycle = build_cycle(ms, n, word)
    ell = len(word)
    fc = Counter(word)
    tL = (t - 1) % n
    tR = (t + 1) % n

    t_mover_steps = sorted([s for s in range(ell) if word[s] == t])

    print(f"\n  word_len={ell}, t={t}")
    for i, sm in enumerate(t_mover_steps):
        prev_sm = t_mover_steps[(i - 1) % 3]

        nm_steps = []
        s = (prev_sm + 1) % ell
        while s != sm:
            nm_steps.append(s)
            s = (s + 1) % ell

        entry = word[nm_steps[0]] if nm_steps else '?'
        exit_ = word[nm_steps[-1]] if nm_steps else '?'
        same = 'SAME' if entry == exit_ else 'diff'

        nL = sum(1 for s in nm_steps if word[s] == tL)
        nR = sum(1 for s in nm_steps if word[s] == tR)
        nO = len(nm_steps) - nL - nR

        ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])

        # Non-neighbor nm steps
        nn_steps = [s for s in nm_steps if word[s] not in (tL, tR)]
        nn_lrs = [(cycle[s][tL], cycle[s][tR]) for s in nn_steps]

        print(f"    Phase {i}: |nm|={len(nm_steps)}, entry={entry}, exit={exit_}, {same}")
        print(f"      tL={nL}, tR={nR}, other={nO}")
        print(f"      mover_ctx={ctx_m}, mover_LR={ctx_m[0],ctx_m[2]}")
        print(f"      nn LRs: {nn_lrs}")

    # Where IS ec?
    ep = [p for p in range(n) if has_ec_at_proc(word, cycle, ms, n, p)]
    print(f"    EC procs: {ep}")

# ===== CRUCIAL: Why does same-side with double+nn NOT give EC in 48 cases? =====
print("\n" + "=" * 70)
print("WHY same-side+double fails: L value mismatch?")
print("=" * 70)

for word, t in exceptions[:3]:
    cycle = build_cycle(ms, n, word)
    ell = len(word)
    tL = (t - 1) % n
    tR = (t + 1) % n

    t_mover_steps = sorted([s for s in range(ell) if word[s] == t])

    print(f"\n  word_len={ell}, t={t}")
    for i, sm in enumerate(t_mover_steps):
        prev_sm = t_mover_steps[(i - 1) % 3]

        nm_steps = []
        s = (prev_sm + 1) % ell
        while s != sm:
            nm_steps.append(s)
            s = (s + 1) % ell

        if len(nm_steps) < 2:
            continue

        entry = word[nm_steps[0]]
        exit_ = word[nm_steps[-1]]
        if entry != exit_:
            continue

        # This is a same-side phase
        ctx_m = (cycle[sm][tL], cycle[sm][t], cycle[sm][tR])
        lr_m = (ctx_m[0], ctx_m[2])
        print(f"\n    Phase {i} (same-side, |nm|={len(nm_steps)}):")
        print(f"      Mover LR = {lr_m}")

        # Show ALL nm steps with their LR and types
        for s in nm_steps:
            lr = (cycle[s][tL], cycle[s][tR])
            mtype = 'tL' if word[s] == tL else ('tR' if word[s] == tR else f'p{word[s]}')
            match = 'MATCH' if lr == lr_m else ''
            print(f"      s={s:2d}: LR={lr}, fires={mtype} {match}")
