#!/usr/bin/env python3
"""binscc_pair_transfer.py — Identify the pair transfer mechanism.

KEY QUESTION: When binary b has no mover alias, does its neighbor t ALWAYS
have mover alias? If so, what structural property forces this?

HYPOTHESIS: For non-adjacent binary b with non-binary neighbor t,
at least one of {b, t} always has mover alias ≥ 2. This would prove
universal entry conflict.

Also check: is it always the SANDWICHED ternary that picks up, or can it
be a more distant proc?
"""

import sys
from collections import Counter, defaultdict
import time


def enumerate_mover_words(ms, n, max_length):
    ring_adj = {p: [(p-1) % n, (p+1) % n] for p in range(n)}
    results = []
    start = tuple(0 for _ in range(n))
    def dfs(word, fc, config):
        if len(word) > max_length:
            return
        if len(word) >= 6 and config == start:
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


def has_mover_alias(ms, n, word, cycle, p):
    """Check if proc p has mover alias >= 2."""
    ell = len(cycle)
    mL = (p - 1) % n
    mR = (p + 1) % n
    ctx_to_count = {}
    mover_ctxs = set()
    for step in range(ell):
        c = cycle[step]
        ctx = (c[mL], c[p], c[mR])
        ctx_to_count[ctx] = ctx_to_count.get(ctx, 0) + 1
        if word[step] == p:
            mover_ctxs.add(ctx)
    for ctx in mover_ctxs:
        if ctx_to_count[ctx] >= 2:
            return True
    return False


def get_mover_alias_detail(ms, n, word, cycle, p):
    """Get detailed mover alias info for proc p."""
    ell = len(cycle)
    mL = (p - 1) % n
    mR = (p + 1) % n

    ctx_to_steps = defaultdict(list)
    mover_ctxs = {}  # ctx -> step
    for step in range(ell):
        c = cycle[step]
        ctx = (c[mL], c[p], c[mR])
        ctx_to_steps[ctx].append(step)
        if word[step] == p:
            mover_ctxs[ctx] = step

    aliased = {}
    for ctx, m_step in mover_ctxs.items():
        if len(ctx_to_steps[ctx]) >= 2:
            nm_steps = [s for s in ctx_to_steps[ctx] if s != m_step]
            aliased[ctx] = (m_step, nm_steps)

    return aliased


def main():
    print("=" * 70)
    print("PAIR TRANSFER MECHANISM ANALYSIS")
    print("=" * 70)

    configs = [
        (5, [2, 3, 2, 3, 2], 21),
        (6, [2, 3, 2, 3, 2, 3], 24),
    ]

    for n, ms, max_len in configs:
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms}")
        bin_procs = [i for i in range(n) if ms[i] == 2]
        nonbin_procs = [i for i in range(n) if ms[i] > 2]
        print(f"  Binary: {bin_procs}, Non-binary: {nonbin_procs}")

        t0 = time.time()
        words = enumerate_mover_words(ms, n, max_len)
        t1 = time.time()
        print(f"  {len(words)} words ({t1-t0:.1f}s)")

        total = 0

        # PART 1: For each binary b, when b has no mover alias,
        # which proc picks up?
        print(f"\n  PART 1: NEIGHBOR PICKUP WHEN BINARY FAILS")

        # Track: for each binary b, how often does it fail?
        # When it fails, which procs have mover alias?
        b_fail_count = {b: 0 for b in bin_procs}
        b_neighbor_pickup = {b: Counter() for b in bin_procs}
        # Does a direct neighbor ALWAYS pick up?
        b_neighbor_always = {b: True for b in bin_procs}

        # PART 2: Pair test — does {b, neighbor} always cover?
        pair_fail = Counter()  # (b, t) -> count of pair failures
        pair_total = Counter()

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1

            # Compute mover alias for each proc
            proc_has_alias = {}
            for p in range(n):
                proc_has_alias[p] = has_mover_alias(ms, n, word, cycle, p)

            for b in bin_procs:
                if not proc_has_alias[b]:
                    b_fail_count[b] += 1
                    # Which procs pick up?
                    for p in range(n):
                        if p != b and proc_has_alias[p]:
                            b_neighbor_pickup[b][p] += 1
                    # Direct neighbors?
                    nL = (b - 1) % n
                    nR = (b + 1) % n
                    if not proc_has_alias[nL] and not proc_has_alias[nR]:
                        b_neighbor_always[b] = False

                # Pair test
                for t in [(b - 1) % n, (b + 1) % n]:
                    if ms[t] > 2:  # non-binary neighbor
                        pair = (min(b, t), max(b, t))
                        pair_total[pair] += 1
                        if not proc_has_alias[b] and not proc_has_alias[t]:
                            pair_fail[pair] += 1

        elapsed = time.time() - t0
        print(f"  Total valid: {total} ({elapsed:.1f}s)")

        for b in bin_procs:
            fails = b_fail_count[b]
            print(f"\n  P{b} (binary) fails: {fails}/{total} "
                  f"({100*fails/total:.1f}%)")
            if fails > 0:
                print(f"    Neighbor pickup:")
                for p in range(n):
                    cnt = b_neighbor_pickup[b].get(p, 0)
                    if cnt > 0:
                        rel = "neighbor" if abs(p - b) % n <= 1 or \
                            abs(p - b) % n >= n - 1 else "distant"
                        print(f"      P{p} (m={ms[p]}, {rel}): "
                              f"{cnt}/{fails} ({100*cnt/fails:.1f}%)")
                print(f"    Direct neighbor ALWAYS picks up: "
                      f"{b_neighbor_always[b]}")

        print(f"\n  PAIR {'{b, neighbor}'} COVERAGE:")
        for pair, cnt in sorted(pair_total.items()):
            fails = pair_fail.get(pair, 0)
            print(f"    P{pair[0]}–P{pair[1]}: "
                  f"fails={fails}/{cnt} ({100*fails/cnt:.1f}%)")

        # PART 3: For pair failures (if any), what's the mechanism?
        any_pair_fail = any(v > 0 for v in pair_fail.values())
        if any_pair_fail:
            print(f"\n  PART 3: PAIR FAILURE ANALYSIS")
            count = 0
            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                for b in bin_procs:
                    for t in [(b - 1) % n, (b + 1) % n]:
                        if ms[t] <= 2:
                            continue
                        if not has_mover_alias(ms, n, word, cycle, b) and \
                           not has_mover_alias(ms, n, word, cycle, t):
                            print(f"    word={word[:15]}... ℓ={len(word)}")
                            print(f"      P{b} (binary) + P{t} (m={ms[t]})"
                                  f" BOTH fail")
                            # Which proc saves?
                            for p in range(n):
                                if has_mover_alias(ms, n, word, cycle, p):
                                    detail = get_mover_alias_detail(
                                        ms, n, word, cycle, p)
                                    print(f"      Saved by P{p} (m={ms[p]}): "
                                          f"{len(detail)} aliased ctx")
                            count += 1
                            if count >= 10:
                                break
                    if count >= 10:
                        break
                if count >= 10:
                    break
        else:
            print(f"\n  ★ ALL pairs {'{b, neighbor}'} cover! "
                  f"Zero pair failures.")

        # PART 4: TRIPLE test: {b, left_neighbor, right_neighbor}
        print(f"\n  PART 4: TRIPLE COVERAGE")
        triple_fail = 0
        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            for b in bin_procs:
                nL = (b - 1) % n
                nR = (b + 1) % n
                if not has_mover_alias(ms, n, word, cycle, b) and \
                   not has_mover_alias(ms, n, word, cycle, nL) and \
                   not has_mover_alias(ms, n, word, cycle, nR):
                    triple_fail += 1
        print(f"  Triple {'{b, nL, nR}'} failures: {triple_fail}")

        # PART 5: Binary phase analysis — when b has no mover alias,
        # characterize the phase structure
        if n == 5 and b_fail_count[0] > 0:
            print(f"\n  PART 5: PHASE STRUCTURE AT P0 (when no mover alias)")
            count = 0
            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                if has_mover_alias(ms, n, word, cycle, 0):
                    continue
                ell = len(cycle)
                # Find UP and DOWN steps for P0
                p0_steps = [s for s in range(ell) if word[s] == 0]
                up_step = None
                down_step = None
                for s in p0_steps:
                    if cycle[s][0] == 0:
                        up_step = s
                    else:
                        down_step = s

                if up_step is None or down_step is None:
                    continue

                # UP phase: steps with c[0]=1 (from up_step+1 to down_step)
                # DOWN phase: steps with c[0]=0 (from down_step+1 to up_step)
                up_phase = []
                down_phase = []
                for s in range(ell):
                    if s == up_step or s == down_step:
                        continue
                    if cycle[s][0] == 1:
                        up_phase.append(s)
                    else:
                        down_phase.append(s)

                # Context at P0's UP: (c[4], 0, c[1])
                up_ctx = (cycle[up_step][4], 0, cycle[up_step][1])
                down_ctx = (cycle[down_step][4], 1, cycle[down_step][1])

                # How many firings of each neighbor in each phase?
                up_n4 = sum(1 for s in up_phase if word[s] == 4)
                up_n1 = sum(1 for s in up_phase if word[s] == 1)
                down_n4 = sum(1 for s in down_phase if word[s] == 4)
                down_n1 = sum(1 for s in down_phase if word[s] == 1)

                if count < 5:
                    print(f"    ℓ={ell} UP@{up_step} DOWN@{down_step}")
                    print(f"      UP ctx={up_ctx} DOWN ctx={down_ctx}")
                    print(f"      UP phase: {len(up_phase)} steps, "
                          f"P4 fires {up_n4}x, P1 fires {up_n1}x")
                    print(f"      DOWN phase: {len(down_phase)} steps, "
                          f"P4 fires {down_n4}x, P1 fires {down_n1}x")
                    # (c[4], c[1]) values during DOWN phase
                    down_pairs = [(cycle[s][4], cycle[s][1])
                                  for s in down_phase]
                    print(f"      DOWN (c4,c1): {down_pairs[:8]}")
                    print(f"      UP target (c4,c1)=({up_ctx[0]},{up_ctx[2]})"
                          f" in DOWN: "
                          f"{(up_ctx[0], up_ctx[2]) in down_pairs}")
                count += 1

        sys.stdout.flush()


if __name__ == "__main__":
    main()
