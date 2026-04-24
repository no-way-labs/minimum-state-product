#!/usr/bin/env python3
"""binscc_return_universal.py — Does return-conflict cover ALL cycles?

Return theorem: If proc p completes its m_p firings and returns to start state,
AND both neighbors also return to their starting values, then p sees its
first-firing context as nonmover → conflict.

Check: does the return mechanism at ANY proc cover 100% of cycles?
"""

from collections import Counter, defaultdict
import sys
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
        needed = sum(max(0, ms[p] - fc[p]) for p in range(n) if fc[p] == 0 or fc[p] % ms[p] != 0)
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


def check_return_conflict(ms, n, word, cycle):
    """For each proc p, check if it returns to start context after completing firings."""
    ell = len(cycle)
    for p in range(n):
        mL = (p-1) % n; mR = (p+1) % n
        m_p = ms[p]

        # Find all firing steps for p
        p_steps = [s for s in range(ell) if word[s] == p]
        if len(p_steps) < m_p:
            continue

        # Check each round of m_p firings
        for round_start_idx in range(0, len(p_steps), m_p):
            if round_start_idx + m_p > len(p_steps):
                break

            first_step = p_steps[round_start_idx]
            last_step = p_steps[round_start_idx + m_p - 1]

            # Context at first firing
            c_first = cycle[first_step]
            first_ctx = (c_first[mL], c_first[p], c_first[mR])

            # After last firing, p returns to same state (mod m_p)
            # Check all subsequent nonmover steps until next firing of p
            if round_start_idx + m_p < len(p_steps):
                next_p = p_steps[round_start_idx + m_p]
            else:
                next_p = p_steps[0]  # wrap

            step = (last_step + 1) % ell
            while step != next_p:
                if word[step] != p:
                    c = cycle[step]
                    ctx = (c[mL], c[p], c[mR])
                    if ctx == first_ctx:
                        return True  # conflict!
                step = (step + 1) % ell

    return False


def check_adjacent_return(ms, n, word, cycle):
    """Weaker: does p see ANY mover context as nonmover?
    (This is just entry conflict, for reference.)"""
    ell = len(cycle)
    for p in range(n):
        mL = (p-1) % n; mR = (p+1) % n
        mover_set = set()
        nonmover_set = set()
        for step in range(ell):
            c = cycle[step]
            ctx = (c[mL], c[p], c[mR])
            if word[step] == p:
                mover_set.add(ctx)
            else:
                nonmover_set.add(ctx)
        if mover_set & nonmover_set:
            return True
    return False


def main():
    print("=" * 70)
    print("UNIVERSAL RETURN CONFLICT TEST")
    print("=" * 70)

    configs = [
        (5, [2, 3, 2, 3, 2], 21),
        (6, [2, 3, 2, 3, 2, 3], 24),
        (5, [2, 4, 2, 3, 2], 21),
        (7, [2, 3, 2, 3, 2, 3, 3], 27),
    ]

    for n, ms, max_len in configs:
        print(f"\n{'='*60}")
        print(f"n={n} ms={ms}")
        t0 = time.time()
        words = enumerate_mover_words(ms, n, max_len)
        t1 = time.time()
        print(f"  {len(words)} words ({t1-t0:.1f}s)")

        total = 0
        return_conflict = 0
        entry_conflict = 0
        return_no = 0  # no return conflict but has entry conflict
        nothing = 0     # no conflict at all

        for word in words:
            cycle = build_cycle(ms, n, word)
            if cycle is None:
                continue
            total += 1

            rc = check_return_conflict(ms, n, word, cycle)
            ec = check_adjacent_return(ms, n, word, cycle)

            if rc:
                return_conflict += 1
            if ec:
                entry_conflict += 1
            if ec and not rc:
                return_no += 1
            if not ec:
                nothing += 1

        elapsed = time.time() - t0
        print(f"  Total valid: {total} ({elapsed:.1f}s)")
        print(f"  Return conflict: {return_conflict}/{total} ({100*return_conflict/total:.1f}%)")
        print(f"  Entry conflict:  {entry_conflict}/{total} ({100*entry_conflict/total:.1f}%)")
        print(f"  Entry but NOT return: {return_no}/{total} ({100*return_no/total:.1f}%)")
        print(f"  No conflict: {nothing}/{total}")

        if return_no > 0 and return_no <= 20:
            print(f"\n  Entry-only (non-return) examples:")
            count = 0
            for word in words:
                cycle = build_cycle(ms, n, word)
                if cycle is None:
                    continue
                rc = check_return_conflict(ms, n, word, cycle)
                ec = check_adjacent_return(ms, n, word, cycle)
                if ec and not rc:
                    ell = len(cycle)
                    # Find where conflict is
                    for p in range(n):
                        mL = (p-1) % n; mR = (p+1) % n
                        ms_set = set(); nms_set = set()
                        for step in range(ell):
                            c = cycle[step]
                            ctx = (c[mL], c[p], c[mR])
                            if word[step] == p: ms_set.add(ctx)
                            else: nms_set.add(ctx)
                        ov = ms_set & nms_set
                        if ov:
                            print(f"    word={word[:15]}... ℓ={ell} conflict@P{p}: {sorted(ov)[:3]}")
                            break
                    count += 1
                    if count >= 5:
                        break

        sys.stdout.flush()


if __name__ == "__main__":
    main()
