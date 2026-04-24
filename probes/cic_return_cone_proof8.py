#!/usr/bin/env python3
"""
CIC Exploration 11h: Check if Tool 3 kills the survivors.

From proof7.py: 2320 survivors across all configs.
All have 0 singletons and no return cone.
They look like bounce-type words.

Check: does Tool 3 (binary-bounce) kill them?
If not, what does?
"""

from collections import Counter


def is_pure_sweep(word, n):
    L = len(word)
    return (all((word[(i+1)%L]-word[i]) % n == 1 for i in range(L)) or
            all((word[i]-word[(i+1)%L]) % n == 1 for i in range(L)))


def count_singletons(word, n):
    edge_counts = Counter()
    L = len(word)
    for i in range(L):
        a, b = word[i], word[(i+1) % L]
        if abs(a - b) == 1:
            e = (min(a, b), max(a, b))
        else:
            e = (0, n - 1)
        edge_counts[e] += 1
    return sum(1 for c in edge_counts.values() if c == 1)


def check_return_cone(word, n):
    L = len(word)
    proc_pos = {p: set() for p in range(n)}
    for t in range(L):
        proc_pos[word[t]].add(t)
    for start in range(n):
        for length in range(1, n):
            S = set((start + i) % n for i in range(length))
            all_pos = set()
            for p in S:
                all_pos |= proc_pos[p]
            if not all_pos or len(all_pos) == L:
                continue
            sorted_pos = sorted(all_pos)
            max_gap = 0
            for i in range(len(sorted_pos)):
                if i + 1 < len(sorted_pos):
                    gap = sorted_pos[i+1] - sorted_pos[i] - 1
                else:
                    gap = (sorted_pos[0] + L) - sorted_pos[-1] - 1
                max_gap = max(max_gap, gap)
            if max_gap > 0 and max_gap == L - len(all_pos):
                return True
    return False


def check_binary_bounce(word, n, binary_set):
    """
    Tool 3: Find interval [t,u) where:
    - p not mover at t, IS mover at u
    - p frozen in [t,u)
    - neighbor q frozen in [t,u)
    - neighbor b (binary) moves exactly twice in [t,u)
    """
    L = len(word)

    for b in range(n):
        if b not in binary_set:
            continue
        for p in [(b-1) % n, (b+1) % n]:
            if p in binary_set:
                continue
            q = (2*p - b) % n

            p_positions = [i for i in range(L) if word[i] == p]
            if not p_positions:
                continue

            for u_idx in range(len(p_positions)):
                u = p_positions[u_idx]
                prev_p = p_positions[u_idx - 1]

                # Interval (prev_p, u) cyclically: p frozen
                interval = []
                pos = (prev_p + 1) % L
                while pos != u:
                    interval.append(word[pos])
                    pos = (pos + 1) % L

                if not interval:
                    continue

                # Split by q appearances
                q_indices = [i for i, m in enumerate(interval)
                            if m == q]

                # Check sub-intervals ending at the end
                boundaries = [-1] + q_indices + [len(interval)]
                for si in range(len(boundaries) - 1):
                    seg_start = boundaries[si] + 1
                    seg_end = boundaries[si + 1]
                    seg = interval[seg_start:seg_end]
                    b_count = seg.count(b)

                    if b_count == 2 and seg_end == len(interval):
                        return True

                # Also check from the beginning
                for si in range(len(boundaries) - 1):
                    seg_start = boundaries[si] + 1
                    seg_end = boundaries[si + 1]
                    seg = interval[seg_start:seg_end]
                    b_count = seg.count(b)

                    if b_count == 2 and seg_start == 0:
                        # sub-interval from start: t = prev_p+1
                        # p is not mover at t (it's in the interval)
                        # p is mover at... hmm, we need p to fire
                        # at the END of the sub-interval.
                        # This doesn't quite match Tool 3.
                        pass

    # Broader check: any proc p (not just neighbors of binary)
    # with binary neighbor b, other neighbor q
    for p in range(n):
        if p in binary_set:
            continue
        neighbors = [(p-1) % n, (p+1) % n]
        for b in neighbors:
            if b not in binary_set:
                continue
            q = neighbors[0] if neighbors[1] == b else neighbors[1]

            p_positions = [i for i in range(L) if word[i] == p]
            if not p_positions:
                continue

            for u_idx in range(len(p_positions)):
                u = p_positions[u_idx]
                # Scan backward: find largest interval before u
                # where p and q don't appear, and count b appearances
                t = (u - 1) % L
                b_count = 0
                steps = 0
                while steps < L - 1:
                    m = word[t]
                    if m == p or m == q:
                        break
                    if m == b:
                        b_count += 1
                    t = (t - 1) % L
                    steps += 1

                if b_count == 2 and steps < L - 1:
                    return True

                # Also scan forward from u to find interval
                # Actually Tool 3 is about [t,u) where u is
                # when p fires. The scan backward is correct.

    return False


def check_binary_bounce_v3(word, n, binary_set):
    """
    Even more thorough Tool 3 check.

    For ALL pairs (t, u) where:
    - u is a position where some non-binary proc p fires
    - t < u (cyclically)
    - p doesn't fire in (t, u)
    - q (other neighbor of p) doesn't fire in (t, u)
    - b (binary neighbor of p) fires exactly 2 times in (t, u)
    """
    L = len(word)

    for p in range(n):
        if p in binary_set:
            continue
        neighbors = [(p-1) % n, (p+1) % n]
        binary_neighbors = [nb for nb in neighbors
                           if nb in binary_set]
        if not binary_neighbors:
            continue

        for b in binary_neighbors:
            q = neighbors[0] if neighbors[1] == b else neighbors[1]

            p_pos = [i for i in range(L) if word[i] == p]
            if len(p_pos) < 1:
                continue

            for u in p_pos:
                # Scan all possible t values going backward
                b_count = 0
                t = (u - 1) % L
                for step in range(1, L):
                    m = word[t]
                    if m == p:
                        break  # hit another p-move
                    if m == q:
                        # q fires here, reset b_count and continue
                        b_count = 0
                        t = (t - 1) % L
                        continue
                    if m == b:
                        b_count += 1
                    # Check: from this t to u, have we seen
                    # exactly 2 b-moves with no p or q?
                    # We need to track more carefully.
                    t = (t - 1) % L

                # Better: enumerate sub-intervals of
                # the p-free zone before u
                # Between consecutive p-appearances
                prev_p_idx = p_pos.index(u) - 1
                prev_p = p_pos[prev_p_idx]

                # Interval (prev_p, u): p doesn't fire
                interval = []
                pos = (prev_p + 1) % L
                while pos != u:
                    interval.append(word[pos])
                    pos = (pos + 1) % L

                # For each contiguous sub-interval ending at the end
                # with no q, count b
                bc = 0
                for j in range(len(interval)-1, -1, -1):
                    m = interval[j]
                    if m == q:
                        break
                    if m == b:
                        bc += 1

                if bc == 2:
                    return True

    return False


def full_check(n, binary_positions, max_L):
    """Full check with all three tools."""
    binary_set = set(binary_positions)
    k = len(binary_positions)

    total = 0
    kill_sweep = 0
    kill_singleton = 0  # >= 2 singletons
    kill_cone = 0       # return cone (no singletons)
    kill_bounce = 0     # binary bounce (Tool 3)
    survivors = []

    def dfs(word, mc):
        nonlocal total, kill_sweep, kill_singleton
        nonlocal kill_cone, kill_bounce

        L = len(word)
        if L > max_L:
            return
        current = word[-1]
        if L >= 2 * n:
            first = word[0]
            d = abs(current - first)
            if d == 1 or d == n - 1:
                if all(c >= 2 for c in mc):
                    if all(mc[b] % 2 == 0
                           for b in binary_positions):
                        total += 1

                        if is_pure_sweep(word, n):
                            kill_sweep += 1
                            return

                        s = count_singletons(word, n)
                        if s >= 2:
                            kill_singleton += 1
                            return

                        if check_return_cone(word, n):
                            kill_cone += 1
                            return

                        if check_binary_bounce_v3(
                                word, n, binary_set):
                            kill_bounce += 1
                            return

                        survivors.append(list(word))
                        if len(survivors) <= 3:
                            print(f"  SURV: {word} S={s}")

        for np_ in [(current-1)%n, (current+1)%n]:
            mc[np_] += 1
            word.append(np_)
            dfs(word, mc)
            word.pop()
            mc[np_] -= 1

    mc = [0] * n
    mc[0] = 1
    dfs([0], mc)

    ns = total - kill_sweep
    print(f"\nn={n} k={k} bin={binary_positions} maxL={max_L}")
    print(f"  Total: {total}, Sweep: {kill_sweep}")
    print(f"  Non-sweep: {ns}")
    print(f"    >=2 singletons: {kill_singleton}")
    print(f"    Return cone: {kill_cone}")
    print(f"    Binary bounce: {kill_bounce}")
    print(f"    Survivors: {len(survivors)}")

    if survivors:
        for w in survivors[:5]:
            mc_w = Counter(w)
            edge_c = Counter()
            for i in range(len(w)):
                a, b = w[i], w[(i+1)%len(w)]
                e = (min(a,b), max(a,b)) if abs(a-b)==1 else (0,n-1)
                edge_c[e] += 1
            print(f"    {w}")
            print(f"      moves={dict(sorted(mc_w.items()))}")
            print(f"      edges={dict(sorted(edge_c.items()))}")

    return len(survivors)


def main():
    print("CIC Exploration 11h: Full 3-tool classification")
    print("=" * 60)

    total = 0
    total += full_check(6, [0, 2, 4], max_L=20)
    total += full_check(7, [0, 2, 4], max_L=18)
    total += full_check(7, [0, 2, 5], max_L=18)
    total += full_check(8, [0, 2, 5], max_L=18)
    total += full_check(8, [0, 3, 6], max_L=18)
    total += full_check(9, [0, 3, 6], max_L=18)
    total += full_check(8, [0, 2, 4, 6], max_L=18)

    print(f"\n{'='*60}")
    print(f"TOTAL SURVIVORS: {total}")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()
