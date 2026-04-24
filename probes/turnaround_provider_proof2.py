"""
Turnaround Binary Provider Proof - Part 2
==========================================
Finding: at n=5,6,7 with consecutive binary, ZERO all-turnaround cycles exist.
Let's check: do ANY turnaround binary procs exist? And try non-consecutive placements.
Also: is the all-turnaround case actually IMPOSSIBLE? That would make the theorem vacuously true.
"""

from itertools import permutations, product as iterproduct
from collections import Counter

def neighbors(p, n):
    return [(p - 1) % n, (p + 1) % n]

def enumerate_good_cycles(n, ms):
    """Enumerate good cycles with DFS."""
    total_fires = sum(ms)
    remaining = list(ms)
    results = []

    def dfs(path, remaining):
        if len(path) == total_fires:
            if path[0] in neighbors(path[-1], n):
                results.append(tuple(path))
            return
        last = path[-1]
        for nb in neighbors(last, n):
            if remaining[nb] > 0:
                remaining[nb] -= 1
                path.append(nb)
                dfs(path, remaining)
                path.pop()
                remaining[nb] += 1

    for start in range(n):
        if remaining[start] > 0:
            remaining[start] -= 1
            dfs([start], remaining)
            remaining[start] += 1

    unique = set()
    for cyc in results:
        rotations = [cyc[i:] + cyc[:i] for i in range(len(cyc))]
        canon = min(rotations)
        unique.add(canon)
    return [list(c) for c in unique]


def get_winding_number(mover_word, n):
    net = 0
    L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n:
            net += 1
        elif nxt == (curr - 1) % n:
            net -= 1
    return net // n


def count_cw_steps(mover_word, n):
    cw = 0
    L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]
        nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n:
            cw += 1
    return cw


def get_firing_counts(mover_word, n):
    fc = [0] * n
    for p in mover_word:
        fc[p] += 1
    return fc


def classify_binary_firing(mover_word, b, n):
    """Classify binary proc b's firing pattern."""
    L = len(mover_word)
    fires = [i for i in range(L) if mover_word[i] == b]
    assert len(fires) == 2

    fire_info = []
    for idx in fires:
        prev_mover = mover_word[(idx - 1) % L]
        next_mover = mover_word[(idx + 1) % L]
        left, right = (b - 1) % n, (b + 1) % n
        arr = 'L' if prev_mover == left else ('R' if prev_mover == right else '?')
        dep = 'L' if next_mover == left else ('R' if next_mover == right else '?')
        fire_info.append((arr, dep))

    is_turnaround = all(arr == dep for arr, dep in fire_info)
    return {'fires': fires, 'fire_info': fire_info, 'turnaround': is_turnaround}


def main():
    # Check various n and binary placements
    for n in [5, 6, 7, 8]:
        threshold = 4 * 3**(n-2)

        # Try all possible placements of 3 binary among n procs
        from itertools import combinations
        binary_placements = list(combinations(range(n), 3))

        print(f"\n{'='*60}")
        print(f"n={n}, threshold={threshold}")
        print(f"{'='*60}")

        total_ta_any = 0
        total_all_ta = 0
        total_filtered = 0

        for bp in binary_placements:
            ms = [3] * n
            for b in bp:
                ms[b] = 2

            prod = 1
            for m in ms:
                prod *= m
            if prod >= threshold:
                continue

            cycles = enumerate_good_cycles(n, ms)

            filtered = []
            for cyc in cycles:
                winding = get_winding_number(cyc, n)
                if winding != 0:
                    continue
                cw = count_cw_steps(cyc, n)
                if cw == 0:
                    continue
                fc = get_firing_counts(cyc, n)
                if any(f < 2 for f in fc):
                    continue
                filtered.append(cyc)

            total_filtered += len(filtered)

            # Count turnaround binary procs
            for cyc in filtered:
                ta_count = 0
                for b in bp:
                    info = classify_binary_firing(cyc, b, n)
                    if info['turnaround']:
                        ta_count += 1
                if ta_count > 0:
                    total_ta_any += 1
                if ta_count == len(bp):
                    total_all_ta += 1

                    # Print details of all-turnaround cycles
                    if total_all_ta <= 5:
                        fc = get_firing_counts(cyc, n)
                        print(f"  ALL-TA: bp={bp}, ms={ms}, cycle={cyc}, fc={fc}")
                        for b in bp:
                            info = classify_binary_firing(cyc, b, n)
                            print(f"    Binary {b}: {info['fire_info']}")

        print(f"  Total filtered cycles: {total_filtered}")
        print(f"  Cycles with any turnaround binary: {total_ta_any}")
        print(f"  Cycles with ALL turnaround binary: {total_all_ta}")

    # ============================================================
    # DEEPER: What does "turnaround" mean structurally?
    # ============================================================
    print("\n\n" + "=" * 70)
    print("TURNAROUND STRUCTURAL ANALYSIS")
    print("=" * 70)

    # At n=5: look at individual turnaround binary procs (not all-turnaround)
    n = 5
    for bp in [(0,1,2), (0,1,3), (0,2,4)]:
        ms = [3] * n
        for b in bp:
            ms[b] = 2
        prod = 1
        for m in ms: prod *= m
        threshold = 4 * 3**(n-2)
        if prod >= threshold:
            continue

        cycles = enumerate_good_cycles(n, ms)
        filtered = []
        for cyc in cycles:
            winding = get_winding_number(cyc, n)
            if winding != 0: continue
            cw = count_cw_steps(cyc, n)
            if cw == 0: continue
            fc = get_firing_counts(cyc, n)
            if any(f < 2 for f in fc): continue
            filtered.append(cyc)

        print(f"\nn={n}, bp={bp}, ms={ms}, filtered cycles: {len(filtered)}")

        for cyc in filtered:
            fc = get_firing_counts(cyc, n)
            ta_info = []
            for b in bp:
                info = classify_binary_firing(cyc, b, n)
                ta_info.append((b, info['turnaround'], info['fire_info']))
            ta_procs = [b for b, is_ta, _ in ta_info if is_ta]
            if len(ta_procs) > 0:
                print(f"  Cycle {cyc}, fc={fc}")
                for b, is_ta, fi in ta_info:
                    marker = "TA" if is_ta else "PT"
                    print(f"    Binary {b} [{marker}]: {fi}")


if __name__ == '__main__':
    main()
