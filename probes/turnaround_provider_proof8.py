"""
Turnaround Provider Proof - Part 8: Complete proof
===================================================
Strategy:
1. Show at most 1 binary can be same-side turnaround (dead edge argument)
2. Show at most 1 binary can be mixed turnaround (excursion nesting argument)
3. Therefore at most 2 binary can be turnaround → with ≥3 binary,
   at least 1 must be passthrough → original theorem (passthrough → provider) applies.

Actually, we should check: can we have 1 same-side + 1 mixed = 2 turnarounds total?
With ≥3 binary, that still leaves ≥1 passthrough. So we need:
  ALL binary turnaround ⟹ at least 3 turnarounds ⟹ impossible.

So the theorem is: with ≥3 binary, not all can be turnaround.
This means at least 1 is passthrough, and the passthrough → provider theorem applies.

Let me prove: can't have 3 turnarounds (any combination of same-side and mixed).

Case A: ≥2 same-side → dead edge disconnection → impossible.
Case B: exactly 1 same-side, ≥2 mixed → needs proof.
Case C: 0 same-side, ≥3 mixed → needs proof.

For Case B and C, I need the mixed-TA excursion argument.

KEY INSIGHT for mixed TA: the walk at b alternates sides.
Fire 1: arr=L, dep=L. Fire 2: arr=R, dep=R.
Between fire 1 dep and fire 2 arr: walk goes from b-1 (left) to b+1 (right),
traversing the ring the LONG way around (through n-2 procs).
Between fire 2 dep and fire 1 arr: walk goes from b+1 (right) to b-1 (left),
traversing the ring the LONG way around.

Total steps in excursions: L - 2 (everything except the 2 fires of b).
Each excursion traverses the ring minus b (a path of n-1 nodes).
Minimum steps per excursion: n-2 (straight path, no backtracking).
So minimum total: 2(n-2) = 2n-4.
Available: L-2 = 3n-5 (for 3 binary, n-3 ternary).
Slack: 3n-5 - (2n-4) = n-1. This slack is used for extra fires
(ternary procs fire 3 times, not 1).

Now for 2 mixed TAs at b1, b2:
b1 uses 2n-4 minimum steps in its excursions.
b2 uses 2n-4 minimum steps.
But these steps OVERLAP (the excursions are interleaved).

The key: consider the excursions as intervals on the cyclic mover word.
b1's excursions: A1 = [f1+1, f2-1], A2 = [f2+1, f1-1] (cyclically).
b2's excursions: B1 = [g1+1, g2-1], B2 = [g2+1, g1-1].
These 4 intervals partition the mover word (minus the 4 fire positions).

Actually no: b1 has 2 fires, b2 has 2 fires. Together 4 fire positions.
The mover word has L positions. The 4 intervals between these fires
partition the remaining L-4 positions.

But the excursions of b1 (A1, A2) and excursions of b2 (B1, B2) don't align.
A1 might contain g1 or g2 (b2's fires).

Let me think about it as an interval graph on the cyclic mover word.
4 special positions: f1, f2, g1, g2.
These divide the cycle into 4 arcs.
Say (cyclically): f1, ..., g1, ..., f2, ..., g2, ..., f1.
The 4 arcs: [f1+1, g1-1], [g1+1, f2-1], [f2+1, g2-1], [g2+1, f1-1].

A1 = arc(f1, f2) = [f1+1, g1-1] ∪ {g1} ∪ [g1+1, f2-1]
A2 = arc(f2, f1) = [f2+1, g2-1] ∪ {g2} ∪ [g2+1, f1-1]
B1 = arc(g1, g2) = [g1+1, f2-1] ∪ {f2} ∪ [f2+1, g2-1]
B2 = arc(g2, g1) = [g2+1, f1-1] ∪ {f1} ∪ [f1+1, g1-1]

A1 and B1 OVERLAP (they share [g1+1, f2-1] and the other has [f2+1, g2-1]).

Each mixed TA excursion must traverse the ring. The shared intervals must
serve both b1's and b2's traversal requirements.

For the walk to work: in the shared interval [g1+1, f2-1], the walk is
simultaneously in excursion A1 of b1 and excursion B1 of b2.
This interval must contribute to both traversals.

The constraint: the walk during [g1+1, f2-1] must visit procs that advance
both b1's CW excursion AND b2's traversal.

I think the RIGHT approach is to consider the walk as having a "signed position"
at each step, and show that 2 mixed TAs force a contradiction in the step budget.

Let me verify computationally: can 2 mixed TAs coexist at n=9?
"""

import random
random.seed(42)

def random_walk_cycle(n, ms, max_attempts=1000):
    L = sum(ms)
    for _ in range(max_attempts):
        rem = list(ms)
        start = random.randint(0, n-1)
        while rem[start] == 0:
            start = random.randint(0, n-1)
        rem[start] -= 1
        path = [start]
        for step in range(L-1):
            nbrs = [(path[-1]-1)%n, (path[-1]+1)%n]
            valid = [nb for nb in nbrs if rem[nb] > 0]
            if not valid: break
            nxt = random.choice(valid)
            rem[nxt] -= 1
            path.append(nxt)
        if len(path) == L and path[0] in [(path[-1]-1)%n, (path[-1]+1)%n]:
            return path
    return None

def classify(mw, b, n):
    L = len(mw)
    fires = [i for i in range(L) if mw[i] == b]
    if len(fires) != 2: return 'bad', None
    fi = []
    for idx in fires:
        prev = mw[(idx-1)%L]
        nxt = mw[(idx+1)%L]
        a = 'L' if prev == (b-1)%n else 'R'
        d = 'L' if nxt == (b-1)%n else 'R'
        fi.append((a,d))
    ta = all(a==d for a,d in fi)
    if not ta: return 'pt', fi
    sides = [f[0] for f in fi]
    if sides[0] == sides[1]: return f'same_{sides[0]}', fi
    return 'mixed', fi

def main():
    print("="*60)
    print("CAN 2 TURNAROUNDS COEXIST? (any type)")
    print("="*60)

    # n=9, various binary placements
    n = 9
    from itertools import combinations

    for bp in [(0,1,2), (0,3,6), (0,1,4), (0,2,5), (0,4,8)]:
        ms = [3]*n
        for b in bp: ms[b] = 2

        max_ta = 0
        mixed_and_ta = 0

        for trial in range(100000):
            cyc = random_walk_cycle(n, ms)
            if cyc is None: continue

            # Filters
            net = 0; cw = 0
            for i in range(len(cyc)):
                c, nx = cyc[i], cyc[(i+1)%len(cyc)]
                if nx == (c+1)%n: net += 1; cw += 1
                elif nx == (c-1)%n: net -= 1
            if net//n != 0: continue
            if cw == 0: continue
            f = [0]*n
            for p in cyc: f[p] += 1
            if any(x < 2 for x in f): continue

            ta_count = 0
            types = []
            for b in bp:
                t, fi = classify(cyc, b, n)
                types.append(t)
                if t != 'pt' and t != 'bad':
                    ta_count += 1

            if ta_count > max_ta:
                max_ta = ta_count
                print(f"  bp={bp}: {ta_count} TA, types={types}")
                if ta_count >= 2:
                    print(f"    cycle={cyc}")

        print(f"  bp={bp}: max simultaneous TA = {max_ta}")

    # ================================================================
    # Also check: what's the max # turnarounds at n=5,7 (exhaustive)?
    # ================================================================
    print("\n" + "="*60)
    print("EXHAUSTIVE MAX TA COUNT (n=5,7)")
    print("="*60)

    def neighbors(p, n):
        return [(p-1)%n, (p+1)%n]

    def enum_cycles(n, ms, maxc=100000):
        L = sum(ms)
        rem = list(ms)
        results = []
        def dfs(path, rem):
            if len(results) >= maxc: return
            if len(path) == L:
                if path[0] in neighbors(path[-1], n):
                    results.append(tuple(path))
                return
            last = path[-1]
            for nb in neighbors(last, n):
                if rem[nb] > 0:
                    rem[nb] -= 1
                    path.append(nb)
                    dfs(path, rem)
                    path.pop()
                    rem[nb] += 1
        for s in range(n):
            if rem[s] > 0 and len(results) < maxc:
                rem[s] -= 1
                dfs([s], rem)
                rem[s] += 1
        unique = set()
        for c in results:
            rots = [c[i:]+c[:i] for i in range(len(c))]
            unique.add(min(rots))
        return [list(c) for c in unique]

    for n in [5, 7]:
        threshold = 4 * 3**(n-2)
        overall_max = 0

        for bp in combinations(range(n), 3):
            ms = [3]*n
            for b in bp: ms[b] = 2
            prod = 1
            for m in ms: prod *= m
            if prod >= threshold: continue

            cycles = enum_cycles(n, ms, 100000)
            for cyc in cycles:
                net = 0; cw = 0
                for i in range(len(cyc)):
                    c, nx = cyc[i], cyc[(i+1)%len(cyc)]
                    if nx == (c+1)%n: net += 1; cw += 1
                    elif nx == (c-1)%n: net -= 1
                if net//n != 0: continue
                if cw == 0: continue
                f = [0]*n
                for p in cyc: f[p] += 1
                if any(x < 2 for x in f): continue

                ta_count = sum(1 for b in bp if classify(cyc, b, n)[0] != 'pt' and classify(cyc, b, n)[0] != 'bad')
                if ta_count > overall_max:
                    overall_max = ta_count
                    types = [classify(cyc, b, n)[0] for b in bp]
                    print(f"  n={n}, bp={bp}: {ta_count} TA, types={types}, cycle={cyc}")

        print(f"n={n}: overall max TA = {overall_max}")


if __name__ == '__main__':
    main()
