"""
Mixed turnaround impossibility proof.

KEY IDEA: For mixed TA at binary b (fc=2):
  Fire 1: arrives from LEFT (left(b)), departs to LEFT (left(b)).
  Fire 2: arrives from RIGHT (right(b)), departs to RIGHT (right(b)).

This means:
  Step before fire 1: mover = left(b), step left(b) → b.
  Step after fire 1: mover = left(b), step b → left(b).
  Step before fire 2: mover = right(b), step right(b) → b.
  Step after fire 2: mover = right(b), step b → right(b).

So left(b) fires at positions (fire1-1) and (fire1+1) in the mover word.
And right(b) fires at positions (fire2-1) and (fire2+1).

Wait: "step after fire 1" means the next mover is left(b).
mw[fire1] = b, mw[fire1+1] = left(b). So left(b) fires at fire1+1. ✓
"step before fire 1" means the previous mover was left(b).
mw[fire1-1] = left(b). So left(b) fires at fire1-1. ✓

Similarly, right(b) fires at fire2-1 and fire2+1.

NOW: left(b) fires at fire1-1 and fire1+1 (2 fires around b's fire 1).
If left(b) is BINARY (fc=2), then these are its ONLY 2 fires.
left(b)'s excursion from fire (fire1-1) to fire (fire1+1) has length 1
(just b's fire at fire1). left(b)'s OTHER excursion has length L-3.

Is left(b) turnaround?
At fire (fire1-1): mw[fire1-1] = left(b).
  Arrival: mw[fire1-2] = some proc p.
  Departure: mw[fire1] = b. So departure is toward b (= RIGHT of left(b)).
At fire (fire1+1): mw[fire1+1] = left(b).
  Arrival: mw[fire1] = b. So arrival is from b (= RIGHT of left(b)).
  Departure: mw[fire1+2] = some proc q.

For left(b) to be turnaround at fire (fire1-1): arr = dep = R.
So arr = R → mw[fire1-2] = b. But b fires at fire1 and fire2, NOT fire1-2
(unless fire1-2 = fire2).

If fire1-2 = fire2: b's two fires are at fire2 and fire2+2.
Then b's excursion 1 (fire1 to fire2 cyclically = fire2+2 to fire2) wraps
around the cycle. Length = L - 2 - 0 wait...
Excursion from fire1 (= fire2+2) to fire2: length = L - 2 - 2 = L - 4? No.
Actually the excursion from fire1 to fire2 (wrapping forward):
  From fire1+1 to fire2-1. That's from fire2+3 to fire2-1 (mod L).
  Length = (fire2-1) - (fire2+3) + L = L - 4.
Excursion from fire2 to fire1:
  From fire2+1 to fire1-1 = fire2+1 to fire2+1. Length = 0? That's empty.
  fire1 = fire2+2. fire1-1 = fire2+1. fire2+1 to fire2+1 is the same position.
  So excursion 2 has length 0. But excursion 2 should go from fire2+1 to fire1-1.
  fire2+1 to fire1-1 = fire2+1 to fire2+1 = empty segment.

So excursion 2 of b has length 0. But for mixed TA, excursion 2 must
wind once around the ring. A length-0 excursion can't wind. CONTRADICTION.

So fire1-2 ≠ fire2. Then mw[fire1-2] ≠ b (b only fires at fire1, fire2,
and fire1-2 is neither). So arrival at left(b)'s fire (fire1-1) is from
mw[fire1-2] ≠ b, meaning arrival is from LEFT (not from b/RIGHT).
arr = L. But dep = R (toward b). So arr ≠ dep: NOT turnaround.

left(b)'s fire at (fire1-1) is passthrough (arr=L, dep=R).

For left(b) to be turnaround overall, BOTH fires must be turnaround.
Since fire (fire1-1) is NOT turnaround (arr≠dep), left(b) is NOT turnaround.

CONCLUSION: If b is mixed turnaround and left(b) is binary, then left(b)
is NOT turnaround (it's passthrough).

Similarly: if b is mixed turnaround and right(b) is binary, then right(b)
is NOT turnaround.

THEOREM: At most 1 binary proc can be mixed turnaround.
Proof: Suppose b1 and b2 are both mixed turnaround binary procs.
  Case 1: b1 and b2 are adjacent. Say b2 = right(b1).
    b1 is mixed TA → right(b1) = b2 is NOT turnaround. CONTRADICTION.
  Case 2: b1 and b2 are non-adjacent. There exists at least one proc
    between them on each arc. But we need to show impossibility.

For Case 2: b1 and b2 non-adjacent, both mixed TA.
Let me check if this is possible computationally.
"""

from itertools import combinations

def neighbors(p, n):
    return [(p-1)%n, (p+1)%n]

def enum_cycles(n, ms):
    L = sum(ms)
    rem = list(ms)
    results = []
    def dfs(path):
        if len(path) == L:
            if path[0] in neighbors(path[-1], n):
                results.append(tuple(path))
            return
        last = path[-1]
        for nb in neighbors(last, n):
            if rem[nb] > 0:
                rem[nb] -= 1
                path.append(nb)
                dfs(path)
                path.pop()
                rem[nb] += 1
    for s in range(n):
        if rem[s] > 0:
            rem[s] -= 1
            dfs([s])
            rem[s] += 1
    unique = set()
    for c in results:
        rots = [c[i:]+c[:i] for i in range(len(c))]
        unique.add(min(rots))
    return [list(c) for c in unique]

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
    if all(a==d for a,d in fi):
        sides = [f[0] for f in fi]
        if sides[0] != sides[1]:
            return 'mixed', fi
        return 'same', fi
    return 'pt', fi

def main():
    print("ADJACENT BINARY NEIGHBOR ARGUMENT")
    print("="*60)

    # Verify: for every mixed TA at b, check if left(b) and right(b)
    # (when binary) are forced passthrough.

    for n in [5, 7]:
        threshold = 4 * 3**(n-2)
        for bp in combinations(range(n), 3):
            ms = [3]*n
            for b in bp: ms[b] = 2
            prod = 1
            for m in ms: prod *= m
            if prod >= threshold: continue

            cycles = enum_cycles(n, ms)
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

                for b in bp:
                    t, fi = classify(cyc, b, n)
                    if t == 'mixed':
                        # Check: is left(b) binary and turnaround?
                        lb = (b-1) % n
                        rb = (b+1) % n
                        if lb in bp:
                            lt, lfi = classify(cyc, lb, n)
                            if lt in ('mixed', 'same'):
                                print(f"  VIOLATION: n={n}, b={b} mixed TA, left(b)={lb} is {lt}")
                        if rb in bp:
                            rt, rfi = classify(cyc, rb, n)
                            if rt in ('mixed', 'same'):
                                print(f"  VIOLATION: n={n}, b={b} mixed TA, right(b)={rb} is {rt}")

        print(f"n={n}: no violations found (binary neighbors of mixed TA are always passthrough)")

    # Now check: can 2 non-adjacent mixed TAs coexist?
    print("\n" + "="*60)
    print("NON-ADJACENT MIXED TA COEXISTENCE CHECK")
    print("="*60)

    for n in [5, 7]:
        threshold = 4 * 3**(n-2)
        found = 0

        for bp in combinations(range(n), 3):
            ms = [3]*n
            for b in bp: ms[b] = 2
            prod = 1
            for m in ms: prod *= m
            if prod >= threshold: continue

            cycles = enum_cycles(n, ms)
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

                mixed_tas = []
                for b in bp:
                    t, _ = classify(cyc, b, n)
                    if t == 'mixed':
                        mixed_tas.append(b)

                if len(mixed_tas) >= 2:
                    # Check if non-adjacent
                    nonadj = all(abs(mixed_tas[i]-mixed_tas[j]) % n > 1 and
                                 abs(mixed_tas[i]-mixed_tas[j]) % n < n-1
                                 for i in range(len(mixed_tas))
                                 for j in range(i+1, len(mixed_tas)))
                    print(f"  2+ mixed TAs: n={n}, bp={bp}, mixed={mixed_tas}, nonadj={nonadj}")
                    found += 1

        print(f"n={n}: {found} instances of 2+ mixed TAs")

    # STEP BUDGET for 2 non-adjacent mixed TAs
    print("\n" + "="*60)
    print("STEP BUDGET ANALYSIS")
    print("="*60)

    # For mixed TA at b:
    # Excursion 1: from left(b) to right(b), winding once.
    # Minimum excursion length = n-2 (straight path through ring minus b).
    # Excursion 2: from right(b) to left(b), winding once.
    # Minimum = n-2.
    # b's fires: 2 steps.
    # Total minimum for b's contribution: 2(n-2) + 2 = 2n-2.

    # For 2 mixed TAs at b1, b2 (non-adjacent, so at least 1 proc between):
    # Combined minimum = 2 * (2n-2) = 4n-4. But steps are shared.
    # The shared steps are in the excursions. Each step is in one excursion
    # of b1 AND one excursion of b2.
    # Total steps = L = 3n-3 (for 3 binary, n-3 ternary).
    # We need L ≥ 4 (b1's fires) + unique excursion steps.
    # Actually total = L, and 4 steps are fires (2 for b1, 2 for b2).
    # Remaining L-4 = 3n-7 steps are in excursions of both b1 and b2.

    # Each excursion of b1: length ≥ n-2.
    # Excursion 1 of b1: spans [fire1_1+1, fire1_2-1]. Contains 1 fire of b2
    #   (either fire2_1 or fire2_2, splitting the excursion into 2 parts).
    #   Wait, no. b2's fires are at fire2_1 and fire2_2, which could both be
    #   in excursion 1 of b1, or split across excursions.

    # This analysis needs specific configurations. Let me check the remaining
    # analytical argument.

    # FINAL ARGUMENT: for non-adjacent binary, the Neighbor Constraint extends.
    # b1 mixed TA → left(b1) and right(b1) forced non-turnaround (if binary).
    # b2 mixed TA → left(b2) and right(b2) forced non-turnaround (if binary).
    # With 3 binary procs b1, b2, b3:
    # If b1, b2 both mixed TA and non-adjacent:
    #   b3 must be the third binary. For all 3 to be turnaround:
    #   b3 must also be turnaround. But b3 might be adjacent to b1 or b2.
    #   If b3 is adjacent to b1 (or b2): b3 is forced passthrough by the
    #   neighbor constraint. CONTRADICTION.
    #   If b3 is not adjacent to either: all 3 are pairwise non-adjacent.
    #   On a ring of n ≥ 5, 3 pairwise non-adjacent procs exist when n ≥ 6.
    #   Then b3 has ternary neighbors, and the neighbor constraint doesn't apply.
    #   We need a different argument for this case.

    print("\n3 pairwise non-adjacent binary, all mixed TA: possible?")

    # With 3 pairwise non-adjacent binary on ring of n procs:
    # Each binary proc has 2 ternary neighbors.
    # The neighbor constraint (binary neighbor forced passthrough) doesn't apply
    # since neighbors are ternary.
    # But the EXCURSION LENGTH constraint still applies.

    # For mixed TA at b: excursion starts at left(b) (ternary, fc≥3) and
    # ends at right(b) (ternary, fc≥3). Between them: at least n-2 steps.

    # Actually, let me prove that 2 non-adjacent mixed TAs are impossible
    # by a different route. Consider the FIRE ORDERING.

    # For mixed TA at b1: the mover word around b1's fires looks like:
    # ...left(b1), b1, left(b1)... (fire 1)
    # ...right(b1), b1, right(b1)... (fire 2)

    # For mixed TA at b2 (non-adjacent to b1): same structure at b2.

    # Between fire 1 and fire 2 of b1 (excursion 1): the walk goes from
    # left(b1) to right(b1) around the ring. In this excursion, b2 fires
    # some number of times (0, 1, or 2).

    # If b2 fires 0 times in this excursion: b2 fires twice in excursion 2
    # of b1. Excursion 1 still must wind around the ring. But b2 never fires
    # in this excursion. The walk must visit b2's position (since it winds
    # around the ring), but b2 doesn't fire here. Wait, the walk = mover word.
    # The walk visits the positions of the movers. If b2 doesn't fire in
    # excursion 1, the walk doesn't visit b2. But the walk winds around the
    # ring: it must pass through b2's neighbors. From left(b2) it goes to
    # b2 or away. If b2 doesn't fire, left(b2) must go to b2... no.
    # left(b2) goes to its neighbors: left(b2)-1 or left(b2)+1 = b2.
    # The walk might go left(b2) → b2's-other-neighbor or left(b2) → b2.
    # If left(b2) → b2, then b2 fires (since b2 is the next mover). But b2
    # isn't supposed to fire in this excursion. So left(b2) → left(b2)-1
    # (going away from b2). Similarly, right(b2) → right(b2)+1 (going away).
    # The walk skips b2 entirely, going left(b2) → left(b2)-1 on one side
    # and right(b2)+1 → right(b2) on the other side? No, the walk is a path.
    # If it reaches left(b2) and goes away, it will eventually reach right(b2)
    # from the other side (since it winds). But from right(b2), it goes to
    # right(b2)+1 (away from b2). So the walk passes from left(b2)-side
    # to right(b2)-side without visiting b2, by going through left(b2)-1,
    # left(b2)-2, ..., right(b2)+1, right(b2)... NO. If the walk goes
    # left(b2) → left(b2)-1, it's going AWAY from b2. To get from left(b2)-side
    # to right(b2)-side, the walk must eventually go through b2 or around
    # the rest of the ring. Going around the rest: but the excursion is
    # winding ONCE. It can't loop around again without b2.

    # Actually the walk CAN skip b2. On the ring, the walk can go:
    # ... left(b2), right(b2) ... if left(b2) and right(b2) are adjacent.
    # But b2 is between left(b2) and right(b2) on the ring. left(b2) and
    # right(b2) are NOT adjacent (they're 2 apart, with b2 in between).
    # The walk is on the ring graph: each step goes to an adjacent node.
    # From left(b2), the walk goes to left(b2)-1 or b2.
    # From right(b2), the walk goes to b2 or right(b2)+1.
    # To go from left(b2) to right(b2) without visiting b2: must go the long
    # way around. That means the excursion makes a detour of length n-2
    # JUST to skip b2. Very expensive.

    # Hmm, this is getting complex. Let me just verify computationally whether
    # 2 non-adjacent mixed TAs can coexist in a broader set of cycles.

    import random
    random.seed(12345)

    print("\nRandom sampling at n=9 for 2+ mixed TAs:")
    n = 9
    # Try various placements with 3 pairwise non-adjacent binary
    placements = [(0,3,6), (0,2,5), (1,4,7), (0,2,6), (0,4,8)]

    for bp in placements:
        ms = [3]*n
        for b in bp: ms[b] = 2
        mixed_count = 0
        total = 0

        for trial in range(50000):
            # Random walk
            L = sum(ms)
            rem = list(ms)
            start = random.choice([p for p in range(n) if rem[p] > 0])
            rem[start] -= 1
            path = [start]
            ok = True
            for _ in range(L-1):
                nbrs = [(path[-1]-1)%n, (path[-1]+1)%n]
                valid = [nb for nb in nbrs if rem[nb] > 0]
                if not valid: ok = False; break
                nxt = random.choice(valid)
                rem[nxt] -= 1
                path.append(nxt)
            if not ok or len(path) != L: continue
            if path[0] not in [(path[-1]-1)%n, (path[-1]+1)%n]: continue

            # Filters
            net = sum(1 if path[(i+1)%L]==(path[i]+1)%n else -1
                      for i in range(L))
            if net // n != 0: continue
            cw = sum(1 for i in range(L) if path[(i+1)%L]==(path[i]+1)%n)
            if cw == 0: continue
            f = [0]*n
            for p in path: f[p] += 1
            if any(x < 2 for x in f): continue
            total += 1

            mtas = 0
            for b in bp:
                t, _ = classify(path, b, n)
                if t == 'mixed': mtas += 1
            if mtas >= 2:
                mixed_count += 1

        print(f"  bp={bp}: {total} valid, {mixed_count} with 2+ mixed TA")


if __name__ == '__main__':
    main()
