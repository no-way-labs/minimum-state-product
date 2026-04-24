"""
PROOF OF ONE-SIDED EXCURSION EXISTENCE

Theorem: In a closed walk on Z_n (n >= 5) with:
  (H1) Zero winding (net displacement = 0)
  (H2) cw > 0 (at least one CW step)
  (H3) fc(p) >= 2 for all p (every position visited >= 2 times)
  (H4) >= 3 binary procs (non-consecutive on ring)

At least one binary proc has a one-sided excursion.

PROOF:

Consider the binary procs b_1, b_2, ..., b_B (B >= 3) arranged on the ring
(say CW order). Since they're non-consecutive, between each consecutive pair
there's at least one ternary proc.

Each binary b has fc(b) >= 2, so it has at least 2 firing steps. Between
consecutive firings of b, the walk makes an excursion. The excursion is a
sub-walk that starts at b, visits some procs, and returns to b.

For binary b, let's classify each excursion as CW, CCW, or BOTH:
  CW: all procs visited are CW of b (between b and the next binary CW)
  CCW: all procs visited are CCW of b
  BOTH: procs from both sides are visited

Suppose for contradiction that EVERY binary proc has ONLY BOTH-sided excursions.

Each BOTH-sided excursion from b visits at least one proc CW of b AND at least
one proc CCW of b. Since b's CW neighbor and CCW neighbor are ternary (non-
consecutive), the excursion visits both ternary neighbors of b.

Now consider what happens at the BOUNDARIES of the excursion. The walk starts
at b, goes to some adjacent position (CW or CCW), eventually visits both sides,
and returns to b. The walk enters by moving to word[s1+1] = b +/- 1 and exits
by arriving at word[s2-1] = b +/- 1.

For a BOTH-sided excursion, the walk must cross b from one side to the other
at some point during the excursion. But b doesn't fire during the excursion!
So the walk doesn't visit b during the excursion. But to go from CW side to
CCW side, the walk MUST pass through b (on a ring, the path from CW side to
CCW side either goes through b or goes all the way around the ring the other
way, which means visiting ALL procs on the other side too).

Wait. On a ring, CW side = {b+1, b+2, ..., b+(n-1)/2} roughly, and CCW side
is the other half. But the walk can go from CW side to CCW side by going
all the way around WITHOUT passing through b. This requires visiting all
n-1 other procs.

Hmm. Actually, on the ring Z_n, the walk moves by +1 or -1 at each step
(or stays). To go from b+1 to b-1 without visiting b, the walk must go
b+1 -> b+2 -> ... -> b-1, traversing the entire ring the long way.

So a BOTH-sided excursion from b, if it doesn't visit b (which it can't,
since b doesn't fire during the excursion), must traverse the ENTIRE ring
minus b to get from one side to the other. This means the excursion visits
ALL n-1 other procs.

FACT: A both-sided excursion from b visits all n-1 other procs.

Now, with B >= 3 binary procs and each having ONLY both-sided excursions,
each excursion visits ALL other procs. This means:

In the excursion from b_1 between its firings at s1 and s2:
  The walk visits b_2 and b_3 (and all ternary procs).
  b_2 fires at least once during this excursion.
  b_3 fires at least once during this excursion.

The total cycle length L = sum fc(p). Each both-sided excursion of b_1 has
length at least 2*(n-1) (go around one way, come back). Actually, the
excursion visits n-1 procs, each at least once, so length >= n-1. But
to visit both sides without passing through b, length >= 2*(n/2-1)+1
approximately. The minimum length to visit all n-1 procs on a ring from b
without crossing b is n-1 (go one direction all the way).

But the net displacement of the excursion is 0 (starts and ends at b).
So the walk goes CW for some steps, then CCW for some steps (or vice versa).
The minimum excursion length to visit all n-1 procs with net displacement 0
is 2*(n-1) (go CW n-1 steps to reach b again, but that crosses b -- WRONG).

Actually, on the ring, from b you go CW. After n-1 CW steps you reach b-1
(= b + (n-1) mod n = b - 1 mod n). Then you need to go 1 more CW step to
reach b, but b doesn't fire during the excursion. Hmm, the walk REACHES b
when it fires at s2, which IS a firing of b.

Wait. Let me re-think. The excursion from b between firings s1 and s2 is:
  Step s1: fire b. Walk at position b.
  Step s1+1: fire word[s1+1] (some neighbor of b).
  ...
  Step s2-1: fire word[s2-1] (some neighbor of b).
  Step s2: fire b. Walk returns to position b.

The positions visited in the excursion are word[s1+1], ..., word[s2-1].
None of these is b (since b doesn't fire between s1 and s2).

For this excursion to visit both sides of b on the ring:
  It must visit some proc on the CW side AND some proc on the CCW side.
  To get from CW side to CCW side, the walk must go the long way around
  (since b is not visited during the excursion).

The minimum path from CW side to CCW side (avoiding b) has length n-2:
  CW neighbor of b -> CW+1 -> ... -> CCW neighbor of b (n-2 steps CW).
  OR the reverse direction (n-2 steps CCW).

But the walk also needs to return to b at the end, and it entered from
one side. So a both-sided excursion has length >= (n-2) + 2 = n (roughly).

The EXACT minimum: The walk exits b going CW (step s1+1 = b+1), traverses
CW all the way to b-1 (n-2 CW steps), then returns CCW to b (but b fires
at s2, so step s2-1 must be b+1 or b-1).

Hmm, this is getting complicated. Let me just verify the CLAIM:

Every both-sided excursion visits all n-1 non-b procs.

This should be TRUE by connectivity: the walk is on Z_n, moves +-1, starts
at b's neighbor, visits both sides of b, and returns to b's neighbor. Without
crossing b, the only path between the two sides is the full ring. So YES,
it visits all n-1 procs.
"""

import sys
sys.path.insert(0, './claude')


def verify_both_sided_visits_all(n=5, ms=None):
    """Verify: every both-sided excursion visits all n-1 procs."""
    if ms is None:
        ms = [2, 3, 2, 3, 2]

    binary_procs = [i for i in range(n) if ms[i] == 2]
    total_both_sided = 0
    visits_all = 0
    not_visits_all = 0

    for L in range(11, 16):
        def gen(word):
            nonlocal total_both_sided, visits_all, not_visits_all
            if len(word) == L:
                disp = 0
                cw = 0
                for i in range(L):
                    nxt = word[(i + 1) % L]
                    diff = (nxt - word[i]) % n
                    if diff == 1:
                        cw += 1
                        disp += 1
                    elif diff == n - 1:
                        disp -= 1
                if disp != 0 or cw == 0:
                    return
                fc = [0] * n
                for m in word:
                    fc[m] += 1
                if any(f < 2 for f in fc):
                    return
                if max(fc) < 3:
                    return
                touched = set()
                for m in word:
                    touched.add(m)
                    touched.add((m-1)%n)
                    touched.add((m+1)%n)
                if len(touched) < n:
                    return

                fire_steps = {p: [] for p in range(n)}
                for i, m in enumerate(word):
                    fire_steps[m].append(i)

                for b in binary_procs:
                    fsteps = fire_steps[b]
                    for idx in range(len(fsteps)):
                        s1 = fsteps[idx]
                        s2 = fsteps[(idx+1) % len(fsteps)]
                        if s2 <= s1:
                            s2 += L
                        exc = [word[k%L] for k in range(s1+1, s2)]
                        if not exc:
                            continue
                        exc_set = set(exc)
                        cw_side = set((b+d)%n for d in range(1,n))
                        ccw_side = set((b-d)%n for d in range(1,n))

                        is_one_sided = exc_set <= cw_side or exc_set <= ccw_side
                        if not is_one_sided:
                            total_both_sided += 1
                            if len(exc_set) == n - 1:
                                visits_all += 1
                            else:
                                not_visits_all += 1
                return

            last = word[-1]
            for nxt in [(last-1)%n, last, (last+1)%n]:
                word.append(nxt)
                gen(word)
                word.pop()

        for start in range(n):
            gen([start])

    print(f"Both-sided excursions: {total_both_sided}")
    print(f"  Visits all n-1: {visits_all}")
    print(f"  Doesn't visit all: {not_visits_all}")


def count_one_sided_excursion_structure():
    """For each walk, count how many binary procs have one-sided excursions."""
    n = 5
    ms = [2, 3, 2, 3, 2]
    binary_procs = [i for i in range(n) if ms[i] == 2]

    from collections import Counter
    count_dist = Counter()

    for L in range(11, 14):
        def gen(word):
            if len(word) == L:
                disp = 0
                cw = 0
                for i in range(L):
                    nxt = word[(i + 1) % L]
                    diff = (nxt - word[i]) % n
                    if diff == 1:
                        cw += 1
                        disp += 1
                    elif diff == n - 1:
                        disp -= 1
                if disp != 0 or cw == 0:
                    return
                fc = [0] * n
                for m in word:
                    fc[m] += 1
                if any(f < 2 for f in fc):
                    return
                if max(fc) < 3:
                    return
                touched = set()
                for m in word:
                    touched.add(m)
                    touched.add((m-1)%n)
                    touched.add((m+1)%n)
                if len(touched) < n:
                    return

                fire_steps = {p: [] for p in range(n)}
                for i, m in enumerate(word):
                    fire_steps[m].append(i)

                # Count binary procs with at least one one-sided excursion
                count = 0
                for b in binary_procs:
                    fsteps = fire_steps[b]
                    has_one_sided = False
                    for idx in range(len(fsteps)):
                        s1 = fsteps[idx]
                        s2 = fsteps[(idx+1) % len(fsteps)]
                        if s2 <= s1:
                            s2 += L
                        exc = [word[k%L] for k in range(s1+1, s2)]
                        if not exc:
                            has_one_sided = True
                            continue
                        exc_set = set(exc)
                        cw_side = set((b+d)%n for d in range(1,n))
                        ccw_side = set((b-d)%n for d in range(1,n))
                        if exc_set <= cw_side or exc_set <= ccw_side:
                            has_one_sided = True
                    if has_one_sided:
                        count += 1
                count_dist[count] += 1
                return

            last = word[-1]
            for nxt in [(last-1)%n, last, (last+1)%n]:
                word.append(nxt)
                gen(word)
                word.pop()

        for start in range(n):
            gen([start])

    print("\nDistribution of #binary with one-sided excursion:")
    for k in sorted(count_dist.keys()):
        print(f"  {k} binary: {count_dist[k]} walks")


if __name__ == "__main__":
    print("=== Verify both-sided excursions visit all procs ===")
    verify_both_sided_visits_all()

    print("\n=== One-sided excursion distribution ===")
    count_one_sided_excursion_structure()
