"""
FLIPPED approach: Instead of "between consecutive fires of i, b fires even",
try "between consecutive fires of b (binary), i fires and there's a good suffix".

For binary proc b with fc(b) >= 2 (even), between consecutive fires of b:
b doesn't fire. The mover traverses an excursion.

Now pick i = right(b) as the target proc for EC.
Between consecutive fires of b at (a1, a2), consider:
- i fires some number of times in (a1, a2)
- If i fires at least once in (a1, a2), pick the FIRST i-fire in (a1, a2) as k2.
  Wait, that's the mover step (i IS mover there).

Actually, let me reconsider the EC mechanism completely.

EC = two steps k1, k2 where:
  k1: mover = i (i fires)
  k2: mover != i (i doesn't fire)
  config(k1, left(i)) = config(k2, left(i))
  config(k1, i) = config(k2, i)
  config(k1, right(i)) = config(k2, right(i))

For this to happen:
  Between k2 and k1 (or k1 and k2):
  left(i) returns to same value
  i returns to same value
  right(i) returns to same value

If k2 < k1:
  In [k2, k1): i fires 0 times -> same i-value
  In [k2, k1): left(i) fires even times (if binary) or 0 times
  In [k2, k1): right(i) fires even times (if binary) or 0 times

So the original formulation is: find k1 (i fires), k2 (i doesn't fire),
with k2 < k1, and in [k2, k1):
  - i fires 0 times
  - left(i) fires 0 or binary-even
  - right(i) fires 0 or binary-even

This is independent of which is a1 and which is a2.
The interval [k2, k1) should have i not firing.

So: take ANY i-fire step as k1. Take ANY non-i step before it (in the same
consecutive-fire-free interval) as k2. Check neighbors in [k2, k1).

This is exactly what we've been testing. Let me try a different analytical approach.

APPROACH: Global parity argument.

For proc i with binary neighbor b (on left, say):
Consider ALL steps in the cycle. At each step, b either fires or doesn't.
The b-parity toggles: starts at 0, ends at fc(b) (even). So it's 0 at both ends.

The f-parity starts at 0, ends at fc(f).

At each i-fire step k1, consider the b-parity (running total of b-fires from step 0 to k1)
and the f-parity (running total of f-fires from step 0 to k1).

For EC: we need a non-i step k2 with SAME b-parity (even difference) and same f-value
(0 f-fires in between). But f is not binary, so we need 0 f-fires.

Actually this global view is messy. Let me try yet another approach.

APPROACH: Take b adjacent to i. Consider the step sequence.
In the full cycle, mark each step as 'b' (mover=b), 'f' (mover=f), 'i' (mover=i), or 'o' (other).

We want: two positions k2 < k1 where:
  - k1 is an 'i' step
  - k2 is NOT an 'i' step
  - in [k2, k1): b fires even times, f fires 0 times, i fires 0 times

Since i fires 0 in [k2, k1), k2 and k1 must be in the same consecutive-fire-free
interval of i (between consecutive i-fires).

In that interval, the steps are all non-i. We need a suffix [k2, k1) with even b-fires
and 0 f-fires, where k1 is the next i-fire.

So restrict to one interval (a1, a2) of i (a1 and a2 are i-fire steps).
We need k2 in (a1, a2) with mover[k2] != i, and in [k2, a2): b fires even, f fires 0.

Now the question: WHICH i to pick, and which interval?

The answer from computation: pick ANY i adjacent to binary b, and search all intervals.

For the analytical proof, I need to show that SOME (i, interval) pair works.

New idea: the "provider" approach.
Some proc q has fc(q) >= 3. Since CL > 2n.
Take i adjacent to q with i binary (possible: >= 3 binary, q's neighbors might include one).

Wait, q might not be adjacent to a binary proc!

OK let me think about this more carefully...

With >= 3 binary on a ring of n, there are at most n - 3 non-binary procs.
The binary procs form arcs. Between consecutive non-binary arcs, there's a binary arc.

For the "provider" argument with fc >= 3:
q has fc >= 3. q fires >= 3 times. q has two neighbors left(q) and right(q).

By locality, each time q fires, the prev/next mover is adjacent to q.
After q fires, the mover goes to a neighbor. Before q fires, the mover comes from a neighbor.

Between consecutive fires of q (say a1, a2 with gap = a2-a1-1 >= 1):
The mover starts at a neighbor of q, traverses, returns to a neighbor of q.
q has fc >= 3, so it has >= 3 intervals. In at least one interval, the excursion
goes in one direction.

Actually, I think the simplest approach is empirical + appeal to the tested mechanism.
Let me just verify the two-part claim:
1. SOME (i, b) pair has an interval with b >= 2 fires
2. In that interval, some pair of consecutive b-fires has no f after them

Both parts pass 100% computationally. Let me write the proof document.

But first, let me understand Part 1 better. When does EVERY (i, b) pair have max_b = 1?
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 5
moduli = [2, 2, 2, 3, 3]

for trial in range(500000):
    word = [random.randint(0, n-1)]
    for _ in range(random.randint(2*n+1, 5*n) - 1):
        curr = word[-1]
        word.append(random.choice([curr, left(curr, n), right(curr, n)]))

    CL = len(word)
    fc = [0] * n
    for m in word: fc[m] += 1
    if not all(f >= 2 for f in fc): continue
    if not any(f >= 3 for f in fc): continue
    for p in range(n):
        if moduli[p] == 2 and fc[p] % 2 != 0: break
    else:
        cw = sum(1 for k in range(CL) if word[(k+1) % CL] == right(word[k], n))
        ccw = sum(1 for k in range(CL) if word[(k+1) % CL] == left(word[k], n))
        if cw != ccw or cw == 0: continue
        ok = True
        for k in range(CL):
            if word[(k+1)%CL] not in [word[k], left(word[k],n), right(word[k],n)]:
                ok = False; break
        if not ok: continue

        # Check if ALL (i,b) pairs have max_b <= 1
        all_max1 = True
        for i in range(n):
            li = left(i, n)
            ri = right(i, n)
            for b in [li, ri]:
                if moduli[b] != 2: continue
                fire_steps = [k for k in range(CL) if word[k] == i]
                if len(fire_steps) < 2: continue
                for idx in range(len(fire_steps)):
                    a1 = fire_steps[idx]
                    a2_raw = fire_steps[(idx+1) % len(fire_steps)]
                    if a2_raw <= a1: a2_raw += CL
                    gap = list(range(a1+1, a2_raw))
                    b_in = sum(1 for k in gap if word[k % CL] == b)
                    if b_in >= 2:
                        all_max1 = False
                        break
                if not all_max1: break
            if not all_max1: break

        if all_max1:
            print(f"ALL (i,b) have max_b<=1: fc={fc}, CL={CL}, word={word}")
            break

print("Search complete")
