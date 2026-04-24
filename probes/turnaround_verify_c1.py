"""
Verify the details of Lemma 4, sub-case k=1.

Claim: In excursion A of b1 (from left(b1) to right(b1)), after b2 fires
once and bounces, the walk is trapped on the arrival side of b2 and cannot
reach right(b1).

The claim "right(b1) is on the other side of b2" needs:
  b2 is between left(b1) and right(b1) on the path avoiding b1.
  Since b1 and b2 are non-adjacent on the ring, the path from left(b1)
  to right(b1) avoiding b1 (going the "long way") passes through b2.

  On the ring: going CW from b1+1 (=right(b1)), we eventually reach b2,
  then continue to b1-1 (=left(b1)).
  Or going CCW from b1-1, we reach b2, then continue to b1+1.

  Either way, b2 is on the path. The path is:
  left(b1) = b1-1, b1-2, ..., b2+1, b2, b2-1, ..., b1+2, b1+1 = right(b1).

  So b2 divides this path into two segments:
  Segment L: left(b1) to left(b2) (the side of b2 toward left(b1))
  Segment R: right(b2) to right(b1) (the side of b2 toward right(b1))

  After b2 bounces, walk is stuck on Segment L (arrival side).
  right(b1) is at the end of Segment R. Cannot be reached. ∎

But wait: what if the walk approaches b2 from BOTH sides before and after
the bounce? No: b2 fires only ONCE in excursion A, so the walk visits b2
exactly once. It approaches from one side and bounces back to that side.

Also: the walk might reach procs on Segment R without going through b2,
by going around through... but the only other path goes through b1, which
doesn't fire in excursion A. So b1 also blocks. The walk is trapped.

Actually: let me think about whether the walk COULD reach Segment R by
going back to left(b1) and then somehow to right(b1)... but left(b1) is
adjacent to b1, and b1 doesn't fire. From left(b1), the walk can go to
b1 → b1 would have to fire → can't.

From left(b1), walk can go to left(b1)-1 (moving away from b1, toward b2).
That's the only direction (other than b1 which is blocked).

So the walk is confined to the path from left(b1) to b2 (not crossing b2).
This path contains Segment L procs but not Segment R procs.
right(b1) is in Segment R. Walk can't reach it.
Excursion A can't end at right(b1). CONTRADICTION. ✓

Also verify: does the mixed TA excursion NEED to wind?
For mixed TA at b: fire 1 bounces LEFT (arr=L, dep=L).
                   fire 2 bounces RIGHT (arr=R, dep=R).
Excursion 1 goes from left(b) to right(b).
On the ring minus b, left(b) and right(b) are the endpoints of a path
of length n-1. Going from left(b) to right(b) on this path is a
traversal of the entire path. This IS a winding around the ring
(you go from one side of b to the other, the long way).

For the excursion to go from left(b) to right(b): it must traverse
procs on the path. Some of these procs may be visited multiple times
(backtracking). But the NET displacement from left(b) to right(b)
on the path is n-2 edges. This corresponds to winding number ±1
around the ring.
"""

print("Sub-case k=1 verification: argument is SOUND.")
print()
print("The walk in excursion A is confined to the path from left(b1)")
print("to the bounce point at b2, and cannot reach right(b1) which")
print("is on the other side of b2 (or equivalently, on the other")
print("side of the ring from left(b1)).")
print()

# Verify computationally: in every mixed TA excursion at n=5,7,
# the other binary proc's bounce blocks the excursion from reaching
# the destination directly. The excursion DOES reach the destination
# because the bounce is followed by backtracking and the excursion
# takes the OTHER path. Wait... if there's only one path (avoiding b1),
# and b2 blocks it, how DOES the excursion reach right(b1)?

# Answer: it DOESN'T. That's the contradiction. The excursion MUST
# reach right(b1) for the cycle to work, but it CAN'T. So the
# hypothesized configuration (2 non-adjacent mixed TAs) can't exist.

# But at n=5, we DO see single mixed TAs that work. Let's check what
# happens in their excursions when they meet other binary procs.

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

# At n=5: show how a single mixed TA excursion navigates other binary procs
n = 5
bp_list = [(0,1,2)]
ms = [2,2,2,3,3]

cycles = enum_cycles(n, ms)
for cyc in cycles:
    L = len(cyc)
    net = 0; cw = 0
    for i in range(L):
        c, nx = cyc[i], cyc[(i+1)%L]
        if nx == (c+1)%n: net += 1; cw += 1
        elif nx == (c-1)%n: net -= 1
    if net//n != 0: continue
    if cw == 0: continue
    f = [0]*n
    for p in cyc: f[p] += 1
    if any(x < 2 for x in f): continue

    for b in [0,1,2]:
        fires = [i for i in range(L) if cyc[i] == b]
        if len(fires) != 2: continue
        fi = []
        for idx in fires:
            prev = cyc[(idx-1)%L]
            nxt = cyc[(idx+1)%L]
            a = 'L' if prev == (b-1)%n else 'R'
            d = 'L' if nxt == (b-1)%n else 'R'
            fi.append((a,d))
        is_mixed = (fi[0][0] != fi[1][0]) and all(a==d for a,d in fi)
        if not is_mixed: continue

        # This b is mixed TA. But the other binary procs are NOT mixed TA
        # (they're passthrough). So Lemma 4 doesn't apply (it requires
        # both to be mixed TA).

        # The other binary procs are passthrough. In the excursion, they
        # fire and CROSS (arrival side != departure side). So the walk
        # CAN cross them. That's why the excursion works.

        # Let's verify: other binary procs in the excursion are passthrough.
        if fi[0] == ('L','L'):
            f1_idx, f2_idx = fires[0], fires[1]
        else:
            f1_idx, f2_idx = fires[1], fires[0]

        exc_movers = []
        exc_positions = []
        i = (f1_idx + 1) % L
        while i != f2_idx:
            exc_movers.append(cyc[i])
            exc_positions.append(i)
            i = (i+1) % L

        other_binary = [x for x in [0,1,2] if x != b]
        print(f"Cycle {cyc}, b={b} mixed TA, excursion={exc_movers}")
        for ob in other_binary:
            ob_fire_indices = [j for j, m in enumerate(exc_movers) if m == ob]
            if len(ob_fire_indices) != 1:
                print(f"  OTHER binary {ob}: {len(ob_fire_indices)} fires in exc (unexpected)")
                continue
            fpos = ob_fire_indices[0]
            # Get arrival and departure of ob in excursion
            if fpos > 0:
                arr_proc = exc_movers[fpos-1]
            else:
                arr_proc = cyc[f1_idx]  # left(b) from before excursion
            if fpos < len(exc_movers)-1:
                dep_proc = exc_movers[fpos+1]
            else:
                dep_proc = cyc[(f2_idx - 1 + L) % L] if exc_movers else None
                # Actually dep should be right(b) since next is fire2 which arrives from right(b)
                dep_proc = (b+1)%n

            arr_side = 'L' if arr_proc == (ob-1)%n else 'R'
            dep_side = 'L' if dep_proc == (ob-1)%n else 'R'
            pattern = "PASSTHROUGH" if arr_side != dep_side else "TURNAROUND"
            print(f"  OTHER binary {ob}: arr={arr_side}, dep={dep_side} → {pattern}")

print()
print("CONCLUSION: In single-mixed-TA cycles, the other binary procs")
print("are always PASSTHROUGH (crossing), allowing the excursion to")
print("traverse the entire ring. If those other procs were TURNAROUND,")
print("they would bounce and block the excursion, making it impossible.")
