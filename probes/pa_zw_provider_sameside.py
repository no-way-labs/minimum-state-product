"""
Test: when departure = approach (same side), does the far side always fire 0?

If dep = L and app = L: walk starts at L(b), ends at L(b).
Can the walk visit R(b) by going the long way?

If R(b) fires in this interval: walk reached R(b) from the left, going
L -> LL -> ... -> R(b) (going through n-2 procs, not including b).
Then must come back: R(b) -> ... -> L(b). This goes through b?
No! It goes RR -> RRR -> ... -> L. On a ring of 9 with b at 0:
L = 8, R = 1. Going from L(=8) to R(=1) the long way: 8->7->6->5->4->3->2->1.
That's 7 steps. Coming back: 1->2->3->4->5->6->7->8. That's 7 steps.
Total: 14 steps just for the round trip. Plus departure and approach: 16 steps.

With n=9, a round trip through the ring takes ~14 steps. For intervals of length 8-25,
this is feasible. But does it actually happen?

The answer from data: NO, R always fires 0 in (L,L) intervals, even long ones.

WHY? Because the walk is constrained by the mover sequence being a walk on the ring.
For the walk to visit R(b) in an (L,L) excursion, it must:
1. Start at L(b)
2. Go left to LL(b), LLL(b), etc.
3. Eventually reach R(b) going the other way around
4. Come back to L(b)

This round trip visits EVERY proc except b. It uses >= 2(n-2) steps
(go from L to R via the far side: n-2 steps; come back from R to L via the far side:
n-2 steps). Wait, going from L(b) to R(b) the short way (through b) is impossible
because b doesn't fire. Going the long way is n-2 steps.

But then coming back from R(b) to L(b) also goes the long way (since can't pass through b):
also n-2 steps. Total round trip >= 2(n-2).

For n=9: >= 14 steps. This is feasible for intervals of length 14+.

But the DATA shows R fires 0 even in intervals of length 25. So the walk
doesn't make the round trip. Why?

Hmm, actually in the data, L fires 7 times in a length-9 (L,L) interval.
The walk bounces back and forth on the left side without crossing to the right.

But with fc >= 2 for all procs, R(b) must fire >= 2 times total.
If R fires 0 in the (L,L) interval, its fires are concentrated in the (R,R) interval.

Actually... wait. Let me re-examine. With binary b at 0, L=8, R=1 on 9-ring:
In the (L,L) interval, mover starts at 8 and ends at 8.
R = 1 fires 0 means proc 1 never fires. But proc 1 fires >= 2 total.
The (R,R) interval has R firing >= 2. That works.

But proc 5 (far from b) also fires >= 2 total.
In the (L,L) interval starting at 8: does the walk reach 5?
8 -> 7 -> 6 -> 5: yes, easily in 3 steps. So procs 3-8 all fire in this interval.
Proc 1 (= R(b)) doesn't fire because the walk goes 8 -> 7 -> 6 -> ... -> 3
but doesn't continue to 2 -> 1 (that would be going toward R(b)).

AH, I see! The walk goes from L(b) = 8 LEFT (toward 7, 6, 5...) and then
comes back RIGHT (toward 7, 8). It doesn't continue past... wait, it COULD
continue to 2, 1. Let me check.

Actually, on the ring: from 8, left is 7, right is 0 (= b, can't fire).
So from 8, the walk can go to 7 or stay at 8.
From 7, it can go to 6, 7, or 8.
The walk can reach 3 by going 8->7->6->5->4->3.
From 3, it can go to 2. From 2, to 1 (= R(b)).
So the walk CAN reach 1 from the left side! Going 8->7->...->2->1.

But then to come back to 8 (for approach = L): 1->2->...->7->8. Through b? No, b=0.
1->0=b: CAN'T (b doesn't fire in this interval).
1->2->3->...->7->8: this is the long way, 7 steps. Total trip: 7+7=14.

So it IS possible. But the data says it doesn't happen. Let me check:
is there a locality constraint I'm missing?

Oh wait, I see. From proc 1, the walk can go to 0 (=b) or 2.
Going to 0 means b fires: IMPOSSIBLE in this interval.
Going to 2 means the walk goes back toward the left side.

So from proc 1, the walk MUST go to 2 (since it can't fire b).
Then from 2, go to 3 or back to 1. From 1, again must go to 2.
So the walk gets "stuck" oscillating between 1 and 2 (since 1 can't go to 0).

Wait, that's not right either. From 1, the walk can go to 0, 1, or 2.
Going to 0 = b: b fires at step k. But this interval is between consecutive
fires of b, so b CAN'T fire here. The walk can't go to 0.
Going to 1: stay. Fine.
Going to 2: move right.

So from 1, the walk goes to 1 or 2. It can't go to 0.
This means: ONCE the walk reaches proc 1, it can never get back to proc 8
without passing through proc 0 (= b), which is forbidden.

ON A RING, proc 1 (= right(b)) is "one-way trapped": it can't reach left(b)
without going through b. So if the walk reaches right(b), it's stuck on the
right side of b and can never return to left(b) for the approach.

THIS IS THE KEY INSIGHT. On a ring, b acts as a "barrier". The walk can't
cross b (since b doesn't fire in this interval). So the walk is confined to
one ARC of the ring (either the left arc or the right arc, not both).

If departure = L and approach = L: the walk is on the LEFT ARC of b.
It cannot reach right(b) because that would require crossing b.
So right(b) fires 0 in this interval!

WAIT: it CAN reach right(b) by going the LONG way: L -> LL -> ... -> R.
But then from R, to get back to L, it needs to go through b again (short way)
which is impossible, or go the long way again (R -> RR -> ... -> L) which is
another full traversal.

So the walk CAN visit R temporarily by going the long way, but then it's
stuck on the R side and can't return to L for the approach. UNLESS it
does another full traversal.

If the walk goes L -> ... -> R -> ... -> L (two full traversals): that's
>= 2(n-2) steps. And it visits R in between.

CRUCIALLY: the approach must end at L. So the last traversal must end at L.
If the walk visits R at some point and then returns to L: it made a full
round-trip through the ring (skipping b). This requires >= 2(n-2) steps.

But: in this case, R fires >= 1 in the interval. And R fires again in the
other interval. So R fires >= 2 total. Fine.

So the question is: CAN this actually happen? With CL large enough, yes.
But the DATA says it DOESN'T. Why?

Maybe it DOES in some rare cases, but the overall EC mechanism still works
through a different (i, b) pair?

Let me check if there are ANY (L,L) intervals where R fires > 0.
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]

violations = 0
total_intervals = 0

for trial in range(5000000):
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

        for b in range(n):
            if moduli[b] != 2: continue
            fire_steps = [k for k in range(CL) if word[k] == b]
            li = left(b, n)
            ri = right(b, n)

            for idx in range(len(fire_steps)):
                s1 = fire_steps[idx]
                s2_raw = fire_steps[(idx + 1) % len(fire_steps)]
                if s2_raw <= s1: s2_raw += CL

                dep = word[(s1 + 1) % CL]
                app = word[(s2_raw - 1) % CL]

                if dep == li and app == li:
                    total_intervals += 1
                    r_fires = sum(1 for k in range(s1+1, s2_raw) if word[k % CL] == ri)
                    if r_fires > 0:
                        violations += 1
                        if violations <= 3:
                            print(f"VIOLATION: b={b}, interval len={s2_raw-s1-1}, R fires={r_fires}")

                elif dep == ri and app == ri:
                    total_intervals += 1
                    l_fires = sum(1 for k in range(s1+1, s2_raw) if word[k % CL] == li)
                    if l_fires > 0:
                        violations += 1
                        if violations <= 3:
                            print(f"VIOLATION: b={b}, interval len={s2_raw-s1-1}, L fires={l_fires}")

print(f"\nTotal same-side intervals: {total_intervals}")
print(f"Violations (far side fires > 0): {violations}")
