"""
THE WALK ARGUMENT:

Between consecutive fires of binary b at steps s_1, s_2:
- mover[s_1] = b (b fires)
- mover[s_1 + 1] is adjacent to b: left(b) or right(b)
- ... walk continues ...
- mover[s_2 - 1] is adjacent to b: left(b) or right(b)
- mover[s_2] = b (b fires)

The walk in (s_1, s_2) starts at a neighbor and ends at a neighbor.
Define:
  departure(k) = mover[s_k + 1] (which neighbor the walk goes to after s_k)
  approach(k+1) = mover[s_{k+1} - 1] (which neighbor the walk comes from before s_{k+1})

For binary b with fc(b) = 2F intervals (2F fires), there are 2F departure-approach pairs:
(departure_k, approach_{k+1}) for k = 0, ..., 2F-1 (cyclic).

By locality, departure is L or R, approach is L or R.
So there are 4 types: (L,L), (L,R), (R,L), (R,R).

Now: if both departure and approach are the same side (L,L) or (R,R),
the walk goes out one side and comes back the same side.
If different: the walk goes through the ring.

KEY CLAIM: If departure is L (mover goes to left(b) right after b fires),
then left(b) fires at step s_k + 1. So in the NEXT interval (from i = left(b)'s
perspective), this left(b) fire starts a new interval of left(b).

Hmm wait, I'm overcomplicating. Let me think about this differently.

For the "zero i between consecutive b-fires" claim:

Binary b fires at s_1, s_2, ..., s_{2F}.
left(b) fires at t_1, t_2, ..., t_{F_L}.

"left(b) fires in every interval of b" means: for every consecutive pair (s_k, s_{k+1}),
there exists some t_j with s_k < t_j < s_{k+1}.

This means: the t_j sequence interleaves with the s_k sequence.
Since there are 2F intervals of b and F_L fires of left(b),
if F_L < 2F: at least 2F - F_L intervals have no left(b) fire.

So: 2F > F_L implies some interval with no left(b) fire. I.e., fc(b) > fc(left(b)).

But we're in the case where fc(b) <= fc(left(b))!
So F_L >= fc(b) = 2F.

Similarly F_R >= fc(b) = 2F.

Total fires: CL = sum fc >= sum_binary fc + F_L_for_each_binary + F_R_for_each_binary - overlaps.

Wait, left(b) and right(b) might be shared among different binary procs.

Let me just use the direct inequality:
For ALL binary b: fc(b) <= fc(left(b)) AND fc(b) <= fc(right(b)).

Summing fc(b) <= fc(left(b)) over all binary b:
sum_{b in B} fc(b) <= sum_{b in B} fc(left(b))

sum_{b in B} fc(left(b)) = sum_{p in L(B)} fc(p), where L(B) = {left(b) : b in B}.

Since |L(B)| = |B| (left is injective on a ring):
sum_B fc(b) <= sum_{L(B)} fc(p)

Also sum_B fc(b) <= sum_{R(B)} fc(p) where R(B) = {right(b) : b in B}.

Now: B, L(B), R(B) are three sets of size |B| each.
Some procs might be in multiple sets (if binary procs are adjacent).

Total CL = sum_all fc. If we add both inequalities:
2 * sum_B fc <= sum_{L(B)} fc + sum_{R(B)} fc

Let N(B) = L(B) union R(B) (all neighbors of binary procs).
|N(B)| <= 2|B| (at most 2 neighbors each, might overlap).

2 * sum_B fc <= sum_{N(B)} fc + overlap_correction

In the worst case (no overlap): 2 * sum_B fc <= sum_{N(B)} fc.

But sum_B fc >= 2|B| (each binary fires >= 2) and sum_{N(B)} fc <= CL - sum_{B \ N(B)} fc.

This gets messy. Let me try a counting argument on the WALK ITSELF.

THE WALK PASSES THROUGH ARGUMENT:

Between consecutive fires of b, the walk goes from a neighbor of b to a neighbor of b.
If it goes from left(b) to left(b): it stays on the left side.
  In this case, right(b) does NOT fire in this interval (walk doesn't reach right side).
  So the interval has no right(b) fire.
  BUT: does the walk necessarily REACH right(b)? Maybe not! The walk can bounce
  around on the left side without ever reaching right(b).

Actually, for right(b) to fire 0 times in the interval: right(b) must accumulate all
its fires in OTHER intervals of b. But right(b) fires fc(R) >= 2 total. If none are
in this interval, they're all in other intervals.

KEY INSIGHT: Consider the departure/approach pattern.

If b fires at s_k with departure to left(b), and at s_{k+1} with approach from left(b):
The excursion stays on the "left side." right(b) fires 0 in this interval.

If this is an (L,L) excursion: right(b) fires 0. So for i = right(b), between s_k and s_{k+1},
i fires 0. -> Two b-fires (s_k and s_{k+1}) bracket an interval with i=0. WIN for Part 1!

But wait: departure = left means mover[s_k + 1] = left(b). Approach = left means
mover[s_{k+1} - 1] = left(b). The walk between these is on the left side.
Does that guarantee right(b) doesn't fire? YES! Because the walk is connected
(by locality), and to reach right(b), the walk must pass through b. But b doesn't
fire in this interval (between consecutive b-fires). The walk can't reach right(b)
without passing through b first!

Wait, that's not quite right. The walk is on a RING. The walk could go:
left(b) -> LL(b) -> ... -> right(b) going the "long way around."

Hmm, but with locality, the walk goes step by step. Starting at left(b),
going left: L(b) -> LL(b) -> ... -> going around the ring. Eventually it
can reach right(b) from the OTHER side (going through all other procs).

So an (L,L) excursion CAN visit right(b) by going the long way around.

OK so the departure/approach argument doesn't directly prevent the far side from firing.

But: if the excursion goes the long way around (from left(b) through the whole ring
back to left(b)), that requires visiting ALL procs. The excursion length must be >= n-1
(visiting n-1 distinct procs besides b).

With fc(b) = 2 intervals and CL > 2n:
Two intervals of total length CL > 2n. If one has length >= n+1, the other has length <= n-1.
The long-way-around excursion needs length >= n-1. So at most one interval can go long-way.

If both intervals are short (length ~n each): neither goes the long way around.
In that case, an (L,L) excursion of length n does NOT visit right(b) (needs n+1 steps
to go the long way, since ring has n procs and we skip b).

Hmm, this is getting really complicated. Let me try yet another approach.

SIMPLEST APPROACH:
Since all fc >= 2 and binary fc even: binary fires at minimum = 2.
CL > 2n. Total binary fires >= 6 (with 3 binary).

For the "interleaving" constraint:
Binary b fires at positions on the cycle. left(b) also fires.
The fires alternate somehow.

The simplest claim: among 3 binary procs, at least one has fc >= 4.
Then for that b, fc(b)/2 >= 2 intervals, and with fc(neighbor) >= 2,
we can ensure... no, this isn't right either.

Let me just check: does EVERY valid cycle have a binary with fc >= 4?
"""
import random
random.seed(42)

def left(p, n): return (p - 1) % n
def right(p, n): return (p + 1) % n

n = 9
moduli = [2, 2, 2, 3, 3, 3, 3, 3, 3]

has_bin_fc4 = 0
no_bin_fc4 = 0
total = 0

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
        total += 1

        bin_fcs = [fc[p] for p in range(n) if moduli[p] == 2]
        if any(f >= 4 for f in bin_fcs):
            has_bin_fc4 += 1
        else:
            no_bin_fc4 += 1

print(f"Total: {total}")
print(f"Some binary fc>=4: {has_bin_fc4}")
print(f"All binary fc=2: {no_bin_fc4}")
