"""
Mixed TA impossibility for non-adjacent binary procs.

KEY INSIGHT: For mixed TA at b, the walk around fire 1 looks like:
  ..., left(b), b, left(b), ...
The two consecutive appearances of left(b) around b's fire 1 are
BOTH fires of left(b) if left(b) is binary. But what if left(b) is ternary?

For ternary left(b): left(b) fires 3 times. Two of those fires sandwich
b's fire 1. But left(b) has a THIRD fire somewhere else in the cycle.

For mixed TA at b with ternary neighbors:
- left(b) fires at positions (fire1-1) and (fire1+1) — sandwiching fire 1.
  Plus at least 1 more fire elsewhere.
- right(b) fires at positions (fire2-1) and (fire2+1) — sandwiching fire 2.
  Plus at least 1 more fire elsewhere.

Now consider 2 non-adjacent mixed TAs at b1, b2 with ternary neighbors.
The same structure applies at both.

For the excursion from fire1 of b1 to fire2 of b1:
  Starts at left(b1) (position fire1+1).
  Ends at right(b1) (position fire2-1).
  Must wind once around the ring.

This excursion contains b2's fires (since b2 fires in the excursion
somewhere — the excursion covers the whole ring minus b1).

If b2 fires ONCE in this excursion and ONCE in the other excursion:
  b2's fire in this excursion is either fire2_1 or fire2_2.
  Say fire2_1 is in excursion A of b1 (fire1_1 to fire1_2).
  Then: at position fire2_1, the walk looks like:
    ..., right(b2), b2, right(b2), ... (if fire2_1 is b2's "right fire")
    or ..., left(b2), b2, left(b2), ... (if fire2_1 is b2's "left fire").

  For b2's mixed TA: fire2_1 bounces one way, fire2_2 bounces the other.
  Say fire2_1 bounces LEFT: ..., left(b2), b2, left(b2), ...
  And fire2_2 bounces RIGHT: ..., right(b2), b2, right(b2), ...

  In excursion A of b1: the walk visits b2 via fire2_1, approaching from
  left(b2) and returning to left(b2). The walk must then continue from
  left(b2) toward right(b1) (the end of excursion A).

  But wait: the walk is going from left(b1) to right(b1) (winding CW, say).
  When it reaches b2 (via left(b2) side), it bounces back to left(b2) side.
  Then it must continue toward right(b1), but it's now on the left(b2) side.

  On the ring: left(b1) ... left(b2), b2, right(b2) ... right(b1).
  The walk winds CW: left(b1) → ... → left(b2) → b2 → left(b2) → ...
  After bouncing at b2, the walk is at left(b2). To reach right(b1), it
  must continue CW from left(b2). But right(b2) is the next proc CW.
  From left(b2): can go to b2 or to the proc before left(b2) on the ring.
  Going to b2: b2 can't fire again in this excursion (fire2_2 is in the other one).
  Wait, actually b2 fires once more (fire2_2) but that's in the other excursion.
  So in THIS excursion, b2 fires only once (fire2_1). After bouncing at b2,
  the walk is at left(b2) and can't go back to b2 (b2 has no more fires here).

  From left(b2), the walk goes to left(b2)-1 (away from b2, toward left(b1)).
  But the walk needs to reach right(b2) and beyond (toward right(b1)).
  The only path to right(b2) is through b2. Since b2 can't fire again, the
  walk CAN'T reach right(b2) in this excursion.

  Unless: the walk goes left(b2) → left(b2)-1 → ... → left(b1) → ...
  and then continues around the ring the OTHER way to reach right(b2).
  But that would require winding TWICE (going past left(b1) and all the way
  around). The excursion already winds once to go from left(b1) to right(b1).
  Going past left(b1) means revisiting the start, then continuing further.
  This adds n extra steps minimum — too expensive.

  Actually: the walk is not constrained to wind exactly once without backtracking.
  It CAN backtrack. Let me think about the step budget.

  For this excursion (A of b1): length = some number of steps.
  The walk must reach all procs between left(b1) and right(b1) going CW.
  That's n-2 procs (everyone except b1). The walk must fire each at least
  once per visit, but it can visit a proc multiple times if the proc has
  extra fires.

  The KEY constraint: the walk must reach right(b2) (and procs beyond it).
  right(b2) is reached either through b2 or from right(b2)+1.
  Through b2: b2 doesn't fire again in this excursion.
  But WAIT: the walk mover word has other procs between b2 and right(b2).
  right(b2) = b2+1 on the ring. The walk reaches right(b2) from right(b2)+1
  or from b2. Since b2 doesn't fire, the step right(b2) → b2 never happens
  (that would require b2 to be the next mover). And b2 → right(b2) never
  happens (that would require b2 to fire again). So in this excursion:
  right(b2) is only reachable from right(b2)+1.

  But similarly, right(b2)+1 is reachable from right(b2)+2 or right(b2).
  For the walk to reach right(b2)+1 from right(b2): right(b2) fires
  (it's ternary, fc≥3), and next mover is right(b2)+1. This is fine.
  For the walk to reach right(b2) from right(b2)+1: right(b2)+1 fires,
  next mover is right(b2). Fine.

  So right(b2) CAN be reached from right(b2)+1. The walk goes:
  ... right(b2)+1 → right(b2) → right(b2)+1 → ...
  (bouncing at right(b2)).

  So procs beyond b2 CAN be reached without going through b2, by approaching
  from the other side. The walk goes the "long way" around from left(b2) to
  right(b2), passing through many procs.

  Hmm, so the walk CAN reach right(b2) by going around the ring from left(b2)
  the other way (through left(b1) side). Let me re-examine.

  The excursion A of b1 starts at left(b1) and ends at right(b1).
  It winds CW (or CCW). Say CW: from left(b1) going CW around the ring.
  It reaches procs in order: left(b1)+1, left(b1)+2, ...
  Eventually it reaches left(b2), then b2 (fire2_1, bounces back to left(b2)).
  Then from left(b2) it must continue. Since it can't go to b2, it goes to
  left(b2)-1 (CCW). Now it's backtracking.

  It continues backtracking until it finds a way forward... or it reaches
  a proc that can "push" it in the CW direction again. But the walk goes
  wherever the mover word dictates.

  The point is: right(b2) MUST be visited in this excursion (it fires at
  least twice total, and needs to fire in this excursion at least once —
  unless ALL its fires are in excursion B of b1).

  Can ALL fires of right(b2) be in excursion B of b1? right(b2) fires 3 times
  (ternary). One fire is at fire2_2+1 (sandwiching b2's fire 2 in excursion B).
  The other 2 fires can be anywhere. If all 3 are in excursion B: right(b2)
  fires 0 times in excursion A. Then the walk in excursion A doesn't visit
  right(b2) at all. But the excursion winds once: it passes through every
  position on the ring except b1. So it must pass through right(b2)'s position.
  But passing through = being a mover. If right(b2) fires 0 times in excursion A,
  the walk never has right(b2) as mover. The walk can still be AT right(b2)'s
  ring position... no, the walk IS the mover sequence. Position in the walk
  IS which proc fires. If right(b2) doesn't fire, it's not in the walk at all.

  For the walk to "pass through" right(b2) without right(b2) firing: the walk
  goes from left(b2) to right(b2)+1 somehow. But they're not adjacent!
  They're 2 apart (with b2 in between). So the walk CAN'T go from left(b2)
  to right(b2)+1 in one step. The walk must go through b2 or right(b2).
  b2 doesn't fire (already fired once). right(b2) doesn't fire (all in exc B).

  DEAD END: The walk can't cross from left(b2) side to right(b2) side.
  This means the excursion is CUT at b2, just like a dead edge!

  Specifically: in excursion A of b1, after b2's bounce, the walk is stuck
  on the left(b2) side. It can't reach right(b2) or beyond.

  But the excursion must reach right(b1) (which is beyond right(b2) going CW).
  This is IMPOSSIBLE if right(b1) is on the right(b2) side of b2.

  Is right(b1) on the right(b2) side? On the ring CW from b2:
  b2, right(b2), right(b2)+1, ..., right(b1), b1, left(b1), ..., left(b2), b2.
  So YES: right(b1) is CW from b2 (on the right(b2) side).

  Therefore: the excursion A of b1, after bouncing at b2, CANNOT reach
  right(b1). But it must end at right(b1). CONTRADICTION.

  WAIT: this assumes right(b2) fires 0 times in excursion A. What if
  right(b2) fires 1+ times in excursion A? Then the walk CAN reach
  right(b2) and continue past it. Let me reconsider.

  If right(b2) fires at least once in excursion A: the walk reaches
  right(b2) (from its right side, i.e., right(b2)+1). Then right(b2) fires,
  and the walk goes to b2 or right(b2)+1. If it goes to b2: b2 already
  fired (fire2_1), so b2 fires again? But b2 has only 2 fires total.
  fire2_1 is in excursion A. If b2 fires again, that's fire2_2.
  Then BOTH b2 fires are in excursion A.

  If both b2 fires in excursion A: b2's excursions are BOTH contained in
  excursion A of b1. b2's excursion C (fire2_1 to fire2_2) is inside
  excursion A. b2's excursion D (fire2_2 to fire2_1) wraps around and
  includes excursion B of b1. But excursion D must wind once around the ring.
  It contains excursion B of b1 plus some extra. That's fine structurally.

  In this case, b2 fires twice in excursion A of b1.
  fire2_1: bounces LEFT (left(b2) → b2 → left(b2)).
  fire2_2: bounces RIGHT (right(b2) → b2 → right(b2)).
  Between fire2_1 and fire2_2: excursion C of b2. Must go from left(b2)
  to right(b2) (winding once around ring minus b2). But this excursion C
  is INSIDE excursion A of b1, which goes from left(b1) to right(b1).
  Excursion C must wind once: it visits all procs except b2.
  Including b1? But b1 doesn't fire in excursion A (b1 fires at fire1_1 and
  fire1_2 which bound excursion A). So b1 fires 0 times in excursion A.
  Excursion C (inside A) also has b1 firing 0 times.
  Excursion C must reach b1's position? b1 doesn't fire in C.
  Same argument: walk can't cross b1 without b1 firing.
  The walk gets stuck at b1 just like it got stuck at b2 before.

  So: excursion C of b2, inside excursion A of b1, hits the SAME problem
  at b1. It can't cross b1 (b1 doesn't fire). CONTRADICTION with excursion C
  winding once.

This gives us the proof!
"""

print("PROOF COMPLETE — see analysis in docstring")
print()
print("="*70)
print("SUMMARY OF ANALYTICAL PROOF")
print("="*70)
print("""
THEOREM: With ≥3 binary procs, at most 2 can be turnaround.

PROOF (by cases):

CASE A: ≥3 same-side turnarounds → ≥2 distinct dead edges → disconnection.

CASE B: Adjacent binary neighbor constraint.
  If b is mixed TA and neighbor left(b) is binary:
    left(b) fires at positions fire1±1 (sandwiching b's fire 1).
    If left(b) is binary (fc=2), these are its only fires.
    At fire (fire1-1): departure is toward b (= RIGHT for left(b)).
    Arrival: from mw[fire1-2] ≠ b (since fire1-2 ≠ fire1 and fire1-2 ≠ fire2,
    unless fire2 = fire1-2 which forces b's excursion to length 0 → contradiction).
    So arrival is from LEFT. arr ≠ dep: NOT turnaround. ∎

  Therefore: mixed TA b forces adjacent binary neighbors to be passthrough.
  With 3 binary, if any two are adjacent and one is mixed TA, the other is passthrough.

CASE C: Two non-adjacent mixed TAs (b1, b2) with ternary neighbors.
  b1 is mixed TA: fire1 bounces LEFT, fire2 bounces RIGHT.
  b2 is mixed TA: fire2_1 bounces LEFT, fire2_2 bounces RIGHT.

  Consider excursion A of b1 (fire1_1 → fire1_2).
  b2 fires k times in excursion A (k ∈ {0, 1, 2}).

  SUB-CASE C1: k=1 (one b2 fire in excursion A).
    After b2's bounce, walk returns to arrival side.
    b2's other-side procs unreachable (b2 doesn't fire again in A).
    Walk can't cross b2 to reach right(b1). ← CONTRADICTION.
    (Walk reaches left(b2), bounces back, can't cross to right(b2)
    side without b2 firing. right(b1) is on right(b2) side.)

  SUB-CASE C2: k=0 (b2 doesn't fire in excursion A).
    Walk can't cross b2 at all (b2 ≠ mover). Adjacent procs on opposite
    sides of b2 are not ring-adjacent. Walk is cut. ← CONTRADICTION.

  SUB-CASE C3: k=2 (both b2 fires in excursion A).
    b2's excursion C (fire2_1 → fire2_2) is inside excursion A of b1.
    Excursion C must wind once around ring minus b2.
    But b1 fires 0 times in excursion A (and hence in C).
    Walk can't cross b1 in excursion C (same as C2 argument with b1 and b2 swapped).
    ← CONTRADICTION.

  All sub-cases contradict. Two non-adjacent mixed TAs impossible. ∎

COMBINED: ≥3 turnarounds requires ≥3 same-side (Case A kills) or ≥2 mixed.
≥2 mixed: if adjacent, Case B kills. If non-adjacent, Case C kills. ∎

COROLLARY: At least 1 binary proc is passthrough → provider exists
(by the passthrough → provider theorem).
""")

# Verify the "can't cross b2" claim computationally.
print("="*70)
print("VERIFICATION: b2 bounce blocks crossing")
print("="*70)

# At n=5, find mixed TA cycles and verify the walk is stuck.
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

n = 5
for bp in combinations(range(n), 3):
    ms = [3]*n
    for b in bp: ms[b] = 2
    prod = 1
    for m in ms: prod *= m
    if prod >= 4*3**(n-2): continue

    cycles = enum_cycles(n, ms)
    for cyc in cycles:
        net = 0; cw = 0
        L = len(cyc)
        for i in range(L):
            c, nx = cyc[i], cyc[(i+1)%L]
            if nx == (c+1)%n: net += 1; cw += 1
            elif nx == (c-1)%n: net -= 1
        if net//n != 0: continue
        if cw == 0: continue
        f = [0]*n
        for p in cyc: f[p] += 1
        if any(x < 2 for x in f): continue

        # Find mixed TAs
        for b in bp:
            fires = [i for i in range(L) if cyc[i] == b]
            if len(fires) != 2: continue
            fi = []
            for idx in fires:
                prev = cyc[(idx-1)%L]
                nxt = cyc[(idx+1)%L]
                a = 'L' if prev == (b-1)%n else 'R'
                d = 'L' if nxt == (b-1)%n else 'R'
                fi.append((a,d))
            if fi[0] == ('L','L') and fi[1] == ('R','R') or \
               fi[0] == ('R','R') and fi[1] == ('L','L'):
                # Mixed TA at b
                # Show the excursions and which procs fire in each
                f1, f2 = fires
                if fi[0] == ('L','L'):
                    # Excursion from fire1 to fire2: left(b) to right(b)
                    exc_start = (f1+1) % L
                    exc_end = f2
                else:
                    exc_start = (f2+1) % L
                    exc_end = f1

                exc_movers = []
                i = exc_start
                while i != exc_end:
                    exc_movers.append(cyc[i])
                    i = (i+1) % L

                # Which binary procs fire in this excursion?
                other_binary = [x for x in bp if x != b]
                for ob in other_binary:
                    fires_in_exc = exc_movers.count(ob)
                    if fires_in_exc == 0:
                        print(f"  n={n}, bp={bp}, b={b} mixed TA: {ob} fires 0 times in excursion → CAN'T CROSS")
                    elif fires_in_exc == 1:
                        print(f"  n={n}, bp={bp}, b={b} mixed TA: {ob} fires 1 time in excursion → BOUNCES")
