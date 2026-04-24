"""
Check: in cycles where a binary proc appears as "turnaround" WITHIN an excursion,
what's its GLOBAL classification?

The concern: if binary proc b2 has one fire in excursion A and one fire in excursion B
of mixed-TA proc b1, then within excursion A, b2 fires once and might look turnaround.
But its GLOBAL classification (both fires combined) might be passthrough.
Our proof only requires that all 3 binary are GLOBALLY turnaround.
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

def classify_global(mw, b, n):
    L = len(mw)
    fires = [i for i in range(L) if mw[i] == b]
    if len(fires) != 2: return 'bad'
    fi = []
    for idx in fires:
        prev = mw[(idx-1)%L]
        nxt = mw[(idx+1)%L]
        a = 'L' if prev == (b-1)%n else 'R'
        d = 'L' if nxt == (b-1)%n else 'R'
        fi.append((a,d))
    if all(a==d for a,d in fi):
        sides = [f[0] for f in fi]
        return f'mixed({fi})' if sides[0] != sides[1] else f'same_{sides[0]}({fi})'
    return f'pt({fi})'

n = 5
ms = [2,2,2,3,3]
cyc = [0, 1, 2, 3, 4, 0, 4, 3, 4, 3, 2, 1]
L = len(cyc)

print(f"Cycle: {cyc}")
for b in [0,1,2]:
    print(f"  b={b}: {classify_global(cyc, b, n)}")

# b=0 is mixed TA. Within excursion, b=1 appears as "turnaround" locally.
# But globally, b=1 should be passthrough.
# Let me check: b=1 fires at positions where?
fires_1 = [i for i in range(L) if cyc[i] == 1]
print(f"\nb=1 fires at positions: {fires_1}")
for idx in fires_1:
    prev = cyc[(idx-1)%L]
    nxt = cyc[(idx+1)%L]
    print(f"  Fire at {idx}: prev={prev}, mover=1, next={nxt}")
    a = 'L' if prev == 0 else 'R'
    d = 'L' if nxt == 0 else 'R'
    print(f"    arr={a}, dep={d} {'(turnaround)' if a==d else '(passthrough)'}")

# So b=1's global type is determined by BOTH fires.
# If fire 1 is (R,R) and fire 2 is (L,R), then fire 1 is turnaround
# but fire 2 is passthrough → globally passthrough.

print()
print("KEY INSIGHT: A proc can be 'turnaround' at ONE fire and 'passthrough'")
print("at the other. Our definition requires BOTH fires to be turnaround for")
print("the proc to be globally turnaround.")
print()
print("In the excursion analysis, we checked one fire of the other binary proc.")
print("That fire might be turnaround, but the other fire (in the other excursion)")
print("might not be. This is consistent: the other binary proc is globally passthrough.")
print()
print("The Lemma 4 argument doesn't depend on local turnaround/passthrough of")
print("individual fires. It depends on whether the walk CAN CROSS b2 during the")
print("excursion. After b2 fires once and bounces (arr_side = dep_side), the walk")
print("returns to the arrival side. The walk is trapped because:")
print("1. b2 can't fire again in this excursion (if k=1).")
print("2. The only path from left(b2)-side to right(b2)-side goes through b2.")
print("3. Without b2 firing, the walk can't step from left(b2) to b2 to right(b2).")
print()
print("Wait: 'the walk can't step from left(b2) to b2': actually left(b2) CAN step")
print("to b2 if b2 fires. But b2 already fired its one allowed fire in this excursion.")
print("... unless b2 fires twice in this excursion (k=2 case).")
print()
print("For k=1: after the single bounce, left(b2) can still step to b2 IF there's")
print("another fire of b2. But k=1 means exactly 1 fire. So no more fires of b2.")
print("From left(b2): walk goes to left(b2)-1 (away from b2) since step to b2")
print("requires b2 to fire. From b2's perspective: the walk last departed b2 to")
print("the arrival side. b2 is 'inactive' for the rest of this excursion.")
print()
print("CONCLUSION: The walk bounces at b2 (single fire, k=1) and is trapped.")
print("Excursion A cannot reach right(b1). Contradiction proven.")
