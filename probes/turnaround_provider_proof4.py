"""
Turnaround Binary Provider Proof - Part 4
==========================================
Prove ALL-turnaround is impossible for ≥3 binary in a zero-winding good cycle
with cwSteps > 0 and all fc ≥ 2.

Key structural argument:

For a turnaround at binary b:
- "Same-side" turnaround to LEFT:
  Edges at b: (b-1)->b and b->(b-1) each appear twice.
  Edges b->b+1 and b+1->b: ZERO times.
  The edge (b, b+1) has 0 crossings from b's fires.

- "Same-side" turnaround to RIGHT:
  Edges at b: b->b+1 and b+1->b each appear twice.
  Edge (b-1, b): ZERO.

- "Mixed" turnaround:
  Fire 1 bounces LEFT: (b-1)->b, b->(b-1)
  Fire 2 bounces RIGHT: (b+1)->b, b->(b+1)
  Each edge has 1 crossing from b's fires. Net flow = 0 on both sides.

Now consider the "crossing number" of the cut between b and b+1.
This is #(b->b+1) + #(b+1->b) = total crossings.

For same-side LEFT turnaround: cut(b, b+1) gets 0 from b's fires.
For same-side RIGHT turnaround: cut(b, b+1) gets 2 from b's fires.
For mixed turnaround: cut(b, b+1) gets 1 from b's fires (fire 2 only).

Total crossings of cut(b, b+1) must be EVEN (each proc contributes
an even number of crossings of any cut, since it enters and exits).

Wait — actually each proc p contributes exactly 2*fc(p) edges total
(fc(p) arrivals + fc(p) departures). The crossings of any particular
cut by proc p equals the number of times p uses that edge.

Hmm, let me think about this differently.

The walk is a closed path of length L = sum(ms). Each step uses one
ring edge. For any cut of the ring (between proc a and proc a+1),
the walk crosses this cut some number of times. Since the walk is
closed and has zero winding, the number of CW crossings = CCW crossings.
So total crossings = 2 * (CW crossings), which is EVEN.

For a turnaround binary b (both fires bounce):
- b's fires use 4 edge-uses total (2 arrivals + 2 departures).
- Same-side LEFT: all 4 on edge (b-1, b). Cut (b, b+1): 0 from b.
- Same-side RIGHT: all 4 on edge (b, b+1). Cut (b-1, b): 0 from b.
- Mixed: 2 on (b-1, b), 2 on (b, b+1). Each cut: 2 from b.

The key constraint: with ≥3 binary all-turnaround and zero winding,
the walk segments between binary firings must also maintain zero
winding. Let me look at this from the excursion perspective.

An "excursion" is the walk between two consecutive firings of a given
proc. For binary b, there are 2 excursions.

A turnaround excursion starts and ends at the same side of b.
It has zero net displacement relative to b (leaves to side X, returns from X).
It's a "loop" that goes out and comes back.

If ALL binary are turnaround, the walk decomposes into excursions
that are all loops. The winding number of the full cycle is the
sum of winding contributions from each excursion.

But a loop excursion from b going LEFT can still wrap around the ring!
If it goes left, passes many procs, eventually wraps around and
approaches b from the LEFT again. That would contribute ±1 winding.

Wait — the walk must return to b from the same side it left.
If it left going LEFT (to b-1), it must return arriving from LEFT (from b-1).
This means the last step before arriving back at b is b-1 -> b.

For a LEFT turnaround excursion that wraps around:
Goes b -> b-1 -> b-2 -> ... -> b+1 -> b? NO! It must arrive from b-1.
So it can't wrap. It must stay on the LEFT side.

ACTUALLY WAIT. The excursion goes from b to b-1, then the walk continues.
It visits other procs. It could go: b-1, b-2, ..., or b-1, b, but b
can't fire again during this excursion. Eventually it must come BACK to b.
Coming back means the walk reaches b-1 and then steps to b.

Can the walk during this excursion wrap around the ring? YES! The walk
goes b -> b-1 -> ... and could go b-1, b-2, ..., b+2, b+1, and then
it's right next to b from the RIGHT. But the excursion must end with
arrival from the LEFT (since it's a LEFT turnaround). So from b+1,
the walk must NOT step to b, but go back: b+1, b+2, ..., b-1, b.
That wraps TWICE. Very expensive in terms of steps.

For a sub-threshold cycle (short total length), wrapping is expensive.
Let me check whether wrapping ever happens.
"""

def neighbors(p, n):
    return [(p - 1) % n, (p + 1) % n]

def enumerate_good_cycles(n, ms):
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
    L = len(mover_word)
    fires = [i for i in range(L) if mover_word[i] == b]
    assert len(fires) == 2

    fire_info = []
    for idx in fires:
        prev_mover = mover_word[(idx - 1) % L]
        next_mover = mover_word[(idx + 1) % L]
        left, right = (b - 1) % n, (b + 1) % n
        arr = 'L' if prev_mover == left else 'R'
        dep = 'L' if next_mover == left else 'R'
        fire_info.append((arr, dep))

    is_turnaround = all(arr == dep for arr, dep in fire_info)
    return {'fires': fires, 'fire_info': fire_info, 'turnaround': is_turnaround}


def get_excursions(mover_word, b, n):
    """
    Get the two excursions of binary proc b.
    Excursion k: walk from fire k to fire k+1 (not including the fires themselves).
    Returns the movers in each excursion and the departure/arrival sides.
    """
    L = len(mover_word)
    fires = [i for i in range(L) if mover_word[i] == b]
    assert len(fires) == 2

    excursions = []
    for k in range(2):
        start = (fires[k] + 1) % L  # first step after fire k
        end = fires[(k + 1) % 2]     # fire k+1

        movers = []
        i = start
        while i != end:
            movers.append(mover_word[i])
            i = (i + 1) % L

        # Departure side of fire k
        dep_side = mover_word[start] if movers else None
        # Arrival side of fire k+1
        arr_proc = mover_word[(end - 1) % L] if movers else None

        # Compute winding of this excursion
        exc_path = [b] + movers + [b]
        exc_winding = 0
        for j in range(len(exc_path) - 1):
            curr = exc_path[j]
            nxt = exc_path[j + 1]
            if nxt == (curr + 1) % n:
                exc_winding += 1
            elif nxt == (curr - 1) % n:
                exc_winding -= 1

        excursions.append({
            'movers': movers,
            'length': len(movers),
            'dep_side': dep_side,
            'arr_proc': arr_proc,
            'winding': exc_winding,
        })

    return excursions


def main():
    print("=" * 70)
    print("EXCURSION ANALYSIS FOR TURNAROUND BINARY")
    print("=" * 70)

    # For each turnaround binary, check:
    # 1. Do excursions wrap around the ring?
    # 2. What's the winding of each excursion?
    # 3. How many procs does each excursion visit?

    n = 5
    for bp in [(0,1,2), (0,1,3), (0,2,4)]:
        ms = [3] * n
        for b in bp: ms[b] = 2

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

        print(f"\nbp={bp}, ms={ms}")
        for cyc in filtered:
            for b in bp:
                info = classify_binary_firing(cyc, b, n)
                if not info['turnaround']:
                    continue
                excs = get_excursions(cyc, b, n)
                sides = [fi[0] for fi in info['fire_info']]
                print(f"  Cycle {cyc}, binary {b} TA sides={sides}")
                for ei, exc in enumerate(excs):
                    print(f"    Exc {ei}: len={exc['length']}, winding={exc['winding']}, movers={exc['movers']}")

    # ============================================================
    # KEY: count edges used at each cut, for turnaround procs
    # ============================================================
    print("\n\n" + "=" * 70)
    print("EDGE BUDGET ARGUMENT")
    print("=" * 70)

    # In a good cycle with sum(ms) = L steps:
    # Total edge uses = L (each step uses one edge).
    # For edge (p, p+1): #uses(p, p+1) = # CW crossings + # CCW crossings.
    # Zero winding => CW = CCW at each cut.
    # cwSteps > 0 => at least one edge has CW crossings > 0.

    # Binary b with fc=2: contributes 4 edge-uses (arrival+departure for each fire).
    # Ternary t with fc=3: contributes 6 edge-uses.
    # Total edge-uses = 2 * L = 2 * sum(ms).
    # Wait, no. L steps = L edge-uses. Not 2L.
    # Each step is one edge-use. L = sum(ms).

    # Hmm, actually each STEP is one edge-use. But I was thinking of
    # each fire having an arrival edge and a departure edge. That's 2 per fire.
    # 2 * L edges... but the walk has L steps, so L edge-uses.
    # Arrival at step i = departure of step i-1. They share the edge.

    # Let me recount. A step goes from mover[i] to mover[i+1].
    # That's one edge-use. Total: L edge-uses.

    # A turnaround binary b at LEFT:
    # Its 2 fires appear at positions idx1, idx2 in the mover word.
    # Steps involving b's fires:
    #   Step idx1-1: prev -> b (arrival edge)
    #   Step idx1: b -> next (departure edge)
    # These are 2 separate edge-uses per fire, but counted in the total L.

    # OK let me just directly count: for each edge of the ring,
    # how many of the L steps use that edge?

    print("\nEdge-use counts per ring-edge:")
    n = 5
    bp = (0, 1, 3)
    ms = [2, 2, 3, 2, 3]
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

    for cyc in filtered:
        L = len(cyc)
        print(f"\nCycle {cyc}, L={L}")
        for e in range(n):
            cw = 0
            ccw = 0
            for i in range(L):
                curr = cyc[i]
                nxt = cyc[(i+1) % L]
                if curr == e and nxt == (e+1) % n:
                    cw += 1
                elif curr == (e+1) % n and nxt == e:
                    ccw += 1
            print(f"  Edge {e}-{(e+1)%n}: CW={cw}, CCW={ccw}, total={cw+ccw}")

    # ============================================================
    # DEFINITIVE TEST: For all n up to where enumeration works,
    # is all-turnaround truly impossible?
    # ============================================================
    print("\n\n" + "=" * 70)
    print("DEFINITIVE ALL-TURNAROUND CHECK (all placements, all n)")
    print("=" * 70)

    from itertools import combinations

    for n in [5, 7]:
        threshold = 4 * 3**(n-2)
        all_ta_total = 0

        # Try ALL placements of ≥3 binary
        for num_binary in [3, 4, 5]:
            if num_binary > n:
                continue
            for bp in combinations(range(n), num_binary):
                ms = [3] * n
                for b in bp:
                    ms[b] = 2
                prod = 1
                for m in ms: prod *= m
                if prod >= threshold:
                    continue

                cycles = enumerate_good_cycles(n, ms)
                for cyc in cycles:
                    winding = get_winding_number(cyc, n)
                    if winding != 0: continue
                    cw = count_cw_steps(cyc, n)
                    if cw == 0: continue
                    fc = get_firing_counts(cyc, n)
                    if any(f < 2 for f in fc): continue
                    if not any(f >= 3 for f in fc): continue

                    # Check if ALL binary are turnaround
                    all_ta = True
                    for b in bp:
                        info = classify_binary_firing(cyc, b, n)
                        if not info['turnaround']:
                            all_ta = False
                            break
                    if all_ta:
                        all_ta_total += 1
                        print(f"  FOUND ALL-TA: n={n}, bp={bp}, ms={ms}, cycle={cyc}")

        print(f"n={n}: total all-turnaround cycles (with fc>=3 somewhere) = {all_ta_total}")


if __name__ == '__main__':
    main()
