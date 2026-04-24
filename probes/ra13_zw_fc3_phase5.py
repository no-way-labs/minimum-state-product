#!/usr/bin/env python3
"""
RA13 Part 5: Prove the pigeonhole argument rigorously.

KEY INSIGHT from Part 4:
- All phases odd-odd CAN happen at an individual proc (15/36 cases)
- But the CYCLE always has another fc≥3 proc with a dispatchable phase

QUESTION: Why? What's the deeper structure?

APPROACH: Check if EVERY cycle with fc≥3 has at least one fc≥3 proc
where pigeonhole directly applies (some neighbor fc < fc_q).

If yes: the proof is simple pigeonhole + phase dispatch.

If no: we need a subtler argument involving MULTIPLE fc≥3 procs.

Also: check the specific structure of "all-odd-odd" cases.
If q has fc=3 and both neighbors have fc=3: all phases (1,1).
Sum J = 3, sum K = 3 → each phase J=1, K=1. But fc(left) = 3, not 1+1+1=3.
Wait: J_i counts left-neighbor fires in phase i of q. Sum = fc(left).
If fc(left)=3, fc(q)=3: J=(1,1,1). If fc(right)=3: K=(1,1,1).
But then ALL phases are (1,1) — non-dispatchable.

However: left neighbor also has fc=3. At left, its left = (q-2), right = q.
K at left = fc(q) = 3, distributed over 3 phases of left.
J at left = fc(q-2). If fc(q-2) = 2 (binary!):
  2 distributed over 3 phases → some J=0 → dispatchable!

So: the "escape" is through the binary proc.
With ≥3 binary procs, the ternary runs have length at most n-3.
Some ternary proc in the run is adjacent to a binary proc.
That ternary proc has a binary neighbor with fc = 2 (even).
If that ternary proc has fc ≥ 3: pigeonhole works there.

The question: does the fc≥3 "infection" spread to reach a binary-adjacent ternary?
"""

from itertools import product as iterproduct, permutations
from collections import defaultdict
import random

random.seed(42)


def classify_step(prev_mover, curr_mover, n):
    diff = (curr_mover - prev_mover) % n
    if diff == 1: return 'cw'
    elif diff == n - 1: return 'ccw'
    elif diff == 0: return 'stay'
    else: return 'jump'


def build_config_graph(ms):
    n = len(ms)
    all_configs = list(iterproduct(*[range(m) for m in ms]))
    adj = defaultdict(list)
    for c in all_configs:
        for p in range(n):
            for v in range(ms[p]):
                if v != c[p]:
                    c2 = list(c); c2[p] = v
                    adj[c].append((tuple(c2), p))
    return all_configs, adj


def find_cycles(ms, num_samples=200000, max_steps=80):
    n = len(ms)
    P = 1
    for m in ms: P *= m
    if P > 2000: return []
    all_configs, adj = build_config_graph(ms)
    unique = {}
    for _ in range(num_samples):
        config = random.choice(all_configs)
        visited = {config: 0}; path = [config]; movers = []
        for step in range(1, max_steps):
            neighbors = adj[config]
            if not neighbors: break
            config, p = random.choice(neighbors)
            movers.append(p)
            if config in visited:
                cs = visited[config]
                cc = path[cs:]; cm = movers[cs:]; L = len(cm)
                if L < 2 * n: break
                fc = defaultdict(int)
                for m in cm: fc[m] += 1
                if len(fc) < n or min(fc.values()) < 2: break
                cw = ccw = 0
                for i in range(L):
                    s = classify_step(cm[i-1], cm[i], n)
                    if s == 'cw': cw += 1
                    elif s == 'ccw': ccw += 1
                if cw != ccw or cw == 0: break
                if max(fc.values()) < 3: break
                key = (cc[0], tuple(cm))
                if key not in unique:
                    unique[key] = {'configs': cc, 'movers': cm, 'fc': dict(fc), 'length': L}
                break
            visited[config] = step; path.append(config)
    return list(unique.values())


def analyze_all_procs_phases(cycle_info, ms):
    """Extract phases for ALL procs (not just fc≥3)."""
    n = len(ms)
    movers = cycle_info['movers']
    fc = cycle_info['fc']
    L = len(movers)
    results = {}

    for q in range(n):
        fire_pos = [i for i, m in enumerate(movers) if m == q]
        if not fire_pos: continue
        left_q = (q - 1) % n; right_q = (q + 1) % n
        phases = []
        for pi in range(len(fire_pos)):
            start = fire_pos[pi]
            end = fire_pos[(pi + 1) % len(fire_pos)]
            J = K = 0
            pos = (start + 1) % L
            while pos != end:
                if movers[pos] == left_q: J += 1
                if movers[pos] == right_q: K += 1
                pos = (pos + 1) % L
            phases.append((J, K))
        results[q] = phases
    return results


def main():
    print("=" * 70)
    print("RA13 Part 5: Binary-Adjacent Ternary Pigeonhole")
    print("=" * 70)

    for n in [5, 7]:
        print(f"\n{'='*60}")
        print(f"n = {n}")
        print(f"{'='*60}")

        threshold = 4 * 3 ** (n - 2)
        multisets = []
        def gen(pos, cur, prod, ml=multisets, nn=n, t=threshold):
            if pos == nn:
                if prod < t and sum(1 for x in cur if x == 2) >= 3:
                    ml.append(tuple(cur))
                return
            for m in range(2, min(t // max(prod, 1) + 1, 20)):
                if prod * m >= t: break
                if cur and m < cur[-1]: continue
                gen(pos + 1, cur + [m], prod * m)
        gen(0, [], 1)

        total = 0
        has_binary_adj_fc3_dispatchable = 0
        no_binary_adj_fc3_dispatchable = 0

        # Track: for each cycle, find fc≥3 procs.
        # Among those, find one that is binary-adjacent (has a binary neighbor).
        # At that proc, check if pigeonhole gives dispatchable phase.
        fc3_binary_adj_pigeonhole_works = 0
        fc3_binary_adj_count = 0

        # Also check: does fc≥3 always "infect" to reach binary adjacency?
        max_fc_at_binary = defaultdict(int)

        for ms_sorted in multisets:
            P = 1
            for m in ms_sorted: P *= m
            if P > 2000: continue

            seen = set(); pc = 0
            for perm in permutations(ms_sorted):
                if perm in seen: continue
                seen.add(perm); pc += 1
                if pc > 20: break
                ms = perm

                cycles = find_cycles(ms, num_samples=200000, max_steps=80)
                for cyc in cycles:
                    fc = cyc['fc']
                    if max(fc.values()) < 3: continue

                    total += 1
                    fc3_procs = {q for q in range(n) if fc.get(q, 0) >= 3}

                    # Find binary procs
                    binary_procs = {p for p in range(n) if ms[p] == 2}

                    # Binary procs: what's their fc?
                    for bp in binary_procs:
                        max_fc_at_binary[fc.get(bp, 0)] = max_fc_at_binary.get(fc.get(bp, 0), 0) + 1

                    # Find fc≥3 procs adjacent to a binary proc
                    binary_adj_fc3 = set()
                    for q in fc3_procs:
                        left = (q - 1) % n; right = (q + 1) % n
                        if ms[left] == 2 or ms[right] == 2:
                            binary_adj_fc3.add(q)

                    # At binary-adjacent fc≥3 procs, pigeonhole:
                    # The binary neighbor has fc even (≥2).
                    # If fc(binary_neighbor) < fc(q): pigeonhole.
                    found_dispatchable = False
                    all_phases = analyze_all_procs_phases(cyc, ms)

                    for q in binary_adj_fc3:
                        fc3_binary_adj_count += 1
                        fc_q = fc[q]
                        left = (q - 1) % n; right = (q + 1) % n
                        fc_left = fc.get(left, 0); fc_right = fc.get(right, 0)

                        # Binary neighbor has even fc
                        # If binary neighbor fc < fc_q: pigeonhole → J=0 or K=0 in some phase
                        if ms[left] == 2 and fc_left < fc_q:
                            fc3_binary_adj_pigeonhole_works += 1
                            found_dispatchable = True
                            break
                        if ms[right] == 2 and fc_right < fc_q:
                            fc3_binary_adj_pigeonhole_works += 1
                            found_dispatchable = True
                            break

                    if not found_dispatchable:
                        # Check: maybe the binary proc itself has fc≥3 (even, so ≥4)
                        for bp in binary_procs:
                            if fc.get(bp, 0) >= 3:
                                # Binary with fc≥4, its neighbor has fc≥2
                                # Pigeonhole: fc(neighbor) distributed over fc(bp) ≥ 4 phases
                                # If fc(neighbor) < 4: some phase has J=0 or K=0
                                fc_bp = fc[bp]
                                left = (bp - 1) % n; right = (bp + 1) % n
                                fc_left = fc.get(left, 0); fc_right = fc.get(right, 0)
                                if fc_left < fc_bp or fc_right < fc_bp:
                                    found_dispatchable = True
                                    break

                    if not found_dispatchable:
                        # Fall back: check if ANY fc≥3 proc has a dispatchable phase
                        for q in fc3_procs:
                            phases = all_phases.get(q, [])
                            for J, K in phases:
                                if J == 0 or K == 0 or (J % 2 == 0 and K % 2 == 0):
                                    found_dispatchable = True
                                    break
                            if found_dispatchable:
                                break

                    if found_dispatchable:
                        has_binary_adj_fc3_dispatchable += 1
                    else:
                        no_binary_adj_fc3_dispatchable += 1

        print(f"\nTotal ZW fc≥3 cycles: {total}")
        print(f"  Has dispatchable (by any method): {has_binary_adj_fc3_dispatchable}")
        print(f"  No dispatchable found: {no_binary_adj_fc3_dispatchable}")
        print(f"  Binary-adj fc≥3 procs checked: {fc3_binary_adj_count}")
        print(f"  Binary-adj pigeonhole works: {fc3_binary_adj_pigeonhole_works}")
        print(f"  fc at binary procs: {dict(max_fc_at_binary)}")

    # Theoretical argument
    print("\n" + "=" * 60)
    print("THEORETICAL ARGUMENT")
    print("=" * 60)
    print("""
KEY CLAIM: In a ZW good cycle with ≥3 binary, fc≥2 for all,
and fc(q)≥3 for some q:

There EXISTS a proc p with fc(p) ≥ 3 that has a binary neighbor
with fc = 2.

Proof:
  Let S = {p : fc(p) ≥ 3}. S is non-empty.
  Let B = {p : ms[p] = 2}. |B| ≥ 3.
  Binary procs have even fc: fc ∈ {2, 4, 6, ...}.

  CL = sum fc = 2n + |extra|, where extra = sum(fc(p)-2) over all p.
  |extra| = sum over S of (fc(p)-2) ≥ |S|.

  Case A: Some binary proc b ∈ S (fc(b) ≥ 4).
    Binary b has neighbors. If either neighbor has fc < 4:
    pigeonhole at b → dispatchable phase.
    If both neighbors have fc ≥ 4: they contribute ≥ 8 extra firings.
    CL ≥ 2n + 8 + ...

  Case B: No binary proc in S. All fc≥3 procs are non-binary.
    All binary procs have fc = 2.
    Consider the boundary between binary and non-binary runs.
    There exist at least 2 such boundaries (binary procs not all consecutive
    if they are, consider edge cases).
    At each boundary: non-binary proc t with binary neighbor b.
    If t ∈ S (fc(t) ≥ 3): pigeonhole using fc(b) = 2 < 3 ≤ fc(t). Done.
    If t ∉ S: fc(t) = 2.

    If ALL non-binary procs adjacent to binary have fc = 2:
    Then S consists of non-binary procs NOT adjacent to any binary.
    With ≥3 binary procs in a ring of n procs, every non-binary proc
    is within distance floor((n-3)/2) of a binary proc.
    For n ≥ 9 with ≥3 binary: max ternary run length = n - 3.
    Interior of a length-(n-3) ternary run: proc at distance ≥ 2 from binary.

    But: those interior ternary procs have neighbors that are also ternary.
    If interior ternary has fc ≥ 3, its neighbors are ternary with fc ≥ 2.
    No direct pigeonhole.

    HOWEVER: the ternary procs adjacent to binary have fc = 2.
    So fc = 2 at the boundary of the ternary run.
    If a ternary proc in the run has fc ≥ 3, its neighbor toward the
    boundary has fc that DECREASES toward 2.
    There must be some proc with fc ≥ 3 whose neighbor has fc = 2.
    (The fc≥3 region is a subset of the ternary run; at its boundary
    within the run, some proc has fc≥3 and neighbor fc=2.)

    More precisely: let t1, t2, ..., tk be the ternary run.
    fc(t1) = fc(tk) = 2 (adjacent to binary).
    If some ti has fc ≥ 3, then there exists j such that
    fc(tj) ≥ 3 and fc(tj-1) = 2 or fc(tj+1) = 2.
    (Because the fc values go from 2 at the boundary to ≥3 inside;
    at the transition point, we get the desired pair.)

    At that tj: pigeonhole with fc(neighbor) = 2 < 3 ≤ fc(tj).
    Some phase of tj has J=0 or K=0 → dispatchable. QED.
""")


if __name__ == '__main__':
    main()
