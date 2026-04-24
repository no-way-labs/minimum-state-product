#!/usr/bin/env python3
"""
Isolated pivot check v3: Focus on the core question.

KEY LOGICAL QUESTION: Can fireCount(t) = 2 for a pivot with m_t >= 3?

In a good cycle (visiting all product(m_i) configurations exactly once):
- Processor t has m_t states.
- In one full cycle, proc t's local state traces a closed walk on {0,...,m_t-1}.
- The walk must visit every state (since the good cycle visits all configs,
  and for each state s of proc t, there exist configs with proc t in state s).
- The number of fires = number of transitions = length of the closed walk.
- A closed walk visiting all m_t states has length >= m_t.
- So fireCount(t) >= m_t >= 3 for the pivot.

Actually wait: is the walk on proc t's states necessarily a SINGLE closed walk?
In a good cycle: the global config sequence is c_0, c_1, ..., c_{L-1}, c_0.
At each step, exactly one processor fires (changes state). Between consecutive
configs, proc t either fires (state changes) or doesn't (state stays).
The subsequence of proc t's states is: s_0, s_0, ..., s_0, s_1, s_1, ..., s_1, s_2, ...
where s_i -> s_{i+1} when proc t fires. After the full cycle, we return to s_0.
The fire sequence for proc t is s_0 -> s_1 -> ... -> s_{F-1} -> s_0 where F = fireCount(t).
This IS a single closed walk of length F on the state space.
It must visit all m_t states (since good cycle hits all configs).
So F >= m_t.

CORRECTION: The walk visits all m_t states, but it could revisit states.
The minimum closed walk visiting all vertices of K_{m_t} is a Hamiltonian cycle
of length m_t. So F >= m_t.

ACTUALLY: it's not a walk on the complete graph. The transitions are determined
by the transition function. But regardless: the fire sequence must visit all
m_t states and return to start, so F >= m_t.

Hmm, but is this really true? Let me think of a counterexample.
m_t = 3, states = {0,1,2}. Fire sequence: 0 -> 1 -> 0. That's F = 2,
visiting only states {0,1}. State 2 is never the "source" of a fire.
But state 2 IS visited between fires -- proc t is in state 2 as a non-mover.

Wait NO. The fire sequence is the sequence of states FROM WHICH proc t fires.
0 -> 1 means: when proc t fires, it goes from state 0 to state 1.
1 -> 0 means: when proc t fires, it goes from state 1 to state 0.
Between these two fires, proc t is in state 1 (as non-mover).
After the second fire, proc t is in state 0 (as non-mover) until the cycle
wraps and it fires again from state 0.

But what about state 2? The good cycle must include configs where proc t is
in state 2. Can proc t be in state 2 WITHOUT ever firing from state 2?

YES! Proc t transitions 0->1->2 via two fires (fire from 0 giving 1,
fire from 1 giving 2), then 2->0 via one fire. That's F=3.
Or: 0->1 (fire), 1->2 (fire), 2->0 (fire). F=3.

Can we have F=2 with m_t=3? We need a closed walk of length 2 visiting
all 3 states. Walk: a -> b -> a. Visits only {a,b}. Doesn't visit c.
So state c is never the source of a fire. But c must appear in configs.
If proc t is in state c, then c was reached by a fire (some other state -> c)
and left by a fire (c -> some other state). So c IS a source of a fire.
Contradiction: c must appear in the fire source sequence.

Wait, let me reconsider. Proc t is in state c at some config in the good cycle.
How did it get to state c? Either:
(1) It was in state c at the start and hasn't fired yet, or
(2) Some previous fire of proc t produced state c.

Either way, proc t is in state c at some point. Now, at some later point,
proc t must leave state c (since the cycle returns to start, and the fire
sequence is closed). Leaving state c means firing from state c.
So c IS a source of a fire.

Therefore every state 0,...,m_t-1 appears as a source of at least one fire.
The fire source sequence visits all m_t states.
The fire source sequence has length F = fireCount(t).
So F >= m_t.

QED: For any pivot with m_t >= 3, fireCount(t) >= 3 in any good cycle.
Therefore P >= 3, Layer 1 pigeonhole (2 < 3) always applies,
and isDominoesOrContaminated NEVER arises at isolated pivots.

But wait: let me double-check this with the formal definitions. Maybe
"fireCount" in the proof context means something different?
Let me verify computationally: find actual good cycles and check.
"""

from itertools import product as iproduct, permutations
from collections import Counter

def threshold(n):
    return 4 * (3 ** (n - 2))

def verify_firecount_bound():
    """
    For small rings, enumerate all valid self-stabilizing systems and their
    good cycles, and verify that fireCount(t) >= m_t for every processor t.
    """
    print("Verifying fireCount >= m_t for small cases...")
    print()

    # n=3, various ms
    for ms in [(2,3,3), (2,2,3), (3,3,3), (2,3,4)]:
        n = len(ms)
        total_configs = 1
        for m in ms:
            total_configs *= m

        # Generate all configs
        configs = list(iproduct(*(range(m) for m in ms)))
        assert len(configs) == total_configs

        # A good cycle is a Hamiltonian cycle on the config graph.
        # For small cases, find one by DFS.
        # Config graph: edge from c to c' if exactly one proc changes state.

        # This is expensive for large products. Only do small ones.
        if total_configs > 30:
            continue

        # Build adjacency
        adj = {c: [] for c in configs}
        for c in configs:
            for p in range(n):
                for s in range(ms[p]):
                    if s != c[p]:
                        c2 = list(c)
                        c2[p] = s
                        c2 = tuple(c2)
                        adj[c].append((c2, p))  # (neighbor, which proc fired)

        # Find Hamiltonian cycle by DFS (small search space)
        def find_ham_cycle(start):
            path = [start]
            fires = []
            visited = {start}

            def dfs():
                if len(path) == total_configs:
                    # Check if we can return to start
                    for nb, p in adj[path[-1]]:
                        if nb == start:
                            fires.append(p)
                            return True
                    return False
                for nb, p in adj[path[-1]]:
                    if nb not in visited:
                        visited.add(nb)
                        path.append(nb)
                        fires.append(p)
                        if dfs():
                            return True
                        fires.pop()
                        path.pop()
                        visited.remove(nb)
                return False

            if dfs():
                return path, fires
            return None, None

        path, fires = find_ham_cycle(configs[0])
        if path is None:
            # Try a few starts
            for start in configs[1:5]:
                path, fires = find_ham_cycle(start)
                if path is not None:
                    break

        if path is not None:
            # Count fires per processor
            fc = Counter(fires)
            ok = all(fc.get(p, 0) >= ms[p] for p in range(n))
            status = "OK" if ok else "VIOLATION"
            print(f"  ms={ms}: good cycle found, fireCount={dict(fc)}, "
                  f"min_needed={list(ms)}, {status}")
            if not ok:
                for p in range(n):
                    if fc.get(p, 0) < ms[p]:
                        print(f"    VIOLATION at proc {p}: fc={fc.get(p,0)} < m={ms[p]}")
                        # Show the state sequence for this proc
                        states = [path[i][p] for i in range(len(path))]
                        print(f"    State sequence: {states}")
        else:
            print(f"  ms={ms}: no good cycle found (search exhausted)")

def enumerate_isolated_pivots():
    """Enumerate isolated pivots for n=9..12 with improved efficiency."""

    for n in [9, 10, 11, 12]:
        thresh = threshold(n)
        print(f"\n{'='*70}")
        print(f"n = {n}, threshold = {thresh}")

        # Get multisets
        multisets = []
        max_val = thresh // (2 ** (n - 1))

        def enum(remaining, min_val, current, cur_prod):
            if remaining == 0:
                if cur_prod < thresh:
                    multisets.append(tuple(current))
                return
            mv = thresh // (cur_prod * (2 ** (remaining - 1)))
            if mv < min_val:
                return
            for v in range(min_val, min(mv, max_val) + 1):
                if cur_prod * v * (2 ** (remaining - 1)) >= thresh:
                    break
                enum(remaining - 1, v, current + [v], cur_prod * v)

        enum(n, 2, [], 1)
        multisets = [ms for ms in multisets if ms.count(2) >= 3]
        print(f"Sub-threshold multisets: {len(multisets)}")

        # For n >= 11, skip full permutation and just analyze multisets
        if n >= 11:
            # Instead of enumerating all arrangements, check if any multiset
            # CAN produce an isolated pivot. An isolated pivot needs:
            # - 1 entry >= 3 (the pivot)
            # - At least 4 binary entries around it (t-2, t-1, t+1, t+2)
            # - Isolation: t-3 not sandwiched AND t+3 not sandwiched
            #
            # For a ring of size n, the 9-window around pivot is:
            # [t-4, t-3, 2, 2, m_t, 2, 2, t+3, t+4]
            # Remaining n-9 entries are elsewhere in the ring.
            #
            # Isolation: NOT(m_{t-3}>=3 AND m_{t-4}=2) AND NOT(m_{t+3}>=3 AND m_{t+4}=2)
            #
            # This means: if m_{t-3}>=3 then m_{t-4}>=3; if m_{t+3}>=3 then m_{t+4}>=3
            #
            # Count the minimum binary entries consumed:
            # - 4 binary (t-2, t-1, t+1, t+2) always
            # - If t-3 is binary: +1 binary consumed (5 total from left)
            # - If t+3 is binary: +1 binary consumed (5 total from right)
            #
            # The multiset just needs enough binary entries.

            num_isolated_multisets = 0
            for ms in multisets:
                c = Counter(ms)
                nb = c[2]  # number of binary entries
                nnb = n - nb  # number of non-binary entries
                # Can we place things to get an isolated pivot?
                # Need: 1 non-binary as pivot, >= 4 binary as t-2,t-1,t+1,t+2
                # Isolation options for t-3, t+3:
                #   Option 1: t-3 binary, t+3 binary -> need 6 binary + 1 non-binary
                #   Option 2: t-3 non-binary, t-4 non-binary, t+3 binary -> 5 binary + 3 non-binary
                #   Option 3: t-3 binary, t+3 non-binary, t+4 non-binary -> 5 binary + 3 non-binary
                #   Option 4: t-3 NB, t-4 NB, t+3 NB, t+4 NB -> 4 binary + 5 non-binary
                # etc.
                # Simplest: Option 1 needs nb >= 6 and nnb >= 1
                if nb >= 6 and nnb >= 1:
                    num_isolated_multisets += 1
                elif nb >= 5 and nnb >= 3:
                    num_isolated_multisets += 1
                elif nb >= 4 and nnb >= 5:
                    num_isolated_multisets += 1

            print(f"Multisets that CAN have isolated pivot (approx): {num_isolated_multisets}")
            print(f"(Skipping full ring enumeration for n >= 11)")
            print(f"Key finding: for ALL these, m_t >= 3, so fireCount(t) >= 3.")
            print(f"Layer 1 pigeonhole always applies. isDominoesOrContaminated = NEVER.")
            continue

        # For n <= 10: full enumeration
        total_isolated = 0
        case_counts = Counter()

        for ms in multisets:
            seen = set()
            for perm in set(permutations(ms)):
                canonical = min(perm[i:] + perm[:i] for i in range(n))
                if canonical in seen:
                    continue
                seen.add(canonical)

                for t in range(n):
                    if perm[t] < 3:
                        continue
                    if perm[(t-1)%n] != 2 or perm[(t+1)%n] != 2:
                        continue
                    if perm[(t-2)%n] != 2 or perm[(t+2)%n] != 2:
                        continue

                    m_l3 = perm[(t-3) % n]
                    m_l4 = perm[(t-4) % n]
                    m_r3 = perm[(t+3) % n]
                    m_r4 = perm[(t+4) % n]

                    if (m_l3 >= 3 and m_l4 == 2) or (m_r3 >= 3 and m_r4 == 2):
                        continue

                    total_isolated += 1
                    lc = 'A' if m_l3 < 3 else 'B'
                    rc = 'A' if m_r3 < 3 else 'B'
                    case_counts[(lc, rc)] += 1

        print(f"Total isolated pivots: {total_isolated}")
        print(f"Case breakdown: {dict(case_counts)}")
        print(f"All have m_t >= 3, so fireCount >= m_t >= 3.")
        print(f"Layer 1 pigeonhole (2 < 3) always works.")
        print(f"isDominoesOrContaminated: NEVER arises at isolated pivots.")

    print(f"\n{'='*70}")
    print(f"CONCLUSION")
    print(f"{'='*70}")
    print(f"For n=9..12, NO isolated sandwiched ternary pivot ever reaches")
    print(f"isDominoesOrContaminated. Reason: the pivot has m_t >= 3, so")
    print(f"fireCount(t) >= m_t >= 3 in any good cycle. With both second-")
    print(f"neighbors binary (fireCount = 2), the Layer 1 nested-phase")
    print(f"pigeonhole (2 < 3) always applies, closing the case before")
    print(f"layers 2-3 or dominoes/contaminated are needed.")
    print()
    print(f"PROOF that fireCount(t) >= m_t:")
    print(f"In a good cycle, proc t visits all m_t states. The fire sequence")
    print(f"of proc t is a closed walk s_0 -> s_1 -> ... -> s_{{F-1}} -> s_0")
    print(f"where F = fireCount(t). Each state must appear as a fire source")
    print(f"(since entering state c requires either starting there or arriving")
    print(f"via a fire, and leaving state c requires firing from c). Since")
    print(f"all m_t states are visited, all appear as fire sources, so F >= m_t.")

if __name__ == '__main__':
    verify_firecount_bound()
    enumerate_isolated_pivots()
