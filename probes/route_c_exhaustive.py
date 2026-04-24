#!/usr/bin/env python3
"""Exhaustive check: can a long-arc mover sequence form a valid good cycle?

For SMALLER n (n=5,7) where the arc is shorter, also check.
At n=5: arc has 3 movers. Should find valid cycles (mixed phases exist at n=5).
At n=7: arc has 5 movers. Borderline.
At n=9: arc has 7 movers. Expect none.
"""
from itertools import product as iterproduct

def ring_adj(a, b, n):
    return min((a-b)%n, (b-a)%n) <= 1

def find_long_arc_cycles(n, ms, t, max_phase2_len=4):
    """Exhaustive search for good cycles containing a long-arc mixed phase."""
    lt = (t-1) % n
    rt = (t+1) % n

    # Build long arc: lt, left²(t), ..., right²(t), rt
    arc = []
    p = lt
    for _ in range(n-2):
        arc.append(p)
        p = (p - 1) % n
        if p == t:
            break
    arc.append(rt)
    if len(arc) != n - 1:
        # Try the other direction
        arc = []
        p = lt
        for _ in range(n-2):
            arc.append(p)
            p = (p + 1) % n
            if p == t:
                p = (p + 1) % n
        # This doesn't work either. Build manually.
        arc = []
        p = lt
        while len(arc) < n - 1:
            arc.append(p)
            p = (p - 1) % n
            if p == t:
                p = (p - 1) % n

    if len(arc) != n - 1 or arc[0] != lt or arc[-1] != rt:
        print(f"  Arc construction failed: {arc}")
        return 0

    # Phase 1: arc + t
    phase1 = arc + [t]

    # Try different phase 2 lengths
    total_found = 0
    total_noec = 0

    for p2_len in range(1, max_phase2_len + 1):
        # Generate all possible phase 2 mover sequences of given length
        # that end with t and are all ring-adjacent
        def gen_phase2(length, current_movers):
            if len(current_movers) == length:
                # Must end with t
                if current_movers[-1] != t:
                    return
                # Check ring-adjacency within phase 2
                for i in range(len(current_movers) - 1):
                    if not ring_adj(current_movers[i], current_movers[i+1], n):
                        return
                # Check ring-adjacency at boundaries
                # Last of phase1 is t, first of phase2 must be adjacent to t
                if not ring_adj(t, current_movers[0], n):
                    return
                # Last of phase2 is t, next is first of phase1 (lt)
                if not ring_adj(current_movers[-1], arc[0], n):
                    return
                yield list(current_movers)
                return
            for p in range(n):
                if len(current_movers) > 0 and not ring_adj(current_movers[-1], p, n):
                    continue
                if len(current_movers) == 0 and not ring_adj(t, p, n):
                    continue
                yield from gen_phase2(length, current_movers + [p])

        for phase2 in gen_phase2(p2_len, []):
            movers = phase1 + phase2
            CL = len(movers)

            # Check no t in phase interiors
            # Phase 1: movers[0:n-2] should not be t (arc movers)
            # Phase 2: movers[n-1:n-1+p2_len-1] should not be t (except last)
            valid_phases = True
            for i in range(n - 2):  # arc part
                if movers[i] == t:
                    valid_phases = False
                    break
            if not valid_phases:
                continue
            for i in range(n - 1, n - 1 + p2_len - 1):
                if i < CL and movers[i] == t:
                    valid_phases = False
                    break
            if not valid_phases:
                continue

            # Try to form a valid good cycle with these movers
            # Enumerate all possible initial configs
            for init in iterproduct(*[range(ms[i]) for i in range(n)]):
                # Try all possible transition choices
                def try_build(step, configs):
                    if step == CL:
                        # Check cycle closure
                        if configs[-1] == configs[0]:
                            # Check all distinct
                            if len(set(configs[:-1])) == CL:
                                return [configs[:-1]]
                        return []

                    p = movers[step]
                    current = list(configs[-1])
                    L_val = current[(p-1)%n]
                    S_val = current[p]
                    R_val = current[(p+1)%n]

                    results = []
                    for new_val in range(ms[p]):
                        if new_val == S_val:
                            continue  # Must change
                        new_config = current[:]
                        new_config[p] = new_val
                        new_tuple = tuple(new_config)

                        # Early termination: if config already seen (and not at end)
                        if step < CL - 1 and new_tuple in set(configs):
                            continue

                        results.extend(try_build(step + 1, configs + [new_tuple]))
                        if results:
                            return results  # Return first found

                    return results

                found = try_build(0, [tuple(init)])
                for cycle_configs in found:
                    total_found += 1
                    # Check EC
                    has_ec = False
                    for p in range(n):
                        mt = set()
                        nmt = set()
                        for k in range(CL):
                            triple = (cycle_configs[k][(p-1)%n],
                                     cycle_configs[k][p],
                                     cycle_configs[k][(p+1)%n])
                            if movers[k] == p:
                                mt.add(triple)
                            else:
                                nmt.add(triple)
                        if mt & nmt:
                            has_ec = True
                            break
                    if not has_ec:
                        total_noec += 1
                        print(f"  ¬EC FOUND! movers={movers}")
                        print(f"    configs={cycle_configs}")
                        return total_noec

    return total_noec

# Test at n=5 first (should find mixed phase ¬EC cycles)
print("n=5 ms=[2,3,2,3,2], t=1 (lt=0 bin, rt=2 bin)")
n, ms, t = 5, [2,3,2,3,2], 1
result = find_long_arc_cycles(n, ms, t, max_phase2_len=4)
print(f"  ¬EC cycles with long arc: {result}")

print("\nn=5 ms=[2,3,2,3,2], t=3 (lt=2 bin, rt=4 bin)")
n, ms, t = 5, [2,3,2,3,2], 3
result = find_long_arc_cycles(n, ms, t, max_phase2_len=4)
print(f"  ¬EC cycles with long arc: {result}")

# Now n=7
print("\nn=7 ms=[2,3,2,3,2,3,3], t=1")
n, ms, t = 7, [2,3,2,3,2,3,3], 1
result = find_long_arc_cycles(n, ms, t, max_phase2_len=3)
print(f"  ¬EC cycles with long arc: {result}")

# n=9 would be too large for exhaustive, but let's try with tight bounds
print("\nn=9 ms=[2,3,2,3,2,3,3,3,3], t=1")
n, ms, t = 9, [2,3,2,3,2,3,3,3,3], 1
print(f"  State space: {2**3 * 3**6} = too large for exhaustive")
print(f"  Trying with phase2_len=2 only...")
result = find_long_arc_cycles(n, ms, t, max_phase2_len=2)
print(f"  ¬EC cycles with long arc: {result}")
