#!/usr/bin/env python3
"""Route C: Can a long-arc walk exist without creating EC at
an intermediate processor?

Key test: construct a minimal cycle with a long-arc mixed phase
and check if ¬EC can hold.

Strategy: Build the simplest possible cycle with a long-arc phase:
- Phase 1: long arc left(t)→left²(t)→...→right(t), then t fires
- Phase 2: one-sided (only L or R fires), then t fires
- Check if ¬EC can hold for this 2-phase cycle.

If no valid ¬EC cycle with a long-arc phase exists: Route C succeeds.
"""
from itertools import product as iterproduct

def check_ec_for_long_arc_cycle(n, ms, t):
    """Try to construct a 2-phase cycle with a long arc in phase 1.

    Phase 1: long arc from left(t) to right(t), then t fires
    Phase 2: some one-sided movers, then t fires

    For simplicity: try all possible initial configs and transition
    functions that produce the long-arc mover sequence.
    """
    lt = (t - 1) % n
    rt = (t + 1) % n

    # Long arc path: left(t), left²(t), ..., right(t)
    # On ring with t removed: going the long way from lt to rt
    arc = []
    p = lt
    while True:
        arc.append(p)
        p = (p - 1) % n  # Go to left²(t), left³(t), etc.
        if p == t:
            p = (p - 1) % n  # Skip t... wait, we shouldn't hit t
            # Actually, going from lt to rt the long way:
            # lt, lt-1, lt-2, ..., rt+2, rt+1, rt
            # But need to avoid t. Since we go from lt to the left:
            # lt, lt-1, ..., 0, n-1, ..., rt+1, rt
            # OR equivalently: lt, left²(t), left³(t), ..., right²(t), rt
            break
        if p == rt:
            arc.append(p)
            break

    # Rebuild arc correctly
    arc = []
    p = lt
    for i in range(n - 2):
        arc.append(p)
        p = (p - 1) % n
        if p == t:
            # This shouldn't happen if we go the right direction
            # Go the other way
            break

    # Actually, the long arc on ring\{t} from lt to rt:
    # lt → left²(t) → ... → right²(t) → rt
    # This is: (t-1), (t-2), ..., (t+2), (t+1) mod n
    # All avoiding t.
    arc = []
    p = lt  # = (t-1) % n
    visited = set()
    while p != rt and p not in visited:
        arc.append(p)
        visited.add(p)
        # Move away from t on the "left side"
        next_p = (p - 1) % n
        if next_p == t:
            # Shouldn't happen for n >= 5 since we go through n-2 processors
            break
        p = next_p

    arc.append(rt)
    assert len(arc) == n - 1, f"Arc length {len(arc)}, expected {n-1}"
    assert t not in arc

    print(f"  Long arc (n={n}, t={t}): {arc}")
    print(f"  Arc length: {len(arc)} movers")

    # Phase 1 movers: arc + [t]
    # Phase 2 movers: [?] + [t]
    # For minimal cycle: phase 2 has just one mover (L or R) + t

    # Try phase 2 = [lt, t] (just L fires then t fires)
    # Full mover sequence: arc + [t] + [lt, t]
    # Or phase 2 = [rt, t]

    for phase2_movers in [[lt], [rt], [lt, lt], [rt, rt]]:
        movers = arc + [t] + phase2_movers + [t]
        CL = len(movers)

        # Check ring-adjacency
        all_adj = all(
            min((movers[i] - movers[(i+1)%CL]) % n, (movers[(i+1)%CL] - movers[i]) % n) <= 1
            for i in range(CL)
        )
        if not all_adj:
            continue

        print(f"\n  Trying movers: {movers} (CL={CL}, all_adj={all_adj})")

        # Now: try all possible initial configs and check if ¬EC is achievable
        # For each initial config and each valid transition function:
        # compute the cycle and check EC.

        # Enumerate initial configs
        noec_count = 0
        total_count = 0

        for init in iterproduct(*[range(ms[i]) for i in range(n)]):
            init = list(init)

            # Try to find transition functions that produce this mover sequence
            # For each step: the mover fires. The transition function must:
            # 1. Make the mover "privileged" (new value ≠ current)
            # 2. Assign a specific new value

            configs = [tuple(init)]
            valid = True

            for k in range(CL):
                p = movers[k]
                config = list(configs[-1])
                L_val = config[(p-1) % n]
                S_val = config[p]
                R_val = config[(p+1) % n]

                # The mover must change: new_val ≠ S_val
                # Try all possible new values
                new_vals = [v for v in range(ms[p]) if v != S_val]
                if not new_vals:
                    valid = False
                    break

                # For now: try the first valid new value
                # (We should try all, but that's expensive)
                found_any = False
                for new_val in new_vals:
                    new_config = config[:]
                    new_config[p] = new_val
                    new_config_tuple = tuple(new_config)

                    # Check: this config must not already appear in the cycle
                    # (unless it's the last step completing the cycle)
                    if k < CL - 1 and new_config_tuple in configs:
                        continue
                    if k == CL - 1 and new_config_tuple != configs[0]:
                        continue

                    found_any = True
                    configs.append(new_config_tuple)
                    break

                if not found_any:
                    valid = False
                    break

            if not valid or len(configs) != CL + 1:
                continue
            if configs[-1] != configs[0]:
                continue

            # Remove the repeated last config
            configs = configs[:-1]

            # Check all configs are distinct
            if len(set(configs)) != CL:
                continue

            total_count += 1

            # Check for entry conflict
            has_ec = False
            for p in range(n):
                mover_triples = set()
                nonmover_triples = set()
                for k in range(CL):
                    L = configs[k][(p-1)%n]
                    S = configs[k][p]
                    R = configs[k][(p+1)%n]
                    triple = (L, S, R)
                    if movers[k] == p:
                        mover_triples.add(triple)
                    else:
                        nonmover_triples.add(triple)
                if mover_triples & nonmover_triples:
                    has_ec = True
                    break

            if not has_ec:
                noec_count += 1
                print(f"    ¬EC CYCLE FOUND! init={init}")
                print(f"    configs: {configs}")
                print(f"    movers: {movers}")

        print(f"    Valid cycles: {total_count}, ¬EC: {noec_count}")

    return noec_count

# Try n=9
print("Route C: Long-arc EC check at n=9")
print("=" * 60)
n = 9
ms = [2, 2, 2, 3, 3, 3, 3, 3, 3]  # binary at 0,1,2; ternary at 3-8

# Pivot t must be ternary with binary neighbors
# Possible pivots: t=1 (left=0 binary, right=2 binary)
# Actually: t must have ms[left(t)]=2 and ms[right(t)]=2 and ms[t]>=3
# For ms=[2,2,2,3,3,3,3,3,3]: t=1 has left=0 (m=2), right=2 (m=2), m_t=2. NOT ternary.
# We need t with m_t >= 3. So t ∈ {3,4,5,6,7,8}.
# t=3: left=2 (m=2), right=4 (m=3). Not both binary neighbors.
# Actually for non-consecutive binary at positions 0,1,2: no ternary t has both binary neighbors.
# Wait: positions are on a ring. t=8: left=7 (m=3), right=0 (m=2). Only one binary.

# For 3 non-consecutive binary: try ms=[2,3,2,3,2,3,3,3,3]
ms2 = [2, 3, 2, 3, 2, 3, 3, 3, 3]
# t=1: left=0 (m=2), right=2 (m=2), m_t=3. YES!
# t=3: left=2 (m=2), right=4 (m=2), m_t=3. YES!

print(f"\nms={ms2}")
for t in range(n):
    lt = (t-1) % n
    rt = (t+1) % n
    if ms2[t] >= 3 and ms2[lt] == 2 and ms2[rt] == 2:
        print(f"\nPivot t={t} (m_t={ms2[t]}, m_L={ms2[lt]}, m_R={ms2[rt]})")
        check_ec_for_long_arc_cycle(n, ms2, t)
