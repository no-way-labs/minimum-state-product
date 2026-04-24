"""
Analyze the n=8 witness: ms=(2,2,3,4,3,3,2,3), product=2592
Focus on P7 (ternary between two binary neighbors P6 and P0)
and P3 (quaternary) to understand the wave filter roles.
"""
import itertools
from collections import Counter

ms = [2, 2, 3, 4, 3, 3, 2, 3]
n = 8

# Rules from n8_sweep_results.txt
rules = {
    0: {(0,0,0):1,(0,0,1):0,(0,1,0):1,(0,1,1):1,(1,0,0):0,(1,0,1):0,(1,1,0):1,(1,1,1):1,(2,0,0):0,(2,0,1):0,(2,1,0):0,(2,1,1):0},
    1: {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):0,(0,1,1):0,(0,1,2):0,(1,0,0):1,(1,0,1):0,(1,0,2):0,(1,1,0):1,(1,1,1):0,(1,1,2):1},
    2: {(0,0,0):0,(0,0,1):1,(0,0,2):0,(0,0,3):0,(0,1,0):2,(0,1,1):1,(0,1,2):0,(0,1,3):0,(0,2,0):2,(0,2,1):1,(0,2,2):2,(0,2,3):1,(1,0,0):1,(1,0,1):0,(1,0,2):2,(1,0,3):0,(1,1,0):1,(1,1,1):0,(1,1,2):2,(1,1,3):0,(1,2,0):2,(1,2,1):0,(1,2,2):2,(1,2,3):0},
    3: {(0,0,0):0,(0,0,1):0,(0,0,2):3,(0,1,0):3,(0,1,1):1,(0,1,2):1,(0,2,0):2,(0,2,1):0,(0,2,2):0,(0,3,0):3,(0,3,1):0,(0,3,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):2,(1,1,1):3,(1,1,2):0,(1,2,0):2,(1,2,1):0,(1,2,2):0,(1,3,0):0,(1,3,1):3,(1,3,2):0,(2,0,0):1,(2,0,1):2,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0,(2,2,0):0,(2,2,1):2,(2,2,2):2,(2,3,0):0,(2,3,1):0,(2,3,2):1},
    4: {(0,0,0):0,(0,0,1):0,(0,0,2):0,(0,1,0):1,(0,1,1):0,(0,1,2):0,(0,2,0):0,(0,2,1):0,(0,2,2):0,(1,0,0):0,(1,0,1):0,(1,0,2):0,(1,1,0):0,(1,1,1):1,(1,1,2):1,(1,2,0):0,(1,2,1):1,(1,2,2):1,(2,0,0):0,(2,0,1):0,(2,0,2):0,(2,1,0):2,(2,1,1):0,(2,1,2):0,(2,2,0):2,(2,2,1):0,(2,2,2):0,(3,0,0):1,(3,0,1):2,(3,0,2):0,(3,1,0):1,(3,1,1):1,(3,1,2):1,(3,2,0):0,(3,2,1):2,(3,2,2):0},
    5: {(0,0,0):0,(0,0,1):0,(0,1,0):1,(0,1,1):0,(0,2,0):0,(0,2,1):0,(1,0,0):0,(1,0,1):0,(1,1,0):2,(1,1,1):0,(1,2,0):2,(1,2,1):2,(2,0,0):1,(2,0,1):0,(2,1,0):1,(2,1,1):1,(2,2,0):0,(2,2,1):0},
    6: {(0,0,0):0,(0,0,1):0,(0,0,2):1,(0,1,0):0,(0,1,1):0,(0,1,2):1,(1,0,0):0,(1,0,1):0,(1,0,2):1,(1,1,0):0,(1,1,1):1,(1,1,2):1,(2,0,0):1,(2,0,1):0,(2,0,2):0,(2,1,0):1,(2,1,1):0,(2,1,2):0},
    7: {(0,0,0):0,(0,0,1):0,(0,1,0):0,(0,1,1):2,(0,2,0):2,(0,2,1):2,(1,0,0):0,(1,0,1):1,(1,1,0):1,(1,1,1):1,(1,2,0):1,(1,2,1):2},
}

def f(i, L, S, R):
    return rules[i][(L, S, R)]

def privileged_set(config):
    priv = []
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        if f(i, L, S, R) != S:
            priv.append(i)
    return priv

def apply_move(config, i):
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    lst = list(config)
    lst[i] = f(i, L, S, R)
    return tuple(lst)

# Find the good cycle by starting from an arbitrary good config
# A good config has exactly 1 privileged processor
print("Finding good cycle for n=8 witness...")

# Start from the all-zeros config
c = tuple([0]*n)
priv = privileged_set(c)
print(f"Start: {c}, priv={priv}")

# Follow the deterministic successor map on single-privilege configs
# until we find a cycle
path = [c]
seen = {c: 0}
while True:
    priv = privileged_set(path[-1])
    if len(priv) != 1:
        print(f"Config {path[-1]} has {len(priv)} privileged: {priv} — not a good config, searching...")
        # Try all configs to find a single-privilege one
        break
    mover = priv[0]
    next_c = apply_move(path[-1], mover)
    if next_c in seen:
        cycle_start = seen[next_c]
        cycle = path[cycle_start:]
        print(f"Found cycle of length {len(cycle)} starting at step {cycle_start}")
        break
    seen[next_c] = len(path)
    path.append(next_c)

if len(priv) != 1:
    # Search for a good config
    print("Searching all configs for single-privilege ones...")
    single_priv_configs = []
    for c in itertools.product(*(range(m) for m in ms)):
        p = privileged_set(c)
        if len(p) == 1:
            single_priv_configs.append(c)
    print(f"Found {len(single_priv_configs)} single-privilege configs")

    # Build functional graph and find cycles
    succ = {}
    for c in single_priv_configs:
        mover = privileged_set(c)[0]
        s = apply_move(c, mover)
        if len(privileged_set(s)) == 1:
            succ[c] = s

    # Find cycles
    visited = set()
    for c in single_priv_configs:
        if c not in succ or c in visited:
            continue
        path = []
        node = c
        path_set = set()
        while node in succ and node not in visited and node not in path_set:
            path.append(node)
            path_set.add(node)
            node = succ[node]
        if node in path_set:
            idx = path.index(node)
            cycle = path[idx:]
            # Check fairness
            movers_in_cycle = set()
            for cc in cycle:
                movers_in_cycle.add(privileged_set(cc)[0])
            if movers_in_cycle == set(range(n)):
                print(f"Found fair cycle of length {len(cycle)}")
                break
        visited.update(path)

# Analyze the cycle
print(f"\nGood cycle length: {len(cycle)}")

# Track movers and processor states
print("\nStep | Config                     | Mover | P7_state | P3_state | P0_state | P6_state")
print("-" * 95)
movers = []
for idx in range(len(cycle)):
    c = cycle[idx]
    c_next = cycle[(idx + 1) % len(cycle)]
    mover = None
    for j in range(n):
        if c[j] != c_next[j]:
            mover = j
            break
    movers.append(mover)
    print(f"  {idx:2d} | {c} | P{mover} | s7={c[7]}    | s3={c[3]}    | s0={c[0]}    | s6={c[6]}")

# Token direction analysis
print("\n" + "=" * 70)
print("TOKEN DIRECTION THROUGH P7 (ternary, between P6=binary and P0=binary)")
print("=" * 70)

for idx in range(len(cycle)):
    if movers[idx] == 7:
        c = cycle[idx]
        prev_mover = movers[(idx-1) % len(cycle)]
        next_mover = movers[(idx+1) % len(cycle)]
        L, S, R = c[6], c[7], c[0]
        new_S = f(7, L, S, R)
        print(f"  step {idx:2d}: P{prev_mover}->P7->P{next_mover}  ({L},{S},{R})->{new_S}")

print("\n" + "=" * 70)
print("TOKEN DIRECTION THROUGH P3 (quaternary)")
print("=" * 70)

for idx in range(len(cycle)):
    if movers[idx] == 3:
        c = cycle[idx]
        prev_mover = movers[(idx-1) % len(cycle)]
        next_mover = movers[(idx+1) % len(cycle)]
        L, S, R = c[2], c[3], c[4]
        new_S = f(3, L, S, R)
        print(f"  step {idx:2d}: P{prev_mover}->P3->P{next_mover}  ({L},{S},{R})->{new_S}")

# Analyze P7's state usage
print("\n" + "=" * 70)
print("P7 STATE SEMANTICS")
print("=" * 70)
for s in range(3):
    print(f"\n  P7 in state {s}:")
    for L in range(2):  # P6 is binary
        for R in range(2):  # P0 is binary
            new_s = f(7, L, s, R)
            priv = "*" if new_s != s else " "
            print(f"    L={L}, R={R}: f7({L},{s},{R})={new_s} {priv}")

# Check: does token enter P7 from BOTH sides?
print("\n" + "=" * 70)
print("DIRECTIONALITY ANALYSIS: Does token enter P7 from both sides?")
print("=" * 70)
enters_from_left = False  # from P6
enters_from_right = False  # from P0
for idx in range(len(cycle)):
    if movers[idx] == 7:
        prev = movers[(idx-1) % len(cycle)]
        if prev == 6:
            enters_from_left = True
            print(f"  step {idx}: enters from LEFT (P6)")
        elif prev == 0:
            enters_from_right = True
            print(f"  step {idx}: enters from RIGHT (P0)")
        else:
            print(f"  step {idx}: enters from P{prev} (neither immediate neighbor)")

print(f"\n  Enters from left (P6): {enters_from_left}")
print(f"  Enters from right (P0): {enters_from_right}")
print(f"  P7 is {'BIDIRECTIONAL' if enters_from_left and enters_from_right else 'UNIDIRECTIONAL'} filter")

# Same analysis for P3
print("\n" + "=" * 70)
print("DIRECTIONALITY ANALYSIS: Does token enter P3 from both sides?")
print("=" * 70)
enters_from_left_3 = False
enters_from_right_3 = False
for idx in range(len(cycle)):
    if movers[idx] == 3:
        prev = movers[(idx-1) % len(cycle)]
        if prev == 2:
            enters_from_left_3 = True
            print(f"  step {idx}: enters from LEFT (P2)")
        elif prev == 4:
            enters_from_right_3 = True
            print(f"  step {idx}: enters from RIGHT (P4)")
        else:
            print(f"  step {idx}: enters from P{prev} (not immediate neighbor)")

print(f"\n  Enters from left (P2): {enters_from_left_3}")
print(f"  Enters from right (P4): {enters_from_right_3}")
print(f"  P3 is {'BIDIRECTIONAL' if enters_from_left_3 and enters_from_right_3 else 'UNIDIRECTIONAL'} filter")

# Full mover sequence
print("\n" + "=" * 70)
print("FULL MOVER SEQUENCE")
print("=" * 70)
print("  " + " -> ".join(f"P{m}" for m in movers))

# Count moves per processor
move_counts = Counter(movers)
print("\nMoves per processor:")
for i in range(n):
    print(f"  P{i} (m={ms[i]}): {move_counts.get(i,0)} moves")
