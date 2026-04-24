"""
Final verification of the counterexample using the project's verifier.
"""
import sys
sys.path.insert(0, './claude')
from verifier import verify_system
from math import gcd
from functools import reduce

# Counterexample system
ms = [2, 3, 3]
n = 3

# The second counterexample (cleaner: only 1 non-adj H-1 pair)
# step 0: (0, 0, 0) mover=0
# step 1: (1, 0, 0) mover=1
# step 2: (1, 1, 0) mover=2
# step 3: (1, 1, 2) mover=2
# step 4: (1, 1, 1) mover=1
# step 5: (1, 2, 1) mover=0
# step 6: (0, 2, 1) mover=1
# step 7: (0, 0, 1) mover=2
# Non-adj H-1: j=2,k=4,p=2,d=2

# Tables from the system that was found:
t0 = {(0, 0, 0): 0, (0, 0, 2): 0, (0, 0, 1): 0, (2, 0, 1): 1, (2, 1, 1): 1,
      (1, 1, 1): 1, (0, 1, 1): 1, (0, 1, 0): 0, (0, 1, 2): 1, (1, 0, 0): 0,
      (1, 0, 1): 1, (1, 0, 2): 0, (1, 1, 0): 0, (1, 1, 2): 0, (2, 0, 0): 1,
      (2, 0, 2): 0, (2, 1, 0): 1, (2, 1, 2): 0}

# Wait, this was from the first search which failed closure. Let me use
# the correct system. The counterexample verification found a different table.
# Let me regenerate from the counterexample search.

# Actually, the counterexample_analyze output showed the second counterexample
# at index 103 with this cycle:
#   step 0: (0, 0, 0) mover=0
#   step 1: (1, 0, 0) mover=1
#   step 2: (1, 1, 0) mover=2
#   step 3: (1, 1, 2) mover=2
#   step 4: (1, 1, 1) mover=1
#   step 5: (1, 2, 1) mover=0
#   step 6: (0, 2, 1) mover=1
#   step 7: (0, 0, 1) mover=2
# Non-adj H-1: j=2,k=4,p=2,d=2

# I need to reconstruct the transition tables. Let me redo the search
# with this specific cycle and save the tables.

import random, itertools

def all_configs_gen(ms):
    return list(itertools.product(*(range(m) for m in ms)))

def hamming_distance(c1, c2):
    return sum(1 for a, b in zip(c1, c2) if a != b)

def privileged_set(config, fs, ms):
    n = len(ms)
    priv = []
    for i in range(n):
        L = config[(i-1) % n]
        S = config[i]
        R = config[(i+1) % n]
        if fs[i](L, S, R) != S:
            priv.append(i)
    return priv

def apply_move(config, i, fs, ms):
    n = len(ms)
    L = config[(i-1) % n]
    S = config[i]
    R = config[(i+1) % n]
    new_s = fs[i](L, S, R)
    lst = list(config)
    lst[i] = new_s
    return tuple(lst)

# Target cycle
cycle_configs = [(0,0,0), (1,0,0), (1,1,0), (1,1,2), (1,1,1), (1,2,1), (0,2,1), (0,0,1)]
movers = [0, 1, 2, 2, 1, 0, 1, 2]
CL = 8

# Build partial tables
tables = [{} for _ in range(n)]
for s in range(CL):
    c = cycle_configs[s]
    m = movers[s]
    c_next = cycle_configs[(s+1) % CL]
    for i in range(n):
        Li = c[(i-1)%n]
        Si = c[i]
        Ri = c[(i+1)%n]
        ctx = (Li, Si, Ri)
        req = c_next[i] if i == m else Si
        if ctx in tables[i] and tables[i][ctx] != req:
            print(f"CONFLICT at proc {i}, step {s}: ctx={ctx} existing={tables[i][ctx]} need={req}")
        tables[i][ctx] = req

# Free contexts
free_ctxs = []
for i in range(n):
    L_range = ms[(i-1)%n]
    S_range = ms[i]
    R_range = ms[(i+1)%n]
    free = [(L,S,R) for L in range(L_range) for S in range(S_range)
            for R in range(R_range) if (L,S,R) not in tables[i]]
    free_ctxs.append(free)
    print(f"proc {i}: {len(tables[i])}/{L_range*S_range*R_range} determined, {len(free)} free")

# Try completions
random.seed(42)
for trial in range(1000000):
    full_tables = [dict(t) for t in tables]
    for i in range(n):
        for ctx in free_ctxs[i]:
            full_tables[i][ctx] = random.randint(0, ms[i]-1)

    def make_f(table):
        def f(L,S,R): return table[(L,S,R)]
        return f
    fs = [make_f(full_tables[i]) for i in range(n)]

    result = verify_system(ms, fs)
    if result['valid']:
        # Check the good cycle matches our target
        good_set = result.get('good_configs', set())
        target_set = set(cycle_configs)
        if target_set.issubset(good_set):
            print(f"\nVALID system found at trial {trial}!")

            # Extract the good cycle
            cycle_out = []
            current = cycle_configs[0]
            for s in range(len(good_set)):
                priv = privileged_set(current, fs, ms)
                if len(priv) != 1:
                    break
                mover_out = priv[0]
                cycle_out.append((current, mover_out))
                current = apply_move(current, mover_out, fs, ms)

            print(f"Good cycle ({len(cycle_out)} configs):")
            for s, (c, m) in enumerate(cycle_out):
                print(f"  step {s}: {c} mover={m}")

            # Check H-1 pairs
            gc = [c for c, m in cycle_out]
            print(f"\nH-1 pairs:")
            for j in range(len(gc)):
                for k in range(j+1, len(gc)):
                    if hamming_distance(gc[j], gc[k]) == 1:
                        d = k - j
                        p = [i for i in range(n) if gc[j][i] != gc[k][i]][0]
                        adj = "ADJ" if d == 1 or d == len(gc)-1 else f"NON-ADJ (d={d})"
                        print(f"  j={j},k={k},p={p},d={d}: {adj}")

            fc = [0]*n
            for c, m in cycle_out:
                fc[m] += 1
            print(f"\nfc={fc}, ms={ms}, gcd={reduce(gcd, ms)}")
            print(f"Valid system properties: {result['properties']}")
            break

    if trial % 100000 == 0 and trial > 0:
        print(f"  Tried {trial}...")
else:
    print(f"\nNo valid system found in 1000000 trials for this specific cycle.")
    print("Trying with a different seed and the first counterexample cycle...")

    # Try the first counterexample cycle
    cycle_configs2 = [(0,0,1), (0,2,1), (0,2,0), (1,2,0), (1,2,2), (1,2,1), (1,1,1), (0,1,1)]
    movers2 = [1, 2, 0, 2, 2, 1, 0, 1]

    tables2 = [{} for _ in range(n)]
    ok = True
    for s in range(CL):
        c = cycle_configs2[s]
        m = movers2[s]
        c_next = cycle_configs2[(s+1) % CL]
        for i in range(n):
            Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
            ctx = (Li, Si, Ri)
            req = c_next[i] if i == m else Si
            if ctx in tables2[i] and tables2[i][ctx] != req:
                ok = False
                break
            tables2[i][ctx] = req
        if not ok:
            break

    if not ok:
        print("  Cycle 2 has TF conflicts.")
    else:
        free2 = []
        for i in range(n):
            L_range = ms[(i-1)%n]; S_range = ms[i]; R_range = ms[(i+1)%n]
            f = [(L,S,R) for L in range(L_range) for S in range(S_range)
                 for R in range(R_range) if (L,S,R) not in tables2[i]]
            free2.append(f)

        random.seed(123)
        for trial in range(1000000):
            full_tables = [dict(t) for t in tables2]
            for i in range(n):
                for ctx in free2[i]:
                    full_tables[i][ctx] = random.randint(0, ms[i]-1)

            def make_f(table):
                def f(L,S,R): return table[(L,S,R)]
                return f
            fs = [make_f(full_tables[i]) for i in range(n)]

            result = verify_system(ms, fs)
            if result['valid']:
                good_set = result.get('good_configs', set())
                target_set = set(cycle_configs2)

                # Extract cycle
                gc_list = sorted(good_set)
                start = gc_list[0]
                cycle_out = []
                current = start
                visited = set()
                while current not in visited:
                    visited.add(current)
                    priv = privileged_set(current, fs, ms)
                    if len(priv) != 1:
                        break
                    cycle_out.append((current, priv[0]))
                    current = apply_move(current, priv[0], fs, ms)

                if len(cycle_out) == len(good_set) and current == start:
                    gc = [c for c, m in cycle_out]
                    has_nonadj = False
                    for j in range(len(gc)):
                        for k in range(j+1, len(gc)):
                            if hamming_distance(gc[j], gc[k]) == 1:
                                d = k - j
                                if 1 < d < len(gc) - 1:
                                    has_nonadj = True
                                    break
                        if has_nonadj:
                            break

                    if has_nonadj:
                        print(f"\nVALID system with non-adj H-1 (trial {trial})!")
                        print(f"Good cycle:")
                        for s, (c, m) in enumerate(cycle_out):
                            print(f"  step {s}: {c} mover={m}")
                        for j in range(len(gc)):
                            for k in range(j+1, len(gc)):
                                if hamming_distance(gc[j], gc[k]) == 1:
                                    d = k - j
                                    if 1 < d < len(gc) - 1:
                                        p = [i for i in range(n) if gc[j][i] != gc[k][i]][0]
                                        print(f"  NON-ADJ H-1: j={j},k={k},p={p},d={d}")
                        fc = [0]*n
                        for c, m in cycle_out: fc[m] += 1
                        print(f"  fc={fc}, gcd={reduce(gcd, ms)}")
                        print(f"  Properties: {result['properties']}")
                        break

            if trial % 100000 == 0 and trial > 0:
                print(f"  Tried {trial}...")
        else:
            print(f"  No valid system found for cycle 2 either.")
