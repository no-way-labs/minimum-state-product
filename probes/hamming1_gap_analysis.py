"""
Gap analysis: the n=3 counterexample to abstract H-1 Uniqueness.

Example: ms=(2,3,3), word=(1,1,2,0,2,2,1,0), d=2
configs = [(0,0,0), (0,2,0), (0,1,0), (0,1,2), (1,1,2), (1,1,1), (1,1,0), (1,0,0)]
g_0 = (0,0,0), g_2 = (0,1,0), differ at position 1 (0 vs 1).

Question: What additional constraint from real systems prevents this?
"""

import itertools

# The example
ms = [2, 3, 3]
n = 3
CL = 8
word = (1, 1, 2, 0, 2, 2, 1, 0)
configs = [(0,0,0), (0,2,0), (0,1,0), (0,1,2), (1,1,2), (1,1,1), (1,1,0), (1,0,0)]

print("Example cycle:")
for s in range(CL):
    c = configs[s]
    m = word[s]
    c_next = configs[(s+1) % CL]
    print(f"  step {s}: {c} mover={m} -> {c_next}")

print(f"\nH-1 pair: g_0={configs[0]}, g_2={configs[2]}, differ at p=1")
print(f"  g_0[1]=0, g_2[1]=1")
print(f"  Arc d=2: movers at steps 0,1 = {word[0]},{word[1]} = 1,1")
print(f"  Arc fire count: proc 1 fires 2 times (= m_1 = 3? NO, m_1=3, a_1=2)")

# Wait — arc fire count for proc 1 in the arc is 2, but m_1 = 3.
# Lemma 2 says a_q in {0, m_q} for q != p. p=1, so we check q=0 and q=2.
# arc_fc[0] = 0 (proc 0 doesn't fire in steps 0,1). a_0=0. OK (0 in {0, 2}).
# arc_fc[2] = 0. a_2=0. OK (0 in {0, 3}).
# For p=1: a_1=2, 0 < 2 < 3 = m_1. OK (doesn't need to be in {0, m_p}).

# So Lemma 2 IS satisfied. But wait, let me check Value Coverage more carefully.
print("\nValue walks per processor:")
for i in range(n):
    vals = [configs[s][i] for s in range(CL)]
    fire_steps = [s for s in range(CL) if word[s] == i]
    print(f"  proc {i} (m={ms[i]}): values={vals}, fires at steps {fire_steps}")
    # Check: visits all values?
    unique_vals = set(vals)
    print(f"    visits {sorted(unique_vals)} (need all of {{0,...,{ms[i]-1}}})")
    if len(unique_vals) == ms[i]:
        print(f"    Value Coverage: YES")
    else:
        print(f"    Value Coverage: NO — only {len(unique_vals)} of {ms[i]}")

# Now: can this abstract cycle be realized by a deterministic transition function?
# For it to be a real system, each proc i needs f_i(L, S, R) that is deterministic.
# Privileged when f_i(L,S,R) != S.

# Let's extract the required transition function from the cycle.
print("\n\nRequired transition function entries:")
for s in range(CL):
    c = configs[s]
    m = word[s]
    c_next = configs[(s+1) % CL]
    # For the mover m at step s:
    L = c[(m-1) % n]
    S = c[m]
    R = c[(m+1) % n]
    S_new = c_next[m]
    print(f"  step {s}: proc {m}, context ({L},{S},{R}) -> {S_new} (privileged: {S_new} != {S})")

    # For all non-movers:
    for i in range(n):
        if i != m:
            Li = c[(i-1) % n]
            Si = c[i]
            Ri = c[(i+1) % n]
            # f_i(Li, Si, Ri) must equal Si (not privileged)
            # Only record if this is a NEW entry
            pass

# Build full transition tables
print("\nBuilding transition tables:")
tables = [{} for _ in range(n)]
consistent = True

for s in range(CL):
    c = configs[s]
    m = word[s]
    c_next = configs[(s+1) % CL]

    for i in range(n):
        Li = c[(i-1) % n]
        Si = c[i]
        Ri = c[(i+1) % n]
        ctx = (Li, Si, Ri)

        if i == m:
            # Mover: f_i(ctx) = c_next[i] != Si
            req_val = c_next[i]
        else:
            # Non-mover: f_i(ctx) = Si
            req_val = Si

        if ctx in tables[i]:
            if tables[i][ctx] != req_val:
                print(f"  CONFLICT at proc {i}, step {s}: ctx={ctx}, "
                      f"existing={tables[i][ctx]}, needed={req_val}")
                consistent = False
        else:
            tables[i][ctx] = req_val

print(f"\nConsistency: {consistent}")

if consistent:
    print("\nTransition tables:")
    for i in range(n):
        print(f"  proc {i} (m={ms[i]}):")
        for ctx in sorted(tables[i].keys()):
            val = tables[i][ctx]
            priv = "PRIV" if val != ctx[1] else "    "
            print(f"    f({ctx}) = {val} {priv}")
else:
    print("\n*** This abstract cycle CANNOT be realized by any deterministic system! ***")
    print("The H-1 Uniqueness Lemma holds for REAL systems (deterministic TFs).")
    print("Abstract cycles can have non-adjacent H-1 pairs, but they require")
    print("contradictory transition entries → no real system can produce them.")

# Check ALL n=3 non-adjacent H-1 examples for consistency
print("\n" + "=" * 70)
print("Checking ALL non-adj H-1 cycles for TF consistency")
print("=" * 70)

def hamming_distance(c1, c2):
    return sum(1 for a, b in zip(c1, c2) if a != b)

def enumerate_mover_words(ms):
    base = []
    for i in range(len(ms)):
        base.extend([i]*ms[i])
    return set(itertools.permutations(base))

ms_test = [2, 3, 3]
n = 3
CL = sum(ms_test)
mover_words = list(enumerate_mover_words(ms_test))
all_cfgs = list(itertools.product(range(2), range(3), range(3)))

consistent_nonadj = 0
inconsistent_nonadj = 0
total_checked = 0
unique_cycles = set()

for word in mover_words:
    for start in all_cfgs:
        stack = [(0, start, [start])]
        while stack:
            step, current, path = stack.pop()
            if step == CL:
                if current == start and len(set(path[:CL])) == CL:
                    configs = path[:CL]
                    # Check for non-adjacent H-1
                    has_nonadj = False
                    for j in range(CL):
                        for k in range(j+1, CL):
                            if hamming_distance(configs[j], configs[k]) == 1:
                                d = k - j
                                if 1 < d < CL - 1:
                                    has_nonadj = True
                                    break
                        if has_nonadj:
                            break

                    if has_nonadj:
                        # Check TF consistency
                        cycle_key = (word, tuple(configs))
                        if cycle_key in unique_cycles:
                            continue
                        unique_cycles.add(cycle_key)
                        total_checked += 1

                        tables = [{} for _ in range(n)]
                        ok = True
                        for s in range(CL):
                            c = configs[s]
                            m = word[s]
                            c_next = configs[(s+1) % CL]
                            for i in range(n):
                                Li = c[(i-1)%n]
                                Si = c[i]
                                Ri = c[(i+1)%n]
                                ctx = (Li, Si, Ri)
                                req = c_next[i] if i == m else Si
                                if ctx in tables[i]:
                                    if tables[i][ctx] != req:
                                        ok = False
                                        break
                                else:
                                    tables[i][ctx] = req
                            if not ok:
                                break

                        if ok:
                            consistent_nonadj += 1
                        else:
                            inconsistent_nonadj += 1
                continue
            mover = word[step]
            for new_val in range(ms_test[mover]):
                if new_val != current[mover]:
                    new_cfg = list(current)
                    new_cfg[mover] = new_val
                    stack.append((step+1, tuple(new_cfg), path + [tuple(new_cfg)]))

    if total_checked > 0 and total_checked % 500 == 0:
        print(f"  Checked {total_checked}: consistent={consistent_nonadj}, "
              f"inconsistent={inconsistent_nonadj}")

print(f"\nTotal unique cycles with non-adj H-1: {total_checked}")
print(f"  TF Consistent: {consistent_nonadj}")
print(f"  TF Inconsistent: {inconsistent_nonadj}")

if consistent_nonadj == 0:
    print("\n*** ALL non-adj H-1 cycles have TF CONFLICTS ***")
    print("The H-1 Uniqueness Lemma is TRUE for real systems:")
    print("deterministic transition functions cannot produce non-adjacent H-1 pairs.")
else:
    print(f"\n*** {consistent_nonadj} cycles are TF-consistent with non-adj H-1 ***")
    print("These could potentially be realized by real systems.")
