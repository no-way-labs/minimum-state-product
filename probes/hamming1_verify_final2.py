"""
Search for valid systems with EXACTLY fc(i) = m_i and non-adj H-1.
"""
import itertools, random
from math import gcd
from functools import reduce

def all_configs(ms):
    return list(itertools.product(*(range(m) for m in ms)))

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

def hamming_distance(c1, c2):
    return sum(1 for a, b in zip(c1, c2) if a != b)

def verify_full(ms, fs):
    n = len(ms)
    configs = all_configs(ms)
    priv_map = {}
    for c in configs:
        priv_map[c] = privileged_set(c, fs, ms)

    dead = [c for c in configs if len(priv_map[c]) == 0]
    if dead:
        return None

    good = [c for c in configs if len(priv_map[c]) == 1]
    good_set = set(good)

    for c in good:
        mover = priv_map[c][0]
        nxt = apply_move(c, mover, fs, ms)
        if nxt not in good_set:
            return None

    # Extract cycle
    start = good[0]
    cycle = []
    current = start
    seen = set()
    while current not in seen:
        seen.add(current)
        mover = priv_map[current][0]
        cycle.append((current, mover))
        current = apply_move(current, mover, fs, ms)

    if current != start or len(cycle) != len(good):
        return None

    # Convergence
    bad_set = set(configs) - good_set
    visited = set()
    for sb in bad_set:
        if sb in visited:
            continue
        stack = [(sb, frozenset([sb]))]
        while stack:
            c, path = stack.pop()
            visited.add(c)
            for p in priv_map[c]:
                nxt = apply_move(c, p, fs, ms)
                if nxt in good_set:
                    continue
                if nxt in path:
                    return None
                if nxt not in visited:
                    stack.append((nxt, path | {nxt}))

    return cycle

# Search
ms = [2, 3, 3]
n = 3
CL_target = sum(ms)  # 8

# Enumerate abstract cycles with fc = m_i
def enumerate_mover_words(ms):
    base = []
    for i in range(len(ms)):
        base.extend([i]*ms[i])
    return set(itertools.permutations(base))

words = list(enumerate_mover_words(ms))
all_cfgs = list(itertools.product(range(2), range(3), range(3)))

# Find abstract cycles with non-adj H-1 and fc = m_i
print(f"Finding abstract cycles with fc={ms}, CL={CL_target}, non-adj H-1...")

nonadj_cycles = []
for word in words:
    for start in all_cfgs:
        stack = [(0, start, [start])]
        while stack:
            step, current, path = stack.pop()
            if step == CL_target:
                if current == start and len(set(path[:CL_target])) == CL_target:
                    configs = path[:CL_target]
                    has_nonadj = False
                    for j in range(CL_target):
                        for k in range(j+1, CL_target):
                            if hamming_distance(configs[j], configs[k]) == 1:
                                d = k - j
                                if 1 < d < CL_target - 1:
                                    has_nonadj = True
                                    break
                        if has_nonadj:
                            break
                    if has_nonadj:
                        nonadj_cycles.append((word, configs))
                continue
            mover = word[step]
            for new_val in range(ms[mover]):
                if new_val != current[mover]:
                    new_cfg = list(current)
                    new_cfg[mover] = new_val
                    stack.append((step+1, tuple(new_cfg), path + [tuple(new_cfg)]))

print(f"Found {len(nonadj_cycles)} abstract cycles")

# Deduplicate
unique = {}
for word, configs in nonadj_cycles:
    key = (word, tuple(configs))
    unique[key] = (word, configs)
print(f"Unique: {len(unique)}")

# For each, try completions and verify with fc check
random.seed(42)
valid_found = 0
total_tried = 0

for idx, (key, (word, configs)) in enumerate(unique.items()):
    if idx >= 500:
        break

    # Build partial tables
    tables = [{} for _ in range(n)]
    ok = True
    for s in range(CL_target):
        c = configs[s]
        m = word[s]
        c_next = configs[(s+1) % CL_target]
        for i in range(n):
            Li = c[(i-1)%n]; Si = c[i]; Ri = c[(i+1)%n]
            ctx = (Li, Si, Ri)
            req = c_next[i] if i == m else Si
            if ctx in tables[i]:
                if tables[i][ctx] != req:
                    ok = False; break
            else:
                tables[i][ctx] = req
        if not ok:
            break
    if not ok:
        continue

    free = []
    for i in range(n):
        L_r = ms[(i-1)%n]; S_r = ms[i]; R_r = ms[(i+1)%n]
        f = [(L,S,R) for L in range(L_r) for S in range(S_r)
             for R in range(R_r) if (L,S,R) not in tables[i]]
        free.append(f)

    for trial in range(2000):
        total_tried += 1
        full = [dict(t) for t in tables]
        for i in range(n):
            for ctx in free[i]:
                full[i][ctx] = random.randint(0, ms[i]-1)

        def make_f(table):
            def f(L,S,R): return table[(L,S,R)]
            return f
        fs = [make_f(full[i]) for i in range(n)]

        cycle = verify_full(ms, fs)
        if cycle is not None:
            gc = [c for c, m in cycle]
            fc = [0]*n
            for c, m in cycle:
                fc[m] += 1

            # Check fc = m_i
            if not all(fc[i] == ms[i] for i in range(n)):
                continue  # Wrong fire counts

            # Check non-adj H-1
            has_nonadj = False
            nonadj_list = []
            for j in range(len(gc)):
                for k in range(j+1, len(gc)):
                    if hamming_distance(gc[j], gc[k]) == 1:
                        d = k - j
                        if 1 < d < len(gc) - 1:
                            has_nonadj = True
                            p = [i for i in range(n) if gc[j][i] != gc[k][i]][0]
                            nonadj_list.append((j,k,p,d))

            if has_nonadj:
                valid_found += 1
                print(f"\n*** COUNTEREXAMPLE (fc=m_i) at idx={idx}, trial={trial} ***")
                for s, (c, m) in enumerate(cycle):
                    print(f"  step {s}: {c} mover={m}")
                print(f"  fc={fc}, ms={ms}, CL={len(cycle)}, gcd={reduce(gcd, ms)}")
                for j,k,p,d in nonadj_list:
                    print(f"  NON-ADJ: j={j},k={k},p={p},d={d}")
                if valid_found >= 5:
                    break

    if idx % 100 == 0:
        print(f"  Checked idx={idx}, total_tried={total_tried}, found={valid_found}")

    if valid_found >= 5:
        break

print(f"\n{'='*70}")
print(f"RESULT: {valid_found} valid counterexamples with fc=m_i")
print(f"Checked {total_tried} completions across {min(idx+1, 500)} cycles")

if valid_found == 0:
    print("\nNo counterexample with fc(i)=m_i found.")
    print("The H-1 Uniqueness Lemma may be TRUE when fc(i)=m_i is enforced.")
    print("The previous 'counterexample' had fc=[3,5,5] != ms=[2,3,3].")
