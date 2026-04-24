"""
Investigation part 12: Check if extending to ternary mod-3 fixes everything.

For ternary proc t with m_t = 3: if t fires k times where k % 3 == 0,
then value returns (any permutation of {0,1,2} applied 3k times returns).
Wait, not necessarily — it depends on transition function.

Actually for binary: even fires → value returns because binary only has 2 values.
For ternary: 3 fires → value returns ONLY if the transition is a fixed permutation
applied 3 times (3-cycle). But transitions depend on context!

So ternary modular preservation is NOT guaranteed. The mechanism must be different.

Let me instead check: for the failing cases, what IS the EC mechanism?
Maybe there's a different binary proc that works, or an EC at a non-fc=2 proc.
"""

import itertools

def fire_counts(word, n):
    fc = [0] * n
    for p in word: fc[p] += 1
    return fc

def winding_number(word, n):
    cw = 0; ccw = 0; L = len(word)
    for i in range(L):
        curr = word[i]; nxt = word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
        elif nxt == (curr - 1) % n: ccw += 1
        else: return None
    if (cw - ccw) % n != 0: return None
    return (cw - ccw) // n

def cw_count(word, n):
    cw = 0; L = len(word)
    for i in range(L):
        curr = word[i]; nxt = word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
    return cw

def enumerate_zw_words(n, cl):
    def dfs(word, pos):
        if len(word) == cl:
            last = word[-1]; first = word[0]
            if (first - last) % n == 1 or (last - first) % n == 1:
                w = winding_number(word, n)
                if w == 0 and cw_count(word, n) > 0:
                    yield tuple(word)
            return
        for nxt in [(pos + 1) % n, (pos - 1) % n]:
            word.append(nxt)
            yield from dfs(word, nxt)
            word.pop()
    seen = set()
    for start in range(n):
        for word in dfs([start], start):
            rotations = [word[i:] + word[:i] for i in range(cl)]
            canonical = min(rotations)
            if canonical not in seen:
                seen.add(canonical)
                yield canonical

def count_fires_in_interval(word, p, start, end, L):
    count = 0
    k = start
    while k != end:
        if word[k] == p: count += 1
        k = (k + 1) % L
    return count

def check_generalized(word, n, ms, b, a1, a2, L):
    left_b = (b - 1) % n
    right_b = (b + 1) % n
    for start_fire, end_fire in [(a1, a2), (a2, a1)]:
        k2 = (start_fire + 1) % L
        while k2 != end_fire:
            if word[k2] != b:
                l_fires = count_fires_in_interval(word, left_b, k2, end_fire, L)
                r_fires = count_fires_in_interval(word, right_b, k2, end_fire, L)
                l_ok = (l_fires == 0) or (ms[left_b] == 2 and l_fires % 2 == 0)
                r_ok = (r_fires == 0) or (ms[right_b] == 2 and r_fires % 2 == 0)
                if l_ok and r_ok:
                    return True
            k2 = (k2 + 1) % L
    return False

n = 5
ms = (2, 2, 2, 3, 3)

# Focus on the failing word
fail_word = (0, 1, 0, 4, 3, 4, 3, 2, 1, 2, 3, 4)
fc = fire_counts(fail_word, n)
L = len(fail_word)

print(f"Analyzing failing word: {fail_word}")
print(f"FC: {fc}")
print(f"Binary procs (m=2): {[p for p in range(n) if ms[p]==2]}")
print(f"Binary with fc=2: {[p for p in range(n) if ms[p]==2 and fc[p]==2]}")
print()

for b in range(n):
    if ms[b] != 2 or fc[b] != 2: continue
    fire_steps_b = [k for k in range(L) if fail_word[k] == b]
    a1, a2 = fire_steps_b
    left_b = (b-1) % n
    right_b = (b+1) % n
    print(f"Binary proc {b}: fires at {fire_steps_b}")
    print(f"  left({b})={left_b} (m={ms[left_b]}), right({b})={right_b} (m={ms[right_b]})")

    # Check interval (a1, a2)
    print(f"  Interval ({a1}, {a2}):")
    for k in range(a1+1, a2):
        print(f"    Step {k}: mover={fail_word[k]}")
    l_fires = sum(1 for k in range(a1+1, a2) if fail_word[k] == left_b)
    r_fires = sum(1 for k in range(a1+1, a2) if fail_word[k] == right_b)
    print(f"    left fires: {l_fires}, right fires: {r_fires}")

    # Check wrapped interval (a2, a1)
    print(f"  Wrapped ({a2}, {a1}):")
    k = (a2 + 1) % L
    while k != a1:
        print(f"    Step {k}: mover={fail_word[k]}")
        k = (k + 1) % L
    l_fires2 = count_fires_in_interval(fail_word, left_b, (a2+1)%L, a1, L)
    r_fires2 = count_fires_in_interval(fail_word, right_b, (a2+1)%L, a1, L)
    print(f"    left fires: {l_fires2}, right fires: {r_fires2}")
    print()

# Now find what EC actually looks like for valid cycles of this word
print("="*60)
print("Finding actual EC for valid cycles of this word")
print("="*60)

cycle_count = [0]

def find_cycles(step, configs, transitions):
    if cycle_count[0] >= 3: return
    if step == L:
        if configs[0] != configs[L]: return
        config_tuples = [tuple(c) for c in configs[:L]]
        if len(set(config_tuples)) != L: return

        cycle_count[0] += 1
        print(f"\nCycle #{cycle_count[0]}, start={tuple(configs[0])}")

        # Show full sequence
        for k in range(L):
            p = fail_word[k]
            ctx = (configs[k][(p-1)%n], configs[k][p], configs[k][(p+1)%n])
            print(f"  Step {k:2d}: mover={p}, ctx=({ctx[0]},{ctx[1]},{ctx[2]}) config={tuple(configs[k])}")

        # Find EC
        for i in range(n):
            mover_ctxs = {}
            nonmover_ctxs = {}
            for k in range(L):
                c = configs[k]
                ctx = (c[(i-1) % n], c[i], c[(i+1) % n])
                if fail_word[k] == i:
                    mover_ctxs.setdefault(ctx, []).append(k)
                else:
                    nonmover_ctxs.setdefault(ctx, []).append(k)
            overlap = set(mover_ctxs.keys()) & set(nonmover_ctxs.keys())
            if overlap:
                for ctx in overlap:
                    mk = mover_ctxs[ctx][0]
                    nk = nonmover_ctxs[ctx][0]
                    print(f"  EC at proc {i} (m={ms[i]}, fc={fc[i]}): "
                          f"ctx={ctx}, mover@{mk}, nonmover@{nk}")

                    # Analyze: what preserves context between these steps?
                    lo, hi = min(mk, nk), max(mk, nk)
                    left_i = (i-1) % n
                    right_i = (i+1) % n
                    lf = sum(1 for j in range(lo, hi) if fail_word[j] == left_i)
                    rf = sum(1 for j in range(lo, hi) if fail_word[j] == right_i)
                    sf = sum(1 for j in range(lo, hi) if fail_word[j] == i)
                    print(f"    In [{lo},{hi}): left({i})={left_i} fires {lf}x, "
                          f"self fires {sf}x, right({i})={right_i} fires {rf}x")
                break
        return

    p = fail_word[step]
    c = configs[step]
    ctx = (c[(p-1) % n], c[p], c[(p+1) % n])
    key = (p, ctx[0], ctx[1], ctx[2])

    if key in transitions:
        new_val = transitions[key]
        if new_val == ctx[1]: return
        new_c = c[:]; new_c[p] = new_val
        configs.append(new_c)
        find_cycles(step + 1, configs, transitions)
        configs.pop()
    else:
        for new_val in range(ms[p]):
            if new_val == ctx[1]: continue
            new_c = c[:]; new_c[p] = new_val
            configs.append(new_c)
            new_trans = dict(transitions)
            new_trans[key] = new_val
            find_cycles(step + 1, configs, new_trans)
            configs.pop()

for start in itertools.product(*[range(m) for m in ms]):
    if cycle_count[0] >= 3: break
    find_cycles(0, [list(start)], {})
