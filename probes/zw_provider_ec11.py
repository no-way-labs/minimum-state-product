"""
Investigation part 11: Generalized mechanism check.

CaseA requires right(b) to be binary. Let's also check:
- CaseA_sym: left(b) binary, right(b) doesn't fire
- CaseB: both left(b) even and right(b) even (both binary)
- CaseC: left(b) = 0 fires AND right(b) = 0 fires (both silent)
- CaseD: ANY neighbor match (doesn't care about binary/ternary parity)

The actual mechanism from the computation (step 2 vs step 11):
Between nonmover=11 and mover=2: left(b) fires EVEN times (2), right(b) fires 0 times.
This works because left(b) IS binary (m=2), so even fires → value preserved.

So the generalized check should allow EITHER:
- left(b) binary + even fires + right(b) zero fires, OR
- left(b) zero fires + right(b) binary + even fires, OR
- left(b) binary + even fires + right(b) binary + even fires

And check BOTH intervals: (a1, a2) and wrapped (a2, a1).
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
    """Count fires of proc p in [start, end) with wrapping."""
    count = 0
    k = start
    while k != end:
        if word[k] == p:
            count += 1
        k = (k + 1) % L
    return count

def check_generalized_caseA(word, n, ms, b, a1, a2, L):
    """Check if generalized CaseA works for binary b between fires a1 and a2."""
    left_b = (b - 1) % n
    right_b = (b + 1) % n

    # Check both intervals: (a1, a2) forward, and (a2, a1) wrapping
    for start_fire, end_fire in [(a1, a2), (a2, a1)]:
        # Iterate over potential k2 in (start_fire, end_fire)
        k2 = (start_fire + 1) % L
        while k2 != end_fire:
            if word[k2] != b:  # k2 must not be a b-fire
                # Count left(b) fires in [k2, end_fire)
                l_fires = count_fires_in_interval(word, left_b, k2, end_fire, L)
                # Count right(b) fires in [k2, end_fire)
                r_fires = count_fires_in_interval(word, right_b, k2, end_fire, L)

                # Check conditions for context preservation:
                l_ok = (l_fires == 0) or (ms[left_b] == 2 and l_fires % 2 == 0)
                r_ok = (r_fires == 0) or (ms[right_b] == 2 and r_fires % 2 == 0)

                if l_ok and r_ok:
                    return True

            k2 = (k2 + 1) % L

    return False

n = 5
ms = (2, 2, 2, 3, 3)

print("Generalized CaseA check (allows either neighbor binary+even or zero fires)")
print("="*60)

total_cycles = 0
gen_works = 0
gen_fails = 0
fail_examples = []

for cl in [12, 14]:
    for word in enumerate_zw_words(n, cl):
        fc = fire_counts(word, n)
        if any(f < 2 for f in fc): continue
        if max(fc) < 3: continue

        L = len(word)

        def check_cycles(step, configs, transitions):
            global total_cycles, gen_works, gen_fails

            if step == L:
                if configs[0] != configs[L]: return
                config_tuples = [tuple(c) for c in configs[:L]]
                if len(set(config_tuples)) != L: return

                total_cycles += 1

                # For each binary b with fc=2
                found = False
                for b in range(n):
                    if ms[b] != 2 or fc[b] != 2: continue
                    fire_steps_b = [k for k in range(L) if word[k] == b]
                    a1, a2 = fire_steps_b[0], fire_steps_b[1]
                    if check_generalized_caseA(word, n, ms, b, a1, a2, L):
                        found = True
                        break

                if found:
                    gen_works += 1
                else:
                    gen_fails += 1
                    if len(fail_examples) < 3:
                        fail_examples.append((word, fc, tuple(configs[0])))
                return

            p = word[step]
            c = configs[step]
            ctx = (c[(p-1) % n], c[p], c[(p+1) % n])
            key = (p, ctx[0], ctx[1], ctx[2])

            if key in transitions:
                new_val = transitions[key]
                if new_val == ctx[1]: return
                new_c = c[:]; new_c[p] = new_val
                configs.append(new_c)
                check_cycles(step + 1, configs, transitions)
                configs.pop()
            else:
                for new_val in range(ms[p]):
                    if new_val == ctx[1]: continue
                    new_c = c[:]; new_c[p] = new_val
                    configs.append(new_c)
                    new_trans = dict(transitions)
                    new_trans[key] = new_val
                    check_cycles(step + 1, configs, new_trans)
                    configs.pop()

        for start in itertools.product(*[range(m) for m in ms]):
            check_cycles(0, [list(start)], {})

print(f"\nTotal valid cycles: {total_cycles}")
print(f"Generalized CaseA works: {gen_works}")
print(f"Generalized CaseA fails: {gen_fails}")

if gen_fails > 0:
    print("\nFail examples:")
    for w, f, s in fail_examples:
        print(f"  word={w}, fc={f}, start={s}")
else:
    print("\nGeneralized CaseA works for ALL cycles!")
    print("The proof needs: find binary b (fc=2), find k2 in interval")
    print("where left(b) preserved (0 fires or binary+even) AND")
    print("right(b) preserved (0 fires or binary+even).")
