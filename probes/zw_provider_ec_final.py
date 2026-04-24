"""
Final investigation: Universal structural EC for ZW+fc>=3.

For EVERY proc i (binary or ternary), and every pair of consecutive fire steps,
check if there exists a non-mover step k where:
  - left(i): preserved (0 fires or binary+even)
  - self(i): 0 fires (always true between consecutive fires)
  - right(i): preserved (0 fires or binary+even)

If this works for ALL valid ZW+fc>=3 cycles, the proof approach is:
  Find ANY proc i and ANY interval where this structural condition holds.
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

def find_structural_ec(word, n, ms):
    """For any proc i, find consecutive fire pair where structural preservation gives EC."""
    L = len(word)
    fc = fire_counts(word, n)

    for i in range(n):
        if fc[i] < 2: continue
        left_i = (i - 1) % n
        right_i = (i + 1) % n

        fire_steps = [k for k in range(L) if word[k] == i]

        # Check all consecutive pairs
        for idx in range(len(fire_steps)):
            a1 = fire_steps[idx]
            a2 = fire_steps[(idx + 1) % len(fire_steps)]

            # Check both intervals: (a1, a2) and (a2, a1)
            for start_fire, end_fire in [(a1, a2), (a2, a1)]:
                k2 = (start_fire + 1) % L
                while k2 != end_fire:
                    if word[k2] != i:
                        l_fires = count_fires_in_interval(word, left_i, k2, end_fire, L)
                        r_fires = count_fires_in_interval(word, right_i, k2, end_fire, L)

                        l_ok = (l_fires == 0) or (ms[left_i] == 2 and l_fires % 2 == 0)
                        r_ok = (r_fires == 0) or (ms[right_i] == 2 and r_fires % 2 == 0)

                        if l_ok and r_ok:
                            return True, i, k2, end_fire
                    k2 = (k2 + 1) % L

    return False, -1, -1, -1

n = 5
ms = (2, 2, 2, 3, 3)

print(f"Universal structural EC check: n={n}, ms={ms}")
print("Checking ALL valid ZW+cw>0+fc>=3 good cycles")
print("Looking at ANY proc (binary or ternary) for structural EC")
print("="*60)

total_cycles = 0
struct_works = 0
struct_fails = 0
fail_details = []

for cl in [12, 14]:
    for word in enumerate_zw_words(n, cl):
        fc = fire_counts(word, n)
        if any(f < 2 for f in fc): continue
        if max(fc) < 3: continue

        L = len(word)

        # First check if structural EC exists at the WORD level
        found_word, ei, ek, ef = find_structural_ec(word, n, ms)

        if not found_word:
            # This word has no structural EC at any proc — check if it even has valid cycles
            pass

        def check_cycles(step, configs, transitions):
            global total_cycles, struct_works, struct_fails

            if step == L:
                if configs[0] != configs[L]: return
                config_tuples = [tuple(c) for c in configs[:L]]
                if len(set(config_tuples)) != L: return

                total_cycles += 1

                if found_word:
                    struct_works += 1
                else:
                    struct_fails += 1
                    if len(fail_details) < 5:
                        fail_details.append((word, fc, tuple(configs[0])))
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
print(f"Structural EC works: {struct_works} ({100*struct_works/max(1,total_cycles):.1f}%)")
print(f"Structural EC fails: {struct_fails}")

if struct_fails > 0:
    print("\nFailing words:")
    for w, f, s in fail_details[:5]:
        print(f"  {w}, fc={f}")
else:
    print("\nSTRUCTURAL EC WORKS FOR ALL CYCLES!")

# Also check with different ms configurations
print("\n" + "="*60)
print("Cross-check with ms=(2,3,2,3,2) — 3 non-consecutive binary")
print("="*60)

ms2 = (2, 3, 2, 3, 2)
total2 = 0
works2 = 0
fails2 = 0

for cl in [12, 14]:
    for word in enumerate_zw_words(n, cl):
        fc = fire_counts(word, n)
        if any(f < 2 for f in fc): continue
        if max(fc) < 3: continue

        L = len(word)
        found_word, _, _, _ = find_structural_ec(word, n, ms2)

        def check_cycles2(step, configs, transitions):
            global total2, works2, fails2
            if step == L:
                if configs[0] != configs[L]: return
                config_tuples = [tuple(c) for c in configs[:L]]
                if len(set(config_tuples)) != L: return
                total2 += 1
                if found_word: works2 += 1
                else: fails2 += 1
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
                check_cycles2(step + 1, configs, transitions)
                configs.pop()
            else:
                for new_val in range(ms2[p]):
                    if new_val == ctx[1]: continue
                    new_c = c[:]; new_c[p] = new_val
                    configs.append(new_c)
                    new_trans = dict(transitions)
                    new_trans[key] = new_val
                    check_cycles2(step + 1, configs, new_trans)
                    configs.pop()

        for start in itertools.product(*[range(m) for m in ms2]):
            check_cycles2(0, [list(start)], {})

print(f"Total valid cycles: {total2}")
print(f"Structural EC works: {works2} ({100*works2/max(1,total2):.1f}%)")
print(f"Structural EC fails: {fails2}")
