"""
Investigation part 6: Verify the actual mechanism and check at n=7.

The mechanism (from the computation at n=5):
- Under ZW + cw > 0 + all fc >= 2 + some fc >= 3:
- There exists a BINARY proc b with fc = 2
- b fires once CW (at step a1) and once CCW (at step a2)
- Between a1 and a2, b doesn't fire
- The binary value of b returns to its original (even interval fire count = 0)
- At a1: b fires, seeing context (L, S, R)
- At some step k between a1 and a2: b is non-mover, same (L, S, R)
- WHY? Because left(b) also doesn't fire between a1 and k (or fires even),
  and right(b) doesn't fire between k and a2 (or fires even)

Actually, the computation shows EC at binary proc with fc=2.
The simplest mechanism: b fires at step a2 with context (L, S, R).
At step a2-1, the mover is some other proc, and b has the same state S
(it hasn't fired since a1). If the left and right neighbors also happen
to have the same values at step a2-1... that's the EC.

Let me verify this more carefully and check if the mechanism works at n=7,9.

For n=7, the smallest sub-threshold multiset with 3 binary is (2,2,2,3,3,3,3)
with product 648. Sub-threshold = 4*3^5 = 972.

But CL=14 with fc>=3 means CL>=16, and enumerating all walks of length 16
on a ring of 7 is 2^16 = 65536 walks per starting position. Feasible.

Actually, ZW walks on ring of 7 with CL=16 is much smaller because of the
zero-winding constraint. Let me check.

Actually, let's take a different approach. Instead of enumerating walks,
let's verify the CLAIM directly:

CLAIM: Under ZW + cw > 0 + fc >= 2 for all, if some fc >= 3:
  1. There exists a binary proc b with fc = 2
  2. b's consecutive fire pair (a1, a2) has a "provider" structure
  3. This gives EC at b

For (1): With >= 3 binary procs and sum fc > 2n, if ALL binary procs had fc >= 3,
then sum fc >= 3*3 + 2*(n-3) = 2n+3. But we also need sum fc = CL and CW = CCW,
so CL is even. The minimum CL with some fc >= 3 is 2n+2.
Binary procs: at least 3. Ternary: at most n-3.
If all binary fc >= 3: sum >= 3*3 + 2*(n-3) = 2n+3 (for exactly 3 binary).
This is possible, so (1) is NOT trivially true.

Wait, but with 3 binary all having fc >= 3: sum >= 9 + 2*(n-3) = 2n+3.
Since CL must be even (CW = CCW under ZW), CL >= 2n+4.
But can all 3 binary have fc = 3? Then sum = 9 + 2*(n-3) = 2n+3.
That needs CL = 2n+3 which is odd. So at least one more fire is needed.
Either a 4th binary fire or a 3rd ternary fire, giving CL >= 2n+4.

So it's conceivable that all binary have fc >= 3. But does this happen?

Let me just check computationally.
"""

import itertools

def winding_number(mover_word, n):
    cw = 0; ccw = 0; L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]; nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
        elif nxt == (curr - 1) % n: ccw += 1
        else: return None
    if (cw - ccw) % n != 0: return None
    return (cw - ccw) // n

def cw_count(mover_word, n):
    cw = 0; L = len(mover_word)
    for i in range(L):
        curr = mover_word[i]; nxt = mover_word[(i + 1) % L]
        if nxt == (curr + 1) % n: cw += 1
    return cw

def fire_counts(word, n):
    fc = [0] * n
    for p in word: fc[p] += 1
    return fc

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

# At n=5: check if there are ZW words where ALL binary procs have fc >= 3
n = 5
binary_positions = {0, 1, 2}  # for ms=(2,2,2,3,3)
print(f"n={n}: Checking if all 3 binary procs can have fc >= 3")

for cl in range(12, 17):
    count = 0
    all_binary_fc3 = 0
    for word in enumerate_zw_words(n, cl):
        fc = fire_counts(word, n)
        if any(f < 2 for f in fc): continue
        if max(fc) < 3: continue
        count += 1
        if all(fc[b] >= 3 for b in binary_positions):
            all_binary_fc3 += 1
            if all_binary_fc3 <= 2:
                print(f"  CL={cl}: ALL binary fc>=3: {word}, fc={fc}")
    if count > 0:
        print(f"  CL={cl}: {count} words with fc>=3, {all_binary_fc3} with ALL binary fc>=3")

print()
print("="*60)
print("If all binary can have fc>=3, then 'find binary b with fc=2' fails.")
print("Need to verify the actual claim more carefully.")
print("="*60)

# Let's check: with ms=(2,2,2,3,3), binary at {0,1,2}
# The key constraint is sub-threshold product.
# Product = 2^3 * 3^2 = 72 < 108 = 4*3^3 ✓

# Actually, the claim in ZeroWinding.lean is specifically:
# "Find a binary proc b with fc=2"
# If ALL binary have fc >= 3, this fails!
# But maybe under ZW + cw > 0, not all binary CAN have fc >= 3?

# Under ZW: every proc fires at least 1 CW and 1 CCW.
# Binary proc with fc=3: fires 2 CW + 1 CCW or 1 CW + 2 CCW.
# CW total = CCW total = CL/2.
# If all 3 binary fire 3 times: total binary fires = 9.
# CW from binary: at least 3 (each fires 1 CW), at most 6 (each fires 2 CW).
# CCW from binary: similarly.
# CW from binary + CW from ternary = CL/2.
# Ternary: n-3 procs, each fires >= 2.
# CW from ternary: at least n-3 (each fires 1 CW), at most sum_ternary_fc - (n-3).

# This doesn't immediately prevent all binary fc >= 3.

# Let me check specifically: does a word with all binary fc >= 3 produce valid cycles?
print()
print("Checking if all-binary-fc>=3 words produce valid good cycles...")

for word in enumerate_zw_words(5, 14):
    fc = fire_counts(word, 5)
    if any(f < 2 for f in fc): continue
    if not all(fc[b] >= 3 for b in binary_positions): continue

    # Try to find a valid cycle
    L = len(word)
    ms = (2, 2, 2, 3, 3)
    found_cycle = [False]

    def dfs_check(step, configs, transitions):
        found_cycle_ref = found_cycle
        if found_cycle[0]: return
        if step == L:
            if configs[0] != configs[L]: return
            config_tuples = [tuple(c) for c in configs[:L]]
            if len(set(config_tuples)) != L: return
            found_cycle[0] = True
            print(f"  VALID CYCLE: word={word}, fc={fc}, start={tuple(configs[0])}")
            return
        p = word[step]
        c = configs[step]
        ctx = (c[(p-1) % 5], c[p], c[(p+1) % 5])
        key = (p, ctx[0], ctx[1], ctx[2])
        if key in transitions:
            new_val = transitions[key]
            if new_val == ctx[1]: return
            new_c = c[:]; new_c[p] = new_val
            configs.append(new_c)
            dfs_check(step + 1, configs, transitions)
            configs.pop()
        else:
            for new_val in range(ms[p]):
                if new_val == ctx[1]: continue
                new_c = c[:]; new_c[p] = new_val
                configs.append(new_c)
                new_trans = dict(transitions)
                new_trans[key] = new_val
                dfs_check(step + 1, configs, new_trans)
                configs.pop()

    for start in itertools.product(*[range(m) for m in ms]):
        if found_cycle[0]: break
        dfs_check(0, [list(start)], {})

    if not found_cycle[0]:
        pass  # No valid cycle for this word
    if found_cycle[0]:
        break

if not found_cycle[0]:
    print("  No valid cycles found for any all-binary-fc>=3 word!")
    print("  This means: in every valid ZW+cw>0 good cycle with some fc>=3,")
    print("  at least one binary proc has fc=2.")
