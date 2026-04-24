"""
Investigation part 7: Core mechanism verification.

The claim from ZeroWinding.lean comment:
"Find a binary proc b with fc=2 whose passthrough excursion creates a
one-sided provider (TernaryPhase at neighbor t where b fires even >= 2
times and the far neighbor is silent). The provider phase gives EC."

Let me verify at n=5: for every valid ZW+cw>0+fc>=3 good cycle,
can we find a binary b with fc=2 such that between b's two fires,
there's a step where b's full (L,S,R) context matches one of b's fire steps?

The mechanism in detail:
- b fires at a1 and a2 (consecutive fires), with a1 < a2
- Between a1 and a2, b doesn't fire → b's state is preserved (binary, 0 fires = even)
- At a2, b's state is the same as right after a1
- But wait: b's state CHANGES at a1 (it fires). So state at a1+1 ... a2-1 = state after a1's fire
- At a2, b fires again. Context at a2: (L_a2, S_a2, R_a2)
  where S_a2 = state after a1 fire (since b didn't fire in between)
- If there exists k in (a1, a2) where:
  * moverAt(k) != b
  * left(b) value at k = left(b) value at a2
  * right(b) value at k = right(b) value at a2
  Then we have EC at b.

The left(b) and right(b) conditions depend on what fires between a1 and a2.
For left(b): if left(b) fires 0 times in [k, a2), preserved → match
For right(b): if right(b) fires even times in [k, a2) (and is binary), preserved → match

This is basically palindromic_step_pair_caseA from the file!

So the question is: under ZW + fc >= 3 + sub-threshold,
can we always find such a b and k?

Let me verify computationally.
"""

import itertools

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

def check_provider_ec(word, n, ms, start_config):
    """Check if provider EC mechanism works for this specific cycle."""
    L = len(word)
    fc = fire_counts(word, n)
    binary_procs = [p for p in range(n) if ms[p] == 2]

    # Build config sequence (need transition tables, so we enumerate)
    # Actually, we need to check for ALL valid cycles with this word.
    # Let's do the full enumeration.

    results = {'total': 0, 'ec': 0, 'no_ec': 0, 'provider_ec': 0}

    def dfs_configs(step, configs, transitions):
        if results['total'] > 500: return  # cap
        if step == L:
            if configs[0] != configs[L]: return
            config_tuples = [tuple(c) for c in configs[:L]]
            if len(set(config_tuples)) != L: return

            results['total'] += 1

            # Check EC
            has_ec = False
            ec_at_binary_fc2 = False
            for i in range(n):
                mover_ctxs = set()
                nonmover_ctxs = set()
                for k in range(L):
                    c = configs[k]
                    ctx = (c[(i-1) % n], c[i], c[(i+1) % n])
                    if word[k] == i:
                        mover_ctxs.add(ctx)
                    else:
                        nonmover_ctxs.add(ctx)
                if mover_ctxs & nonmover_ctxs:
                    has_ec = True
                    if ms[i] == 2 and fc[i] == 2:
                        ec_at_binary_fc2 = True
                    break

            if has_ec:
                results['ec'] += 1
                if ec_at_binary_fc2:
                    results['provider_ec'] += 1
            else:
                results['no_ec'] += 1
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
            dfs_configs(step + 1, configs, transitions)
            configs.pop()
        else:
            for new_val in range(ms[p]):
                if new_val == ctx[1]: continue
                new_c = c[:]; new_c[p] = new_val
                configs.append(new_c)
                new_trans = dict(transitions)
                new_trans[key] = new_val
                dfs_configs(step + 1, configs, new_trans)
                configs.pop()

    for start in itertools.product(*[range(m) for m in ms]):
        dfs_configs(0, [list(start)], {})

    return results

# Comprehensive check at n=5
n = 5
ms = (2, 2, 2, 3, 3)
print(f"n={n}, ms={ms}")
print(f"Checking ALL valid ZW+cw>0+fc>=3 good cycles")
print()

grand = {'total': 0, 'ec': 0, 'no_ec': 0, 'provider_ec': 0}

for cl in [12, 14]:
    print(f"CL={cl}:")
    word_count = 0
    for word in enumerate_zw_words(n, cl):
        fc = fire_counts(word, n)
        if any(f < 2 for f in fc): continue
        if max(fc) < 3: continue

        r = check_provider_ec(word, n, ms, None)
        if r['total'] > 0:
            word_count += 1
            for k in grand: grand[k] += r[k]
            if r['no_ec'] > 0:
                print(f"  NO EC: word={word}, fc={fc}, results={r}")

    print(f"  {word_count} words with valid cycles")

print(f"\nGRAND TOTAL:")
print(f"  Valid cycles: {grand['total']}")
print(f"  With EC: {grand['ec']} ({100*grand['ec']/max(1,grand['total']):.1f}%)")
print(f"  EC at binary fc=2: {grand['provider_ec']} ({100*grand['provider_ec']/max(1,grand['total']):.1f}%)")
print(f"  Without EC: {grand['no_ec']}")

print()
print("="*60)
print("ALTERNATIVE APPROACH: Can we bypass zw_provider_ec entirely?")
print("="*60)
print()
print("The sorry zw_provider_ec is used to prove:")
print("  fc >= 3 at some proc → EC → False")
print("  which gives: all fc = 2")
print()
print("Alternative: prove all fc = 2 directly from ZW + cw > 0 structure")
print("without going through EC.")
print()
print("Under ZW with cw > 0:")
print("  CL = CW + CCW, CW = CCW (zero winding)")
print("  Each proc fires at CW steps and CCW steps")
print("  Walk visits each position at least twice (once each direction)")
print()
print("The walk is constrained: it's a closed walk on the ring graph")
print("with zero net displacement. The minimum such walk visiting")
print("each vertex at least twice has length 2n (palindromic).")
print()
print("If CL > 2n, the walk has 'excursions' — sub-walks that retrace.")
print("These excursions create providers for EC.")
print()
print("BUT: proving this analytically requires showing that the provider")
print("always exists, which is what zw_provider_ec does!")
print()
print("So we can't easily bypass it. It needs new work.")
